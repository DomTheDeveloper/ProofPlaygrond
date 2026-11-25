/-
Scan compiled Lean modules (public `.olean`, `.olean.server`, `.olean.private`) and emit, per module,
one JSON line describing every constant: its kind in the public and in the most private part, a
structural hash of its type and value, and the constants it refers to.

Usage: lean --run Scan.lean <list-file> <out-file>
where each line of <list-file> is `<moduleName>\t<path to .olean>`.
-/
import Lean
open Lean

def kindChar (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "A" | .defnInfo _ => "D" | .thmInfo _ => "T" | .opaqueInfo _ => "O"
  | .quotInfo _ => "Q" | .inductInfo _ => "I" | .ctorInfo _ => "C" | .recInfo _ => "R"

/-- All constants a declaration refers to (type, value, and the structural links of inductives). -/
def usedConsts (ci : ConstantInfo) : Array Name := Id.run do
  let mut acc : Array Name := ci.type.getUsedConstants
  match ci with
  | .axiomInfo _ => pure ()
  | .quotInfo _ => pure ()
  | .defnInfo v => acc := acc ++ v.value.getUsedConstants
  | .thmInfo v => acc := acc ++ v.value.getUsedConstants
  | .opaqueInfo v => acc := acc ++ v.value.getUsedConstants
  | .inductInfo v => acc := acc ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => acc := acc.push v.induct
  | .recInfo v =>
    acc := acc ++ v.all.toArray
    for r in v.rules do
      acc := (acc.push r.ctor) ++ r.rhs.getUsedConstants
  return acc

def valueHash (ci : ConstantInfo) : UInt64 :=
  match ci with
  | .defnInfo v => v.value.hash
  | .thmInfo v => v.value.hash
  | .opaqueInfo v => v.value.hash
  | _ => 0

def valueOf? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def flagsOf (ci : ConstantInfo) : Nat :=
  (if ci.isUnsafe then 1 else 0) + (if ci.isPartial then 2 else 0)

def jstr (s : String) : String := (Json.str s).compress

structure Interner where
  map : Std.HashMap Name Nat := {}
  names : Array Name := #[]

def Interner.get (it : Interner) (n : Name) : Interner × Nat :=
  match it.map[n]? with
  | some i => (it, i)
  | none => ({ map := it.map.insert n it.names.size, names := it.names.push n }, it.names.size)

unsafe def scanModuleCore (modName : String) (mFile : System.FilePath) (out : IO.FS.Handle) :
    IO (Array CompactedRegion) := do
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  let some (pub, _) := parts[0]? | throw <| IO.userError "no parts"
  let some (priv, _) := parts[parts.size - 1]? | throw <| IO.userError "no parts"
  let mut it : Interner := {}
  -- most private part
  let mut privIdx : Std.HashMap Name ConstantInfo := {}
  let mut privOut : Array String := #[]
  let mut dupInPriv : Array String := #[]
  for ci in priv.constants do
    if privIdx.contains ci.name then dupInPriv := dupInPriv.push (toString ci.name)
    privIdx := privIdx.insert ci.name ci
    let (it1, i) := it.get ci.name
    it := it1
    let mut used : Array Nat := #[]
    let mut seen : Std.HashSet Nat := {}
    for u in usedConsts ci do
      let (it2, j) := it.get u
      it := it2
      if !seen.contains j then
        seen := seen.insert j
        used := used.push j
    let usedStr := ",".intercalate (used.toList.map toString)
    privOut := privOut.push s!"[{i},\"{kindChar ci}\",{flagsOf ci},{ci.type.hash},{valueHash ci},{ci.levelParams.length},[{usedStr}]]"
  -- public part: kind there, and consistency with the most private part
  let mut pubOut : Array String := #[]
  if parts.size > 1 then
    for ci in pub.constants do
      let (it1, i) := it.get ci.name
      it := it1
      -- code: 0 = missing in private part, otherwise bit flags
      let code : Nat :=
        match privIdx[ci.name]? with
        | none => 0
        | some q =>
          let typeEq := ci.type == q.type
          let lvlEq := ci.levelParams == q.levelParams
          let valEq := match valueOf? ci, valueOf? q with
            | some a, some b => a == b
            | none, _ => true      -- public view hides the body
            | some _, none => false
          1 + (if typeEq then 2 else 0) + (if lvlEq then 4 else 0) + (if valEq then 8 else 0)
      let qk := match privIdx[ci.name]? with
        | none => "-"
        | some q => kindChar q
      pubOut := pubOut.push s!"[{i},\"{kindChar ci}\",\"{qk}\",{code},{if (valueOf? ci).isSome then 1 else 0}]"
  let importsStr := ",".intercalate (pub.imports.toList.map fun imp =>
    s!"[{jstr (toString imp.module)},{if imp.importAll then 1 else 0},{if imp.isExported then 1 else 0},{if imp.isMeta then 1 else 0}]")
  let namesStr := ",".intercalate (it.names.toList.map fun n => jstr (toString n))
  let line := "{\"m\":" ++ jstr modName ++ ",\"isModule\":" ++ (if pub.isModule then "1" else "0")
    ++ ",\"parts\":" ++ toString parts.size
    ++ ",\"imports\":[" ++ importsStr ++ "]"
    ++ ",\"dup\":[" ++ ",".intercalate (dupInPriv.toList.map jstr) ++ "]"
    ++ ",\"names\":[" ++ namesStr ++ "]"
    ++ ",\"pub\":[" ++ ",".intercalate pubOut.toList ++ "]"
    ++ ",\"priv\":[" ++ ",".intercalate privOut.toList ++ "]}\n"
  out.putStr line
  return parts.map (·.2)

/-- Scan one module, then unmap its files. The regions are released only after `scanModuleCore`
has returned, so that nothing that points into them is still alive. -/
unsafe def scanModule (modName : String) (mFile : System.FilePath) (out : IO.FS.Handle) : IO Unit := do
  let regions ← scanModuleCore modName mFile out
  for region in regions do
    region.free

unsafe def main (args : List String) : IO UInt32 := do
  let [listFile, outFile] := args | do
    IO.eprintln "usage: Scan <list-file> <out-file>"; return 2
  let out ← IO.FS.Handle.mk outFile .append
  let mut n := 0
  let mut bad := 0
  for line in (← IO.FS.lines listFile) do
    match line.splitOn "\t" with
    | [modName, path] =>
      try
        scanModule modName path out
        n := n + 1
      catch e =>
        bad := bad + 1
        out.putStr ("{\"m\":" ++ jstr modName ++ ",\"error\":" ++ jstr (toString e) ++ "}\n")
    | _ => pure ()
  out.flush
  IO.println s!"scanned {n} modules, {bad} errors"
  return (if bad == 0 then 0 else 1)
