/-
Compare constants of the same name in two sets of compiled modules, structurally (`==` on the
kernel terms, i.e. equality up to binder names), not by hash.

usage: lean --run Compare.lean <A.olean>[,<A2.olean>...] <B.olean>[,<B2.olean>...] [name ...]
With no names, every name declared on both sides is compared.
Prints, per name: kinds, whether universe parameters, type and value agree.
-/
import Lean
open Lean

def kindStr (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def valueOf? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- All constants of the most private part of each file. -/
unsafe def load (files : String) : IO (Std.HashMap Name ConstantInfo) := do
  let mut m : Std.HashMap Name ConstantInfo := {}
  for f in files.splitOn "," do
    let mFile : System.FilePath := f
    let mut fnames := #[mFile]
    let sFile := OLeanLevel.server.adjustFileName mFile
    if (← sFile.pathExists) then
      fnames := fnames.push sFile
      let pFile := OLeanLevel.private.adjustFileName mFile
      if (← pFile.pathExists) then fnames := fnames.push pFile
    let parts ← readModuleDataParts fnames
    if let some (md, _) := parts[parts.size - 1]? then
      for ci in md.constants do
        m := m.insert ci.name ci
  return m

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | a :: b :: names =>
    let ma ← load a
    let mb ← load b
    let names : List Name :=
      if names.isEmpty then (ma.toList.map (·.1)).filter (mb.contains ·) |>.toArray |>.qsort Name.lt |>.toList
      else names.map String.toName
    let mut bad := 0
    for n in names do
      match ma[n]?, mb[n]? with
      | some x, some y =>
        let lv := x.levelParams == y.levelParams
        let ty := x.type == y.type
        let val := match valueOf? x, valueOf? y with
          | some u, some v => if u == v then "identical" else "different"
          | none, none => "none"
          | _, _ => "one side only"
        unless lv && ty do bad := bad + 1
        IO.println s!"{n}: {kindStr x} / {kindStr y}; universe parameters {if lv then "identical" else "DIFFERENT"}; type {if ty then "identical" else "DIFFERENT"}; value {val}"
      | _, _ =>
        bad := bad + 1
        IO.println s!"{n}: missing on one side"
    return (if bad == 0 then 0 else 1)
  | _ =>
    IO.eprintln "usage: Compare <A.olean,...> <B.olean,...> [name ...]"
    return 2
