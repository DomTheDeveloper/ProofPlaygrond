/-
Module-wise kernel replay of a Lean 4 `module` build.

The replay logic below is adapted from `Lean.Kernel.Environment.replay` (`src/lean/Lean/Replay.lean`,
Copyright (c) 2023 Kim Morrison, released under Apache 2.0) of Lean 4 v4.37.0-rc1.

The worker keeps one kernel environment `E`.

* `E` starts as the environment obtained by importing the *external* modules given on the command
  line (Mathlib, Lean core, ...) the way a `module` file imports them (`OLeanLevel.exported`); an
  argument `all:Foo.Bar` imports that module with `import all`. These modules are trusted, not
  replayed.
* Then it reads lines `idx<TAB>module<TAB>path-to-.olean<TAB>view<TAB>check` from stdin, in a
  topological order of the import graph. For every line:
    1. if `check` is `1`, all three parts of the module (`.olean`, `.olean.server`,
       `.olean.private`) are read and every constant of the most private part is sent to the Lean
       kernel (`Kernel.Environment.addDeclCore`, full type checking) on top of `E`. The public part
       is compared with the private part (same names, types, universe parameters; bodies either
       hidden or identical).
    2. always: the constants of the part named by `view` (`pub`: the `.olean`; `priv`: the most
       private part, used for the few modules that some other module imports with `import all`) are
       added to `E` *without* checking (`addDeclWithoutChecking`). They are checked by step 1 of
       whichever worker has `check = 1` for the module.
  So `E` only ever contains views of modules that come earlier in the order, and no declaration is
  checked against anything that comes later.

Names declared by several modules (Lean lets different modules prove the same auto-generated
theorem, e.g. `f.eq_1`): the copy already in `E` must have the same type and universe parameters.
A theorem that meets such a copy is still checked in full, under a fresh name. A definition must be
identical to the copy in `E`. Anything else is an error.

A line `SYNC<TAB>k` makes the worker print `SYNCED k` (a barrier for the driver).
-/
import Lean
open Lean

namespace RHReplay

def kindChar (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "A" | .defnInfo _ => "D" | .thmInfo _ => "T" | .opaqueInfo _ => "O"
  | .quotInfo _ => "Q" | .inductInfo _ => "I" | .ctorInfo _ => "C" | .recInfo _ => "R"

/-- What to do with a constant `c` whose name is already taken by `e` in the environment. -/
inductive DupAction where
  /-- nothing to check: `c` is literally the constant already present -/
  | skip
  /-- `c` is a theorem with the type of `e`: check its proof under a fresh name -/
  | checkTheorem
  /-- the two constants cannot be reconciled -/
  | conflict

/-- `e` is already in the environment; a module's most private part declares `c` with the same name. -/
def dupChecked (e c : ConstantInfo) : DupAction :=
  if !(e.levelParams == c.levelParams && e.type == c.type) then .conflict else
  match e, c with
  | .inductInfo a, .inductInfo b => if a == b then .skip else .conflict
  | .ctorInfo a, .ctorInfo b => if a == b then .skip else .conflict
  | .recInfo a, .recInfo b => if a == b then .skip else .conflict
  | .defnInfo a, .defnInfo b => if a.value == b.value && a.safety == b.safety then .skip else .conflict
  | .opaqueInfo a, .opaqueInfo b => if a.value == b.value && a.isUnsafe == b.isUnsafe then .skip else .conflict
  | .thmInfo _, .thmInfo _ => .checkTheorem
  | .axiomInfo a, .thmInfo _ => if a.isUnsafe then .conflict else .checkTheorem
  | _, _ => .conflict

/-- `e` is already in the environment; a view that is added without checking has `c` with the same
name. Both must be statements (theorem or axiom view) of the same type, or identical. -/
def dupUnchecked (e c : ConstantInfo) : Bool :=
  e.levelParams == c.levelParams && e.type == c.type &&
  match e, c with
  | .inductInfo a, .inductInfo b => a == b
  | .ctorInfo a, .ctorInfo b => a == b
  | .recInfo a, .recInfo b => a == b
  | .defnInfo a, .defnInfo b => a.value == b.value && a.safety == b.safety
  | .opaqueInfo a, .opaqueInfo b => a.value == b.value && a.isUnsafe == b.isUnsafe
  | .thmInfo _, .thmInfo _ => true
  | .axiomInfo a, .thmInfo _ => !a.isUnsafe
  | .thmInfo _, .axiomInfo b => !b.isUnsafe
  | .axiomInfo a, .axiomInfo b => !a.isUnsafe && !b.isUnsafe
  | _, _ => false

/--
Is the public constant `p` a faithful view of the private constant `q` of the same module?
Either identical, or `p` is an axiom standing for a theorem / definition / opaque with the same
type and universe parameters. An axiom that stands for an unsafe or partial definition is marked
unsafe, and unsafe constants never enter the environment (see `replay`).
-/
def isViewOf (p q : ConstantInfo) : Bool :=
  p.levelParams == q.levelParams && p.type == q.type &&
  match p, q with
  | .inductInfo a, .inductInfo b => a == b
  | .ctorInfo a, .ctorInfo b => a == b
  | .recInfo a, .recInfo b => a == b
  | .thmInfo a, .thmInfo b => a.value == b.value
  | .defnInfo a, .defnInfo b => a.value == b.value && a.safety == b.safety
  | .opaqueInfo a, .opaqueInfo b => a.value == b.value && a.isUnsafe == b.isUnsafe
  | .axiomInfo a, .axiomInfo b => a.isUnsafe == b.isUnsafe
  | .axiomInfo a, .thmInfo _ => !a.isUnsafe
  -- `Lean.addDecl` exports a definition whose body is hidden as
  -- `.axiomInfo { defn with isUnsafe := defn.safety != .safe }` (`src/lean/Lean/AddDecl.lean`)
  | .axiomInfo a, .defnInfo b => a.isUnsafe == (b.safety != .safe)
  | .axiomInfo a, .opaqueInfo b => a.isUnsafe == b.isUnsafe
  | .quotInfo a, .quotInfo b => a == b
  | _, _ => false

structure Context where
  newConstants : Std.HashMap Name ConstantInfo
  /-- `true`: full kernel type checking. `false`: `addDeclWithoutChecking`. -/
  checked : Bool

structure State where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}
  /-- number of declarations handed to the kernel -/
  added : Nat := 0
  /-- slowest declarations, as text -/
  slow : Array String := #[]

abbrev M := ReaderT Context <| StateRefT State IO

def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

def throwKernelException (ex : Kernel.Exception) : M Unit := do
  throw <| .userError <| (← ex.toMessageData {} |>.toString)

def addDecl (d : Declaration) : M Unit := do
  let t0 ← IO.monoMsNow
  let checked := (← read).checked
  let env0 := (← get).env
  let r : Except Kernel.Exception Kernel.Environment :=
    if checked then env0.addDeclCore 0 0 d (cancelTk? := none)
    else env0.addDeclWithoutChecking d
  match r with
  | .ok env =>
    modify fun s => { s with env := env, added := s.added + 1 }
    let t1 ← IO.monoMsNow
    if t1 - t0 ≥ 20000 then
      let nm := match d.getNames with | n :: _ => toString n | [] => "?"
      modify fun s => { s with slow := s.slow.push s!"{nm}:{t1 - t0}ms" }
  | .error ex => throwKernelException ex

mutual
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    if (← get).pending.contains name then
      try
        match ci with
        | .defnInfo   info => addDecl (Declaration.defnDecl   info)
        | .thmInfo    info => addDecl (Declaration.thmDecl    info)
        | .axiomInfo  info => addDecl (Declaration.axiomDecl  info)
        | .opaqueInfo info => addDecl (Declaration.opaqueDecl info)
        | .inductInfo info =>
          let lparams := info.levelParams
          let nparams := info.numParams
          let all ← info.all.mapM fun n => do
            match (← read).newConstants[n]? with
            | some c => pure c
            | none => throw <| IO.userError s!"mutual inductive {n} is missing from the module"
          for o in all do
            modify fun s =>
              { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
          let ctorInfo ← all.mapM fun ci => do
            pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
              match (← read).newConstants[n]? with
              | some c => pure c
              | none => throw <| IO.userError s!"constructor {n} is missing from the module")
          for (ci, ctors) in ctorInfo do
            replayConstants ci.getUsedConstantsAsSet
            for ctor in ctors do
              replayConstants ctor.getUsedConstantsAsSet
          let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
            { name := ci.name
              type := ci.type
              ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
          addDecl (Declaration.inductDecl lparams nparams types false)
        | .ctorInfo info =>
          modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
        | .recInfo info =>
          modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
        | .quotInfo _ =>
          replayConstant `Eq
          addDecl (Declaration.quotDecl)
        modify fun s => { s with pending := s.pending.erase name }
      catch ex =>
        throw <| .userError s!"while replaying declaration '{name}':\n{ex}"

partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n
end

def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

structure Outcome where
  env : Kernel.Environment
  /-- declarations handed to the kernel (an inductive block counts once) -/
  added : Nat
  /-- duplicate theorems checked in full under a fresh name -/
  dupTheorems : Nat
  /-- constants identical to one already present, as `envKind/newKind` counts -/
  dups : Std.HashMap String Nat
  skippedUnsafe : Nat
  slow : Array String

/--
Add `consts` to `env`, in dependency order. Unsafe and partial constants are skipped, as in
`Lean.Kernel.Environment.replay`. See the file header for names that are already present.
-/
def replay (consts : Array ConstantInfo) (env : Kernel.Environment) (checked : Bool) (tag : String) :
    IO Outcome := do
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  let mut remaining : NameSet := ∅
  let mut dups : Std.HashMap String Nat := {}
  let mut dupThms : Array TheoremVal := #[]
  let mut skippedUnsafe := 0
  for ci in consts do
    if newConstants.contains ci.name then
      throw <| IO.userError s!"constant {ci.name} occurs twice in one module part"
    if ci.isUnsafe || ci.isPartial then
      skippedUnsafe := skippedUnsafe + 1
      continue
    match env.find? ci.name with
    | some e =>
      let key := s!"{kindChar e}/{kindChar ci}"
      if checked then
        match dupChecked e ci with
        | .skip => dups := dups.insert key (dups.getD key 0 + 1)
        | .checkTheorem =>
          match ci with
          | .thmInfo v => dupThms := dupThms.push v
          | _ => throw <| IO.userError s!"internal error: {ci.name} is not a theorem"
        | .conflict =>
          throw <| IO.userError s!"constant {ci.name} is already declared with different data (present: {kindChar e}, new: {kindChar ci})"
      else
        if dupUnchecked e ci then
          dups := dups.insert key (dups.getD key 0 + 1)
        else
          throw <| IO.userError s!"constant {ci.name} is already declared with different data (present: {kindChar e}, new: {kindChar ci})"
    | none =>
      newConstants := newConstants.insert ci.name ci
      remaining := remaining.insert ci.name
  let (_, s) ← StateRefT'.run (s := ({ env, remaining } : State)) do
    ReaderT.run (r := ({ newConstants, checked } : Context)) do
      replayConstant ``String.ofList
      replayConstant ``Char.ofNat
      for n in remaining do
        replayConstant n
      checkPostponedConstructors
      checkPostponedRecursors
  unless s.remaining.isEmpty && s.pending.isEmpty do
    throw <| IO.userError "internal error: constants left over after replay"
  -- duplicate theorems: check the module's own proof, under a fresh name, in the final environment
  let mut i := 0
  for v in dupThms do
    let fresh := Name.mkNum (Name.mkStr (Name.mkStr .anonymous "_dupcheck") tag) i ++ v.name
    i := i + 1
    let d := Declaration.thmDecl { v with name := fresh, all := [fresh] }
    match s.env.addDeclCore 0 0 d (cancelTk? := none) with
    | .ok _ => pure ()
    | .error ex =>
      throw <| .userError s!"while checking the duplicate theorem '{v.name}':\n{← ex.toMessageData {} |>.toString}"
  return { env := s.env, added := s.added, dupTheorems := dupThms.size, dups, skippedUnsafe, slow := s.slow }

def fmtDups (d : Std.HashMap String Nat) : String :=
  " ".intercalate (d.toList.map fun (k, v) => s!"{k}={v}")

/--
Fully check one module on top of `env`, given its three parts: kernel-replay the most private part
and compare the public part with it. Returns a report line.
-/
def checkParts (env : Kernel.Environment) (parts : Array (ModuleData × CompactedRegion)) (tag : String) :
    IO String := do
  let some (pub, _) := parts[0]? | throw <| IO.userError "no module data"
  let some (priv, _) := parts[2]? | throw <| IO.userError "no private module data"
  unless pub.isModule do throw <| IO.userError "not a `module`"
  let t0 ← IO.monoMsNow
  let out ← replay priv.constants env (checked := true) tag
  let t1 ← IO.monoMsNow
  -- the public part must be a view of the private part
  let mut privIdx : Std.HashMap Name ConstantInfo := {}
  for ci in priv.constants do
    privIdx := privIdx.insert ci.name ci
  let mut nPub := 0
  for p in pub.constants do
    nPub := nPub + 1
    match privIdx[p.name]? with
    | none => throw <| IO.userError s!"public constant {p.name} is not in the private part"
    | some q =>
      unless isViewOf p q do
        throw <| IO.userError s!"public constant {p.name} ({kindChar p}) is not a view of the private one ({kindChar q})"
  let mut nAxioms := 0
  for ci in priv.constants do
    if let .axiomInfo _ := ci then nAxioms := nAxioms + 1
  let slow := if out.slow.isEmpty then "" else " slow=[" ++ ",".intercalate out.slow.toList ++ "]"
  return s!"consts={priv.constants.size} kernel={out.added} dupthm={out.dupTheorems} dups=[{fmtDups out.dups}] unsafe={out.skippedUnsafe} axioms={nAxioms} pub={nPub} ms={t1 - t0}{slow}"

/--
Read a module's files, once. With `all`, the three parts; otherwise only the public `.olean`.

The files stay mapped for the life of the process: the environment's lookup cache
(`Lean.LookupCache`) may keep pointers to `Name`s of any part that was looked at, so unmapping a
part while the environment is alive is not safe. The driver therefore restarts the workers between
rounds instead of releasing memory inside a worker.
-/
unsafe def readParts (mFile : System.FilePath) (all : Bool) : IO (Array (ModuleData × CompactedRegion)) := do
  if all then
    let sFile := OLeanLevel.server.adjustFileName mFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    unless (← sFile.pathExists) && (← pFile.pathExists) do
      throw <| IO.userError s!"missing .olean.server / .olean.private next to {mFile}"
    readModuleDataParts #[mFile, sFile, pFile]
  else
    readModuleDataParts #[mFile]

/-- Add a view of a module (the constants of one of its parts) to `env` without checking. -/
def addView (env : Kernel.Environment) (md : ModuleData) (tag : String) : IO (Kernel.Environment × String) := do
  let out ← replay md.constants env (checked := false) tag
  let d := if out.dups.isEmpty then "" else s!"viewdups=[{fmtDups out.dups}]"
  return (out.env, d)

unsafe def run (externals : Array String) : IO UInt32 := do
  let imports : Array Import := externals.map fun s =>
    if s.startsWith "all:" then { module := (s.drop 4).toString.toName, importAll := true }
    else { module := s.toName }
  let t0 ← IO.monoMsNow
  let env0 ← importModules imports {} (trustLevel := 0) (loadExts := false) (level := OLeanLevel.exported)
  let mut env := env0.toKernelEnv
  let stdout ← IO.getStdout
  let stdin ← IO.getStdin
  stdout.putStrLn s!"READY externals={externals.size} importMs={(← IO.monoMsNow) - t0}"
  stdout.flush
  let mut failures := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := if line.endsWith "\n" then (line.dropEnd 1).toString else line
    match line.splitOn "\t" with
    | ["SYNC", k] =>
      stdout.putStrLn s!"SYNCED {k}"
      stdout.flush
    | ["HAS", n] =>
      let r := match env.find? n.toName with
        | some ci => s!"{kindChar ci}"
        | none => "-"
      stdout.putStrLn s!"HAS\t{n}\t{r}"
      stdout.flush
    | [idxS, modName, path, view, check] =>
      -- each file of the module is mapped exactly once
      let parts? ← try
          pure (some (← readParts path (check == "1" || view == "priv")))
        catch e =>
          failures := failures + 1
          let kind := if check == "1" then "FAIL" else "VIEWFAIL"
          stdout.putStrLn s!"{kind}\t{idxS}\t{modName}\t{(toString e).replace "\n" " | "}"
          stdout.flush
          pure none
      if let some parts := parts? then
        if check == "1" then
          try
            let report ← checkParts env parts idxS
            stdout.putStrLn s!"OK\t{idxS}\t{modName}\t{report}"
          catch e =>
            failures := failures + 1
            stdout.putStrLn s!"FAIL\t{idxS}\t{modName}\t{(toString e).replace "\n" " | "}"
          stdout.flush
        try
          let some (md, _) := (if view == "priv" then parts[2]? else parts[0]?)
            | throw <| IO.userError "module part missing"
          let (env', d) ← addView env md idxS
          env := env'
          if !d.isEmpty && check == "1" then
            stdout.putStrLn s!"NOTE\t{idxS}\t{modName}\t{d}"
        catch e =>
          failures := failures + 1
          stdout.putStrLn s!"VIEWFAIL\t{idxS}\t{modName}\t{(toString e).replace "\n" " | "}"
          stdout.flush
    | _ =>
      stdout.putStrLn s!"BADLINE {line}"
      stdout.flush
  stdout.putStrLn s!"END failures={failures}"
  stdout.flush
  return (if failures == 0 then 0 else 1)

end RHReplay

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  RHReplay.run args.toArray
