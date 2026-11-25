module

public import Init
meta import Lean

/-!
Control: a second module, which does not import `DupA`, declares `Dup.t : True` again, this time
with the proof term `Nat.zero` (added with the kernel switched off). Lean allows two modules to
prove the same theorem; a re-check must still reject this proof.
-/

public section

open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| Lean.addDecl <| Declaration.thmDecl {
  name := `Dup.t, levelParams := [], type := mkConst ``True, value := mkConst ``Nat.zero }
