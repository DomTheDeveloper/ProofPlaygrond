module

public import Init
meta import Lean

/-!
Negative control for the replay tool: a "theorem" `Bogus.falseHolds : False` whose proof term is
`True.intro`. It is added with the kernel switched off (`debug.skipKernelTC`), so Lean accepts the
file; any real re-check must reject it.
-/

public section

theorem Bogus.fine : True := True.intro

open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM <| Lean.addDecl <| Declaration.thmDecl {
  name := `Bogus.falseHolds, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }

theorem Bogus.usesIt : False := Bogus.falseHolds
