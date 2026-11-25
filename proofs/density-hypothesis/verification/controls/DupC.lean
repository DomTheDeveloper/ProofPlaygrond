module

public import Init

/-! Control: a second module, which does not import `DupA`, defines `Dup.d` with another body. -/

@[expose] public section

def Dup.d : Nat := 2
