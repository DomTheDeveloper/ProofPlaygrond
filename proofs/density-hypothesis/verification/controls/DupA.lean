module

public import Init

/-! Control: the honest first declaration of names that `DupB.lean` declares again. -/

public section

theorem Dup.t : True := True.intro

def Dup.d : Nat := 1
