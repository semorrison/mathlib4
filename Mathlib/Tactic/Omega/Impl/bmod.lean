import Mathlib.Tactic.Omega.ForStd

set_option autoImplicit true

@[simp] theorem Int.sign_ofNat_add_one {x : Nat} : Int.sign (x + 1) = 1 := rfl
