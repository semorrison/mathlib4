import Std

namespace Int

theorem natCast_ofNat {x : Nat} :
    @Nat.cast Int instNatCastInt (no_index (OfNat.ofNat x)) = OfNat.ofNat x := rfl

theorem lt_of_gt {x y : Int} (h : x > y) : y < x := gt_iff_lt.mp h
theorem le_of_ge {x y : Int} (h : x ≥ y) : y ≤ x := ge_iff_le.mp h

theorem ofNat_congr {a b : Nat} (h : a = b) : (a : Int) = (b : Int) := congrArg _ h
theorem ofNat_lt_of_lt {a b : Nat} (h : a < b) : (a : Int) < (b : Int) := Int.ofNat_lt.mpr h
theorem ofNat_le_of_le {a b : Nat} (h : a ≤ b) : (a : Int) ≤ (b : Int) := Int.ofNat_le.mpr h

theorem ofNat_sub_sub {a b c : Nat} : ((a - b - c : Nat) : Int) = ((a - (b + c) : Nat) : Int) :=
  congrArg _ (Nat.sub_sub _ _ _)

protected alias ⟨lt_of_not_ge, _⟩ := Int.not_le
protected alias ⟨lt_of_not_le, not_le_of_lt⟩ := Int.not_le
protected alias ⟨_, lt_le_asymm⟩ := Int.not_le

protected alias ⟨le_of_not_gt, not_lt_of_ge⟩ := Int.not_lt
protected alias ⟨le_of_not_lt, not_lt_of_le⟩ := Int.not_lt
protected alias ⟨_, le_lt_asymm⟩ := Int.not_lt

theorem add_congr {a b c d : Int} (h₁ : a = b) (h₂ : c = d) : a + c = b + d := by
  subst h₁; subst h₂; rfl

theorem mul_congr_right (a : Int) {c d : Int} (h₂ : c = d) : a * c = a * d := by
  subst h₂; rfl

theorem sub_congr {a b c d : Int} (h₁ : a = b) (h₂ : c = d) : a - c = b - d := by
  subst h₁; subst h₂; rfl

theorem neg_congr {a b : Int} (h₁ : a = b) : -a = -b := by
  subst h₁; rfl

end Int

theorem Nat.lt_of_gt {x y : Nat} (h : x > y) : y < x := gt_iff_lt.mp h
theorem Nat.le_of_ge {x y : Nat} (h : x ≥ y) : y ≤ x := ge_iff_le.mp h
