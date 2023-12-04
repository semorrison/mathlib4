import Mathlib.Tactic.Omega.ForStd

set_option autoImplicit true

/-- Balanced mod, taking values in the range [- m/2, (m - 1)/2]. -/
def Int.bmod (x : Int) (m : Nat) : Int :=
  let r := x % m
  if r < (m + 1) / 2 then
    r
  else
    r - m

example : Int.bmod 3 7 = 3 := rfl
example : Int.bmod 4 7 = -3 := rfl
example : Int.bmod 3 8 = 3 := rfl
example : Int.bmod 4 8 = -4 := rfl

theorem Int.ofNat_two : ((2 : Nat) : Int) = 2 := rfl

@[simp] theorem Int.bmod_emod : (Int.bmod x m) % m = x % m := sorry

@[simp] theorem Int.bmod_zero : Int.bmod 0 m = 0 := by
  dsimp [Int.bmod]
  simp only [Int.zero_emod, Int.zero_sub, ite_eq_left_iff, Int.neg_eq_zero]
  -- `omega` would be helpful here.
  intro h
  rw [@Int.not_lt] at h
  match m with
  | 0 => rfl
  | (m+1) =>
    exfalso
    rw [Int.natCast_add, Int.ofNat_one, Int.add_assoc, Int.add_ediv_of_dvd_right] at h
    change _ + 2 / 2 ≤ 0 at h
    rw [Int.ediv_self, ← Int.ofNat_two, ← Int.ofNat_ediv, Int.add_one_le_iff, ← @Int.not_le] at h
    exact h (Int.ofNat_nonneg _)
    all_goals decide

theorem Int.dvd_emod_sub_self {x : Int} {m : Nat} : (m : Int) ∣ x % m - x := by
  apply Int.dvd_of_emod_eq_zero
  simp [Int.sub_emod]

theorem Int.dvd_bmod_sub_self {x : Int} {m : Nat} : (m : Int) ∣ Int.bmod x m - x := by
  dsimp [Int.bmod]
  split
  · exact Int.dvd_emod_sub_self
  · rw [Int.sub_sub, Int.add_comm, ← Int.sub_sub]
    exact Int.dvd_sub Int.dvd_emod_sub_self (Int.dvd_refl _)

-- theorem Int.le_bmod {x : Int} {m : Nat} (h : 0 < m) : - m/2 ≤ Int.bmod x m := by
--   dsimp [Int.bmod]
--   split
--   · apply Int.le_trans
--     · show _ ≤ 0
--       sorry
--     · exact Int.emod_nonneg _ (Int.natAbs_pos.mp h)
--   · rename_i h
--     rw [Int.not_lt] at h
--     have : ((m : Int) + 1)/ 2 - m ≤ x % m - m := by exact Int.sub_le_sub_right h ↑m
--     refine Int.le_trans ?_ this
--     sorry

theorem Int.bmod_lt {x : Int} {m : Nat} (h : 0 < m) : Int.bmod x m < (m + 1) / 2 := by
  dsimp [Int.bmod]
  split
  · assumption
  · apply Int.lt_of_lt_of_le
    · show _ < 0
      have : x % m < m := Int.emod_lt_of_pos x (Int.ofNat_pos.mpr h)
      exact Int.sub_neg_of_lt this
    · exact Int.le.intro_sub _ rfl

theorem Int.bmod_le {x : Int} {m : Nat} (h : 0 < m) : Int.bmod x m ≤ (m - 1) / 2 := by
  refine Int.lt_add_one_iff.mp ?_
  calc
    bmod x m < (m + 1) / 2  := Int.bmod_lt h
    _ = ((m + 1 - 2) + 2)/2 := by simp
    _ = (m - 1) / 2 + 1     := by
      rw [Int.add_ediv_of_dvd_right]
      · simp (config := {decide := true}) only [Int.ediv_self]
        congr 2
        rw [Int.add_sub_assoc, ← Int.sub_neg]
        congr
      · trivial

@[simp] theorem Int.emod_self_add_one {x : Int} (h : 0 ≤ x) : x % (x + 1) = x :=
  Int.emod_eq_of_lt h (Int.lt_succ x)

@[simp] theorem Int.sign_ofNat_add_one {x : Nat} : Int.sign (x + 1) = 1 := rfl
@[simp] theorem Int.sign_negSucc {x : Nat} : Int.sign (Int.negSucc x) = -1 := rfl


-- In fact the only exceptional value we need to rule out if `x = -1`,
-- but in our application we know `w : 1 < x.natAbs`, so just use that.
theorem Int.bmod_natAbs_plus_one (x : Int) (w : 1 < x.natAbs) :
    Int.bmod x (x.natAbs + 1) = - x.sign := by
  have t₁ : ∀ (x : Nat), x % (x + 2) = x :=
    fun x => Nat.mod_eq_of_lt (Nat.lt_succ_of_lt (Nat.lt.base x))
  have t₂ : ∀ (x : Int), 0 ≤ x → x % (x + 2) = x := fun x h => by
    match x, h with
    | Int.ofNat x, _ => erw [← Int.ofNat_two, ←Int.ofNat_add, ← Int.ofNat_emod, t₁]; rfl
  cases x with
  | ofNat x =>
    simp only [bmod, Int.ofNat_eq_coe, Int.natAbs_ofNat, Int.natCast_add, Int.ofNat_one,
      emod_self_add_one (Int.ofNat_nonneg x)]
    match x with
    | 0 => rw [if_pos] <;> simp (config := {decide := true})
    | (x+1) =>
      rw [if_neg]
      · simp [← Int.sub_sub]
      · refine Int.not_lt.mpr ?_
        simp only [← Int.natCast_add, ← Int.ofNat_one, ← Int.ofNat_two, ← Int.ofNat_ediv]
        match x with
        | 0 => apply Int.le_refl
        | (x+1) =>
          -- Just the sort of tedious problem we want `omega` for!
          refine Int.ofNat_le.mpr ?_
          apply Nat.div_le_of_le_mul
          simp only [Nat.two_mul, Nat.add_assoc]
          apply Nat.add_le_add_left
          apply Nat.add_le_add_left
          apply Nat.add_le_add_left
          exact Nat.le_add_left (1 + 1) x
  | negSucc x =>
    simp only [bmod, Int.natAbs_negSucc, Int.natCast_add, Int.ofNat_one, sign_negSucc, Int.neg_neg]
    rw [Nat.succ_eq_add_one, Int.negSucc_emod]
    erw [t₂]
    · simp only [Int.natCast_add, Int.ofNat_one, Int.add_sub_cancel]
      rw [Int.add_comm, Int.add_sub_cancel]
      rw [if_pos]
      · match x, w with
        | (x+1), _ =>
          -- Another one for `omega`:
          rw [Int.add_assoc, Int.add_ediv_of_dvd_right]
          show _ < _ + 2 / 2
          rw [Int.ediv_self]
          apply Int.lt_add_one_of_le
          rw [Int.add_comm, Int.ofNat_add]
          rw [Int.add_assoc, Int.add_ediv_of_dvd_right]
          show _ ≤ _ + 2 / 2
          rw [Int.ediv_self]
          apply Int.le_add_of_nonneg_left
          exact Int.le.intro_sub _ rfl
          all_goals decide
    · exact Int.ofNat_nonneg x
    · exact Int.succ_ofNat_pos (x + 1)
