import Std

import Mathlib.Tactic.LibrarySearch

set_option autoImplicit true
set_option relaxedAutoImplicit true

alias ⟨and_not_not_of_not_or, _⟩ := not_or
alias ⟨Decidable.or_not_not_of_not_and, _⟩ := Decidable.not_and_iff_or_not

/-- A type synonym to equip a type with its lexicographic order. -/
def Lex' (α : Type _) := α

@[inherit_doc] notation:35 α " ×ₗ " β:34 => Lex' (Prod α β)

instance Prod.Lex.instLT' (α β : Type _) [LT α] [LT β] : LT (α ×ₗ β) where
  lt := Prod.Lex (· < ·) (· < ·)

-- Next three in https://github.com/leanprover/std4/pull/438
/-- A `dite` whose results do not actually depend on the condition may be reduced to an `ite`. -/
@[simp] theorem dite_eq_ite' [Decidable P] : (dite P (fun _ ↦ a) fun _ ↦ b) = ite P a b :=
  rfl

@[simp] theorem ite_some_none_eq_none [Decidable P] :
    (if P then some x else none) = none ↔ ¬ P := by
  split <;> simp_all

@[simp] theorem ite_some_none_eq_some [Decidable P] :
    (if P then some x else none) = some y ↔ P ∧ x = y := by
  split <;> simp_all

namespace Nat

-- https://github.com/leanprover/std4/pull/436
theorem emod_pos_of_not_dvd {a b : Nat} (h : ¬ a ∣ b) : 0 < b % a := by
  rw [dvd_iff_mod_eq_zero] at h
  exact Nat.pos_of_ne_zero h

end Nat

namespace Int

theorem le_iff_ge {a b : Int} : a ≤ b ↔ b ≥ a := Iff.rfl

-- https://github.com/leanprover/std4/pull/436
theorem emod_pos_of_not_dvd {a b : Int} (h : ¬ a ∣ b) : a = 0 ∨ 0 < b % a := by
  rw [dvd_iff_emod_eq_zero] at h
  by_cases w : a = 0
  · simp_all
  · exact Or.inr (Int.lt_iff_le_and_ne.mpr ⟨emod_nonneg b w, Ne.symm h⟩)

-- Next two in https://github.com/leanprover/std4/pull/437
theorem mul_ediv_self_le {x k : Int} (h : k ≠ 0) : k * (x / k) ≤ x :=
  calc k * (x / k)
    _ ≤ k * (x / k) + x % k := Int.le_add_of_nonneg_right (emod_nonneg x h)
    _ = x                   := ediv_add_emod _ _

theorem lt_mul_ediv_self_add {x k : Int} (h : 0 < k) : x < k * (x / k) + k :=
  calc x
    _ = k * (x / k) + x % k := (ediv_add_emod _ _).symm
    _ < k * (x / k) + k     := Int.add_lt_add_left (emod_lt_of_pos x h) _

-- https://github.com/leanprover/std4/pull/443
protected theorem mul_le_mul_of_nonpos_left {a b c : Int}
    (ha : a ≤ 0) (h : c ≤ b) : a * b ≤ a * c := by
  rw [Int.mul_comm a b, Int.mul_comm a c]
  apply Int.mul_le_mul_of_nonpos_right h ha

theorem pow_two {x : Int} : x^2 = x * x := by
  change Int.pow _ _ = _
  simp [Int.pow]

theorem mul_self_nonneg {x : Int} : 0 ≤ x * x := by
  match x with
  | .ofNat n =>
    simpa only [ofNat_eq_coe, ← Int.ofNat_mul] using Int.ofNat_nonneg _
  | .negSucc n =>
    simpa only [negSucc_mul_negSucc, ge_iff_le, ← Int.ofNat_mul] using Int.ofNat_nonneg _

theorem add_le_iff_le_sub (a b c : Int) : a + b ≤ c ↔ a ≤ c - b := by
  conv =>
    lhs
    rw [← Int.add_zero c, ← Int.sub_self (-b), Int.sub_eq_add_neg, ← Int.add_assoc, Int.neg_neg,
      Int.add_le_add_iff_right]

theorem le_add_iff_sub_le (a b c : Int) : a ≤ b + c ↔ a - c ≤ b := by
  conv =>
    lhs
    rw [← Int.neg_neg c, ← Int.sub_eq_add_neg, ← add_le_iff_le_sub]

theorem add_le_zero_iff_le_neg (a b : Int) : a + b ≤ 0 ↔ a ≤ - b := by
  rw [add_le_iff_le_sub, Int.zero_sub]
theorem add_le_zero_iff_le_neg' (a b : Int) : a + b ≤ 0 ↔ b ≤ -a := by
  rw [Int.add_comm, add_le_zero_iff_le_neg]
theorem add_nonnneg_iff_neg_le (a b : Int) : 0 ≤ a + b ↔ -b ≤ a := by
  rw [le_add_iff_sub_le, Int.zero_sub]
theorem add_nonnneg_iff_neg_le' (a b : Int) : 0 ≤ a + b ↔ -a ≤ b := by
  rw [Int.add_comm, add_nonnneg_iff_neg_le]

-- Next three in https://github.com/leanprover/std4/pull/444
protected theorem ne_iff_lt_or_gt {a b : Int} : a ≠ b ↔ a < b ∨ b < a := by
  constructor
  · intro h
    rcases Int.lt_trichotomy a b with lt | rfl | gt
    · exact Or.inl lt
    · simp_all
    · exact Or.inr gt
  · rintro (lt | gt)
    exact Int.ne_of_lt lt
    exact Int.ne_of_gt gt

protected alias ⟨lt_or_gt_of_ne, _⟩ := Int.ne_iff_lt_or_gt

protected theorem eq_iff_le_and_ge {x y : Int} : x = y ↔ x ≤ y ∧ y ≤ x := by
  constructor
  · simp_all
  · rintro ⟨h₁, h₂⟩
    exact Int.le_antisymm h₁ h₂



-- In https://github.com/leanprover/std4/pull/442
attribute [simp] sign_eq_zero_iff_zero

@[simp] theorem sign_sign : sign (sign x) = sign x := by
  match x with
  | 0 => rfl
  | .ofNat (_ + 1) => rfl
  | .negSucc _ => rfl

@[simp] theorem sign_nonneg : 0 ≤ sign x ↔ 0 ≤ x := by
  match x with
  | 0 => rfl
  | .ofNat (_ + 1) =>
    simp (config := { decide := true }) only [sign, true_iff]
    exact Int.le_add_one (ofNat_nonneg _)
  | .negSucc _ => simp (config := {decide := true}) [sign]

end Int

namespace List

-- https://github.com/leanprover/std4/pull/441
@[simp] theorem reverse_eq_nil_iff {xs : List α} : xs.reverse = [] ↔ xs = [] := by
  induction xs <;> simp

-- https://github.com/leanprover/std4/pull/445
@[simp] theorem isEmpty_nil : ([] : List α).isEmpty = true := rfl
@[simp] theorem isEmpty_cons : (x :: xs : List α).isEmpty = false := rfl

instance {xs : List α} : Decidable (xs = []) :=
  decidable_of_decidable_of_iff (by induction xs <;> simp : xs.isEmpty ↔ xs = [])

@[simp] theorem dropWhile_nil : ([] : List α).dropWhile p = [] := rfl

theorem dropWhile_cons :
    (x :: xs : List α).dropWhile p = if p x then xs.dropWhile p else x :: xs := by
  split <;> simp_all [dropWhile]

theorem dropWhile_append {xs ys : List α} :
    (xs ++ ys).dropWhile p =
      if xs.dropWhile p = [] then ys.dropWhile p else xs.dropWhile p ++ ys := by
  induction xs with
  | nil => simp
  | cons h t ih =>
    simp only [cons_append, dropWhile_cons]
    split <;> simp_all

@[simp]
theorem get?_coe {xs : List α} {i : Fin xs.length} : xs.get? i = some (xs.get i) :=
   get?_eq_some.mpr ⟨i.2, rfl⟩

/--
Return an index for an element in a list, given that the element is a member of the list.
This function is `O(xs.length)`, as it just traverses the list looking the element.
-/
def idx_of_mem [DecidableEq α] {xs : List α} (h : y ∈ xs) : Fin xs.length :=
  ⟨xs.findIdx (· = y), xs.findIdx_lt_length_of_exists ⟨y, h, by simp⟩⟩

theorem idx_of_mem_spec [DecidableEq α] {xs : List α} (w : y ∈ xs) :
    xs.get (xs.idx_of_mem w) = y :=
  decide_eq_true_eq.mp (List.findIdx_get (p := (· = y)) (xs := xs))

@[simp]
theorem map_id''' (l : List α) : l.map (fun a => a) = l := l.map_id

theorem mem_of_mem_filter' {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
  (mem_filter.mp h).1

theorem mem_iff_mem_erase_or_eq [DecidableEq α] (l : List α) (a b : α) :
    a ∈ l ↔ a ∈ l.erase b ∨ (a = b ∧ b ∈ l) := by
  by_cases h : a = b
  · subst h
    simp [or_iff_right_of_imp List.mem_of_mem_erase]
  · simp_all

end List

-- Currently not even using
-- namespace UInt64

-- attribute [ext] UInt64

-- protected theorem min_def {a b : UInt64} : min a b = if a ≤ b then a else b := rfl
-- protected theorem le_def {a b : UInt64} : a ≤ b ↔ a.val.val ≤ b.val.val := Iff.rfl
-- protected theorem lt_def {a b : UInt64} : a < b ↔ a.val.val < b.val.val := Iff.rfl

-- @[simp] protected theorem not_le {a b : UInt64} : ¬ (a ≤ b) ↔ b < a := by
--   rw [UInt64.le_def, UInt64.lt_def]
--   exact Fin.not_le

-- protected theorem min_comm {a b : UInt64} : min a b = min b a := by
--   ext
--   have min_val_val : ∀ a b : UInt64, (min a b).val.val = min a.val.val b.val.val := by
--     intros
--     simp only [UInt64.min_def, UInt64.le_def, Nat.min_def]
--     split <;> rfl
--   simp [min_val_val, Nat.min_comm]

-- protected theorem min_eq_left {a b : UInt64} (h : a ≤ b) : min a b = a := by
--   simp [UInt64.min_def, h]

-- protected theorem min_eq_right {a b : UInt64} (h : b ≤ a) : min a b = b := by
--   rw [UInt64.min_comm]; exact UInt64.min_eq_left h

-- end UInt64


namespace List

-- https://github.com/leanprover/std4/pull/440
/-- Variant of `List.insert` using `BEq` instead of `DecidableEq`. -/
@[inline] protected def insert' [BEq α] (a : α) (l : List α) : List α :=
  if l.elem a then l else a :: l

end List

namespace Std.HashMap

def all [BEq α] [Hashable α] (m : HashMap α β) (f : α → β → Bool) : Bool :=
  m.fold (init := true) fun r a b => r && f a b

end Std.HashMap

-- namespace Std.AssocList

-- def insert [BEq α] (a : α) (b : β) : AssocList α β → AssocList α β
--   | .nil => .cons a b .nil
--   | .cons x y t => if x == a then .cons x b t else .cons x y (insert a b t)

-- def partitionMapRev (f : α → β → γ ⊕ δ) (l : AssocList α β) : AssocList α γ × AssocList α δ :=
--   go {} {} l
-- where
--   go : AssocList α γ → AssocList α δ → AssocList α β → AssocList α γ × AssocList α δ
--   | xs, ys, .nil => (xs, ys)
--   | xs, ys, .cons a b t => match f a b with
--     | .inl x => go (cons a x xs) ys t
--     | .inr y => go xs (cons a y ys) t

-- def partitionRev (f : α → β → Bool) (l : AssocList α β) : AssocList α β × AssocList α β :=
--   l.partitionMapRev fun a b => bif f a b then .inl b else .inr b

-- end Std.AssocList

-- These are in https://github.com/leanprover/std4/pull/439
namespace Option

@[simp] theorem all_none : Option.all p none = true := rfl
@[simp] theorem all_some : Option.all p (some x) = p x := rfl

@[simp]
def min [Min α] : Option α → Option α → Option α
  | some x, some y => some (Min.min x y)
  | some x, none => some x
  | none, some y => some y
  | none, none => none

@[simp]
def max [Max α] : Option α → Option α → Option α
  | some x, some y => some (Max.max x y)
  | some x, none => some x
  | none, some y => some y
  | none, none => none

end Option

def _root_.String.bullet (s : String) := "• " ++ s.replace "\n" "\n  "
