/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std

set_option autoImplicit true
set_option relaxedAutoImplicit true

open Lean (HashSet)

-- https://github.com/leanprover/std4/pull/449
open Lean in
instance name_collision : ToExpr Int where
  toTypeExpr := .const ``Int []
  toExpr i := match i with
    | .ofNat n => mkApp (.const ``Int.ofNat []) (toExpr n)
    | .negSucc n => mkApp (.const ``Int.negSucc []) (toExpr n)


namespace Int


-- theorem pow_two {x : Int} : x^2 = x * x := by
--   change Int.pow _ _ = _
--   simp [Int.pow]

-- theorem mul_self_nonneg {x : Int} : 0 ≤ x * x := by
--   match x with
--   | .ofNat n =>
--     simpa only [ofNat_eq_coe, ← Int.ofNat_mul] using Int.ofNat_nonneg _
--   | .negSucc n =>
--     simpa only [negSucc_mul_negSucc, ge_iff_le, ← Int.ofNat_mul] using Int.ofNat_nonneg _

-- Next three in https://github.com/leanprover/std4/pull/451
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


end Int

namespace List

-- @[simp]
-- theorem get?_coe {xs : List α} {i : Fin xs.length} : xs.get? i = some (xs.get i) :=
--    get?_eq_some.mpr ⟨i.2, rfl⟩

-- /--
-- Return an index for an element in a list, given that the element is a member of the list.
-- This function is `O(xs.length)`, as it just traverses the list looking the element.
-- -/
-- def idx_of_mem [DecidableEq α] {xs : List α} (h : y ∈ xs) : Fin xs.length :=
--   ⟨xs.findIdx (· = y), xs.findIdx_lt_length_of_exists ⟨y, h, by simp⟩⟩

-- theorem idx_of_mem_spec [DecidableEq α] {xs : List α} (w : y ∈ xs) :
--     xs.get (xs.idx_of_mem w) = y :=
--   decide_eq_true_eq.mp (List.findIdx_get (p := (· = y)) (xs := xs))

-- https://github.com/leanprover/std4/pull/450
@[simp]
theorem map_id''' (l : List α) : l.map (fun a => a) = l := l.map_id

-- theorem mem_of_mem_filter' {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
--   (mem_filter.mp h).1

-- theorem mem_iff_mem_erase_or_eq [DecidableEq α] (l : List α) (a b : α) :
--     a ∈ l ↔ a ∈ l.erase b ∨ (a = b ∧ b ∈ l) := by
--   by_cases h : a = b
--   · subst h
--     simp [or_iff_right_of_imp List.mem_of_mem_erase]
--   · simp_all

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


-- namespace Std.HashMap

-- def all [BEq α] [Hashable α] (m : HashMap α β) (f : α → β → Bool) : Bool :=
--   m.fold (init := true) fun r a b => r && f a b

-- end Std.HashMap

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


def _root_.String.bullet (s : String) := "• " ++ s.replace "\n" "\n  "
