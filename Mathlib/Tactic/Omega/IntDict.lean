/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.AssocList
import Std.Data.Int.Basic
import Std
import Mathlib.Tactic.ToExpr
import Mathlib.Tactic.Omega.IntList

open Std (AssocList)

set_option autoImplicit true
set_option relaxedAutoImplicit true

namespace Std.AssocList

-- https://github.com/leanprover/std4/pull/435
/-- The number of entries in an `AssocList`. -/
def size (L : AssocList α β) : Nat :=
  match L with
  | .nil => 0
  | .cons _ _ t => t.size + 1

@[simp] theorem size_nil : size (.nil : AssocList α β) = 0 := rfl
@[simp] theorem size_cons : size (.cons a b t) = size t + 1 := rfl

def last? (L : AssocList α β) : Option (α × β) :=
  match L with
  | .nil => none
  | .cons a b .nil => some (a, b)
  | .cons _ _ t => last? t

deriving instance Lean.ToExpr for AssocList
deriving instance DecidableEq for AssocList
deriving instance Hashable for AssocList

deriving instance Repr for AssocList

-- https://github.com/leanprover/std4/pull/434
private def beq [BEq α] [BEq β] : AssocList α β → AssocList α β → Bool
  | .nil, .nil => true
  | .cons _ _ _, .nil => false
  | .nil, .cons _ _ _ => false
  | .cons a b t, .cons a' b' t' => a == a' && b == b' && beq t t'

instance [BEq α] [BEq β] : BEq (AssocList α β) where beq := beq

@[simp] theorem beq_nil₂ [BEq α] [BEq β] : ((.nil : AssocList α β) == .nil) = true := rfl
@[simp] theorem beq_nil_cons [BEq α] [BEq β] : ((.nil : AssocList α β) == .cons a b t) = false :=
  rfl
@[simp] theorem beq_cons_nil [BEq α] [BEq β] : ((.cons a b t : AssocList α β) == .nil) = false :=
  rfl
@[simp] theorem beq_cons₂ [BEq α] [BEq β] :
    ((.cons a b t : AssocList α β) == .cons a' b' t') = (a == a' && b == b' && t == t') := rfl

instance [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] : LawfulBEq (AssocList α β) where
  rfl := @fun L => by induction L <;> simp_all
  eq_of_beq := @fun L M => by
    induction L generalizing M with
    | nil => cases M <;> simp_all
    | cons a b L ih =>
      cases M with
      | nil => simp_all
      | cons a' b' M =>
        simp_all only [beq_cons₂, Bool.and_eq_true, beq_iff_eq, cons.injEq, true_and, and_imp]
        intros _ _ h
        exact ih _ h

end Std.AssocList

/--
A type synonum for `AssocList Nat Int`, used by `omega`.

In this use case, we always have the keys in strictly increasing order,
and no zero values. (Neither of these conditions are verified, however.)
-/
def IntDict := AssocList Nat Int

namespace IntDict

deriving instance Lean.ToExpr for IntDict
deriving instance Hashable for IntDict

instance : BEq IntDict := inferInstanceAs <| BEq (AssocList Nat Int)
instance : LawfulBEq IntDict := inferInstanceAs <| LawfulBEq (AssocList Nat Int)
instance : DecidableEq IntDict := inferInstanceAs <| DecidableEq (AssocList Nat Int)
instance : EmptyCollection IntDict := inferInstanceAs <| EmptyCollection (AssocList Nat Int)
instance : Repr IntDict := inferInstanceAs <| Repr (AssocList Nat Int)

-- TODO tail recursive version?
/-- Apply a function to all values in an `IntDict`, dropping zeroes. -/
def map (f : Int → Int) (xs : IntDict) : IntDict :=
  match xs with
  | .nil => .nil
  | .cons i x t =>
    let r := f x
    if r = 0 then
      map f t
    else
      .cons i r (map f t)

/--
Construct an "dense" `IntDict` from a list (dropping zeroes).
-/
def ofList (xs : List Int) : IntDict :=
  go 0 xs
where
  go : Nat → List Int → IntDict
  | _, [] => .nil
  | i, 0 :: xs => go (i+1) xs
  | i, x :: xs => .cons i x (go (i+1) xs)

/-- The "dimension" of an `IntDict`, i.e. one greater than the largest key. -/
def length (xs : IntDict) : Nat := xs.last?.map (·.1 + 1) |>.getD 0

theorem length_le_length_cons {xs : IntDict} : length xs ≤ length (.cons i x xs) := by
  cases xs <;> dsimp [length, AssocList.last?]
  · exact Nat.zero_le (i + 1)
  · exact Nat.le_refl _

/--
Convert a "sparse" `IntDict` to a list, filling in zeroes as needed.

(We drop any out of order terms!)
-/
def toList (xs : IntDict) : List Int :=
  go 0 xs
where
  go : Nat → IntDict → List Int
  | _, .nil => []
  | i, .cons j x t => if i ≤ j then List.replicate (j - i) 0 ++ x :: go (j+1) t else go i t

@[simp] theorem toList_nil : toList .nil = [] := rfl

/-- String representation of an `IntDict`. -/
nonrec def toString (xs : IntDict) : String :=
  toString <| AssocList.toList xs

instance : ToString IntDict where toString := toString

theorem map_length (f : Int → Int) : (xs : IntDict) → (xs.map f).length ≤ xs.length
  | .nil => sorry
  | .cons i x xs => by
    rw [map]
    dsimp
    split
    · refine Nat.le_trans (map_length f xs) ?_
      exact length_le_length_cons
    · sorry


/-- Returns the value in the `i`-th coordinate, or zero if there is no such key. -/
def get (xs : IntDict) (i : Nat) : Int :=
  match xs with
  | .nil => 0
  | .cons j x t =>
    if i = j then x else if i < j then 0 else get t i

@[simp] theorem get_nil : get (.nil : IntDict) i = 0 := rfl

/-- Sets the `i`-th coordinate to a specified value (and drops it if that value is zero). -/
def set (xs : IntDict) (i : Nat) (y : Int) : IntDict :=
  match xs with
  | .nil => .cons i y .nil
  | .cons j x t =>
    if i = j then
      if y = 0 then t else .cons j y t
    else if i < j then
      .cons i y xs
    else
      .cons j x (set t i y )

/-- Calculates the gcd of the absolute values of the values. -/
def gcd (xs : IntDict) : Nat :=
  xs.foldl (fun g _ x => Nat.gcd x.natAbs g) 0

/-- Multiplies all values by a constant. (Returns the empty `IntDict` if the constant is zero.) -/
def smul (xs : IntDict) (g : Int) : IntDict :=
  if g = 0 then .nil else xs.mapVal fun _ x => g * x

instance : HMul Int IntDict IntDict where hMul i xs := smul xs i

/-- Divides all values by a constant (dropping zeros). -/
def sdiv (xs : IntDict) (g : Int) : IntDict :=
  xs.map (· / g)

/-- Computes the dot product of two `IntDict`s. -/
def dot (xs ys : IntDict) : Int :=
  match xs, ys with
  | .nil, _ => 0
  | _, .nil => 0
  | .cons i x xs, .cons j y ys =>
    if i < j then
      dot xs (.cons j y ys)
    else if j < i then
      dot (.cons i x xs) ys
    else x * y + dot xs ys
termination_by dot xs ys => xs.size + ys.size

@[simp] theorem dot_nil_left : dot .nil ys = 0 := by cases ys <;> rfl
@[simp] theorem dot_nil_right : dot xs .nil = 0 := by cases xs <;> rfl

-- theorem dot_eq_dot_toList : (xs ys : IntDict) → dot xs ys = IntList.dot xs.toList ys.toList
--   | .nil, _ => by simp
--   | _, .nil => by simp
--   | .cons i x xs, .cons j y ys => by
--     rw [dot]
--     split
--     · rw [dot_eq_dot_toList xs (.cons j y ys)]


/-- Adds two `IntDict`s, dropping any zero values. -/
def add (xs ys : IntDict) : IntDict :=
  match xs, ys with
  | .nil, _ => ys
  | _, .nil => xs
  | .cons i x xs, .cons j y ys =>
    if i < j then
      .cons i x (add xs (.cons j y ys))
    else if j < i then
      .cons j y (add (.cons i x xs) ys)
    else
      let r := x + y
      if r = 0 then
        add xs ys
      else
        .cons i r (add xs ys)
termination_by add xs ys => xs.size + ys.size

instance : Add IntDict where add := add

theorem add_def {xs ys : IntDict} : xs + ys = add xs ys := rfl

@[simp] theorem add_nil_left {ys : IntDict} : .nil + ys = ys := by
  cases ys <;> rfl
@[simp] theorem add_nil_right {xs : IntDict} : xs + .nil = xs := by
  cases xs <;> rfl

/-- Negates an `IntDict`. -/
def neg (xs : IntDict) : IntDict := xs.mapVal fun _ x => -x

instance : Neg IntDict where neg := neg

theorem neg_def {xs : IntDict} : (-xs) = neg xs := rfl

@[simp] theorem neg_nil : (- (.nil) : IntDict) = .nil := rfl
@[simp] theorem neg_cons {i : Nat} {x : Int} {xs : IntDict} :
    (- (.cons i x xs) : IntDict) = .cons i (-x) (-xs) := rfl

theorem neg_cons' {i : Nat} {x : Int} {xs : IntDict} :
    (neg (.cons i x xs) : IntDict) = .cons i (-x) (neg xs) := rfl

/-- Subtracts two `IntDict`s, dropping any zero values. -/
def sub (xs ys : IntDict) : IntDict :=
  match xs, ys with
  | .nil, _ => -ys
  | _, .nil => xs
  | .cons i x xs, .cons j y ys =>
    if i < j then
      .cons i x (sub xs (.cons j y ys))
    else if j < i then
      .cons j (-y) (sub (.cons i x xs) ys)
    else
      let r := x - y
      if r = 0 then
        sub xs ys
      else
        .cons i r (sub xs ys)
termination_by sub xs ys => xs.size + ys.size

instance : Sub IntDict where sub := sub

theorem sub_def {xs ys : IntDict} : xs - ys = sub xs ys := rfl

@[simp] theorem sub_nil_left {ys : IntDict} : .nil - ys = -ys := by
  cases ys <;> rfl
@[simp] theorem sub_nil_right {xs : IntDict} : xs - .nil = xs := by
  cases xs <;> rfl

theorem sub_eq_add_neg : (xs ys : IntDict) → xs - ys = xs + -ys
  | .nil, _ => by rw [sub_nil_left, add_nil_left]
  | _, .nil => by rw [sub_nil_right, neg_nil, add_nil_right]
  | .cons i x xs, .cons j y ys => by
    rw [sub_def, sub, neg_cons, add_def, add]
    split
    · congr
      rw [← sub_def, ← add_def, sub_eq_add_neg xs (.cons j y ys), neg_cons]
    · split
      · congr
        rw [← sub_def, ← add_def, sub_eq_add_neg (.cons i x xs) ys]
      · rw [← sub_def, ← add_def, sub_eq_add_neg xs ys, Int.sub_eq_add_neg]
termination_by sub_eq_add_neg xs ys => xs.size + ys.size

@[simp] theorem dot_neg_left : (xs ys : IntDict) → (-xs).dot ys = -(xs.dot ys)
  | .nil, _ => by simp
  | _, .nil => by simp
  | .cons i x xs, .cons j y ys => by
    rw [neg_cons, dot, dot]
    split
    · rw [dot_neg_left xs (.cons j y ys)]
    · split
      · rw [← neg_cons, dot_neg_left (.cons i x xs) ys]
      · rw [dot_neg_left xs ys, Int.neg_add, Int.neg_mul]
termination_by dot_neg_left xs ys => xs.size + ys.size

/-- Computes a linear combination of two `IntDict`s, dropping any zero values. -/
def combo (a : Int) (xs : IntDict) (b : Int) (ys : IntDict) : IntDict :=
  if a = 0 then smul ys b else
  if b = 0 then smul xs a else
  match xs, ys with
  | .nil, _ => smul ys b
  | _, .nil => smul xs a
  | .cons i x xs, .cons j y ys =>
    if i < j then
      .cons i (a * x) (combo a xs b (.cons j y ys))
    else if j < i then
      .cons j (b * y) (combo a (.cons i x xs) b ys)
    else
      let r := a * x + b * y
      if r = 0 then
        combo a xs b ys
      else
        .cons i (a * x + b * y) (combo a xs b ys)
termination_by combo a xs b ys => xs.size + ys.size

def leading (xs : IntDict) : Int :=
  match xs with
  | .nil => 0
  | .cons _ 0 t => leading t
  | .cons _ x _ => x

theorem get_of_length_le {i : Nat} {xs : IntDict} (h : length xs ≤ i) : get xs i = 0 :=
  sorry

@[simp] theorem dot_set_left (xs ys : IntDict) (i : Nat) (z : Int) :
    dot (set xs i z) ys = dot xs ys + (z - get xs i) * get ys i := by
  sorry

@[simp] theorem dot_sdiv_left (xs ys : IntDict) {d : Int} (h : d ∣ xs.gcd) :
    dot (xs.sdiv d) ys = (dot xs ys) / d :=
  sorry

@[simp] theorem dot_smul_left (xs ys : IntDict) (i : Int) :
    dot (i * xs) ys = i * dot xs ys :=
  sorry

theorem dot_distrib_left (xs ys zs : IntDict) : (add xs ys).dot zs = xs.dot zs + ys.dot zs := by
  induction xs generalizing ys zs with
  | nil => sorry
  | cons i x xs ih => sorry

theorem combo_eq_smul_add_smul (a : Int) (xs : IntDict) (b : Int) (ys : IntDict) :
    combo a xs b ys = add (smul xs a) (smul ys b) :=
  sorry

theorem gcd_dvd_dot_left (xs ys : IntDict) : (gcd xs : Int) ∣ dot xs ys :=
  sorry

@[simp] theorem dot_zero_of_gcd_zero (xs ys : IntDict) (h : xs.gcd = 0) : dot xs ys = 0 := sorry

abbrev bmod (x : IntDict) (m : Nat) : IntDict := x.map (Int.bmod · m)

theorem bmod_length (x : IntDict) (m) : (bmod x m).length ≤ x.length := map_length _ _

abbrev bmod_dot_sub_dot_bmod (m : Nat) (a b : IntDict) : Int :=
    (Int.bmod (dot a b) m) - dot (bmod a m) b

theorem dvd_bmod_dot_sub_dot_bmod (m : Nat) : (xs ys : IntDict) →
    (m : Int) ∣ bmod_dot_sub_dot_bmod m xs ys
  | .nil, _ => sorry
  | _, .nil => sorry
  | .cons i x xs, .cons j y ys => by
    dsimp [bmod_dot_sub_dot_bmod]
    -- rw [bmod, map]
    rw [dot]
    split <;> rename_i h₁
    · rw [bmod, map]
      dsimp only
      split
      · exact dvd_bmod_dot_sub_dot_bmod m xs (.cons j y ys)
      · rw [dot]
        rw [if_pos h₁]
        exact dvd_bmod_dot_sub_dot_bmod m xs (.cons j y ys)
    · split
      · rw [bmod, map]
        dsimp only
        split
        · sorry
        · sorry
      · sorry


end IntDict
