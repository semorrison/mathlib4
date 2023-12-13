import Std.Data.AssocList
import Std.Data.Int.Basic
import Std
import Mathlib.Tactic.ToExpr

open Std (AssocList)

set_option autoImplicit true
set_option relaxedAutoImplicit true

namespace Std.AssocList

instance : EmptyCollection (AssocList α β) where emptyCollection := .nil

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
deriving instance BEq for AssocList
deriving instance DecidableEq for AssocList
deriving instance Hashable for AssocList

deriving instance Repr for AssocList

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

def IntDict := AssocList Nat Int

namespace IntDict

deriving instance Lean.ToExpr for IntDict
deriving instance Hashable for IntDict

instance : BEq IntDict := inferInstanceAs <| BEq (AssocList Nat Int)
instance : LawfulBEq IntDict := inferInstanceAs <| LawfulBEq (AssocList Nat Int)
instance : DecidableEq IntDict := inferInstanceAs <| DecidableEq (AssocList Nat Int)
instance : EmptyCollection IntDict := inferInstanceAs <| EmptyCollection (AssocList Nat Int)
instance : Repr IntDict := inferInstanceAs <| Repr (AssocList Nat Int)

def ofList (xs : List Int) : IntDict := List.toAssocList xs.enum

partial def toList (xs : IntDict) : List Int :=
  go 0 xs
where
  go : Nat → IntDict → List Int
  | _, .nil => []
  | i, .cons j x t => if i < j then 0 :: go (i+1) (.cons j x t) else x :: go (i+1) t

instance : ToString IntDict where toString xs := toString xs.toList

def length (xs : IntDict) : Nat := xs.last?.map (·.1) |>.getD 0

def get (xs : IntDict) (i : Nat) : Int :=
  match xs with
  | .nil => 0
  | .cons j x t =>
    if i = j then x else if i < j then 0 else get t i

@[simp] theorem get_nil : get (.nil : IntDict) i = 0 := rfl

-- This is not tail recursive.
def set (xs : IntDict) (i : Nat) (y : Int) : IntDict :=
  match xs with
  | .nil => .cons i y .nil
  | .cons j x t =>
    if i = j then .cons j y t else if i < j then .cons i y xs else .cons j x (set t i y )

def gcd (xs : IntDict) : Nat :=
  xs.foldl (fun g _ x => Nat.gcd x.natAbs g) 0

def smul (xs : IntDict) (g : Int) : IntDict :=
  xs.mapVal fun _ x => g * x

instance : HMul Int IntDict IntDict where hMul i xs := smul xs i

def sdiv (xs : IntDict) (g : Int) : IntDict :=
  xs.mapVal fun _ x => x / g

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

def add (xs ys : IntDict) : IntDict :=
  match xs, ys with
  | .nil, _ => ys
  | _, .nil => xs
  | .cons i x xs, .cons j y ys =>
    if i < j then
      .cons i x (add xs (.cons j y ys))
    else if j < i then
      .cons j y (add (.cons i x xs) ys)
    else .cons i (x + y) (add xs ys)
termination_by add xs ys => xs.size + ys.size

instance : Add IntDict where add := add

theorem add_get {xs ys : IntDict} {i : Nat} : (xs + ys).get i = xs.get i + ys.get i := by
  sorry

theorem add_nil_left {ys : IntDict} : .nil + ys = ys := by
  cases ys <;> rfl
theorem add_nil_right {xs : IntDict} : xs + .nil = xs := by
  cases xs <;> rfl

def neg (xs : IntDict) : IntDict := xs.mapVal fun _ x => -x

instance : Neg IntDict where neg := neg

def sub (xs ys : IntDict) : IntDict :=
  match xs, ys with
  | .nil, _ => -ys
  | _, .nil => xs
  | .cons i x xs, .cons j y ys =>
    if i < j then
      .cons i x (sub xs (.cons j y ys))
    else if j < i then
      .cons j (-y) (sub (.cons i x xs) ys)
    else .cons i (x - y) (sub xs ys)
termination_by sub xs ys => xs.size + ys.size

instance : Sub IntDict where sub := sub

theorem sub_eq_add_neg (xs ys : IntDict) : xs - ys = xs + -ys := by
  induction xs generalizing ys with
  | nil => sorry
  | cons i x xs ih => sorry

@[simp] theorem dot_neg_left (xs ys : IntDict) : (-xs).dot ys = -(xs.dot ys) := by
  sorry

def combo (a : Int) (xs : IntDict) (b : Int) (ys : IntDict) : IntDict :=
  match xs, ys with
  | .nil, _ => smul ys b
  | _, .nil => smul xs a
  | .cons i x xs, .cons j y ys =>
    if i < j then
      .cons i (a * x) (combo a xs b (.cons j y ys))
    else if j < i then
      .cons j (b * y) (combo a (.cons i x xs) b ys)
    else .cons i (a * x + b * y) (combo a xs b ys)
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

-- theorem gcd_dvd (xs : IntDict) {a : Int} (m : a ∈ xs) : (xs.gcd : Int) ∣ a := by
--   sorry

-- theorem dvd_gcd (xs : IntDict) (c : Nat) (w : ∀ {a : Int}, a ∈ xs → (c : Int) ∣ a) :
--     c ∣ xs.gcd := by
--   sorry

-- theorem gcd_eq_iff (xs : IntDict) (g : Nat) :
--     xs.gcd = g ↔ (∀ {a : Int}, a ∈ xs → (g : Int) ∣ a) ∧ (∀ (c : Nat), (∀ {a : Int}, a ∈ xs → (c : Int) ∣ a) → c ∣ g) := by
--   sorry

-- @[simp] theorem gcd_eq_zero (xs : IntDict) : xs.gcd = 0 ↔ ∀ x ∈ xs, x = 0 := by
--   simp [gcd_eq_iff, Nat.dvd_zero]


end IntDict
