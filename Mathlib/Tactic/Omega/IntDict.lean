import Std.Data.AssocList

open Std (AssocList)

set_option autoImplicit true

namespace Std.AssocList

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

end Std.AssocList

def IntDict := AssocList Nat Int

namespace IntDict

def length (xs : IntDict) : Nat := xs.last?.map (·.1) |>.getD 0

def get (xs : IntDict) (i : Nat) : Int :=
  match xs with
  | .nil => 0
  | .cons j x t =>
    if i = j then x else if i < j then 0 else get t i

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

end IntDict

-- abbrev Coeffs := IntList
-- abbrev Coeffs.get (xs : Coeffs) (i : Nat) : Int := IntList.get xs i
-- abbrev Coeffs.set (xs : Coeffs) (i : Nat) (y : Int) : IntList := IntList.set xs i y
-- abbrev Coeffs.gcd (xs : Coeffs) : Nat := IntList.gcd xs
-- abbrev Coeffs.smul (xs : Coeffs) (g : Int) : Coeffs := IntList.smul xs g
-- abbrev Coeffs.sdiv (xs : Coeffs) (g : Int) : Coeffs := IntList.sdiv xs g
-- abbrev Coeffs.dot (xs ys : Coeffs) : Int := IntList.dot xs ys
-- abbrev Coeffs.combo (a : Int) (xs : Coeffs) (b : Int) (ys : Coeffs) : Coeffs := IntList.combo a xs b ys
-- abbrev Coeffs.length (xs : Coeffs) := List.length xs

-- abbrev Coeffs.get_of_length_le {i : Nat} {xs : Coeffs} (h : Coeffs.length xs ≤ i) :
--     Coeffs.get xs i = 0 :=
--   IntList.get_of_length_le h
-- abbrev Coeffs.dot_set_left (xs ys : Coeffs) (i : Nat) (z : Int) :
--     Coeffs.dot (Coeffs.set xs i z) ys =
--       Coeffs.dot xs ys + (z - Coeffs.get xs i) * Coeffs.get ys i :=
--   IntList.dot_set_left xs ys i z
-- abbrev Coeffs.dot_sdiv_left (xs ys : Coeffs) {d : Int} (h : d ∣ xs.gcd) :
--     dot (xs.sdiv d) ys = (dot xs ys) / d :=
--   IntList.dot_sdiv_left xs ys h
-- abbrev Coeffs.dot_smul_left (xs ys : Coeffs) (i : Int) :
--     Coeffs.dot (i * xs) ys = i * Coeffs.dot xs ys :=
--   IntList.dot_smul_left xs ys i
-- abbrev Coeffs.dot_distrib_left (xs ys zs : Coeffs) : (xs + ys).dot zs = xs.dot zs + ys.dot zs :=
--   IntList.dot_distrib_left xs ys zs
-- abbrev Coeffs.combo_eq_smul_add_smul (a : Int) (xs : Coeffs) (b : Int) (ys : Coeffs) :
--     Coeffs.combo a xs b ys = a * xs + b * ys :=
--   IntList.combo_eq_smul_add_smul a xs b ys
-- abbrev Coeffs.gcd_dvd_dot_left (xs ys : Coeffs) : (Coeffs.gcd xs : Int) ∣ Coeffs.dot xs ys :=
--   IntList.gcd_dvd_dot_left xs ys
