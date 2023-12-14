import Mathlib.Tactic.Omega.IntList
import Mathlib.Tactic.Omega.MinNatAbs

/-!
# `Coeffs` as a wrapper for `IntList`

Currently `omega` uses a dense representation for coefficients.
However, we can swap this out for a sparse representation.

This file sets up `Coeffs` as a type synonym for `IntList`,
and abbreviations for the functions in the `IntList` namespace which we need to use in the
`omega` algorithm.

There is an equivalent file setting up `Coeffs` as a type synonym for `AssocList Nat Int`.
Not all the theorems about the algebraic operations on that representation have been proved yet.
When they are ready, we can replace the implementation in `omega` simply by importing
`Mathlib.Tactic.Omega.Coeffs.IntDict` instead of `Mathlib.Tactic.Omega.Coeffs.IntList`.

For small problems, the sparse representation is actually slightly slower,
so it is not urgent to make this replacement.
-/

set_option autoImplicit true

namespace Std.Tactic.Omega

abbrev Coeffs := IntList

namespace Coeffs

abbrev toList (xs : Coeffs) : List Int := xs
abbrev ofList (xs : List Int) : Coeffs := xs
abbrev set (xs : Coeffs) (i : Nat) (y : Int) : Coeffs := IntList.set xs i y
abbrev get (xs : Coeffs) (i : Nat) : Int := IntList.get xs i
abbrev gcd (xs : Coeffs) : Nat := IntList.gcd xs
abbrev smul (xs : Coeffs) (g : Int) : Coeffs := IntList.smul xs g
abbrev sdiv (xs : Coeffs) (g : Int) : Coeffs := IntList.sdiv xs g
abbrev dot (xs ys : Coeffs) : Int := IntList.dot xs ys
abbrev add (xs ys : Coeffs) : Coeffs := IntList.add xs ys
abbrev sub (xs ys : Coeffs) : Coeffs := IntList.sub xs ys
abbrev neg (xs : Coeffs) : Coeffs := IntList.neg xs
abbrev combo (a : Int) (xs : Coeffs) (b : Int) (ys : Coeffs) : Coeffs := IntList.combo a xs b ys
abbrev length (xs : Coeffs) := List.length xs
abbrev leading (xs : Coeffs) : Int := IntList.leading xs
abbrev map (f : Int → Int) (xs : Coeffs) : Coeffs := List.map f xs

abbrev bmod_dot_sub_dot_bmod (m : Nat) (a b : Coeffs) : Int :=
  IntList.bmod_dot_sub_dot_bmod m a b
abbrev bmod (x : Coeffs) (m : Nat) : Coeffs := IntList.bmod x m
abbrev bmod_length (x : Coeffs) (m : Nat) : (bmod x m).length ≤ x.length :=
  IntList.bmod_length x m
abbrev dvd_bmod_dot_sub_dot_bmod (m : Nat) (xs ys : Coeffs) :
    (m : Int) ∣ bmod_dot_sub_dot_bmod m xs ys := IntList.dvd_bmod_dot_sub_dot_bmod m xs ys

abbrev get_of_length_le {i : Nat} {xs : Coeffs} (h : length xs ≤ i) : get xs i = 0 :=
  IntList.get_of_length_le h
abbrev dot_set_left (xs ys : Coeffs) (i : Nat) (z : Int) :
    dot (set xs i z) ys = dot xs ys + (z - get xs i) * get ys i :=
  IntList.dot_set_left xs ys i z
abbrev dot_sdiv_left (xs ys : Coeffs) {d : Int} (h : d ∣ xs.gcd) :
    dot (xs.sdiv d) ys = (dot xs ys) / d :=
  IntList.dot_sdiv_left xs ys h
abbrev dot_smul_left (xs ys : Coeffs) (i : Int) : dot (i * xs) ys = i * dot xs ys :=
  IntList.dot_smul_left xs ys i
abbrev dot_distrib_left (xs ys zs : Coeffs) : (xs + ys).dot zs = xs.dot zs + ys.dot zs :=
  IntList.dot_distrib_left xs ys zs
abbrev sub_eq_add_neg (xs ys : Coeffs) : xs - ys = xs + -ys :=
  IntList.sub_eq_add_neg xs ys
abbrev combo_eq_smul_add_smul (a : Int) (xs : Coeffs) (b : Int) (ys : Coeffs) :
    combo a xs b ys = (a * xs) + (b * ys) :=
  IntList.combo_eq_smul_add_smul a xs b ys
abbrev gcd_dvd_dot_left (xs ys : Coeffs) : (gcd xs : Int) ∣ dot xs ys :=
  IntList.gcd_dvd_dot_left xs ys
abbrev map_length {xs : Coeffs} : (xs.map f).length ≤ xs.length :=
  Nat.le_of_eq (List.length_map xs f)

abbrev dot_nil_right {xs : Coeffs} : dot xs .nil = 0 := IntList.dot_nil_right
abbrev get_nil : get .nil i = 0 := IntList.get_nil
abbrev dot_neg_left (xs ys : IntList) : dot (-xs) ys = -dot xs ys :=
  IntList.dot_neg_left xs ys
