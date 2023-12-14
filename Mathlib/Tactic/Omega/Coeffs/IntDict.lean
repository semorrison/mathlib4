import Mathlib.Tactic.Omega.IntDict
import Mathlib.Tactic.Omega.MinNatAbs

/-!
# `Coeffs` as a wrapper for `IntDict`

Currently `omega` uses a dense representation for coefficients.
However, we can swap this out for a sparse representation.

This file sets up `Coeffs` as a type synonym for `IntDict = AssocList Nat Int`,
and abbreviations for the functions in the `IntDict` namespace which we need to use in the
`omega` algorithm.

Some of the theorems we need here still need proofs,
but when they are ready we can swap out the representations simply by replacing an `import`.
-/

set_option autoImplicit true

namespace Std.Tactic.Omega

abbrev Coeffs := IntDict

namespace Coeffs

abbrev toList (xs : Coeffs) : List Int := IntDict.toList xs
abbrev ofList (xs : List Int) : Coeffs := IntDict.ofList xs
abbrev get (xs : Coeffs) (i : Nat) : Int := IntDict.get xs i
abbrev set (xs : Coeffs) (i : Nat) (y : Int) : IntDict := IntDict.set xs i y
abbrev gcd (xs : Coeffs) : Nat := IntDict.gcd xs
abbrev smul (xs : Coeffs) (g : Int) : Coeffs := IntDict.smul xs g
abbrev sdiv (xs : Coeffs) (g : Int) : Coeffs := IntDict.sdiv xs g
abbrev dot (xs ys : Coeffs) : Int := IntDict.dot xs ys
abbrev add (xs ys : Coeffs) : Coeffs := IntDict.add xs ys
abbrev sub (xs ys : Coeffs) : Coeffs := IntDict.sub xs ys
abbrev neg (xs : Coeffs) : Coeffs := IntDict.neg xs
abbrev combo (a : Int) (xs : Coeffs) (b : Int) (ys : Coeffs) : Coeffs := IntDict.combo a xs b ys
abbrev length (xs : Coeffs) := IntDict.length xs
abbrev leading (xs : Coeffs) : Int := IntDict.leading xs
def minNatAbs (xs : Coeffs) : Nat := xs.toList.minNatAbs -- FIXME
def maxNatAbs (xs : Coeffs) : Nat := xs.toList.minNatAbs -- FIXME
def findIdx? (xs : Coeffs) (p : Int → Bool) : Option Nat :=
  (·.1) <$> xs.findEntryP? fun _ x => p x

abbrev bmod_dot_sub_dot_bmod (m : Nat) (a b : Coeffs) : Int :=
  IntDict.bmod_dot_sub_dot_bmod m a b
abbrev bmod (x : Coeffs) (m : Nat) : Coeffs := IntDict.bmod x m
abbrev bmod_length (x : Coeffs) (m : Nat) : (bmod x m).length ≤ x.length :=
  IntDict.bmod_length x m
abbrev dvd_bmod_dot_sub_dot_bmod (m : Nat) (xs ys : Coeffs) :
    (m : Int) ∣ bmod_dot_sub_dot_bmod m xs ys := IntDict.dvd_bmod_dot_sub_dot_bmod m xs ys


@[simp] theorem ofList_get (xs : List Int) (i : Nat) : get (ofList xs) i = (xs.get? i |>.getD 0) := sorry

abbrev get_of_length_le {i : Nat} {xs : Coeffs} (h : length xs ≤ i) : get xs i = 0 :=
  IntDict.get_of_length_le h
abbrev dot_set_left (xs ys : Coeffs) (i : Nat) (z : Int) :
    dot (set xs i z) ys = dot xs ys + (z - get xs i) * get ys i :=
  IntDict.dot_set_left xs ys i z
abbrev dot_sdiv_left (xs ys : Coeffs) {d : Int} (h : d ∣ xs.gcd) :
    dot (xs.sdiv d) ys = (dot xs ys) / d :=
  IntDict.dot_sdiv_left xs ys h
abbrev dot_smul_left (xs ys : Coeffs) (i : Int) : dot (i * xs) ys = i * dot xs ys :=
  IntDict.dot_smul_left xs ys i
abbrev dot_distrib_left (xs ys zs : Coeffs) : (xs + ys).dot zs = xs.dot zs + ys.dot zs :=
  IntDict.dot_distrib_left xs ys zs
abbrev sub_eq_add_neg (xs ys : Coeffs) : xs - ys = xs + -ys :=
  IntDict.sub_eq_add_neg xs ys
abbrev combo_eq_smul_add_smul (a : Int) (xs : Coeffs) (b : Int) (ys : Coeffs) :
    combo a xs b ys = (a * xs) + (b * ys) :=
  IntDict.combo_eq_smul_add_smul a xs b ys
abbrev gcd_dvd_dot_left (xs ys : Coeffs) : (gcd xs : Int) ∣ dot xs ys :=
  IntDict.gcd_dvd_dot_left xs ys
abbrev map_length {xs : Coeffs} : (xs.map f).length ≤ xs.length :=
  sorry

abbrev dot_nil_right {xs : Coeffs} : dot xs .nil = 0 := IntDict.dot_nil_right
abbrev get_nil : get .nil i = 0 := IntDict.get_nil
abbrev dot_neg_left (xs ys : Coeffs) : dot (-xs) ys = -dot xs ys :=
  IntDict.dot_neg_left xs ys
