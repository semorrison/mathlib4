import Mathlib.Tactic.Omega.IntList
import Mathlib.Tactic.Omega.IntDict
import Mathlib.Tactic.Omega.Impl.MinNatAbs

open Std (HashMap RBSet RBMap AssocList)
open Lean (HashSet)

set_option autoImplicit true

abbrev Coeffs := IntList
abbrev Coeffs.toList (xs : Coeffs) : List Int := xs
abbrev Coeffs.ofList (xs : List Int) : Coeffs := xs
abbrev Coeffs.get (xs : Coeffs) (i : Nat) : Int := IntList.get xs i
abbrev Coeffs.set (xs : Coeffs) (i : Nat) (y : Int) : Coeffs := IntList.set xs i y
abbrev Coeffs.gcd (xs : Coeffs) : Nat := IntList.gcd xs
abbrev Coeffs.smul (xs : Coeffs) (g : Int) : Coeffs := IntList.smul xs g
abbrev Coeffs.sdiv (xs : Coeffs) (g : Int) : Coeffs := IntList.sdiv xs g
abbrev Coeffs.dot (xs ys : Coeffs) : Int := IntList.dot xs ys
abbrev Coeffs.add (xs ys : Coeffs) : Coeffs := IntList.add xs ys
abbrev Coeffs.sub (xs ys : Coeffs) : Coeffs := IntList.sub xs ys
abbrev Coeffs.neg (xs : Coeffs) : Coeffs := IntList.neg xs
abbrev Coeffs.combo (a : Int) (xs : Coeffs) (b : Int) (ys : Coeffs) : Coeffs := IntList.combo a xs b ys
abbrev Coeffs.length (xs : Coeffs) := List.length xs
abbrev Coeffs.leading (xs : Coeffs) : Int := IntList.leading xs
abbrev Coeffs.map (f : Int → Int) (xs : Coeffs) : Coeffs := List.map f xs

abbrev Coeffs.bmod_dot_sub_dot_bmod (m : Nat) (a b : Coeffs) : Int :=
  IntList.bmod_dot_sub_dot_bmod m a b
abbrev Coeffs.bmod (x : Coeffs) (m : Nat) : Coeffs := IntList.bmod x m
abbrev Coeffs.bmod_length (x : Coeffs) (m : Nat) : (bmod x m).length = x.length :=
  IntList.bmod_length x m
abbrev Coeffs.dvd_bmod_dot_sub_dot_bmod (m : Nat) (xs ys : Coeffs) :
    (m : Int) ∣ bmod_dot_sub_dot_bmod m xs ys := IntList.dvd_bmod_dot_sub_dot_bmod m xs ys


abbrev Coeffs.get_of_length_le {i : Nat} {xs : Coeffs} (h : Coeffs.length xs ≤ i) :
    Coeffs.get xs i = 0 :=
  IntList.get_of_length_le h
abbrev Coeffs.dot_set_left (xs ys : Coeffs) (i : Nat) (z : Int) :
    Coeffs.dot (Coeffs.set xs i z) ys =
      Coeffs.dot xs ys + (z - Coeffs.get xs i) * Coeffs.get ys i :=
  IntList.dot_set_left xs ys i z
abbrev Coeffs.dot_sdiv_left (xs ys : Coeffs) {d : Int} (h : d ∣ xs.gcd) :
    dot (xs.sdiv d) ys = (dot xs ys) / d :=
  IntList.dot_sdiv_left xs ys h
abbrev Coeffs.dot_smul_left (xs ys : Coeffs) (i : Int) :
    Coeffs.dot (i * xs) ys = i * Coeffs.dot xs ys :=
  IntList.dot_smul_left xs ys i
abbrev Coeffs.dot_distrib_left (xs ys zs : Coeffs) : (xs + ys).dot zs = xs.dot zs + ys.dot zs :=
  IntList.dot_distrib_left xs ys zs
abbrev Coeffs.sub_eq_add_neg (xs ys : Coeffs) :
    xs - ys = xs + -ys :=
  IntList.sub_eq_add_neg xs ys
abbrev Coeffs.combo_eq_smul_add_smul (a : Int) (xs : Coeffs) (b : Int) (ys : Coeffs) :
    Coeffs.combo a xs b ys = (a * xs) + (b * ys) :=
  IntList.combo_eq_smul_add_smul a xs b ys
abbrev Coeffs.gcd_dvd_dot_left (xs ys : Coeffs) : (Coeffs.gcd xs : Int) ∣ Coeffs.dot xs ys :=
  IntList.gcd_dvd_dot_left xs ys
abbrev Coeffs.map_length {xs : Coeffs} : (xs.map f).length = xs.length :=
  List.length_map xs f

abbrev Coeffs.dot_nil_right {xs : Coeffs} : dot xs .nil = 0 := IntList.dot_nil_right
abbrev Coeffs.get_nil : get .nil i = 0 := IntList.get_nil
abbrev Coeffs.dot_neg_left (xs ys : IntList) : dot (-xs) ys = -dot xs ys :=
  IntList.dot_neg_left xs ys

-- abbrev Coeffs := IntDict
-- abbrev Coeffs.toList (xs : Coeffs) : List Int := IntDict.toList xs
-- abbrev Coeffs.ofList (xs : List Int) : Coeffs := IntDict.ofList xs
-- abbrev Coeffs.get (xs : Coeffs) (i : Nat) : Int := IntDict.get xs i
-- abbrev Coeffs.set (xs : Coeffs) (i : Nat) (y : Int) : IntDict := IntDict.set xs i y
-- abbrev Coeffs.gcd (xs : Coeffs) : Nat := IntDict.gcd xs
-- abbrev Coeffs.smul (xs : Coeffs) (g : Int) : Coeffs := IntDict.smul xs g
-- abbrev Coeffs.sdiv (xs : Coeffs) (g : Int) : Coeffs := IntDict.sdiv xs g
-- abbrev Coeffs.dot (xs ys : Coeffs) : Int := IntDict.dot xs ys
-- abbrev Coeffs.add (xs ys : Coeffs) : Coeffs := IntDict.add xs ys
-- abbrev Coeffs.sub (xs ys : Coeffs) : Coeffs := IntDict.sub xs ys
-- abbrev Coeffs.neg (xs : Coeffs) : Coeffs := IntDict.neg xs
-- abbrev Coeffs.combo (a : Int) (xs : Coeffs) (b : Int) (ys : Coeffs) : Coeffs := IntDict.combo a xs b ys
-- abbrev Coeffs.length (xs : Coeffs) := IntDict.length xs
-- abbrev Coeffs.leading (xs : Coeffs) : Int := IntDict.leading xs
-- def Coeffs.minNatAbs (xs : Coeffs) : Nat := xs.toList.minNatAbs -- FIXME
-- def Coeffs.maxNatAbs (xs : Coeffs) : Nat := xs.toList.minNatAbs -- FIXME
-- def Coeffs.findIdx? (xs : Coeffs) (p : Int → Bool) : Option Nat :=
--   (·.1) <$> xs.findEntryP? fun _ x => p x

-- abbrev Coeffs.bmod_dot_sub_dot_bmod (m : Nat) (a b : Coeffs) : Int :=
--   IntDict.bmod_dot_sub_dot_bmod m a b
-- abbrev Coeffs.bmod (x : Coeffs) (m : Nat) : Coeffs := IntDict.bmod x m
-- abbrev Coeffs.bmod_length (x : Coeffs) (m : Nat) : (bmod x m).length = x.length :=
--   IntDict.bmod_length x m
-- abbrev Coeffs.dvd_bmod_dot_sub_dot_bmod (m : Nat) (xs ys : Coeffs) :
--     (m : Int) ∣ bmod_dot_sub_dot_bmod m xs ys := IntDict.dvd_bmod_dot_sub_dot_bmod m xs ys


-- @[simp] theorem Coeffs.ofList_get (xs : List Int) (i : Nat) : get (ofList xs) i = (xs.get? i |>.getD 0) := sorry

-- abbrev Coeffs.get_of_length_le {i : Nat} {xs : Coeffs} (h : Coeffs.length xs ≤ i) :
--     Coeffs.get xs i = 0 :=
--   IntDict.get_of_length_le h
-- abbrev Coeffs.dot_set_left (xs ys : Coeffs) (i : Nat) (z : Int) :
--     Coeffs.dot (Coeffs.set xs i z) ys =
--       Coeffs.dot xs ys + (z - Coeffs.get xs i) * Coeffs.get ys i :=
--   IntDict.dot_set_left xs ys i z
-- abbrev Coeffs.dot_sdiv_left (xs ys : Coeffs) {d : Int} (h : d ∣ xs.gcd) :
--     dot (xs.sdiv d) ys = (dot xs ys) / d :=
--   IntDict.dot_sdiv_left xs ys h
-- abbrev Coeffs.dot_smul_left (xs ys : Coeffs) (i : Int) :
--     Coeffs.dot (i * xs) ys = i * Coeffs.dot xs ys :=
--   IntDict.dot_smul_left xs ys i
-- abbrev Coeffs.dot_distrib_left (xs ys zs : Coeffs) : (xs + ys).dot zs = xs.dot zs + ys.dot zs :=
--   IntDict.dot_distrib_left xs ys zs
-- abbrev Coeffs.sub_eq_add_neg (xs ys : Coeffs) :
--     xs - ys = xs + -ys :=
--   IntDict.sub_eq_add_neg xs ys
-- abbrev Coeffs.combo_eq_smul_add_smul (a : Int) (xs : Coeffs) (b : Int) (ys : Coeffs) :
--     Coeffs.combo a xs b ys = (a * xs) + (b * ys) :=
--   IntDict.combo_eq_smul_add_smul a xs b ys
-- abbrev Coeffs.gcd_dvd_dot_left (xs ys : Coeffs) : (Coeffs.gcd xs : Int) ∣ Coeffs.dot xs ys :=
--   IntDict.gcd_dvd_dot_left xs ys
-- abbrev Coeffs.map_length {xs : Coeffs} : (xs.map f).length = xs.length :=
--   sorry

-- abbrev Coeffs.dot_nil_right {xs : Coeffs} : dot xs .nil = 0 := IntDict.dot_nil_right
-- abbrev Coeffs.get_nil : get .nil i = 0 := IntDict.get_nil
-- abbrev Coeffs.dot_neg_left (xs ys : Coeffs) : dot (-xs) ys = -dot xs ys :=
--   IntDict.dot_neg_left xs ys
