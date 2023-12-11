-- structure Coefficients where
--   coeffs : List Int
--   -- spec: first nonzero entry is nonnegative, and no trailing zeroes?
--   gcd : Nat := IntList.gcd coeffs
--   -- gcd_spec

--   -- TODO cache the hash
--   hash : UInt64 := Hashable.hash coeffs

--   minNatAbs : Nat := coeffs.minNatAbs
--   -- minNatAbs_spec

--   -- maxNatAbs : Nat := coeffs.map Int.natAbs |>.maximum? |>.getD 0
--   -- maxNatAbs_spec
-- deriving Repr

-- namespace Coefficients

-- instance : Ord Coefficients where
--   compare x y := compareOfLessAndEq x.coeffs y.coeffs

-- instance : BEq Coefficients where
--   beq x y := x.hash == y.hash && x.coeffs == y.coeffs

-- -- TODO remove the `DecidableEq` instance, which compares determined fields,
-- -- in favour of a `LawfulBEq` instance.

-- instance : ToString Coefficients where
--   toString c := " + ".intercalate <| c.coeffs.enum.map fun ⟨i, c⟩ => s!"{c} * x{i+1}"

-- abbrev eval (c : Coefficients) (v : List Int) : Int := IntList.dot c.coeffs v

-- instance : Hashable Coefficients := ⟨hash⟩

-- def div_gcd (c : Coefficients) : Coefficients :=
--   { coeffs := IntList.sdiv c.coeffs c.gcd |>.trim
--     gcd := 1
--     minNatAbs := c.minNatAbs / c.gcd }

-- end Coefficients
