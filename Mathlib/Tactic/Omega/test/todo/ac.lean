-- TODO: AC normalization in atoms
-- example (u v r s t : Int) (h : 0 < u*(t*v + t*r + s)) : 0 < (t*(r + v) + s)*3*u := by
--   simp only [Int.add_mul, Int.mul_add] at *
--   omega

-- example (A B : Int) (h : 0 < A * B) : 0 < 8 * A * B := by omega

-- example (A B : Int) (h : 0 < A * B) : 0 < A * 8 * B := by omega

-- example (A B : Nat) (h : 0 < A * B) : 0 < 8 * A * B := by omega

-- example (A B : Nat) (h : 0 < A * B) : 0 < A * 8 * B := by omega

-- example (u v r s t : Int) (h : 0 < u*(t*v + t*r + s)) :
--     0 < (t*(r + v) + s)*3*u := by omega

-- TODO Not sure what we want to do with this, it's a trickier one!
-- example (A B : Int) (h : 0 < A * B) : 0 < A/8*B := by omega
