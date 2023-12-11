import Mathlib.Tactic.Omega.Impl2.Frontend

open Omega ProofProducing

example : True := by
  fail_if_success omega
  trivial

example (_ : (1 : Int) < (0 : Int)) : False := by omega

example (_ : (0 : Int) < (0 : Int)) : False := by omega
example (_ : (0 : Int) < (1 : Int)) : True := by (fail_if_success omega); trivial

example {x : Int} (_ : 0 ≤ x) (_ : x ≤ 1) : True := by (fail_if_success omega); trivial
example {x : Int} (_ : 0 ≤ x) (_ : x ≤ -1) : False := by omega

example {x : Int} (_ : x % 2 < x - 2 * (x / 2)) : False := by omega
example {x : Int} (_ : x % 2 > 5) : False := by omega

example {x : Int} (_ : 2 * (x / 2) > x) : False := by omega
example {x : Int} (_ : 2 * (x / 2) ≤ x - 2) : False := by omega

example (_ : 7 < 3) : False := by omega
example (_ : 0 < 0) : False := by omega

example {x : Nat} (_ : x > 7) (_ : x < 3) : False := by omega
example {x : Nat} (_ : x ≥ 7) (_ : x ≤ 3) : False := by omega
example {x y : Nat} (_ : x + y > 10) (_ : x < 5) (_ : y < 5) : False := by omega

example {x y : Int} (_ : x + y > 10) (_ : 2 * x < 5) (_ : y < 5) : False := by omega
example {x y : Nat} (_ : x + y > 10) (_ : 2 * x < 5) (_ : y < 5) : False := by omega

example {x y : Int} (_ : 2 * x + 4 * y = 5) : False := by omega
example {x y : Nat} (_ : 2 * x + 4 * y = 5) : False := by omega

example {x y : Int} (_ : 6 * x + 7 * y = 5) : True := by (fail_if_success omega); trivial

example {x y : Nat} (_ : 6 * x + 7 * y = 5) : False := by omega

example {x : Nat} (_ : x < 0) : False := by omega

example {x y z : Int} (_ : x + y > z) (_ : x < 0) (_ : y < 0) (_ : z > 0) : False := by omega

example {x y : Nat} (_ : x - y = 0) (_ : x > y) : False := by omega

example {x y z : Int} (_ : x - y - z = 0) (_ : x > y + z) : False := by omega

example {x y z : Nat} (_ : x - y - z = 0) (_ : x > y + z) : False := by omega

example {a b c d e f : Nat} (_ : a - b - c - d - e - f = 0) (_ : a > b + c + d + e + f) : False := by
  omega

example {x y : Nat} (h₁ : x - y ≤ 0) (h₂ : y < x) : False := by omega

example {x y : Int} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by omega

example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by omega

example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 4) : False := by omega

example {x y : Nat} (_ : x / 2 - y / 3 < x % 2) (_ : 3 * x ≥ 2 * y + 4) : False := by omega

example {x : Int} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by omega

example {x : Nat} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by omega

example {x : Nat} (h₁ : x / 3 ≥ 2) (h₂ : x < 6) : False := by omega

example {x : Int} {y : Nat} (_ : 0 < x) (_ : x + y ≤ 0) : False := by omega

example {a b c : Nat} (_ : a - (b - c) ≤ 5) (_ : b ≥ c + 3) (_ : a + c ≥ b + 6) : False := by omega

example {x y : Nat} (h1 : x / 2 - y / 3 < x % 2) (h2 : 3 * x ≥ 2 * y + 4) : False := by omega

example {x : Nat} : 1 < (1 + ((x + 1 : Nat) : Int) + 2) / 2 := by omega

example {x : Nat} : (x + 4) / 2 ≤ x + 2 := by omega

example {x : Int} {m : Nat} (_ : 0 < m) (_ : ¬x % ↑m < (↑m + 1) / 2) : -↑m / 2 ≤ x % ↑m - ↑m := by
  omega


example (h : (7 : Int) = 0) : False := by omega

example (h : (7 : Int) ≤ 0) : False := by omega

example (h : (-7 : Int) + 14 = 0) : False := by omega

example (h : (-7 : Int) + 14 ≤ 0) : False := by omega

example (h : (1 : Int) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 0) : False := by
  omega

example (h : (7 : Int) - 14 = 0) : False := by omega

example (h : (14 : Int) - 7 ≤ 0) : False := by omega

example (h : (1 : Int) - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 - 1 + 1 = 0) : False := by
  omega

example (h : -(7 : Int) = 0) : False := by omega

example (h : -(-7 : Int) ≤ 0) : False := by omega

example (h : 2 * (7 : Int) = 0) : False := by omega

example (h : (7 : Int) < 0) : False := by omega

example {x : Int} (h : x + x + 1 = 0) : False := by omega

example {x : Int} (h : 2 * x + 1 = 0) : False := by omega

example {x y : Int} (h : x + x + y + y + 1 = 0) : False := by omega

example {x y : Int} (h : 2 * x + 2 * y + 1 = 0) : False := by omega

example {x : Int} (h₁ : 0 ≤ -7 + x) (h₂ : 0 ≤ 3 - x) : False := by omega

example {x : Int} (h₁ : 0 ≤ -7 + x) (h₂ : 0 < 4 - x) : False := by omega

example {x : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : 2 * x + 1 ≤ 0) : False := by omega

example {x : Int} (h₁ : 0 < 2 * x + 2) (h₂ : 2 * x + 1 ≤ 0) : False := by omega

example {x y : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : x = y) (h₃ : 2 * y + 1 ≤ 0) : False := by omega

example {x y z : Int} (h₁ : 0 ≤ 2 * x + 1) (h₂ : x = y) (h₃ : y = z) (h₄ : 2 * z + 1 ≤ 0) :
    False := by omega

example {x1 x2 x3 x4 x5 x6 : Int} (h : 0 ≤ 2 * x1 + 1) (h : x1 = x2) (h : x2 = x3) (h : x3 = x4)
    (h : x4 = x5) (h : x5 = x6) (h : 2 * x6 + 1 ≤ 0) : False := by omega

example {x : Int} (_ : 1 ≤ -3 * x) (_ : 1 ≤ 2 * x) : False := by omega

example {x y : Int} (_ : 2 * x + 3 * y = 0) (_ : 1 ≤ x) (_ : 1 ≤ y) : False := by omega

example {x y z : Int} (_ : 2 * x + 3 * y + 4 * z = 0) (_ : 1 ≤ x + y) (_ : 1 ≤ y + z)
    (_ : 1 ≤ x + z) : False := by omega

example {x y : Int} (_ : 1 ≤ 3 * x) (_ : y ≤ 2) (_ : 6 * x - 2 ≤ y) : False := by omega

example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : 1 ≤ x) : False := by omega
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : x ≥ 1) : False := by omega
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : 0 < x) : False := by omega
example {x y : Int} (_ : y = x) (_ : 0 ≤ x - 2 * y) (_ : x - 2 * y ≤ 1) (_ : x > 0) : False := by omega

example {x y : Nat} (_ : 5 ∣ x) (_ : ¬ 10 ∣ x) (_ : y = 7) (_ : x - y ≤ 2) (_ : x ≥ 6) : False := by omega

-- theorem omega_nightmare {x y : Int} (_ : 3 ≤ 11 * x + 13 * y) (_ : 11 * x + 13 * y ≤ 21)
--     (_ : -8 ≤ 7 * x - 9 * y) (_ : 7 * x - 9 * y ≤ 6) : False := by
--   -- omega -- need to implement the shadows before we can do this!
--   sorry

example {n : Nat} (_ : n > 0) : (2*n - 1) % 2 = 1 := by omega

example (x : Int) (_ : x > 0 ∧ x < -1) : False := by omega
example (x : Int) (_ : x > 7) : x < 0 ∨ x > 3 := by omega

example (a b c d e : Int)
    (ha : 2 * a + b + c + d + e = 4)
    (hb : a + 2 * b + c + d + e = 5)
    (hc : a + b + 2 * c + d + e = 6)
    (hd : a + b + c + 2 * d + e = 7)
    (he : a + b + c + d + 2 * e = 8) : e = 3 := by omega

--- Adapting tests from `linarith`.

example {a b : Int} (h : a < b) (w : b < a) : False := by omega

example {a b c : Int}
    (h : a < 0) (_ : ¬b = 0) (_ : c = 0) (_ : (1 - a) * (b * b) ≤ 0) (_ : 0 ≤ 0)
    (_ : -(a * -b * -b + b * -b + 0) = (1 - a) * (b * b)) (_ : (1 - a) * (b * b) ≤ 0) :
    0 < 1 - a := by
  omega

example (_e b c a v0 v1 : Int) (_h1 : v0 = 5*a) (_h2 : v1 = 3*b) (h3 : v0 + v1 + c = 10) :
    v0 + 5 + (v1 - 3) + (c - 2) = 10 := by omega

example (h : (1 : Int) < 0) (_ : ¬ (37 : Int) < 42) (_ : True) (_ : (-7 : Int) < 5) :
    (3 : Int) < 7 := by omega

-- TODO: AC normalization in atoms
-- example (u v r s t : Int) (h : 0 < u*(t*v + t*r + s)) : 0 < (t*(r + v) + s)*3*u := by
--   simp only [Int.add_mul, Int.mul_add] at *
--   omega

example (A B : Int) (h : 0 < A * B) : 0 < 8 * (A * B) := by omega

-- example (A B : Int) (h : 0 < A * B) : 0 < 8 * A * B := by omega

-- example (A B : Int) (h : 0 < A * B) : 0 < A * 8 * B := by omega

-- example (A B : Nat) (h : 0 < A * B) : 0 < 8 * A * B := by omega

-- example (A B : Nat) (h : 0 < A * B) : 0 < A * 8 * B := by omega

-- example (u v r s t : Int) (h : 0 < u*(t*v + t*r + s)) :
--     0 < (t*(r + v) + s)*3*u := by omega

example (A B : Nat) (h : 7 < A * B) : 0 < A*B/8 := by omega
example (A B : Int) (h : 7 < A * B) : 0 < A*B/8 := by omega

-- TODO Not sure what we want to do with this, it's a trickier one!
-- example (A B : Rat) (h : 0 < A * B) : 0 < A/8*B := by omega

example (ε : Int) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε := by omega

example (x y z : Int) (h1 : 2*x < 3*y) (h2 : -4*x + z/2 < 0) (h3 : 12*y - z < 0) : False := by omega

example (ε : Int) (h1 : ε > 0) : ε / 2 < ε := by omega

example (ε : Int) (_ : ε > 0) : ε - 2 ≤ ε / 3 + ε / 3 + ε / 3 := by omega
example (ε : Int) (_ : ε > 0) : ε / 3 + ε / 3 + ε / 3 ≤ ε := by omega
example (ε : Int) (_ : ε > 0) : ε - 2 ≤ ε / 3 + ε / 3 + ε / 3 ∧ ε / 3 + ε / 3 + ε / 3 ≤ ε := by
  omega

example (x : Int) (h : 0 < x) : 0 < x / 1 := by omega

-- TODO needs fixing?
-- example (x : Int) (h : x < 0) : 0 < x/(-1) := by omega

-- example (x : Int) (h : x < -1) : 0 < x/(-2) := by omega

example (x : Int) (h : 5 < x) : 0 < x/2/3 := by omega

-- TODO do we want to handle this?
-- example (x : Int) (h : 1 < x) : 0 < x/(4/2) := by omega

example (_a b _c : Nat) (h2 : b + 2 > 3 + b) : False := by omega
example (_a b _c : Int) (h2 : b + 2 > 3 + b) : False := by omega

example (g v V c h : Int) (_ : h = 0) (_ : v = V) (_ : V > 0) (_ : g > 0)
    (_ : 0 ≤ c) (_ : c < 1) : v ≤ V := by omega

example (x y z : Int) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0) (h3 : 12*y - 4* z < 0) : False := by
  omega

example (x y z : Int) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0) (_h3 : x*y < 5) (h3 : 12*y - 4* z < 0) :
    False := by omega

example (a b c : Int) (h1 : a > 0) (h2 : b > 5) (h3 : c < -10) (h4 : a + b - c < 3) : False := by
  omega

example (_ b _ : Int) (h2 : b > 0) (h3 : ¬ b ≥ 0) : False := by
  omega

example (x y z : Int) (hx : x ≤ 3*y) (h2 : y ≤ 2*z) (h3 : x ≥ 6*z) : x = 3*y := by
  omega

example (x y z : Int) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0) (_h3 : x*y < 5) : ¬ 12*y - 4* z < 0 := by
  omega

example (x y z : Int) (hx : ¬ x > 3*y) (h2 : ¬ y > 2*z) (h3 : x ≥ 6*z) : x = 3*y := by
  omega

example (x y : Int) (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3) (h' : (x + 4) * x ≥ 0)
    (h'' : (6 + 3 * y) * y ≥ 0) : False := by omega

example (a : Int) (ha : 0 ≤ a) : 0 * 0 ≤ 2 * a := by omega

example (x y : Int) (h : x < y) : x ≠ y := by omega

example (x y : Int) (h : x < y) : ¬ x = y := by omega

example (x : Int) : id x ≥ x := by omega

example (prime : Nat → Prop) (x y z : Int) (h1 : 2*x + ((-3)*y) < 0) (h2 : (-4)*x + 2*z < 0) (h3 : 12*y + (-4)* z < 0)
    (_ : prime 7) : False := by omega

example (i n : Nat) (h : (2 : Int) ^ i ≤ 2 ^ n) : (0 : Int) ≤ 2 ^ n - 2 ^ i := by omega

-- Check we use `exfalso` on non-comparison goals.
example (prime : Nat → Prop) (_ b _ : Nat) (h2 : b > 0) (h3 : b < 0) : prime 10 := by
  omega

example (a b c : Nat) (h2 : (2 : Nat) > 3)  : a + b - c ≥ 3 := by omega

-- Verify that we split conjunctions in hypotheses.
example (x y : Int)
    (h : 6 + ((x + 4) * x + (6 + 3 * y) * y) = 3 ∧ (x + 4) * x ≥ 0 ∧ (6 + 3 * y) * y ≥ 0) :
    False := by omega

example (mess : Nat → Nat) (S n : Nat) :
    mess S + (n * mess S + n * 2 + 1) < n * mess S + mess S + (n * 2 + 2) := by omega

example (p n p' n' : Nat) (h : p + n' = p' + n) : n + p' = n' + p := by
  omega

example (a b c : Int) (h1 : 32 / a < b) (h2 : b < c) : 32 / a < c := by omega

-- This would need a nonlinear preprocessor, as nlinarith is for linarith
-- example (u v x y A B : Int)
-- (a : 0 < A)
-- (a_1 : 0 <= 1 - A)
-- (a_2 : 0 <= B - 1)
-- (a_3 : 0 <= B - x)
-- (a_4 : 0 <= B - y)
-- (a_5 : 0 <= u)
-- (a_6 : 0 <= v)
-- (a_7 : 0 < A - u)
-- (a_8 : 0 < A - v) :
--  u * y + v * x + u * v < 3 * A * B :=
--  by omega

-- example (u v x y A B : Int) : (0 < A) → (A ≤ 1) → (1 ≤ B)
-- → (x ≤ B) → (y ≤ B)
-- → (0 ≤ u ) → (0 ≤ v )
-- → (u < A) → (v < A)
-- → (u * y + v * x + u * v < 3 * A * B) := by
--   intros
--   omega

-- example (u v x y A B : Int)
-- (a_7 : 0 < A - u)
-- (a_8 : 0 < A - v) :
-- (0 <= A * (1 - A))
-- -> (0 <= A * (B - 1))
-- -> (0 < A * (A - u))
-- -> (0 <= (B - 1) * (A - u))
-- -> (0 <= (B - 1) * (A - v))
-- -> (0 <= (B - x) * v)
-- -> (0 <= (B - y) * u)
-- -> (0 <= u * (A - v))
-- ->
--  u * y + v * x + u * v < 3 * A * B := by
--   intros
--   omega

-- example (u v x y A B : Int)
-- (a : 0 < A)
-- (a_1 : 0 <= 1 - A)
-- (a_2 : 0 <= B - 1)
-- (a_3 : 0 <= B - x)
-- (a_4 : 0 <= B - y)
-- (a_5 : 0 <= u)
-- (a_6 : 0 <= v)
-- (a_7 : 0 < A - u)
-- (a_8 : 0 < A - v) :
--  (0 < A * A)
-- -> (0 <= A * (1 - A))
-- -> (0 <= A * (B - 1))
-- -> (0 <= A * (B - x))
-- -> (0 <= A * (B - y))
-- -> (0 <= A * u)
-- -> (0 <= A * v)
-- -> (0 < A * (A - u))
-- -> (0 < A * (A - v))
-- -> (0 <= (1 - A) * A)
-- -> (0 <= (1 - A) * (1 - A))
-- -> (0 <= (1 - A) * (B - 1))
-- -> (0 <= (1 - A) * (B - x))
-- -> (0 <= (1 - A) * (B - y))
-- -> (0 <= (1 - A) * u)
-- -> (0 <= (1 - A) * v)
-- -> (0 <= (1 - A) * (A - u))
-- -> (0 <= (1 - A) * (A - v))
-- -> (0 <= (B - 1) * A)
-- -> (0 <= (B - 1) * (1 - A))
-- -> (0 <= (B - 1) * (B - 1))
-- -> (0 <= (B - 1) * (B - x))
-- -> (0 <= (B - 1) * (B - y))
-- -> (0 <= (B - 1) * u)
-- -> (0 <= (B - 1) * v)
-- -> (0 <= (B - 1) * (A - u))
-- -> (0 <= (B - 1) * (A - v))
-- -> (0 <= (B - x) * A)
-- -> (0 <= (B - x) * (1 - A))
-- -> (0 <= (B - x) * (B - 1))
-- -> (0 <= (B - x) * (B - x))
-- -> (0 <= (B - x) * (B - y))
-- -> (0 <= (B - x) * u)
-- -> (0 <= (B - x) * v)
-- -> (0 <= (B - x) * (A - u))
-- -> (0 <= (B - x) * (A - v))
-- -> (0 <= (B - y) * A)
-- -> (0 <= (B - y) * (1 - A))
-- -> (0 <= (B - y) * (B - 1))
-- -> (0 <= (B - y) * (B - x))
-- -> (0 <= (B - y) * (B - y))
-- -> (0 <= (B - y) * u)
-- -> (0 <= (B - y) * v)
-- -> (0 <= (B - y) * (A - u))
-- -> (0 <= (B - y) * (A - v))
-- -> (0 <= u * A)
-- -> (0 <= u * (1 - A))
-- -> (0 <= u * (B - 1))
-- -> (0 <= u * (B - x))
-- -> (0 <= u * (B - y))
-- -> (0 <= u * u)
-- -> (0 <= u * v)
-- -> (0 <= u * (A - u))
-- -> (0 <= u * (A - v))
-- -> (0 <= v * A)
-- -> (0 <= v * (1 - A))
-- -> (0 <= v * (B - 1))
-- -> (0 <= v * (B - x))
-- -> (0 <= v * (B - y))
-- -> (0 <= v * u)
-- -> (0 <= v * v)
-- -> (0 <= v * (A - u))
-- -> (0 <= v * (A - v))
-- -> (0 < (A - u) * A)
-- -> (0 <= (A - u) * (1 - A))
-- -> (0 <= (A - u) * (B - 1))
-- -> (0 <= (A - u) * (B - x))
-- -> (0 <= (A - u) * (B - y))
-- -> (0 <= (A - u) * u)
-- -> (0 <= (A - u) * v)
-- -> (0 < (A - u) * (A - u))
-- -> (0 < (A - u) * (A - v))
-- -> (0 < (A - v) * A)
-- -> (0 <= (A - v) * (1 - A))
-- -> (0 <= (A - v) * (B - 1))
-- -> (0 <= (A - v) * (B - x))
-- -> (0 <= (A - v) * (B - y))
-- -> (0 <= (A - v) * u)
-- -> (0 <= (A - v) * v)
-- -> (0 < (A - v) * (A - u))
-- -> (0 < (A - v) * (A - v))
-- ->
--  u * y + v * x + u * v < 3 * A * B := by
--   intros
--   omega

-- example (A B : Int) : (0 < A) → (1 ≤ B) → (0 < A / 8 * B) := by
--   intros
--   nlinarith

-- example (x y : Int) : 0 ≤ x ^2 + y ^2 := by
--   nlinarith

-- example (x y : Int) : 0 ≤ x*x + y*y := by
--   nlinarith

-- example (x y : Int) : x = 0 → y = 0 → x*x + y*y = 0 := by
--   intros
--   nlinarith

-- theorem norm_eq_zero_iff {x y : Int} : x * x + y * y = 0 ↔ x = 0 ∧ y = 0 := by
--   constructor
--   · intro
--     constructor <;> omega
--   · intro; omega

-- theorem norm_zero_left {x y : Int} (h1 : x * x + y * y = 0) : x = 0 := by
--   omega

-- theorem norm_nonpos_right {x y : Int} (h1 : x * x + y * y ≤ 0) : y = 0 := by
--   omega

-- theorem norm_nonpos_left (x y : Int) (h1 : x * x + y * y ≤ 0) : x = 0 := by
--   omega

-- example (p q r s t u v w : Nat) (h1 : p + u = q + t) (h2 : r + w = s + v) :
--   p * r + q * s + (t * w + u * v) = p * s + q * r + (t * v + u * w) :=
-- by omega
