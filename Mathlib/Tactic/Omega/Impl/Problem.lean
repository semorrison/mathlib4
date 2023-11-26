import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.SolveByElim
import Mathlib.Tactic.Classical

import Mathlib.Tactic.Omega.IntList
import Mathlib.Tactic.Omega.Problem
import Mathlib.Tactic.Omega.Impl.MinNatAbs
import Mathlib.Tactic.Omega.Impl.bmod

import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Rewrites

set_option autoImplicit true
set_option relaxedAutoImplicit true



open Classical

namespace Omega.Impl

structure LinearCombo where
  const : Int := 0
  coeffs : IntList := []
  -- smallCoeff : Option Nat := coeffs.findIdx? fun i => i.natAbs = 1
  -- smallCoeff_eq : smallCoeff = coeffs.findIdx? fun i => i.natAbs = 1 := by rfl
deriving DecidableEq, Repr

instance : ToString LinearCombo where
  toString lc := s!"{lc.const}{String.join <| lc.coeffs.enum.map fun ⟨i, c⟩ => s!" + {c} * x{i+1}"}"

example : toString (⟨7, [3, 5]/-, none, rfl-/⟩ : LinearCombo) = "7 + 3 * x1 + 5 * x2" := rfl

namespace LinearCombo

@[simps]
def of (a : Omega.LinearCombo) : LinearCombo := { a with }

@[simps]
def to (a : LinearCombo) : Omega.LinearCombo := { a with }

instance : Inhabited LinearCombo := ⟨{const := 1}⟩

@[ext] theorem ext {a b : LinearCombo} (w₁ : a.const = b.const) (w₂ : a.coeffs = b.coeffs) :
    a = b := by
  cases a; cases b
  subst w₁; subst w₂
  congr
  -- simp_all

theorem ext_iff {a b : LinearCombo} : a = b ↔ a.const = b.const ∧ a.coeffs = b.coeffs :=
  ⟨by rintro rfl; simp, fun ⟨w₁, w₂⟩ => ext w₁ w₂⟩

def sign (a : LinearCombo) : Int :=
  IntList.leadingSign a.coeffs

def coordinate (i : Nat) : LinearCombo where
  const := 0
  coeffs := List.replicate i 0 ++ [1]
  -- smallCoeff := i
  -- smallCoeff_eq := by simp

/--
Evaluate a linear combination `⟨r, [c_1, …, c_k]⟩` at values `[v_1, …, v_k]` to obtain
`r + (c_1 * x_1 + (c_2 * x_2 + ... (c_k * x_k + 0))))`.
-/
def eval (lc : LinearCombo) (values : IntList) : Int :=
  lc.const + lc.coeffs.dot values

@[simp] theorem eval_nil : (lc : LinearCombo).eval [] = lc.const := by
  simp [eval]

@[simp] theorem of_eval (a : Omega.LinearCombo) : (of a).eval v = a.eval v := rfl
@[simp] theorem to_eval (a : LinearCombo) : (to a).eval v = a.eval v := rfl

@[simp] theorem coordinate_eval (i : Nat) (v : IntList) :
    (coordinate i).eval v = (v.get? i).getD 0 := by
  simp [eval, coordinate]
  induction v generalizing i with
  | nil => simp
  | cons x v ih =>
    cases i with
    | zero => simp
    | succ i => simp_all

def add (l₁ l₂ : LinearCombo) : LinearCombo where
  const := l₁.const + l₂.const
  coeffs := l₁.coeffs + l₂.coeffs

instance : Add LinearCombo := ⟨add⟩

@[simp] theorem add_const {l₁ l₂ : LinearCombo} : (l₁ + l₂).const = l₁.const + l₂.const := rfl
@[simp] theorem add_coeffs {l₁ l₂ : LinearCombo} : (l₁ + l₂).coeffs = l₁.coeffs + l₂.coeffs := rfl

def sub (l₁ l₂ : LinearCombo) : LinearCombo where
  const := l₁.const - l₂.const
  coeffs := l₁.coeffs - l₂.coeffs

instance : Sub LinearCombo := ⟨sub⟩

@[simp] theorem sub_const {l₁ l₂ : LinearCombo} : (l₁ - l₂).const = l₁.const - l₂.const := rfl
@[simp] theorem sub_coeffs {l₁ l₂ : LinearCombo} : (l₁ - l₂).coeffs = l₁.coeffs - l₂.coeffs := rfl

/-- Negating a linear combination means negating the constant term and the coefficients. -/
def neg (lc : LinearCombo) : LinearCombo where
  const := -lc.const
  coeffs := -lc.coeffs

instance : Neg LinearCombo := ⟨neg⟩

@[simp] theorem neg_const {l : LinearCombo} : (-l).const = -l.const := rfl
@[simp] theorem neg_coeffs {l : LinearCombo} : (-l).coeffs = -l.coeffs  := rfl

theorem sub_eq_add_neg (l₁ l₂ : LinearCombo) : l₁ - l₂ = l₁ + -l₂ := by
  rcases l₁ with ⟨a₁, c₁⟩; rcases l₂ with ⟨a₂, c₂⟩
  ext1
  · simp [Int.sub_eq_add_neg]
  · simp [IntList.sub_eq_add_neg]

def smul (lc : LinearCombo) (i : Int) : LinearCombo where
  const := i * lc.const
  coeffs := lc.coeffs.smul i

instance : HMul Int LinearCombo LinearCombo := ⟨fun i lc => lc.smul i⟩

@[simp] theorem smul_const {lc : LinearCombo} {i : Int} : (i * lc).const = i * lc.const := rfl
@[simp] theorem smul_coeffs {lc : LinearCombo} {i : Int} : (i * lc).coeffs = i * lc.coeffs := rfl

@[simp]
theorem add_eval (l₁ l₂ : LinearCombo) (v : List Int) : (l₁ + l₂).eval v = l₁.eval v + l₂.eval v := by
  rcases l₁ with ⟨r₁, c₁⟩; rcases l₂ with ⟨r₂, c₂⟩
  simp only [eval, add_const, add_coeffs, Int.add_assoc, Int.add_left_comm]
  congr
  exact IntList.dot_distrib_left c₁ c₂ v

@[simp]
theorem neg_eval (lc : LinearCombo) (v : List Int) : (-lc).eval v = - lc.eval v := by
  rcases lc with ⟨a, coeffs⟩
  simp [eval, Int.neg_add]

@[simp]
theorem sub_eval (l₁ l₂ : LinearCombo) (v : List Int) :
    (l₁ - l₂).eval v = l₁.eval v - l₂.eval v := by
  simp [sub_eq_add_neg, Int.sub_eq_add_neg]

@[simp]
theorem smul_eval (lc : LinearCombo) (i : Int) (v : List Int) :
    (i * lc).eval v = i * lc.eval v := by
  rcases lc with ⟨a, coeffs⟩
  simp [eval, Int.mul_add]

def coeff (lc : LinearCombo) (i : Nat) : Int := lc.coeffs.get i

@[simp]
theorem coeff_mk {const} {coeffs} {i} : LinearCombo.coeff { const, coeffs } i = coeffs.get i := rfl

@[simps]
def setCoeff (lc : LinearCombo) (i : Nat) (x : Int) : LinearCombo where
  const := lc.const
  coeffs := lc.coeffs.set i x

@[simp]
theorem setCoeff_coeff_self (lc : LinearCombo) (i : Nat) (x : Int) :
    (lc.setCoeff i x).coeff i = x := by
  simp [setCoeff]

@[simp] theorem setCoeff_eval {lc : LinearCombo} :
    (lc.setCoeff i x).eval v = lc.eval v + (x - lc.coeff i) * v.get i := by
  simp [eval, Int.add_assoc, Int.sub_mul]
  rfl

@[simp]
theorem eval_set {lc : LinearCombo} :
    lc.eval (v.set i x) = lc.eval v + lc.coeff i * (x - v.get i) := by
  simp [eval, Int.add_assoc]
  rfl

theorem setCoeff_coeff_of_ne (lc : LinearCombo) (i j : Nat) (w : i ≠ j) (x : Int) :
    (lc.setCoeff j x).coeff i = lc.coeff i := by
  simp_all [set, coeff, w.symm]


@[simp] theorem coeff_zero {lc : LinearCombo} (w : ∀ x, x ∈ lc.coeffs → x = 0) :
    lc.coeff i = 0 := by
  simp [coeff, IntList.get]
  cases h : lc.coeffs.get? i with
  | none => simp
  | some x' =>
    apply w
    simp only [Option.getD_some]
    exact List.get?_mem h

end LinearCombo

/--
An equality is a linear combo (which we interpret as being constrained to be zero)
along with some optional cached data about the smallest absolute value of a nonzero coefficient.

We cache this data as it is used repeatedly when eliminating equalities.
-/
structure Equality where
  linearCombo : LinearCombo
  /--
  Cached value of `minCoeff`, the smallest absolute value of a nonzero coefficient
  (or zero if all coefficients are zero).
  -/
  minCoeff? : Option Nat := none
  /--
  Cached value of `minCoeffIdx`, the index of some coefficient whose absolute value is `minCoeff`.
  -/
  minCoeffIdx? : Option Nat := none
  minCoeff?_spec : SatisfiesM (fun min => min = linearCombo.coeffs.minNatAbs) minCoeff? := by simp
  minCoeffIdx?_spec :
    SatisfiesM (fun idx => minCoeff?.isSome ∧ (linearCombo.coeff idx).natAbs = minCoeff?) minCoeffIdx? := by simp
deriving DecidableEq

namespace Equality

/-- The smallest absolute value of a nonzero coefficient (or zero if all coefficients are zero). -/
def minCoeff (e : Equality) : Nat :=
  match e.minCoeff? with
  | none => e.linearCombo.coeffs.minNatAbs
  | some min => min

theorem minCoeff_spec (e : Equality) : e.minCoeff = e.linearCombo.coeffs.minNatAbs := by
  rcases e with ⟨lc, ⟨⟩|⟨n⟩, _, spec, _⟩
  · rfl
  · dsimp [minCoeff]
    rw [SatisfiesM_Option_eq] at spec
    exact (spec n rfl)

-- Needs a better name
theorem minCoeff_spec' (e : Equality) :
    (∃ i, (e.linearCombo.coeff i).natAbs = e.minCoeff) ∧
      (∀ i, e.minCoeff ≤ (e.linearCombo.coeff i).natAbs ∨ (e.linearCombo.coeff i) = 0) ∧
      (e.minCoeff ≠ 0 ∨ ∀ i, (e.linearCombo.coeff i) = 0) := by
  rw [minCoeff_spec]
  dsimp [minCoeff]
  cases h : e.linearCombo.coeffs.minNatAbs with
  | zero => simp_all
  | succ n =>
    rw [List.minNatAbs_eq_nonzero_iff] at h
    · obtain ⟨⟨y, m, h₁⟩, h₂⟩ := h
      let i := e.linearCombo.coeffs.idx_of_mem m
      refine ⟨⟨i, ?_⟩, ?_, by simp⟩
      · dsimp [LinearCombo.coeff, IntList.get]
        simp_all [e.linearCombo.coeffs.idx_of_mem_spec m]
      · dsimp [LinearCombo.coeff, IntList.get]
        intro j
        match h : e.linearCombo.coeffs.get? j with
        | none => simp
        | some y =>
          apply h₂
          rw [List.mem_iff_get?]
          refine ⟨j, h⟩
    · exact Nat.succ_ne_zero n

theorem coeff_zero_of_minCoeff_zero {e : Equality} (h : e.minCoeff = 0) (i) :
    e.linearCombo.coeff i = 0 := by
  cases e.minCoeff_spec'.2.2 <;> solve_by_elim

def minCoeffIdx (e : Equality) : Nat :=
  match e.minCoeffIdx? with
  | some i => i
  | none =>
    let m := e.minCoeff
    e.linearCombo.coeffs.findIdx fun x => x.natAbs = m

theorem minCoeffIdx_spec (e : Equality) :
    (e.linearCombo.coeff e.minCoeffIdx).natAbs = e.minCoeff := by
  rcases e with ⟨lc, m?, ⟨⟩|⟨n⟩, spec, specIdx⟩
  · dsimp [minCoeffIdx, LinearCombo.coeff, IntList.get]
    rw [minCoeff_spec]
    dsimp
    by_cases h : lc.coeffs.minNatAbs = 0
    · simp only [h, Int.natAbs_eq_zero]
      cases h' : lc.coeffs.get? (lc.coeffs.findIdx (· = 0))
      · simp
      · simpa using List.findIdx_of_get?_eq_some h'
    · have h₁ := lc.coeffs.minNatAbs_eq_nonzero_iff h
      simp at h₁
      have h₂ := List.findIdx_get?_eq_get_of_exists
        (p := fun x : Int => x.natAbs = lc.coeffs.minNatAbs)
        (by simpa using h₁.1)
      simp only [h₂]
      simpa using List.findIdx_get (p := fun x : Int => x.natAbs = lc.coeffs.minNatAbs)
  · dsimp [minCoeffIdx]
    rw [SatisfiesM_Option_eq] at specIdx
    obtain ⟨i, h⟩ := specIdx n rfl
    match m?, i with
    | some m, _ => simpa using h

/-- Calculate the `minCoeff?` field, if is is not already available. -/
def calculateMinCoeff (e : Equality) : Equality :=
  match e.minCoeff? with
  | some _ => e
  | none =>
    { linearCombo := e.linearCombo
      minCoeff? := e.minCoeff
      minCoeff?_spec := by
        rw [SatisfiesM_Option_eq]
        rintro a ⟨⟩
        exact e.minCoeff_spec }

/-- Calculate the `minCoeffIdx?` field, if is is not already available. -/
def calculateMinCoeffIdx (e : Equality) : Equality :=
  match e.minCoeffIdx? with
  | some _ => e
  | none =>
    let e' := calculateMinCoeff e
    { e' with
      minCoeffIdx? := e'.minCoeffIdx
      minCoeffIdx?_spec := by
        rw [SatisfiesM_Option_eq]
        rintro a ⟨⟩
        rw [e'.minCoeffIdx_spec]
        simp only [calculateMinCoeff]
        split <;> simp_all [minCoeff] }

instance : ToString Equality where
  toString eq := s!"{eq.linearCombo} = 0"

-- TODO: make sure this is only called on `Equality`s with precomputed `minCoeff` and `minCoeffIdx`.
def smallCoeff (a : Equality) : Option Nat :=
  if a.minCoeff = 1 then
    a.minCoeffIdx
  else
    none

theorem smallCoeff_natAbs {a : Equality} (w : a.smallCoeff = some i) :
    (a.linearCombo.coeff i).natAbs = 1 := by
  dsimp [smallCoeff] at w
  simp at w
  rcases w with ⟨w, rfl⟩
  rw [a.minCoeffIdx_spec, w]

end Equality

-- structure CoeffsKey where
--   coeffs : IntList
--   sign_nonneg : 0 ≤ coeffs.sign
--   coeffsHash : UInt64 := coeffs.hash
--   coeffsHash_spec : coeffsHash = coeffs.hash := by rfl

-- @[ext] theorem CoeffsKey.ext {k₁ k₂ : CoeffsKey} (w : k₁.coeffs = k₂.coeffs) : k₁ = k₂ := by
--   cases k₁; cases k₂; simp_all

-- instance : Hashable CoeffsKey := ⟨CoeffsKey.coeffsHash⟩
-- instance : BEq CoeffsKey := ⟨fun k₁ k₂ => k₁.coeffs == k₂.coeffs⟩

-- @[simp] theorem CoeffsKey_beq {k₁ k₂ : CoeffsKey} : (k₁ == k₂) = (k₁.coeffs == k₂.coeffs) := rfl

-- instance : LawfulBEq CoeffsKey where
--   eq_of_beq := by intros; ext; simp_all
--   rfl := by simp

-- structure Inequality where
--   linearCombo : LinearCombo
--   sign : Int := linearCombo.coeffs.sign
--   sign_spec : sign = linearCombo.coeffs.sign := by rfl
--   key : CoeffsKey :=
--   { coeffs := linearCombo.coeffs.sign * linearCombo.coeffs
--     sign_nonneg := IntList.sign_mul_self_nonneg }
--   key_spec : key.coeffs = linearCombo.coeffs.sign * linearCombo.coeffs := by rfl

-- @[ext] theorem Inequality.ext {i₁ i₂ : Inequality} (w : i₁.linearCombo = i₂.linearCombo) :
--     i₁ = i₂ := by
--   cases i₁; cases i₂
--   simp_all only [mk.injEq, true_and]
--   ext1
--   simp_all

-- instance : BEq Inequality := ⟨fun i₁ i₂ => i₁.linearCombo == i₂.linearCombo⟩

-- @[simp] theorem Inequality_beq {i₁ i₂ : Inequality} :
--     (i₁ == i₂) = (i₁.linearCombo == i₂.linearCombo) := rfl

-- instance : LawfulBEq Inequality where
--   eq_of_beq := by intros; ext1; simp_all
--   rfl := by simp


-- structure Inequalities where
--   /--
--   For each list of coefficients (with first nonzero entry positive), we store
--   at most one inequality with those coefficients, and
--   at most one inequality with those coefficients negated.

--   If we have two inequalities with the same coefficients, one must be redundant.
--   Given a pair of inequalities with opposite coefficients
--   `a + ∑ cᵢ * xᵢ ≥ 0` and `b - ∑ cᵢ * xᵢ ≥ 0`, we must have `-a ≤ b`.
--   -/
--   map : Std.HashMap CoeffsKey (Option Inequality × Option Inequality) := ∅
--   -- map_spec k : SatisfiesM (x := map.find? k) fun ⟨i₁?, i₂?⟩ =>
--   --   SatisfiesM (fun i₁ => i₁.key = k ∧ i₁.linearCombo.coeffs.sign = -1) i₁? ∧
--   --     SatisfiesM (fun i₂ => i₂.key = k ∧ i₂.linearCombo.coeffs.sign = 1) i₂?


-- namespace Inequalities

-- -- def contains (m : Inequalities) (i : Inequality) : Bool :=
-- --   match m.map.find? i.key with
-- --   | none => false
-- --   | some (none, none) => false
-- --   | some (some i₁, none) => i₁ == i
-- --   | some (none, some i₂) => i₂ == i
-- --   | some (some i₁, some i₂) => i₁ == i || i₂ == i

-- def mem (m : Inequalities) : Inequality → Prop :=
--   fun i => ∃ k, i ∈ m.map.find? k >>= (·.1) ∨ i ∈ m.map.find? k >>= (·.2)

-- inductive Inequality
-- | lowerBound (x : Int)
-- | upperBound (x : Int)

-- namespace Inequality

-- def sat : Inequality → Int → Prop
-- | .lowerBound x, y => x ≤ y
-- | .upperBound x, y => y ≤ x

-- end Inequality

-- inductive Constraint
-- | impossible
-- | lowerBound (x : Int)
-- | upperBound (x : Int)
-- | between (x y : Int)

-- namespace Constraint

-- def sat : Constraint → Int → Prop
-- | .impossible, _ => False
-- | .lowerBound x, y => x ≤ y
-- | .upperBound x, y => y ≤ x
-- | .between x y, z => x ≤ z ∧ z ≤ y

-- def combine : Constraint → Inequality → Constraint
-- | .impossible, .lowerBound _ => .impossible
-- | .impossible, .upperBound _ => .impossible
-- | .lowerBound x, .lowerBound w => if x < w then .lowerBound w else .lowerBound x
-- | .lowerBound x, .upperBound z => if z < x then .impossible else .between x z
-- | .upperBound y, .lowerBound w => if y < w then .impossible else .between w y
-- | .upperBound y, .upperBound z => if y < z then .upperBound y else .upperBound y
-- | .between x y, .lowerBound w =>
--   if y < w then .impossible else if x ≤ w then .between w y else .between x y
-- | .between x y, .upperBound z =>
--   if z < x then .impossible else if z ≤ y then .between x z else .between x y

-- theorem combine_sat :
--     (c : Constraint) → (i : Inequality) → (t : Int) → (c.combine i).sat t = (c.sat t ∧ i.sat t)
-- | .impossible, .lowerBound _, t => by simp [sat, combine]
-- | .impossible, .upperBound _, t => by simp [sat, combine]
-- | .lowerBound x, .lowerBound w, t => by
--   simp [combine]
--   split <;> rename_i h <;> simp [sat, Inequality.sat]
--   · sorry
--   · sorry
-- | .lowerBound x, .upperBound z, t => sorry
-- | .upperBound y, .lowerBound w, t => sorry
-- | .upperBound y, .upperBound z, t => sorry
-- | .between x y, .lowerBound w, t => sorry
-- | .between x y, .upperBound z, t => sorry

-- end Constraint


-- end Inequalities

structure Problem where
  possible : Bool := true
  equalities : List Equality := []
  inequalities : List LinearCombo := []
  -- inequalities' : Inequalities := {}

namespace Problem

instance : ToString Problem where
  toString p :=
    if p.possible then
      if p.equalities = [] ∧ p.inequalities = [] then
        "trivial"
      else
        "\n".intercalate <|
          (p.equalities.map fun e => s!"{e}") ++ (p.inequalities.map fun e => s!"{e} ≥ 0")
    else
      "impossible"

/--
A propositional representation of whether a `Problem` contains a particular equality.
We use this to decouple all the proofs (e.g. regarding equivalence or termination)
from the data representation of the equalities.
-/
def hasEquality (p : Problem) (e : Equality) : Prop := e ∈ p.equalities

/--
A propositional representation of whether a `Problem` contains a particular inequality.
We use this to decouple all the proofs (e.g. regarding equivalence or termination)
from the data representation of the inequalities.
-/
def hasInequality (p : Problem) (e : LinearCombo) : Prop := e ∈ p.inequalities

@[simps]
def of (p : Omega.Problem) : Problem where
  possible := p.possible
  equalities := p.equalities.map fun lc => { linearCombo := .of lc }
  inequalities := p.inequalities.map .of

@[simps]
def to (p : Problem) : Omega.Problem where
  possible := p.possible
  equalities := p.equalities.map fun eq => LinearCombo.to eq.linearCombo
  inequalities := p.inequalities.map LinearCombo.to

structure sat (p : Problem) (values : List Int) : Prop where
  possible : p.possible = true := by trivial
  equalities : p.hasEquality eq → eq.linearCombo.eval values = 0
  inequalities : p.hasInequality lc → lc.eval values ≥ 0

/-- The trivial problem, with no constraints. -/
@[simps]
def trivial : Problem where

@[simp] theorem trivial_hasEquality : trivial.hasEquality e = False := by simp [hasEquality]
@[simp] theorem trivial_hasInequality : trivial.hasInequality e = False := by simp [hasInequality]

theorem trivial_sat (values : List Int) : trivial.sat values where
  equalities := by simp
  inequalities := by simp

theorem of_sat (p : Omega.Problem) : (of p).sat v ↔ p.sat v := by
  constructor
  · intro ⟨_, _, _⟩
    constructor <;> simp_all (config := {decide := true}) [hasEquality, hasInequality]
  · intro ⟨_, _, _⟩
    constructor <;> simp_all (config := {decide := true}) [hasEquality, hasInequality]

theorem to_sat (p : Problem) : (to p).sat v ↔ p.sat v := by
  constructor
  · intro ⟨_, _, _⟩
    constructor <;> simp_all (config := {decide := true}) [hasEquality, hasInequality]
  · intro ⟨_, _, _⟩
    constructor <;> simp_all (config := {decide := true}) [hasEquality, hasInequality]

def equalitiesZero (p : Problem) : Prop :=
  ∀ {eq : Equality} (_ : eq ∈ p.equalities) (i), eq.linearCombo.coeff i = 0

def solutions (p : Problem) : Type :=
  { values // p.sat values }

instance : CoeSort Problem Type where
  coe := solutions

def map_of (p : Omega.Problem) : p → of p := fun ⟨v, s⟩ => ⟨v, (of_sat p).mpr s⟩
def map_to (p : Problem) : p → to p := fun ⟨v, s⟩ => ⟨v, (to_sat p).mpr s⟩

def map_of_sat {p q : Problem} (h : ∀ v, p.sat v → q.sat v) : p → q :=
  fun ⟨v, s⟩ => ⟨v, h v s⟩

def unsat (p : Problem) : Prop := p → False

def trivial_solution : (trivial : Type) := ⟨[], { equalities := by simp, inequalities := by simp }⟩

theorem unsat_of_impossible {p : Problem} (h : p.possible = false) : p.unsat :=
  fun ⟨v, s⟩ => by
    rw [s.possible] at h
    simp at h

@[simps]
def impossible : Problem where
  possible := false

theorem impossible_unsat : impossible.unsat := unsat_of_impossible rfl

@[simp] theorem not_sat_impossible : sat impossible v ↔ False :=
  ⟨fun h => impossible_unsat ⟨_, h⟩, False.elim⟩

/-- A solution to a problem consists either of a witness, or a proof of unsatisfiability. -/
inductive Solution (p : Problem)
| sat : p → Solution p
| unsat : p.unsat → Solution p


instance : ToString (Solution p) where
  toString s := match s with
  | .sat ⟨v, _⟩ => s!"satisfied at {v}"
  | .unsat _ => "unsat"

/--
Two problems are equivalent if a solution to one gives a solution to the other.
We don't care that this is bijective,
just that the solution sets are either both empty or both non-empty.
-/
structure equiv (p q : Problem) where
  mp : p → q
  mpr : q → p

def equiv_of_sat_iff {p q : Problem} (h : ∀ v, p.sat v ↔ q.sat v) : p.equiv q where
  mp := fun ⟨v, s⟩ => ⟨v, (h v).mp s⟩
  mpr := fun ⟨v, s⟩ => ⟨v, (h v).mpr s⟩

namespace equiv

def refl (p : Problem) : p.equiv p where
  mp := id
  mpr := id

def trans {p q r : Problem} (e : p.equiv q) (f : q.equiv r) : p.equiv r where
  mp := f.mp ∘ e.mp
  mpr := e.mpr ∘ f.mpr

end equiv

end Problem

-- structure DisjunctiveProblem where
--   problems : List Problem

-- namespace DisjunctiveProblem

-- def sat (d : DisjunctiveProblem) (values : List Int) : Prop :=
--   ∃ p ∈ d.problems, p.sat values

-- def solutions (p : DisjunctiveProblem) : Type :=
--   { values // p.sat values }

-- instance : CoeSort DisjunctiveProblem Type where
--   coe := solutions

-- def unsat (p : DisjunctiveProblem) : Prop := p → False

-- inductive Solution (d : DisjunctiveProblem)
-- | sat : d.sat values → Solution d
-- | unsat : d.unsat → Solution d

-- end DisjunctiveProblem

/-!
Erasing an inequality results in a larger solution space.
-/
namespace Problem

-- @[simps]
-- def eraseEquality (p : Problem) (eq : Equality) : Problem :=
--   { p with equalities := p.equalities.erase eq }

-- @[simps]
-- def eraseInequality (p : Problem) (lc : LinearCombo) : Problem :=
--   { p with inequalities := p.inequalities.erase lc }

-- theorem of_eraseInequality_hasInequality {p : Problem} (w : (p.eraseInequality lc).hasInequality lc') :
--     p.hasInequality lc' := by
--   simpa [hasInequality] using List.mem_of_mem_erase w

-- theorem of_eraseEquality_hasEquality {p : Problem} (w : (p.eraseEquality e).hasEquality e') :
--     p.hasEquality e' := by
--   simpa [hasEquality] using List.mem_of_mem_erase w

-- theorem eraseEquality_sat (p : Problem) (eq : Equality) (v : List Int) (s : p.sat v) :
--     (p.eraseEquality eq).sat v :=
--   { s with
--     equalities := fun m => s.equalities (of_eraseEquality_hasEquality m) }

-- theorem eraseInequality_sat (p : Problem) (lc : LinearCombo) (v : List Int) (s : p.sat v) :
--     (p.eraseInequality lc).sat v :=
--   { s with
--     inequalities := fun m => s.inequalities (of_eraseInequality_hasInequality m) }

-- /-- Any solution gives a solution after erasing an equality. -/
-- def eraseEquality_map (p : Problem) (eq : Equality) :
--     p → { p with equalities := p.equalities.erase eq } :=
--   map_of_sat (p.eraseEquality_sat eq)

-- /-- Any solution gives a solution after erasing an inequality. -/
-- def eraseInequality_map (p : Problem) (lc : LinearCombo) :
--     p → { p with inequalities := p.inequalities.erase lc } :=
--   map_of_sat (p.eraseInequality_sat lc)

@[simps]
def filterEqualities (p : Problem) (f : Equality → Bool) : Problem :=
  { p with equalities := p.equalities.filter f }

@[simps]
def filterInequalities (p : Problem) (f : LinearCombo → Bool) : Problem :=
  { p with inequalities := p.inequalities.filter f }

@[simp] theorem filterEqualities_hasEquality {p : Problem} {f} :
    (p.filterEqualities f).hasEquality e ↔ p.hasEquality e ∧ f e := by
  simp [List.mem_filter, hasEquality]

@[simp] theorem filterEqualities_hasInequality {p : Problem} {f} :
    (p.filterEqualities f).hasInequality e ↔ p.hasInequality e := by
  simp only [hasInequality, filterEqualities_inequalities]

@[simp] theorem filterInequalities_hasEquality {p : Problem} {f} :
    (p.filterInequalities f).hasEquality e ↔ p.hasEquality e := by
  simp only [hasEquality, filterInequalities_equalities]

@[simp] theorem filterInequalities_hasInequality {p : Problem} {f} :
    (p.filterInequalities f).hasInequality e ↔ p.hasInequality e ∧ f e := by
  simp [List.mem_filter, hasInequality]

theorem filterEqualities_sat (p : Problem) (f) (v : List Int) (s : p.sat v) :
    (p.filterEqualities f).sat v :=
  { s with
    equalities := fun m =>
      s.equalities (by simpa [hasEquality] using List.mem_of_mem_filter' m) }

theorem filterInequalities_sat (p : Problem) (f) (v : List Int) (s : p.sat v) :
    (p.filterInequalities f).sat v :=
  { s with
    inequalities := fun m =>
      s.inequalities (by simpa [hasInequality] using List.mem_of_mem_filter' m) }

def filterEqualities_map (p : Problem) (f) :
    p → (p.filterEqualities f) :=
  map_of_sat (p.filterEqualities_sat f)

def filterInequalities_map (p : Problem) (f) :
    p → (p.filterInequalities f) :=
  map_of_sat (p.filterInequalities_sat f)

end Problem

/-!
Define `a ≤ b` on linear combinations to mean that the coefficients are identical,
and the constant terms satisfy `≤`.

If `a ≤ b`, then the non-negative set for `a` is a subset of the non-negative set for `b`.

(Note this is only a preorder, not even a partial order,
as we don't allow for rescaling when comparing coefficients.)

We show:
```
a < b → a ∈ p.inequalities → { p with equalities := p.equalities.erase b } → p
```
-/

namespace LinearCombo

/--
Define `a ≤ b` on linear combinations to mean that the coefficients are identical,
and the constant terms satisfy `≤`.

If `a ≤ b`, then the non-negative set for `a` is a subset of the non-negative set for `b`.

(Note this is only a preorder, not even a partial order,
as we don't allow for rescaling when comparing coefficients.)
-/
def le (a b : LinearCombo) : Prop :=
  a.coeffs = b.coeffs ∧ a.const ≤ b.const

instance : LE LinearCombo := ⟨le⟩

theorem le_def (a b : LinearCombo) : a ≤ b ↔ a.coeffs = b.coeffs ∧ a.const ≤ b.const := Iff.rfl

instance : DecidableRel ((· : LinearCombo) ≤ ·) :=
  fun a b => decidable_of_iff' _ (le_def a b)

theorem eval_le_of_le {a b : LinearCombo} (h : a ≤ b) (v : List Int) : a.eval v ≤ b.eval v := by
  simp [LinearCombo.eval]
  rcases a with ⟨a, coeffs⟩; rcases b with ⟨b, bcoeffs⟩
  rcases h with ⟨rfl, h⟩
  apply Int.add_le_add_right h

theorem evalNonneg_of_le {a b : LinearCombo} (h : a ≤ b) : a.eval v ≥ 0 → b.eval v ≥ 0 :=
  fun w => Int.le_trans w (eval_le_of_le h v)

/--
Define `a < b` on linear combinations to mean that the coefficients are identical,
and the constant terms satisfy `<`.

If `a < b`, then the non-negative set for `a` is a strict subset of the non-negative set for `b`.
-/
def lt (a b : LinearCombo) : Prop :=
  a ≤ b ∧ a ≠ b

instance : LT LinearCombo := ⟨lt⟩

theorem lt_def (a b : LinearCombo) : a < b ↔ a.coeffs = b.coeffs ∧ a.const < b.const := by
  change a ≤ b ∧ ¬a = b ↔ _
  rw [le_def]
  rcases a with ⟨a, as⟩; rcases b with ⟨b, bs⟩
  simp only [ext_iff]
  constructor
  · rintro ⟨⟨rfl, le⟩, h⟩
    simp_all only [and_true, true_and]
    exact Int.lt_iff_le_and_ne.mpr ⟨le, h⟩
  · rintro ⟨rfl, lt⟩
    simp only [true_and, and_true]
    exact ⟨Int.le_of_lt lt, Int.ne_of_lt lt⟩

instance : DecidableRel ((· : LinearCombo) < ·) :=
  fun a b => decidable_of_iff' _ (lt_def a b)

theorem eval_lt_of_lt {a b : LinearCombo} (h : a < b) (v : List Int) : a.eval v < b.eval v := by
  simp [LinearCombo.eval]
  rcases a with ⟨a, coeffs⟩; rcases b with ⟨b, bcoeffs⟩
  rw [lt_def] at h
  rcases h with ⟨rfl, h⟩
  apply Int.add_lt_add_right h

end LinearCombo

-- namespace Problem

-- /--
-- If `a < b` is a strict comparison between inequality constraints,
-- in any problems containing `a`, we can discard `b`.
-- -/
-- theorem sat_of_eraseRedundantInequality_sat
--     (p : Problem) {a b : LinearCombo} (lt : a < b) (m : a ∈ p.inequalities) (v)
--     (s : (p.eraseInequality b).sat v) : p.sat v :=
--   { s with
--     inequalities := fun m' => by
--       rw [hasInequality, List.mem_iff_mem_erase_or_eq _ _ b] at m'
--       rcases m' with m' | ⟨rfl, m'⟩
--       · apply s.inequalities
--         exact m'
--       · rcases lt with ⟨le, ne⟩
--         apply LinearCombo.evalNonneg_of_le le
--         apply s.inequalities
--         simpa using (List.mem_erase_of_ne ne).mpr m }

-- /--
-- If `a < b` is a strict comparison between inequality constraints,
-- in any problems containing `a`, we can discard `b` to obtain an equivalent problem.
-- -/
-- def eraseRedundantInequality_equiv
--     (p : Problem) {a b : LinearCombo} (lt : a < b) (m : a ∈ p.inequalities) :
--     { p with inequalities := p.inequalities.erase b }.equiv p :=
--   equiv_of_sat_iff
--     fun v => ⟨p.sat_of_eraseRedundantInequality_sat lt m v, p.eraseInequality_sat b v⟩

-- end Problem

/-!
We define negation of a linear combination,
and show that `a < b.neg` gives a contradition.
-/
namespace Problem

theorem contradiction_of_neg_lt (p : Problem) {a b : LinearCombo}
    (ma : a ∈ p.inequalities) (mb : b ∈ p.inequalities) (w : a < -b) : p.unsat := by
  rintro ⟨v, s⟩
  have := LinearCombo.eval_lt_of_lt w v
  simp only [LinearCombo.neg_eval] at this
  apply Int.lt_irrefl 0 (Int.lt_of_lt_of_le (Int.lt_of_le_of_lt (s.inequalities ma) this)
    (Int.neg_le_neg (s.inequalities mb)))

/--
We verify that `x - 1 ≥ 0` and `-x ≥ 0` have no solutions.
-/
example :
    let p : Problem := { inequalities := [{const:=-1, coeffs:=[1]}, {const:=0, coeffs:=[-1]}] };
    p.unsat := by
  apply contradiction_of_neg_lt (a := {const:=-1, coeffs:=[1]}) (b := {const:=0, coeffs:=[-1]}) <;>
  simp (config := {decide := true})

instance {α : Type _} [DecidableEq α] {l : List α} (p : α → Prop) [∀ a, Decidable (p a)] :
    Decidable (∃ (a : α) (_ : a ∈ l), p a) :=
  decidable_of_iff (∃ (a : α), a ∈ l ∧ p a) (exists_congr (fun _ => exists_prop.symm))

-- FIXME
-- Dump redundant inequalities (i.e `a < b`)!
-- Turn tight pairs (i.e. `a = -b`) into equalities, because we have better ways to deal with them

-- TODO make this efficient using the map
def checkContradictions (p : Problem) : Problem :=
  if p.inequalities.any fun a => p.inequalities.any fun b => a < -b then
  -- if ∃ (a : LinearCombo) (_ : a ∈ p.inequalities) (b : LinearCombo) (_ : b ∈ p.inequalities), a < -b then
    impossible
  else p

theorem checkContradictions_equalities_length (p : Problem) :
    p.checkContradictions.equalities.length ≤ p.equalities.length := by
  dsimp [checkContradictions]
  split
  · apply Nat.zero_le
  · apply Nat.le_refl

theorem checkContradictions_inequalities_length (p : Problem) :
    p.checkContradictions.inequalities.length ≤ p.inequalities.length := by
  dsimp [checkContradictions]
  split
  · apply Nat.zero_le
  · apply Nat.le_refl

theorem checkContradictions_sat_iff (p : Problem) (v) : p.checkContradictions.sat v ↔ p.sat v := by
  dsimp [checkContradictions]
  split <;> rename_i h
  · constructor
    · intro s
      simp_all
    · intro s
      simp only [not_sat_impossible]
      simp only [List.any_eq_true, decide_eq_true_eq] at h
      obtain ⟨a, ma, b, mb, w⟩ := h
      exact p.contradiction_of_neg_lt ma mb w ⟨v, s⟩
  · rfl

def checkContradictions_equiv (p : Problem) : p.checkContradictions.equiv p :=
  Problem.equiv_of_sat_iff p.checkContradictions_sat_iff

end Problem

namespace LinearCombo

/-- Return the constant term if all coefficients of variables are zero. -/
def constant? (lc : LinearCombo) : Option Int :=
  if lc.coeffs.all (· = 0) then
    some lc.const
  else
    none

theorem eval_eq_of_constant (lc : LinearCombo) (h : lc.constant? = some c) : lc.eval v = c := by
  simp only [constant?, List.all_eq_true, decide_eq_true_eq, ite_some_none_eq_some] at h
  rcases h with ⟨h, rfl⟩
  rcases lc with ⟨c, coeffs⟩
  simp only [eval]
  conv =>
    rhs
    rw [← Int.add_zero c]
  congr
  exact IntList.dot_of_left_zero h

end LinearCombo

namespace Equality

theorem constant?_eq_none_iff {e : Equality} : e.linearCombo.constant? = none ↔ e.minCoeff ≠ 0 := by
  rw [minCoeff_spec, Ne, List.minNatAbs_eq_zero_iff, LinearCombo.constant?]
  simp only [ite_eq_right_iff]
  change ¬ _ ↔ _
  simp
end Equality

namespace Problem

/--
We look for any constant equalities with nonzero constant,
or for any constant inequalities with negative constant.

If we find any, the problem is impossible.
Otherwise, we can discard all constants.
-/
def processConstants (p : Problem) : Problem :=
  let equalityConstants := p.equalities.filterMap fun eq => eq.linearCombo.constant?
  let inequalityConstants := p.inequalities.filterMap LinearCombo.constant?
  if equalityConstants.all (· = 0) ∧ inequalityConstants.all (· ≥ 0) then
    p.filterEqualities (fun eq => eq.linearCombo.constant? = none)
      |>.filterInequalities (fun lc => lc.constant? = none)
  else
    impossible

theorem processConstants_equalities_length (p : Problem) :
    p.processConstants.equalities.length ≤ p.equalities.length := by
  dsimp [processConstants]
  split
  · apply List.length_filter_le
  · apply Nat.zero_le

theorem processConstants_inequalities_length (p : Problem) :
    p.processConstants.inequalities.length ≤ p.inequalities.length := by
  dsimp [processConstants]
  split
  · apply List.length_filter_le
  · apply Nat.zero_le

theorem processConstants_sat (p : Problem) (v) (s : p.sat v) : p.processConstants.sat v := by
  dsimp [processConstants]
  split <;> rename_i w
  · exact Problem.filterEqualities_sat _ _ _ (Problem.filterInequalities_sat _ _ _ s)
  · exfalso
    simp only [Decidable.not_and] at w
    simp only [List.all_eq_true, List.mem_filterMap, decide_eq_true_eq, forall_exists_index,
      and_imp, not_forall, exists_prop, exists_and_left] at w
    rcases w with (⟨c, eq, w, m, ne⟩ | ⟨c, eq, w, m, ne⟩)
    · have := s.equalities w
      simp [eq.linearCombo.eval_eq_of_constant m] at this
      exact ne this
    · have := s.inequalities w
      simp [eq.eval_eq_of_constant m] at this
      exact ne this

theorem sat_of_processConstants_sat (p : Problem) (v) (s : p.processConstants.sat v) : p.sat v := by
  dsimp [processConstants] at s
  split at s <;> rename_i w
  · simp only [List.all_eq_true, List.mem_filterMap, decide_eq_true_eq, forall_exists_index,
      and_imp] at w
    rcases w with ⟨eqs, ineqs⟩
    constructor
    · exact s.possible
    · intro eq mem
      match h : eq.linearCombo.constant? with
      | some c =>
        rw [eq.linearCombo.eval_eq_of_constant h]
        exact eqs _ eq mem h
      | none =>
        apply s.equalities
        simp only [filterInequalities_hasEquality, filterEqualities_hasEquality]
        exact ⟨mem, decide_eq_true h⟩
    · intro lc mem
      match h : lc.constant? with
      | some c =>
        rw [lc.eval_eq_of_constant h]
        exact ineqs _ lc mem h
      | none =>
        apply s.inequalities
        simp only [filterInequalities_hasInequality, filterInequalities_hasEquality]
        exact ⟨mem, decide_eq_true h⟩
  · replace s := s.possible
    simp at s

/-- A problem is equivalent to the problem after processing constants. -/
def processConstants_equiv (p : Problem) : p.processConstants.equiv p :=
  equiv_of_sat_iff fun v => ⟨p.sat_of_processConstants_sat v, p.processConstants_sat v⟩

example : processConstants { equalities := [{linearCombo := {const := 1}}] } = impossible := rfl
example : processConstants { equalities := [{linearCombo := {const := 1}}] } |>.unsat := impossible_unsat
example : Problem.unsat { equalities := [{linearCombo := {const := 1}}] } :=
  impossible_unsat ∘ (processConstants_equiv _).mpr
example : Problem.unsat { inequalities := [{const := -1}] } :=
  impossible_unsat ∘ (processConstants_equiv _).mpr

theorem processConstants_equalities_of_equalitiesZero {p : Problem} (w : p.equalitiesZero) :
    p.processConstants.equalities.length = 0 := by
  dsimp [processConstants]
  split <;> (rename_i h; simp at h)
  · simp [List.length_eq_zero, List.filter_eq_nil, LinearCombo.constant?]
    intro eq m x m'
    rw [@List.mem_iff_get] at m'
    obtain ⟨n, rfl⟩ := m'
    simpa [LinearCombo.coeff, IntList.get, List.get?_coe] using w m n
  · rfl

end Problem

namespace LinearCombo

/--
To normalize an inequality, we divide through by the gcd of the coefficients,
using floor rounding when we divide the constant term.
-/
def normalizeInequality (lc : LinearCombo) : LinearCombo :=
  let gcd := lc.coeffs.gcd
  if gcd = 0 then
    { const := lc.const
      coeffs := [] }
  else
    { coeffs := lc.coeffs.sdiv gcd
      -- Since `gcd ≥ 0`, `ediv` and `fdiv` coincide: this is floor rounding.
      const := lc.const / gcd }

example : ({const := 1, coeffs := [2]} : LinearCombo).normalizeInequality =
    {const := 0, coeffs := [1]} := rfl
example : ({const := 5, coeffs := [6, 15]} : LinearCombo).normalizeInequality =
    {const := 1, coeffs := [2, 5]} := rfl
example : ({const := -5, coeffs := [6, 15]} : LinearCombo).normalizeInequality =
    {const := -2, coeffs := [2, 5]} := rfl
example : ({const := 10, coeffs := [6, 8]} : LinearCombo).normalizeInequality =
    {const := 5, coeffs := [3, 4]} := rfl

/--
To normalize an equality, we check if the constant term is divisible by the gcd of the coefficients.
If it is, we divide through by the gcd. Otherwise, the equality is unsatisfiable.
-/
def normalizeEquality (lc : LinearCombo) : LinearCombo :=
  let gcd := lc.coeffs.gcd
  if (gcd : Int) ∣ lc.const then
    { coeffs := lc.coeffs.sdiv gcd
      const := lc.const / gcd }
  else
    { coeffs := []
      const := 1 }

example : ({const := 1, coeffs := [2]} : LinearCombo).normalizeEquality = {const := 1} := rfl
example : ({const := -1, coeffs := [-2]} : LinearCombo).normalizeEquality = {const := 1} := rfl
example : ({const := 1, coeffs := [6, 9]} : LinearCombo).normalizeEquality = {const := 1} := rfl
example : ({const := 3, coeffs := [6, 9]} : LinearCombo).normalizeEquality =
    {const := 1, coeffs := [2, 3]} := rfl

@[simp] theorem normalizeInequality_eval {lc : LinearCombo} :
    lc.normalizeInequality.eval v ≥ 0 ↔ lc.eval v ≥ 0 := by
  rcases lc with ⟨const, coeffs⟩
  dsimp [normalizeInequality, eval]
  split <;> rename_i h
  · rw [IntList.gcd_eq_zero] at h
    simp [IntList.dot_of_left_zero h]
  · rw [IntList.dot_sdiv_gcd_left, ← Int.add_ediv_of_dvd_right (IntList.gcd_dvd_dot_left coeffs v),
      Int.div_nonneg_iff_of_pos]
    match coeffs.gcd, h with
    | (n+1), _ => exact Int.ofNat_succ_pos n

@[simp] theorem normalizeEquality_eval {lc : LinearCombo} :
    lc.normalizeEquality.eval v = 0 ↔ lc.eval v = 0 := by
  rcases lc with ⟨const, coeffs⟩
  dsimp [normalizeEquality, eval]
  split <;> rename_i h
  · simp only [IntList.dot_sdiv_gcd_left]
    by_cases w : coeffs.gcd = 0
    · simp only [w, Int.ofNat_zero, Int.zero_dvd, Int.ediv_zero, Int.add_zero, true_iff] at h ⊢
      simp only [h, Int.zero_add]
      simp at w
      rw [IntList.dot_of_left_zero w]
    · replace w : (coeffs.gcd : Int) ≠ 0 := Int.ofNat_ne_zero.mpr w
      rw [← Int.mul_eq_mul_right_iff w]
      have : (coeffs.gcd : Int) ∣ IntList.dot coeffs v := IntList.gcd_dvd_dot_left _ _
      simp_all [Int.add_mul, Int.ediv_mul_cancel]
  · simp (config := {decide := true}) only [IntList.dot_nil_left, Int.add_zero, false_iff]
    intro w
    apply h
    replace w := congrArg (fun x : Int => x % coeffs.gcd) w
    simp [Int.add_emod] at w
    exact Int.dvd_of_emod_eq_zero w

end LinearCombo

namespace Equality

@[simps]
def normalize (eq : Equality) : Equality :=
  { linearCombo := eq.linearCombo.normalizeEquality }
  -- TODO copy other fields?

theorem normalize_eval {eq : Equality} :
  eq.normalize.linearCombo.eval v = 0 ↔ eq.linearCombo.eval v = 0 := by simp

theorem normalize_minCoeff_le (eq : Equality) : eq.normalize.minCoeff ≤ eq.minCoeff := by
  dsimp [normalize, LinearCombo.normalizeEquality]
  split <;> rename_i dvd
  · rw [minCoeff_spec, minCoeff_spec]
    dsimp
    apply List.nonzeroMininum_map_le_nonzeroMinimum
    · intro a m
      simp only [Int.natAbs_eq_zero]
      constructor
      · rintro rfl; simp
      · intro h
        rw [← Int.ediv_mul_cancel (IntList.gcd_dvd _ m)]
        simp [h]
    · intro a _ _
      apply Int.natAbs_div_le_natAbs
  · simp [minCoeff_spec]

theorem normalize_minCoeff_zero (eq : Equality) (h : eq.minCoeff = 0) :
    eq.normalize.minCoeff = 0 := by
  have := eq.normalize_minCoeff_le
  simp_all

end Equality

namespace Problem

/-- To normalize a problem we normalize each equality and inequality. -/
@[simps]
def normalize (p : Problem) : Problem where
  possible := p.possible
  equalities := p.equalities.map Equality.normalize
  inequalities := p.inequalities.map LinearCombo.normalizeInequality

@[simp] theorem normalize_hasEquality {p : Problem} :
    p.normalize.hasEquality e ↔ ∃ e', p.hasEquality e' ∧ e'.normalize = e := by
  simp [hasEquality]

@[simp] theorem normalize_hasInequality {p : Problem} :
    p.normalize.hasInequality e ↔ ∃ e', p.hasInequality e' ∧ e'.normalizeInequality = e := by
  simp [hasInequality]

theorem normalize_sat (p : Problem) (h : p.sat v) : p.normalize.sat v where
  possible := h.possible
  equalities m := by
    simp only [normalize_hasEquality] at m
    obtain ⟨a, m, rfl⟩ := m
    simpa using h.equalities m
  inequalities m := by
    simp only [normalize_hasInequality] at m
    obtain ⟨a, m, rfl⟩ := m
    simpa using h.inequalities m

theorem sat_of_normalize_sat (p : Problem) (h : p.normalize.sat v) : p.sat v where
  possible := h.possible
  equalities m := by
    rw [← Equality.normalize_eval]
    apply h.equalities
    simp only [normalize_hasEquality]
    refine ⟨_, m, rfl⟩
  inequalities m := by
    rw [← LinearCombo.normalizeInequality_eval]
    apply h.inequalities
    simp only [normalize_hasInequality]
    refine ⟨_, m, rfl⟩

/-- The normalization of a problem is equivalent to the problem. -/
def normalize_equiv (p : Problem) : p.normalize.equiv p :=
  equiv_of_sat_iff fun _ => ⟨p.sat_of_normalize_sat, p.normalize_sat⟩

theorem normalize_equalitiesZero_of_equalitiesZero {p : Problem} (w : p.equalitiesZero) :
    p.normalize.equalitiesZero := by
  dsimp [equalitiesZero] at *
  intro eq m i
  simp only [normalize, List.mem_map] at m
  obtain ⟨eq', m', rfl⟩ := m
  specialize w m' i
  simp only [Equality.normalize, LinearCombo.normalizeEquality]
  split <;> simp_all [LinearCombo.coeff]

-- TODO: make sure this is fast and idempotent, because we do it a lot!
def tidy (p : Problem) : Problem :=
  p.normalize.processConstants.checkContradictions

theorem tidy_equalities_length (p : Problem) :
    p.tidy.equalities.length ≤ p.equalities.length :=
  calc p.tidy.equalities.length
      ≤ p.normalize.processConstants.equalities.length := checkContradictions_equalities_length _
    _ ≤ p.normalize.equalities.length := processConstants_equalities_length _
    _ = p.equalities.length := List.length_map _ _

theorem tidy_inequalities_length (p : Problem) :
    p.tidy.inequalities.length ≤ p.inequalities.length :=
  calc p.tidy.inequalities.length
      ≤ p.normalize.processConstants.inequalities.length := checkContradictions_inequalities_length _
    _ ≤ p.normalize.inequalities.length := processConstants_inequalities_length _
    _ = p.inequalities.length := List.length_map _ _

def tidy_equiv (p : Problem) : p.tidy.equiv p :=
  (Problem.checkContradictions_equiv _).trans ((Problem.processConstants_equiv _).trans p.normalize_equiv)

end Problem

namespace LinearCombo

/-- Replace `xᵢ` in `b` with `r`. -/
def substitute (b : LinearCombo) (i : Nat) (r : LinearCombo) : LinearCombo :=
  if b.coeff i = 0 then
    b
  else
    b.setCoeff i 0 + (b.coeff i * r)

@[simp] theorem substitute_eval :
    (substitute b i r).eval v = b.eval v + b.coeff i * (r.eval v - v.get i) := by
  rw [substitute]
  split
  · simp_all
  · simp only [add_eval, setCoeff_eval, Int.zero_sub, Int.neg_mul, smul_eval, Int.add_assoc,
      Int.mul_sub]
    simp only [Int.sub_eq_add_neg, Int.add_comm (_ * _)]

end LinearCombo

namespace Equality

/--
Assuming `a = 0`, solve for the variable `xᵢ`, as a `LinearCombo`.

The result is only valid if `(a.coeff i).natAbs = 1`.
-/
def solveFor (a : Equality) (i : Nat) : LinearCombo :=
  (- (a.linearCombo.coeff i)) * a.linearCombo.setCoeff i 0

end Equality

theorem Int.mul_self_eq_one_of_natAbs_eq_one {x : Int} (h : x.natAbs = 1) : x * x = 1 := by
  match x, h with
  | 1,            _ => simp
  | Int.negSucc 0, _ => simp

namespace LinearCombo

theorem substitute_solveFor_eval (w : (a.linearCombo.coeff i).natAbs = 1) (h : a.linearCombo.eval v = 0) :
    (LinearCombo.substitute b i (Equality.solveFor a i)).eval v = b.eval v := by
  simp only [Equality.solveFor, substitute_eval, smul_eval, setCoeff_eval, h, Int.zero_sub, Int.neg_mul,
    Int.zero_add, Int.mul_neg, Int.neg_neg]
  rw [← Int.mul_assoc (a.linearCombo.coeff i), Int.mul_self_eq_one_of_natAbs_eq_one w, Int.one_mul,
    Int.sub_self, Int.mul_zero, Int.add_zero]

end LinearCombo

namespace Equality

-- Are we going to regret not storing matrices? Or row operations??
def backSubstitution (a : Equality) (i : Nat) (w : IntList) : IntList :=
  w.set i ((a.solveFor i).eval w)

attribute [simp] Int.sub_self

theorem eval_backSubstitution (a : Equality) (b : LinearCombo) (i : Nat) (w : IntList) :
    b.eval (a.backSubstitution i w) = (b.substitute i (solveFor a i)).eval w := by
  simp [backSubstitution]

open LinearCombo

theorem eval_backSubstitution_self (a : Equality) (w : (a.linearCombo.coeff i).natAbs = 1) :
    a.linearCombo.eval (a.backSubstitution i v) = 0 := by
  simp only [backSubstitution, solveFor, smul_eval, setCoeff_eval, Int.zero_sub, Int.neg_mul,
    eval_set, Int.mul_sub, Int.mul_neg]
  rw [← Int.mul_assoc]
  rw [Int.mul_self_eq_one_of_natAbs_eq_one w]
  simp only [Int.one_mul, Int.neg_add, Int.neg_neg, Int.add_sub_cancel]
  simp only [← Int.sub_eq_add_neg, Int.sub_self]

@[simps]
def substitute (a : Equality) (i : Nat) (r : LinearCombo) : Equality :=
  { linearCombo := a.linearCombo.substitute i r }
  -- TODO: Other fields?

end Equality

namespace Problem

-- This only makes sense when `a ∈ p.equalities` and `(a.linearCombo.coeff i).natAbs = 1`.
-- TODO should we delete the variable, too?
@[simps]
def eliminateEquality (p : Problem) (a : Equality) (i : Nat) : Problem :=
  let r := a.solveFor i
  { possible := p.possible
    equalities := (p.equalities.erase a).map fun eq => eq.substitute i r
    inequalities := p.inequalities.map fun ineq => ineq.substitute i r }

theorem eliminateEquality_hasEquality (w : (∃ e', (e' ≠ a ∧ p.hasEquality e') ∧ e'.substitute i (a.solveFor i) = e)) :
    (eliminateEquality p a i).hasEquality e := by
  obtain ⟨e', ⟨ne, m⟩, rfl⟩ := w
  simp only [hasEquality, eliminateEquality_equalities, List.mem_map, ne_eq]
  refine ⟨e', (List.mem_erase_of_ne ne).mpr m, rfl⟩

theorem of_eliminateEquality_hasEquality (w : (eliminateEquality p a i).hasEquality e) :
    (∃ e', p.hasEquality e' ∧ e'.substitute i (a.solveFor i) = e) := by
  simp only [hasEquality, eliminateEquality_equalities, List.mem_map, ne_eq] at w
  obtain ⟨e, m, rfl⟩ := w
  refine ⟨e, List.mem_of_mem_erase m, rfl⟩

@[simp] theorem eliminateEquality_hasInequality :
    (eliminateEquality p a i).hasInequality lc ↔
      ∃ lc', p.hasInequality lc' ∧ lc'.substitute i (a.solveFor i) = lc := by
  simp only [hasInequality]
  simp only [eliminateEquality_inequalities, List.mem_map]

theorem eliminateEquality_equalities_length (p : Problem) {a : Equality} (i : Nat)
    (ma : a ∈ p.equalities) :
    (p.eliminateEquality a i).equalities.length + 1 = p.equalities.length := by
  simp only [eliminateEquality_equalities, List.length_map, ma, List.length_erase_of_mem]
  rw [Nat.add_one, Nat.succ_pred]
  rw [← @Nat.pos_iff_ne_zero]
  exact List.length_pos_of_mem ma

theorem eliminateEquality_sat (p : Problem) {a : Equality} {i : Nat} (ma : a ∈ p.equalities)
    (w : (a.linearCombo.coeff i).natAbs = 1) (v) (s : p.sat v) : (p.eliminateEquality a i).sat v where
  possible := s.possible
  equalities mb := by
    obtain ⟨b, mb', rfl⟩ := of_eliminateEquality_hasEquality mb
    rw [Equality.substitute_linearCombo, LinearCombo.substitute_solveFor_eval w (s.equalities ma),
      s.equalities mb']
  inequalities mb := by
    simp only [eliminateEquality_hasInequality] at mb
    obtain ⟨b, mb, rfl⟩ := mb
    rw [LinearCombo.substitute_solveFor_eval w (s.equalities ma)]
    exact s.inequalities mb

theorem sat_of_eliminateEquality_sat (p : Problem) {a : Equality} {i : Nat}
    (m : a ∈ p.equalities) (w : (a.linearCombo.coeff i).natAbs = 1) (v)
    (s : (p.eliminateEquality a i).sat v) : p.sat (a.backSubstitution i v) where
  possible := s.possible
  equalities := by
    intro eq mb
    by_cases h : eq = a
    · subst h
      rw [Equality.eval_backSubstitution_self _ w]
    · rw [Equality.eval_backSubstitution, ← Equality.substitute_linearCombo]
      apply s.equalities
      apply eliminateEquality_hasEquality
      refine ⟨eq, ⟨h, mb⟩, rfl⟩
  inequalities mb := by
    rw [Equality.eval_backSubstitution]
    apply s.inequalities
    simp only [eliminateEquality_hasInequality]
    exact ⟨_, mb, rfl⟩

/-- The normalization of a problem is equivalent to the problem. -/
def eliminateEquality_equiv (p : Problem) {a : Equality} {i : Nat} (m : a ∈ p.equalities)
    (w : (a.linearCombo.coeff i).natAbs = 1) : (p.eliminateEquality a i).equiv p where
  mp := fun ⟨v, s⟩ => ⟨a.backSubstitution i v, p.sat_of_eliminateEquality_sat m w v s⟩
  mpr := fun ⟨v, s⟩ => ⟨v, p.eliminateEquality_sat m w v s⟩

end Problem



namespace Problem

def smallCoeffEquality (p : Problem) : Option (Equality × Nat) :=
  p.equalities.findSome? fun e => match e.smallCoeff with | some i => some (e, i) | none => none

theorem smallCoeffEquality_mem {p : Problem} (w : p.smallCoeffEquality = some (e, i)) :
    e ∈ p.equalities := by
  obtain ⟨e', m, h⟩ := List.exists_of_findSome?_eq_some w
  split at h <;> simp_all

theorem smallCoeffEquality_natAbs_Eq {p : Problem} (w : p.smallCoeffEquality = some (e, i)) :
    (e.linearCombo.coeff i).natAbs = 1 := by
  obtain ⟨e', m, h⟩ := List.exists_of_findSome?_eq_some w
  split at h <;> simp_all
  exact e.smallCoeff_natAbs ‹_›

def eliminateEasyEqualities_aux (n : Nat) (p : Problem) (w : p.equalities.length ≤ n) : Problem :=
  match n with
  | 0 => p
  | n+1 =>
    match h : p.smallCoeffEquality with
    | some (e, i) =>
      have m : e ∈ p.equalities := smallCoeffEquality_mem h
      have : (p.equalities.erase e).length < p.equalities.length := by
        rw [← p.eliminateEquality_equalities_length i m]
        simp
      have : (p.eliminateEquality e i).equalities.length ≤ n := by
        simpa using Nat.lt_succ.mp (Nat.lt_of_lt_of_le this w)
      eliminateEasyEqualities_aux n (p.eliminateEquality e i) this
    | none => p

def eliminateEasyEqualities (p : Problem) : Problem :=
  match p.equalities with
  | [] => p
  | _ => p.eliminateEasyEqualities_aux _ (Nat.le_refl _)

def eliminateEasyEqualities_equiv_aux (n : Nat) (p : Problem) (w : p.equalities.length ≤ n) :
    (p.eliminateEasyEqualities_aux n w).equiv p :=
  match n with
  | 0 => equiv.refl p
  | n+1 => by
    dsimp [eliminateEasyEqualities_aux]
    -- TODO I'm unhappy to have to use `split` here.
    -- Just using `match h : p.smallCoeffEquality with` results in `tag not found`.
    split
    · rename_i e i h
      have m : e ∈ p.equalities := smallCoeffEquality_mem h
      have : (p.equalities.erase e).length < p.equalities.length := by
        rw [← p.eliminateEquality_equalities_length i m]
        simp
      have : (p.eliminateEquality e i).equalities.length ≤ n := by
        simpa using Nat.lt_succ.mp (Nat.lt_of_lt_of_le this w)
      exact (eliminateEasyEqualities_equiv_aux n (p.eliminateEquality e i) this).trans
        (p.eliminateEquality_equiv m (smallCoeffEquality_natAbs_Eq h))
    · exact equiv.refl p

def eliminateEasyEqualities_equiv (p : Problem) : p.eliminateEasyEqualities.equiv p := by
  dsimp [eliminateEasyEqualities]
  split
  · exact equiv.refl p
  · exact p.eliminateEasyEqualities_equiv_aux _ (Nat.le_refl _)

end Problem

namespace LinearCombo

@[simps]
def bmod (lc : LinearCombo) (m : Nat) : LinearCombo where
  const := Int.bmod lc.const m
  coeffs := lc.coeffs.map (fun a => Int.bmod a m)

@[simp] theorem coeff_bmod (lc : LinearCombo) (m : Nat) (k : Nat) :
    (lc.bmod m).coeff k = Int.bmod (lc.coeff k) m := by
  simp [bmod, coeff, IntList.get_map]

theorem dvd_eval_sub_bmod_eval (lc : LinearCombo) (m : Nat) (v : IntList) :
    (m : Int) ∣ lc.eval v - (lc.bmod m).eval v := by
  dsimp [eval]
  rw [← Int.sub_sub, Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.add_right_comm lc.const,
    Int.add_assoc, ←Int.sub_eq_add_neg, ←Int.sub_eq_add_neg, ←IntList.dot_sub_left]
  apply Int.dvd_add
  · rw [← Int.neg_sub, Int.dvd_neg]
    exact Int.dvd_bmod_sub_self
  · apply IntList.dvd_dot_of_dvd_left
    intro x m
    obtain ⟨i, h⟩ := List.get?_of_mem m
    replace h := congrArg (fun o => o.getD 0) h
    change IntList.get _ _ = _ at h
    simp only [IntList.get_map, IntList.sub_get, Int.bmod_zero, Option.getD_some] at h
    rw [← h, ← Int.neg_sub, Int.dvd_neg]
    exact Int.dvd_bmod_sub_self

/--
Given an equation `eq : c + ∑ aᵢ * xᵢ = 0` and an index `k`, produce the equation
`bmod c m + ∑ (bmod aᵢ m) * xᵢ + m xₙ`
where `m = |aₖ| + 1`.

(Here `n` is large enough to be a fresh variable in all constraints in the problem.)

Since `bmod x m` differs from `x` by a multiple of `m`, this equation must admit a solution.
Note that the coefficient of `xᵢ` in the new equation is `- sign aₖ`, so we can solve for `xᵢ`.
-/
def shrinkingConstraint (eq : LinearCombo) (k : Nat) (n : Nat) : LinearCombo :=
  let m := (eq.coeff k).natAbs + 1
  (eq.bmod m).setCoeff n m

theorem shrinkingConstraint_coeff_natAbs {eq : LinearCombo} (h : 1 < (eq.coeff k).natAbs) (w : k < n) :
    ((eq.shrinkingConstraint k n).coeff k).natAbs = 1 := by
  rw [shrinkingConstraint, setCoeff_coeff_of_ne, coeff_bmod, Int.bmod_natAbs_plus_one _ h]
  · rw [Int.natAbs_neg, Int.natAbs_sign, if_neg]
    intro
    simp_all (config := {decide := true})
  · exact Nat.ne_of_lt w

def shrinkingConstraintSolution (eq : LinearCombo) (k : Nat) (n : Nat) (v : IntList) : IntList :=
  let m := (eq.coeff k).natAbs + 1
  -- It might be more natural to leave out the `v.get n` term here,
  -- as we will only use this with `n` a fresh variable, so `v.get n = 0`.
  -- The calculations are slightly smoother with this term, however.
  v.set n (v.get n + ((eq - eq.shrinkingConstraint k n).eval v) / m)

attribute [simp] Int.dvd_neg

theorem shrinkingConstraint_eval {eq : LinearCombo} (w : eq.eval v = 0)
    (h₁ : eq.coeffs.length ≤ n) :
    (eq.shrinkingConstraint k n).eval (eq.shrinkingConstraintSolution k n v) = 0 := by
  dsimp [shrinkingConstraint, shrinkingConstraintSolution]
  simp only [Int.natCast_add, Int.ofNat_one, sub_eval, setCoeff_eval, coeff_bmod, eval_set, setCoeff_coeff_self]
  replace h₁ : eq.coeff n = 0 := IntList.get_of_length_le h₁
  rw [Int.mul_sub, Int.mul_add, Int.add_comm (a := _ * _), Int.add_sub_cancel, Int.mul_ediv_cancel']
  · simp [h₁, w, ← Int.sub_eq_add_neg]
  · -- Side goal about divisibility.
    simp only [h₁, Int.bmod_zero, Int.sub_zero, Int.mul_zero, Int.add_zero, ← Int.sub_sub]
    apply Int.dvd_add
    · apply dvd_eval_sub_bmod_eval
    · rw [Int.dvd_neg]
      apply Int.dvd_mul_right

def maxNatAbs (eq : LinearCombo) : Nat := eq.coeffs.foldr (fun x r => Nat.max x.natAbs r) 0

def memNatAbs (eq : LinearCombo) (x : Nat) : Bool := eq.coeffs.any fun y => y.natAbs = x

end LinearCombo


namespace Problem

@[simps]
def addEquality (p : Problem) (eq : Equality) : Problem where
  possible := p.possible
  equalities := eq :: p.equalities
  inequalities := p.inequalities

@[simp] theorem addEquality_hasEquality {p : Problem} :
    (p.addEquality eq).hasEquality e ↔ e = eq ∨ p.hasEquality e := by
  simp [hasEquality]

def addEquality_equiv (p : Problem) {eq : Equality} (f : p → p)
    (w : ∀ x : p, eq.linearCombo.eval (f x).1 = 0) :
    (p.addEquality eq).equiv p where
  mp := fun ⟨v, h⟩ => ⟨v, { h with equalities := fun m => h.equalities (by simpa using Or.inr m) }⟩
  mpr := fun x => ⟨(f x).1,
    { possible := (f x).2.possible
      equalities := fun m => by
        simp at m
        rcases m with rfl | m
        · exact w x
        · exact (f x).2.equalities m
      inequalities := fun m => (f x).2.inequalities m }⟩

/--
Add a new equality to a problem,
and then immediately solve that equality for the `i`-th variable.
-/
def addAndEliminateEquality (p : Problem) (eq : Equality) (i : Nat) : Problem :=
  (p.addEquality eq).eliminateEquality eq i

/--
Suppose for every solution to `p` we can find a solution to `p`
at which an equality `eq` also vanishes.

Further suppose that the `i`-th coefficient of `eq` has absolute value `1`.

Then adding `eq` and solving for the `i`-th variable produces
a problem equivalent to the original problem.
-/
def addAndEliminateEquality_equiv (p : Problem) (eq : Equality) (i : Nat)
    (f : p → p)
    (w : ∀ x : p, eq.linearCombo.eval (f x).1 = 0)
    (h : (eq.linearCombo.coeff i).natAbs = 1) :
    (p.addAndEliminateEquality eq i).equiv p :=
  equiv.trans (eliminateEquality_equiv _ (by simp) h) (addEquality_equiv _ f w)

-- We will need to prove properties of this.
-- Should we store the value?
def numVars (p : Problem) : Nat :=
  List.foldr (Nat.max)
    (List.foldr (Nat.max) 0 (p.equalities.map (fun eq => eq.linearCombo.coeffs.length)))
    (p.inequalities.map (fun ineq => ineq.coeffs.length))

theorem equality_length_le_numVars {p : Problem} {eq : Equality} (m : eq ∈ p.equalities) :
    eq.linearCombo.coeffs.length ≤ p.numVars := by
  dsimp [numVars]
  generalize p.equalities = equalities at m -- Sad we can't just `induction p.equalities`.
  -- Humans should not need to write proofs like this one.
  induction p.inequalities with
  | nil =>
    induction equalities with
    | nil => simp_all
    | cons eq ineqs ih =>
      simp only [List.map_cons, List.foldr_cons, List.map_nil, List.foldr_nil]
      simp only [List.mem_cons] at m
      rcases m with (rfl | m)
      · apply Nat.le_max_left
      · apply Nat.le_trans (ih m) _
        apply Nat.le_max_right
  | cons ineq ineqs ih =>
    simp only [List.map_cons, List.foldr_cons]
    apply Nat.le_trans ih _
    apply Nat.le_max_right

theorem minCoeffIdx_lt_numVars {p : Problem} {eq : Equality} (m : eq ∈ p.equalities)
    (h : eq.minCoeff ≠ 0) : eq.minCoeffIdx < p.numVars := by
  have : eq.minCoeffIdx < eq.linearCombo.coeffs.length := by
    rw [← eq.minCoeffIdx_spec, LinearCombo.coeff, ne_eq, Int.natAbs_eq_zero] at h
    exact IntList.lt_length_of_get_nonzero h
  apply Nat.lt_of_lt_of_le
  · exact this
  · apply equality_length_le_numVars m

theorem inequality_length_le_numVars
    {p : Problem} {ineq : LinearCombo} (m : ineq ∈ p.inequalities) :
    ineq.coeffs.length ≤ p.numVars := by
  dsimp [numVars]
  generalize p.inequalities = inequalities at m
  induction inequalities with
  | nil => simp_all
  | cons ineq ineqs ih =>
    simp only [List.map_cons, List.foldr_cons]
    simp only [List.mem_cons] at m
    rcases m with (rfl | m)
    · apply Nat.le_max_left
    · apply Nat.le_trans (ih m) _
      apply Nat.le_max_right

theorem equality_eval_set_numVars {p : Problem} {eq : Equality} (m : eq ∈ p.equalities) :
    eq.linearCombo.eval (v.set (p.numVars) x) = eq.linearCombo.eval v := by
  rw [LinearCombo.eval_set]
  have t : eq.linearCombo.coeff p.numVars = 0 :=
    IntList.get_of_length_le (equality_length_le_numVars m)
  simp [t]

theorem inequality_eval_set_numVars {p : Problem} {ineq : LinearCombo} (m : ineq ∈ p.inequalities) :
    ineq.eval (v.set (p.numVars) x) = ineq.eval v := by
  rw [LinearCombo.eval_set]
  have t : ineq.coeff p.numVars = 0 :=
    IntList.get_of_length_le (inequality_length_le_numVars m)
  simp [t]

/--
Given an equation `eq` in a problem, and a solution to that problem,
generate a new solution at which `eq.linearCombo.shrinkingConstraint` also vanishes.

(This is possible because that constraint introduces a new variable `α`, and is of the form
`m * α = ...` where the RHS is divisible by `m`.)
-/
def shrinkEqualitySolution (p : Problem) (eq : Equality) (i : Nat) : p → p :=
  let n := p.numVars
  fun ⟨v, h⟩ => ⟨eq.linearCombo.shrinkingConstraintSolution i n v,
  { possible := h.possible
    equalities := fun m => by
      rw [LinearCombo.shrinkingConstraintSolution, equality_eval_set_numVars m]
      exact h.equalities m
    inequalities := fun m => by
      rw [LinearCombo.shrinkingConstraintSolution, inequality_eval_set_numVars m]
      exact h.inequalities m }⟩

theorem shrinkEqualitySolution_spec
    (p : Problem) (eq : Equality) (m : eq ∈ p.equalities) (i : Nat) :
    ∀ x : p, (eq.linearCombo.shrinkingConstraint i p.numVars).eval
      (p.shrinkEqualitySolution eq i x).1 = 0 := by
  rintro ⟨v, h⟩
  dsimp [shrinkEqualitySolution]
  apply LinearCombo.shrinkingConstraint_eval
  · exact h.equalities m
  · exact equality_length_le_numVars m

-- FIXME: do we want to normalize everything again? presumably yes?
def shrinkEqualityCoeffs (p : Problem) (eq : Equality) (i : Nat) : Problem :=
  let n := p.numVars
  p.addAndEliminateEquality { linearCombo := eq.linearCombo.shrinkingConstraint i n } i

theorem shrinkEqualityCoeffs_length_le (p : Problem) (eq : Equality) (i : Nat) :
    (p.shrinkEqualityCoeffs eq i).equalities.length ≤ p.equalities.length := by
  dsimp only [shrinkEqualityCoeffs, addAndEliminateEquality]
  let n := p.numVars
  let eq' : Equality := { linearCombo := eq.linearCombo.shrinkingConstraint i n }
  have := eliminateEquality_equalities_length (p.addEquality eq') i (List.mem_cons_self _ _)
  apply Nat.le_of_eq
  simpa only [addEquality_equalities, List.length_cons, Nat.succ_eq_add_one,
    Nat.add_right_cancel_iff] using this

def shrinkEqualityCoeffs_equiv (p : Problem) (eq : Equality) (m : eq ∈ p.equalities) (i : Nat)
    (h : 1 < (eq.linearCombo.coeff i).natAbs) (w : i < p.numVars) :
    (p.shrinkEqualityCoeffs eq i).equiv p :=
  addAndEliminateEquality_equiv _ _ _
    (p.shrinkEqualitySolution eq i)
    (p.shrinkEqualitySolution_spec eq m i)
    (LinearCombo.shrinkingConstraint_coeff_natAbs h w)

/-- The minimal absolute value of a nonzero coefficient appearing in an equality. -/
def minEqualityCoeff (p : Problem) : Nat :=
  p.equalities.map (fun eq => eq.minCoeff) |>.nonzeroMinimum

@[simp] theorem impossible_minEqualityCoeff : impossible.minEqualityCoeff = 0 := rfl

/-!
Unfortunately it's simply not true that `p.normalize.minEqualityCoeff ≤ p.minEqualityCoeff`,
because the minimal coefficient could disappear if it appears in a constraint
where the gcd of the coefficients does not divide the constant term.

Fortunately in this case `p.normalize.processConstants = impossible`,
but we still need to work a bit here.
-/

-- theorem normalize_minEqualityCoeff_le (p : Problem) :
--     p.normalize.minEqualityCoeff ≤ p.minEqualityCoeff := by
--   dsimp [normalize, minEqualityCoeff]
--   rw [List.map_map]
--   dsimp only [Function.comp]
--   sorry

theorem normalize_processConstants_impossible_or₁ (p : Problem) :
    p.normalize.processConstants = impossible ∨
      ∀ {eq}, eq ∈ p.equalities → (eq.linearCombo.coeffs.gcd : Int) ∣ eq.linearCombo.const := by
  apply Decidable.or_iff_not_imp_right.mpr
  simp only [not_forall, exists_prop, forall_exists_index, and_imp]
  intro eq m h
  dsimp [processConstants]
  rw [if_neg]
  rw [Decidable.not_and]
  left
  simp only [List.all_eq_true, List.mem_filterMap, decide_eq_true_eq, forall_exists_index, and_imp,
    not_forall, exists_prop, exists_and_left]
  refine ⟨1, eq.normalize, List.mem_map_of_mem _ m, ?_, by decide⟩
  dsimp [Equality.normalize, LinearCombo.normalizeEquality]
  rw [if_neg h]
  rfl

-- theorem _root_.IntList.sdiv_gcd_minNatAbs {xs : IntList} :
--     (xs.sdiv xs.gcd).minNatAbs = xs.minNatAbs / xs.gcd := by
--   rw [List.minNatAbs_eq_nonzero_iff]
--   · constructor
--     · sorry
--     · sorry
--   · sorry

-- theorem normalize_processConstants_impossible_or₂ (p : Problem) :
--     p.normalize.processConstants = impossible ∨
--       ∀ {eq}, eq ∈ p.equalities → eq.minCoeff ≠ 0 →
--         eq.normalize.minCoeff ≠ 0 ∧ eq.normalize.minCoeff ≤ eq.minCoeff := by
--   cases p.normalize_processConstants_impossible_or₁ with
--   | inl h => left; exact h
--   | inr h =>
--     right
--     intro eq m ne
--     specialize h m
--     dsimp [Equality.normalize, LinearCombo.normalizeEquality]
--     simp only [if_pos h]
--     rw [Equality.minCoeff_spec, Ne, List.minNatAbs_eq_zero_iff] at ne
--     rw [Equality.minCoeff_spec, List.minNatAbs_eq_zero_iff]
--     simp only [not_forall, exists_prop] at *
--     obtain ⟨x, xm, xne⟩ := ne
--     constructor
--     · refine ⟨_, IntList.mem_sdiv xm, ?_⟩
--       intro w
--       apply xne
--       have dvd : (eq.linearCombo.coeffs.gcd : Int) ∣ x := IntList.gcd_dvd _ xm
--       rw [← Int.ediv_mul_cancel dvd]
--       simp_all
--     · rw [IntList.sdiv_gcd_minNatAbs]
--       calc
--         _ ≤ eq.linearCombo.coeffs.minNatAbs := by apply Nat.div_le_self
--         _ ≤ _ := by rw [Equality.minCoeff_spec]; apply Nat.le_refl

-- theorem normalize_processConstants_impossible_or₃ (p : Problem) :
--     p.normalize.processConstants = impossible ∨
--       p.normalize.minEqualityCoeff ≤ p.minEqualityCoeff := by
--   cases p.normalize_processConstants_impossible_or₂ with
--   | inl h => exact Or.inl h
--   | inr h =>
--     right
--     apply List.nonzeroMininum_map_le_nonzeroMinimum
--     · intro eq m
--       specialize h m
--       constructor
--       · exact eq.normalize_minCoeff_zero
--       · intro w
--         by_contra e
--         exact (h e).1 w
--     · intro eq _ _
--       apply Equality.normalize_minCoeff_le

theorem processConstants_minEqualityCoeff_le (p : Problem) :
    p.processConstants.minEqualityCoeff ≤ p.minEqualityCoeff := by
  dsimp [processConstants]
  split
  · dsimp [minEqualityCoeff]
    simp only [Equality.constant?_eq_none_iff]
    simp only [List.nonzeroMinimum]
    rw [List.map_filter, List.map_filter, List.filter_filter]
    simp only [ne_eq, decide_not, Function.comp_apply, Bool.not_eq_true', decide_eq_false_iff_not,
      and_self]
    apply Nat.le_refl
  · simp

-- theorem normalize_processConstants_minEqualityCoeff_le (p : Problem) :
--     p.normalize.processConstants.minEqualityCoeff ≤ p.minEqualityCoeff := by
--   cases p.normalize_processConstants_impossible_or₃ with
--   | inl h => simp_all
--   | inr h => calc
--       _ ≤ _ := processConstants_minEqualityCoeff_le _
--       _ ≤ _ := h

theorem checkContradictions_minEqualityCoeff_le (p : Problem) :
    p.checkContradictions.minEqualityCoeff ≤ p.minEqualityCoeff := by
  dsimp [checkContradictions]
  split <;> simp

-- theorem tidy_minEqualityCoeff_le (p : Problem) :
--     p.tidy.minEqualityCoeff ≤ p.minEqualityCoeff :=
--   calc
--     _ ≤ _ := checkContradictions_minEqualityCoeff_le _
--     _ ≤ _ := normalize_processConstants_minEqualityCoeff_le _

-- TODO fast lookup!
def minCoeffEquality (p : Problem) (w : p.minEqualityCoeff ≠ 0) : Equality :=
  match h : p.equalities.find? fun eq => eq.minCoeff = p.minEqualityCoeff with
  | some eq => eq
  | none => by
    exfalso
    rw [List.find?_eq_none] at h
    obtain ⟨eq, m, q⟩ := List.mem_map.mp (List.nonzeroMinimum_mem w)
    exact h eq m (decide_eq_true_eq.mpr q)

/-- Anything is true about `False.elim _`. -/
theorem _root_.False.elim_spec {x : False} (P : α → Prop) : P (False.elim x) :=
  False.elim x

theorem minCoeffEquality_mem (p : Problem) (w : p.minEqualityCoeff ≠ 0) :
    p.minCoeffEquality w ∈ p.equalities := by
  dsimp [minCoeffEquality]
  split <;> rename_i h
  · exact List.mem_of_find?_eq_some h
  · exact False.elim_spec (· ∈ p.equalities)

theorem minCoeffEquality_minCoeff (p : Problem) (w : p.minEqualityCoeff ≠ 0) :
    (p.minCoeffEquality w).minCoeff = p.minEqualityCoeff := by
  dsimp [minCoeffEquality]
  split <;> rename_i h
  · simpa using List.find?_some h
  · exact False.elim_spec (Equality.minCoeff · = p.minEqualityCoeff)

theorem equalitiesZero_of_minEqualityCoeff_zero {p : Problem} (w : p.minEqualityCoeff = 0) :
    p.equalitiesZero := by
  intro eq m
  have : eq.minCoeff = 0 := by
    by_contra h
    exact Nat.ne_of_gt (List.nonzeroMinimum_pos (List.mem_map_of_mem Equality.minCoeff m) h) w
  apply eq.coeff_zero_of_minCoeff_zero this

theorem tidy_equalities_of_minEqualityCoeff_eq_zero {p : Problem} (w : p.minEqualityCoeff = 0) :
    p.tidy.equalities.length = 0 := by
  dsimp only [tidy, checkContradictions]
  split
  · rfl
  · apply processConstants_equalities_of_equalitiesZero
    apply normalize_equalitiesZero_of_equalitiesZero
    exact equalitiesZero_of_minEqualityCoeff_zero w

-- theorem shrinkEqualityCoeffs_minEqualityCoeff_le (p : Problem) (eq : Equality) (i : Nat) :
--     (p.shrinkEqualityCoeffs eq i).minEqualityCoeff ≤ p.minEqualityCoeff :=
--   sorry

def shrinkEqualityCoeffsAndTidy (p : Problem) (eq : Equality) (i : Nat) : Problem :=
  (p.shrinkEqualityCoeffs eq i).tidy

theorem shrinkEqualityCoeffsAndTidy_length_le (p : Problem) (eq : Equality) (i : Nat) :
    (p.shrinkEqualityCoeffsAndTidy eq i).equalities.length ≤ p.equalities.length :=
  calc
    _ ≤ _ := tidy_equalities_length _
    _ ≤ _ := shrinkEqualityCoeffs_length_le _ _ _

-- theorem shrinkEqualityCoeffsAndTidy_minEqualityCoeff_le (p : Problem) (eq : Equality) (i : Nat) :
--     (p.shrinkEqualityCoeffsAndTidy eq i).minEqualityCoeff ≤ p.minEqualityCoeff :=
--   calc
--     _ ≤ _ := tidy_minEqualityCoeff_le _
--     _ ≤ _ := shrinkEqualityCoeffs_minEqualityCoeff_le p eq i

def shrinkEqualityCoeffsAndTidy_equiv (p : Problem) (eq : Equality) (m : eq ∈ p.equalities)
    (i : Nat) (h : 1 < (eq.linearCombo.coeff i).natAbs) (w : i < p.numVars) :
    (p.shrinkEqualityCoeffsAndTidy eq i).equiv p :=
  (tidy_equiv _).trans
    (p.shrinkEqualityCoeffs_equiv eq m i h w)

-- TODO make sure this is fast, i.e. don't use `find?`!
/-- Given that the minimal coefficient in an equality is 1, select such an equality. -/
def easyEquality (p : Problem) (w : p.minEqualityCoeff = 1) : Equality :=
  match h : p.equalities.find? fun eq => eq.minCoeff = 1 with
  | some eq => eq
  | none => by
    exfalso
    rw [List.find?_eq_none] at h
    specialize h (p.minCoeffEquality (by simp_all))
    simp only [minCoeffEquality_minCoeff, decide_eq_true_eq] at h
    apply h (minCoeffEquality_mem p _) w

theorem easyEquality_mem (p : Problem) (h : p.minEqualityCoeff = 1) :
    p.easyEquality h ∈ p.equalities := by
  dsimp [easyEquality]
  split <;> rename_i h
  · exact List.mem_of_find?_eq_some h
  · exact False.elim_spec (· ∈ p.equalities)

theorem easyEquality_minCoeff (p : Problem) (h : p.minEqualityCoeff = 1) :
    (p.easyEquality h).minCoeff = 1 := by
  dsimp [easyEquality]
  split <;> rename_i h
  · simpa using List.find?_some h
  · exact False.elim_spec (Equality.minCoeff · = 1)

/-- Given that the minimal coefficient in an equality is 1, eliminate such an equality. -/
def eliminateEasyEquality (p : Problem) (h : p.minEqualityCoeff = 1) : Problem :=
  let eq := p.easyEquality h
  (p.eliminateEquality eq eq.minCoeffIdx).tidy

/-- `eliminateEasyEquality` produces an equivalent problem. -/
def eliminateEasyEquality_equiv (p : Problem) (h) :
    (p.eliminateEasyEquality h).equiv p :=
  (tidy_equiv _).trans
    (p.eliminateEquality_equiv (p.easyEquality_mem h)
      ((p.easyEquality h).minCoeffIdx_spec.trans (p.easyEquality_minCoeff h)))

theorem eliminateEasyEquality_equalities_length (p : Problem) (h) :
    (p.eliminateEasyEquality h).equalities.length < p.equalities.length :=
  calc
    _ ≤ _ := Nat.add_le_add_right (tidy_equalities_length _) 1
    _ = _ := p.eliminateEquality_equalities_length _ (p.easyEquality_mem h)

/--
For each equality with a coefficient with absolute value `p.minEqualityCoeff`,
compute the largest absolute value of the coefficients,
and then take the smallest of these.
-/
-- There's no need for this to be efficient,
-- as we only use it in termination proofs and it is not computed.
-- TODO perhaps worth verifying this by making it really **inefficient**!
def maxEqualityCoeff (p : Problem) : Nat :=
  p.equalities.filter (fun eq => eq.linearCombo.memNatAbs p.minEqualityCoeff)
    |>.map (fun eq => eq.linearCombo.maxNatAbs)
    |>.foldr (fun x r? => match r? with | none => x | some r => Nat.min x r) none
    |>.getD 0

-- theorem shrinkEqualityCoeffs_maxEqualityCoeff_lt (p : Problem) (eq : Equality) (i : Nat)
--     (w : (p.shrinkEqualityCoeffs eq i).minEqualityCoeff = p.minEqualityCoeff) :
--     (p.shrinkEqualityCoeffs eq i).maxEqualityCoeff < p.maxEqualityCoeff :=
--   -- Lots of work hiding here! Required for termination proof without fuel.
--   sorry

-- theorem shrinkEqualityCoeffsAndTidy_maxEqualityCoeff_lt (p : Problem) (eq : Equality) (i : Nat)
--     (w : (p.shrinkEqualityCoeffsAndTidy eq i).minEqualityCoeff = p.minEqualityCoeff) :
--     (p.shrinkEqualityCoeffsAndTidy eq i).maxEqualityCoeff < p.maxEqualityCoeff :=
--   -- Some work hiding here!
--   sorry

attribute [irreducible] tidy tidy_equiv shrinkEqualityCoeffsAndTidy shrinkEqualityCoeffsAndTidy_equiv

theorem _root_.Prod.Lex.right'' [LT α] {a₁ a₂ : α} {b₁ b₂ : β} (ha : a₁ = a₂) (hb : s b₁ b₂) :
    Prod.Lex (· < ·) s (a₁, b₁) (a₂, b₂) :=
  ha ▸ Prod.Lex.right a₁ hb

-- The linter incorrectly complains about our decreasing witnesses.
set_option linter.unusedVariables false in
def eliminateEqualities : Nat → Problem → Problem
| 0, _ => trivial
| (fuel + 1), p =>
  if lengthEqZero : p.equalities.length = 0 then
    -- We are done!
    p
  else if minEqZero : p.minEqualityCoeff = 0 then
    -- This can only happen if `p` was not normalized: do that now.
    p.tidy
  else if minEqOne : p.minEqualityCoeff = 1 then
    let p' := p.eliminateEasyEquality minEqOne
    have lengthLt : p'.equalities.length < p.equalities.length :=
      p.eliminateEasyEquality_equalities_length minEqOne
    p'.eliminateEqualities (fuel + 1)
  else
    let eq := p.minCoeffEquality minEqZero
    let i := eq.minCoeffIdx
    let p' := p.shrinkEqualityCoeffsAndTidy eq i
    if lengthLt : p'.equalities.length < p.equalities.length then
      -- We accidentally reduced the number of equalities because some became trivial
      p'.eliminateEqualities (fuel + 1)
    else
      have lengthEq : p'.equalities.length = p.equalities.length :=
        (or_iff_not_imp_right.mp (Nat.eq_or_lt_of_le (p.shrinkEqualityCoeffsAndTidy_length_le eq i))) lengthLt
      if minLt : p'.minEqualityCoeff < p.minEqualityCoeff then
        p'.eliminateEqualities (fuel + 1)
      else
        -- have minEq : p'.minEqualityCoeff = p.minEqualityCoeff :=
        --   (or_iff_not_imp_right.mp (Nat.eq_or_lt_of_le (p.shrinkEqualityCoeffsAndTidy_minEqualityCoeff_le eq i))) minLt
        -- have maxLt : p'.maxEqualityCoeff < p.maxEqualityCoeff :=
        --   -- p.shrinkEqualityCoeffsAndTidy_maxEqualityCoeff_lt eq i minEq
        have : fuel < fuel + 1 := Nat.lt.base fuel
        p'.eliminateEqualities fuel
termination_by eliminateEqualities fuel p => (fuel, p.equalities.length, p.minEqualityCoeff, p.maxEqualityCoeff)
decreasing_by
  -- TODO: solve_by_elim needs to move to Std asap
  solve_by_elim (config := { maxDepth := 10 }) [Prod.Lex.left, Prod.Lex.right'']

-- The linter incorrectly complains about our decreasing witnesses.
set_option linter.unusedVariables false in
theorem eliminateEqualities_equalities_length {fuel : Nat} {p : Problem} :
    (p.eliminateEqualities fuel).equalities.length = 0 := by
  match fuel with
  | 0 => rw [eliminateEqualities]; rfl
  | (fuel + 1) =>
    rw [eliminateEqualities]
    -- Use `split` (or `split_ifs`) for splitting the outer `if` statements
    -- results in a giant blow up in elaboration time.
    -- It makes some very expensive calls to the simplifier!
    by_cases lengthEqZero : p.equalities.length = 0
    · rw [dif_pos lengthEqZero]
      assumption
    · rw [dif_neg lengthEqZero]
      by_cases minEqZero : p.minEqualityCoeff = 0
      · rw [dif_pos minEqZero]
        exact tidy_equalities_of_minEqualityCoeff_eq_zero minEqZero
      · rw [dif_neg minEqZero]
        by_cases minEqOne : p.minEqualityCoeff = 1
        · rw [dif_pos minEqOne]
          let p' := p.eliminateEasyEquality minEqOne
          have lengthLt : p'.equalities.length < p.equalities.length :=
            p.eliminateEasyEquality_equalities_length minEqOne
          apply eliminateEqualities_equalities_length
        · rw [dif_neg minEqOne]
          dsimp
          let eq := p.minCoeffEquality minEqZero
          let i := eq.minCoeffIdx
          let p' := p.shrinkEqualityCoeffsAndTidy eq i
          split <;> rename_i lengthLt
          · apply eliminateEqualities_equalities_length
          · have lengthEq : p'.equalities.length = p.equalities.length :=
              (or_iff_not_imp_right.mp (Nat.eq_or_lt_of_le (p.shrinkEqualityCoeffsAndTidy_length_le eq i))) lengthLt
            split <;> rename_i minLt
            · apply eliminateEqualities_equalities_length
            · -- have minEq : p'.minEqualityCoeff = p.minEqualityCoeff :=
              --  (or_iff_not_imp_right.mp (Nat.eq_or_lt_of_le (p.shrinkEqualityCoeffsAndTidy_minEqualityCoeff_le eq i))) minLt
              -- have maxLt : p'.maxEqualityCoeff < p.maxEqualityCoeff :=
              --   p.shrinkEqualityCoeffsAndTidy_maxEqualityCoeff_lt eq i minEq
              have : fuel < fuel + 1 := Nat.lt.base fuel
              apply eliminateEqualities_equalities_length
termination_by eliminateEqualities_equalities_length fuel p => (fuel, p.equalities.length, p.minEqualityCoeff, p.maxEqualityCoeff)
decreasing_by
  solve_by_elim (config := { maxDepth := 10 }) [Prod.Lex.left, Prod.Lex.right'']

-- For now this is just a map, not an equivalence.
-- When we prove termination, we can get rid of the fuel parameter and turn it into a equiv again!
-- The linter incorrectly complains about our decreasing witnesses.
set_option linter.unusedVariables false in
def eliminateEqualities_equiv (fuel : Nat) (p : Problem) : p → p.eliminateEqualities fuel := by
  match fuel with
  | 0 =>
    rw [eliminateEqualities]
    exact fun _ => trivial_solution
  | (fuel + 1) =>
    rw [eliminateEqualities]
    by_cases lengthEqZero : p.equalities.length = 0
    · rw [dif_pos lengthEqZero]
      exact (equiv.refl p).mpr
    · rw [dif_neg lengthEqZero]
      by_cases minEqZero : p.minEqualityCoeff = 0
      · rw [dif_pos minEqZero]
        exact (p.tidy_equiv).mpr
      · rw [dif_neg minEqZero]
        by_cases minEqOne : p.minEqualityCoeff = 1
        · rw [dif_pos minEqOne]
          let p' := p.eliminateEasyEquality minEqOne
          have lengthLt : p'.equalities.length < p.equalities.length :=
            p.eliminateEasyEquality_equalities_length minEqOne
          exact (p'.eliminateEqualities_equiv (fuel + 1)) ∘ (p.eliminateEasyEquality_equiv minEqOne).mpr
        · rw [dif_neg minEqOne]
          dsimp
          let eq := p.minCoeffEquality minEqZero
          let i := eq.minCoeffIdx
          have big : 1 < (eq.linearCombo.coeff i).natAbs := by
            rw [eq.minCoeffIdx_spec, minCoeffEquality_minCoeff]
            match p.minEqualityCoeff, minEqZero, minEqOne with
            | (i+2), _, _ => exact Nat.lt_of_sub_eq_succ rfl
          let p' := p.shrinkEqualityCoeffsAndTidy eq i
          have m := p.minCoeffEquality_mem minEqZero
          have h : (p.minCoeffEquality minEqZero).minCoeff ≠ 0 := by
            rwa [p.minCoeffEquality_minCoeff minEqZero]
          let e' := p.shrinkEqualityCoeffsAndTidy_equiv eq m i big (p.minCoeffIdx_lt_numVars m h)
          -- Can't use `split` here, it only works in `Prop`. :-(
          -- split_ifs with lengthLt minLt
          by_cases lengthLt : (p.shrinkEqualityCoeffsAndTidy (p.minCoeffEquality minEqZero)
            ((p.minCoeffEquality minEqZero).minCoeffIdx)).equalities.length <
              p.equalities.length
          · rw [if_pos lengthLt]
            exact p'.eliminateEqualities_equiv (fuel + 1) ∘ e'.mpr
          · rw [if_neg lengthLt]
            by_cases minLt : (p.shrinkEqualityCoeffsAndTidy (p.minCoeffEquality minEqZero)
              ((p.minCoeffEquality minEqZero).minCoeffIdx)).minEqualityCoeff <
                p.minEqualityCoeff
            · rw [if_pos minLt]
              have lengthEq : p'.equalities.length = p.equalities.length :=
                (or_iff_not_imp_right.mp (Nat.eq_or_lt_of_le (p.shrinkEqualityCoeffsAndTidy_length_le eq i))) lengthLt
              exact p'.eliminateEqualities_equiv (fuel + 1) ∘ e'.mpr
            · rw [if_neg minLt]
              have lengthEq : p'.equalities.length = p.equalities.length :=
                (or_iff_not_imp_right.mp (Nat.eq_or_lt_of_le (p.shrinkEqualityCoeffsAndTidy_length_le eq i))) lengthLt
              -- have minEq : p'.minEqualityCoeff = p.minEqualityCoeff :=
              --   (or_iff_not_imp_right.mp (Nat.eq_or_lt_of_le (p.shrinkEqualityCoeffsAndTidy_minEqualityCoeff_le eq i))) minLt
              -- have maxLt : p'.maxEqualityCoeff < p.maxEqualityCoeff :=
              --   p.shrinkEqualityCoeffsAndTidy_maxEqualityCoeff_lt eq i minEq
              have : fuel < fuel + 1 := Nat.lt.base fuel
              exact p'.eliminateEqualities_equiv fuel ∘ e'.mpr
termination_by eliminateEqualities_equiv fuel p => (fuel, p.equalities.length, p.minEqualityCoeff, p.maxEqualityCoeff)
decreasing_by
  solve_by_elim (config := { maxDepth := 10 }) [Prod.Lex.left, Prod.Lex.right'']

/--
Separate the inequalities in a problems into the lower bounds for a variable,
the upper bounds for that variable, and the inequalities not involving that variable.
-/
def bounds (p : Problem) (i : Nat) : List LinearCombo × List LinearCombo × List LinearCombo :=
  let (relevant, irrelevant) := p.inequalities.partition fun ineq => ineq.coeff i ≠ 0
  let (lower, upper) := relevant.partition fun ineq => ineq.coeff i > 0
  (lower, upper, irrelevant)

theorem mem_of_mem_bounds_1 {p : Problem} {i : Nat} (h : lc ∈ (p.bounds i).1) :
    lc ∈ p.inequalities := by
  simp [bounds] at h
  exact List.mem_of_mem_filter' h
theorem mem_of_mem_bounds_2 {p : Problem} {i : Nat} (h : lc ∈ (p.bounds i).2.1) :
    lc ∈ p.inequalities := by
  simp [bounds] at h
  exact List.mem_of_mem_filter' h
theorem mem_of_mem_bounds_3 {p : Problem} {i : Nat} (h : lc ∈ (p.bounds i).2.2) :
    lc ∈ p.inequalities := by
  simp [bounds] at h
  exact List.mem_of_mem_filter' h

theorem coeff_of_mem_bounds_1 {p : Problem} {i : Nat} (h : lc ∈ (p.bounds i).1) :
    lc.coeff i > 0 := by simp_all [bounds, List.mem_filter]
theorem coeff_of_mem_bounds_2 {p : Problem} {i : Nat} (h : lc ∈ (p.bounds i).2.1) :
    lc.coeff i < 0 := by
  have := Int.lt_trichotomy (lc.coeff i) 0
  simp_all [bounds, List.mem_filter]
theorem coeff_of_mem_bounds_3 {p : Problem} {i : Nat} (h : lc ∈ (p.bounds i).2.2) :
    lc.coeff i = 0 := by simp_all [bounds, List.mem_filter]

def combineBounds (lower upper : LinearCombo) (i : Nat) : LinearCombo :=
  lower.coeff i * upper.setCoeff i 0 - upper.coeff i * lower.setCoeff i 0

theorem combineBounds_eval (lower upper : LinearCombo) (i : Nat)
    (wl : lower.coeff i > 0) (wu : upper.coeff i < 0) (v : IntList)
    (hl : lower.eval v ≥ 0) (hu : upper.eval v ≥ 0) : (combineBounds lower upper i).eval v ≥ 0 := by
  simp only [combineBounds, LinearCombo.sub_eval, LinearCombo.smul_eval, LinearCombo.setCoeff_eval,
    Int.zero_sub]
  rw [Int.mul_add, Int.mul_add, Int.add_comm (upper.coeff i * _), ← Int.sub_sub]
  rw [Int.add_sub_assoc]
  conv in lower.coeff i * _ - _ =>
    simp only [Int.neg_mul, Int.mul_neg, ← Int.mul_assoc]
    rw [Int.mul_comm (lower.coeff i)]
    rw [Int.sub_self]
  simp only [Int.add_zero]
  rw [Int.sub_eq_add_neg]
  apply Int.add_nonneg
  · exact Int.mul_nonneg (Int.le_of_lt wl) hu
  · rw [← Int.neg_mul]
    exact Int.mul_nonneg (Int.neg_nonneg_of_nonpos (Int.le_of_lt wu)) hl

-- TODO we should be deleting variables as we go!

def realShadow (p : Problem) (i : Nat) : Problem :=
  let (lower, upper, irrelevant) := p.bounds i
  if lower.length = 0 ∨ upper.length = 0 then
    { p with inequalities := irrelevant }
  else
    let combined := lower.bind fun l => upper.map fun u => combineBounds l u i
    { p with inequalities := irrelevant ++ combined }

def realShadow_map (p : Problem) (i : Nat) : p → p.realShadow i :=
  fun ⟨v, h⟩ => ⟨v, by
    dsimp [realShadow]
    split <;> rename_i w
    · exact { h with
        inequalities := @fun lc m => h.inequalities (mem_of_mem_bounds_3 m) }
    · exact { h with
        inequalities := @fun lc m => by
          simp [hasInequality] at m
          rcases m with m|m
          · exact h.inequalities (mem_of_mem_bounds_3 m)
          · simp only [List.mem_bind, List.mem_map] at m
            obtain ⟨l, ml, u, mu, rfl⟩ := m
            apply combineBounds_eval
            · exact coeff_of_mem_bounds_1 ml
            · exact coeff_of_mem_bounds_2 mu
            · exact h.inequalities (mem_of_mem_bounds_1 ml)
            · exact h.inequalities (mem_of_mem_bounds_2 mu) }⟩

-- TODO these next four functions should probably be cached, or computed all at once, etc.

def minimumInequalityCoeff (p : Problem) (i : Nat) : Option Int :=
  (p.inequalities.map fun ineq => ineq.coeff i).minimum?

def maximumInequalityCoeff (p : Problem) (i : Nat) : Option Int :=
  (p.inequalities.map fun ineq => ineq.coeff i).maximum?

def countLowerBounds (p : Problem) (i : Nat) : Nat := (p.bounds i).1.length
def countUpperBounds (p : Problem) (i : Nat) : Nat := (p.bounds i).2.1.length

def countFourierMotzkinInequalities (p : Problem) (i : Nat) : Nat :=
  let b := p.bounds i
  b.1.length * b.2.1.length

@[irreducible]
def eliminateInequalityIdx (p : Problem) : Option Nat :=
  let vars := Array.range p.numVars
  let exactEliminations := vars.filter fun i => p.minimumInequalityCoeff i = some (-1) ∨ p.maximumInequalityCoeff i = some 1
  let candidates := if exactEliminations.isEmpty then
    vars.filter fun i => (p.minimumInequalityCoeff i).isSome
  else
    exactEliminations
  -- FIXME we need a sorting algorithm!
  let sorted := (candidates.map fun i => (p.countFourierMotzkinInequalities i, i)) |>.insertionSort (·.1 < ·.1)
  sorted[0]?.map (·.2)

-- TODO: we need to fix tidy to turn tight pairs of inequalities into equalities, and then this algorithm needs to keep eliminating equalities as they arise.
def eliminateInequalities (fuel : Nat) (p : Problem) : Problem :=
  match fuel with
  | 0 => trivial
  | fuel + 1 =>
  match p.eliminateInequalityIdx with
  | none => p
  | some i => (p.realShadow i).tidy.eliminateInequalities fuel

def eliminateInequalities_map (fuel : Nat) (p : Problem) : p → p.eliminateInequalities fuel := by
  match fuel with
  | 0 =>
    rw [eliminateInequalities]
    exact fun _ => trivial_solution
  | (fuel + 1) =>
    rw [eliminateInequalities]
    match p.eliminateInequalityIdx with
    | none => exact (equiv.refl p).mpr
    | some i => exact eliminateInequalities_map _ _ ∘ (tidy_equiv _).mpr ∘ p.realShadow_map i

end Problem

end Omega.Impl
