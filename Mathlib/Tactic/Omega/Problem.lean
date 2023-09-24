import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.Omega.IntList
import Mathlib.Tactic.LibrarySearch

set_option autoImplicit true
set_option relaxedAutoImplicit true

/-!
# Abstract description of integer linear programming problems.

We define `LinearCombo`, `Problem`, and `DisjunctiveProblem`.
These are abstract descriptions of integer linear programming problems.

In particular, they are intended to be easy to reason about,
but need not be fast to compute with.

Later we will define variants carrying additional data required to run Omega efficiently,
and transfer the proofs from these simpler versions.
-/

namespace Omega

structure LinearCombo where
  const : Int := 0
  coeffs : IntList := []
deriving DecidableEq, Repr

instance : ToString LinearCombo where
  toString lc := s!"{lc.const}{String.join <| lc.coeffs.enum.map fun ⟨i, c⟩ => s!" + {c} * x{i+1}"}"

example : toString (⟨7, [3, 5]⟩ : LinearCombo) = "7 + 3 * x1 + 5 * x2" := rfl

namespace LinearCombo

instance : Inhabited LinearCombo := ⟨{const := 1}⟩

@[ext] theorem ext {a b : LinearCombo} (w₁ : a.const = b.const) (w₂ : a.coeffs = b.coeffs) :
    a = b := by
  cases a; cases b
  subst w₁; subst w₂
  congr

/--
Evaluate a linear combination `⟨r, [c_1, …, c_k]⟩` at values `[v_1, …, v_k]` to obtain
`r + (c_1 * x_1 + (c_2 * x_2 + ... (c_k * x_k + 0))))`.
-/
def eval (lc : LinearCombo) (values : IntList) : Int :=
  lc.const + lc.coeffs.dot values

@[simp] theorem eval_nil : (lc : LinearCombo).eval [] = lc.const := by
  simp [eval]

def coordinate (i : Nat) : LinearCombo where
  const := 0
  coeffs := List.replicate i 0 ++ [1]

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

end LinearCombo

structure Problem where
  possible : Bool := true
  equalities : List LinearCombo := []
  inequalities : List LinearCombo := []
deriving Repr

namespace Problem

instance : ToString Problem where
  toString p :=
    if p.possible then
      if p.equalities = [] ∧ p.inequalities = [] then
        "trivial"
      else
        "\n".intercalate <|
          (p.equalities.map fun e => s!"{e} = 0") ++(p.inequalities.map fun e => s!"{e} ≥ 0")
    else
      "impossible"

structure sat (p : Problem) (values : List Int) : Prop where
  possible : p.possible = true := by trivial
  equalities : lc ∈ p.equalities → lc.eval values = 0
  inequalities : lc ∈ p.inequalities → lc.eval values ≥ 0

@[simps]
def trivial : Problem where

theorem trivial_sat (values : List Int) : trivial.sat values where
  equalities := by simp
  inequalities := by simp

@[simps]
def and (p q : Problem) : Problem where
  possible := p.possible && q.possible
  equalities := p.equalities ++ q.equalities
  inequalities := p.inequalities ++ q.inequalities

theorem and_sat {p q : Problem} (hp : p.sat values) (hq : q.sat values) : (p.and q).sat values where
  possible := by simp [hp.possible, hq.possible]
  equalities := by
    intros lc m
    simp only [and_equalities, List.mem_append] at m
    rcases m with pm | qm <;>
    simp_all [hp.equalities, hq.equalities]
  inequalities := by
    intros lc m
    simp only [and_inequalities, List.mem_append] at m
    rcases m with pm | qm <;>
    simp_all [hp.inequalities, hq.inequalities]

def solutions (p : Problem) : Type :=
  { values // p.sat values }

instance : CoeSort Problem Type where
  coe := solutions

def map_of_sat {p q : Problem} (h : ∀ v, p.sat v → q.sat v) : p → q :=
  fun ⟨v, s⟩ => ⟨v, h v s⟩

def unsat (p : Problem) : Prop := p → False

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

end Problem
