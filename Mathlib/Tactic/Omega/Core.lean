/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.Omega.OmegaM
import Mathlib.Tactic.Omega.Constraint

set_option autoImplicit true
set_option relaxedAutoImplicit true

open Lean (HashSet)

namespace Std.Tactic.Omega

open Lean (Expr)
open Lean.Meta

/--
A delayed proof that a constraint is satisfied at the atoms.
-/
abbrev Proof : Type := OmegaM Expr

def normalize? : Constraint × Coeffs → Option (Constraint × Coeffs)
  | ⟨s, x⟩ =>
    let gcd := Coeffs.gcd x -- TODO should we be caching this?
    if gcd = 0 then
      if s.sat 0 then
        some (.trivial, x)
      else
        some (.impossible, x)
    else if gcd = 1 then
      none
    else
      some (s.div gcd, Coeffs.sdiv x gcd)

def normalize (p : Constraint × Coeffs) : Constraint × Coeffs :=
  normalize? p |>.getD p

abbrev normalizeConstraint (s : Constraint) (x : Coeffs) : Constraint := (normalize (s, x)).1
abbrev normalizeCoeffs (s : Constraint) (x : Coeffs) : Coeffs := (normalize (s, x)).2

theorem normalize?_eq_some (w : normalize? (s, x) = some (s', x')) :
    normalizeConstraint s x = s' ∧ normalizeCoeffs s x = x' := by
  simp_all [normalizeConstraint, normalizeCoeffs, normalize]

theorem normalize_sat {s x v} (w : s.sat' x v) :
    (normalizeConstraint s x).sat' (normalizeCoeffs s x) v := by
  dsimp [normalizeConstraint, normalizeCoeffs, normalize, normalize?]
  split <;> rename_i h
  · split
    · simp
    · dsimp [Constraint.sat'] at w
      simp_all
  · split
    · exact w
    · exact Constraint.div_sat' h w

def positivize? : Constraint × Coeffs → Option (Constraint × Coeffs)
  | ⟨s, x⟩ =>
    if 0 ≤ x.leading then
      none
    else
      (s.neg, Coeffs.smul x (-1) )

def positivize (p : Constraint × Coeffs) : Constraint × Coeffs :=
  positivize? p |>.getD p

abbrev positivizeConstraint (s : Constraint) (x : Coeffs) : Constraint := (positivize (s, x)).1
abbrev positivizeCoeffs (s : Constraint) (x : Coeffs) : Coeffs := (positivize (s, x)).2

theorem positivize?_eq_some (w : positivize? (s, x) = some (s', x')) :
    positivizeConstraint s x = s' ∧ positivizeCoeffs s x = x' := by
  simp_all [positivizeConstraint, positivizeCoeffs, positivize]

theorem positivize_sat {s x v} (w : s.sat' x v) :
    (positivizeConstraint s x).sat' (positivizeCoeffs s x) v := by
  dsimp [positivizeConstraint, positivizeCoeffs, positivize, positivize?]
  split
  · exact w
  · simp [Constraint.sat']
    erw [Coeffs.dot_smul_left, ← Int.neg_eq_neg_one_mul]
    exact Constraint.neg_sat w

-- theorem trim_sat {s : Constraint} {x v} (w : s.sat' x v) : s.sat' (IntList.trim x) v := by
--   dsimp [Constraint.sat']
--   rw [Coeffs.dot]
--   rw [IntList.dot_trim_left]
--   exact w

def tidy? : Constraint × Coeffs → Option (Constraint × Coeffs)
  | ⟨s, x⟩ =>
    -- match IntList.trim? x with
    -- | none =>
    match positivize? (s, x) with
      | none => match normalize? (s, x) with
        | none => none
        | some (s', x') => some (s', x')
      | some (s', x') => normalize (s', x')
    -- | some x' => normalize (positivize (s, x'))

def tidy (p : Constraint × Coeffs) : Constraint × Coeffs :=
  tidy? p |>.getD p

abbrev tidyConstraint (s : Constraint) (x : Coeffs) : Constraint := (tidy (s, x)).1
abbrev tidyCoeffs (s : Constraint) (x : Coeffs) : Coeffs := (tidy (s, x)).2

theorem tidy_sat {s x v} (w : s.sat' x v) : (tidyConstraint s x).sat' (tidyCoeffs s x) v := by
  dsimp [tidyConstraint, tidyCoeffs, tidy, tidy?]
  -- split <;> rename_i ht
  · split <;> rename_i hp
    · split <;> rename_i hn
      · simp_all
      · rcases normalize?_eq_some hn with ⟨rfl, rfl⟩
        exact normalize_sat w
    · rcases positivize?_eq_some hp with ⟨rfl, rfl⟩
      exact normalize_sat (positivize_sat w)
  -- · rcases IntList.trim?_eq_some ht with rfl
  --   exact normalize_sat (positivize_sat (trim_sat w))

theorem combo_sat' (s t : Constraint)
    (a : Int) (x : Coeffs) (b : Int) (y : Coeffs) (v : Coeffs)
    (wx : s.sat' x v) (wy : t.sat' y v) :
    (Constraint.combo a s b t).sat' (Coeffs.combo a x b y) v := by
  rw [Constraint.sat', Coeffs.combo_eq_smul_add_smul, Coeffs.dot_distrib_left,
    Coeffs.dot_smul_left, Coeffs.dot_smul_left]
  exact Constraint.combo_sat a wx b wy

abbrev bmod_div_term (m : Nat) (a b : Coeffs) : Int := Coeffs.bmod_dot_sub_dot_bmod m a b / m

def bmod_coeffs (m : Nat) (i : Nat) (x : Coeffs) : Coeffs :=
  Coeffs.set (Coeffs.bmod x m) i m

theorem bmod_sat (m : Nat) (r : Int) (i : Nat) (x v : Coeffs)
    (h : x.length ≤ i)  -- during proof reconstruction this will be by `decide`
    (p : Coeffs.get v i = bmod_div_term m x v) -- and this will be by `rfl`
    (w : (Constraint.exact r).sat' x v) :
    (Constraint.exact (Int.bmod r m)).sat' (bmod_coeffs m i x) v := by
  simp at w
  simp only [p, bmod_coeffs, Constraint.exact_sat, Coeffs.dot_set_left, decide_eq_true_eq]
  replace h := Nat.le_trans (Coeffs.bmod_length x m) h
  rw [Coeffs.get_of_length_le h, Int.sub_zero,
    Int.mul_ediv_cancel' (Coeffs.dvd_bmod_dot_sub_dot_bmod _ _ _), w,
    ← Int.add_sub_assoc, Int.add_comm, Int.add_sub_assoc, Int.sub_self, Int.add_zero]

inductive Justification : Constraint → Coeffs → Type
-- `Problem.assumptions[i]` generates a proof that `s.sat (Coeffs.dot coeffs atoms)`
| assumption (coeffs : Coeffs) (s : Constraint) (i : Nat) : Justification s coeffs
| tidy (j : Justification s c) : Justification (tidyConstraint s c) (tidyCoeffs s c)
| combine {s t c} (j : Justification s c) (k : Justification t c) : Justification (s.combine t) c
| combo {s t x y} (a : Int) (j : Justification s x) (b : Int) (k : Justification t y) :
    Justification (Constraint.combo a s b t) (Coeffs.combo a x b y)
  -- This only makes sense when `s = .exact r`, but there is no point in enforcing that here:
| bmod (m : Nat) (r : Int) (i : Nat) {x} (j : Justification (.exact r) x) :
    Justification (.exact (Int.bmod r m)) (bmod_coeffs m i x)

nonrec def Justification.tidy? (j : Justification s c) : Option (Σ s' c', Justification s' c') :=
  match tidy? (s, c) with
  | some _ => some ⟨_, _, tidy j⟩
  | none => none



namespace Justification

-- TODO deduplicate??

def toString : Justification s x → String
| assumption _ _ i => s!"{x} ∈ {s}: assumption {i}"
| @tidy s' x' j => if s == s' && x == x' then j.toString else s!"{x} ∈ {s}: tidying up:\n" ++ j.toString.bullet
| combine j k => s!"{x} ∈ {s}: combination of:\n" ++ j.toString.bullet ++ "\n" ++ k.toString.bullet
| combo a j b k => s!"{x} ∈ {s}: {a} * x + {b} * y combo of:\n" ++ j.toString.bullet ++ "\n" ++ k.toString.bullet
| bmod m _ i j => s!"{x} ∈ {s}: bmod with m={m} and i={i} of:\n" ++ j.toString.bullet

instance : ToString (Justification s x) where toString := toString

open Lean

def normalizeProof (s : Constraint) (x : Coeffs) (v : Expr) (prf : Expr) : Expr :=
  mkApp4 (.const ``normalize_sat []) (toExpr s) (toExpr x) v prf

def positivizeProof (s : Constraint) (x : Coeffs) (v : Expr) (prf : Expr) : Expr :=
  mkApp4 (.const ``positivize_sat []) (toExpr s) (toExpr x) v prf

def tidyProof (s : Constraint) (x : Coeffs) (v : Expr) (prf : Expr) : Expr :=
  mkApp4 (.const ``tidy_sat []) (toExpr s) (toExpr x) v prf

def combineProof (s t : Constraint) (x : Coeffs) (v : Expr) (ps pt : Expr) : Expr :=
  mkApp6 (.const ``Constraint.combine_sat' []) (toExpr s) (toExpr t) (toExpr x) v ps pt

def comboProof (s t : Constraint) (a : Int) (x : Coeffs) (b : Int) (y : Coeffs)
    (v : Expr) (px py : Expr) : Expr :=
  mkApp9 (.const ``combo_sat' []) (toExpr s) (toExpr t) (toExpr a) (toExpr x) (toExpr b) (toExpr y)
    v px py

/-- Construct the term with type hint `(Eq.refl a : a = b)`-/
def mkEqReflWithExpectedType (a b : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)

-- def takeListLit : Nat → Level → Expr → Expr → Expr
--   | 0, u, ty, _ => mkApp (.const ``List.nil [u]) ty
--   | (k + 1), u, ty, e =>
--     match e.getAppFnArgs with
--     | (``List.cons, #[_, h, t]) => mkApp3 (.const ``List.cons [u]) ty h (takeListLit k u ty t)
--     | _ => mkApp (.const ``List.nil [u]) ty

def bmodProof (m : Nat) (r : Int) (i : Nat) (x : Coeffs) (v : Expr) (w : Expr) : MetaM Expr := do
  let m := toExpr m
  let r := toExpr r
  let i := toExpr i
  let x := toExpr x
  let h ← mkDecideProof (mkApp4 (.const ``LE.le [.zero]) (.const ``Nat []) (.const ``instLENat [])
    (.app (.const ``Coeffs.length []) x) i)
  let lhs := mkApp2 (.const ``Coeffs.get []) v i
  let rhs := mkApp3 (.const ``bmod_div_term []) m x v
  let p ← mkEqReflWithExpectedType lhs rhs
  return mkApp8 (.const ``bmod_sat []) m r i x v h p w

-- TODO deduplicate: don't prove the same thing twice in different branches

/-- Constructs a proof that `s.sat' c v = true` -/
def proof (v : Expr) (assumptions : Array Proof) : Justification s c → Proof
  | assumption s c i => assumptions[i]!
  | @tidy s c j => return tidyProof s c v (← proof v assumptions j)
  | @combine s t c j k =>
    return combineProof s t c v (← proof v assumptions j) (← proof v assumptions k)
  | @combo s t x y a j b k =>
    return comboProof s t a x b y v (← proof v assumptions j) (← proof v assumptions k)
  | @bmod m r i x j => do bmodProof m r i x v (← proof v assumptions j)

end Justification

-- inductive Result (assumptions : List (Constraint × Coeffs)) (atoms : Coeffs) (proof : ∀ a ∈ assumptions, a.1.sat' a.2 atoms) :
--     Constraint × Coeffs → Type
--   | assumption (i : Fin assumptions.length) : Result assumptions atoms proof (assumptions.get i)
--   | tidy (p : Constraint × Coeffs) : Result assumptions atoms proof p → Result assumptions atoms proof (tidy p)
--   | combine (s t : Constraint) (x : Coeffs) : Result assumptions atoms proof (s, x) → Result assumptions atoms proof (t, x) →
--       Result assumptions atoms proof (s.combine t, x)
--   | combo (p q : Constraint × Coeffs) (a b : Int) : Result assumptions atoms proof p → Result assumptions atoms proof q →
--       Result assumptions atoms proof (.combo a p.1 b q.1, Coeffs.combo a p.2 b q.2)
--   | bmod (m : Nat) (r : Int) (i : Nat) (x : Coeffs) : x.length ≤ i → atoms.get i = bmod_div_term m x atoms → Result assumptions atoms proof (.exact r, x) →
--       Result assumptions atoms proof (.exact (Int.bmod r m), bmod_coeffs m i x)

-- theorem Result.sat {assumptions atoms proof} : Result assumptions atoms proof p → p.1.sat' p.2 atoms
--   | .assumption i => proof _ (List.get_mem _ _ _)
--   | .tidy p f => tidy_sat (Result.sat f)
--   | .combine s t x fs ft => Constraint.combine_sat' (Result.sat fs) (Result.sat ft)
--   | .combo p q a b fp fq => combo_sat' _ _ _ _ _ _ _ (Result.sat fp) (Result.sat fq)
--   | .bmod m r i x h w f => bmod_sat _ _ _ _ _ h w (Result.sat f)

structure Fact where
  coeffs : Coeffs
  constraint : Constraint
  justification : Justification constraint coeffs

namespace Fact

instance : ToString Fact where
  toString f := toString f.justification

def tidy (f : Fact) : Fact :=
  match f.justification.tidy? with
  | some ⟨_, _, justification⟩ => { justification }
  | none => f

def combo (a : Int) (f : Fact) (b : Int) (g : Fact) : Fact :=
  { justification := .combo a f.justification b g.justification }

end Fact

structure Problem where
  assumptions : Array Proof := ∅

  numVars : Nat := 0

  constraints : HashMap Coeffs Fact := ∅

  possible : Bool := true

  proveFalse? : Option Proof := none
  proveFalse?_spec : possible || proveFalse?.isSome := by rfl

  explanation? : Option String := none

  equalities : HashSet Coeffs := ∅

  -- Stores equations that have already been used to eliminate variables,
  -- along with the variable which was removed, and its coefficient (either `1` or `-1`).
  -- The earlier elements are more recent,
  -- so if these are being reapplied it is essential to use `List.foldr`.
  eliminations : List (Fact × Nat × Int) := []


namespace Problem

def isEmpty (p : Problem) : Bool := p.constraints.isEmpty

instance : ToString Problem where
  toString p :=
    if p.possible then
      if p.isEmpty then
        "trivial"
      else
        "\n".intercalate <|
          (p.constraints.toList.map fun ⟨coeffs, ⟨_, cst, _⟩⟩ => s!"{coeffs} ∈ {cst}")
    else
      "impossible"


open Lean in
/--
Takes a proof that `s.sat' x v` for some `s` such that `s.isImpossible`,
and constructs a proof of `False`.
-/
def proveFalse {s x} (j : Justification s x) (assumptions : Array Proof) : Proof := do
  let v := .app (.const ``Coeffs.ofList []) (← atomsList)
  let prf ← j.proof v assumptions
  let x := toExpr x
  let s := toExpr s
  let impossible ← mkDecideProof (← mkEq (mkApp (.const ``Constraint.isImpossible []) s) (.const ``true []))
  return mkApp5 (.const ``Constraint.not_sat'_of_isImpossible []) s impossible x v prf

/--
Insert a constraint into the problem,
without checking if there is already a constraint for these coefficients.
-/
def insertConstraint (p : Problem) : Fact → Problem
  | f@⟨x, s, j⟩ =>
    if s.isImpossible then
      { p with
        possible := false
        proveFalse? := some (proveFalse j p.assumptions)
        explanation? := some j.toString
        proveFalse?_spec := rfl }
    else
      { p with
        numVars := max p.numVars x.length
        constraints := p.constraints.insert x f
        proveFalse?_spec := p.proveFalse?_spec
        equalities :=
        if f.constraint.isExact then
          p.equalities.insert x
        else
          p.equalities }

def addConstraint (p : Problem) : Fact → Problem
  | f@⟨x, s, j⟩ =>
    if p.possible then
      match p.constraints.find? x with
      | none =>
        match s with
        | .trivial => p
        | _ => p.insertConstraint f
      | some ⟨x', t, k⟩ =>
        if h : x = x' then
          p.insertConstraint ⟨x, s.combine t, j.combine (h ▸ k)⟩
        else
          p -- unreachable
    else
      p

def selectEquality (p : Problem) : Option Coeffs :=
  p.equalities.fold (init := none) fun
  | none, c => c
  | some r, c => if 2 ≤ r.minNatAbs && (c.minNatAbs < r.minNatAbs || c.minNatAbs = r.minNatAbs && c.maxNatAbs < r.maxNatAbs) then c else r

def replayEliminations (p : Problem) (f : Fact) : Fact :=
  p.eliminations.foldr (init := f) fun (f, i, s) g =>
    match Coeffs.get g.coeffs i with
    | 0 => g
    | y => Fact.combo (-1 * s * y) f 1 g

def solveEasyEquality (p : Problem) (c : Coeffs) : Problem :=
  let i := c.findIdx? (·.natAbs = 1) |>.getD 0 -- findIdx? is always some
  let sign := c.get i |> Int.sign
  match p.constraints.find? c with
  | some f =>
    -- TODO Lame that we are copying around assumptions here:
    let init :=
    { assumptions := p.assumptions
      eliminations := (f, i, sign) :: p.eliminations }
    p.constraints.fold (init := init) fun p' coeffs g =>
      match Coeffs.get coeffs i with
      | 0 =>
        p'.addConstraint g
      | ci =>
        let k := -1 * sign * ci
        p'.addConstraint (Fact.combo k f 1 g).tidy
  | _ => p -- unreachable

open Lean in
/--
We deal with a hard equality by introducing a new easy equality.

After solving the easy equality,
the minimum lexicographic value of `(c.minNatAbs, c.maxNatAbs)` will have been reduced.
-/
def dealWithHardEquality (p : Problem) (c : Coeffs) : OmegaM Problem :=
  match p.constraints.find? c with
  | some ⟨_, ⟨some r, some r'⟩, j⟩ => do
    let m := c.minNatAbs + 1
    let x := mkApp3 (.const ``bmod_div_term []) (toExpr m) (toExpr c) (← atomsList)
    let (i, facts?) ← lookup x
    if hr : r' = r then
      match facts? with
      | none => throwError "When solving hard equality, new atom had been seen before!"
      | some facts => if ! facts.isEmpty then
        throwError "When solving hard equality, there should not have been interesting facts about the new atom!"
      return p.addConstraint { coeffs := _, constraint := _, justification := (hr ▸ j).bmod m r i }
    else
      throwError "Invalid constraint, expected an equation." -- unreachable
  | _ =>
    return p -- unreachable

def solveEquality (p : Problem) (c : Coeffs) : OmegaM Problem :=
  if c.minNatAbs = 1 then
    return p.solveEasyEquality c
  else
    p.dealWithHardEquality c

partial def solveEqualities (p : Problem) : OmegaM Problem :=
  if p.possible then
    match p.selectEquality with
    | some c => do (← p.solveEquality c).solveEqualities
    | none => return p
  else return p

theorem addInequality_sat (w : c + Coeffs.dot x y ≥ 0) :
    ({ lowerBound := some (-c), upperBound := none } : Constraint).sat' x y := by
  simp [Constraint.sat', Constraint.sat]
  rw [← Int.zero_sub c]
  exact Int.sub_left_le_of_le_add w

open Lean in
def addInequality_proof (c : Int) (x : Coeffs) (p : Proof) : Proof := do
  return mkApp4 (.const ``addInequality_sat []) (toExpr c) (toExpr x) (← atomsList) (← p)

theorem addEquality_sat (w : c + Coeffs.dot x y = 0) :
    ({ lowerBound := some (-c), upperBound := some (-c) } : Constraint).sat' x y := by
  simp [Constraint.sat', Constraint.sat]
  rw [Int.eq_iff_le_and_ge] at w
  rwa [Int.add_le_zero_iff_le_neg', Int.add_nonnneg_iff_neg_le', and_comm] at w

open Lean in
def addEquality_proof (c : Int) (x : Coeffs) (p : Proof) : Proof := do
  return mkApp4 (.const ``addEquality_sat []) (toExpr c) (toExpr x) (← atomsList) (← p)

-- prf? : const + Coeffs.dot coeffs atoms ≥ 0
-- But we need to transform this to `Coeffs.dot coeffs atoms ≥ -const` i.e.

-- This is only ever used to add assumptions: during the elimination we call `addConstraint`.
def addInequality (p : Problem) (const : Int) (coeffs : Coeffs) (prf? : Option Proof) : Problem :=
    let prf := prf?.getD (do mkSorry (← mkFreshExprMVar none) false)
    let i := p.assumptions.size
    let p' := { p with assumptions := p.assumptions.push (addInequality_proof const coeffs prf) }
    let f : Fact :=
    { coeffs
      constraint := { lowerBound := some (-const), upperBound := none }
      justification := .assumption _ _ i }
    let f := p.replayEliminations f
    let f := f.tidy
    p'.addConstraint f

def addEquality (p : Problem) (const : Int) (coeffs : Coeffs) (prf? : Option Proof) : Problem :=
    let prf := prf?.getD (do mkSorry (← mkFreshExprMVar none) false)
    let i := p.assumptions.size
    let p' := { p with assumptions := p.assumptions.push (addEquality_proof const coeffs prf) }
    let f : Fact :=
    { coeffs
      constraint := { lowerBound := some (-const), upperBound := some (-const) }
      justification := .assumption _ _ i }
    let f := p.replayEliminations f
    let f := f.tidy
    p'.addConstraint f

def addInequalities (p : Problem) (ineqs : List (Int × Coeffs × Option Proof)) : Problem :=
  ineqs.foldl (init := p) fun p ⟨const, coeffs, prf?⟩ => p.addInequality const coeffs prf?

def addEqualities (p : Problem) (eqs : List (Int × Coeffs × Option Proof)) : Problem :=
  eqs.foldl (init := p) fun p ⟨const, coeffs, prf?⟩ => p.addEquality const coeffs prf?

structure FourierMotzkinData where
  irrelevant : List Fact := []
  lowerBounds : List (Fact × Int) := []
  upperBounds : List (Fact × Int) := []
  lowerExact : Bool := true
  upperExact : Bool := true
deriving Inhabited

instance : ToString FourierMotzkinData where
  toString d := s!"• irrelevant: {d.irrelevant}\n" ++ s!"• lowerBounds: {d.lowerBounds}\n" ++ s!"• upperBounds: {d.upperBounds}"

def FourierMotzkinData.isEmpty (d : FourierMotzkinData) : Bool :=
  d.lowerBounds.isEmpty && d.upperBounds.isEmpty
def FourierMotzkinData.size (d : FourierMotzkinData) : Nat := d.lowerBounds.length * d.upperBounds.length
def FourierMotzkinData.exact (d : FourierMotzkinData) : Bool := d.lowerExact || d.upperExact

def fourierMotzkinData (p : Problem) : Array FourierMotzkinData := Id.run do
  -- For each variable, prepare the irrelevant constraints, lower and upper bounds,
  -- and whether the elimination would be exact.
  -- TODO Does it make sense to precompute some or all of this?
  let n := p.numVars
  let mut data : Array FourierMotzkinData := Array.mkArray p.numVars {}
  for (_, f@⟨xs, s, _⟩) in p.constraints.toList do -- We could make a forIn instance for HashMap
    for i in [0:n] do
      let x := Coeffs.get xs i
      data := data.modify i fun d =>
        if x = 0 then
          { d with irrelevant := f :: d.irrelevant }
        else Id.run do
          let s' := s.scale x
          let mut d' := d
          if s'.lowerBound.isSome then
            d' := { d' with
              lowerBounds := (f, x) :: d'.lowerBounds
              lowerExact := d'.lowerExact && x.natAbs = 1 }
          if s'.upperBound.isSome then
            d' := { d' with
              upperBounds := (f, x) :: d'.upperBounds
              upperExact := d'.upperExact && x.natAbs = 1 }
          return d'
  return data

-- Now decide which variable to eliminate.
-- We want an exact elimination if possible,
-- and otherwise the one with the fewest new constraints.
def fourierMotzkinSelect (data : Array FourierMotzkinData) : FourierMotzkinData := Id.run do
  let data := data.filter fun d => ¬ d.isEmpty
  let mut bestIdx := 0
  let mut bestSize := data[0]!.size
  let mut bestExact := data[0]!.exact
  if bestSize = 0 then return data[0]!
  for i in [1:data.size] do
    let exact := data[i]!.exact
    let size := data[i]!.size
    if size = 0 || !bestExact && exact || size < bestSize then
      if size = 0 then return data[i]!
      bestIdx := i
      bestExact := exact
      bestSize := size
  return data[bestIdx]!

def fourierMotzkin (p : Problem) : Problem := Id.run do
  -- For each variable, prepare the irrelevant constraints, lower and upper bounds,
  -- and whether the elimination would be exact.
  -- TODO Does it make sense to precompute some or all of this?
  let data := p.fourierMotzkinData
  -- Now perform the elimination.
  let ⟨irrelevant, lower, upper, _, _⟩ := fourierMotzkinSelect data
  let mut r : Problem := { assumptions := p.assumptions, eliminations := p.eliminations }
  for f in irrelevant do
    r := r.insertConstraint f
  for ⟨f, b⟩ in lower do
    for ⟨g, a⟩ in upper do
      r := r.addConstraint (Fact.combo a f (-b) g).tidy
  return r

partial def run (p : Problem) : OmegaM Problem := do
  trace[omega] "Running omega on: {p}"
  if p.possible then
    let p' ← p.solveEqualities
    if p'.possible then
      if p'.isEmpty then
        return p'
      else
        trace[omega] "Running Fourier-Motzkin on:\n{p'}"
        run p'.fourierMotzkin
    else
      return p'
  else
    return p

-- As for `run'`, but assuming the first round of solving equalities has already happened.
def run' (p : Problem) : OmegaM Problem :=
  if p.possible then
    if p.isEmpty then
      return p
    else do
      trace[omega] "Running Fourier-Motzkin on:\n{p}"
      run p.fourierMotzkin
  else
    return p
