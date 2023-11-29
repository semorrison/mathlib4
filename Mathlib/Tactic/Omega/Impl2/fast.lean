
import Std
import Mathlib.Tactic.Omega.IntList
import Mathlib.Tactic.Omega.OmegaM
import Mathlib.Tactic.Omega.Impl.MinNatAbs
import Mathlib.Tactic.Omega.Impl.bmod
import Qq
import Mathlib.Tactic.DeriveToExpr
import Mathlib.Tactic.LibrarySearch
import Mathlib.Util.Time

set_option autoImplicit true
set_option relaxedAutoImplicit true

open Std (HashMap RBSet RBMap AssocList)

namespace Int

theorem eq_iff_le_and_ge {x y : Int} : x = y ↔ x ≤ y ∧ y ≤ x := by
  constructor
  · simp_all
  · rintro ⟨h₁, h₂⟩
    exact Int.le_antisymm h₁ h₂

end Int

namespace List

@[inline] protected def insert' [BEq α] (a : α) (l : List α) : List α :=
  if l.elem a then l else a :: l

end List

namespace Std.HashMap

def all [BEq α] [Hashable α] (m : HashMap α β) (f : α → β → Bool) : Bool :=
  m.fold (init := true) fun r a b => r && f a b

end Std.HashMap

namespace Std.AssocList

def insert [BEq α] (a : α) (b : β) : AssocList α β → AssocList α β
  | .nil => .cons a b .nil
  | .cons x y t => if x == a then .cons x b t else .cons x y (insert a b t)

end Std.AssocList

namespace Omega.ProofProducing

inductive Bound
  | lowerBound (x : Int)
  | upperBound (x : Int)

namespace Bound

def sat : Bound → Int → Prop
  | .lowerBound x, y => x ≤ y
  | .upperBound x, y => y ≤ x

end Bound

inductive Constraint
  | impossible
  | lowerBound (x : Int)
  | upperBound (x : Int)
  | between (x y : Int)
  | exact (x : Int) -- Note this is redundant with `between x x`
  | trivial
deriving BEq, Repr, Lean.ToExpr

namespace Constraint

instance : ToString Constraint where
  toString := fun
  | impossible => "∅"
  | .lowerBound x => s!"[{x}, ∞)"
  | .upperBound y => s!"(-∞, {y}]"
  | .between x y => s!"[{x}, {y}]"
  | .exact x => s!"\{{x}}"
  | .trivial => s!"(-∞, ∞)"

def sat : Constraint → Int → Prop
  | .impossible, _ => False
  | .lowerBound x, y => x ≤ y
  | .upperBound x, y => y ≤ x
  | .between x y, z => x ≤ z ∧ z ≤ y
  | .exact x, z => x = z
  | .trivial, _ => True

theorem impossible_not_sat (t : Int) : ¬ Constraint.impossible.sat t := id

def translate : Constraint → Int → Constraint
  | .impossible, _ => .impossible
  | .lowerBound x, t => .lowerBound (x + t)
  | .upperBound y, t => .upperBound (y + t)
  | .between x y, t => .between (x + t) (y + t)
  | .exact x, t => .exact (x + t)
  | .trivial, _ => .trivial

theorem translate_sat : {c : Constraint} → {v : Int} → sat c v → sat (c.translate t) (v + t)
  | .lowerBound x, _, h => by simp_all [sat, translate]; exact Int.add_le_add_right h _
  | .upperBound y, _, h => by simp_all [sat, translate]; exact Int.add_le_add_right h _
  | .between x y, _, h => by
    simp_all [sat, translate]; exact ⟨Int.add_le_add_right h.1 _, Int.add_le_add_right h.2 _⟩
  | .exact x, _, h => by simp_all [sat, translate]
  | .trivial, _, _ => by trivial

def neg : Constraint → Constraint
  | .impossible => .impossible
  | .lowerBound x => .upperBound (-x)
  | .upperBound y => .lowerBound (-y)
  | .between x y => .between (-y) (-x)
  | .exact x => .exact (-x)
  | .trivial => .trivial

theorem neg_sat : {c : Constraint} → {v : Int} → sat c v → sat (c.neg) (-v)
  | .lowerBound x, _, h => by simp_all [sat, neg]; exact Int.neg_le_neg h
  | .upperBound y, _, h => by simp_all [sat, neg]; exact Int.neg_le_neg h
  | .between x y, _, h => by simp_all [sat, neg]; exact ⟨Int.neg_le_neg h.2, Int.neg_le_neg h.1⟩
  | .exact x, _, h => by simp_all [sat, neg]
  | .trivial, _, _ => by trivial

def interval (x y : Int) : Constraint :=
  if y < x then
    .impossible
  else if x = y then
    .exact x
  else
    .between x y

def combine_bound : Constraint → Bound → Constraint
  | .impossible, .lowerBound _ => .impossible
  | .impossible, .upperBound _ => .impossible
  | .lowerBound x, .lowerBound w => if x < w then .lowerBound w else .lowerBound x
  | .lowerBound x, .upperBound z => interval x z
  | .upperBound y, .lowerBound w => interval w y
  | .upperBound y, .upperBound z => if y < z then .upperBound y else .upperBound z
  | .between x y, .lowerBound w =>
    if x ≤ w then interval w y else .between x y
  | .between x y, .upperBound z =>
    if z ≤ y then interval x z else .between x y
  | .exact x, .lowerBound w => if w ≤ x then .exact x else .impossible
  | .exact x, .upperBound z => if x ≤ z then .exact x else .impossible
  | .trivial, .lowerBound w => .lowerBound w
  | .trivial, .upperBound z => .upperBound z

theorem combine_bound_sat :
    (c : Constraint) → (i : Bound) → (t : Int) → (c.combine_bound i).sat t = (c.sat t ∧ i.sat t)
  | .impossible, .lowerBound _, t => by simp [sat, combine_bound]
  | .impossible, .upperBound _, t => by simp [sat, combine_bound]
  | .lowerBound x, .lowerBound w, t => by
    simp only [combine_bound]
    split <;> rename_i h <;> simp [sat, Bound.sat]
    · intro; apply Int.le_of_lt; apply Int.lt_of_lt_of_le <;> assumption
    · rw [Int.not_lt] at h; intro; apply Int.le_trans <;> assumption
  | .lowerBound x, .upperBound z, t => by
    simp only [combine_bound, interval]
    split <;> rename_i h <;> simp [sat, Bound.sat]
    · rw [Int.not_le]; intro; apply Int.lt_of_lt_of_le <;> assumption
    · rw [Int.not_lt] at h
      by_cases h : x = z
      · simp [h]; apply Int.eq_iff_le_and_ge
      · simp [h]
  | .upperBound y, .lowerBound w, t => by
    simp only [combine_bound, interval]
    split <;> rename_i h <;> simp [sat, Bound.sat]
    · rw [Int.not_le]; intro; apply Int.lt_of_le_of_lt <;> assumption
    · rw [Int.not_lt] at h
      by_cases h : w = y
      · simp [h]; rw [eq_comm]; apply Int.eq_iff_le_and_ge
      · simp [h, and_comm]
  | .upperBound y, .upperBound z, t => by
    simp only [combine_bound]
    split <;> rename_i h <;> simp [sat, Bound.sat]
    · intro; apply Int.le_of_lt; apply Int.lt_of_le_of_lt <;> assumption
    · rw [Int.not_lt] at h; intro; apply Int.le_trans <;> assumption
  | .between x y, .lowerBound w, t => sorry
  | .between x y, .upperBound z, t => sorry
  | .exact x, .lowerBound w, t => sorry
  | .exact x, .upperBound z, t => sorry
  | .trivial, .lowerBound w, t => sorry
  | .trivial, .upperBound z, t => sorry

def combine : Constraint → Constraint → Constraint
  | _, .impossible => .impossible
  | c, .lowerBound w => combine_bound c (.lowerBound w)
  | c, .upperBound z => combine_bound c (.upperBound z)
  | c, .between x y => combine_bound (combine_bound c (.lowerBound x)) (.upperBound y)
  | c, .exact x => combine_bound (combine_bound c (.lowerBound x)) (.upperBound x)
  | c, .trivial => c

theorem combine_sat : (c : Constraint) → (c' : Constraint) → (t : Int) →
     (c.combine c').sat t = (c.sat t ∧ c'.sat t) := sorry

def div : Constraint → Nat → Constraint
  | .impossible, _ => .impossible
  | .lowerBound x, k => .lowerBound (- ((- x) / k))
  | .upperBound y, k => .upperBound (y / k)
  | .between x y, k =>
    let x' := - ((- x) / k)
    let y' := y / k
    if x'  = y' then .exact x' else .between x' y'
  | .exact x, k => if (k : Int) ∣ x then .exact (x / k) else .impossible
  | .trivial, _ => .trivial

theorem div_sat (c : Constraint) (k : Nat) (t : Int) (h : (c.div k).sat t) : c.sat (t * k) := sorry

end Constraint

def hashIntList (v : List Int) : UInt64 :=
  v.foldl (init := 37) fun r x => 7 * r + Hashable.hash (73 * (x + 17))

structure Coefficients where
  coeffs : List Int
  -- spec: first nonzero entry is nonnegative, and no trailing zeroes?
  gcd : Nat := IntList.gcd coeffs
  -- gcd_spec

  -- TODO cache the hash
  hash : UInt64 := hashIntList coeffs

  minNatAbs : Nat := coeffs.minNatAbs
  -- minNatAbs_spec

  maxNatAbs : Nat := coeffs.map Int.natAbs |>.maximum? |>.getD 0
  -- maxNatAbs_spec
deriving Repr

namespace Coefficients

instance : Ord Coefficients where
  compare x y := compareOfLessAndEq x.coeffs y.coeffs

instance : BEq Coefficients where
  beq x y := x.hash == y.hash && x.coeffs == y.coeffs

-- TODO remove the `DecidableEq` instance, which compares determined fields,
-- in favour of a `LawfulBEq` instance.

instance : ToString Coefficients where
  toString c := " + ".intercalate <| c.coeffs.enum.map fun ⟨i, c⟩ => s!"{c} * x{i+1}"

def eval (c : Coefficients) (v : List Int) : Int := IntList.dot c.coeffs v

instance : Hashable Coefficients := ⟨hash⟩

-- It is essential that the kernel can compute our hash function.
example : hash ({ coeffs := [1, 2] } : Coefficients) = 22983 := rfl

def div_gcd (c : Coefficients) : Coefficients :=
  { coeffs := IntList.sdiv c.coeffs c.gcd |>.trim
    gcd := 1
    minNatAbs := c.minNatAbs / c.gcd }

end Coefficients

-- instance : LawfulBEq Coefficients := sorry

-- structure Indexer (α : Type _) [BEq α] [Hashable α] where
--   keys : HashMap α Nat := ∅
--   values : Array α := #[]
--   spec : ∀ c i, keys.find? c = some i ↔ values.get? i = some c := by intros; simp

-- @[simp] theorem Array.nil_getElem? {i : Nat} : (#[] : Array α)[i]?  = none := rfl

-- @[simp] theorem Std.HashMap.empty_find? {α : Type _} [BEq α] [Hashable α] {a : α} :
--     (∅ : HashMap α β).find? a = none := by
--   sorry

-- theorem Std.HashMap.insert_find? {α : Type _} [BEq α] [LawfulBEq α] [Hashable α]
--     (m : HashMap α β) (a a' : α) (b : β) :
--     (m.insert a b).find? a' = if a' == a then some b else m.find? a' :=
--   sorry

-- theorem Array.push_getElem? {a : Array α} : (a.push x)[i]? = if i = a.size then some x else a[i]? :=
--   sorry
-- @[simp] theorem Array.getElem?_size {a : Array α} : a[a.size]? = none :=
--   sorry

-- def Indexer.empty (α : Type _) [BEq α] [Hashable α] : Indexer α where

-- def Indexer.insert {α : Type _} [BEq α] [LawfulBEq α] [Hashable α] (m : Indexer α) (a : α) : Nat × Indexer α :=
--   match h : m.keys.find? a with
--   | some i => (i, m)
--   | none =>
--     (m.values.size,
--       { keys := m.keys.insert a m.values.size
--         values := m.values.push a
--         spec := fun c i => by
--           simp only [Array.get?_eq_getElem?, HashMap.insert_find?, Array.push_getElem?]
--           have s := m.spec c i
--           split <;> rename_i h <;> simp only [beq_iff_eq] at h <;> split <;> rename_i h'
--           · simp_all
--           · replace h' := Ne.symm h'
--             simp_all
--           · replace h := Ne.symm h
--             simp_all
--           · simp_all })

-- def Indexer.lookup {α : Type _} [BEq α] [Hashable α] (m : Indexer α) (i : Nat) : Option α :=
--   m.values[i]?

open Lean (Expr)
open Lean.Meta
/--
A delayed proof that a constraint is satisfied at the atoms.

The `Proof?` associated to a `(c, s) : Coefficients × Constraint` pair
should be an `Expr` containing loose bvars,
which when instantiated at the atoms gives a proof that `s.sat (IntList.dot c.coeffs atoms)`.
-/
def Proof? : Type := OmegaM Expr

instance : Inhabited Proof? where
  default := do failure

section
open Lean Meta
private def throwAppBuilderException {α} (op : Name) (msg : MessageData) : MetaM α :=
  throwError "AppBuilder for '{op}', {msg}"

private def mkAppMFinal (methodName : Name) (f : Expr) (args : Array Expr) (instMVars : Array MVarId) : MetaM Expr := do
  instMVars.forM fun mvarId => do
    let mvarDecl ← mvarId.getDecl
    let mvarVal  ← synthInstance mvarDecl.type
    mvarId.assign mvarVal
  let result ← instantiateMVars (mkAppN f args)
  -- if (← hasAssignableMVar result) then throwAppBuilderException methodName ("result contains metavariables" ++ indentExpr result)
  return result

private partial def mkAppMArgs (f : Expr) (fType : Expr) (xs : Array Expr) : MetaM Expr :=
  let rec loop (type : Expr) (i : Nat) (j : Nat) (args : Array Expr) (instMVars : Array MVarId) : MetaM Expr := do
    if i >= xs.size then
      mkAppMFinal `mkAppM f args instMVars
    else match type with
      | Expr.forallE n d b bi =>
        let d  := d.instantiateRevRange j args.size args
        match bi with
        | BinderInfo.implicit     =>
          let mvar ← mkFreshExprMVar d MetavarKind.natural n
          loop b i j (args.push mvar) instMVars
        | BinderInfo.strictImplicit     =>
          let mvar ← mkFreshExprMVar d MetavarKind.natural n
          loop b i j (args.push mvar) instMVars
        | BinderInfo.instImplicit =>
          let mvar ← mkFreshExprMVar d MetavarKind.synthetic n
          loop b i j (args.push mvar) (instMVars.push mvar.mvarId!)
        | _ =>
          let x := xs[i]!
          let xType ← inferType x
          if (← isDefEq d xType) then
            loop b (i+1) j (args.push x) instMVars
          else
            throwAppTypeMismatch (mkAppN f args) x
      | type =>
        let type := type.instantiateRevRange j args.size args
        let type ← whnfD type
        if type.isForall then
          loop type i args.size args instMVars
        else
          throwAppBuilderException `mkAppM m!"too many explicit arguments provided to{indentExpr f}\narguments{indentD xs}"
  loop fType 0 0 #[] #[]

private def mkFun (constName : Name) : MetaM (Expr × Expr) := do
  let cinfo ← getConstInfo constName
  let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  let f := mkConst constName us
  let fType ← instantiateTypeLevelParams cinfo us
  return (f, fType)

def mkAppM' (constName : Name) (xs : Array Expr) : MetaM Expr := do
    let (f, fType) ← mkFun constName
    mkAppMArgs f fType xs
end

def mkEqMPR' (eqProof pr : Expr) : MetaM Expr :=
  mkAppM' ``Eq.mpr #[eqProof, pr]

open Qq Lean in
def combine_proofs (p₁ p₂ : Proof?) : Proof? := do
  let p₁ ← p₁ -- s₁.sat (IntList.dot c a)
  let p₂ ← p₂ -- s₂.sat (IntList.dot c a)
  let c₁ ← mkFreshExprMVar (some (.const ``Constraint [])) -- We could fill these in from `inferType p₁`
  let c₂ ← mkFreshExprMVar (some (.const ``Constraint []))
  let t ← mkFreshExprMVar (some (.const ``Int []))
  mkEqMPR' (mkApp3 (.const ``Constraint.combine_sat []) c₁ c₂ t) (← mkAppM' ``And.intro #[p₁, p₂])

open Lean in
def trivial_proof : Proof? := do
  let ty := mkApp2 (.const ``Constraint.sat []) (.const ``Constraint.trivial []) (← mkFreshExprMVar (some (.const ``Int [])))
  mkExpectedTypeHint (.const ``True.intro []) ty

open Lean in
def sorry_proof (cst : Constraint) : Proof? := do
  let ty := mkApp2 (.const ``Constraint.sat []) (toExpr cst) (← mkFreshExprMVar (some (.const ``Int [])))
  mkSorry ty false

structure Problem where
  constraints : AssocList Coefficients (Constraint × Proof?) := ∅

  possible : Bool := true
  -- possible_spec : ¬ ∃ c, contraints.find? c matches some (.impossible)

  proveFalse? : Option Proof? := none

  equalities : List Coefficients := ∅
  -- equalities_spec : ∀ i, equalities.contains i ↔ constraints.find? i matches some (.exact _)

  -- lowerBounds : Array (HashSet Nat)
  -- lowerBounds_spec :
  -- upperBounds : Array (HashSet Nat)


instance : ToString Problem where
  toString p :=
    if p.possible then
      if p.constraints.isEmpty then
        "trivial"
      else
        "\n".intercalate <|
          (p.constraints.toList.map fun ⟨coeffs, ⟨cst, _⟩⟩ => s!"{coeffs} ∈ {cst}")
    else
      "impossible"

structure Inequality where
  coeffs : Coefficients
  cst : Constraint

namespace Inequality

def sat (i : Inequality) (v : List Int) : Prop :=
  i.cst.sat (i.coeffs.eval v)

def normalize (i : Inequality) : Inequality :=
  if i.coeffs.gcd = 0 then
    match i.cst with
    | .lowerBound x => if 0 < x then { i with cst := .impossible } else { i with cst := .trivial }
    | .upperBound y => if y < 0 then { i with cst := .impossible } else { i with cst := .trivial }
    | .between x y => if 0 < x || y < 0 then { i with cst := .impossible } else { i with cst := .trivial }
    | .exact x => if x = 0 then { i with cst := .trivial } else { i with cst := .impossible }
    | _ => i
  else if i.coeffs.gcd = 1 then
    i
  else
    { coeffs := i.coeffs.div_gcd
      cst := i.cst.div i.coeffs.gcd }

theorem normalize_sat {i : Inequality} : i.normalize.sat v = i.sat v :=
  sorry

def of (coeffs : List Int) (cst : Constraint) : Inequality :=
  let coeffs := IntList.trim coeffs
  normalize <|
  if 0 ≤ (coeffs.find? (! · == 0) |>.getD 0) then
    { coeffs := { coeffs }
      cst := cst }
  else
    { coeffs := { coeffs := IntList.smul coeffs (-1) }
      cst := cst.neg }

/-- Convert `const + ∑ coeffs[i] * xᵢ ≥ 0` into an `Inequality`. -/
def of_le (coeffs : List Int) (const : Int) : Inequality :=
  of coeffs (.lowerBound (-const))

/-- Convert `const + ∑ coeffs[i] * xᵢ = 0` into an `Inequality`. -/
def of_eq (coeffs : List Int) (const : Int) : Inequality :=
  of coeffs (.exact (-const))

theorem of_sat {coeffs cst v} : (of coeffs cst).sat v = cst.sat (IntList.dot coeffs v) :=
  sorry

theorem of_le_sat {coeffs const v} : (of_le coeffs const).sat v = (0 ≤ (IntList.dot coeffs v) + const) :=
  sorry

theorem of_eq_sat {coeffs const v} : (of_eq coeffs const).sat v = ((IntList.dot coeffs v) + const = 0) :=
  sorry

-- open Lean in
-- def typecheck (i : Inequality) (p : Proof?) (v : Array Expr) : MetaM Unit := do
--   let p ← p
--   let p := p.instantiate v
--   let t ← inferType p
--   -- Construct the Expr for `i.cst.sat (IntList.dot i.coeffs.coeffs v)`
--   let t' := mkApp2 (.const ``Constraint.sat []) (toExpr i.cst)
--     (mkApp2 (.const ``IntList.dot []) (toExpr i.coeffs.coeffs)
--       (← mkListLit (.const ``Int []) v.toList))
--   -- and check defeq
--   guard (← Meta.isDefEq t t')
section
open Lean

def normalize_proof {i : Inequality} (p : Proof?) : Proof? := do
  let p ← p
  let v ← mkFreshExprMVar (some (mkApp (.const ``List []) (.const ``Int [])))
  -- Hmm, I don't like that we have `Inequality` expressions. Can it even be found by unification?
  let i ← mkFreshExprMVar (some (.const ``Inequality [])) -- We could fill tis in from `inferType p`
  mkEqMPR' (mkApp2 (.const ``Inequality.normalize_sat []) v i) p

def of_proof (coeffs : List Int) (cst : Constraint) (p : Proof?) : Proof? := do
  let p ← p
  mkEqMPR' (mkApp3 (.const ``Inequality.of_sat []) (toExpr coeffs) (toExpr cst) (← atomsList)) p

def of_le_proof (coeffs : List Int) (const : Int) (p : Proof?) : Proof? := do
  let p ← p
  mkEqMPR' (mkApp3 (.const ``Inequality.of_le_sat []) (toExpr coeffs) (toExpr const) (← atomsList)) p

def of_eq_proof (coeffs : List Int) (const : Int) (p : Proof?) : Proof? := do
  let p ← p
  mkEqMPR' (mkApp3 (.const ``Inequality.of_eq_sat []) (toExpr coeffs) (toExpr const) (← atomsList)) p

end

end Inequality

namespace Problem

instance : Inhabited Problem := ⟨{}⟩

-- Membership instance to AssocList?
def sat (p : Problem) (v : List Int) : Prop :=
  ∀ z ∈ p.constraints.toList, (fun ⟨coeffs, cst, _⟩ => cst.sat (coeffs.eval v)) z

open Lean in
/-- Takes a proof that `.impossible.sat t` for some `t`, and constructs a proof of `False`. -/
def proveFalse (coeffs : List Int) (prf : Proof?) : Proof? := do
  let prf ← prf
  let t := mkApp2 (.const ``IntList.dot []) (toExpr coeffs) (← atomsList)
  return mkApp2 (.const ``Constraint.impossible_not_sat []) t prf

def addCondition (p : Problem) (ineq : Inequality) (prf : Proof?) : Problem :=
  if p.possible then
    let ⟨cst', prf'⟩ := (p.constraints.find? ineq.coeffs).getD (.trivial, trivial_proof)
    match cst' with
    | .trivial =>
      match ineq.cst with
      | .trivial => p
      | .impossible => { possible := false, proveFalse? := proveFalse ineq.coeffs.coeffs prf }
      | cst =>
        let constraints := p.constraints.insert ineq.coeffs (cst, prf)
        { constraints
          possible := p.possible
          equalities :=
          if cst matches .exact _ then
            p.equalities.insert' ineq.coeffs
          else
            p.equalities}
    | _ =>
    match cst'.combine ineq.cst with
    | .trivial => p
    | .impossible => { possible := false, proveFalse? := proveFalse ineq.coeffs.coeffs (combine_proofs prf' prf) }
    | cst'' =>
      let constraints := p.constraints.insert ineq.coeffs (cst'', combine_proofs prf' prf)
      { constraints
        possible := p.possible
        -- possible_spec := sorry
        equalities :=
        if cst'' matches .exact _ then
          p.equalities.insert' ineq.coeffs
        else
          p.equalities
        -- equalities_spec := sorry
        }
  else
    p

theorem addCondition_sat : (addCondition p ineq prf).sat v = p.sat v ∧ ineq.sat v :=
  sorry

def addInequality (p : Problem) (coeffs : List Int) (const : Int) (prf? : Option Proof?) : Problem :=
    let i := (.of_le coeffs const)
    let prf := prf?.getD (do mkSorry (← mkFreshExprMVar none) false)
    p.addCondition i (Inequality.of_le_proof coeffs const prf)

def addEquality (p : Problem) (coeffs : List Int) (const : Int) (prf? : Option Proof?) : Problem :=
    let i := (.of_eq coeffs const)
    let prf := prf?.getD (do mkSorry (← mkFreshExprMVar none) false)
    p.addCondition i (Inequality.of_eq_proof coeffs const prf)

def addInequalities (p : Problem) (ineqs : List (List Int × Int × Option Proof?)) : Problem :=
  ineqs.foldl (init := p) fun p ⟨coeffs, const, prf?⟩ => p.addInequality coeffs const prf?

def addEqualities (p : Problem) (ineqs : List (List Int × Int × Option Proof?)) : Problem :=
  ineqs.foldl (init := p) fun p ⟨coeffs, const, prf?⟩ => p.addEquality coeffs const prf?


example : (Problem.addInequalities {}
    [([1, 1], -1, none), ([-1, -1], -1, none)] |>.possible) = false := rfl

example : (Problem.addInequalities {}
    [([2], 2, none), ([-2], -2, none)] |>.possible) = true := rfl

example : (Problem.addInequalities {}
    [([2], 1, none), ([-2], -1, none)] |>.possible) = false := rfl

example : (Problem.addEqualities {}
    [([2], 2, none)] |>.possible) = true := rfl

example : (Problem.addEqualities {}
    [([2], 1, none)] |>.possible) = false := rfl

def selectEquality (p : Problem) : Option Coefficients :=
  p.equalities.foldl (init := none) fun
  | none, c => c
  | some r, c => if 2 ≤ r.minNatAbs && (c.minNatAbs < r.minNatAbs || c.minNatAbs = r.minNatAbs && c.maxNatAbs < r.maxNatAbs) then c else r

def add_smul (c₁ c₂ : List Int) (k : Int) : List Int := c₁ + k * c₂  -- turn this into a single operation

theorem add_smul_sat {c₁ c₂ : List Int} {k : Int} {v : List Int} {cst : Constraint} {r : Int}
    (h₁ : cst.sat (IntList.dot c₁ v)) (h₂ : (Constraint.exact r).sat (IntList.dot c₂ v)) :
    (cst.translate (k * r)).sat (IntList.dot (add_smul c₁ c₂ k) v) :=
  sorry

open Lean in
def add_smul_proof (c₁ c₂ : List Int) (k : Int) (cst : Constraint) (r : Int)
    (prf₁ prf₂ : Proof?) : Proof? := do
  let prf₁ ← prf₁
  let prf₂ ← prf₂
  let v ← mkFreshExprMVar (some (mkApp (.const ``List []) (.const ``Int [])))
  return mkApp8 (.const ``add_smul_sat []) (toExpr c₁) (toExpr c₂) (toExpr k) v (toExpr cst) (toExpr r) prf₁ prf₂

open Lean in
def of_add_smul_proof (c₁ c₂ : List Int) (k : Int) (cst : Constraint) (r : Int)
    (prf₁ prf₂ : Proof?) : Proof? := do
  let p := add_smul_proof c₁ c₂ k cst r prf₁ prf₂ -- this is the proof `(cst.translate (k * r)).sat (IntList.dot (add_smul c₁ c₂ k) v)`
  Inequality.of_proof (add_smul c₁ c₂ k) (cst.translate (k * r)) p

def solveEasyEquality (p : Problem) (c : Coefficients) : Problem :=
  let i := c.coeffs.findIdx? (·.natAbs = 1) |>.getD 0 -- findIdx? is always some
  let sign := c.coeffs.get? i |>.getD 0 |> Int.sign
  match p.constraints.find? c with
  | some (.exact r, prf) =>
    p.constraints.foldl (init := {}) fun p' coeffs ⟨cst, prf'⟩ =>
      match coeffs.coeffs.get? i |>.getD 0 with
      | 0 =>
        p'.addCondition { coeffs, cst } prf'
      | ci =>
        let k := -1 * sign * ci
        p'.addCondition (.of
          (add_smul coeffs.coeffs c.coeffs k)
          (cst.translate (k * r))) (of_add_smul_proof coeffs.coeffs c.coeffs k cst r prf' prf)
  | _ => unreachable!

def freshVar (p : Problem) : Nat := p.constraints.foldl (init := 0) fun l c _ => max l c.coeffs.length

def bmod_coeffs (m : Nat) (coeffs : List Int) (j : Nat) : List Int :=
  IntList.set (coeffs.map fun x => Int.bmod x m) j (-m)

def bmod_cst (m : Nat) (r : Int) : Constraint := .exact (Int.bmod r m)

def bmod (m : Nat) (c : Coefficients) (j : Nat) (r : Int) : Inequality :=
  { coeffs :=
    { coeffs := bmod_coeffs m c.coeffs j }
    cst := bmod_cst m r }

def bmod_transform (m : Nat) (coeffs : List Int) (j : Nat) (r : Int) (v : List Int) : List Int :=
  IntList.set v j sorry

theorem bmod_sat (m : Nat) (coeffs : List Int) (j : Nat) (r : Int) (v : List Int) :
    (bmod_cst m r).sat (IntList.dot (bmod_coeffs m coeffs j) (bmod_transform m coeffs j r v)) =
      (Constraint.exact r).sat (IntList.dot coeffs v) :=
  sorry

open Lean in
def bmod_proof (m : Nat) (coeffs : List Int) (j : Nat) (r : Int) (p : Proof?) : Proof? := do
  let p ← p
  let v ← mkFreshExprMVar (some (mkApp (.const ``List []) (.const ``Int [])))
  mkEqMPR' (mkApp5 (.const ``bmod_sat []) (toExpr m) (toExpr coeffs) (toExpr j) (toExpr r) v) p

/--
We deal with a hard equality by introducing a new easy equality.

After solving the easy equality,
the minimum lexicographic value of `(c.minNatAbs, c.maxNatAbs)` will have been reduced.
-/
def dealWithHardEquality (p : Problem) (c : Coefficients) : Problem :=
  let m := c.minNatAbs + 1
  let j := p.freshVar
  match p.constraints.find? c with
  | some (.exact r, prf) =>
    p.addCondition
      (bmod m c j r)
      (bmod_proof m c.coeffs j r prf)
  | _ => unreachable!

def solveEquality (p : Problem) (c : Coefficients) : Problem :=
  if c.minNatAbs = 1 then
    p.solveEasyEquality c
  else
    p.dealWithHardEquality c

def solveEqualities (p : Problem) (fuel : Nat := 100) : Problem :=
  match fuel with
  | 0 => p
  | f + 1 =>
  -- dbgTrace ("---\n" ++ toString p) fun _ =>
  match p.selectEquality with
  | some c => (p.solveEquality c).solveEqualities f
  | none => p

def run (p : Problem) : Problem := p.solveEqualities 100
