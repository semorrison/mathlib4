
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
open Lean (HashSet)

namespace Int

theorem eq_iff_le_and_ge {x y : Int} : x = y ↔ x ≤ y ∧ y ≤ x := by
  constructor
  · simp_all
  · rintro ⟨h₁, h₂⟩
    exact Int.le_antisymm h₁ h₂

end Int

namespace List

/-- Variant of `List.insert` using `BEq` instead of `DecidableEq`. -/
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

def partitionMapRev (f : α → β → γ ⊕ δ) (l : AssocList α β) : AssocList α γ × AssocList α δ :=
  go {} {} l
where
  go : AssocList α γ → AssocList α δ → AssocList α β → AssocList α γ × AssocList α δ
  | xs, ys, .nil => (xs, ys)
  | xs, ys, .cons a b t => match f a b with
    | .inl x => go (cons a x xs) ys t
    | .inr y => go xs (cons a y ys) t

-- def partitionMap (f : α → β → γ ⊕ δ) (l : AssocList α β) : AssocList α γ × AssocList α δ :=
--   match l.partitionMapRev f with
--   | (xs, ys) => (xs.reverse, ys.reverse)

def partitionRev (f : α → β → Bool) (l : AssocList α β) : AssocList α β × AssocList α β :=
  l.partitionMapRev fun a b => bif f a b then .inl b else .inr b

end Std.AssocList

namespace Option

@[simp] theorem all_none : Option.all p none = true := rfl
@[simp] theorem all_some : Option.all p (some x) = p x := rfl

def min [Min α] : Option α → Option α → Option α
  | some x, some y => some (Min.min x y)
  | some x, none => some x
  | none, some y => some y
  | none, none => none

def max [Max α] : Option α → Option α → Option α
  | some x, some y => some (Max.max x y)
  | some x, none => some x
  | none, some y => some y
  | none, none => none

end Option

namespace Omega.ProofProducing

abbrev LowerBound : Type := Option Int
abbrev UpperBound : Type := Option Int

def LowerBound.sat (b : LowerBound) (t : Int) := b.all fun x => x ≤ t
def UpperBound.sat (b : UpperBound) (t : Int) := b.all fun y => t ≤ y

structure Constraint where
  lowerBound : LowerBound
  upperBound : UpperBound
deriving BEq, Repr, Lean.ToExpr

namespace Constraint

instance : ToString Constraint where
  toString := fun
  | ⟨none, none⟩ => "(-∞, ∞)"
  | ⟨none, some y⟩ => s!"(-∞, {y}]"
  | ⟨some x, none⟩ => s!"[{x}, ∞)"
  | ⟨some x, some y⟩ =>
    if y < x then "∅" else if x = y then s!"\{{x}}" else s!"[{x}, {y}]"

def sat (c : Constraint) (t : Int) : Bool := c.lowerBound.sat t ∧ c.upperBound.sat t

def map (c : Constraint) (f : Int → Int) : Constraint where
  lowerBound := c.lowerBound.map f
  upperBound := c.upperBound.map f

def translate (c : Constraint) (t : Int) : Constraint := c.map (· + t)

theorem translate_sat : {c : Constraint} → {v : Int} → sat c v → sat (c.translate t) (v + t) := by
  rintro ⟨_ | l, _ | u⟩ v w <;> simp_all [sat, translate, LowerBound.sat, UpperBound.sat, map]
  · exact Int.add_le_add_right w t
  · exact Int.add_le_add_right w t
  · rcases w with ⟨w₁, w₂⟩; constructor
    · exact Int.add_le_add_right w₁ t
    · exact Int.add_le_add_right w₂ t

def flip (c : Constraint) : Constraint where
  lowerBound := c.upperBound
  upperBound := c.lowerBound

def neg (c : Constraint) : Constraint := c.flip.map (- ·)

theorem neg_sat : {c : Constraint} → {v : Int} → sat c v → sat (c.neg) (-v) := sorry

def trivial : Constraint := ⟨none, none⟩
def impossible : Constraint := ⟨some 1, some 0⟩
def exact (r : Int) : Constraint := ⟨some r, some r⟩

@[simp] theorem exact_sat (r : Int) (t : Int) : (Constraint.exact r).sat t = decide (r = t) := sorry

def isImpossible : Constraint → Bool
  | ⟨some x, some y⟩ => y < x
  | _ => false

def isExact : Constraint → Bool
  | ⟨some x, some y⟩ => x = y
  | _ => false

theorem not_sat_of_isImpossible (h : isImpossible c) {t} : ¬ c.sat t := sorry

def scale (k : Int) (c : Constraint) : Constraint :=
  if k = 0 then
    if c.isImpossible then c else ⟨some 0, some 0⟩
  else if 0 < k then
    c.map (k * ·)
  else
    c.flip.map (k * ·)

theorem scale_sat {c : Constraint } (w : c.sat t) : (scale k c).sat (k * t) := sorry

def add (x y : Constraint) : Constraint where
  lowerBound := do let a ← x.lowerBound; let b ← y.lowerBound; pure (a + b)
  upperBound := do let a ← x.upperBound; let b ← y.upperBound; pure (a + b)

theorem add_sat (w₁ : c₁.sat x₁) (w₂ : c₂.sat x₂) : (add c₁ c₂).sat (x₁ + x₂) := sorry

def combo (a : Int) (x : Constraint) (b : Int) (y : Constraint) : Constraint :=
  add (scale a x) (scale b y)

def combo_sat (w₁ : c₁.sat x₁) (w₂ : c₂.sat x₂) : (combo a c₁ b c₂).sat (a * x₁ + b * x₂) := sorry

def combine (x y : Constraint) : Constraint where
  lowerBound := Option.max x.lowerBound y.lowerBound
  upperBound := Option.min x.upperBound y.upperBound

theorem combine_sat : (c : Constraint) → (c' : Constraint) → (t : Int) →
     (c.combine c').sat t = (c.sat t ∧ c'.sat t) := sorry


def div (c : Constraint) (k : Nat) : Constraint where
  lowerBound := c.lowerBound.map fun x => (- ((- x) / k))
  upperBound := c.upperBound.map fun y => y / k

theorem div_sat (c : Constraint) (k : Nat) (t : Int) (h : (c.div k).sat t) : c.sat (t * k) := sorry

abbrev sat' (c : Constraint) (x y : List Int) := c.sat (IntList.dot x y)

theorem combine_sat' {s t : Constraint} {x y} (ws : s.sat' x y) (wt : t.sat' x y) : (s.combine t).sat' x y := sorry

theorem not_sat'_of_isImpossible (h : isImpossible c) {x y} : ¬ c.sat' x y := sorry

end Constraint

-- FIXME get rid of this: no kernel computation
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

  -- maxNatAbs : Nat := coeffs.map Int.natAbs |>.maximum? |>.getD 0
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

abbrev eval (c : Coefficients) (v : List Int) : Int := IntList.dot c.coeffs v

instance : Hashable Coefficients := ⟨hash⟩

-- FIXME not:
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
-/
abbrev Proof : Type := OmegaM Expr

-- instance : Inhabited Proof? where
--   default := do failure

-- section
-- open Lean Meta
-- private def throwAppBuilderException {α} (op : Name) (msg : MessageData) : MetaM α :=
--   throwError "AppBuilder for '{op}', {msg}"

-- private def mkAppMFinal (methodName : Name) (f : Expr) (args : Array Expr) (instMVars : Array MVarId) : MetaM Expr := do
--   instMVars.forM fun mvarId => do
--     let mvarDecl ← mvarId.getDecl
--     let mvarVal  ← synthInstance mvarDecl.type
--     mvarId.assign mvarVal
--   let result ← instantiateMVars (mkAppN f args)
--   -- if (← hasAssignableMVar result) then throwAppBuilderException methodName ("result contains metavariables" ++ indentExpr result)
--   return result

-- private partial def mkAppMArgs (f : Expr) (fType : Expr) (xs : Array Expr) : MetaM Expr :=
--   let rec loop (type : Expr) (i : Nat) (j : Nat) (args : Array Expr) (instMVars : Array MVarId) : MetaM Expr := do
--     if i >= xs.size then
--       mkAppMFinal `mkAppM f args instMVars
--     else match type with
--       | Expr.forallE n d b bi =>
--         let d  := d.instantiateRevRange j args.size args
--         match bi with
--         | BinderInfo.implicit     =>
--           let mvar ← mkFreshExprMVar d MetavarKind.natural n
--           loop b i j (args.push mvar) instMVars
--         | BinderInfo.strictImplicit     =>
--           let mvar ← mkFreshExprMVar d MetavarKind.natural n
--           loop b i j (args.push mvar) instMVars
--         | BinderInfo.instImplicit =>
--           let mvar ← mkFreshExprMVar d MetavarKind.synthetic n
--           loop b i j (args.push mvar) (instMVars.push mvar.mvarId!)
--         | _ =>
--           let x := xs[i]!
--           let xType ← inferType x
--           if (← isDefEq d xType) then
--             loop b (i+1) j (args.push x) instMVars
--           else
--             throwAppTypeMismatch (mkAppN f args) x
--       | type =>
--         let type := type.instantiateRevRange j args.size args
--         let type ← whnfD type
--         if type.isForall then
--           loop type i args.size args instMVars
--         else
--           throwAppBuilderException `mkAppM m!"too many explicit arguments provided to{indentExpr f}\narguments{indentD xs}"
--   loop fType 0 0 #[] #[]

-- private def mkFun (constName : Name) : MetaM (Expr × Expr) := do
--   let cinfo ← getConstInfo constName
--   let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
--   let f := mkConst constName us
--   let fType ← instantiateTypeLevelParams cinfo us
--   return (f, fType)

-- def mkAppM' (constName : Name) (xs : Array Expr) : MetaM Expr := do
--     let (f, fType) ← mkFun constName
--     mkAppMArgs f fType xs
-- end

-- def mkEqMPR' (eqProof pr : Expr) : MetaM Expr :=
--   mkAppM' ``Eq.mpr #[eqProof, pr]

-- open Qq Lean in
-- def combine_proofs (p₁ p₂ : Proof?) : Proof? := do
--   let p₁ ← p₁ -- s₁.sat (IntList.dot c a)
--   let p₂ ← p₂ -- s₂.sat (IntList.dot c a)
--   let c₁ ← mkFreshExprMVar (some (.const ``Constraint [])) -- We could fill these in from `inferType p₁`
--   let c₂ ← mkFreshExprMVar (some (.const ``Constraint []))
--   let t ← mkFreshExprMVar (some (.const ``Int []))
--   mkEqMPR' (mkApp3 (.const ``Constraint.combine_sat []) c₁ c₂ t) (← mkAppM' ``And.intro #[p₁, p₂])

-- open Lean in
-- def trivial_proof : Proof? := do
--   let ty := mkApp2 (.const ``Constraint.sat []) (.const ``Constraint.trivial []) (← mkFreshExprMVar (some (.const ``Int [])))
--   mkExpectedTypeHint (.const ``True.intro []) ty

-- open Lean in
-- def sorry_proof (cst : Constraint) : Proof? := do
--   let ty := mkApp2 (.const ``Constraint.sat []) (toExpr cst) (← mkFreshExprMVar (some (.const ``Int [])))
--   mkSorry ty false

def normalize : Constraint × List Int → Constraint × List Int
  | ⟨s, x⟩ =>
    let gcd := IntList.gcd x -- TODO should we be caching this?
    if gcd = 0 then
      if s.sat 0 then
        (.trivial, x)
      else
        (.impossible, x)
    else if gcd = 1 then
      (s, x)
    else
      (s.div gcd, IntList.sdiv x gcd)

abbrev normalizeConstraint (s : Constraint) (x : List Int) : Constraint := (normalize (s, x)).1
abbrev normalizeCoeffs (s : Constraint) (x : List Int) : List Int := (normalize (s, x)).2

theorem normalize_sat {s x v} (w : s.sat' x v) :
    (normalizeConstraint s x).sat' (normalizeCoeffs s x) v := sorry

def positivize : Constraint × List Int → Constraint × List Int
  | ⟨s, x⟩ =>
    let x := IntList.trim x -- TODO why?
    if 0 ≤ (x.find? (! · == 0) |>.getD 0) then
      (s, x)
    else
      (s.neg, IntList.smul x (-1) )

abbrev positivizeConstraint (s : Constraint) (x : List Int) : Constraint := (positivize (s, x)).1
abbrev positivizeCoeffs (s : Constraint) (x : List Int) : List Int := (positivize (s, x)).2

theorem positivize_sat {s x v} (w : s.sat' x v) :
    (positivizeConstraint s x).sat' (positivizeCoeffs s x) v := sorry

-- TODO make this a single operation
def IntList.combo (a : Int) (x : List Int) (b : Int) (y : List Int) : List Int :=
  IntList.add (IntList.smul x a) (IntList.smul y b)

theorem combo_sat (s t : Constraint)
    (a : Int) (x : List Int) (b : Int) (y : List Int) (v : List Int)
    (wx : s.sat' x v) (wy : t.sat' y v) : (Constraint.combo a s b t).sat' (IntList.combo a x b y) v :=
  sorry

def IntList.bmod (x : List Int) (m : Nat) : List Int := x.map (Int.bmod · m)

theorem IntList.bmod_length (m) : (IntList.bmod x m).length = x.length := List.length_map _ _

def bmod_coeffs (m : Nat) (i : Nat) (x : List Int) : List Int :=
  IntList.set (IntList.bmod x m) i m

abbrev bmod_sub_term (m : Nat) (a b : List Int) : Int :=
    (Int.bmod (IntList.dot a b) m) - IntList.dot (IntList.bmod a m) b

theorem bmod_sat_aux (m : Nat) (a b : List Int) : (m : Int) ∣ bmod_sub_term m a b :=
  sorry

abbrev bmod_div_term (m : Nat) (a b : List Int) : Int := bmod_sub_term m a b / m

theorem bmod_sat (m : Nat) (r : Int) (i : Nat) (x v : List Int)
    (h : x.length ≤ i)  -- during proof reconstruction this will be by `decide`
    (p : IntList.get v i = bmod_div_term m x v) -- and this will be by `rfl`
    (w : (Constraint.exact r).sat' x v) :
    (Constraint.exact (Int.bmod r m)).sat' (bmod_coeffs m i x) v := by
  simp at w
  simp only [p, bmod_coeffs, Constraint.exact_sat, IntList.dot_set_left, decide_eq_true_eq]
  rw [← IntList.bmod_length m] at h
  rw [IntList.get_of_length_le h, Int.sub_zero, Int.mul_ediv_cancel' (bmod_sat_aux _ _ _), w,
    ← Int.add_sub_assoc, Int.add_comm, Int.add_sub_assoc, Int.sub_self, Int.add_zero]

inductive Justification : Constraint → List Int → Type
-- `Problem.assumptions[i]` generates a proof that `s.sat (IntList.dot coeffs atoms)`
| assumption (coeffs : List Int) (s : Constraint) (i : Nat) : Justification s coeffs
| normalize (j : Justification s c) : Justification (normalizeConstraint s c) (normalizeCoeffs s c)
| positivize (j : Justification s c) : Justification (positivizeConstraint s c) (positivizeCoeffs s c)
| combine {s t c} (j : Justification s c) (k : Justification t c) : Justification (s.combine t) c
| combo {s t x y} (a : Int) (j : Justification s x) (b : Int) (k : Justification t y) : Justification (Constraint.combo a s b t) (IntList.combo a x b y)
| bmod (m : Nat) (r : Int) (i : Nat) {x} (j : Justification (.exact r) x) : Justification (.exact (Int.bmod r m)) (bmod_coeffs m i x)

namespace Justification

open Lean

def normalizeProof (s : Constraint) (x : List Int) (v : Expr) (prf : Expr) : Expr :=
  mkApp4 (.const ``normalize_sat []) (toExpr s) (toExpr x) v prf

def positivizeProof (s : Constraint) (x : List Int) (v : Expr) (prf : Expr) : Expr :=
  mkApp4 (.const ``positivize_sat []) (toExpr s) (toExpr x) v prf

def combineProof (s t : Constraint) (x : List Int) (v : Expr) (ps pt : Expr) : Expr :=
  mkApp6 (.const ``Constraint.combine_sat' []) (toExpr s) (toExpr t) (toExpr x) v ps pt

def comboProof (s t : Constraint) (a : Int) (x : List Int) (b : Int) (y : List Int)
    (v : Expr) (px py : Expr) : Expr :=
  mkApp9 (.const ``combo_sat []) (toExpr s) (toExpr t) (toExpr a) (toExpr x) (toExpr b) (toExpr y)
    v px py

/-- Construct the term with type hint `(Eq.refl a : a = b)`-/
def mkEqReflWithExpectedType (a b : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)

open Qq in
def bmodProof (m : Nat) (r : Int) (i : Nat) (x : List Int) (v : Expr) (w : Expr) : MetaM Expr := do
  let m := toExpr m
  let r := toExpr r
  let i := toExpr i
  let x := toExpr x
  let h ← mkDecideProof q(List.length $x ≤ $i)
  let p ← mkEqReflWithExpectedType (mkApp2 (.const ``IntList.get []) v i) (mkApp3 (.const ``bmod_div_term []) m x v)
  return mkApp8 (.const ``bmod_sat []) m r i x v h p w

/-- Constructs a proof that `s.sat' c v = true` -/
def proof (v : Expr) (assumptions : Array Proof) : Justification s c → Proof
| assumption s c i => assumptions[i]!
| @normalize s c j => return normalizeProof s c v (← proof v assumptions j)
| @positivize s c j => return positivizeProof s c v (← proof v assumptions j)
| @combine s t c j k => return combineProof s t c v (← proof v assumptions j) (← proof v assumptions k)
| @combo s t x y a j b k => return comboProof s t a x b y v (← proof v assumptions j) (← proof v assumptions k)
| @bmod m r i x j => do bmodProof m r i x v (← proof v assumptions j)

end Justification

structure Fact where
  coeffs : List Int
  constraint : Constraint
  justification : Justification constraint coeffs

namespace Fact

def positivize (f : Fact) : Fact := { justification := f.justification.positivize }
def normalize (f : Fact) : Fact := { justification := f.justification.normalize }
def combo (a : Int) (f : Fact) (b : Int) (g : Fact) : Fact :=
  { justification := .combo a f.justification b g.justification }

end Fact

structure Problem where
  assumptions : Array Proof := ∅
  constraints : AssocList (List Int) Fact := ∅

  possible : Bool := true

  proveFalse? : Option Proof := none
  proveFalse?_spec : possible || proveFalse?.isSome := by rfl

  equalities : List (List Int) := ∅

instance : ToString Problem where
  toString p :=
    if p.possible then
      if p.constraints.isEmpty then
        "trivial"
      else
        "\n".intercalate <|
          (p.constraints.toList.map fun ⟨coeffs, ⟨_, cst, _⟩⟩ => s!"{coeffs} ∈ {cst}")
    else
      "impossible"


-- structure Inequality where
--   coeffs : Coefficients
--   cst : Constraint

-- namespace Inequality

-- abbrev sat (i : Inequality) (v : List Int) : Prop :=
--   i.cst.sat (i.coeffs.eval v)

-- def normalize (i : Inequality) : Inequality :=
--   if i.coeffs.gcd = 0 then
--     if i.cst.sat 0 then
--       { i with cst := .trivial }
--     else
--       { i with cst := .impossible }
--   else if i.coeffs.gcd = 1 then
--     i
--   else
--     { coeffs := i.coeffs.div_gcd
--       cst := i.cst.div i.coeffs.gcd }

-- theorem normalize_sat {i : Inequality} : i.normalize.sat v = i.sat v :=
--   sorry

-- def of (coeffs : List Int) (cst : Constraint) : Inequality :=
--   let coeffs := IntList.trim coeffs
--   normalize <|
--   if 0 ≤ (coeffs.find? (! · == 0) |>.getD 0) then
--     { coeffs := { coeffs }
--       cst := cst }
--   else
--     { coeffs := { coeffs := IntList.smul coeffs (-1) }
--       cst := cst.neg }

-- /-- Convert `const + ∑ coeffs[i] * xᵢ ≥ 0` into an `Inequality`. -/
-- def of_le (coeffs : List Int) (const : Int) : Inequality :=
--   of coeffs ⟨some (-const), none⟩

-- /-- Convert `const + ∑ coeffs[i] * xᵢ = 0` into an `Inequality`. -/
-- def of_eq (coeffs : List Int) (const : Int) : Inequality :=
--   of coeffs ⟨some (-const), some (-const)⟩

-- theorem of_sat {coeffs cst v} : (of coeffs cst).sat v = cst.sat (IntList.dot coeffs v) :=
--   sorry

-- theorem of_le_sat {coeffs const v} : (of_le coeffs const).sat v = (0 ≤ const + (IntList.dot coeffs v)) :=
--   sorry

-- theorem of_eq_sat {coeffs const v} : (of_eq coeffs const).sat v = (const + (IntList.dot coeffs v) = 0) :=
--   sorry

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
-- section
-- open Lean

-- def normalize_proof {i : Inequality} (p : Proof?) : Proof? := do
--   let p ← p
--   let v ← mkFreshExprMVar (some (mkApp (.const ``List [.zero]) (.const ``Int [])))
--   -- Hmm, I don't like that we have `Inequality` expressions. Can it even be found by unification?
--   let i ← mkFreshExprMVar (some (.const ``Inequality [])) -- We could fill tis in from `inferType p`
--   mkEqMPR' (mkApp2 (.const ``Inequality.normalize_sat []) v i) p

-- def of_proof (coeffs : List Int) (cst : Constraint) (p : Proof?) : Proof? := do
--   let p ← p
--   mkEqMPR' (mkApp3 (.const ``Inequality.of_sat []) (toExpr coeffs) (toExpr cst) (← atomsList)) p

-- def of_le_proof (coeffs : List Int) (const : Int) (p : Proof?) : Proof? := do
--   let p ← p
--   mkEqMPR' (mkApp3 (.const ``Inequality.of_le_sat []) (toExpr coeffs) (toExpr const) (← atomsList)) p

-- def of_eq_proof (coeffs : List Int) (const : Int) (p : Proof?) : Proof? := do
--   let p ← p
--   mkEqMPR' (mkApp3 (.const ``Inequality.of_eq_sat []) (toExpr coeffs) (toExpr const) (← atomsList)) p

-- end

-- end Inequality

namespace Problem

-- instance : Inhabited Problem where
--   default :=
--   { assumptions := ∅
--     equalities := ∅
--     possible := true
--     proveFalse?_spec := rfl
--     }
-- instance : EmptyCollection Problem where emptyCollection := default

-- -- Membership instance to AssocList?
-- def sat (p : Problem) (v : List Int) : Prop :=
--   ∀ z ∈ p.constraints.toList, (fun ⟨coeffs, cst, _⟩ => cst.sat (coeffs.eval v)) z

open Lean in
/--
Takes a proof that `s.sat' x v` for some `s` such that `s.isImpossible`,
and constructs a proof of `False`.
-/
def proveFalse {s x} (j : Justification s x) (assumptions : Array Proof) : Proof := do
  let atoms ← atoms
  let v ← mkListLit (.const ``Int [])
    (atoms ++ (← (List.range (x.length - atoms.length)).mapM fun _ => Meta.mkFreshExprMVar (some (.const ``Int []))))
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
        proveFalse?_spec := rfl }
    else
      { p with
        constraints := p.constraints.insert x f
        proveFalse?_spec := p.proveFalse?_spec
        equalities :=
        if f.constraint.isExact then
          p.equalities.insert' x
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

-- theorem addConstraint_sat : (addConstraint p ineq prf).sat v = p.sat v ∧ ineq.sat v :=
--   sorry

def addInequality (p : Problem) (coeffs : List Int) (const : Int) (prf? : Option Proof) : Problem :=
    let prf := prf?.getD (do mkSorry (← mkFreshExprMVar none) false)
    let i := p.assumptions.size
    let p' := { p with assumptions := p.assumptions.push prf }
    let f : Fact :=
    { coeffs
      constraint := { lowerBound := const, upperBound := none }
      justification := .assumption _ _ i }
    p'.addConstraint f.positivize.normalize
def addEquality (p : Problem) (coeffs : List Int) (const : Int) (prf? : Option Proof) : Problem :=
    let prf := prf?.getD (do mkSorry (← mkFreshExprMVar none) false)
    let i := p.assumptions.size
    let p' := { p with assumptions := p.assumptions.push prf }
    let f : Fact :=
    { coeffs
      constraint := { lowerBound := const, upperBound := const }
      justification := .assumption _ _ i }
    p'.addConstraint f.positivize.normalize

def addInequalities (p : Problem) (ineqs : List (List Int × Int × Option Proof)) : Problem :=
  ineqs.foldl (init := p) fun p ⟨coeffs, const, prf?⟩ => p.addInequality coeffs const prf?

def addEqualities (p : Problem) (eqs : List (List Int × Int × Option Proof)) : Problem :=
  eqs.foldl (init := p) fun p ⟨coeffs, const, prf?⟩ => p.addEquality coeffs const prf?

/-- info: [1, 1] ∈ [-1, 1] -/
#guard_msgs in
#eval Problem.addInequalities {} [([1, 1], -1, none), ([-1, -1], -1, none)]

/-- info: [1] ∈ {1} -/
#guard_msgs in
#eval Problem.addInequalities {} [([2], 2, none), ([-2], -2, none)]

/-- info: impossible -/
#guard_msgs in
#eval Problem.addInequalities {} [([2], 1, none), ([-2], -1, none)]

/-- info: [1] ∈ {1} -/
#guard_msgs in
#eval Problem.addEqualities {} [([2], 2, none)]

/-- info: impossible -/
#guard_msgs in
#eval Problem.addEqualities {} [([2], 1, none)]

def selectEquality (p : Problem) : Option Coefficients :=
  p.equalities.foldl (init := none) fun
  | none, c => c
  | some r, c => if 2 ≤ r.minNatAbs && (c.minNatAbs < r.minNatAbs || c.minNatAbs = r.minNatAbs && c.maxNatAbs < r.maxNatAbs) then c else r

def add_smul (c₁ c₂ : List Int) (k : Int) : List Int := c₁ + k * c₂  -- turn this into a single operation
def combo (a : Int) (x : List Int) (b : Int) (y : List Int) := a * x + b * y -- turn this into a single operation

theorem add_smul_sat {c₁ c₂ : List Int} {k : Int} {v : List Int} {cst : Constraint} {r : Int}
    (h₁ : cst.sat (IntList.dot c₁ v)) (h₂ : Constraint.sat ⟨some r, some r⟩ (IntList.dot c₂ v)) :
    (cst.translate (k * r)).sat (IntList.dot (add_smul c₁ c₂ k) v) :=
  sorry

open Lean in
def add_smul_proof (c₁ c₂ : List Int) (k : Int) (cst : Constraint) (r : Int)
    (prf₁ prf₂ : Proof?) : Proof? := do
  let prf₁ ← prf₁
  let prf₂ ← prf₂
  let v ← mkFreshExprMVar (some (mkApp (.const ``List [.zero]) (.const ``Int [])))
  return mkApp8 (.const ``add_smul_sat []) (toExpr c₁) (toExpr c₂) (toExpr k) v (toExpr cst) (toExpr r) prf₁ prf₂

open Lean in
def of_add_smul_proof (c₁ c₂ : List Int) (k : Int) (cst : Constraint) (r : Int)
    (prf₁ prf₂ : Proof?) : Proof? := do
  let p := add_smul_proof c₁ c₂ k cst r prf₁ prf₂ -- this is the proof `(cst.translate (k * r)).sat (IntList.dot (add_smul c₁ c₂ k) v)`
  Inequality.of_proof (add_smul c₁ c₂ k) (cst.translate (k * r)) p

theorem combo_sat (a : Int) (x : List Int) (b : Int) (y : List Int) (s t : Constraint) (v : List Int)
    (hs : s.sat (IntList.dot x v)) (ht : t.sat (IntList.dot y v)) :
    (Constraint.combo a s b t).sat (IntList.dot (combo a x b y) v) :=
  sorry

open Lean in
def combo_proof (a : Int) (x : List Int) (b : Int) (y : List Int) (s t : Constraint)
    (sp tp : Proof?) : Proof? := do
  let sp ← sp
  let tp ← tp
  let v ← mkFreshExprMVar (some (mkApp (.const ``List [.zero]) (.const ``Int [])))
  return mkApp9 (.const ``combo_sat []) (toExpr a) (toExpr x) (toExpr b) (toExpr y) (toExpr s) (toExpr t) v sp tp

open Lean in
def of_combo_proof (a : Int) (x : List Int) (b : Int) (y : List Int) (s t : Constraint)
    (sp tp : Proof?) : Proof? := do
  let p := combo_proof a x b y s t sp tp -- this is the proof `(Constraint.combo a s b t).sat (IntList.dot (combo a x b y) v)`
  Inequality.of_proof (combo a x b y) (Constraint.combo a s b t) p

def solveEasyEquality (p : Problem) (c : Coefficients) : Problem :=
  let i := c.coeffs.findIdx? (·.natAbs = 1) |>.getD 0 -- findIdx? is always some
  let sign := c.coeffs.get? i |>.getD 0 |> Int.sign
  match p.constraints.find? c with
  | some (⟨some r, _⟩, prf) =>
    p.constraints.foldl (init := {}) fun p' coeffs ⟨cst, prf'⟩ =>
      match coeffs.coeffs.get? i |>.getD 0 with
      | 0 =>
        p'.addConstraint { coeffs, cst } prf'
      | ci =>
        let k := -1 * sign * ci
        p'.addConstraint (.of -- FIXME can we combine addCondition and of?
          (add_smul coeffs.coeffs c.coeffs k)
          (cst.translate (k * r))) (of_add_smul_proof coeffs.coeffs c.coeffs k cst r prf' prf)
  | _ => unreachable!

-- TODO probably should just cache the active variables, or this number
def maxVar (p : Problem) : Nat := p.constraints.foldl (init := 0) fun l c _ => max l c.coeffs.length
-- we could use mex here:
def freshVar (p : Problem) : Nat := p.maxVar

def IntList.bmod (xs : List Int) (m : Nat) : List Int :=
  xs.map fun x => Int.bmod x m

theorem IntList.dvd_sub_bmod_dot (xs ys : List Int) (m : Nat) :
    (m : Int) ∣ (IntList.dot (xs - IntList.bmod xs m) ys) := sorry

def bmod_coeffs (m : Nat) (coeffs : List Int) (j : Nat) : List Int :=
  IntList.set (IntList.bmod coeffs m) j (-m)
  -- coeffs +

def bmod_cst (m : Nat) (r : Int) : Constraint := .exact (Int.bmod r m)

def bmod (m : Nat) (c : Coefficients) (j : Nat) (r : Int) : Inequality :=
  { coeffs :=
    { coeffs := bmod_coeffs m c.coeffs j }
    cst := bmod_cst m r }

-- IntList.get v j will be zero here, but it makes the proofs easier.
def bmod_transform (m : Nat) (coeffs : List Int) (j : Nat) (r : Int) (v : List Int) : List Int :=
  IntList.set v j (IntList.get v j + (IntList.dot (coeffs - bmod_coeffs m coeffs j) v )/m  + - (r - Int.bmod r m)/m)

-- bmod r m = ()

theorem bmod_sat (m : Nat) (coeffs : List Int) (j : Nat) (r : Int) (v : List Int) :
    (bmod_cst m r).sat (IntList.dot (bmod_coeffs m coeffs j) (bmod_transform m coeffs j r v)) =
      (Constraint.exact r).sat (IntList.dot coeffs v) := by
  simp? [bmod_cst, bmod_coeffs, bmod_transform, Constraint.exact_sat]
  sorry

theorem bmod_sat_of (m : Nat) (coeffs : List Int) (j : Nat) (r : Int) (v : List Int)
    (w : (Constraint.exact r).sat (IntList.dot coeffs v)) :
    (bmod_cst m r).sat (IntList.dot (bmod_coeffs m coeffs j) (bmod_transform m coeffs j r v)) := by
  simp_all [bmod_sat]


open Lean in
def bmod_proof (m : Nat) (coeffs : List Int) (j : Nat) (r : Int) (p : Proof?) : Proof? := do
  let p ← p
  let ty ← inferType p
  let ty ← whnf ty
  IO.println s!"{← ppExpr ty}"
  let v ← match ty.getAppFnArgs with
  | (``Eq, #[(.const ``Bool []), lhs, _]) =>
    match lhs.getAppFnArgs with
    | (``Constraint.sat, #[_, dot]) => do
      IO.println s!"{dot}"
      match dot.getAppFnArgs with
      | (``IntList.dot, #[_, v]) => do pure v
      | (``Coefficients.eval, #[_, v]) => do pure v
      | _ => throwError "doesn't look like IntList.dot _ v: {dot}"
    | _ => throwError "doesn't look like Constraint.sat _ _: {lhs}"
  | _ => throwError "doesn't look like _ = _: {ty}"
  -- let v ← mkFreshExprMVar (some (mkApp (.const ``List [.zero]) (.const ``Int [])))
  return mkApp6 (.const ``bmod_sat_of []) (toExpr m) (toExpr coeffs) (toExpr j) (toExpr r) v p

/--
We deal with a hard equality by introducing a new easy equality.

After solving the easy equality,
the minimum lexicographic value of `(c.minNatAbs, c.maxNatAbs)` will have been reduced.
-/
def dealWithHardEquality (p : Problem) (c : Coefficients) : Problem :=
  let m := c.minNatAbs + 1
  let j := p.freshVar
  match p.constraints.find? c with
  | some (⟨some r, _⟩, prf) =>
    p.addConstraint
      (bmod m c j r)
      (bmod_proof m c.coeffs j r prf)
  | _ => unreachable!

def solveEquality (p : Problem) (c : Coefficients) : Problem :=
  if c.minNatAbs = 1 then
    p.solveEasyEquality c
  else
    p.dealWithHardEquality c

partial def solveEqualities (p : Problem) : Problem :=
  match p.selectEquality with
  | some c => (p.solveEquality c).solveEqualities
  | none => p

structure FourierMotzkinData where
  irrelevant : List (Coefficients × Constraint × Proof?) := []
  lowerBounds : List (Coefficients × (Constraint × Proof?) × Int) := []
  upperBounds : List (Coefficients × (Constraint × Proof?) × Int) := []
  lowerExact : Bool := true
  upperExact : Bool := true
deriving Inhabited

def FourierMotzkinData.size (d : FourierMotzkinData) : Nat := d.lowerBounds.length * d.upperBounds.length
def FourierMotzkinData.exact (d : FourierMotzkinData) : Bool := d.lowerExact || d.upperExact

def fourierMotzkinData (p : Problem) : Array FourierMotzkinData := Id.run do
  -- For each variable, prepare the irrelevant constraints, lower and upper bounds,
  -- and whether the elimination would be exact.
  -- TODO Does it make sense to precompute some or all of this?
  let n := p.maxVar
  let mut data : Array FourierMotzkinData := Array.mk (List.replicate p.maxVar {})
  for (coeffs, cst, prf?) in p.constraints do
    for i in [0:n] do
      let x := IntList.get coeffs.coeffs i
      data := data.modify i fun d =>
        if x = 0 then
          { d with irrelevant := (coeffs, cst, prf?) :: d.irrelevant }
        else Id.run do
          let cst' := cst.scale x
          let mut d' := d
          if cst'.lowerBound.isSome then
            d' := { d' with
              lowerBounds := (coeffs, ⟨cst, prf?⟩, x) :: d'.lowerBounds
              lowerExact := d'.lowerExact && x.natAbs = 1 }
          if cst'.upperBound.isSome then
            d' := { d' with
              upperBounds := (coeffs, ⟨cst, prf?⟩, x) :: d'.upperBounds
              upperExact := d'.upperExact && x.natAbs = 1 }
          return d'
  return data

-- Now decide which variable to eliminate.
-- We want an exact elimination if possible,
-- and otherwise the one with the fewest new constraints.
def fourierMotzkinSelect (data : Array FourierMotzkinData) : FourierMotzkinData := Id.run do
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
  let mut r : Problem := ∅
  for (c, cst, prf) in irrelevant do
    r := r.insertConstraint c cst prf
  for ⟨x, ⟨xc, xp⟩, b⟩ in lower do
    for ⟨y, ⟨yc, yp⟩, a⟩ in upper do
      r := r.addConstraint (.of
        (combo a x.coeffs (-b) y.coeffs) (Constraint.combo a xc (-b) yc))
        (of_combo_proof a x.coeffs (-b) y.coeffs xc yc xp yp)
  return r

partial def run (p : Problem) : Problem :=
  if p.possible then
    let p' := p.solveEqualities
    if p'.possible then
      if p'.constraints.isEmpty then
        p'
      else
        run (p'.fourierMotzkin)
    else
      p'
  else
    p

#eval Problem.addInequalities {} [([1], 1, none), ([-1], 1, none)]
#eval Problem.addInequalities {} [([1], 1, none), ([-1], 1, none)] |>.solveEqualities
#eval Problem.addInequalities {} [([1], 1, none), ([-1], 1, none)] |>.fourierMotzkinData.size
#eval (Problem.addInequalities {} [([1], 1, none), ([-1], 1, none)]).fourierMotzkinData[0]!.irrelevant.length
#eval (Problem.addInequalities {} [([1], 1, none), ([-1], 1, none)]).fourierMotzkinData[0]!.lowerBounds.length
#eval (Problem.addInequalities {} [([1], 1, none), ([-1], 1, none)]).fourierMotzkinData[0]!.upperBounds.length
#eval Problem.addInequalities {} [([1], 1, none), ([-1], 1, none)] |>.fourierMotzkin


-- example {x y : Nat} (_ : x + y > 10) (_ : x < 5) (_ : y < 5) : False := by omega
#eval Problem.addInequalities {} [([1, 1], -11, none), ([-1], 4, none), ([0, -1], 4, none)]
#eval Problem.addInequalities {} [([1, 1], -11, none), ([-1], 4, none), ([0, -1], 4, none)] |>.solveEqualities
#eval Problem.addInequalities {} [([1, 1], -11, none), ([-1], 4, none), ([0, -1], 4, none)] |>.fourierMotzkinData.size
#eval Problem.addInequalities {} [([1, 1], -11, none), ([-1], 4, none), ([0, -1], 4, none)] |>.fourierMotzkinData[0]!.irrelevant.length
#eval Problem.addInequalities {} [([1, 1], -11, none), ([-1], 4, none), ([0, -1], 4, none)] |>.fourierMotzkinData[0]!.lowerBounds.length
#eval Problem.addInequalities {} [([1, 1], -11, none), ([-1], 4, none), ([0, -1], 4, none)] |>.fourierMotzkinData[0]!.upperBounds.length
#eval Problem.addInequalities {} [([1, 1], -11, none), ([-1], 4, none), ([0, -1], 4, none)] |>.fourierMotzkinData[1]!.irrelevant.length
#eval Problem.addInequalities {} [([1, 1], -11, none), ([-1], 4, none), ([0, -1], 4, none)] |>.fourierMotzkinData[1]!.lowerBounds.length
#eval Problem.addInequalities {} [([1, 1], -11, none), ([-1], 4, none), ([0, -1], 4, none)] |>.fourierMotzkinData[1]!.upperBounds.length
#eval Problem.addInequalities {} [([1, 1], -11, none), ([-1], 4, none), ([0, -1], 4, none)] |>.fourierMotzkin
