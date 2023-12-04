
import Std
import Mathlib.Tactic.Omega.IntList
import Mathlib.Tactic.Omega.OmegaM
import Mathlib.Tactic.Omega.Impl.MinNatAbs
import Mathlib.Tactic.Omega.Impl.bmod
import Qq
import Mathlib.Tactic.DeriveToExpr
import Mathlib.Tactic.LibrarySearch
import Mathlib.Util.Time

-- Try out different data structures (even try an Array!)
-- Cache hashes?
-- Cache GCD
-- Precompute FM data
-- Precompute just enough to choose the target variable for FM
-- Don't actually prepare the FM data until the variable has been chosen
-- A deduplicating cache for constructing the proof
-- Skip unused normalize/positivize steps
-- Reuse output when case splitting
-- More general mechanism for case splitting
-- Precompute data required for `selectEquality`
-- Easier to type check proofs??
-- Avoid metavariables?
-- Cache `maxVar`
-- Use `AssocList` or `HashMap` for coefficients?
-- Reuse variable slots??
-- Precompute target equality

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

@[simp]
def min [Min α] : Option α → Option α → Option α
  | some x, some y => some (Min.min x y)
  | some x, none => some x
  | none, some y => some y
  | none, none => none

@[simp]
def max [Max α] : Option α → Option α → Option α
  | some x, some y => some (Max.max x y)
  | some x, none => some x
  | none, some y => some y
  | none, none => none

end Option

namespace Omega.ProofProducing

abbrev LowerBound : Type := Option Int
abbrev UpperBound : Type := Option Int

abbrev LowerBound.sat (b : LowerBound) (t : Int) := b.all fun x => x ≤ t
abbrev UpperBound.sat (b : UpperBound) (t : Int) := b.all fun y => t ≤ y

structure Constraint where
  lowerBound : LowerBound
  upperBound : UpperBound
deriving BEq, DecidableEq, Repr, Lean.ToExpr

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
  rintro ⟨_ | l, _ | u⟩ v w <;> simp_all [sat, translate, map]
  · exact Int.add_le_add_right w t
  · exact Int.add_le_add_right w t
  · rcases w with ⟨w₁, w₂⟩; constructor
    · exact Int.add_le_add_right w₁ t
    · exact Int.add_le_add_right w₂ t

def flip (c : Constraint) : Constraint where
  lowerBound := c.upperBound
  upperBound := c.lowerBound

def neg (c : Constraint) : Constraint := c.flip.map (- ·)

theorem neg_sat : {c : Constraint} → {v : Int} → sat c v → sat (c.neg) (-v) := by
  rintro ⟨_ | l, _ | u⟩ v w <;> simp_all [sat, neg, flip, map]
  · exact Int.neg_le_neg w
  · exact Int.neg_le_neg w
  · rcases w with ⟨w₁, w₂⟩; constructor
    · exact Int.neg_le_neg w₂
    · exact Int.neg_le_neg w₁

def trivial : Constraint := ⟨none, none⟩
def impossible : Constraint := ⟨some 1, some 0⟩
def exact (r : Int) : Constraint := ⟨some r, some r⟩

@[simp] theorem trivial_say : trivial.sat t := by
  simp [sat, trivial]

@[simp] theorem exact_sat (r : Int) (t : Int) : (exact r).sat t = decide (r = t) := by
  simp only [sat, exact, Option.all_some, decide_eq_true_eq, decide_eq_decide]
  exact Int.eq_iff_le_and_ge.symm

def isImpossible : Constraint → Bool
  | ⟨some x, some y⟩ => y < x
  | _ => false

def isExact : Constraint → Bool
  | ⟨some x, some y⟩ => x = y
  | _ => false

theorem not_sat_of_isImpossible (h : isImpossible c) {t} : ¬ c.sat t := by
  rcases c with ⟨_ | l, _ | u⟩ <;> simp [isImpossible, sat] at h ⊢
  intro w
  rw [Int.not_le]
  exact Int.lt_of_lt_of_le h w

def scale (k : Int) (c : Constraint) : Constraint :=
  if k = 0 then
    if c.isImpossible then c else ⟨some 0, some 0⟩
  else if 0 < k then
    c.map (k * ·)
  else
    c.flip.map (k * ·)

theorem scale_sat {c : Constraint} (k) (w : c.sat t) : (scale k c).sat (k * t) := by
  simp [scale]
  split
  · split
    · simp_all [not_sat_of_isImpossible]
    · simp_all [sat]
  · rcases c with ⟨_ | l, _ | u⟩ <;> split <;> rename_i h <;> simp_all [sat, flip, map]
    · replace h := Int.le_of_lt h
      exact Int.mul_le_mul_of_nonneg_left w h
    · rw [Int.not_lt] at h
      sorry
    · replace h := Int.le_of_lt h
      exact Int.mul_le_mul_of_nonneg_left w h
    · rw [Int.not_lt] at h
      sorry
    · cases w
      constructor
      · sorry
      · sorry
    · cases w
      constructor
      · sorry
      · sorry


def add (x y : Constraint) : Constraint where
  lowerBound := x.lowerBound.bind fun a => y.lowerBound.map fun b => a + b
  upperBound := x.upperBound.bind fun a => y.upperBound.map fun b => a + b

theorem add_sat (w₁ : c₁.sat x₁) (w₂ : c₂.sat x₂) : (add c₁ c₂).sat (x₁ + x₂) := by
  rcases c₁ with ⟨_ | l₁, _ | u₁⟩ <;> rcases c₂ with ⟨_ | l₂, _ | u₂⟩
    <;> simp [sat, LowerBound.sat, UpperBound.sat, add] at *
  · exact Int.add_le_add w₁ w₂
  · exact Int.add_le_add w₁ w₂.2
  · exact Int.add_le_add w₁ w₂
  · exact Int.add_le_add w₁ w₂.1
  · exact Int.add_le_add w₁.2 w₂
  · exact Int.add_le_add w₁.1 w₂
  · constructor
    · exact Int.add_le_add w₁.1 w₂.1
    · exact Int.add_le_add w₁.2 w₂.2

def combo (a : Int) (x : Constraint) (b : Int) (y : Constraint) : Constraint :=
  add (scale a x) (scale b y)

def combo_sat (a) (w₁ : c₁.sat x₁) (b) (w₂ : c₂.sat x₂) : (combo a c₁ b c₂).sat (a * x₁ + b * x₂) :=
  add_sat (scale_sat a w₁) (scale_sat b w₂)

def combine (x y : Constraint) : Constraint where
  lowerBound := Option.max x.lowerBound y.lowerBound
  upperBound := Option.min x.upperBound y.upperBound

theorem combine_sat : (c : Constraint) → (c' : Constraint) → (t : Int) →
    (c.combine c').sat t = (c.sat t ∧ c'.sat t) := by
  rintro ⟨_ | l₁, _ | u₁⟩ <;> rintro ⟨_ | l₂, _ | u₂⟩ t
    <;> simp [sat, LowerBound.sat, UpperBound.sat, combine, Int.le_min, Int.max_le] at *
  · rw [And.comm]
  · rw [← and_assoc, And.comm (a := l₂ ≤ t), and_assoc]
  · rw [and_assoc]
  · rw [and_assoc]
  · rw [and_assoc, and_assoc, And.comm (a := l₂ ≤ t)]
  · rw [and_assoc, ← and_assoc (a := l₂ ≤ t), And.comm (a := l₂ ≤ t), and_assoc, and_assoc]

def div (c : Constraint) (k : Nat) : Constraint where
  lowerBound := c.lowerBound.map fun x => (- ((- x) / k))
  upperBound := c.upperBound.map fun y => y / k

-- theorem div_sat (c : Constraint) (k : Nat) (t : Int) (h : (c.div k).sat t) : c.sat (t * k) := by
--   rcases c with ⟨_ | l, _ | u⟩
--   · simp_all [sat, div]
--   · simp_all [sat, div]
--     sorry
--   · simp_all [sat, div]
--     sorry
--   · simp_all [sat, div]
--     sorry

theorem div_sat (c : Constraint) (t : Int) (k : Nat) (h : (k : Int) ∣ t) (w : c.sat t) :
    (c.div k).sat (t / k) := by
  rcases c with ⟨_ | l, _ | u⟩
  · simp_all [sat, div]
  · simp_all [sat, div]
    apply Int.le_of_sub_nonneg
    replace w := Int.sub_nonneg_of_le w
    rw [← Int.sub_ediv_of_dvd _ h]
    rw [Int.le_iff_ge]
    rw [Int.div_nonneg_iff_of_pos] -- This seems to be all we have available!
    suffices p : t / k * k ≤ u / k * k by
      apply Int.mul_le_of
    have := Int.ediv_le
    sorry
  · simp_all [sat, div]
    sorry
  · simp_all [sat, div]
    sorry
#exit
abbrev sat' (c : Constraint) (x y : List Int) := c.sat (IntList.dot x y)

theorem combine_sat' {s t : Constraint} {x y} (ws : s.sat' x y) (wt : t.sat' x y) :
    (s.combine t).sat' x y := (combine_sat _ _ _).mpr ⟨ws, wt⟩

theorem div_sat' {c : Constraint} {x y} (w : c.sat (IntList.dot x y)) :
    (c.div (IntList.gcd x)).sat' (IntList.sdiv x (IntList.gcd x)) y := by
  dsimp [sat']
  rw [IntList.dot_sdiv_left _ _ (Int.dvd_refl _)]
  exact div_sat c _ (IntList.gcd x) (IntList.gcd_dvd_dot_left x y) w

theorem not_sat'_of_isImpossible (h : isImpossible c) {x y} : ¬ c.sat' x y :=
  not_sat_of_isImpossible h

end Constraint

structure Coefficients where
  coeffs : List Int
  -- spec: first nonzero entry is nonnegative, and no trailing zeroes?
  gcd : Nat := IntList.gcd coeffs
  -- gcd_spec

  -- TODO cache the hash
  hash : UInt64 := Hashable.hash coeffs

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

def normalize? : Constraint × List Int → Option (Constraint × List Int)
  | ⟨s, x⟩ =>
    let gcd := IntList.gcd x -- TODO should we be caching this?
    if gcd = 0 then
      if s.sat 0 then
        some (.trivial, x)
      else
        some (.impossible, x)
    else if gcd = 1 then
      none
    else
      some (s.div gcd, IntList.sdiv x gcd)

def normalize (p : Constraint × List Int) : Constraint × List Int :=
  normalize? p |>.getD p

abbrev normalizeConstraint (s : Constraint) (x : List Int) : Constraint := (normalize (s, x)).1
abbrev normalizeCoeffs (s : Constraint) (x : List Int) : List Int := (normalize (s, x)).2

theorem normalize?_eq_some (w : normalize? (s, x) = some (s', x')) :
    normalizeConstraint s x = s' ∧ normalizeCoeffs s x = x' := by
  simp_all [normalizeConstraint, normalizeCoeffs, normalize]

theorem normalize_sat {s x v} (w : s.sat' x v) :
    (normalizeConstraint s x).sat' (normalizeCoeffs s x) v := by
  dsimp [normalizeConstraint, normalizeCoeffs, normalize, normalize?]
  split
  · split
    · simp
    · dsimp [Constraint.sat'] at w
      simp_all
  · split
    · exact w
    · exact Constraint.div_sat' w

def positivize? : Constraint × List Int → Option (Constraint × List Int)
  | ⟨s, x⟩ =>
    if 0 ≤ (x.find? (! · == 0) |>.getD 0) then
      none
    else
      (s.neg, IntList.smul x (-1) )

def positivize (p : Constraint × List Int) : Constraint × List Int :=
  positivize? p |>.getD p

abbrev positivizeConstraint (s : Constraint) (x : List Int) : Constraint := (positivize (s, x)).1
abbrev positivizeCoeffs (s : Constraint) (x : List Int) : List Int := (positivize (s, x)).2

theorem positivize?_eq_some (w : positivize? (s, x) = some (s', x')) :
    positivizeConstraint s x = s' ∧ positivizeCoeffs s x = x' := by
  simp_all [positivizeConstraint, positivizeCoeffs, positivize]

theorem positivize_sat {s x v} (w : s.sat' x v) :
    (positivizeConstraint s x).sat' (positivizeCoeffs s x) v := by
  dsimp [positivizeConstraint, positivizeCoeffs, positivize, positivize?]
  split
  · exact w
  · simp [Constraint.sat']
    erw [IntList.dot_smul_left, ← Int.neg_eq_neg_one_mul]
    exact Constraint.neg_sat w

theorem trim_sat {s : Constraint} {x v} (w : s.sat' x v) : s.sat' (IntList.trim x) v := by
  dsimp [Constraint.sat']
  rw [IntList.dot_trim_left]
  exact w

def tidy? : Constraint × List Int → Option (Constraint × List Int)
  | ⟨s, x⟩ =>
    match IntList.trim? x with
    | none => match positivize? (s, x) with
      | none => match normalize? (s, x) with
        | none => none
        | some (s', x') => some (s', x')
      | some (s', x') => normalize (s', x')
    | some x' => normalize (positivize (s, x'))

def tidy (p : Constraint × List Int) : Constraint × List Int :=
  tidy? p |>.getD p

abbrev tidyConstraint (s : Constraint) (x : List Int) : Constraint := (tidy (s, x)).1
abbrev tidyCoeffs (s : Constraint) (x : List Int) : List Int := (tidy (s, x)).2

theorem tidy_sat {s x v} (w : s.sat' x v) : (tidyConstraint s x).sat' (tidyCoeffs s x) v := by
  dsimp [tidyConstraint, tidyCoeffs, tidy, tidy?]
  split <;> rename_i ht
  · split <;> rename_i hp
    · split <;> rename_i hn
      · simp_all
      · rcases normalize?_eq_some hn with ⟨rfl, rfl⟩
        exact normalize_sat w
    · rcases positivize?_eq_some hp with ⟨rfl, rfl⟩
      exact normalize_sat (positivize_sat w)
  · rcases IntList.trim?_eq_some ht with rfl
    exact normalize_sat (positivize_sat (trim_sat w))

theorem combo_sat' (s t : Constraint)
    (a : Int) (x : List Int) (b : Int) (y : List Int) (v : List Int)
    (wx : s.sat' x v) (wy : t.sat' y v) :
    (Constraint.combo a s b t).sat' (IntList.combo a x b y) v := by
  rw [Constraint.sat', IntList.combo_eq_smul_add_smul, IntList.dot_distrib_left,
    IntList.dot_smul_left, IntList.dot_smul_left]
  exact Constraint.combo_sat a wx b wy

abbrev IntList.bmod (x : List Int) (m : Nat) : List Int := x.map (Int.bmod · m)

theorem IntList.bmod_length (m) : (IntList.bmod x m).length = x.length := List.length_map _ _

def bmod_coeffs (m : Nat) (i : Nat) (x : List Int) : List Int :=
  IntList.set (IntList.bmod x m) i m

abbrev bmod_sub_term (m : Nat) (a b : List Int) : Int :=
    (Int.bmod (IntList.dot a b) m) - IntList.dot (IntList.bmod a m) b

theorem bmod_sat_aux (m : Nat) (xs ys : List Int) : (m : Int) ∣ bmod_sub_term m xs ys := by
  dsimp [bmod_sub_term]
  rw [Int.dvd_iff_emod_eq_zero]
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      simp only [IntList.dot_cons₂, List.map_cons]
      specialize ih ys
      rw [Int.sub_emod, Int.bmod_emod] at ih
      rw [Int.sub_emod, Int.bmod_emod, Int.add_emod, Int.add_emod (Int.bmod x m * y),
        ← Int.sub_emod, ← Int.sub_sub, Int.sub_eq_add_neg, Int.sub_eq_add_neg,
        Int.add_assoc (x * y % m), Int.add_comm (IntList.dot _ _ % m), ← Int.add_assoc,
        Int.add_assoc, ← Int.sub_eq_add_neg, ← Int.sub_eq_add_neg, Int.add_emod, ih, Int.add_zero,
        Int.emod_emod, Int.mul_emod, Int.mul_emod (Int.bmod x m), Int.bmod_emod, Int.sub_self,
        Int.zero_emod]

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
  -- This only makes sense when `s = .exact r`, but there is no point in enforcing that here:
| bmod (m : Nat) (r : Int) (i : Nat) {x} {s} (j : Justification s x) : Justification (.exact (Int.bmod r m)) (bmod_coeffs m i x)


def _root_.String.bullet (s : String) := "• " ++ s.replace "\n" "\n  "
namespace Justification

-- TODO deduplicate??

def toString : Justification s x → String
| assumption _ _ i => s!"{x} ∈ {s}: assumption {i}"
| @normalize s' x' j => if s = s' ∧ x = x' then j.toString else s!"{x} ∈ {s}: normalization of:\n" ++ j.toString.bullet
| @positivize s' x' j => if s = s' ∧ x = x' then j.toString else s!"{x} ∈ {s}: positivization of:\n" ++ j.toString.bullet
| combine j k => s!"{x} ∈ {s}: combination of:\n" ++ j.toString.bullet ++ "\n" ++ k.toString.bullet
| combo a j b k => s!"{x} ∈ {s}: {a} * x + {b} * y combo of:\n" ++ j.toString.bullet ++ "\n" ++ k.toString.bullet
| bmod m _ i j => s!"{x} ∈ {s}: bmod with m={m} and i={i} of:\n" ++ j.toString.bullet

instance : ToString (Justification s x) where toString := toString

open Lean

def normalizeProof (s : Constraint) (x : List Int) (v : Expr) (prf : Expr) : Expr :=
  mkApp4 (.const ``normalize_sat []) (toExpr s) (toExpr x) v prf

def positivizeProof (s : Constraint) (x : List Int) (v : Expr) (prf : Expr) : Expr :=
  mkApp4 (.const ``positivize_sat []) (toExpr s) (toExpr x) v prf

def combineProof (s t : Constraint) (x : List Int) (v : Expr) (ps pt : Expr) : Expr :=
  mkApp6 (.const ``Constraint.combine_sat' []) (toExpr s) (toExpr t) (toExpr x) v ps pt

def comboProof (s t : Constraint) (a : Int) (x : List Int) (b : Int) (y : List Int)
    (v : Expr) (px py : Expr) : Expr :=
  mkApp9 (.const ``combo_sat' []) (toExpr s) (toExpr t) (toExpr a) (toExpr x) (toExpr b) (toExpr y)
    v px py

/-- Construct the term with type hint `(Eq.refl a : a = b)`-/
def mkEqReflWithExpectedType (a b : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)


def takeListLit : Nat → Level → Expr → Expr → Expr
  | 0, u, ty, _ => mkApp (.const ``List.nil [u]) ty
  | (k + 1), u, ty, e =>
    match e.getAppFnArgs with
    | (``List.cons, #[_, h, t]) => mkApp3 (.const ``List.cons [u]) ty h (takeListLit k u ty t)
    | _ => mkApp (.const ``List.nil [u]) ty


open Qq in
def bmodProof (m : Nat) (r : Int) (i : Nat) (x : List Int) (v : Expr) (w : Expr) : MetaM Expr := do
  let v' := takeListLit x.length .zero (.const ``Int []) v
  let m := toExpr m
  let r := toExpr r
  let i := toExpr i
  let x := toExpr x
  let h ← mkDecideProof q(List.length $x ≤ $i)
  -- TODO Clean up
  let lhs := mkApp2 (.const ``IntList.get []) v i
  let rhs := mkApp3 (.const ``bmod_div_term []) m x v'
  _ ← isDefEq lhs rhs
  let p ← mkEqReflWithExpectedType lhs rhs
  return mkApp8 (.const ``bmod_sat []) m r i x v h p w

-- TODO deduplicate: don't prove the same thing twice in different branches

/-- Constructs a proof that `s.sat' c v = true` -/
def proof (v : Expr) (assumptions : Array Proof) : Justification s c → Proof
| assumption s c i => assumptions[i]!
| @normalize s c j => return normalizeProof s c v (← proof v assumptions j)
| @positivize s c j => return positivizeProof s c v (← proof v assumptions j)
| @combine s t c j k => return combineProof s t c v (← proof v assumptions j) (← proof v assumptions k)
| @combo s t x y a j b k => return comboProof s t a x b y v (← proof v assumptions j) (← proof v assumptions k)
| @bmod m r i x s j => do bmodProof m r i x v (← proof v assumptions j)

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

  explanation? : Option String := none

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
        explanation? := some j.toString
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

theorem addInequality_sat (w : c + IntList.dot x y ≥ 0) :
    ({ lowerBound := some (-c), upperBound := none } : Constraint).sat' x y := by
  simp [Constraint.sat', Constraint.sat]
  rw [← Int.zero_sub c]
  exact Int.sub_left_le_of_le_add w

open Lean in
def addInequality_proof (c : Int) (x : List Int) (p : Proof) : Proof := do
  return mkApp4 (.const ``addInequality_sat []) (toExpr c) (toExpr x) (← atomsList) (← p)

theorem Int.add_le_iff_le_sub (a b c : Int) : a + b ≤ c ↔ a ≤ c - b := by
  conv =>
    lhs
    rw [← Int.add_zero c, ← Int.sub_self (-b), Int.sub_eq_add_neg, ← Int.add_assoc, Int.neg_neg,
      Int.add_le_add_iff_right]

theorem Int.le_add_iff_sub_le (a b c : Int) : a ≤ b + c ↔ a - c ≤ b := by
  conv =>
    lhs
    rw [← Int.neg_neg c, ← Int.sub_eq_add_neg, ← add_le_iff_le_sub]

theorem Int.add_le_zero_iff_le_neg (a b : Int) : a + b ≤ 0 ↔ a ≤ - b := by
  rw [add_le_iff_le_sub, Int.zero_sub]
theorem Int.add_le_zero_iff_le_neg' (a b : Int) : a + b ≤ 0 ↔ b ≤ -a := by
  rw [Int.add_comm, Int.add_le_zero_iff_le_neg]
theorem Int.add_nonnneg_iff_neg_le (a b : Int) : 0 ≤ a + b ↔ -b ≤ a := by
  rw [le_add_iff_sub_le, Int.zero_sub]
theorem Int.add_nonnneg_iff_neg_le' (a b : Int) : 0 ≤ a + b ↔ -a ≤ b := by
  rw [Int.add_comm, Int.add_nonnneg_iff_neg_le]

theorem addEquality_sat (w : c + IntList.dot x y = 0) :
    ({ lowerBound := some (-c), upperBound := some (-c) } : Constraint).sat' x y := by
  simp [Constraint.sat', Constraint.sat]
  rw [Int.eq_iff_le_and_ge] at w
  rwa [Int.add_le_zero_iff_le_neg', Int.add_nonnneg_iff_neg_le', and_comm] at w

open Lean in
def addEquality_proof (c : Int) (x : List Int) (p : Proof) : Proof := do
  return mkApp4 (.const ``addEquality_sat []) (toExpr c) (toExpr x) (← atomsList) (← p)

-- prf? : const + IntList.dot coeffs atoms ≥ 0
-- But we need to transform this to `IntList.dot coeffs atoms ≥ -const` i.e.
def addInequality (p : Problem) (const : Int) (coeffs : List Int) (prf? : Option Proof) : Problem :=
    let prf := prf?.getD (do mkSorry (← mkFreshExprMVar none) false)
    let i := p.assumptions.size
    let p' := { p with assumptions := p.assumptions.push (addInequality_proof const coeffs prf) }
    let f : Fact :=
    { coeffs
      constraint := { lowerBound := some (-const), upperBound := none }
      justification := .assumption _ _ i }
    p'.addConstraint f.positivize.normalize

def addEquality (p : Problem) (const : Int) (coeffs : List Int) (prf? : Option Proof) : Problem :=
    let prf := prf?.getD (do mkSorry (← mkFreshExprMVar none) false)
    let i := p.assumptions.size
    let p' := { p with assumptions := p.assumptions.push (addEquality_proof const coeffs prf) }
    let f : Fact :=
    { coeffs
      constraint := { lowerBound := some (-const), upperBound := some (-const) }
      justification := .assumption _ _ i }
    p'.addConstraint f.positivize.normalize

def addInequalities (p : Problem) (ineqs : List (Int × List Int × Option Proof)) : Problem :=
  ineqs.foldl (init := p) fun p ⟨const, coeffs, prf?⟩ => p.addInequality const coeffs prf?

def addEqualities (p : Problem) (eqs : List (Int × List Int × Option Proof)) : Problem :=
  eqs.foldl (init := p) fun p ⟨const, coeffs, prf?⟩ => p.addEquality const coeffs prf?

/-- info: impossible -/
#guard_msgs in
#eval Problem.addInequalities {} [(-2, [], none)]

/-- info: [1, 1] ∈ [-1, 1] -/
#guard_msgs in
#eval Problem.addInequalities {} [(1, [1, 1], none), (1, [-1, -1], none)]

/-- info: [1] ∈ {1} -/
#guard_msgs in
#eval Problem.addInequalities {} [(-2, [2], none), (2, [-2], none)]

/-- info: impossible -/
#guard_msgs in
#eval Problem.addInequalities {} [(-1, [2], none), (1, [-2], none)]

/-- info: [1] ∈ {1} -/
#guard_msgs in
#eval Problem.addEqualities {} [(-2, [2], none)]

/-- info: impossible -/
#guard_msgs in
#eval Problem.addEqualities {} [(-1, [2], none)]

def selectEquality (p : Problem) : Option (List Int) :=
  p.equalities.foldl (init := none) fun
  | none, c => c
  | some r, c => if 2 ≤ r.minNatAbs && (c.minNatAbs < r.minNatAbs || c.minNatAbs = r.minNatAbs && c.maxNatAbs < r.maxNatAbs) then c else r

def solveEasyEquality (p : Problem) (c : List Int) : Problem :=
  let i := c.findIdx? (·.natAbs = 1) |>.getD 0 -- findIdx? is always some
  let sign := c.get? i |>.getD 0 |> Int.sign
  match p.constraints.find? c with
  | some f =>
    -- TODO Lame that we are copying around assumptions here:
    p.constraints.foldl (init := { assumptions := p.assumptions }) fun p' coeffs g =>
      match coeffs.get? i |>.getD 0 with
      | 0 =>
        p'.addConstraint g
      | ci =>
        let k := -1 * sign * ci
        p'.addConstraint (Fact.combo k f 1 g).positivize.normalize
  | _ => p -- unreachable

/-- info: trivial -/
#guard_msgs in
#eval Problem.addEqualities {} [(-2, [2], none)] |>.solveEasyEquality [1]

/-- info: [0, 1, 2] ∈ {-10} -/
#guard_msgs in
#eval Problem.addEqualities {} [(-2, [1,2,3], none), (-38, [4,5,6], none)] |>.solveEasyEquality [1,2,3]

-- TODO probably should just cache the active variables, or this number
def maxVar (p : Problem) : Nat := p.constraints.foldl (init := 0) fun l c _ => max l c.length
-- we could use mex here:
def freshVar (p : Problem) : Nat := p.maxVar

/--
We deal with a hard equality by introducing a new easy equality.

After solving the easy equality,
the minimum lexicographic value of `(c.minNatAbs, c.maxNatAbs)` will have been reduced.
-/
def dealWithHardEquality (p : Problem) (c : List Int) : Problem :=
  let m := c.minNatAbs + 1
  let i := p.freshVar
  match p.constraints.find? c with
  | some ⟨_, ⟨some r, _⟩, j⟩ =>
    p.addConstraint { coeffs := _, constraint := _, justification := j.bmod m r i }
  | _ =>
    p -- unreachable

def solveEquality (p : Problem) (c : List Int) : Problem :=
  if c.minNatAbs = 1 then
    p.solveEasyEquality c
  else
    p.dealWithHardEquality c

partial def solveEqualities (p : Problem) : Problem :=
  if p.possible then
    match p.selectEquality with
    | some c => (p.solveEquality c).solveEqualities
    | none => p
  else p

/-- info: [0, 0, 1] ∈ [-22, ∞) -/
#guard_msgs in
#eval Problem.addEqualities {} [(-2, [1,2,3], none), (-38, [4,5,6], none)]
  |>.addInequalities [(0, [1,0,0], none)]
  |>.solveEqualities


def ex1 : Problem := Problem.addEqualities {}
    [(17, [7, 12, 31], none), (7, [3, 5, 24], none)]

def ex1_1 : Problem := ex1.addInequalities [(-1000, [1], none)]
def ex1_2 : Problem := ex1.addInequalities [(-1000, [0,1], none)]
def ex1_3 : Problem := ex1.addInequalities [(8, [0,0,1], none)]
def ex1_all : Problem := ex1.addInequalities [(-1000, [1], none), (-1000, [0,1], none), (8, [0,0,1], none)]

/-- info: [0, 0, 1, 0, 0] ∈ (-∞, -8] -/
#guard_msgs in
#eval ex1_1.solveEqualities
/-- info: [0, 0, 1, 0, 0] ∈ [14, ∞) -/
#guard_msgs in
#eval ex1_2.solveEqualities
/-- info: [0, 0, 1] ∈ [-8, ∞) -/
#guard_msgs in
#eval ex1_3.solveEqualities
/-- info: impossible -/
#guard_msgs in
#eval ex1_all.solveEqualities


structure FourierMotzkinData where
  irrelevant : List Fact := []
  lowerBounds : List (Fact × Int) := []
  upperBounds : List (Fact × Int) := []
  lowerExact : Bool := true
  upperExact : Bool := true
deriving Inhabited

def FourierMotzkinData.isEmpty (d : FourierMotzkinData) : Bool :=
  d.lowerBounds.isEmpty && d.upperBounds.isEmpty
def FourierMotzkinData.size (d : FourierMotzkinData) : Nat := d.lowerBounds.length * d.upperBounds.length
def FourierMotzkinData.exact (d : FourierMotzkinData) : Bool := d.lowerExact || d.upperExact

def fourierMotzkinData (p : Problem) : Array FourierMotzkinData := Id.run do
  -- For each variable, prepare the irrelevant constraints, lower and upper bounds,
  -- and whether the elimination would be exact.
  -- TODO Does it make sense to precompute some or all of this?
  let n := p.maxVar
  -- What is `Array.replicate` called?
  let mut data : Array FourierMotzkinData := Array.mk (List.replicate p.maxVar {})
  for (_, f@⟨xs, s, _⟩) in p.constraints do
    for i in [0:n] do
      let x := IntList.get xs i
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
  let mut r : Problem := { assumptions := p.assumptions }
  for f in irrelevant do
    r := r.insertConstraint f
  for ⟨f, b⟩ in lower do
    for ⟨g, a⟩ in upper do
      r := r.addConstraint (Fact.combo a f (-b) g).positivize.normalize
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

/-- info: [1] ∈ [-1, 1] -/
#guard_msgs in
#eval Problem.addInequalities {} [(1, [1], none), (1, [-1], none)]
/-- info: trivial -/
#guard_msgs in
#eval Problem.addInequalities {} [(1, [1], none), (1, [-1], none)] |>.fourierMotzkin

-- example {x y : Nat} (_ : x + y > 10) (_ : x < 5) (_ : y < 5) : False := by omega
/--
info: [1, 1] ∈ [11, ∞)
[1] ∈ (-∞, 4]
[0, 1] ∈ (-∞, 4]
-/
#guard_msgs in
#eval Problem.addInequalities {} [(-11, [1, 1], none), (4, [-1], none), (4, [0, -1], none)]
/-- info: impossible -/
#guard_msgs in
#eval Problem.addInequalities {} [(-11, [1, 1], none), (4, [-1], none), (4, [0, -1], none)] |>.fourierMotzkin

-- def P := Problem.addEqualities {} [(0, [1], none), (0, [1, -1, 1], none)]
--   |>.addInequalities [(-1, [0, 1, -1], none), (0, [0, 1], none), (0, [0, 0, 1], none)]

-- #eval P
-- #eval P.selectEquality
-- #eval P.solveEquality P.selectEquality.get!
-- #eval P.solveEquality P.selectEquality.get! |>.selectEquality
-- #eval P.solveEqualities

-- example {a b c : Int} (_ : a = 0) (_ : b - c ≥ 1) (_ : b ≥ 0) (_ : c ≥ 0)
--   (_ : a - b + c = 0) : False := by omega
