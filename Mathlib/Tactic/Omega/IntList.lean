import Mathlib.Tactic.Omega.ForStd
-- import Mathlib.Tactic.Rewrites

set_option autoImplicit true
set_option relaxedAutoImplicit true

abbrev IntList := List Int

namespace IntList

/-- Get the `i`-th element (interpreted as `0` if the list is not long enough). -/
def get (xs : IntList) (i : Nat) : Int := (xs.get? i).getD 0

@[simp] theorem get_nil : get ([] : IntList) i = 0 := rfl
@[simp] theorem get_cons_zero : get (x :: xs) 0 = x := rfl
@[simp] theorem get_cons_succ : get (x :: xs) (i+1) = get xs i := rfl

theorem get_map {xs : IntList} (h : f 0 = 0) : get (xs.map f) i = f (xs.get i) := by
  simp only [get, List.get?_map]
  cases xs.get? i <;> simp_all

theorem get_of_length_le {xs : IntList} (h : xs.length ≤ i) : xs.get i = 0 := by
  rw [get, List.get?_eq_none.mpr h]
  rfl

theorem lt_length_of_get_nonzero {xs : IntList} (h : xs.get i ≠ 0) : i < xs.length := by
  revert h
  simpa using mt get_of_length_le

/-- Like `List.set`, but right-pad with zeroes as necessary first. -/
def set (xs : IntList) (i : Nat) (y : Int) : IntList :=
  match xs, i with
  | [], 0 => [y]
  | [], (i+1) => 0 :: set [] i y
  | _ :: xs, 0 => y :: xs
  | x :: xs, (i+1) => x :: set xs i y

@[simp] theorem set_nil_zero : set [] 0 y = [y] := rfl
@[simp] theorem set_nil_succ : set [] (i+1) y = 0 :: set [] i y := rfl
@[simp] theorem set_cons_zero : set (x :: xs) 0 y = y :: xs := rfl
@[simp] theorem set_cons_succ : set (x :: xs) (i+1) y = x :: set xs i y := rfl

theorem set_get_eq : get (set xs i y) j = if i = j then y else xs.get j := by
  induction xs generalizing i j with
  | nil =>
    induction i generalizing j with
    | zero => cases j <;> simp [set]
    | succ i => cases j <;> simp_all [set]
  | cons x xs ih =>
    induction i with
    | zero => cases j <;> simp [set]
    | succ i => cases j <;> simp_all [set]

@[simp] theorem set_get_self : get (set xs i y) i = y := by simp [set_get_eq]
@[simp] theorem set_get_of_ne (h : i ≠ j) : get (set xs i y) j = xs.get j := by simp [set_get_eq, h]

def add (xs ys : IntList) : IntList :=
  List.zipWithAll (fun x y => x.getD 0 + y.getD 0) xs ys

instance : Add IntList := ⟨add⟩

theorem add_def (xs ys : IntList) :
    xs + ys = List.zipWithAll (fun x y => x.getD 0 + y.getD 0) xs ys :=
  rfl

@[simp] theorem add_get (xs ys : IntList) (i : Nat) : (xs + ys).get i = xs.get i + ys.get i := by
  simp only [add_def, get, List.zipWithAll_get?, List.get?_eq_none]
  cases xs.get? i <;> cases ys.get? i <;> simp

def mul (xs ys : IntList) : IntList := List.zipWith (· * ·) xs ys

instance : Mul IntList := ⟨mul⟩

theorem mul_def (xs ys : IntList) : xs * ys = List.zipWith (· * ·) xs ys :=
  rfl

@[simp] theorem mul_get (xs ys : IntList) (i : Nat) : (xs * ys).get i = xs.get i * ys.get i := by
  simp only [mul_def, get, List.zipWith_get?]
  cases xs.get? i <;> cases ys.get? i <;> simp

@[simp] theorem mul_nil_left : ([] : IntList) * ys = [] := rfl
@[simp] theorem mul_nil_right : xs * ([] : IntList) = [] := List.zipWith_nil_right
@[simp] theorem mul_cons₂ : (x::xs : IntList) * (y::ys) = (x * y) :: (xs * ys) := rfl

def neg (xs : IntList) : IntList := xs.map fun x => -x

instance : Neg IntList := ⟨neg⟩

theorem neg_def (xs : IntList) : - xs = xs.map fun x => -x := rfl

@[simp] theorem neg_get (xs : IntList) (i : Nat) : (- xs).get i = - xs.get i := by
  simp only [neg_def, get, List.get?_map]
  cases xs.get? i <;> simp

@[simp] theorem neg_nil : (- ([] : IntList)) = [] := rfl
@[simp] theorem neg_cons : (- (x::xs : IntList)) = -x :: -xs := rfl

def sub (xs ys : IntList) : IntList :=
  List.zipWithAll (fun x y => x.getD 0 - y.getD 0) xs ys

instance : Sub IntList := ⟨sub⟩

theorem sub_def (xs ys : IntList) :
    xs - ys = List.zipWithAll (fun x y => x.getD 0 - y.getD 0) xs ys :=
  rfl

def smul (xs : IntList) (i : Int) : IntList :=
  xs.map fun x => i * x

instance : HMul Int IntList IntList where
  hMul i xs := xs.smul i

theorem smul_def (xs : IntList) (i : Int) : i * xs = xs.map fun x => i * x := rfl

@[simp] theorem smul_get (xs : IntList) (a : Int) (i : Nat) : (a * xs).get i = a * xs.get i := by
  simp only [smul_def, get, List.get?_map]
  cases xs.get? i <;> simp

@[simp] theorem smul_nil {i : Int} : i * ([] : IntList) = [] := rfl
@[simp] theorem smul_cons {i : Int} : i * (x::xs : IntList) = i * x :: i * xs := rfl

theorem mul_comm (xs ys : IntList) : xs * ys = ys * xs := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih => cases ys <;> simp_all [Int.mul_comm]

@[simp] theorem neg_neg {xs : IntList} : - - xs = xs := by
  induction xs <;> simp_all

attribute [local simp] add_def mul_def in
theorem mul_distrib_left (xs ys zs : IntList) : (xs + ys) * zs = xs * zs + ys * zs := by
  induction xs generalizing ys zs with
  | nil =>
    cases ys with
    | nil => simp
    | cons _ _ =>
      cases zs with
      | nil => simp
      | cons _ _ => simp_all [Int.add_mul]
  | cons x xs ih₁ =>
    cases ys with
    | nil => simp_all
    | cons _ _ =>
      cases zs with
      | nil => simp
      | cons _ _ => simp_all [Int.add_mul]

theorem mul_neg_left (xs ys : IntList) : (-xs) * ys = -(xs * ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => simp_all [Int.neg_mul]

attribute [local simp] add_def neg_def sub_def in
theorem sub_eq_add_neg (xs ys : IntList) : xs - ys = xs + (-ys) := by
  induction xs generalizing ys with
  | nil => simp; rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => simp_all [Int.sub_eq_add_neg]

@[simp] theorem sub_get (xs ys : IntList) (i : Nat) : (xs - ys).get i = xs.get i - ys.get i := by
  rw [sub_eq_add_neg, add_get, neg_get, ← Int.sub_eq_add_neg]

@[simp] theorem mul_smul_left {i : Int} {xs ys : IntList} : (i * xs) * ys = i * (xs * ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => simp_all [Int.mul_assoc]

def sum (xs : IntList) : Int := xs.foldr (· + ·) 0

@[simp] theorem sum_nil : sum ([] : IntList) = 0 := rfl
@[simp] theorem sum_cons : sum (x::xs : IntList) = x + sum xs := rfl

attribute [local simp] sum add_def in
theorem sum_add (xs ys : IntList) : (xs + ys).sum = xs.sum + ys.sum := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => simp_all [Int.add_assoc, Int.add_left_comm]

@[simp]
theorem sum_neg (xs : IntList) : (-xs).sum = -(xs.sum) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp_all [Int.neg_add]

@[simp]
theorem sum_smul (i : Int) (xs : IntList) : (i * xs).sum = i * (xs.sum) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp_all [Int.mul_add]

def dot (xs ys : IntList) : Int := (xs * ys).sum

@[simp] theorem dot_nil_left : dot ([] : IntList) ys = 0 := rfl
@[simp] theorem dot_nil_right : dot xs ([] : IntList) = 0 := by simp [dot]
@[simp] theorem dot_cons₂ : dot (x::xs) (y::ys) = x * y + dot xs ys := rfl

theorem dot_comm (xs ys : IntList) : dot xs ys = dot ys xs := by
  rw [dot, dot, mul_comm]

@[simp] theorem dot_set_left (xs ys : IntList) (i : Nat) (z : Int) :
    dot (xs.set i z) ys = dot xs ys + (z - xs.get i) * ys.get i := by
  induction xs generalizing i ys with
  | nil =>
    induction i generalizing ys with
    | zero => cases ys <;> simp
    | succ i => cases ys <;> simp_all
  | cons x xs ih =>
    induction i generalizing ys with
    | zero =>
      cases ys with
      | nil => simp
      | cons y ys =>
        simp only [Nat.zero_eq, set_cons_zero, dot_cons₂, get_cons_zero, Int.sub_mul]
        rw [Int.add_right_comm, Int.add_comm (x * y), Int.sub_add_cancel]
    | succ i =>
      cases ys with
      | nil => simp
      | cons y ys => simp_all [Int.add_assoc]

@[simp] theorem dot_set_right (xs ys : IntList) (i : Nat) (z : Int) :
    dot xs (ys.set i z) = dot xs ys + xs.get i * (z - ys.get i) := by
  rw [dot_comm, dot_set_left, dot_comm, Int.mul_comm]

theorem dot_distrib_left (xs ys zs : IntList) : (xs + ys).dot zs = xs.dot zs + ys.dot zs := by
  simp [dot, mul_distrib_left, sum_add]

@[simp] theorem dot_neg_left (xs ys : IntList) : (-xs).dot ys = -(xs.dot ys) := by
  simp [dot, mul_neg_left]

@[simp] theorem dot_smul_left (xs ys : IntList) (i : Int) : (i * xs).dot ys = i * xs.dot ys := by
  simp [dot]

theorem dot_sub_left (xs ys zs : IntList) : (xs - ys).dot zs = xs.dot zs - ys.dot zs := by
  rw [sub_eq_add_neg, dot_distrib_left, dot_neg_left, ← Int.sub_eq_add_neg]

theorem dot_of_left_zero (w : ∀ x, x ∈ xs → x = 0) : dot xs ys = 0 := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      rw [dot_cons₂, w x (by simp), ih]
      · simp
      · intro x m
        apply w
        exact List.mem_cons_of_mem _ m

theorem dvd_dot_of_dvd_left (w : ∀ x, x ∈ xs → m ∣ x) : m ∣ dot xs ys := by
  induction xs generalizing ys with
  | nil => exact Int.dvd_zero m
  | cons x xs ih =>
    cases ys with
    | nil => exact Int.dvd_zero m
    | cons y ys =>
      rw [dot_cons₂]
      apply Int.dvd_add
      · apply Int.dvd_trans
        rotate_left
        · apply Int.dvd_mul_right
        · apply w
          apply List.mem_cons_self
      · apply ih
        intro x m
        apply w x
        apply List.mem_cons_of_mem _ m

def sdiv (xs : IntList) (g : Int) : IntList := xs.map fun x => x / g

@[simp] theorem sdiv_nil : sdiv [] g = [] := rfl
@[simp] theorem sdiv_cons : sdiv (x::xs) g = (x / g) :: sdiv xs g := rfl

@[simp] theorem sdiv_get {xs : IntList} {g : Int} {i} : (xs.sdiv g).get i = xs.get i / g := by
  simp only [sdiv, get, List.get?_map]
  cases xs.get? i <;> simp

theorem mem_sdiv {xs : IntList} (h : x ∈ xs) : x / g ∈ xs.sdiv g := by
  apply List.mem_map_of_mem _ h

def gcd (xs : IntList) : Nat := xs.foldr (fun x g => Nat.gcd x.natAbs g) 0

@[simp] theorem gcd_nil : gcd [] = 0 := rfl
@[simp] theorem gcd_cons : gcd (x :: xs) = Nat.gcd x.natAbs (gcd xs) := rfl

theorem gcd_cons_div_left : (gcd (x::xs) : Int) ∣ x := by
  simp only [gcd, List.foldr_cons, Int.ofNat_dvd_left]
  apply Nat.gcd_dvd_left

theorem gcd_cons_div_right : gcd (x::xs) ∣ gcd xs := by
  simp only [gcd, List.foldr_cons]
  apply Nat.gcd_dvd_right

theorem gcd_cons_div_right' : (gcd (x::xs) : Int) ∣ (gcd xs : Int) := by
  rw [Int.ofNat_dvd_left, Int.natAbs_ofNat]
  exact gcd_cons_div_right

theorem gcd_dvd (xs : IntList) {a : Int} (m : a ∈ xs) : (xs.gcd : Int) ∣ a := by
  rw [Int.ofNat_dvd_left]
  induction m with
  | head =>
    simp only [gcd_cons]
    apply Nat.gcd_dvd_left
  | tail b m ih =>   -- FIXME: why is the argument of tail implicit?
    simp only [gcd_cons]
    exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) ih

theorem dvd_gcd (xs : IntList) (c : Nat) (w : ∀ {a : Int}, a ∈ xs → (c : Int) ∣ a) :
    c ∣ xs.gcd := by
  simp only [Int.ofNat_dvd_left] at w
  induction xs with
  | nil => simpa using Nat.dvd_zero c
  | cons x xs ih =>
    simp
    apply Nat.dvd_gcd
    · apply w
      simp
    · apply ih
      intro b m
      apply w
      exact List.mem_cons_of_mem x m

theorem gcd_eq_iff (xs : IntList) (g : Nat) :
    xs.gcd = g ↔ (∀ {a : Int}, a ∈ xs → (g : Int) ∣ a) ∧ (∀ (c : Nat), (∀ {a : Int}, a ∈ xs → (c : Int) ∣ a) → c ∣ g) := by
  constructor
  · rintro rfl
    exact ⟨gcd_dvd _, dvd_gcd _⟩
  · rintro ⟨hi, hg⟩
    apply Nat.dvd_antisymm
    · apply hg
      intro i m
      exact gcd_dvd xs m
    · exact dvd_gcd xs g hi

attribute [simp] Int.zero_dvd

@[simp] theorem gcd_eq_zero (xs : IntList) : xs.gcd = 0 ↔ ∀ x ∈ xs, x = 0 := by
  simp [gcd_eq_iff, Nat.dvd_zero]

@[simp] theorem dot_mod_gcd_left (xs ys : IntList) : dot xs ys % xs.gcd = 0 := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      rw [dot_cons₂, Int.add_emod,
        ← Int.emod_emod_of_dvd (x * y) (gcd_cons_div_left),
        ← Int.emod_emod_of_dvd (dot xs ys) (Int.ofNat_dvd.mpr gcd_cons_div_right)]
      simp_all

theorem gcd_dvd_dot_left (xs ys : IntList) : (xs.gcd : Int) ∣ dot xs ys :=
  Int.dvd_of_emod_eq_zero (dot_mod_gcd_left xs ys)

attribute [simp] Int.zero_ediv

theorem dot_sdiv_left (xs ys : IntList) {d : Int} (h : d ∣ xs.gcd) :
    dot (xs.sdiv d) ys = (dot xs ys) / d := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      have wx : d ∣ x := Int.dvd_trans h (gcd_cons_div_left)
      have wxy : d ∣ x * y := Int.dvd_trans wx (Int.dvd_mul_right x y)
      have w : d ∣ (IntList.gcd xs : Int) := Int.dvd_trans h (gcd_cons_div_right')
      simp_all [Int.add_ediv_of_dvd_left, Int.mul_ediv_assoc']

@[simp] theorem dot_sdiv_gcd_left (xs ys : IntList) :
    dot (xs.sdiv xs.gcd) ys = (dot xs ys) / xs.gcd :=
  dot_sdiv_left xs ys (by exact Int.dvd_refl _)

def leadingSign (xs : IntList) : Int :=
  match xs with
  | [] => 0
  | 0 :: xs => leadingSign xs
  | x :: _ => x.sign

@[simp] theorem leadingSign_nil : leadingSign [] = 0 := rfl
@[simp] theorem leadingSign_cons_zero : leadingSign (0 :: xs) = leadingSign xs := rfl
theorem leadingSign_cons : leadingSign (x :: xs) = if x = 0 then leadingSign xs else x.sign := by
  split <;> rename_i h
  · subst h
    rfl
  · rw [leadingSign]
    intro w
    exact h w

attribute [simp] Int.neg_eq_zero

theorem leadingSign_neg {xs : IntList} : (-xs).leadingSign = - xs.leadingSign := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : x = 0
    · subst h
      simp_all
    · simp_all [leadingSign_cons]

def trim (xs : IntList) : IntList :=
  (xs.reverse.dropWhile (· == 0)).reverse

@[simp] theorem trim_nil : trim [] = [] := rfl

@[simp] theorem trim_append_zero {xs : IntList} : (xs ++ [0]).trim = xs.trim := by
  simp [trim, List.dropWhile]

theorem trim_cons :
    trim (x :: xs) = if x = 0 then if trim xs = [] then [] else 0 :: trim xs else x :: trim xs := by
  simp only [trim, List.reverse_cons]
  generalize xs.reverse = xs'
  simp only [List.dropWhile_append, List.reverse_eq_nil_iff]
  split <;> rename_i h
  · simp only [List.dropWhile_cons, beq_iff_eq, List.dropWhile_nil, h, List.reverse_nil]
    split <;> simp
  · split <;> simp_all

@[simp] theorem trim_neg {xs : IntList} : (-xs).trim = -xs.trim := by
  simp only [trim, neg_def, List.reverse_map]
  generalize xs.reverse = xs'
  induction xs' with
  | nil => simp
  | cons x xs' ih =>
    simp only [List.map_cons, List.dropWhile_cons, Int.neg_eq_zero, beq_iff_eq]
    split <;>
    simp_all [List.reverse_map]

end IntList
