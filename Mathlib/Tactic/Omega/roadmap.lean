/-!
# `omega` roadmap

I'm following William Pugh's
"The omega test: a fast and practical integer programming algorithm for dependence analysis"
https://doi.org/10.1145/125826.125848.

Chapter 5.5 of "Decision procedures" is also helpful,
but has less detail about important optimizations.

## Architecture

I'll describe the overall architecture of the tactic first.

I'll pretend in this description that we're using the most simple data structures
(for which writing proofs is easy), and in the "Optimizations" section describe
the more complicated data structures that allow faster algorithms.

### Preprocessors

Run `intros` and then `exfalso`.

Replace hypotheses `¬ a ≤ b` in `Int` or `Nat` with `b < a`, etc.

Select hypotheses which are `=`, `≥`, or `>` in `Int` or `Nat`.

We then apply the following pre-processors (item marked `[x]` are implemented).

* [ ] Replace `x > y` with `x ≥ y + 1`.
* [x] Replace `x ≥ y` with `x - y ≥ 0`.
* [ ] Given `x ≥ 0` for `x : Nat`, replace it with `(x : Int) ≥ 0`.
* [ ] Push `Nat`-to-`Int` coercions inwards across `+`, `*`, `/`, `%`.
* [ ] For each `(a - b : Int)` with `a b : Nat`, replace with two problems:
  * replacing `(a - b : Int)` with `(a : Int) - (b : Int)`, adding `(a : Int) ≥ (b : Int)`
  * replacing `(a - b : Int)` with `0`, adding `(b : Int) > (a : Int)`
* [ ] If `x / m` appears, for some `x : Int` and `m : Nat`,
  replace `x / m` with a new variable `α` and add the constraints
  `0 ≤ - m * α + x ≤ m - 1`.
* [ ] If `x % m` appears, similarly, introduce the same new contraints
  but replace `x % m` with `- m * α + x`.

Now all hypotheses are of the form `x = 0` or `x ≥ 0`,
where `x` is an integer linear combination of atoms.

**Status**:
Barely started, so the current tactic only runs on `x ≥ y` and `x = y` hypotheses in `Int`.

### Processing

We define `LinearCombo` and `Problem`:

```
structure LinearCombo where
  const : Int
  coeffs : List Int

structure Problem where
  possible : Bool
  equalities : List LinearCombo
  inequalities : List LinearCombo
```

and a predicate `Problem.unsat`.

Given a collection of `Expr`s representing the pre-processed hypotheses,
we construct a `p : Problem` and an `r : Expr` of type `p.unsat → False`.

Simplifying slightly, we could now express a semi-decision procedure as a pair

* `f : Problem → Problem`
* `t : {p : Problem} → (f p).unsat → p.unsat`,

and execute it as follows:

* Attempt to construct the `Eq.refl` proof that `u : (f p).possible = false`.
* From this construct the proofs `u' : (f p).unsat` and `u'' : p.unsat := t u'`.
* Assign `Expr.app r u''`, to complete our proof of `False`.

If we have a decision procedure, we can express that instead as
* `f : Problem → Problem`
* `t : {p : Problem} → (p → f p) × (f p → p)`
* `w : ∀ {p : Problem}, f p = impossible ∨ f p = trivial`
where here we're using a coercion from `Problem` to `Type` given by the solution set.
Now we have the option of either
proving `False` using the forwards direction of `t` (if `f p = impossible`) as before, or
constructing a witness using the backwards direction of `t` (if `f p = trivial`).

The complication is that our procedure will not actually be of the form
`Problem → Problem`, but rather `Problem → Formula Problem`, where a `Formula` is just a clause
built via `and` and `or` out of `Problem`s.
So instead of proving `(f p).possible = false` by `rfl`,
we'll be proving that `f p` is the empty disjunction.

**Status** Implemented but messy, in decision procedure form, without `Formula`.

**TODO**
* Refactor so we can run in semi-decision procedure form,
  so we can delay implementing completeness, and writing termination proofs, until later.
* Decide the design for formulas, and refactor to use that.
* The `Expr` munging code could be made more efficient,
  and I need to check in case this is the bottleneck on large-but-easy problems.

### The algorithm

For simplicity in this section all equalities are of the form `c + ∑ aᵢ * xᵢ = 0` and
all inequalities are of the form `c + ∑ aᵢ * xᵢ ≥ 0`.

#### Normalization

For each equality:
* If all `aᵢ = 0`, then `c = 0` (in which case discard the equality), or the problem is impossible.
* Calculate the gcd of the `aᵢ`.
  If this divides `c`, divide through, otherwise conclude the problem is impossible.

For each inequality:
* If all `aᵢ = 0`, then `c ≥ 0` (in which case discard), or the problem is impossible.
* Calculate the gcd `g`  of the non-constant coefficients.
  Divide through, rounding down `c / g` to the next integer.

Now check if there is a pair of inequalities `c + ∑ aᵢ * xᵢ ≥ 0` and `c' - ∑ aᵢ * xᵢ ≥ 0`
(i.e. with the opposite non-constant coefficients) such that `c < -c'`,
and if so conclude the problem is impossible.

These steps are call "normalization",
and we run them repeatedly so it is important that they are efficient.

Note that during normalization the number of equation or inequalities can only decrease.

**Status:** Implemented, but I need to add a hashtable to allow fast discovery of inequalities with
opposite non-constant coefficients.

#### Eliminating equalities

If we have an equation with some `aᵢ = ± 1`, then we can solve for `xᵢ` and eliminate that equation.

Otherwise, suppose all nonzero `aᵢ` have absolute value at least 2.
Let `m = min ∣aᵢ|` (the minimum is over all equations, and all coefficients of those equations).
Let `M` be the minimum, over all equations containing a coefficient with absolute value `m`,
of the maximum absolute value of an `aᵢ`.

We can make a substitution which (before normalization):
* keeps the number of equations constant, and
* either reduces the value `m` of the minimal `|aᵢ|` constant, or
* produces an problem that has the same value of `m`, and strictly smaller `M`.

Thus we can implement a recursive algorithm which decreases in lexicographic order
`(# of equations, m, M)`, and so on termination has eliminated all equalities.

If `m` reduces to zero, we're done because all the equalities are constants,
so normalization will get rid of them all.
If `m` reduces to one, we can eliminate an equation, thus reducing `# of equations`.
Otherwise, we can reduce `M` until it is equal to `m`,
at which point the equation witnessing `M` has all coefficients equal,
and so will be removed by normalization.

**Status**
* The substitution that reduces `M` is implemented.
* The framework for the well-founded recursion is implemented.
* The critical inequality (that `M` strictly decreases) is just a `sorry`.
  It's hopefully at most a day's work, but I've been avoiding thinking about. :-)

**TODO**
* Before completing the termination proof, add an optional fuel parameter
  so this part is usable as a semi-decision procedure even before writing the termination proof.

#### Eliminating inequalities

We now have a problem `P` consisting solely of inequalities `c + ∑ aᵢ * xᵢ ≥ 0`.

If any variable is unbounded (i.e all `aᵢ` for that `i` are non-negative, or all are non-positive),
then we can reduce the problem by deleting all inequalities involving that variable.

Now, given any choice of bounded variable, we can construct an equivalence

```
P ↔ RealShadow ∧ (DarkShadow ∨ GreyShadows)
```

where the "real shadow" and "dark shadow" problems are again integer linear arithmetic problems
(still with no equalities), and the "grey shadow" problem is itself a somewhat complicated recursive
clause built out of integer linear arithmetic problems with additional equalities and inequalities.

It will be important here that we evaluate theses clauses from left to right,
and only lazily construct the later problems.

We are hoping that the real shadow is unsatisfiable
(so we never need to think about the dark and grey shadows),
or failing that, we are hoping that the dark shadow is satisfiable
(so we never need to think about the grey shadows).
It's only on the difficult and annoying problems that we expect to have to decide the grey shadows!

An obvious short cut to a semi-decision procedure is
to just fail whenever the real shadow is satisfiable.
(This was what the `omega` implemented in Lean 3 did, although I didn't know this until recently!)

The real shadow is just the usual Fourier-Motzkin elimination.
If we are eliminating `xᵢ`, then `RealShadow` contains all inequalities with `aᵢ = 0`,
and for each pair of inequalities `e ≥ 0` and `e' ≥ 0`
where the coefficient of `xᵢ` in `e` is `aᵢ > 0` and the coefficient of `xᵢ` in `e'` is `aᵢ' < 0`
the inequality
```
aᵢ * (e' - aᵢ' * xᵢ) ≥ aᵢ' * (e - aᵢ * xᵢ)
```

It's trivial to see that if `P` is satisfiable then `RealShadow` is too.
Over the rationals, they are equi-satisfiable, but that is not directly relevant to `omega`.

The dark shadow is the same as the real shadow, except that the new inequality we add for
pair `e` and `e'` as above is instead:
```
aᵢ * (e' - aᵢ' * xᵢ) ≥ (|aᵢ * aᵢ'| - |aᵢ'| - aᵢ + 1) + aᵢ' * (e - aᵢ * xᵢ)
```

In fact, very frequently we can chose a bounded variable that results in an "exact elimination",
meaning that the real shadow and dark shadow have the same integer solutions.
Whenever this occurs there are no grey shadows.
Whenever this is possible we use such a reduction.

There are two criteria for deciding if eliminating `xᵢ` is exact:
1. All the negative `aᵢ` equal -1, or all the positive `aᵢ` equal +1.
  (In which case the actual inequalities produced are identical, not just their solutions.)
2. A criteria that I can't interpret clearly in the original paper, haven't found elsewhere,
  and haven't found time to try to reconstruct with pen and paper!

We now describe the grey shadow for eliminating `xᵢ`.
Let `m` be the most negative coefficient of `xᵢ` in any inequality.
For any lower bound `e ≥ 0` with coefficient `aᵢ > 0` of `xᵢ`,
define `r e := (|m * aᵢ| - |m| - aᵢ)/|m|`
(note that division is in `Int`, so implicitly has a "floor").

To describe the grey shadow, we pick an ordering of the lower bounds `eₖ ≥ 0` for `xᵢ`, with
`k ∈ {0, ..., n}`.
Then
```
GreyShadow = GreyShadow' (n+1) 0
GreyShadow' (a+1) b = R b ∨ (Q (b+1) ∧ GreyShadow' a (b+1))
GreyShadow' 0 b = unsat
```
where
* `R k` is the disjunction over `j` in the range `0, ..., r eₖ` of `Q k` with the additional
  equality constraints `eₖ = j`
* `Q 0 = P`
* `Q (k+1)` is `Q k` with `eₖ ≥ 0` replaced by `eₖ ≥ 1 + r eₖ`.

This is a little complicated, so we'll spell out how it evaluates, considering the case `n = 1`
(i.e. we have two lower bounds).
Because we eagerly evaluate the left-hand-side of `∧` and `∨`,
we begin with
`GreyShadow' 2 0 = R 0 ∨ (Q 1 ∧ GreyShadow' 1 1) = R 0 ∨ (Q 1 ∧ (R 1 ∨ (Q 2 ∧ unsat)))`.
Then `R 0` is a disjunction over `j` of `Q 0 = P` with the additional equality constraints `e₀ = j`.
If we find one of these is satisfied we short-circuit and
do not need to consider the rest of the clause.
However if `R 0` is unsat, we turn to `(Q 1 ∧ (R 1 ∨ (Q 1 ∧ unsat)))`, and
next decide `Q 1`. This is `Q 0 = P` with `e₀ ≥ 0` replaced by `e₀ ≥ 1 + r e₀`.
If this is unsat, we can short-circuit.
Otherwise we need to decide `R 1`, which a disjunction over `j` of `Q 1` as just described,
with the additional equality constraints `e₁ = j`.
Finally, when we reach `Q 1 ∧ unsat`, we hope we are clever enough to avoid thinking about `Q 1`
and can just say the problem is unsatisfiable.

Termination is a little tricky here. The new problems `RealShadow`, `DarkShadow`, and each `R k`
are straightforward: they have strictly fewer variables than `P`.
It turns out the `Q k` terms are not strictly needed, but are helpful for algorithmic efficiency.
Thus we define a modified version `Q' f k`, for `f : Nat`, such that
* `Q' 0 k` is trivially satisfiable
* `Q' (f+1) k = Q k`

The disjunctions `R k` are stil constructed by adding a equality constraint to `Q k` itself,
without the `f` parameter. Our modified `GreyShadow` is given by
```
GreyShadow' (f+1) (a+1) b = R b ∨ (Q f (b+1) ∧ GreyShadow' (f+1) a (b+1))
GreyShadow' 0 (a+1) b = R b ∨ GreyShadow' 0 a (b+1)
```

With this, we can show termination of inequality elimination by decreasing along the lexicographic
order on `(# of variables, f)`, starting at any arbitrary `f`
(in practice chosen large enough that it won't exhaust).
Each recursive call to inequality elimination either strictly decreased `# of variables`,
or leaves it unchanged and strictly decreases `f`.

**Note:** I haven't found discussion of termination in the literature;
if anyone knows a way to do this without the fuel parameter, please let me know.

**Status:**
* No code!

## Optimizations

During inequality elimination it is essential that we perform exact elimination where possible,
and amongst those chose eliminations that result in the fewest new constraints
(i.e. minimizing the product of the numbers of upper and lower bounds).
During inexact elimination, we choose a variable `xᵢ` and order the lower bounds to consider
so as to minimize the branching factor in the disjunctions `R k`.

We spend a lot of time in the algorithm:

* looking up pairs of inequalities with opposite nonconstant coefficients (during normalization)
* looking up coefficients with minimal absolute value (during equality elimination)
* looking up inequalities which are upper/lower bounds for a given variable
  (during inequality elimination)

so it's important that our data structures cache this information accessibly.

Currently coefficients of a constraint are just stored as a `List Int`.
We could explore replacing this with either `AssocList Nat Int` or `HashMap Nat Int`
(or even a data data structure that dynamically switches between these).
Hopefully this isn't too hard as there is a thin API in place around `List Int` already.

-/
