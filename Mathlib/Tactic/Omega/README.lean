
/-
# `omega` roadmap

I'm following William Pugh's
"The omega test: a fast and practical integer programming algorithm for dependence analysis"
https://doi.org/10.1145/125826.125848.

Chapter 5.5 of "Decision procedures" is also helpful,
but has less detail about important optimizations.

## Architecture

### Preprocessors

Apply `exfalso`.

Select hypotheses which are `=`, `≥`, or `>` in `Int` or `Nat`.

We then apply the following pre-processors (item marked `[x]` are implemented).

* [ ] Replace `x > y` with `x ≥ y + 1`.
* [x] Replace `x ≥ y` with `x - y ≥ 0`.
* [ ] Given `x ≥ 0` for `x : Nat`, replace it with `(x : Int) ≥ 0`.
* [ ] Push `Nat`-to-`Int` coercions inwards across `+`, `*`, `/`, `%`.
* [ ] For each `(a - b : Int)` with `a b : Nat`, replace with two problems:
  * replacing `(a - b : Int)` with `(a : Int) - (b : Int)`, adding `(a : Int) ≥ (b : Int)`
  * replacing `(a - b : Int)` with `0`, adding `(b : Int) ≥ (a : Int)`
* [ ] If `x / m` appears, for some `x : Int` and `m : Nat`,
  replace `x / m` with a new variable `α` and add the constraints
  `0 ≤ - m * α + x ≤ m - 1`.
* [ ] If `x % m` appears, similarly, introduce the same new contraints
  but replace `x % m` with `- m * α + x`.

Now all hypotheses are of the form `x = 0` or `x ≥ 0`,
where `x` is an integer linear combination of atoms.

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
we construct a `p : Problem` and an `Expr` of type `p.unsat → False`.

Simplifying slightly, we could now expression a semi-decision procedure as a pair
* `f : Problem → Problem`
* `t : ∀ p, (f p).unsat → p.unsat`,
and execute it as follows:
* Construct, via
-/
