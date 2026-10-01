/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Coefficient sequences

[2, Definition 6], in the two-variable shape: a coefficient sequence is a function of an integer `n`
and a scale parameter `x`, of size `τ(n)^{O(1)} log(x)^{O(1)}`, together with the three side
conditions the five equidistribution estimates of [2] are stated in terms of — being located at a
scale, having the Siegel–Walfisz property, and being smooth at a scale.

## Conventions

[2] writes `α(n;x)` for a function on `ℕ × (1,∞)`; we take the curried form `ℕ → ℝ → ℂ` and carry
`1 < x` as a hypothesis where it is needed, rather than working over a subtype of `ℝ`.

Vinogradov `≪` is rendered in the style of `Nat.HasLevelOfDistribution` and
`BombieriVinogradov` upstream: an explicit `∃ c > 0` bound, with the quantifier order recording
which parameters the implied constant may depend on. An `O(1)` appearing in an *exponent* becomes
an existentially quantified natural number, and it is bound *outside* the parameters the implied
constant depends on, since the `O(1)` there is absolute.

## Main definitions

* `Gap212.IsCoefficientSequenceFamily`: `|α(n;x)| ≪ τ(n)^{O(1)} log(x)^{O(1)}`.
* `Gap212.LocatedAtScaleFamily`: `α(·;x)` is supported on `[c N(x), C N(x)]`.
* `Gap212.IsSmoothAtScaleFamily`: `α(n;x) = ψ(n/N(x))` for a smooth `ψ` with log-power
  derivative bounds.
* `Gap212.dconvFamily`: the Dirichlet convolution `(α ⋆ β)(n;x) = ∑_{d ∣ n} α(d;x) β(n/d;x)`.
-/

@[expose] public section

namespace Gap212

open Real

/-- A **coefficient sequence** ([2, Definition 6]): `|α(n;x)| ≪ τ(n)^{O(1)} log(x)^{O(1)}`.

Both `O(1)`s are exponents, so each becomes an existentially quantified natural number; the
implied constant is absolute. -/
def IsCoefficientSequenceFamily (α : ℕ → ℝ → ℂ) : Prop :=
  ∃ (C : ℝ) (k l : ℕ), 0 < C ∧
    ∀ (n : ℕ) (x : ℝ), 1 < x → ‖α n x‖ ≤ C * (n.divisors.card : ℝ) ^ k * (log x) ^ l

/-- `α` is **located at scale** `N` ([2, Definition 6 (i)]): for absolute constants `0 < c ≤ C`, the
function `α(·;x)` is supported on `[c N(x), C N(x)]` for every `x > 1`.

The condition `1 ≪ c ≪ C ≪ 1` says exactly that `c` and `C` are absolute and positive: they may not
depend on `x`, which is why they are bound outside the quantifier over `x`. -/
def LocatedAtScaleFamily (α : ℕ → ℝ → ℂ) (N : ℝ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ (x : ℝ), 1 < x → ∀ n : ℕ, α n x ≠ 0 → c * N x ≤ (n : ℝ) ∧ (n : ℝ) ≤ C * N x

/-- `α` is **smooth at scale** `N` ([2, Definition 6 (iii)]): `α(n;x) = ψ(n/N(x))` for a smooth `ψ`
supported on an absolute interval `[c,C]`, whose derivatives satisfy
`|ψ^{(j)}(t)| ≪_j log(x)^{O_j(1)}`.

The bound on the `j`-th derivative is allowed to depend on `j` in both its constant and its
exponent, which is what the subscripted `≪_j` and `O_j(1)` record. `ψ` depends on `x`,
so it is quantified inside. -/
def IsSmoothAtScaleFamily (α : ℕ → ℝ → ℂ) (N : ℝ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ (x : ℝ), 1 < x → ∃ ψ : ℝ → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      (∀ t : ℝ, ψ t ≠ 0 → t ∈ Set.Icc c C) ∧
      (∀ j : ℕ, ∃ (b : ℝ) (m : ℕ), 0 < b ∧
        ∀ t : ℝ, ‖iteratedDeriv j ψ t‖ ≤ b * (log x) ^ m) ∧
      ∀ n : ℕ, α n x = ψ ((n : ℝ) / N x)

/-- The **Dirichlet convolution** in the arithmetic variable:
`(α ⋆ β)(n;x) = ∑_{d ∣ n} α(d;x) β(n/d;x)`. -/
def dconvFamily (α β : ℕ → ℝ → ℂ) : ℕ → ℝ → ℂ :=
  fun n x ↦ ∑ d ∈ n.divisors, α d x * β (n / d) x

@[inherit_doc] scoped infixl:70 " ⋆ " => Gap212.dconvFamily

end Gap212
