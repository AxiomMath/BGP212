/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Definitions
public import Gap212.Equidistribution.CoefficientSequence
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Totient

/-!
# The Siegel–Walfisz property and equidistribution over a set of moduli

The Siegel–Walfisz property of [2, Definition 6 (ii)] and the equidistribution of [2], in the
two-variable shape where a sequence takes the scale `x` as an argument.

## Uniformity in the parameter triple

The definition of equidistribution in [2] adds: "the implied constant is only allowed to depend on
`ω`, `γ` and `δ` insofar as they determine which `ε` are sufficiently small". So the constant is a
function of `(A, ε)` alone. A predicate stated at a single triple `(ω, γ, δ)` cannot say this — in a
context fixing the triple, an `∃ c` may always depend on it. So `HasEquidistributionFamily` takes a
*set* `S` of triples and places `∃ c` before `∀ p ∈ S`.

The same mechanism is what lets these estimates apply to the convolution classes of `Gap212.Harman`,
where `N(x) = x^{γ(x)}` with `γ` a *function of `x`*. If `γ(x)` takes values in `G`, instantiate at
`S = {(ω, γ, δ) | γ ∈ G}`: uniformity of `c` over `S` means one constant serves every `x`, so the
diagonal statement — the estimate at `γ(x)` for each `x` — follows. [2, Lemmas 3–7] each write
`N(x) = x^γ` as though `γ` were constant; the uniform reading is the one under which they apply to
sequences with `γ(x)`.

## Main definitions

* `Gap212.HasSiegelWalfiszFamily`: [2, Definition 6 (ii)].
* `Gap212.HasEquidistributionFamily`: equidistribution, uniform over a family of parameter triples.
-/

@[expose] public section

namespace Gap212

open Real Finset

/-- **Siegel–Walfisz** ([2, Definition 6 (ii)]): the error in the expected count of `α` over a
congruence class is `≪_A τ(qr)^{O(1)} N(x)/log(x)^A`.

The exponent `k` on `τ(qr)` is bound outside `∀ A`, since the `O(1)` there is absolute
while the implied constant carries the subscript `A`.

The sums are `finsum`s over the full congruence class, as in [2]. They are finite exactly when
`α (·) x` has finite support, which is what `LocatedAtScaleFamily α N` provides — [2] states this
property only for sequences already located at scale `N`, and so do all five of the estimates that
consume it. It is separate from `LocatedAtScaleFamily`, as items (i) and (ii) of [2, Definition 6]
are; the cost is that this predicate alone says nothing about a sequence not located at scale `N`,
since `finsum` is `0` on infinite support. Always use it conjoined with `LocatedAtScaleFamily`. -/
def HasSiegelWalfiszFamily (α : ℕ → ℝ → ℂ) (N : ℝ → ℝ) : Prop :=
  ∃ k : ℕ, ∀ A > (1 : ℝ), ∃ c > (0 : ℝ), ∀ (x : ℝ), 1 < x → ∀ q r : ℕ, 1 ≤ q → 1 ≤ r →
    ∀ a : ℕ, Nat.Coprime a q →
      ‖(∑ᶠ n ∈ {n : ℕ | n ≡ a [MOD q] ∧ Nat.Coprime n r}, α n x) -
        (1 / (Nat.totient q : ℂ)) * ∑ᶠ n ∈ {n : ℕ | Nat.Coprime n (q * r)}, α n x‖ ≤
      c * ((q * r).divisors.card : ℝ) ^ k * N x / (log x) ^ A

/-- **Equidistribution over a family of moduli sets.**

`D x ω γ δ ε` is the set of moduli at scale `x` for the parameters `(ω, γ, δ)` and small parameter
`ε`; `S` is a family of admissible triples `(ω, γ, δ)`.

The quantifier order is the content of the definition. `ε₀` witnesses "for any sufficiently small
`ε`". The `∃ c` precedes `∀ p ∈ S`, which is how the restriction of [2] — that the implied
constant may depend on the triple only through which `ε` are small enough — is expressed. -/
def HasEquidistributionFamily (f : ℕ → ℝ → ℂ)
    (D : ℝ → ℝ → ℝ → ℝ → ℝ → Finset ℕ) (S : Set (ℝ × ℝ × ℝ)) : Prop :=
  ∃ ε₀ > (0 : ℝ), ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∀ A > (0 : ℝ), ∃ c > (0 : ℝ),
    ∀ p ∈ S, ∀ (x : ℝ), 1 < x → ∀ a : ℕ, CoprimeBelow a x →
      ∑ q ∈ D x p.1 p.2.1 p.2.2 ε with Squarefree q,
        ‖(∑ n ∈ dyadic x with n ≡ a [MOD q], f n x) -
          (1 / (Nat.totient q : ℂ)) * ∑ n ∈ dyadic x with Nat.Coprime n q, f n x‖ ≤
      c * x / (log x) ^ A

end Gap212
