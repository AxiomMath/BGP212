/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Equidistribution.Estimates
public import Gap212.Equidistribution.SmoothAtScale
public import Gap212.Main
public meta import Gap212.Attr

/-!
# The Harman decomposition class, and the external reduction to it

[2, Definition 9]: `ℋ(ξ₁, ξ₂, ξ₃)` is the class of convolutions the equidistribution
estimates can handle. Three shapes:

* **Type I** — `α ⋆ β` with `β` *smooth* at scale `N`, and `N = x^{γ(x)}` with `γ ≥ ξ₁ - ϵ`;
* **Type II** — `α ⋆ β` with *both* factors having Siegel–Walfisz, and `ξ₂ - ϵ ≤ γ ≤ 1 - ξ₂ + ϵ`;
* **Type III** — `α ⋆ ψ₁ ⋆ ψ₂ ⋆ ψ₃` with three smooth factors in prescribed ranges.

`ϵ = 10⁻¹⁰` throughout, the fixed slack of [2, Definition 9].

## Type II asks more than the estimates deliver

Type II requires the Siegel–Walfisz property of **both** `α` and `β`, whereas the estimates over
`D_{IIa}`, `D_{IIb}` and `D_{IIc}` ([2, Lemmas 3, 4 and 6]) each require it of `β` only. The extra
strength is what licenses the `γ ↔ 1 - γ` symmetry reduction in the routing argument — the roles of
`α` and `β` are swapped to bring `γ` below `1/2`, and that swap needs Siegel–Walfisz on whichever
factor ends up second.

## Why this class matters even though `ρ = 1_ℙ`

At `ξ₂ = 2/5` the Harman minorant degenerates to the prime indicator, so no
correction sums survive (`Gap212.PointA.gamma₂_empty`). It does **not** follow that the
decomposition is unnecessary. `1_ℙ` is not itself a member of `ℋ`, and the only route to its
equidistribution over the generated moduli is the Buchstab identity

    1_ℙ = θ₀ + Σ₁ + Σ₂ - Σ₃

with `θ₀` already equidistributed and each `Σ` reduced to members of `ℋ`. That identity and the
routing of its sums are not proved here: the reduction is the prime-indicator endpoint of
[2, Proposition 2], and appears below as the hypothesis `HarmanReductionFamily`.

## Main definitions

* `Gap212.Harman.slack`: the fixed `ϵ = 10⁻¹⁰`.
* `Gap212.Harman.TypeIFamily`, `TypeIIFamily`, `TypeIIIFamily`: the three shapes of
  [2, Definition 9].
* `Gap212.Harman.HarmanClassFamily`: their disjunction, `ℋ(ξ₁, ξ₂, ξ₃)`.
* `Gap212.Harman.HarmanReductionFamily`: the cited reduction of `1_ℙ` to the class.
-/

@[expose] public section

namespace Gap212.Harman

open Real

/-- The fixed slack `ϵ = 10⁻¹⁰` of [2, Definition 9], in the `Harman` namespace, for the classes
below. The same constant is `Gap212.slack`. -/
noncomputable def slack : ℝ := 1 / 10 ^ 10

/-- **Type I** of [2, Definition 9]: `f = α ⋆ β` with `α` a coefficient sequence at scale `M`, `β` a
*smooth* coefficient sequence at scale `N`, `M(x)N(x) ≍ x`, and `N(x) = x^{γ(x)}` with
`γ(x) ≥ ξ₁ - ϵ`.

No Siegel–Walfisz is required, because smoothness is stronger.

Smoothness here is `Gap212.Corrected.IsSmoothAtScaleFamily`, which binds the
derivative bounds `b` and `m`
*before* `∀ x`: `b_j` and `m_j` are chosen before `x` and depend on `j` alone.
`Gap212.IsSmoothAtScaleFamily` binds them inside, so the
bound may be re-chosen per `x`, and membership against it is a strictly larger class. -/
def TypeIFamily (ξ₁ : ℝ) (f : ℕ → ℝ → ℂ) : Prop :=
  ∃ (α β : ℕ → ℝ → ℂ) (M N : ℝ → ℝ),
    f = dconvFamily α β ∧
    IsCoefficientSequenceFamily α ∧ LocatedAtScaleFamily α M ∧
    IsCoefficientSequenceFamily β ∧ Gap212.Corrected.IsSmoothAtScaleFamily β N ∧
    AsympEq (fun x ↦ M x * N x) id ∧
    ∀ x : ℝ, 1 < x → ∃ g : ℝ, ξ₁ - slack ≤ g ∧ N x = x ^ g

/-- **Type II** of [2, Definition 9]: `f = α ⋆ β` with both factors coefficient sequences having the
Siegel–Walfisz property, `M(x)N(x) ≍ x`, and `ξ₂ - ϵ ≤ γ(x) ≤ 1 - ξ₂ + ϵ`.

Siegel–Walfisz on *both* factors is what the `γ ↔ 1 - γ` swap in the routing argument needs. -/
def TypeIIFamily (ξ₂ : ℝ) (f : ℕ → ℝ → ℂ) : Prop :=
  ∃ (α β : ℕ → ℝ → ℂ) (M N : ℝ → ℝ),
    f = dconvFamily α β ∧
    IsCoefficientSequenceFamily α ∧ LocatedAtScaleFamily α M ∧ HasSiegelWalfiszFamily α M ∧
    IsCoefficientSequenceFamily β ∧ LocatedAtScaleFamily β N ∧ HasSiegelWalfiszFamily β N ∧
    AsympEq (fun x ↦ M x * N x) id ∧
    ∀ x : ℝ, 1 < x → ∃ g : ℝ, ξ₂ - slack ≤ g ∧ g ≤ 1 - ξ₂ + slack ∧ N x = x ^ g

/-- **Type III** of [2, Definition 9]: `f = α ⋆ ψ₁ ⋆ ψ₂ ⋆ ψ₃` with three smooth factors at scales
`N₁, N₂, N₃` satisfying `M N₁ N₂ N₃ ≍ x`, `x^{1-2ξ₃-ϵ} ≤ Nᵢ ≤ x^{ξ₃+ϵ}`, and
`NᵢNⱼ ≥ x^{1-ξ₃-ϵ}` for `i ≠ j`.

The size conditions are transcribed as the literal pointwise inequalities the definition states,
rather than as `≪`/`≫`, since the `ϵ` already absorbs the implied constants.

Smoothness is `Gap212.Corrected.IsSmoothAtScaleFamily`, for the reason given at
`Gap212.Harman.TypeIFamily`. -/
def TypeIIIFamily (ξ₃ : ℝ) (f : ℕ → ℝ → ℂ) : Prop :=
  ∃ (α ψ₁ ψ₂ ψ₃ : ℕ → ℝ → ℂ) (M N₁ N₂ N₃ : ℝ → ℝ),
    f = dconvFamily α (dconvFamily ψ₁ (dconvFamily ψ₂ ψ₃)) ∧
    IsCoefficientSequenceFamily α ∧ LocatedAtScaleFamily α M ∧
    Gap212.Corrected.IsSmoothAtScaleFamily ψ₁ N₁ ∧ Gap212.Corrected.IsSmoothAtScaleFamily ψ₂ N₂ ∧
    Gap212.Corrected.IsSmoothAtScaleFamily ψ₃ N₃ ∧
    AsympEq (fun x ↦ M x * (N₁ x * (N₂ x * N₃ x))) id ∧
    (∀ x : ℝ, 1 < x →
      (x ^ (1 - 2 * ξ₃ - slack) ≤ N₁ x ∧ N₁ x ≤ x ^ (ξ₃ + slack)) ∧
      (x ^ (1 - 2 * ξ₃ - slack) ≤ N₂ x ∧ N₂ x ≤ x ^ (ξ₃ + slack)) ∧
      (x ^ (1 - 2 * ξ₃ - slack) ≤ N₃ x ∧ N₃ x ≤ x ^ (ξ₃ + slack)) ∧
      x ^ (1 - ξ₃ - slack) ≤ N₁ x * N₂ x ∧
      x ^ (1 - ξ₃ - slack) ≤ N₁ x * N₃ x ∧
      x ^ (1 - ξ₃ - slack) ≤ N₂ x * N₃ x)

/-- **`ℋ(ξ₁, ξ₂, ξ₃)`** of [2, Definition 9]: the convolutions of one of the three shapes. -/
def HarmanClassFamily (ξ₁ ξ₂ ξ₃ : ℝ) (f : ℕ → ℝ → ℂ) : Prop :=
  TypeIFamily ξ₁ f ∨ TypeIIFamily ξ₂ f ∨ TypeIIIFamily ξ₃ f

/-- **The Harman reduction**, a cited hypothesis. If every member of `ℋ(ξ₁, ξ₂, ξ₃)`
equidistributes over the moduli a support generates, then so does the prime indicator.

At `ξ₂ = 2/5` this is the prime-indicator endpoint of [2, Proposition 2], where the minorant
degenerates to `ρ = 1_ℙ`. The Buchstab construction and the routing of its sums are not proved
here.

The equidistribution of the members of `ℋ` is the antecedent, not an assumption. -/
def HarmanReductionFamily (p : SupportParams) (ξ₁ ξ₂ ξ₃ : ℝ) : Prop :=
  (∀ f : ℕ → ℝ → ℂ, HarmanClassFamily ξ₁ ξ₂ ξ₃ f → HasEquidistributionOverQstarFamily p f) →
    HasEquidistributionOverQstarFamily p primeIndicatorFamily

/-- **The routing criterion.** Every member of `ℋ(ξ₁, ξ₂, ξ₃)` equidistributes over the moduli
generated by `p`.

This is the conclusion of the routing argument: a case analysis over the three shapes and the
`γ`-ranges, routing each to one of the five Type estimates via the factor-extraction lemmas. It is
not proved in this two-variable form; the single-scale form at the datum is
`Gap212.HarmanClassEquidistributes`, which `Gap212.halfLevelCoverage` derives from the five
estimates, bilinear Bombieri–Vinogradov and `Gap212.PackingCertificate`. -/
def RoutingConclusionFamily (p : SupportParams) (ξ₁ ξ₂ ξ₃ : ℝ) : Prop :=
  ∀ f : ℕ → ℝ → ℂ, HarmanClassFamily ξ₁ ξ₂ ξ₃ f → HasEquidistributionOverQstarFamily p f

/-- **The arithmetic certificate, assembled.** Given the cited Harman reduction and the routing
conclusion, the prime indicator equidistributes over the support's generated moduli — which is
exactly `Gap212.ArithmeticCertificateFamily`, at the datum `gap212Params`.

The proof is one application. -/
theorem arithmeticCertificate_of_routingFamily {ξ₁ ξ₂ ξ₃ : ℝ}
    (hharman : HarmanReductionFamily gap212Params ξ₁ ξ₂ ξ₃)
    (hroute : RoutingConclusionFamily gap212Params ξ₁ ξ₂ ξ₃) :
    ArithmeticCertificateFamily :=
  hharman hroute

/-- **`H₁ ≤ 212` from the sieve criterion, the Harman reduction, the routing conclusion, and the
numerical certificate.**

Compared with `Gap212.nthPrimeGapLE_212_of_inputsFamily`, the hypothesis
`ArithmeticCertificateFamily` is resolved into the cited Harman reduction and the routing
conclusion. -/
theorem nthPrimeGapLE_212_of_parts {ξ₁ ξ₂ ξ₃ : ℝ}
    (hsieve : SieveCriterionFamily)
    (hharman : HarmanReductionFamily gap212Params ξ₁ ξ₂ ξ₃)
    (hroute : RoutingConclusionFamily gap212Params ξ₁ ξ₂ ξ₃)
    (hcert : Gap212Certificate) :
    NthPrimeGapLE 212 :=
  nthPrimeGapLE_212_of_inputsFamily hsieve
    (arithmeticCertificate_of_routingFamily hharman hroute) hcert

end Gap212.Harman
