/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Equidistribution.Moduli

/-!
# The five analytic estimates

[2, Lemmas 3–7], in the two-variable shape — the variants in [2] of [1, Theorem 2.8 (iv), (ii) and
(v)], of Baker–Irving's Type I estimate, and of Stadlmann's earlier Type I estimate, each with the
moduli restriction relaxed from `i`-tuply `x^δ`-dense divisibility to the mere existence of divisors
in prescribed windows.

**These are hypotheses, not theorems.** [2] records only the amendments to the original proofs,
so they are carried as hypotheses, as `PrimeGapsLib` carries `BombieriVinogradov`.

## How `γ` is handled

Each lemma writes `N(x) = x^γ` as though `γ` were a constant, but the convolution classes of
`Gap212.Harman` — which supply these sequences downstream — have `N(x) = x^{γ(x)}`. So `γ` is
quantified here as a *set* `G` of permissible values, with `N x = x ^ g` for some `g ∈ G` at each
`x`, and the lemma's inequalities required of every `g ∈ G` with a *uniform slack* `ε₁ > 0`. The
slack is the device of [2], which observes that the permissible triples are cut out by strict
inequalities and that demanding them "with room to spare" is what makes `ε`, and so the implied
constant, uniform in the triple.

## Main definitions

* `Gap212.TypeIIPolymathFamily`: [2, Lemma 3].
* `Gap212.TypeIbPolymathFamily`: [2, Lemma 4].
* `Gap212.TypeIBakerIrvingFamily`: [2, Lemma 5].
* `Gap212.TypeIStadlmannFamily`: [2, Lemma 6].
* `Gap212.TypeIIIPolymathFamily`: [2, Lemma 7].
-/

@[expose] public section

namespace Gap212

open Real

/-- `f ≍ g`: `c g ≤ f ≤ C g` for absolute positive constants. -/
def AsympEq (f g : ℝ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ x : ℝ, 1 < x → c * g x ≤ f x ∧ f x ≤ C * g x

/-- `f ≫ g`. -/
def DomGE (f g : ℝ → ℝ) : Prop := ∃ c > (0 : ℝ), ∀ x : ℝ, 1 < x → c * g x ≤ f x

/-- `f ≪ g`. -/
def DomLE (f g : ℝ → ℝ) : Prop := ∃ C > (0 : ℝ), ∀ x : ℝ, 1 < x → f x ≤ C * g x

/-- The family of triples `{(ω, g, δ) | g ∈ G}` that each estimate's conclusion is uniform over. -/
def triples (ω δ : ℝ) (G : Set ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 = ω ∧ p.2.1 ∈ G ∧ p.2.2 = δ}

/-- The common hypotheses of [2, Lemmas 3, 4 and 6]: `f = α ⋆ β` with `α` a coefficient sequence
at scale `M`, `β` a coefficient sequence at scale `N` with the Siegel–Walfisz property,
`M(x) N(x) ≍ x`, and `N(x) ≤ x^{1/2}`. -/
structure TypeIISetup (α β : ℕ → ℝ → ℂ) (M N : ℝ → ℝ) (G : Set ℝ) : Prop where
  alphaCoeff : IsCoefficientSequenceFamily α
  alphaScale : LocatedAtScaleFamily α M
  betaCoeff : IsCoefficientSequenceFamily β
  betaScale : LocatedAtScaleFamily β N
  betaSW : HasSiegelWalfiszFamily β N
  product : AsympEq (fun x ↦ M x * N x) id
  betaSmall : ∀ x : ℝ, 1 < x → N x ≤ x ^ (1 / 2 : ℝ)
  /-- `N(x) = x^{γ(x)}` with every value of `γ` drawn from `G`. -/
  exponent : ∀ x : ℝ, 1 < x → ∃ g ∈ G, N x = x ^ g

/-- **[2, Lemma 3] (Polymath Type II)**, the variant in [2] of [1, Theorem 2.8 (iv)], serving as a
replacement for [1, Theorem 2.8 (i)]. Under `24ω + 7δ - 5γ < -2` and `8ω + 3δ - γ < 0`, the
convolution equidistributes over `D_{IIa}`. -/
def TypeIIPolymathFamily : Prop :=
  ∀ (α β : ℕ → ℝ → ℂ) (M N : ℝ → ℝ) (ω δ : ℝ) (G : Set ℝ),
    TypeIISetup α β M N G →
    (∃ ε₁ > (0 : ℝ), ∀ g ∈ G,
      24 * ω + 7 * δ - 5 * g + ε₁ < -2 ∧ 8 * ω + 3 * δ - g + ε₁ < 0) →
    HasEquidistributionFamily (dconvFamily α β) moduliIIaFamily (triples ω δ G)

/-- **[2, Lemma 4] (Polymath Type I(ii))**, the variant in [2] of [1, Theorem 2.8 (ii)]. Under
`24ω + 7δ - 3γ < -1` and `8ω + 3δ - γ < 0`, the convolution equidistributes over `D_{IIb}`. -/
def TypeIbPolymathFamily : Prop :=
  ∀ (α β : ℕ → ℝ → ℂ) (M N : ℝ → ℝ) (ω δ : ℝ) (G : Set ℝ),
    TypeIISetup α β M N G →
    (∃ ε₁ > (0 : ℝ), ∀ g ∈ G,
      24 * ω + 7 * δ - 3 * g + ε₁ < -1 ∧ 8 * ω + 3 * δ - g + ε₁ < 0) →
    HasEquidistributionFamily (dconvFamily α β) moduliIIbFamily (triples ω δ G)

/-- **[2, Lemma 5] (Baker–Irving Type I)**, the variant in [2] of Baker–Irving's Type I estimate.
Here `β` is *smooth* at scale `N`, and there is no `N ≤ x^{1/2}` restriction.

The conditions are piecewise in `γ`: `3γ - 12ω - 3δ > 1` for `γ ≤ 1/2`, and `68ω + 14δ < 1` for
`γ ∈ (1/2, 1/2 + 2ω + ε]`. That upper cutoff mentions the small parameter `ε`, which in this
formalization is quantified *inside* `HasEquidistributionFamily` and so is not available here. We
therefore require the second condition for every `g > 1/2`, which is marginally stronger than the
display and hence makes this *assumption* marginally weaker — the safe direction. It costs nothing
downstream: at the parameters of [2, Theorem 1], `ω = 0.003` and `δ = 0.028`, giving
`68ω + 14δ = 0.596 < 1`. -/
def TypeIBakerIrvingFamily : Prop :=
  ∀ (α β : ℕ → ℝ → ℂ) (M N : ℝ → ℝ) (ω δ : ℝ) (G : Set ℝ),
    IsCoefficientSequenceFamily α → LocatedAtScaleFamily α M →
    IsCoefficientSequenceFamily β → IsSmoothAtScaleFamily β N →
    AsympEq (fun x ↦ M x * N x) id →
    (∀ x : ℝ, 1 < x → ∃ g ∈ G, N x = x ^ g) →
    (∃ ε₁ > (0 : ℝ), ∀ g ∈ G,
      (g ≤ 1 / 2 → 1 + ε₁ < 3 * g - 12 * ω - 3 * δ) ∧
      (1 / 2 < g → 68 * ω + 14 * δ + ε₁ < 1)) →
    HasEquidistributionFamily (dconvFamily α β) moduliIFamily (triples ω δ G)

/-- **[2, Lemma 6] (Stadlmann Type I)**, the variant in [2] of Stadlmann's earlier Type I estimate.
Under `8ω + 4δ + 2γ < 1`, `32ω + 10δ - γ < 0` and `48ω + 16δ - 4γ < -1`, the convolution
equidistributes over `D_{IIc}`. -/
def TypeIStadlmannFamily : Prop :=
  ∀ (α β : ℕ → ℝ → ℂ) (M N : ℝ → ℝ) (ω δ : ℝ) (G : Set ℝ),
    TypeIISetup α β M N G →
    (∃ ε₁ > (0 : ℝ), ∀ g ∈ G,
      8 * ω + 4 * δ + 2 * g + ε₁ < 1 ∧
      32 * ω + 10 * δ - g + ε₁ < 0 ∧
      48 * ω + 16 * δ - 4 * g + ε₁ < -1) →
    HasEquidistributionFamily (dconvFamily α β) moduliIIcFamily (triples ω δ G)

/-- **[2, Lemma 7] (Polymath Type III)**, the variant in [2] of [1, Theorem 2.8 (v)]. Here
`f = α ⋆ ψ₁ ⋆ ψ₂ ⋆ ψ₃` with three smooth factors, `γ` enters through the size conditions on the
`Nᵢ` rather than through a single scale, and the sole condition is `28ω + 9γ + 8δ < 4`. -/
def TypeIIIPolymathFamily : Prop :=
  ∀ (α ψ₁ ψ₂ ψ₃ : ℕ → ℝ → ℂ) (M N₁ N₂ N₃ : ℝ → ℝ) (ω δ : ℝ) (G : Set ℝ),
    IsCoefficientSequenceFamily α → LocatedAtScaleFamily α M →
    IsSmoothAtScaleFamily ψ₁ N₁ → IsSmoothAtScaleFamily ψ₂ N₂ → IsSmoothAtScaleFamily ψ₃ N₃ →
    AsympEq (fun x ↦ M x * (N₁ x * (N₂ x * N₃ x))) id →
    (∀ g ∈ G,
      DomGE (fun x ↦ N₁ x * N₂ x) (fun x ↦ x ^ (1 - g)) ∧
      DomGE (fun x ↦ N₁ x * N₃ x) (fun x ↦ x ^ (1 - g)) ∧
      DomGE (fun x ↦ N₂ x * N₃ x) (fun x ↦ x ^ (1 - g)) ∧
      DomGE N₁ (fun x ↦ x ^ (1 - 2 * g)) ∧ DomLE N₁ (fun x ↦ x ^ g) ∧
      DomGE N₂ (fun x ↦ x ^ (1 - 2 * g)) ∧ DomLE N₂ (fun x ↦ x ^ g) ∧
      DomGE N₃ (fun x ↦ x ^ (1 - 2 * g)) ∧ DomLE N₃ (fun x ↦ x ^ g)) →
    (∃ ε₁ > (0 : ℝ), ∀ g ∈ G, 28 * ω + 9 * g + 8 * δ + ε₁ < 4) →
    HasEquidistributionFamily (dconvFamily α (dconvFamily ψ₁ (dconvFamily ψ₂ ψ₃)))
      moduliIIIFamily (triples ω δ G)

end Gap212
