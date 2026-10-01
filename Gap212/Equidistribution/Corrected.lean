/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Equidistribution.SmoothAtScale
public import Gap212.Harman
public import Gap212.Notation
public meta import Gap212.Attr

/-!
# The two estimates that mention smoothness, at uniform derivative bounds

`Gap212.IsSmoothAtScaleFamily` binds the derivative bounds `b` and `m` *inside* `∀ x`, so they may
be re-chosen for each `x`. `Gap212.Corrected.IsSmoothAtScaleFamily` binds them before `x`, as
functions of `j` alone, and `Gap212.Corrected.isSmoothAtScale_le` shows it is the stronger notion.

This module restates `TypeIBakerIrvingFamily` and `TypeIIIPolymathFamily` at the uniform notion
and proves that the original forms imply them. The directions differ for the estimates and for
the class:

* For the **estimates**, smoothness is a *hypothesis* of an inner implication. Strengthening it
  quantifies over fewer sequences, so the restated proposition is **weaker**:
  `TypeIBakerIrvingFamily → TypeIBakerIrvingFamily'`.
* For the **class**, smoothness is part of the *definition* of membership:
  `Gap212.Harman.TypeIFamily` and `TypeIIIFamily` use the uniform notion directly. Strengthening
  membership shrinks `ℋ`, so `Gap212.Harman.HarmanReductionFamily` — whose antecedent quantifies
  over `ℋ` — is a *stronger* hypothesis at the uniform notion, not a weaker one. That is the
  faithful reading, because Type I membership is defined through smoothness at a scale.

## Main results

* `Gap212.Corrected.typeIBakerIrving'`, `typeIIIPolymath'`: the two estimates at uniform
  smoothness.
* `Gap212.Corrected.typeIBakerIrving'_of_family`, `typeIIIPolymath'_of_family`: the family-form
  estimates imply them.
-/

@[expose] public section

namespace Gap212.Corrected

open Real Gap212.Notation

/-! ## The two estimates, at uniform smoothness -/

/-- **The Baker–Irving Type I estimate, at uniform smoothness.** Identical to
`Gap212.TypeIBakerIrvingFamily` except that the smooth factor satisfies
`Gap212.Corrected.IsSmoothAtScaleFamily`. -/
def typeIBakerIrving' : Prop :=
  ∀ (α β : ℕ → ℝ → ℂ) (M N : ℝ → ℝ) (ω δ : ℝ) (G : Set ℝ),
    IsCoefficientSequenceFamily α → LocatedAtScaleFamily α M →
    IsCoefficientSequenceFamily β → Gap212.Corrected.IsSmoothAtScaleFamily β N →
    AsympEq (fun x ↦ M x * N x) id →
    (∀ x : ℝ, 1 < x → ∃ g ∈ G, N x = x ^ g) →
    (∃ ε₁ > (0 : ℝ), ∀ g ∈ G,
      (g ≤ 1 / 2 → 1 + ε₁ < 3 * g - 12 * ω - 3 * δ) ∧
      (1 / 2 < g → 68 * ω + 14 * δ + ε₁ < 1)) →
    HasEquidistributionFamily (dconvFamily α β) moduliIFamily (triples ω δ G)

/-- **The Polymath Type III estimate, at uniform smoothness.** -/
def typeIIIPolymath' : Prop :=
  ∀ (α ψ₁ ψ₂ ψ₃ : ℕ → ℝ → ℂ) (M N₁ N₂ N₃ : ℝ → ℝ) (ω δ : ℝ) (G : Set ℝ),
    IsCoefficientSequenceFamily α → LocatedAtScaleFamily α M →
    Gap212.Corrected.IsSmoothAtScaleFamily ψ₁ N₁ → Gap212.Corrected.IsSmoothAtScaleFamily ψ₂ N₂ →
    Gap212.Corrected.IsSmoothAtScaleFamily ψ₃ N₃ →
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

/-! ## The estimates: the family form implies the uniform form

Smoothness is a hypothesis, so strengthening it makes the proposition weaker. Each proof is the
family-form estimate applied after `Gap212.Corrected.isSmoothAtScale_le` has weakened the
smoothness the caller supplied. -/

/-- **The family-form Type I estimate implies the uniform one.** -/
theorem typeIBakerIrving'_of_family (h : TypeIBakerIrvingFamily) : typeIBakerIrving' := by
  intro α β M N ω δ G hα hαM hβcoeff hβ hMN hG hwall
  exact h α β M N ω δ G hα hαM hβcoeff (isSmoothAtScale_le hβ) hMN hG hwall

/-- **The family-form Type III estimate implies the uniform one.** -/
theorem typeIIIPolymath'_of_family (h : TypeIIIPolymathFamily) : typeIIIPolymath' := by
  intro α ψ₁ ψ₂ ψ₃ M N₁ N₂ N₃ ω δ G hα hαM hψ₁ hψ₂ hψ₃ hprod hsize hwall
  exact h α ψ₁ ψ₂ ψ₃ M N₁ N₂ N₃ ω δ G hα hαM (isSmoothAtScale_le hψ₁)
    (isSmoothAtScale_le hψ₂) (isSmoothAtScale_le hψ₃) hprod hsize hwall

end Gap212.Corrected
