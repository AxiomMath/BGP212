/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Equidistribution.Estimates
public import Gap212.Routing.Monotone
public meta import Gap212.Attr

/-!
# Bilinear Bombieri–Vinogradov, and the four modulus ranges

The factor-extraction lemmas conclude only for `q > x^{1/2 - ε₁}`: below that the smooth reservoir
is no longer guaranteed to reach the target window. So the sub-half range needs a separate input,
and it is the bilinear Bombieri–Vinogradov theorem, [1, Theorem 2.9].

This is a cited result, carried as a hypothesis. Its statement already applies to
divisor-bounded convolution coefficients in primitive residue classes, not only to `Λ`.

## The shape of the statement

Two features distinguish it from the five Type estimates. The sum runs over **all** `q` up to
`x^{1/2}(log x)^{-B}` — no factorization requirement, no squarefree restriction, no special moduli:
below the half-level, logarithmic savings absorb everything. And the cutoff exponent `B` is chosen
*after* `A`, which is what the `B = B(A)` of [1, Theorem 2.9] records; the routing then spends part
of the saving on the `O((log x)^{C₁ + C₂})` pieces the dyadic and Heath–Brown decompositions
produce.

## The four ranges

The dyadic blocks split into four disjoint classes: the genuinely sub-half range handled by
this input, a logarithmically thin transition range, the exact half-level endpoint block, and the
positive-level range handled by Stadlmann's Type estimates.

The endpoint class `𝒬₀` is the dyadic block whose normalized exponent is exactly `1/2`, and
`x^{1/2}` need not be an integer. So it is not a set of moduli but an exponent-level notion, and
correspondingly `Gap212.Inputs.mem_range_or_endpoint` states the coverage of the three *modulus*
classes with the `(q : ℝ) = x^{1/2}` case broken out rather than swept in.

## Main definitions

* `Gap212.Inputs.BilinearBombieriVinogradovFamily`: the cited input.
* `Gap212.Inputs.subhalfModuli`, `transitionModuli`, `positiveLevelModuli`: the modulus classes.

## Main results

* `Gap212.Inputs.mem_range_or_endpoint`: the three classes cover, apart from the exact endpoint.
* `Gap212.Inputs.subhalf_disjoint_transition` and companions: they are pairwise disjoint.
* `Gap212.Inputs.subhalfSum_le_of_bv`: the sub-half discrepancy bound, for any set of moduli inside
  the range.
-/

@[expose] public section

namespace Gap212.Inputs

open Finset Real Gap212.Routing

/-! ## The three modulus classes -/

/-- `𝒬_BV`: the genuinely sub-half moduli, `q ≤ x^{1/2}(log x)^{-C}`. -/
@[gap212 "def_range_bv"]
def subhalfModuli (x C : ℝ) : Set ℕ :=
  {q : ℕ | (q : ℝ) ≤ x ^ (1 / 2 : ℝ) / (Real.log x) ^ C}

/-- `𝒬_tr`: the logarithmically thin transition range, where neither the sub-half input nor the
positive-level estimates apply verbatim. -/
def transitionModuli (x C : ℝ) : Set ℕ :=
  {q : ℕ | x ^ (1 / 2 : ℝ) / (Real.log x) ^ C < (q : ℝ) ∧ (q : ℝ) < x ^ (1 / 2 : ℝ)}

/-- `𝒬₊`: the positive-level moduli, handled by Stadlmann's Type estimates. -/
@[gap212 "def_range_plus"]
def positiveLevelModuli (x : ℝ) : Set ℕ :=
  {q : ℕ | x ^ (1 / 2 : ℝ) < (q : ℝ)}

/-- **The three modulus classes cover, apart from the exact endpoint.** Every modulus is sub-half,
transitional, or positive-level — unless it sits exactly at `x^{1/2}`.

That case is broken out because the fourth class `𝒬₀` is an *exponent-level* block, not a set of
moduli, and `x^{1/2}` need not be an integer. -/
@[gap212 "lem_ranges_exhaust"]
theorem mem_range_or_endpoint (x C : ℝ) (q : ℕ) :
    q ∈ subhalfModuli x C ∨ q ∈ transitionModuli x C ∨ q ∈ positiveLevelModuli x ∨
      (q : ℝ) = x ^ (1 / 2 : ℝ) := by
  by_cases h₁ : (q : ℝ) ≤ x ^ (1 / 2 : ℝ) / (Real.log x) ^ C
  · exact Or.inl h₁
  · rcases lt_trichotomy ((q : ℝ)) (x ^ (1 / 2 : ℝ)) with h | h | h
    · exact Or.inr (Or.inl ⟨not_le.mp h₁, h⟩)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))

/-- The sub-half moduli `𝒬_BV` and the transition moduli `𝒬_tr` are disjoint. -/
theorem subhalf_disjoint_transition (x C : ℝ) :
    Disjoint (subhalfModuli x C) (transitionModuli x C) := by
  rw [Set.disjoint_left]
  intro q hq hq'
  exact absurd hq (not_le.mpr hq'.1)

/-- For `x > 1` and `(log x)^C ≥ 1`, the sub-half moduli `𝒬_BV` and the positive-level moduli
`𝒬₊` are disjoint. -/
theorem subhalf_disjoint_positive {x C : ℝ} (hx : 1 < x) (hC : 1 ≤ (Real.log x) ^ C) :
    Disjoint (subhalfModuli x C) (positiveLevelModuli x) := by
  rw [Set.disjoint_left]
  intro q hq hq'
  have hpos : (0 : ℝ) < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) _
  have hdiv : x ^ (1 / 2 : ℝ) / (Real.log x) ^ C ≤ x ^ (1 / 2 : ℝ) := div_le_self hpos.le hC
  have h1 : (q : ℝ) ≤ x ^ (1 / 2 : ℝ) / (Real.log x) ^ C := hq
  have h2 : x ^ (1 / 2 : ℝ) < (q : ℝ) := hq'
  linarith

/-- The transition moduli `𝒬_tr` and the positive-level moduli `𝒬₊` are disjoint. -/
theorem transition_disjoint_positive (x C : ℝ) :
    Disjoint (transitionModuli x C) (positiveLevelModuli x) := by
  rw [Set.disjoint_left]
  intro q hq hq'
  exact absurd hq.2 (not_lt.mpr hq'.le)

/-! ## The cited input -/

/-- **Bilinear Bombieri–Vinogradov** ([1, Theorem 2.9]).

For divisor-bounded coefficient sequences `α`, `β` at scales `M`, `N` with `M N ≍ x`, **at least
one** of them having the Siegel–Walfisz property and both scales at least `x^η`, the discrepancy of
`α ⋆ β` over *every* modulus up to `x^{1/2}(log x)^{-B}` beats `x/(log x)^A`.

The disjunction is the cited theorem's, verbatim: **at least one** of them has the Siegel–Walfisz
property. Demanding it of `β` alone would be a *narrowing* of the cited theorem — safe in the
sense that it assumes less, but it does not match the citation, and a Type II member with the
property on the wrong factor could not be routed through it without first commuting the
convolution.

The order of quantifiers is the content: `A` is given first and `B = B(A)` chosen after, which is
what lets the routing spend part of the saving on the `O((log x)^{C₁+C₂})` pieces the dyadic and
Heath–Brown decompositions produce, and still be left with `A`.

The scale hypothesis is `∃ X, ∀ x ≥ X` — **eventually**, not `∀ x > 1`. [1, Theorem 2.9] writes
`min(M,N) ≥ x^η` with no quantifier on `x`, every statement there being asymptotic. Read as
`∀ x > 1` it is unusable: a Harman-class member gives `M x ≫ x^{ξ₂-ϵ}` *with a constant*, and near
`x = 1` a constant below `1` breaks the pointwise inequality while leaving the asymptotic one
intact. So the eventual reading is the faithful one, and it is what makes the citation applicable
at all — see `Gap212.Routing.typeII_scale_eventually`. -/
def BilinearBombieriVinogradovFamily : Prop :=
  ∀ (α β : ℕ → ℝ → ℂ) (M N : ℝ → ℝ) (η : ℝ), 0 < η →
    IsCoefficientSequenceFamily α → LocatedAtScaleFamily α M →
    IsCoefficientSequenceFamily β → LocatedAtScaleFamily β N →
    (HasSiegelWalfiszFamily α M ∨ HasSiegelWalfiszFamily β N) →
    AsympEq (fun x ↦ M x * N x) id →
    (∃ X : ℝ, ∀ x : ℝ, X ≤ x → x ^ η ≤ M x ∧ x ^ η ≤ N x) →
    ∀ A > (0 : ℝ), ∃ B > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ x : ℝ, 1 < x → ∀ a : ℕ, CoprimeBelow a x →
        ∑ q ∈ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / (Real.log x) ^ B⌋₊,
          discrepancy (dconvFamily α β) x a q ≤ c * x / (Real.log x) ^ A

/-- **The sub-half bound, for any set of moduli inside the range.** Since the discrepancy is
nonnegative, the bilinear input applies to any `Finset` of moduli contained in
`[1, x^{1/2}(log x)^{-B}]` — in particular to whichever moduli the support generates there.

This is the form the routing consumes for `𝒬_BV`. -/
theorem subhalfSum_le_of_bv (hbv : BilinearBombieriVinogradovFamily)
    {α β : ℕ → ℝ → ℂ} {M N : ℝ → ℝ} {η : ℝ} (hη : 0 < η)
    (hα : IsCoefficientSequenceFamily α) (hαM : LocatedAtScaleFamily α M)
    (hβ : IsCoefficientSequenceFamily β) (hβN : LocatedAtScaleFamily β N)
    (hSW : HasSiegelWalfiszFamily α M ∨ HasSiegelWalfiszFamily β N)
    (hMN : AsympEq (fun x ↦ M x * N x) id)
    (hscale : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → x ^ η ≤ M x ∧ x ^ η ≤ N x)
    {A : ℝ} (hA : 0 < A) :
    ∃ B > (0 : ℝ), ∃ c > (0 : ℝ), ∀ x : ℝ, 1 < x → ∀ a : ℕ, CoprimeBelow a x →
      ∀ D : Finset ℕ, D ⊆ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / (Real.log x) ^ B⌋₊ →
        ∑ q ∈ D, discrepancy (dconvFamily α β) x a q ≤ c * x / (Real.log x) ^ A := by
  obtain ⟨B, hB, c, hc, hbound⟩ :=
    hbv α β M N η hη hα hαM hβ hβN hSW hMN hscale A hA
  refine ⟨B, hB, c, hc, fun x hx a ha D hD ↦ ?_⟩
  exact le_trans (discrepancySum_le_of_subset hD) (hbound x hx a ha)

end Gap212.Inputs
