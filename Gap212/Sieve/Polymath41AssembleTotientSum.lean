/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssembleTotientCoprime

/-!
# The left-hand side of `Gap212.Sieve.Polymath41Totient` meets the interchange

`Gap212.Sieve.Polymath41FubiniTotient` performs the source's interchange for the totient
kernel, but at a sum over **all** pairs `(d,d') ∈ ℕ × ℕ` — whereas
`Gap212.Sieve.pairSumTotient`, which is literally the left-hand side of
`Gap212.Sieve.Polymath41Totient`, is a **finite** sum over `d, d' ≤ B` coprime to `W`. This file
identifies the two and hence puts the interchange under the `Prop` to be proved:

  `pairSumTotient W B x F G = ∫∫ f(ξ) g(ξ') K^φ_W(ξ,ξ') dξ dξ'`.

## The two differences, and why neither costs an estimate

* **The truncation.** The profiles vanish on `[β,∞)` and `x^β ≤ B`, so a divisor past `B` is read
  by the profile at a point `≥ β` (`Gap212.Sieve.le_logx_of_lt_of_rpow_le`) and contributes `0`.
  This is the same argument that makes the `∀ B` quantifier of the obligations vacuous
  (`Gap212.Sieve.pairSumTotient_congr_of_rpow_le`), used here in the other direction: to *extend*
  the finite sum to all of `ℕ × ℕ` rather than to move between two truncations. The extension is
  exact, not an approximation — every added term is literally zero.
* **The coprimality.** The sum's filter is `(W,d) = 1` on each coordinate, and the weight's
  restriction `Gap212.Sieve.coprimeWeight` is `(W,[d,d']) = 1` on the pair; they agree by
  `Gap212.Sieve.coprime_lcm_iff`. This is why the restriction could be installed on the *weight*,
  at the generic layer, instead of being carried through the interchange.

Together these say the source is entitled to write its sum without a truncation — it does — and
that the coprimality condition it does write is the one this development's pair sums carry.

## Main results

* `Gap212.Sieve.tsum_coprimeTotientWeightPairSum_eq_pairSumTotient`: the finite coprime sum is the
  unrestricted `tsum` of the restricted weight.
* `Gap212.Sieve.ofReal_pairSumTotient_eq_integral`,
  `Gap212.Sieve.ofReal_pairSumTotient_eq_integral_integral`: **the interchange at the `Prop`'s own
  left-hand side**, over the product measure and in the source's iterated form.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset MeasureTheory Real
open scoped FourierTransform ContDiff ArithmeticFunction.Moebius

/-! ## The finite coprime sum is a `tsum` over all pairs -/

/-- **A divisor outside the sum's range is outside it for one of exactly three reasons**: it is
`0`, it exceeds the truncation, or it shares a factor with `W`. Each of the three kills the
corresponding term of the pair sum, and they kill it for three different reasons — `μ(0) = 0`, the
profile's vanishing, and the weight's restriction. -/
theorem eq_zero_or_lt_or_not_coprime_of_notMem_filter {W B e : ℕ}
    (he : e ∉ {d ∈ Icc 1 B | Nat.Coprime W d}) :
    e = 0 ∨ B < e ∨ ¬ Nat.Coprime W e := by
  by_cases h0 : e = 0
  · exact Or.inl h0
  by_cases hc : Nat.Coprime W e
  · refine Or.inr (Or.inl ?_)
    by_contra hle
    exact he (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, hc⟩)
  · exact Or.inr (Or.inr hc)

/-- **`Gap212.Sieve.pairSumTotient` is the unrestricted pair sum of the restricted weight.** The
left-hand side of `Gap212.Sieve.Polymath41Totient`, in the shape the interchange of
`Gap212.Sieve.Polymath41Fubini` consumes:

  `∑'_{(d,d') ∈ ℕ×ℕ} 1_{([d,d'],W)=1}·μ(d)μ(d')/φ([d,d'])·F(log_x d)·G(log_x d')`
  `  = pairSumTotient W B x F G`.

Both differences between the two sides are exact. The `tsum` is over all pairs and the sum over
`d, d' ≤ B` coprime to `W`; the terms in between vanish for the three reasons of
`Gap212.Sieve.eq_zero_or_lt_or_not_coprime_of_notMem_filter`, and the pairwise coprimality
condition matches the coordinatewise one by `Gap212.Sieve.coprime_lcm_iff`. No summability is used:
the `tsum` is a finite sum in disguise. -/
theorem tsum_coprimeTotientWeightPairSum_eq_pairSumTotient {x : ℝ} (hx : 1 < x) {β : ℝ}
    {F G : ℝ → ℝ} (hFv : ∀ t, β ≤ t → F t = 0) (hGv : ∀ t, β ≤ t → G t = 0) (W : ℕ) {B : ℕ}
    (hB : x ^ β ≤ (B : ℝ)) :
    ∑' p : ℕ × ℕ, coprimeWeight W totientPairWeight p *
        ((F (Notation.logx x p.1) : ℂ) * (G (Notation.logx x p.2) : ℂ))
      = ((pairSumTotient W B x F G : ℝ) : ℂ) := by
  classical
  set S : Finset ℕ := {d ∈ Icc 1 B | Nat.Coprime W d} with hS
  have hnotcop : ∀ d d' : ℕ, (¬ Nat.Coprime W d) ∨ (¬ Nat.Coprime W d') →
      coprimeWeight W totientPairWeight (d, d') = 0 := by
    intro d d' h
    have hne : ¬ Nat.Coprime W (Nat.lcm d d') := by
      intro hcop
      rcases h with h | h
      · exact h ((coprime_lcm_iff W d d').1 hcop).1
      · exact h ((coprime_lcm_iff W d d').1 hcop).2
    simp only [coprimeWeight]
    rw [if_neg hne]
  have hzero : ∀ p : ℕ × ℕ, p ∉ S ×ˢ S →
      coprimeWeight W totientPairWeight p *
        ((F (Notation.logx x p.1) : ℂ) * (G (Notation.logx x p.2) : ℂ)) = 0 := by
    rintro ⟨d, d'⟩ hp
    have hor : d ∉ S ∨ d' ∉ S := by
      by_cases hd : d ∈ S
      · exact Or.inr fun hd' ↦ hp (mem_product.2 ⟨hd, hd'⟩)
      · exact Or.inl hd
    rcases hor with hd | hd'
    · rcases eq_zero_or_lt_or_not_coprime_of_notMem_filter (hS ▸ hd) with h | h | h
      · rw [coprimeTotientWeight_eq_zero W (d, d') (Or.inl h), zero_mul]
      · rw [hFv _ (le_logx_of_lt_of_rpow_le hx hB h), Complex.ofReal_zero, zero_mul, mul_zero]
      · rw [hnotcop d d' (Or.inl h), zero_mul]
    · rcases eq_zero_or_lt_or_not_coprime_of_notMem_filter (hS ▸ hd') with h | h | h
      · rw [coprimeTotientWeight_eq_zero W (d, d') (Or.inr h), zero_mul]
      · rw [hGv _ (le_logx_of_lt_of_rpow_le hx hB h), Complex.ofReal_zero, mul_zero, mul_zero]
      · rw [hnotcop d d' (Or.inr h), zero_mul]
  rw [tsum_eq_sum hzero, Finset.sum_product, pairSumTotient, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun d' hd' ↦ ?_
  have hcop : Nat.Coprime W (Nat.lcm d d') :=
    (coprime_lcm_iff W d d').2 ⟨(mem_filter.1 (hS ▸ hd)).2, (mem_filter.1 (hS ▸ hd')).2⟩
  simp only [coprimeWeight, totientPairWeight, if_pos hcop]
  push_cast
  ring

/-! ## The interchange, at the `Prop`'s own left-hand side -/

/-- **The interchange for `Gap212.Sieve.pairSumTotient`** — the source's interchange with `[d,d']`
replaced by `φ([d,d'])`, at the sum `Gap212.Sieve.Polymath41Totient` is about: for
`F, G` smooth with compact support vanishing on `[β,∞)`, `x > 1` and `x^β ≤ B`,

  `pairSumTotient W B x F G = ∫_{ℝ²} f(ξ) g(ξ') K^φ_W(ξ,ξ') d(ξ,ξ')`,

with `f = Gap212.Sieve.profileFourier F`, `g = Gap212.Sieve.profileFourier G` and `K^φ_W` the
coprime totient kernel `Gap212.Sieve.coprimeTotientKernel` at the exponents
`Gap212.Sieve.kernelArg x ξ`, whose real part is `1/log x`.

The totient kernel's limiting local factor is `1 - 1/(p-1)`, not `1 - 1/p`, so the product over
`p ∤ W` carries the correction `∏_{p∤W}(1-1/(p-1)²)`
(`Gap212.Sieve.localFactorTotient_one_one_eq_mul`), which is driven to `1` at `W = W(x)` by
`Gap212.Sieve.tendsto_tprod_corr_W`. That correction vanishes identically at `p = 2`
(`Gap212.Sieve.localFactorTotient_two_one_one_eq_zero`), which is where this kernel's oddness
requirement comes from and why it is `W(x)` — always even — that makes it harmless. -/
theorem ofReal_pairSumTotient_eq_integral {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) {x : ℝ}
    (hx : 1 < x) {β : ℝ} (hFv : ∀ t, β ≤ t → F t = 0) (hGv : ∀ t, β ≤ t → G t = 0) (W : ℕ)
    {B : ℕ} (hB : x ^ β ≤ (B : ℝ)) :
    ((pairSumTotient W B x F G : ℝ) : ℂ)
      = ∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 *
          coprimeTotientKernel W (kernelArg x w.1) (kernelArg x w.2) := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  rw [← tsum_coprimeTotientWeightPairSum_eq_pairSumTotient hx hFv hGv W hB]
  exact tsum_weightPairSum_eq_integral (coprimeTotientWeight_eq_zero W) hF hFc hG hGc hx
    (summable_weightMajorant_coprimeTotientWeight W (by positivity))

/-- **The same in the source's iterated form** `∫ dξ ∫ dξ'`. -/
theorem ofReal_pairSumTotient_eq_integral_integral {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) {x : ℝ}
    (hx : 1 < x) {β : ℝ} (hFv : ∀ t, β ≤ t → F t = 0) (hGv : ∀ t, β ≤ t → G t = 0) (W : ℕ)
    {B : ℕ} (hB : x ^ β ≤ (B : ℝ)) :
    ((pairSumTotient W B x F G : ℝ) : ℂ)
      = ∫ ξ : ℝ, ∫ ξ' : ℝ, profileFourier F ξ * profileFourier G ξ' *
          coprimeTotientKernel W (kernelArg x ξ) (kernelArg x ξ') := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  rw [← tsum_coprimeTotientWeightPairSum_eq_pairSumTotient hx hFv hGv W hB]
  exact tsum_weightPairSum_eq_integral_integral (coprimeTotientWeight_eq_zero W) hF hFc hG hGc hx
    (summable_weightMajorant_coprimeTotientWeight W (by positivity))

end Gap212.Sieve
