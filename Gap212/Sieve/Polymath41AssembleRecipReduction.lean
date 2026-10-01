/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssembleRecipCoprime

/-!
# `Gap212.Sieve.Polymath41Recip` reduced to its kernel integral

Everything upstream of this file speaks about kernels, weights and Dirichlet series; the `Prop`
`Gap212.Sieve.Polymath41Recip` speaks about `Gap212.Sieve.pairSumRecip`, a *finite real double sum*
over `d, d' ≤ ⌈x^β⌉₊` coprime to `W(x)`. This file joins the two, so that the `Prop` becomes a
statement about the kernel and nothing else.

Two steps, both exact:

1. `Gap212.Sieve.ofReal_pairSumRecip_eq_tsum`: the finite real sum, cast to `ℂ`, **is** the
   unrestricted `tsum` over `ℕ × ℕ` of the coprimality-restricted weight against the profiles.
   Three things make the extension harmless: the weight vanishes when `d = 0` or `d' = 0`
   (`μ(0) = 0`), it vanishes when `W` fails to be coprime to `[d,d']` (which by
   `Gap212.Sieve.coprime_lcm_iff` is the sum's own filter), and the *profile* vanishes when
   `d > B ≥ x^β` (`Gap212.Sieve.le_logx_of_lt_of_rpow_le`). So the `tsum` has finite support,
   exactly the sum's index set.
2. `Gap212.Sieve.polymath41Recip_of_tendsto_integral`: feeding that through the interchange of
   `Gap212.Sieve.Polymath41Fubini` at the restricted weight turns the `Prop` into

     `B_x · ∫_{ℝ²} f(ξ) g(ξ') K_{W(x)}(ξ,ξ') d(ξ,ξ') ⟶ ∫₀^∞ F'G'`,

   `B_x = (φ(W(x))/W(x))·log x` the source's normalization and `K_W` the kernel
   `Gap212.Sieve.coprimeRecipKernel` whose Euler product over `p ∤ W` is
   `Gap212.Sieve.tprod_localFactorRecip_eq_coprimeRecipKernel`.

The hypothesis of `Gap212.Sieve.polymath41Recip_of_tendsto_integral` is the analytic core of Lemma
4.1, supplied by `Gap212.Sieve.polymath41Recip` in `Gap212.Sieve.Polymath41CloseRecip`. What
the reduction buys is that the core no longer mentions `Gap212.Sieve.pairSumRecip`, the truncation
`⌈x^β⌉₊`, the Möbius function or the coprimality filter: all of that is discharged here, once,
exactly.

## Main results

* `Gap212.Sieve.ofReal_pairSumRecip_eq_tsum`: the sieve's finite sum as a `tsum` over `ℕ × ℕ`.
* `Gap212.Sieve.ofReal_pairSumRecip_eq_integral`: the interchange applied to the sieve's own sum.
* `Gap212.Sieve.polymath41Recip_of_tendsto_integral`: the `Prop`, reduced to its kernel
  integral.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY MeasureTheory
open scoped ArithmeticFunction.Moebius

/-! ## The sieve's finite sum is a `tsum` over `ℕ × ℕ` -/

/-- **The support of the restricted summand.** Outside the sum's own index set every term is `0`,
for one of three reasons: the weight vanishes at a degenerate pair, the weight vanishes when `W` is
not coprime to `[d,d']`, or a profile vanishes because the divisor exceeds `B ≥ x^β`. -/
theorem coprimeWeight_recip_mul_profiles_eq_zero {W : ℕ} {x β : ℝ} (hx : 1 < x) {F G : ℝ → ℝ}
    (hF : ∀ t, β ≤ t → F t = 0) (hG : ∀ t, β ≤ t → G t = 0) {B : ℕ} (hB : x ^ β ≤ (B : ℝ))
    {p : ℕ × ℕ}
    (hp : p ∉ ({d ∈ Icc 1 B | Nat.Coprime W d} ×ˢ {d ∈ Icc 1 B | Nat.Coprime W d} :
      Finset (ℕ × ℕ))) :
    coprimeWeight W recipPairWeight p *
        ((F (Notation.logx x p.1) : ℂ) * (G (Notation.logx x p.2) : ℂ)) = 0 := by
  by_cases hcop : Nat.Coprime W (Nat.lcm p.1 p.2)
  swap
  · rw [coprimeWeight, if_neg hcop, zero_mul]
  obtain ⟨hc1, hc2⟩ := (coprime_lcm_iff W p.1 p.2).1 hcop
  rcases Nat.eq_zero_or_pos p.1 with h0 | h1
  · rw [coprimeWeight_eq_zero recipPairWeight_eq_zero W p (Or.inl h0), zero_mul]
  rcases Nat.eq_zero_or_pos p.2 with h0 | h2
  · rw [coprimeWeight_eq_zero recipPairWeight_eq_zero W p (Or.inr h0), zero_mul]
  have hgt : B < p.1 ∨ B < p.2 := by
    by_contra hcon
    simp only [not_or, not_lt] at hcon
    exact hp (Finset.mem_product.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h1, hcon.1⟩, hc1⟩,
        Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h2, hcon.2⟩, hc2⟩⟩)
  rcases hgt with hgt | hgt
  · rw [hF _ (le_logx_of_lt_of_rpow_le hx hB hgt)]
    simp
  · rw [hG _ (le_logx_of_lt_of_rpow_le hx hB hgt)]
    simp

/-- **The sieve's finite double sum, cast to `ℂ`, is the `tsum` the interchange consumes.** No
approximation: the `tsum` over all of `ℕ × ℕ` has support inside the sum's index set, so the two
are literally equal. -/
theorem ofReal_pairSumRecip_eq_tsum (W : ℕ) {x β : ℝ} (hx : 1 < x) {F G : ℝ → ℝ}
    (hF : ∀ t, β ≤ t → F t = 0) (hG : ∀ t, β ≤ t → G t = 0) {B : ℕ} (hB : x ^ β ≤ (B : ℝ)) :
    ((pairSumRecip W B x F G : ℝ) : ℂ)
      = ∑' p : ℕ × ℕ, coprimeWeight W recipPairWeight p *
          ((F (Notation.logx x p.1) : ℂ) * (G (Notation.logx x p.2) : ℂ)) := by
  rw [tsum_eq_sum fun p hp ↦ coprimeWeight_recip_mul_profiles_eq_zero hx hF hG hB hp,
    Finset.sum_product, pairSumRecip, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun d' hd' ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_Icc] at hd hd'
  have hcop : Nat.Coprime W (Nat.lcm d d') :=
    (coprime_lcm_iff W d d').2 ⟨hd.2, hd'.2⟩
  rw [coprimeWeight, if_pos hcop, recipPairWeight]
  push_cast
  ring

/-! ## The interchange, applied to the sieve's own sum -/

/-- **The sieve's finite sum equals the kernel integral** — the interchange of
`Gap212.Sieve.Polymath41Fubini` at the coprimality-restricted weight, composed with
`Gap212.Sieve.ofReal_pairSumRecip_eq_tsum`. This is the source's interchange of the Fourier
expansion with the pair sum, applied to the sum `Gap212.Sieve.Polymath41Recip` is about. -/
theorem ofReal_pairSumRecip_eq_integral (W : ℕ) {x β : ℝ} (hx : 1 < x) {F G : ℝ → ℝ}
    (hFd : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) (hGd : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G) (hF : ∀ t, β ≤ t → F t = 0) (hG : ∀ t, β ≤ t → G t = 0)
    {B : ℕ} (hB : x ^ β ≤ (B : ℝ)) :
    ((pairSumRecip W B x F G : ℝ) : ℂ)
      = ∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 *
          coprimeRecipKernel W (kernelArg x w.1) (kernelArg x w.2) := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  rw [ofReal_pairSumRecip_eq_tsum W hx hF hG hB]
  exact tsum_weightPairSum_eq_integral (coprimeWeight_eq_zero recipPairWeight_eq_zero W)
    hFd hFc hGd hGc hx
    (summable_weightMajorant_coprimeWeight W
      (summable_weightMajorant_recipPairWeight (by positivity)))

/-! ## The reduction -/

/-- **`Gap212.Sieve.Polymath41Recip` follows from the asymptotic of its kernel integral.**

The hypothesis is the analytic core of Polymath8b Lemma 4.1 at `k = 1, N = 1`: with
`B_x = (φ(W(x))/W(x))·log x` the source's normalization,

  `B_x · ∫_{ℝ²} f(ξ) g(ξ') K_{W(x)}(ξ,ξ') d(ξ,ξ') ⟶ ∫₀^∞ F'G'`,

where `f = Gap212.Sieve.profileFourier F`, `g = Gap212.Sieve.profileFourier G` and `K_W` is
`Gap212.Sieve.coprimeRecipKernel`, whose Euler product over `p ∤ W` is
`Gap212.Sieve.tprod_localFactorRecip_eq_coprimeRecipKernel`.

Everything *arithmetic* in the `Prop` is discharged here: the truncation at `⌈x^β⌉₊`, the Möbius
weights, the coprimality filter and the passage from a finite real sum to an absolutely convergent
complex one. What is left in the hypothesis is analysis about `ζ` and about the Fourier transforms
of the profiles. -/
theorem polymath41Recip_of_tendsto_integral
    (h : ∀ F G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → ContDiff ℝ (⊤ : ℕ∞) G →
      HasCompactSupport G → ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) → (∀ t, β ≤ t → G t = 0) →
      Tendsto (fun x : ℝ ↦ ((((W x).totient : ℝ) / (W x : ℝ) * Real.log x : ℝ) : ℂ) *
          ∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 *
            coprimeRecipKernel (W x) (kernelArg x w.1) (kernelArg x w.2)) atTop
        (nhds (((∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t : ℝ) : ℂ)))) :
    Polymath41Recip := by
  intro F G hFd hFc hGd hGc β hβ hF hG
  have hcplx := h F G hFd hFc hGd hGc β hβ hF hG
  have hre := (Complex.continuous_re.tendsto
    (((∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t : ℝ) : ℂ))).comp hcplx
  rw [Complex.ofReal_re] at hre
  refine hre.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Function.comp_apply, ← ofReal_pairSumRecip_eq_integral (W x) hx hFd hFc hGd hGc hF hG
    (Nat.le_ceil _), ← Complex.ofReal_mul, Complex.ofReal_re]

end Gap212.Sieve
