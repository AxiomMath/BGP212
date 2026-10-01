/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41CloseLimit
public import Gap212.Sieve.Polymath41CloseRatio
public import Gap212.Sieve.Polymath41AssembleRecipReduction
public import Gap212.Sieve.Polymath41Carriers

/-!
# Polymath8b Lemma 4.1 for the reciprocal kernel, proved

`Gap212.Sieve.polymath41Recip_of_tendsto_integral` reduced `Gap212.Sieve.Polymath41Recip` to

  `B_x · ∫_{ℝ²} f(ξ) g(ξ') K_{W(x)}(ξ,ξ') d(ξ,ξ') ⟶ ∫₀^∞ F'G'`,   `B_x = (φ(W(x))/W(x))·\log x`,

and this file proves that hypothesis, and with it `Gap212.Sieve.Polymath41Recip` and
`Gap212.Sieve.NuDenominator 45`.

## All that is reciprocal-specific are the two estimates

`Gap212.Sieve.Polymath41CloseLimit` proves the closing limit for an arbitrary normalised
kernel `P`, given a crude bound `‖P‖ ≤ b\log⁴x` and the residue estimate on the truncation range.
This file supplies those two for `P x ξ ξ' = B_x·K_{W(x)}(kernelArg x ξ, kernelArg x ξ')`:

* the crude bound is `Gap212.Sieve.norm_mul_coprimeRecipKernel_le`, at `b = 8`: `‖φ(W)/W‖ ≤ 1`, one
  factor `\log x`, and step 2's `Z(1+1/\log x)³`, which is `≤ 8\log³x` because
  `Gap212.Sieve.tendsto_zetaSeries_one_add_inv_div` says `Z(1+1/L) ~ L`;
* the residue estimate is
  `Gap212.Sieve.eventually_forall_norm_mul_coprimeRecipKernel_sub_limitKernel_le`.

Nothing else about the reciprocal kernel is used, which is what makes
`Gap212.Sieve.Polymath41CloseLimit` serve the totient kernel of the source's closing paragraph as
well.

## Main results

* `Gap212.Sieve.norm_coprimeRecipKernel_le`: step 2's `‖K_W‖ ≤ Z(1+σ)³` with the coprimality
  filter.
* `Gap212.Sieve.norm_mul_coprimeRecipKernel_le`: `‖B_x·K_{W(x)}‖ ≤ 8\log⁴x`, uniformly in `(ξ,ξ')`.
* `Gap212.Sieve.tendsto_mul_integral_coprimeRecipKernel`: the analytic core of Lemma 4.1.
* `Gap212.Sieve.polymath41Recip`: **`Gap212.Sieve.Polymath41Recip`.**
* `Gap212.Sieve.nuDenominator_45`: `Gap212.Sieve.NuDenominator 45`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Gap212.GPY MeasureTheory Real
open scoped ArithmeticFunction.Moebius ContDiff

/-! ## The crude bound for the normalised reciprocal kernel -/

/-- **`‖K_W‖ ≤ Z(1+σ)³`, uniform in the exponents and in `W`** — step 2's bound
(`Gap212.Sieve.norm_recipKernel_le`) with the coprimality restriction, which only removes terms. -/
theorem norm_coprimeRecipKernel_le (W : ℕ) {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ} (hs : s.re = σ)
    (hs' : s'.re = σ) : ‖coprimeRecipKernel W s s'‖ ≤ zetaSeries (1 + σ) ^ 3 := by
  have hsum : Summable (weightMajorant (coprimeWeight W recipPairWeight) σ) :=
    summable_weightMajorant_coprimeWeight W (summable_weightMajorant_recipPairWeight hσ)
  rw [coprimeRecipKernel]
  refine (norm_pairKernel_le_tsum (coprimeWeight_eq_zero recipPairWeight_eq_zero W)
    hsum hs hs').trans ?_
  refine le_trans (Summable.tsum_le_tsum
    (fun p ↦ weightMajorant_coprimeWeight_le W recipPairWeight σ p) hsum
    (summable_weightMajorant_recipPairWeight hσ)) ?_
  rw [tsum_congr fun p ↦ weightMajorant_recipPairWeight σ p]
  exact tsum_pairMajorant_le hσ

/-- `0 ≤ Z(σ)`: every term of the series is nonnegative. -/
theorem zetaSeries_nonneg (σ : ℝ) : 0 ≤ zetaSeries σ :=
  tsum_nonneg fun n ↦ natRpow_neg_nonneg _ n

/-- **`Z(1+1/\log x) ≤ 2\log x` for large `x`** — `Gap212.Sieve.tendsto_zetaSeries_one_add_inv_div`
(`Z(1+1/L) ~ L`) with the constant `2`, which is all the discarded range needs of step 2's
majorant. -/
theorem eventually_zetaSeries_le : ∀ᶠ x : ℝ in atTop,
    zetaSeries (1 + 1 / Real.log x) ≤ 2 * Real.log x := by
  have h := tendsto_zetaSeries_one_add_inv_div.comp Real.tendsto_log_atTop
  filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hlx : 0 < Real.log x := Real.log_pos hx1
  rw [Function.comp_apply, div_lt_iff₀ hlx] at hx
  linarith

/-- **`‖φ(W)/W‖ ≤ 1`**: `Gap212.Sieve.wDensity` is the real number `φ(W)/W` and `φ(W) ≤ W`. -/
theorem norm_wDensity_le_one {W : ℕ} (hW : W ≠ 0) : ‖wDensity W‖ ≤ 1 := by
  rw [wDensity_eq_totient_div hW, norm_div, Complex.norm_natCast, Complex.norm_natCast,
    div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hW)]
  exact_mod_cast Nat.totient_le W

/-- **`‖B_x·K_{W(x)}‖ ≤ 8\log⁴x`**, uniformly in `(ξ,ξ')`: `‖φ(W)/W‖ ≤ 1`, one factor `\log x`, and
step 2's `Z(1+1/\log x)³ ≤ 8\log³x`. This is the only bound available on the range the residue of
`ζ` does not cover, and `Gap212.Sieve.Polymath41CloseLimit` is what makes it enough. -/
theorem norm_mul_coprimeRecipKernel_le {x : ℝ} (hx : 1 < x)
    (hZ : zetaSeries (1 + 1 / Real.log x) ≤ 2 * Real.log x) (ξ ξ' : ℝ) :
    ‖wDensity (W x) * (Real.log x : ℂ) *
        coprimeRecipKernel (W x) (kernelArg x ξ) (kernelArg x ξ')‖
      ≤ 8 * Real.log x ^ 4 := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hK := (norm_coprimeRecipKernel_le (W x) (by positivity : (0 : ℝ) < 1 / Real.log x)
    (kernelArg_re x ξ) (kernelArg_re x ξ')).trans (pow_le_pow_left₀ (zetaSeries_nonneg _) hZ 3)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlx]
  calc _ ≤ 1 * Real.log x * (2 * Real.log x) ^ 3 := by
        gcongr
        exact norm_wDensity_le_one (primorial_pos _).ne'
    _ = 8 * Real.log x ^ 4 := by ring

/-- The crude bound of `Gap212.Sieve.Polymath41CloseLimit`, for the reciprocal kernel at
`b = 8`. -/
theorem eventually_forall_norm_mul_coprimeRecipKernel_le : ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ,
    ‖wDensity (W x) * (Real.log x : ℂ) *
      coprimeRecipKernel (W x) (kernelArg x ξ) (kernelArg x ξ')‖ ≤ 8 * Real.log x ^ 4 := by
  filter_upwards [eventually_zetaSeries_le, eventually_gt_atTop (1 : ℝ)] with x hZ hx1 ξ ξ'
  exact norm_mul_coprimeRecipKernel_le hx1 hZ ξ ξ'

/-! ## The integrand is integrable -/

/-- The normalised reciprocal integrand is integrable for every `x > 1` — the interchange's own
integrability (`Gap212.Sieve.integrable_pairKernel_mul`) times a constant. -/
theorem eventually_integrable_mul_coprimeRecipKernel {F G : ℝ → ℝ} (hFd : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hGd : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) :
    ∀ᶠ x : ℝ in atTop, Integrable fun w : ℝ × ℝ ↦
      profileFourier F w.1 * profileFourier G w.2 *
        (wDensity (W x) * (Real.log x : ℂ) *
          coprimeRecipKernel (W x) (kernelArg x w.1) (kernelArg x w.2)) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx1
  have hσ : (0 : ℝ) < 1 / Real.log x := by have := Real.log_pos hx1; positivity
  have hKint : Integrable fun w : ℝ × ℝ ↦ profileFourier F w.1 * profileFourier G w.2 *
      coprimeRecipKernel (W x) (kernelArg x w.1) (kernelArg x w.2) := by
    simp only [coprimeRecipKernel]
    exact integrable_pairKernel_mul (coprimeWeight_eq_zero recipPairWeight_eq_zero (W x))
      hFd hFc hGd hGc
      (summable_weightMajorant_coprimeWeight (W x) (summable_weightMajorant_recipPairWeight hσ))
  refine (hKint.const_mul (wDensity (W x) * (Real.log x : ℂ))).congr
    (Filter.Eventually.of_forall fun w ↦ ?_)
  ring

/-! ## The analytic core of Lemma 4.1, and `Gap212.Sieve.Polymath41Recip` -/

/-- **The analytic core of Polymath8b Lemma 4.1 for the reciprocal kernel**: for `F, G` smooth with
compact support,

  `(φ(W(x))/W(x))·\log x · ∫_{ℝ²} f(ξ) g(ξ') K_{W(x)}(ξ,ξ') d(ξ,ξ')
     ⟶ ∫_{ℝ²} f(ξ) g(ξ') limitKernel ξ ξ' d(ξ,ξ')`   as `x → ∞`.

This is the hypothesis `Gap212.Sieve.polymath41Recip_of_tendsto_integral` asks for, up to the
closing identity of `Gap212.Sieve.Polymath41AssembleLimitParseval`.

Only two facts about the kernel enter: the crude bound
`Gap212.Sieve.eventually_forall_norm_mul_coprimeRecipKernel_le` and the residue estimate
`Gap212.Sieve.eventually_forall_norm_mul_coprimeRecipKernel_sub_limitKernel_le`. No hypothesis on
the profiles beyond smoothness and compact support is used — in particular the vanishing above `β`
that `Gap212.Sieve.Polymath41Recip` also supplies plays no part. -/
theorem tendsto_mul_integral_coprimeRecipKernel {F G : ℝ → ℝ} (hFd : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hGd : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) :
    Tendsto (fun x : ℝ ↦ ((((W x).totient : ℝ) / (W x : ℝ) * Real.log x : ℝ) : ℂ) *
        ∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 *
          coprimeRecipKernel (W x) (kernelArg x w.1) (kernelArg x w.2)) atTop
      (nhds (∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 * limitKernel w.1 w.2)) := by
  have hmain := tendsto_integral_of_forall_norm_closeDiff_le hFd hFc hGd hGc
    (P := fun x ξ ξ' ↦ wDensity (W x) * (Real.log x : ℂ) *
      coprimeRecipKernel (W x) (kernelArg x ξ) (kernelArg x ξ'))
    (eventually_integrable_mul_coprimeRecipKernel hFd hFc hGd hGc)
    fun ε hε ↦ eventually_forall_norm_closeDiff_le hFd hFc hGd hGc (by norm_num)
      eventually_forall_norm_mul_coprimeRecipKernel_le
      (eventually_forall_norm_mul_coprimeRecipKernel_sub_limitKernel_le hε) hε
  refine hmain.congr' ?_
  filter_upwards with x
  have hW : W x ≠ 0 := (primorial_pos _).ne'
  have hcast : ((((W x).totient : ℝ) / (W x : ℝ) * Real.log x : ℝ) : ℂ)
      = wDensity (W x) * (Real.log x : ℂ) := by
    rw [wDensity_eq_totient_div hW]
    push_cast
    ring
  rw [hcast, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun w ↦ by ring)

/-- **Polymath8b Lemma 4.1 at `k = 1`, `N = 1`, for the reciprocal kernel.**
`Gap212.Sieve.Polymath41Recip`, the `Prop` the denominator asymptotic rests on
(`Gap212.Sieve.nuDenominator_of_polymath41Recip`).

`Gap212.Sieve.polymath41Recip_of_tendsto_integral` discharged everything arithmetic — the
truncation at `⌈x^β⌉₊`, the Möbius weights, the coprimality filter, the passage to an absolutely
convergent complex sum; `Gap212.Sieve.tendsto_ofReal_integral_deriv_mul_of_tendsto` discharged the
closing identity `∫∫ f g·limitKernel = ∫₀^∞ F'G'`; and
`Gap212.Sieve.tendsto_mul_integral_coprimeRecipKernel` is the analytic core between them. -/
theorem polymath41Recip : Polymath41Recip :=
  polymath41Recip_of_tendsto_integral fun _F _G hFd hFc hGd hGc _ _ _ _ ↦
    tendsto_ofReal_integral_deriv_mul_of_tendsto hFd hFc hGd hGc
      (tendsto_mul_integral_coprimeRecipKernel hFd hFc hGd hGc)

/-- **`Gap212.Sieve.NuDenominator 45`**, the denominator asymptotic:
`Gap212.Sieve.nuDenominator_of_polymath41Recip` at the proved `Gap212.Sieve.polymath41Recip`. -/
theorem nuDenominator_45 : NuDenominator 45 :=
  nuDenominator_of_polymath41Recip polymath41Recip 44

end Gap212.Sieve
