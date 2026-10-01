/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssemblePoleTail
public import Gap212.Sieve.Polymath41PoleUniform
public import Gap212.Sieve.WSieve
public import Gap212.Sieve.GramRiemannSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Every factor of the Euler-factor estimate is `1 + o(1)`, uniformly over `|ξ| ≤ √(log x)`

`Gap212.Sieve.coprimeRecipKernel_eq_zeta_quotient_mul` writes the sieve's kernel as a product of
seven factors: three `ζ`-values, three `W`-products, and the correction. Multiplied by the
normalisation `B_x` the whole thing is `Gap212.Sieve.limitKernel ξ ξ'` times a quotient of *seven*
quantities, each of which the source asserts to be `1+o(1)`. This file proves each of the seven,
uniformly over the truncation range `|ξ|, |ξ'| ≤ √(log x)`, and supplies the two elementary
inequalities that let seven such bounds be multiplied.

## The three `ζ`-factors

`Gap212.Sieve.Polymath41PoleUniform` already gives
`‖s·ζ(1+s) - 1‖ ≤ ε` uniformly for `s = Gap212.Sieve.poleArg x ξ` with `|ξ| ≤ √(log x)`, and
`Gap212.Sieve.poleArg x ξ` **is** `Gap212.Sieve.kernelArg x ξ`, by definition. What is not covered
there is the *third* exponent `s + s'`, whose numerator has real part `2` rather than `1` and so is
not `poleArg x ξ''` for any real `ξ''`. It is covered here
(`Gap212.Sieve.eventually_forall_norm_kernelArgAdd_mul_riemannZeta_sub_one_le`) by going back to the
`ε`-`δ` form `Gap212.Sieve.exists_norm_mul_riemannZeta_one_add_sub_one_le`, whose hypothesis
constrains `s` only through `‖s‖`.

## The three `W`-factors

`Gap212.Sieve.norm_wTwistedProduct_div_sub_one_le'` bounds `‖w(t)/(φ(W)/W) - 1‖` by
`exp(2‖t‖·ellV W) - 1`, so what the `W`-factors need is `‖t‖·ellV(W(x)) → 0`. That follows from
`Gap212.Sieve.W_le_log` (`W(x) ≤ log x`) and `Gap212.Sieve.ellV_le_log`
(`ellV m ≤ log m`), giving `ellV(W(x)) ≤ log log x` — together with `‖t‖ = O((1+√(log x))/log x)`.
The resulting limit is `Gap212.Sieve.tendsto_truncBound_mul_logLog_atTop`.

One statement covers all three `W`-factors at once, because it is quantified over `t` with only a
bound on `‖t‖`, and `‖s‖, ‖s'‖, ‖s+s'‖` are all at most twice the same quantity.

## The seventh factor

The correction product is `Gap212.Sieve.eventually_forall_norm_tprod_coprimeKpError_sub_one_le`,
from `Gap212.Sieve.Polymath41AssemblePoleTail`, and it needs only `Re s ≥ 0`.

## Multiplying seven bounds

`Gap212.Sieve.norm_mul_sub_one_le_three_mul`: `‖a-1‖, ‖b-1‖ ≤ d ≤ 1` gives `‖ab-1‖ ≤ 3d`, and
`Gap212.Sieve.norm_inv_sub_one_le`: `‖a-1‖ ≤ d ≤ 1/2` gives `‖a⁻¹-1‖ ≤ 2d`. Six applications of the
first turn seven factors within `d` of `1` into a product within `3⁶d` of `1`; the second is what
puts the four denominators on the same footing as the three numerators. The constants are
deliberately crude — the statement proved is that a *limit* is `1`, so any constant will do.

## Main results

* `Gap212.Sieve.norm_mul_sub_one_le_three_mul`, `Gap212.Sieve.norm_inv_sub_one_le`: the two
  elementary inequalities.
* `Gap212.Sieve.eventually_forall_norm_kernelArgAdd_mul_riemannZeta_sub_one_le`: the third
  `ζ`-factor, at the exponent `s + s'`.
* `Gap212.Sieve.tendsto_truncBound_mul_logLog_atTop`: `((1+2π√(log x))/log x)·log log x → 0`.
* `Gap212.Sieve.eventually_forall_norm_wTwistedProduct_div_sub_one_le`: the `W`-factors, uniformly
  in `t` with `‖t‖` on the truncation scale.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY Real
open scoped ArithmeticFunction.Moebius

/-! ## Multiplying "within `d` of `1`" bounds -/

/-- **`‖a-1‖, ‖b-1‖ ≤ d ≤ 1` gives `‖ab-1‖ ≤ 3d`.** From `ab-1 = (a-1)(b-1)+(a-1)+(b-1)`, so the
bound is `d² + 2d ≤ 3d`. The constant `3` is crude on purpose: it is applied six times and the
conclusion is only that a limit is `1`. -/
theorem norm_mul_sub_one_le_three_mul {a b : ℂ} {d : ℝ} (hd : d ≤ 1) (ha : ‖a - 1‖ ≤ d)
    (hb : ‖b - 1‖ ≤ d) : ‖a * b - 1‖ ≤ 3 * d := by
  have h := norm_add₃_le (a := (a - 1) * (b - 1)) (b := a - 1) (c := b - 1)
  rw [norm_mul, show (a - 1) * (b - 1) + (a - 1) + (b - 1) = a * b - 1 by ring] at h
  nlinarith [norm_nonneg (a - 1), norm_nonneg (b - 1)]

/-- **`‖a-1‖ ≤ d ≤ 1/2` gives `‖a⁻¹-1‖ ≤ 2d`.** The modulus of `a` is at least `1 - d ≥ 1/2`, so
`‖a⁻¹ - 1‖ = ‖1-a‖/‖a‖ ≤ d/(1-d) ≤ 2d`. This is what lets the four denominators of the display be
treated exactly like its three numerators. -/
theorem norm_inv_sub_one_le {a : ℂ} {d : ℝ} (hd : d ≤ 1 / 2) (ha : ‖a - 1‖ ≤ d) :
    ‖a⁻¹ - 1‖ ≤ 2 * d := by
  have hlow : 1 / 2 ≤ ‖a‖ := by
    have h := norm_sub_norm_le (1 : ℂ) a
    rw [norm_one, norm_sub_rev] at h
    linarith
  have ha0 : a ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [show a⁻¹ - 1 = (1 - a) / a by field_simp, norm_div, norm_sub_rev,
    div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (a - 1)]

/-! ## The third `ζ`-factor, at the exponent `s + s'` -/

/-- `(kernelArg x ξ + kernelArg x ξ').re = 2/log x`, so the sum is nonzero for `x > 1`. -/
theorem kernelArgAdd_ne_zero {x : ℝ} (hx : 1 < x) (ξ ξ' : ℝ) :
    kernelArg x ξ + kernelArg x ξ' ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [Complex.add_re, kernelArg_re, kernelArg_re, Complex.zero_re] at hre
  linarith [one_div_pos.mpr (Real.log_pos hx)]

/-- `‖kernelArg x ξ + kernelArg x ξ'‖ ≤ 2·(1+2π√(log x))/log x` on the truncation range. -/
theorem norm_kernelArgAdd_le {x : ℝ} (hx : 1 < x) {ξ ξ' : ℝ}
    (hξ : |ξ| ≤ Real.sqrt (Real.log x)) (hξ' : |ξ'| ≤ Real.sqrt (Real.log x)) :
    ‖kernelArg x ξ + kernelArg x ξ'‖
      ≤ 2 * ((1 + 2 * π * Real.sqrt (Real.log x)) / Real.log x) := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  refine (norm_add_le _ _).trans ?_
  rw [two_mul]
  gcongr <;> exact (norm_poleArg_le hx _).trans (by gcongr)

/-- **The third `ζ`-factor of the display is `1 + o(1)`, uniformly over the truncation range.** The
exponent `s + s'` is not of the form `Gap212.Sieve.poleArg x ξ''` — its numerator has real part
`2` — so this goes back to the `ε`-`δ` form of the pole estimate, whose hypothesis constrains the
exponent only through its modulus. -/
theorem eventually_forall_norm_kernelArgAdd_mul_riemannZeta_sub_one_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ, |ξ| ≤ Real.sqrt (Real.log x) →
      |ξ'| ≤ Real.sqrt (Real.log x) →
      ‖(kernelArg x ξ + kernelArg x ξ') *
        riemannZeta (1 + (kernelArg x ξ + kernelArg x ξ')) - 1‖ ≤ ε := by
  obtain ⟨δ, hδ, hmain⟩ := exists_norm_mul_riemannZeta_one_add_sub_one_le hε
  filter_upwards [(tendsto_truncBound_log_atTop.const_mul 2).eventually
    (gt_mem_nhds (by rwa [mul_zero])), eventually_gt_atTop (1 : ℝ)] with x hx hx1 ξ ξ' hξ hξ'
  exact hmain _ (kernelArgAdd_ne_zero hx1 ξ ξ')
    ((norm_kernelArgAdd_le hx1 hξ hξ').trans hx.le)

/-! ## The `W`-factors -/

/-- **`log L/L → 0` and `log L/√L → 0`, combined**: `((1+2π√L)/L)·log L → 0`. -/
theorem tendsto_truncBound_mul_log_atTop :
    Tendsto (fun L : ℝ ↦ (1 + 2 * π * Real.sqrt L) / L * Real.log L) atTop (nhds 0) := by
  have h1 : Tendsto (fun L : ℝ ↦ Real.log L / L) atTop (nhds 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun L : ℝ ↦ Real.log L / Real.sqrt L) atTop (nhds 0) := by
    have hc := (h1.comp Real.tendsto_sqrt_atTop).const_mul (2 : ℝ)
    rw [mul_zero] at hc
    refine hc.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    rw [Function.comp_apply, Real.log_sqrt hL]
    ring
  have hsum := h1.add (h2.const_mul (2 * π))
  simp only [mul_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  obtain ⟨r, hr0, hrL⟩ : ∃ r : ℝ, 0 < r ∧ L = r * r :=
    ⟨Real.sqrt L, Real.sqrt_pos.2 hL, (Real.mul_self_sqrt hL.le).symm⟩
  rw [hrL, Real.sqrt_mul_self hr0.le]
  field_simp

/-- **`((1+2π√(log x))/log x)·log log x → 0`.** At `m = W(x)` the error exponent of
`Gap212.Sieve.norm_wTwistedProduct_div_sub_one_le'` is `2‖s‖·ellV(W(x))`, and
`ellV(W(x)) ≤ log log x`. -/
theorem tendsto_truncBound_mul_logLog_atTop :
    Tendsto (fun x : ℝ ↦ (1 + 2 * π * Real.sqrt (Real.log x)) / Real.log x *
      Real.log (Real.log x)) atTop (nhds 0) :=
  tendsto_truncBound_mul_log_atTop.comp Real.tendsto_log_atTop

/-- **The `W`-factors of the display are `1 + o(1)`, uniformly in the exponent.** For every
`ε > 0`, once `x` is large enough, *every* `t` with `‖t‖ ≤ 2(1+2π√(log x))/log x` satisfies

  `‖w(t)/(φ(W(x))/W(x)) - 1‖ ≤ ε`,   `w(t) = Gap212.Sieve.wTwistedProduct (W x) t`.

One statement serves all three exponents `s`, `s'`, `s+s'` of the display, since all three have
modulus at most that bound. Both hypotheses of
`Gap212.Sieve.norm_wTwistedProduct_div_sub_one_le'` are discharged from
`Gap212.Sieve.W_le_log` and `Gap212.Sieve.ellV_le_log`, which give `ellV(W(x)) ≤ log(W(x)) ≤
log log x`. -/
theorem eventually_forall_norm_wTwistedProduct_div_sub_one_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℂ,
      ‖t‖ ≤ 2 * ((1 + 2 * π * Real.sqrt (Real.log x)) / Real.log x) →
      ‖wTwistedProduct (W x) t / wDensity (W x) - 1‖ ≤ ε := by
  have hβ0 : Tendsto (fun x ↦ 4 * ((1 + 2 * π * √(log x)) / log x * log (log x))) atTop
      (nhds 0) := by
    simpa using tendsto_truncBound_mul_logLog_atTop.const_mul (4 : ℝ)
  have hexp := ((Real.continuous_exp.tendsto 0).comp hβ0).sub_const 1
  rw [Real.exp_zero, sub_self] at hexp
  filter_upwards [hexp.eventually (gt_mem_nhds hε), hβ0.eventually (gt_mem_nhds one_pos),
    W_le_log, eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (0 : ℝ)]
    with x hxε hxβ hWL hx1 hllx t ht
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hW0 : 0 < W x := primorial_pos _
  have hlogW : Real.log (W x) ≤ Real.log (Real.log x) :=
    Real.log_le_log (by exact_mod_cast hW0) hWL
  have hlogW0 : 0 ≤ Real.log (W x) := Real.log_nonneg (by exact_mod_cast hW0)
  have h1 := mul_le_mul ht ((ellV_le_log hW0).trans hlogW) (PrimeGaps.ellV_nonneg _)
    (by positivity)
  have h2 := mul_le_mul ht hlogW hlogW0 (by positivity)
  refine (norm_wTwistedProduct_div_sub_one_le' hW0.ne' (by nlinarith)).trans ?_
  have := Real.exp_le_exp.2 (show 2 * ‖t‖ * PrimeGaps.ellV (W x)
    ≤ 4 * ((1 + 2 * π * √(log x)) / log x * log (log x)) by nlinarith)
  simp only [Function.comp_apply] at hxε
  linarith

end Gap212.Sieve
