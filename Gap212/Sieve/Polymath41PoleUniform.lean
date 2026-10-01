/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41Fourier
public import Gap212.Sieve.Polymath41Pole

/-!
# Step 4b of Polymath8b Lemma 4.1: the pole estimate, uniformly over `|ξ| ≤ √(log x)`

The source's step 4 truncates the `ξ`-integral of step 1 at `|ξ| ≤ √(log x)` and then
uses the pole of `ζ` at `s = 1` *uniformly* over that range. This file is the uniformity, and the
truncation's pointwise justification.

## The one inequality that makes it uniform

Write `Gap212.Sieve.poleArg x ξ = (1 + 2πiξ)/log x` for the exponent shift the sieve produces (the
negation of the exponent appearing in `Gap212.Sieve.ofReal_logx_eq_integral_profileFourier`; the
source's `ξ` is `2π` times this one, as recorded in `Gap212.Sieve.Polymath41Fourier`). Then

  `‖poleArg x ξ‖ ≤ (1 + 2π|ξ|)/log x`   (`Gap212.Sieve.norm_poleArg_le`),

and on the truncation range `|ξ| ≤ √(log x)` the right-hand side is at most
`(1 + 2π√(log x))/log x`, which tends to `0` as `x → ∞` with no reference to `ξ` at all
(`Gap212.Sieve.tendsto_truncBound_log_atTop`). Since the `ε`-`δ` form of the pole estimate,
`Gap212.Sieve.exists_norm_mul_riemannZeta_one_add_sub_one_le`, constrains `s` only through `‖s‖`,
the two combine into

  `Gap212.Sieve.eventually_forall_norm_poleArg_mul_riemannZeta_sub_one_le`:
  for every `ε > 0`, eventually in `x`, *every* `ξ` with `|ξ| ≤ √(log x)` satisfies
  `‖s·ζ(1+s) - 1‖ ≤ ε` at `s = poleArg x ξ`.

That is the source's `1 + o(1)`, uniform in `ξ` over the truncation range. Nothing about the size
of `ζ` on the line `Re s = 1` is used or needed: the whole estimate happens in a shrinking disc
around the pole, where the residue alone controls the product.

## The truncation itself

Discarding `|ξ| > √(log x)` needs the rapid decay of `Gap212.Sieve.profileFourier`
(`Gap212.Sieve.profileFourier_decay`, the source's "rapidly decreasing"). Its pointwise form is
here: `Gap212.Sieve.eventually_forall_norm_profileFourier_tail_le` says that for every `ε > 0`,
eventually in `x`, the transform is smaller than `ε` *everywhere* outside the truncation range. The
bound on the discarded integral is in `Gap212.Sieve.Polymath41CloseLimit`.

## Main definitions

* `Gap212.Sieve.poleArg`: `(1 + 2πiξ)/log x`, the shift at which the pole is met.

## Main results

* `Gap212.Sieve.norm_poleArg_le`: `‖poleArg x ξ‖ ≤ (1 + 2π|ξ|)/log x`.
* `Gap212.Sieve.tendsto_truncBound_log_atTop`: `(1 + 2π√(log x))/log x → 0`.
* `Gap212.Sieve.eventually_forall_norm_poleArg_mul_riemannZeta_sub_one_le`: the uniform `1 + o(1)`.
* `Gap212.Sieve.tendsto_poleArg_mul_riemannZeta`: the same at fixed `ξ`, as a limit in `x`.
* `Gap212.Sieve.eventually_forall_norm_profileFourier_tail_le`: the discarded range is uniformly
  small.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Topology Real

/-! ## The exponent shift, and its modulus -/

/-- **The shift at which Lemma 4.1 meets the pole of `ζ`**: `poleArg x ξ = (1 + 2πiξ)/log x`. It is
the negation of the exponent of `d` in
`Gap212.Sieve.ofReal_logx_eq_integral_profileFourier`, so that the kernel's factor is
`ζ(1 + poleArg x ξ)` rather than `ζ(1 - …)`. -/
noncomputable def poleArg (x ξ : ℝ) : ℂ :=
  (1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ)) / (Real.log x : ℂ)

/-- **The numerator of `Gap212.Sieve.poleArg` never vanishes**: its real part is `1`. This is why
the pole estimate may be applied at all — `riemannZeta_residue_one` lives on the *punctured*
neighbourhood. -/
theorem poleArgNum_ne_zero (ξ : ℝ) : (1 : ℂ) + 2 * (π : ℂ) * Complex.I * (ξ : ℂ) ≠ 0 :=
  fun h ↦ by simpa using congrArg Complex.re h

/-- `poleArg x ξ ≠ 0` for `x > 1`. -/
theorem poleArg_ne_zero {x : ℝ} (hx : 1 < x) (ξ : ℝ) : poleArg x ξ ≠ 0 :=
  div_ne_zero (poleArgNum_ne_zero ξ) (by exact_mod_cast (Real.log_pos hx).ne')

/-- **The modulus of the shift**: `‖poleArg x ξ‖ ≤ (1 + 2π|ξ|)/log x`. The bound depends on `ξ`
only through `|ξ|`, which is what lets one `δ` cover the whole truncation range. -/
theorem norm_poleArg_le {x : ℝ} (hx : 1 < x) (ξ : ℝ) :
    ‖poleArg x ξ‖ ≤ (1 + 2 * π * |ξ|) / Real.log x := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hnum : ‖(1 : ℂ) + 2 * (π : ℂ) * Complex.I * (ξ : ℂ)‖ ≤ 1 + 2 * π * |ξ| :=
    (norm_add_le _ _).trans (by simp [abs_of_pos Real.pi_pos])
  rw [poleArg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlx]
  gcongr

/-! ## The truncation bound tends to zero -/

/-- **`(1 + 2π√L)/L → 0`.** Split as `1/L + 2π/√L`; both halves vanish. This is the whole reason
the truncation `|ξ| ≤ √(log x)` is compatible with the pole estimate: `√(log x)`
grows, but not fast enough to keep `(1 + 2πiξ)/log x` away from `0`. -/
theorem tendsto_truncBound_atTop :
    Tendsto (fun L : ℝ ↦ (1 + 2 * π * Real.sqrt L) / L) atTop (𝓝 0) := by
  have h1 : Tendsto (fun L : ℝ ↦ 1 / L) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero (𝕜 := ℝ)
  have h2 : Tendsto (fun L : ℝ ↦ 2 * π / Real.sqrt L) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds Real.tendsto_sqrt_atTop
  have h := h1.add h2
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
  field_simp
  linear_combination (-2 * π) * hsq

/-- The same at `L = log x`, which is the scale Lemma 4.1 runs at. -/
theorem tendsto_truncBound_log_atTop :
    Tendsto (fun x : ℝ ↦ (1 + 2 * π * Real.sqrt (Real.log x)) / Real.log x) atTop (𝓝 0) :=
  tendsto_truncBound_atTop.comp Real.tendsto_log_atTop

/-! ## The uniform `1 + o(1)` -/

/-- **The source's `1 + o(1)`, uniform over the truncation range**. For
every `ε > 0`, once `x` is large enough, *every* `ξ` with `|ξ| ≤ √(log x)`
satisfies

  `‖s·ζ(1+s) - 1‖ ≤ ε`,  `s = Gap212.Sieve.poleArg x ξ`.

The quantifier order is the point: `x` is chosen before `ξ`, so the estimate is uniform. It holds
because `Gap212.Sieve.exists_norm_mul_riemannZeta_one_add_sub_one_le` constrains `s` through `‖s‖`
alone and `Gap212.Sieve.norm_poleArg_le` bounds that modulus by a quantity free of `ξ` on the
truncation range. -/
theorem eventually_forall_norm_poleArg_mul_riemannZeta_sub_one_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ ξ : ℝ, |ξ| ≤ Real.sqrt (Real.log x) →
      ‖poleArg x ξ * riemannZeta (1 + poleArg x ξ) - 1‖ ≤ ε := by
  obtain ⟨δ, hδ, hmain⟩ := exists_norm_mul_riemannZeta_one_add_sub_one_le hε
  filter_upwards [tendsto_truncBound_log_atTop.eventually (gt_mem_nhds hδ),
    eventually_gt_atTop (1 : ℝ)] with x hx hx1 ξ hξ
  have hlx : 0 < Real.log x := Real.log_pos hx1
  refine hmain _ (poleArg_ne_zero hx1 ξ) (((norm_poleArg_le hx1 ξ).trans ?_).trans hx.le)
  gcongr

/-- **The same at a fixed `ξ`**, as a limit in the scale: `s·ζ(1+s) → 1` along `L → ∞` with
`s = (1 + 2πiξ)/L`. A corollary of `Gap212.Sieve.tendsto_mul_riemannZeta_one_add_div`; it is what
one uses after the `ξ`-integral has been dealt with, and it is strictly weaker than the uniform
statement above. -/
theorem tendsto_poleArg_mul_riemannZeta (ξ : ℝ) :
    Tendsto (fun L : ℝ ↦ ((1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ)) / (L : ℂ)) *
      riemannZeta (1 + (1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ)) / (L : ℂ))) atTop (𝓝 1) :=
  tendsto_mul_riemannZeta_one_add_div (poleArgNum_ne_zero ξ)

/-! ## The discarded range -/

/-- **The truncation discards a uniformly small integrand.** For `F` smooth with compact support
and every `ε > 0`, once `x` is large enough the transform `Gap212.Sieve.profileFourier F` is below
`ε` at *every* `ξ` outside `|ξ| ≤ √(log x)`. This is `Gap212.Sieve.profileFourier_decay` at order
`1`, which gives `‖f ξ‖ ≤ C/(1+|ξ|)`, evaluated at `|ξ| ≥ √(log x) → ∞`.

It is the pointwise half of the source's truncation; the bound on the discarded *integral* is in
`Gap212.Sieve.Polymath41CloseLimit`. -/
theorem eventually_forall_norm_profileFourier_tail_le {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ ξ : ℝ, Real.sqrt (Real.log x) ≤ |ξ| →
      ‖profileFourier F ξ‖ ≤ ε := by
  obtain ⟨C, hC0, hC⟩ := profileFourier_decay hF hFc 1
  have hgrow : Tendsto (fun x : ℝ ↦ C / (1 + Real.sqrt (Real.log x))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ 1 (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
  filter_upwards [hgrow.eventually (gt_mem_nhds hε)] with x hx ξ hξ
  refine le_trans ?_ ((div_le_div_of_nonneg_left hC0 (by positivity)
    (by linarith : 1 + √(log x) ≤ 1 + |ξ|)).trans hx.le)
  rw [le_div_iff₀' (by positivity)]
  simpa using hC ξ

end Gap212.Sieve
