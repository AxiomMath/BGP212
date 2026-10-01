/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41Fourier
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The source's `F'(t) = -∫_ℝ (1+iξ)e^{-t(1+iξ)} f(ξ) dξ`

Polymath8b closes the proof of Lemma 4.1 with two sentences:

> But from dividing [the Fourier expansion of `e^tF_j(t)`] by `e^t` and differentiating under the
> integral sign, we have
> `F'_j(t) = - ∫_ℝ (1+iξ) e^{-t(1+iξ)} f_j(ξ) dξ`,
> and the claim then follows from Fubini's theorem.

This file is the first of those two sentences: differentiation under the integral sign in the
display `Gap212.Sieve.ofReal_eq_integral_profileFourier` of `Gap212.Sieve.Polymath41Fourier`.
`Gap212.Sieve.Polymath41AssembleLimitParseval` is the second.

Nothing here mentions `W`, a kernel, or `x`: the statement is about a smooth compactly supported
profile and its transform alone, which is why it is shared by
`Gap212.Sieve.Polymath41Recip` and `Gap212.Sieve.Polymath41Totient` without conflating them.

## Normalisation

The source's `ξ` is this repository's `2πξ` (see the module docstring of
`Gap212.Sieve.Polymath41Fourier`), so the source's factor `1+iξ` is
`Gap212.Sieve.limitNum ξ = 1 + 2πiξ` here, and the source's `e^{-t(1+iξ)}` is
`Complex.exp (-(t · limitNum ξ))`.

## What licenses the differentiation

`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le` needs a dominating function for
the `t`-derivative of the integrand, locally uniformly in `t`. The derivative's modulus is
`‖1+2πiξ‖ · ‖f ξ‖ · e^{-t}`, so the dominating function is `(1+2π|ξ|)‖f ξ‖` up to a constant, and
its integrability is exactly one order of the rapid decay of `f`. That order is taken from the
Schwartz space rather than from `Gap212.Sieve.profileFourier_decay`:
`Gap212.Sieve.exists_schwartzMap_coe_eq_profileFourier` exhibits `f` as a Schwartz function — it is
`𝓕⁻` of one — and `SchwartzMap.integrable_pow_mul` then gives the weighted integrability directly.

## Main definitions

* `Gap212.Sieve.limitNum`: the source's `1+iξ`, at `ξ_source = 2πξ`.

## Main results

* `Gap212.Sieve.exists_schwartzMap_coe_eq_profileFourier`: `Gap212.Sieve.profileFourier F` is a
  Schwartz function.
* `Gap212.Sieve.integrable_limitNum_mul_profileFourier`: `ξ ↦ (1+2πiξ)f(ξ)` is integrable.
* `Gap212.Sieve.ofReal_deriv_eq_integral_profileFourier`: **the source's formula for `F'`.**
-/

@[expose] public section

namespace Gap212.Sieve

open MeasureTheory Real
open scoped FourierTransform ContDiff SchwartzMap

/-! ## The factor `1+iξ` -/

/-- **The source's `1+iξ`**, in this repository's normalisation of the Fourier
transform, where the source's `ξ` is scaled by `2π`. It is the numerator of
`Gap212.Sieve.poleArg x ξ` times `log x`, and the factor that turns a profile into its derivative:
differentiating `F(t) = ∫ f(ξ)e^{-t·limitNum ξ}dξ` in `t` produces one copy of it. -/
noncomputable def limitNum (ξ : ℝ) : ℂ := 1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ)

/-- `Gap212.Sieve.limitNum` has real part `1` — the reason its sum over two variables has real part
`2`, which is the `2` in the denominator of the source's closing display. -/
@[simp]
theorem limitNum_re (ξ : ℝ) : (limitNum ξ).re = 1 := by
  simp [limitNum, Complex.mul_re, Complex.mul_im]

/-- `Gap212.Sieve.limitNum` never vanishes, since its real part is `1`. -/
theorem limitNum_ne_zero (ξ : ℝ) : limitNum ξ ≠ 0 := by
  intro h
  simpa [h] using limitNum_re ξ

/-- `‖1+2πiξ‖ ≤ 1 + 2π|ξ|` — the triangle inequality, and the only size information about
`Gap212.Sieve.limitNum` the domination argument uses. -/
theorem norm_limitNum_le (ξ : ℝ) : ‖limitNum ξ‖ ≤ 1 + 2 * π * |ξ| := by
  refine (norm_add_le _ _).trans_eq ?_
  rw [norm_one]
  congr 1
  simp [abs_of_pos Real.pi_pos]

/-- **The modulus of the source's `e^{-t(1+iξ)}` is `e^{-t}`, with no `ξ` in it.** This is what
makes the dominating function of the differentiation step a function of `ξ` alone. -/
theorem norm_exp_neg_mul_limitNum (t ξ : ℝ) :
    ‖Complex.exp (-((t : ℂ) * limitNum ξ))‖ = Real.exp (-t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [limitNum, Complex.mul_re, Complex.mul_im]

/-! ## `Gap212.Sieve.profileFourier F` as a Schwartz function -/

/-- **`Gap212.Sieve.profileFourier F` is a Schwartz function.** It is `𝓕⁻` of a smooth compactly
supported function, hence `𝓕⁻` of a Schwartz function
(`Gap212.Sieve.exists_schwartzMap_coe_eq`), and the Schwartz space is stable under `𝓕⁻`. Packaged
as an existential, in the style of `Gap212.Sieve.exists_schwartzMap_coe_eq`, so that the Schwartz
API can be applied to the bare function. -/
theorem exists_schwartzMap_coe_eq_profileFourier {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) : ∃ S : 𝓢(ℝ, ℂ), ⇑S = profileFourier F := by
  obtain ⟨S, hS⟩ := exists_schwartzMap_coe_eq (contDiff_expProfile hF)
    (hasCompactSupport_expProfile hFc)
  exact ⟨𝓕⁻ S, by rw [SchwartzMap.fourierInv_coe, hS, profileFourier_def]⟩

/-- **One order of the rapid decay of `Gap212.Sieve.profileFourier F`, in integrable form**:
`ξ ↦ |ξ|·‖f ξ‖` is integrable. This is `SchwartzMap.integrable_pow_mul` at `k = 1`; the pointwise
statement `Gap212.Sieve.profileFourier_decay` would give the same thing at the cost of comparing
with `(1+|ξ|)^{-2}`, and going through the Schwartz space avoids that. -/
theorem integrable_abs_mul_norm_profileFourier {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) :
    Integrable (fun ξ : ℝ ↦ |ξ| * ‖profileFourier F ξ‖) := by
  obtain ⟨S, hS⟩ := exists_schwartzMap_coe_eq_profileFourier hF hFc
  simpa [hS, Real.norm_eq_abs] using S.integrable_pow_mul volume 1

/-- **The dominating function of the differentiation step is integrable**: so is
`ξ ↦ c·(1+2π|ξ|)‖f ξ‖`, for any constant `c`. -/
theorem integrable_const_mul_one_add_mul_norm_profileFourier {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) (c : ℝ) :
    Integrable (fun ξ : ℝ ↦ c * ((1 + 2 * π * |ξ|) * ‖profileFourier F ξ‖)) := by
  refine Integrable.const_mul ?_ c
  have heq : (fun ξ : ℝ ↦ (1 + 2 * π * |ξ|) * ‖profileFourier F ξ‖)
      = fun ξ : ℝ ↦ ‖profileFourier F ξ‖ + 2 * π * (|ξ| * ‖profileFourier F ξ‖) := by
    funext ξ; ring
  rw [heq]
  exact (integrable_profileFourier hF hFc).norm.add
    ((integrable_abs_mul_norm_profileFourier hF hFc).const_mul _)

/-- **`ξ ↦ (1+2πiξ)·f(ξ)` is integrable** — the integrand of the source's formula for `F'` at
`t = 0`, and the function whose product over two variables the Fubini step of
`Gap212.Sieve.Polymath41AssembleLimitParseval` integrates. -/
theorem integrable_limitNum_mul_profileFourier {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) :
    Integrable (fun ξ : ℝ ↦ limitNum ξ * profileFourier F ξ) := by
  have hcont : Continuous fun ξ : ℝ ↦ limitNum ξ * profileFourier F ξ := by
    refine Continuous.mul ?_ (contDiff_profileFourier hF hFc).continuous
    unfold limitNum; fun_prop
  refine (integrable_const_mul_one_add_mul_norm_profileFourier hF hFc 1).mono'
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ ↦ ?_)
  rw [one_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_limitNum_le ξ) (norm_nonneg _)

/-! ## Differentiating under the integral sign -/

/-- **Differentiation under the integral sign in the source's Fourier expansion of `e^tF(t)`.** For
`F` smooth with compact support, `t ↦ F(t)` (complexified) is differentiable at every `t` with
derivative `∫_ℝ -(1+2πiξ)f(ξ)e^{-t(1+2πiξ)}dξ`.

The hypotheses of `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le` are discharged
on the ball `Metric.ball t 1`, where `e^{-s} ≤ e^{1-t}`, against the dominating function
`Gap212.Sieve.integrable_const_mul_one_add_mul_norm_profileFourier`. -/
theorem hasDerivAt_ofReal_profile {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ((F t : ℝ) : ℂ))
      (∫ ξ : ℝ, -(limitNum ξ * profileFourier F ξ *
        Complex.exp (-((t : ℂ) * limitNum ξ)))) t := by
  set Φ : ℝ → ℝ → ℂ := fun t ξ ↦ profileFourier F ξ * Complex.exp (-((t : ℂ) * limitNum ξ))
    with hΦ
  set Φ' : ℝ → ℝ → ℂ := fun t ξ ↦ -(limitNum ξ * profileFourier F ξ *
    Complex.exp (-((t : ℂ) * limitNum ξ))) with hΦ'
  have hcontf : Continuous (profileFourier F) := (contDiff_profileFourier hF hFc).continuous
  have hcontnum : Continuous limitNum := by unfold limitNum; fun_prop
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable (Φ s) volume := fun s ↦
    (hcontf.mul (by fun_prop)).aestronglyMeasurable
  have hmeas' : ∀ s : ℝ, AEStronglyMeasurable (Φ' s) volume := fun s ↦
    ((hcontnum.mul hcontf).mul (by fun_prop)).neg.aestronglyMeasurable
  have hdiff : ∀ ξ s : ℝ, HasDerivAt (Φ · ξ) (Φ' s ξ) s := by
    intro ξ s
    have h0 : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 s := by
      exact_mod_cast Complex.ofRealCLM.hasDerivAt (x := s)
    have h1 : HasDerivAt (fun t : ℝ ↦ -((t : ℂ) * limitNum ξ)) (-(1 * limitNum ξ)) s :=
      (h0.mul_const _).neg
    have h2 := (h1.cexp).const_mul (profileFourier F ξ)
    have h3 : profileFourier F ξ *
          (Complex.exp (-((s : ℂ) * limitNum ξ)) * -(1 * limitNum ξ))
        = -(limitNum ξ * profileFourier F ξ * Complex.exp (-((s : ℂ) * limitNum ξ))) := by
      ring
    rw [h3] at h2
    exact h2
  have hint : Integrable (Φ t) volume := by
    refine ((integrable_profileFourier hF hFc).norm.const_mul (Real.exp (-t))).mono'
      (hmeas t) (Filter.Eventually.of_forall fun ξ ↦ ?_)
    simp only [hΦ, norm_mul, norm_exp_neg_mul_limitNum]
    exact le_of_eq (mul_comm _ _)
  have hbound : ∀ᵐ ξ : ℝ, ∀ s ∈ Metric.ball t 1,
      ‖Φ' s ξ‖ ≤ Real.exp (1 - t) * ((1 + 2 * π * |ξ|) * ‖profileFourier F ξ‖) := by
    refine Filter.Eventually.of_forall fun ξ s hs ↦ ?_
    simp only [hΦ', norm_neg, norm_mul, norm_exp_neg_mul_limitNum]
    have hlt : t - 1 < s := by
      have h := abs_lt.1 (by rw [← Real.dist_eq]; exact Metric.mem_ball.1 hs)
      linarith [h.1]
    calc ‖limitNum ξ‖ * ‖profileFourier F ξ‖ * Real.exp (-s)
        ≤ (1 + 2 * π * |ξ|) * ‖profileFourier F ξ‖ * Real.exp (1 - t) := by
          gcongr
          · exact norm_limitNum_le ξ
          · linarith
      _ = Real.exp (1 - t) * ((1 + 2 * π * |ξ|) * ‖profileFourier F ξ‖) := by ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := Φ) (F' := Φ') (x₀ := t) (μ := volume)
    (bound := fun ξ ↦ Real.exp (1 - t) * ((1 + 2 * π * |ξ|) * ‖profileFourier F ξ‖))
    (Metric.ball_mem_nhds t one_pos) (Filter.Eventually.of_forall hmeas) hint (hmeas' t) hbound
    (integrable_const_mul_one_add_mul_norm_profileFourier hF hFc _)
    (Filter.Eventually.of_forall fun ξ s _ ↦ hdiff ξ s)
  have heq : (fun t : ℝ ↦ ((F t : ℝ) : ℂ)) = fun t : ℝ ↦ ∫ ξ : ℝ, Φ t ξ := funext fun s ↦ by
    have := ofReal_eq_integral_profileFourier hF hFc s
    simpa [hΦ, limitNum] using this
  rw [heq]
  exact key.2

/-- **The source's formula for `F'`**: for `F` smooth with compact support and every `t`,

  `F'(t) = -∫_ℝ (1+2πiξ)·f(ξ)·e^{-t(1+2πiξ)} dξ`,

with `f = Gap212.Sieve.profileFourier F`. The source's `1+iξ` is `1+2πiξ` here because its `ξ` is
this repository's `2πξ`.

The derivative on the left is `deriv F`, the real derivative of the real profile, complexified; the
identity is obtained by matching the two derivatives of `t ↦ (F t : ℂ)` given by
`HasDerivAt.ofReal_comp` and by `Gap212.Sieve.hasDerivAt_ofReal_profile`. -/
theorem ofReal_deriv_eq_integral_profileFourier {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (t : ℝ) :
    ((deriv F t : ℝ) : ℂ)
      = -∫ ξ : ℝ, limitNum ξ * profileFourier F ξ *
          Complex.exp (-((t : ℂ) * limitNum ξ)) := by
  have hd : HasDerivAt F (deriv F t) t :=
    ((hF.differentiable (by norm_num)) t).hasDerivAt
  have h1 := hd.ofReal_comp
  have h2 := hasDerivAt_ofReal_profile hF hFc t
  rw [← integral_neg]
  exact h1.unique h2

end Gap212.Sieve
