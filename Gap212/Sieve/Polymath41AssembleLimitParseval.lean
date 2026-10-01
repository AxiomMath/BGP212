/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssembleLimitDeriv

/-!
# The closing computation of Polymath8b Lemma 4.1: `∫∫ (1+iξ)(1+iξ')/(2+iξ+iξ') f g = ∫₀^∞ F'G'`

Polymath8b (D. H. J. Polymath, *Variants of the Selberg sieve, and bounded intervals containing
many primes*) reduces Lemma 4.1, after the Euler product and the residue, to the identity (at
`k = 1`):

> `∫_ℝ ∫_ℝ (1+iξ)(1+iξ')/(2+iξ+iξ') · f(ξ) g(ξ') dξ dξ' = ∫_0^{+∞} F'(t) G'(t) dt`,

and proves it in two sentences: differentiate the Fourier expansion of `e^tF(t)` under the integral
sign, and apply Fubini. The first sentence is `Gap212.Sieve.ofReal_deriv_eq_integral_profileFourier`
in `Gap212.Sieve.Polymath41AssembleLimitDeriv`; this file is the second, and the identity itself is
`Gap212.Sieve.integral_profileFourier_mul_limitKernel_eq`.

## This is the meeting point of the two obligations, and it mentions neither kernel

`Gap212.Sieve.polymath41Recip_of_tendsto_integral` and
`Gap212.Sieve.polymath41Totient_of_tendsto_integral` each reduce their `Prop` to

  `B_x · ∫_{ℝ²} f(ξ) g(ξ') K_{W(x)}(ξ,ξ') d(ξ,ξ') ⟶ ∫₀^∞ F'G'`,

with `B_x = (φ(W(x))/W(x))·log x` and two *different* kernels `K`. The pole estimate replaces
`B_x·K` by its leading behaviour, which is `Gap212.Sieve.limitKernel` for both kernels alike — that
is the content of the source's kernel asymptotic at `k = 1, N = 1`. What remains after that
replacement is the right-hand side computed here, and **nothing in this file mentions `W`, a kernel,
or `x`**: every statement is about `Gap212.Sieve.profileFourier` of two smooth compactly supported
profiles.

## The hypotheses are exactly the ones the obligations supply, and one of them is not needed

`Gap212.Sieve.Polymath41Recip` and `Gap212.Sieve.Polymath41Totient` quantify over profiles that are
`ContDiff ℝ (⊤ : ℕ∞)`, have compact support, and vanish on `[β,∞)`. The identity below uses the
**first two only**: the vanishing above `β` plays no part, because the Fourier expansion holds at
every real `t` and the domination of the differentiation step and of Fubini comes from the rapid
decay of the transform rather than from the support of the profile. In particular no hypothesis
beyond the three supplied is needed, and `F` is *not* required to vanish on `(-∞,0]` either, even
though the source's profiles live on `[0,+∞)`.

## Normalisation

The source's `ξ` is this repository's `2πξ`, so the source's `1+iξ` is `Gap212.Sieve.limitNum ξ`,
`1+2πiξ`, and the source's denominator `2+iξ+iξ'` is `limitNum ξ + limitNum ξ'`, which
`Gap212.Sieve.limitKernel_apply` records as `2 + 2πi(ξ+ξ')`. The constant `2` is the sum of the two
real parts `1` of `Gap212.Sieve.limitNum`, and it is forced: it is the `2` for which
`∫_{t>0} e^{-t(limitNum ξ + limitNum ξ')} dt` converges and equals `1/(limitNum ξ + limitNum ξ')`
(`Gap212.Sieve.limitNum_add_re`).

## Main definitions

* `Gap212.Sieve.limitKernel`: the source's `(1+iξ)(1+iξ')/(2+iξ+iξ')`, at `ξ_source = 2πξ`.
* `Gap212.Sieve.limitDerivIntegrand`: the integrand of the source's formula for `F'`.

## Main results

* `Gap212.Sieve.limitKernel_apply`: the kernel written out, `2 + 2πi(ξ+ξ')` denominator and all.
* `Gap212.Sieve.integral_profileFourier_mul_limitKernel_eq`: **the source's closing identity.**
* `Gap212.Sieve.integral_profileFourier_mul_div_eq_integral_deriv_mul`: the same with
  `Gap212.Sieve.limitKernel` written out, which is the form the two reductions meet.
* `Gap212.Sieve.tendsto_ofReal_integral_deriv_mul_of_tendsto` and its primed variant: the identity
  as a change of limit value, which is how the two reductions consume it.
-/

@[expose] public section

namespace Gap212.Sieve

open MeasureTheory Real
open scoped FourierTransform ContDiff SchwartzMap

/-! ## The limiting kernel -/

/-- **The source's `(1+iξ)(1+iξ')/(2+iξ+iξ')`**, at `ξ_source = 2πξ`: the leading
behaviour of `B_x · K_{W(x)}(kernelArg x ξ, kernelArg x ξ')` for *either* of the two kernels of
Lemma 4.1, which is why the closing computation is kernel-independent. Written with
`Gap212.Sieve.limitNum` in both numerator and denominator; see `Gap212.Sieve.limitKernel_apply` for
the form the source writes. -/
noncomputable def limitKernel (ξ ξ' : ℝ) : ℂ :=
  limitNum ξ * limitNum ξ' / (limitNum ξ + limitNum ξ')

/-- **The sum of two copies of `Gap212.Sieve.limitNum` has real part `2`.** This is the source's
denominator `2+iξ+iξ'`, and the `2` is what makes `∫_{t>0}e^{-t((1+iξ)+(1+iξ'))}` converge. -/
@[simp]
theorem limitNum_add_re (ξ ξ' : ℝ) : (limitNum ξ + limitNum ξ').re = 2 := by
  rw [Complex.add_re, limitNum_re, limitNum_re]
  norm_num

/-- The denominator of `Gap212.Sieve.limitKernel` never vanishes, its real part being `2`. -/
theorem limitNum_add_ne_zero (ξ ξ' : ℝ) : limitNum ξ + limitNum ξ' ≠ 0 := by
  intro h
  simpa [h] using limitNum_add_re ξ ξ'

/-- **`Gap212.Sieve.limitKernel` written out**: `(1+2πiξ)(1+2πiξ')/(2+2πi(ξ+ξ'))`. The source's
closing display with its `ξ` scaled by `2π`; the `2` in the denominator is the sum of the two
`1`s of the numerators, which is the arithmetic `Gap212.Sieve.limitNum_add_re` records. -/
theorem limitKernel_apply (ξ ξ' : ℝ) :
    limitKernel ξ ξ'
      = (1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ)) * (1 + 2 * (π : ℂ) * Complex.I * (ξ' : ℂ)) /
          (2 + 2 * (π : ℂ) * Complex.I * ((ξ : ℂ) + (ξ' : ℂ))) := by
  rw [limitKernel, limitNum, limitNum]
  congr 1
  ring

/-! ## The integrand of the source's formula for `F'` -/

/-- **The integrand of the source's formula for `F'`**: `(1+2πiξ)·f(ξ)·e^{-t(1+2πiξ)}`, so that
`Gap212.Sieve.ofReal_deriv_eq_integral_profileFourier` reads `F'(t) = -∫_ℝ` of this. -/
noncomputable def limitDerivIntegrand (F : ℝ → ℝ) (t ξ : ℝ) : ℂ :=
  limitNum ξ * profileFourier F ξ * Complex.exp (-((t : ℂ) * limitNum ξ))

/-- `Gap212.Sieve.ofReal_deriv_eq_integral_profileFourier`, phrased with
`Gap212.Sieve.limitDerivIntegrand`. -/
theorem ofReal_deriv_eq_integral_limitDerivIntegrand {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (t : ℝ) :
    ((deriv F t : ℝ) : ℂ) = -∫ ξ : ℝ, limitDerivIntegrand F t ξ :=
  ofReal_deriv_eq_integral_profileFourier hF hFc t

/-- `‖(1+2πiξ)f(ξ)e^{-t(1+2πiξ)}‖ = ‖(1+2πiξ)f(ξ)‖·e^{-t}`: the `t`-dependence of the integrand's
size is a single `e^{-t}`, with no `ξ` in it. This is what makes the dominating function of the
Fubini step below a product of a function of `t` and a function of `(ξ,ξ')`. -/
theorem norm_limitDerivIntegrand (F : ℝ → ℝ) (t ξ : ℝ) :
    ‖limitDerivIntegrand F t ξ‖ = ‖limitNum ξ * profileFourier F ξ‖ * Real.exp (-t) := by
  rw [limitDerivIntegrand, norm_mul, norm_exp_neg_mul_limitNum]

/-- **The product of the two derivatives is a double integral.** Combining
`Gap212.Sieve.ofReal_deriv_eq_integral_profileFourier` for `F` and for `G` — the two minus signs
cancelling — and `MeasureTheory.integral_prod_mul`. -/
theorem ofReal_deriv_mul_eq_integral {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) (t : ℝ) :
    ((deriv F t * deriv G t : ℝ) : ℂ)
      = ∫ w : ℝ × ℝ, limitDerivIntegrand F t w.1 * limitDerivIntegrand G t w.2 := by
  rw [Complex.ofReal_mul, Measure.volume_eq_prod,
    ofReal_deriv_eq_integral_limitDerivIntegrand hF hFc,
    ofReal_deriv_eq_integral_limitDerivIntegrand hG hGc, neg_mul_neg,
    ← integral_prod_mul (fun ξ : ℝ ↦ limitDerivIntegrand F t ξ)
      (fun ξ' : ℝ ↦ limitDerivIntegrand G t ξ')]

/-! ## The `t`-integral, and the domination that licenses exchanging it with `(ξ,ξ')` -/

/-- **The `t`-integral that produces the kernel.** For fixed `(ξ,ξ')`,

  `∫_{t>0} (1+2πiξ)f(ξ)e^{-t(1+2πiξ)}·(1+2πiξ')g(ξ')e^{-t(1+2πiξ')} dt
     = f(ξ)g(ξ')·limitKernel ξ ξ'`,

because the two exponentials combine into `e^{-t(limitNum ξ + limitNum ξ')}`, whose integral over
`(0,∞)` is `1/(limitNum ξ + limitNum ξ')` — the denominator of `Gap212.Sieve.limitKernel`. The
convergence is exactly `Gap212.Sieve.limitNum_add_re`, real part `2 > 0`. -/
theorem integral_Ioi_limitDerivIntegrand_mul (F G : ℝ → ℝ) (w : ℝ × ℝ) :
    ∫ t : ℝ in Set.Ioi (0 : ℝ), limitDerivIntegrand F t w.1 * limitDerivIntegrand G t w.2
      = profileFourier F w.1 * profileFourier G w.2 * limitKernel w.1 w.2 := by
  have hu : limitNum w.1 + limitNum w.2 ≠ 0 := limitNum_add_ne_zero w.1 w.2
  have hre : (-(limitNum w.1 + limitNum w.2)).re < 0 := by
    rw [Complex.neg_re, limitNum_add_re]; norm_num
  have hcongr : ∀ t : ℝ, limitDerivIntegrand F t w.1 * limitDerivIntegrand G t w.2
      = (limitNum w.1 * profileFourier F w.1 * (limitNum w.2 * profileFourier G w.2)) *
        Complex.exp (-(limitNum w.1 + limitNum w.2) * (t : ℂ)) := by
    intro t
    have he : Complex.exp (-(limitNum w.1 + limitNum w.2) * (t : ℂ))
        = Complex.exp (-((t : ℂ) * limitNum w.1)) * Complex.exp (-((t : ℂ) * limitNum w.2)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [limitDerivIntegrand, limitDerivIntegrand, he]
    ring
  simp_rw [hcongr]
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_complex_Ioi hre 0, limitKernel]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

/-- **The domination that licenses Fubini.** The integrand of
`Gap212.Sieve.integral_Ioi_limitDerivIntegrand_mul`, as a function of `(t, (ξ,ξ'))`, is integrable
for the product of `volume.restrict (Ioi 0)` and `volume` on `ℝ × ℝ`.

The dominating function is a product: `e^{-2t}` in `t`, integrable on `(0,∞)`, times
`‖(1+2πiξ)f(ξ)‖·‖(1+2πiξ')g(ξ')‖` in `(ξ,ξ')`, integrable by
`Gap212.Sieve.integrable_limitNum_mul_profileFourier` in each variable. The `e^{-2t}` is where the
real part `2` of `Gap212.Sieve.limitNum_add_re` enters a second time. -/
theorem integrable_uncurry_limitDerivIntegrand_mul {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) :
    Integrable (Function.uncurry fun (t : ℝ) (w : ℝ × ℝ) ↦
        limitDerivIntegrand F t w.1 * limitDerivIntegrand G t w.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure (ℝ × ℝ))) := by
  have hcontnum : Continuous limitNum := by unfold limitNum; fun_prop
  have hcf : Continuous (profileFourier F) := (contDiff_profileFourier hF hFc).continuous
  have hcg : Continuous (profileFourier G) := (contDiff_profileFourier hG hGc).continuous
  have hcont : Continuous (Function.uncurry fun (t : ℝ) (w : ℝ × ℝ) ↦
      limitDerivIntegrand F t w.1 * limitDerivIntegrand G t w.2) := by
    unfold Function.uncurry limitDerivIntegrand
    fun_prop
  have hp : Integrable (fun t : ℝ ↦ Real.exp (-2 * t)) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrableOn_exp_mul_Ioi (by norm_num) 0
  have hq : Integrable (fun w : ℝ × ℝ ↦ ‖limitNum w.1 * profileFourier F w.1‖ *
      ‖limitNum w.2 * profileFourier G w.2‖) (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact Integrable.mul_prod (integrable_limitNum_mul_profileFourier hF hFc).norm
      (integrable_limitNum_mul_profileFourier hG hGc).norm
  refine (hp.mul_prod hq).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z ↦ ?_)
  obtain ⟨t, w⟩ := z
  simp only [Function.uncurry_apply_pair, norm_mul, norm_limitDerivIntegrand]
  rw [show Real.exp (-2 * t) = Real.exp (-t) * Real.exp (-t) by rw [← Real.exp_add]; ring_nf]
  ring_nf
  exact le_refl _

/-! ## The identity -/

/-- **The closing computation of Polymath8b Lemma 4.1** (at `k = 1`): for `F, G` smooth
with compact support,

  `∫_{ℝ²} f(ξ)·g(ξ')·limitKernel ξ ξ' d(ξ,ξ') = ∫_{t>0} F'(t)G'(t) dt`,

with `f = Gap212.Sieve.profileFourier F`, `g = Gap212.Sieve.profileFourier G` and
`Gap212.Sieve.limitKernel ξ ξ' = (1+2πiξ)(1+2πiξ')/(2+2πi(ξ+ξ'))`.

**Kernel-independent, and free of `W` and of `x`.** This is the right-hand side both
`Gap212.Sieve.polymath41Recip_of_tendsto_integral` and
`Gap212.Sieve.polymath41Totient_of_tendsto_integral` must meet: their hypotheses ask for a limit
whose value is `∫₀^∞ F'G'`, and once the pole estimate has replaced `B_x·K_{W(x)}` by
`Gap212.Sieve.limitKernel` this identity is what identifies the surviving Fourier integral with
that value.

**The hypotheses are `ContDiff` and `HasCompactSupport` only.** The vanishing of the profiles on
`[β,∞)` that the two `Prop`s also supply is not used, and no hypothesis beyond what they supply is
needed.

The proof is the source's: substitute `Gap212.Sieve.ofReal_deriv_eq_integral_profileFourier` for
each derivative, exchange the `t`-integral with the `(ξ,ξ')`-integral
(`Gap212.Sieve.integrable_uncurry_limitDerivIntegrand_mul` licenses it), and evaluate the resulting
`t`-integral (`Gap212.Sieve.integral_Ioi_limitDerivIntegrand_mul`). -/
theorem integral_profileFourier_mul_limitKernel_eq {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) :
    ∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 * limitKernel w.1 w.2
      = ((∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t : ℝ) : ℂ) := by
  have h1 : ∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 * limitKernel w.1 w.2
      = ∫ w : ℝ × ℝ, ∫ t : ℝ in Set.Ioi (0 : ℝ),
          limitDerivIntegrand F t w.1 * limitDerivIntegrand G t w.2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun w ↦
      (integral_Ioi_limitDerivIntegrand_mul F G w).symm)
  rw [h1, ← integral_integral_swap (integrable_uncurry_limitDerivIntegrand_mul hF hFc hG hGc),
    ← integral_complex_ofReal]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t ↦
    (ofReal_deriv_mul_eq_integral hF hFc hG hGc t).symm)

/-- **The same identity with `Gap212.Sieve.limitKernel` written out**, which is the shape the two
reductions of Lemma 4.1 meet after their pole estimate:

  `∫_{ℝ²} f(ξ)g(ξ')·(1+2πiξ)(1+2πiξ')/(2+2πi(ξ+ξ')) d(ξ,ξ') = ∫_{t>0} F'(t)G'(t) dt`.

Stated separately so that a consumer needs no definition of this file; it is
`Gap212.Sieve.integral_profileFourier_mul_limitKernel_eq` composed with
`Gap212.Sieve.limitKernel_apply`. -/
theorem integral_profileFourier_mul_div_eq_integral_deriv_mul {F G : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G) :
    ∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 *
        ((1 + 2 * (π : ℂ) * Complex.I * (w.1 : ℂ)) *
            (1 + 2 * (π : ℂ) * Complex.I * (w.2 : ℂ)) /
          (2 + 2 * (π : ℂ) * Complex.I * ((w.1 : ℂ) + (w.2 : ℂ))))
      = ((∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t : ℝ) : ℂ) := by
  rw [← integral_profileFourier_mul_limitKernel_eq hF hFc hG hGc]
  exact integral_congr_ae (Filter.Eventually.of_forall fun w ↦ by simp only [limitKernel_apply])

/-! ## The form the two reductions apply -/

/-- **The identity as a change of limit value.** A family `A : ℝ → ℂ` converging to the Fourier
integral against `Gap212.Sieve.limitKernel` converges to `∫₀^∞ F'G'`.

This is the shape in which the two reductions of Lemma 4.1 consume the closing computation: the
pole estimate shows `B_x·∫_{ℝ²} f g K_{W(x)}` converges to `∫_{ℝ²} f g · limitKernel`, and this
turns that into the hypothesis of `Gap212.Sieve.polymath41Recip_of_tendsto_integral` or of
`Gap212.Sieve.polymath41Totient_of_tendsto_integral`, whose target is `∫₀^∞ F'G'`.

`A` is an arbitrary family, so the statement mentions no kernel, no `W` and no `x`; the caller
supplies `A x = B_x·∫ f g K_{W(x)}` for whichever of the two kernels is its own. -/
theorem tendsto_ofReal_integral_deriv_mul_of_tendsto {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G)
    {A : ℝ → ℂ} (h : Filter.Tendsto A Filter.atTop
      (nhds (∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 * limitKernel w.1 w.2))) :
    Filter.Tendsto A Filter.atTop
      (nhds (((∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t : ℝ) : ℂ))) := by
  rwa [integral_profileFourier_mul_limitKernel_eq hF hFc hG hGc] at h

/-- `Gap212.Sieve.tendsto_ofReal_integral_deriv_mul_of_tendsto` with
`Gap212.Sieve.limitKernel` written out, so that a consumer needs no definition of this file. -/
theorem tendsto_ofReal_integral_deriv_mul_of_tendsto' {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G)
    {A : ℝ → ℂ} (h : Filter.Tendsto A Filter.atTop
      (nhds (∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 *
        ((1 + 2 * (π : ℂ) * Complex.I * (w.1 : ℂ)) *
            (1 + 2 * (π : ℂ) * Complex.I * (w.2 : ℂ)) /
          (2 + 2 * (π : ℂ) * Complex.I * ((w.1 : ℂ) + (w.2 : ℂ))))))) :
    Filter.Tendsto A Filter.atTop
      (nhds (((∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t : ℝ) : ℂ))) := by
  rwa [integral_profileFourier_mul_div_eq_integral_deriv_mul hF hFc hG hGc] at h

end Gap212.Sieve
