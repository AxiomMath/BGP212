/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41CloseRecip
public import Gap212.Sieve.Polymath41AssembleTotientReduction
public import Gap212.Sieve.Polymath41AssembleTotientEstimate

/-!
# Polymath8b Lemma 4.1 for the totient kernel, proved

The source's Lemma 4.1 ends with one sentence about the totient kernel: "the only change … is
that the `1/p` term in [`K_p`] is replaced by `1/(p-1)`; but this modification may be absorbed into
the `1+O(1/p²)` factor in [the Euler-factor estimate]". This file is that sentence, carried out, and
with it `Gap212.Sieve.Polymath41Totient` and `Gap212.Sieve.NumeratorAsymptotic 44`.

## The absorption, named

`Gap212.Sieve.kpErrorTotient p u v = K^φ_p·(1-uv/p)/((1-u/p)(1-v/p))` is the totient kernel's own
Euler-factor correction: the factor by which its Euler factor differs from the `ζ`-quotient. It is
within `64/p²` of `1` (`Gap212.Sieve.norm_kpErrorTotient_cpow_sub_one_le`), and the proof is
exactly the source's sentence — the difference from the reciprocal correction is
`(K^φ_p - K_p)(1-uv/p)/((1-u/p)(1-v/p))`, which
`Gap212.Sieve.norm_localFactorTotient_sub_localFactorRecip_cpow_le` bounds by `6/p²` times a factor
at most `8`, and the reciprocal correction is itself within `16/p²` of `1`.

From there **nothing is specific to the totient kernel**:

* `Gap212.Sieve.eq_zeta_quotient_mul_of_hasProd` is already stated at an arbitrary local-factor and
  error family, so it gives the Euler-factor estimate for `Gap212.Sieve.coprimeTotientKernel`;
* `Gap212.Sieve.mul_kernel_eq_limitKernel_mul_closeRatio` and
  `Gap212.Sieve.eventually_forall_norm_mul_kernel_sub_limitKernel_le` are stated at an arbitrary
  correction, so the residue estimate follows with the same six other factors;
* `Gap212.Sieve.eventually_forall_norm_tprod_coprimeRestrict_sub_one_le` is stated at an arbitrary
  error family, so the correction product tends to `1` along `W(x)`;
* `Gap212.Sieve.tendsto_integral_of_forall_norm_closeDiff_le` is stated at an arbitrary normalised
  kernel, so the closing limit follows from the residue estimate and the crude bound.

The one place the totient kernel costs something is the crude bound: its majorant
`Gap212.Sieve.norm_coprimeTotientKernel_le_sharp` carries an absolute constant `Z(2)⁶` that the
reciprocal kernel's does not, so `b = 8·Z(2)⁶` instead of `b = 8`. The closing limit does not care
which constant it is.

## Main definitions

* `Gap212.Sieve.kpErrorTotient`, `Gap212.Sieve.coprimeKpErrorTotient`: the totient kernel's
  Euler-factor correction, and the same with the primes dividing `W` neutralised.

## Main results

* `Gap212.Sieve.norm_kpErrorTotient_cpow_sub_one_le`: **the absorption**, `‖E^φ_p - 1‖ ≤ 64/p²`.
* `Gap212.Sieve.coprimeTotientKernel_eq_zeta_quotient_mul`: the Euler-factor estimate for the
  totient kernel.
* `Gap212.Sieve.tendsto_mul_integral_coprimeTotientKernel`: the analytic core of Lemma 4.1.
* `Gap212.Sieve.polymath41Totient`: **`Gap212.Sieve.Polymath41Totient`.**
* `Gap212.Sieve.numeratorAsymptotic_44`: `Gap212.Sieve.NumeratorAsymptotic 44`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Gap212.GPY MeasureTheory Real
open scoped ArithmeticFunction.Moebius ContDiff

/-! ## The reciprocal correction as a quotient -/

/-- **The reciprocal kernel's Euler-factor identity, uncleared**:
`K_p·(1-uv/p) = (1-u/p)(1-v/p)·E_p`. `Gap212.Sieve.localFactorRecip_mul_one_sub` with the error
written as `Gap212.Sieve.kpError`, which is what `Gap212.Sieve.mul_one_sub_div_eq_sub` converts
between. -/
theorem localFactorRecip_mul_one_sub_eq_mul_kpError {p u v : ℂ} (hp : p ≠ 0)
    (hA : 1 - u / p ≠ 0) (hB : 1 - v / p ≠ 0) :
    localFactorRecip p u v * (1 - u * v / p)
      = (1 - u / p) * (1 - v / p) * kpError p u v := by
  rw [localFactorRecip_mul_one_sub hp, kpError]
  exact (mul_one_sub_div_eq_sub hA hB (pow_ne_zero 2 hp)).symm

/-! ## The totient correction -/

/-- **The totient kernel's Euler-factor correction**: the factor by which its Euler factor differs
from the `ζ`-quotient,

  `kpErrorTotient p u v = K^φ_p(u,v)·(1-uv/p)/((1-u/p)(1-v/p))`.

Defined as the quotient, so that the cleared identity
`Gap212.Sieve.localFactorTotient_mul_one_sub_eq_mul_kpErrorTotient` is a field computation and the
whole content is the *bound* `Gap212.Sieve.norm_kpErrorTotient_cpow_sub_one_le`, which is the
source's "may be absorbed into the `1+O(1/p²)` factor". -/
noncomputable def kpErrorTotient (p u v : ℂ) : ℂ :=
  localFactorTotient p u v * (1 - u * v / p) / ((1 - u / p) * (1 - v / p))

/-- **The totient kernel's Euler-factor identity, cleared**:
`K^φ_p·(1-uv/p) = (1-u/p)(1-v/p)·E^φ_p`. -/
theorem localFactorTotient_mul_one_sub_eq_mul_kpErrorTotient {p u v : ℂ} (hA : 1 - u / p ≠ 0)
    (hB : 1 - v / p ≠ 0) :
    localFactorTotient p u v * (1 - u * v / p)
      = (1 - u / p) * (1 - v / p) * kpErrorTotient p u v := by
  rw [kpErrorTotient]
  field_simp

/-- **`‖1 - uv/p‖ ≤ 2` for `‖u‖, ‖v‖ ≤ 1` and `p ≥ 2`** — the numerator of
`Gap212.Sieve.kpErrorTotient`, bounded crudely. -/
theorem norm_one_sub_mul_div_le {p : ℕ} (hp : 2 ≤ p) {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖1 - u * v / (p : ℂ)‖ ≤ 2 := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (by lia : 1 ≤ p)
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_div, norm_mul, Complex.norm_natCast]
  linarith [div_le_one_of_le₀ ((mul_le_one₀ hu (norm_nonneg v) hv).trans hpR) (by positivity)]

/-- **The absorption of the source's closing sentence, quantified.** For every prime `p` and
exponents with nonnegative real part,

  `‖kpErrorTotient p (p^{-s}) (p^{-s'}) - 1‖ ≤ 64/p²`.

Two steps and no more: the difference from the reciprocal correction is
`(K^φ_p - K_p)(1-uv/p)/((1-u/p)(1-v/p))`, whose numerator
`Gap212.Sieve.norm_localFactorTotient_sub_localFactorRecip_cpow_le` bounds by `6/p²` times at most
`2` and whose denominator `Gap212.Sieve.half_le_norm_one_sub_div` bounds below by `1/4`, giving
`48/p²`; and the reciprocal correction is within `16/p²` of `1`
(`Gap212.Sieve.norm_kpError_cpow_sub_one_le`). The constant `64` is crude on purpose — all that is
used of it downstream is that `∑_p 64/p²` converges. -/
theorem norm_kpErrorTotient_cpow_sub_one_le (p : Nat.Primes) {s s' : ℂ} (hs : 0 ≤ s.re)
    (hs' : 0 ≤ s'.re) :
    ‖kpErrorTotient ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s')) - 1‖
      ≤ 64 / ((p : ℕ) : ℝ) ^ 2 := by
  set u : ℂ := ((p : ℕ) : ℂ) ^ (-s)
  set v : ℂ := ((p : ℕ) : ℂ) ^ (-s')
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hu : ‖u‖ ≤ 1 := norm_natCast_cpow_neg_le_one p.2.one_lt.le hs
  have hv : ‖v‖ ≤ 1 := norm_natCast_cpow_neg_le_one p.2.one_lt.le hs'
  have hA := half_le_norm_one_sub_div hp2 hu
  have hB := half_le_norm_one_sub_div hp2 hv
  have hAne : (1 : ℂ) - u / ((p : ℕ) : ℂ) ≠ 0 := norm_pos_iff.1 (by linarith)
  have hBne : (1 : ℂ) - v / ((p : ℕ) : ℂ) ≠ 0 := norm_pos_iff.1 (by linarith)
  have hDlow : (1 : ℝ) / 4 ≤ ‖(1 - u / ((p : ℕ) : ℂ)) * (1 - v / ((p : ℕ) : ℂ))‖ := by
    rw [norm_mul]; nlinarith
  have step : ‖kpErrorTotient ((p : ℕ) : ℂ) u v - kpError ((p : ℕ) : ℂ) u v‖
      ≤ 48 / ((p : ℕ) : ℝ) ^ 2 := by
    rw [kpErrorTotient, ← mul_div_cancel_left₀ (kpError _ u v) (mul_ne_zero hAne hBne),
      ← localFactorRecip_mul_one_sub_eq_mul_kpError (Nat.cast_ne_zero.2 p.2.ne_zero) hAne hBne,
      div_sub_div_same, ← sub_mul, norm_div, norm_mul, div_le_iff₀ (by linarith)]
    have hL : ‖localFactorTotient _ u v - localFactorRecip _ u v‖ ≤ 6 / ((p : ℕ) : ℝ) ^ 2 :=
      norm_localFactorTotient_sub_localFactorRecip_cpow_le p.2 hs hs'
    have := mul_le_mul hL (norm_one_sub_mul_div_le hp2 hu hv) (norm_nonneg _) (by positivity)
    have := mul_le_mul_of_nonneg_left hDlow (by positivity : (0 : ℝ) ≤ 48 / ((p : ℕ) : ℝ) ^ 2)
    linarith [show (6 : ℝ) / ((p : ℕ) : ℝ) ^ 2 * 2 = 48 / ((p : ℕ) : ℝ) ^ 2 * (1 / 4) by ring]
  calc _ ≤ _ := norm_sub_le_norm_sub_add_norm_sub _ (kpError ((p : ℕ) : ℂ) u v) _
    _ ≤ 48 / ((p : ℕ) : ℝ) ^ 2 + 16 / ((p : ℕ) : ℝ) ^ 2 :=
      add_le_add step (norm_kpError_cpow_sub_one_le p hs hs')
    _ = 64 / ((p : ℕ) : ℝ) ^ 2 := by ring

/-! ## The restricted correction, and its product -/

/-- **The totient kernel's correction restricted to `p ∤ W`** — the source's `∏_{p ∤ W}(1+O(1/p²))`
for the totient kernel, written as a product over all primes through
`Gap212.Sieve.coprimeRestrict`, which is what lets the generic tail estimate of
`Gap212.Sieve.Polymath41AssemblePoleTail` apply unchanged. -/
noncomputable def coprimeKpErrorTotient (W : ℕ) (s s' : ℂ) : Nat.Primes → ℂ :=
  coprimeRestrict W fun p ↦
    kpErrorTotient ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s'))

/-- `∏_{p ∤ W} E^φ_p` converges, the majorant being the summable `64/p²`. -/
theorem multipliable_coprimeKpErrorTotient (W : ℕ) {s s' : ℂ} (hs : 0 ≤ s.re) (hs' : 0 ≤ s'.re) :
    Multipliable (coprimeKpErrorTotient W s s') :=
  multipliable_coprimeRestrict W (b := fun p : Nat.Primes ↦ 64 / ((p : ℕ) : ℝ) ^ 2)
    (fun p ↦ by positivity) (summable_const_div_prime_sq 64)
    fun p ↦ norm_kpErrorTotient_cpow_sub_one_le p hs hs'

/-- **The totient correction product tends to `1` along `W(x)`, uniformly in the exponents** — the
generic tail estimate at the family of `Gap212.Sieve.kpErrorTotient`. -/
theorem eventually_forall_norm_tprod_coprimeKpErrorTotient_sub_one_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ s s' : ℂ, 0 ≤ s.re → 0 ≤ s'.re →
      ‖(∏' p : Nat.Primes, coprimeKpErrorTotient (W x) s s' p) - 1‖ ≤ ε :=
  eventually_forall_norm_tprod_coprimeRestrict_sub_one_le
    (E := fun (s s' : ℂ) (p : Nat.Primes) ↦
      kpErrorTotient ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s')))
    (b := fun p : Nat.Primes ↦ 64 / ((p : ℕ) : ℝ) ^ 2) (fun p ↦ by positivity)
    (summable_const_div_prime_sq 64)
    (fun s s' hs hs' p ↦ norm_kpErrorTotient_cpow_sub_one_le p hs hs') hε

/-! ## The Euler-factor estimate for the totient kernel -/

/-- **The cleared per-prime identity for the totient kernel**, with the convention that all four
factors are `1` at `p ∣ W`. The totient companion of
`Gap212.Sieve.coprimeLocalFactor_mul_coprimeFactor`, and the same proof: clear the `cpow`
bookkeeping with `Gap212.Sieve.primeCpow_div_eq` and apply the field identity. -/
theorem coprimeLocalFactorTotient_mul_coprimeFactor (W : ℕ) {s s' : ℂ} (hs : 0 < s.re)
    (hs' : 0 < s'.re) (p : Nat.Primes) :
    (if (p : ℕ) ∣ W then 1
        else localFactorTotient ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s'))) *
        coprimeFactor W (1 + (s + s')) p
      = coprimeFactor W (1 + s) p * coprimeFactor W (1 + s') p *
          coprimeKpErrorTotient W s s' p := by
  by_cases hdvd : (p : ℕ) ∣ W
  · simp only [coprimeFactor, coprimeKpErrorTotient, coprimeRestrict, if_pos hdvd, mul_one]
  simp only [coprimeFactor, coprimeKpErrorTotient, coprimeRestrict, if_neg hdvd]
  rw [← primeCpow_mul_div_eq p s s', ← primeCpow_div_eq p s, ← primeCpow_div_eq p s']
  refine localFactorTotient_mul_one_sub_eq_mul_kpErrorTotient ?_ ?_ <;> rw [primeCpow_div_eq] <;>
    exact one_sub_primeCpow_ne_zero (by rw [Complex.add_re, Complex.one_re]; linarith) p

/-- The totient Euler product of `Gap212.Sieve.Polymath41AssembleTotientCoprime` in `HasProd`
form, which is what lets it be multiplied by other convergent products. -/
theorem hasProd_coprimeLocalFactorTotient (W : ℕ) {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ} (hs : s.re = σ)
    (hs' : s'.re = σ) :
    HasProd (fun p : Nat.Primes ↦ if (p : ℕ) ∣ W then 1
        else localFactorTotient ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s')))
      (coprimeTotientKernel W s s') := by
  convert (isMultiplicative_restrictCoprime W
    (isMultiplicative_kernelArithTotient s s')).eulerProduct_hasProd
      (summable_norm_restrictCoprime_kernelArithTotient W hσ hs hs') using 1
  · funext p
    rw [tsum_restrictCoprime_prime_pow W (isMultiplicative_kernelArithTotient s s') p.2,
      tsum_kernelArithTotient_prime_pow p.2]
  · exact coprimeTotientKernel_eq_tsum hσ hs hs'

/-- **The source's Euler-factor estimate for the totient kernel**, exact — the totient instance of
`Gap212.Sieve.eq_zeta_quotient_mul_of_hasProd`, whose three `ζ`-side families are the *same* as the
reciprocal kernel's. -/
theorem coprimeTotientKernel_eq_zeta_quotient_mul {W : ℕ} (hW : W ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    {s s' : ℂ} (hs : s.re = σ) (hs' : s'.re = σ) :
    coprimeTotientKernel W s s'
      = (riemannZeta (1 + s))⁻¹ * (riemannZeta (1 + s'))⁻¹ * riemannZeta (1 + (s + s')) *
          (wTwistedProduct W (s + s') / (wTwistedProduct W s * wTwistedProduct W s')) *
          ∏' p : Nat.Primes, coprimeKpErrorTotient W s s' p := by
  have hsre : 0 < s.re := hs ▸ hσ
  have hs're : 0 < s'.re := hs' ▸ hσ
  exact eq_zeta_quotient_mul_of_hasProd hW hsre hs're
    (hasProd_coprimeLocalFactorTotient W hσ hs hs')
    (multipliable_coprimeKpErrorTotient W hsre.le hs're.le)
    fun p ↦ coprimeLocalFactorTotient_mul_coprimeFactor W hsre hs're p

/-! ## The two estimates the closing limit asks for -/

/-- **The totient kernel's instance of the exact identity of
`Gap212.Sieve.mul_kernel_eq_limitKernel_mul_closeRatio`.** -/
theorem mul_coprimeTotientKernel_eq_limitKernel_mul_closeRatio {W : ℕ} (hW : W ≠ 0) {x : ℝ}
    (hx : 1 < x) (ξ ξ' : ℝ) :
    wDensity W * (Real.log x : ℂ) *
        coprimeTotientKernel W (kernelArg x ξ) (kernelArg x ξ')
      = limitKernel ξ ξ' * closeRatio W (kernelArg x ξ) (kernelArg x ξ')
          (∏' p : Nat.Primes, coprimeKpErrorTotient W (kernelArg x ξ) (kernelArg x ξ') p) :=
  mul_kernel_eq_limitKernel_mul_closeRatio hx ξ ξ'
    (coprimeTotientKernel_eq_zeta_quotient_mul hW (one_div_pos.2 (Real.log_pos hx))
      (kernelArg_re x ξ) (kernelArg_re x ξ'))

/-- The totient correction product at the exponents of Lemma 4.1 is uniformly `1+o(1)`. -/
theorem eventually_forall_norm_tprod_coprimeKpErrorTotient_kernelArg_sub_one_le {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ,
      ‖(∏' p : Nat.Primes,
          coprimeKpErrorTotient (W x) (kernelArg x ξ) (kernelArg x ξ') p) - 1‖ ≤ η := by
  filter_upwards [eventually_forall_norm_tprod_coprimeKpErrorTotient_sub_one_le hη,
    eventually_gt_atTop (1 : ℝ)] with x hx hx1 ξ ξ'
  have hlx : 0 < Real.log x := Real.log_pos hx1
  refine hx _ _ ?_ ?_ <;> rw [kernelArg_re] <;> positivity

/-- **The residue estimate for the totient kernel**, uniformly over the truncation range: the
`hres` hypothesis of `Gap212.Sieve.eventually_forall_norm_closeDiff_le`. -/
theorem eventually_forall_norm_mul_coprimeTotientKernel_sub_limitKernel_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ, |ξ| ≤ Real.sqrt (Real.log x) →
      |ξ'| ≤ Real.sqrt (Real.log x) →
      ‖wDensity (W x) * (Real.log x : ℂ) *
          coprimeTotientKernel (W x) (kernelArg x ξ) (kernelArg x ξ') - limitKernel ξ ξ'‖
        ≤ ε * (‖limitNum ξ‖ * ‖limitNum ξ'‖) := by
  refine eventually_forall_norm_mul_kernel_sub_limitKernel_le ?_
    (fun η hη ↦ eventually_forall_norm_tprod_coprimeKpErrorTotient_kernelArg_sub_one_le hη) hε
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx1 ξ ξ'
  exact mul_coprimeTotientKernel_eq_limitKernel_mul_closeRatio (primorial_pos _).ne' hx1 ξ ξ'

/-- **The crude bound for the normalised totient kernel**: `‖B_x·K^φ_{W(x)}‖ ≤ 8Z(2)⁶·\log⁴x`. The
constant `Z(2)⁶` is the whole price the totient kernel pays over the reciprocal one in step 2
(`Gap212.Sieve.norm_coprimeTotientKernel_le_sharp`), and the closing limit does not care what it
is. -/
theorem eventually_forall_norm_mul_coprimeTotientKernel_le : ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ,
    ‖wDensity (W x) * (Real.log x : ℂ) *
      coprimeTotientKernel (W x) (kernelArg x ξ) (kernelArg x ξ')‖
      ≤ 8 * zetaSeries 2 ^ 6 * Real.log x ^ 4 := by
  filter_upwards [eventually_zetaSeries_le, eventually_gt_atTop (1 : ℝ)] with x hZ hx1 ξ ξ'
  have hlx : 0 < Real.log x := Real.log_pos hx1
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlx]
  calc _ ≤ 1 * Real.log x * (zetaSeries 2 ^ 6 * (2 * Real.log x) ^ 3) := by
        gcongr
        · exact norm_wDensity_le_one (primorial_pos _).ne'
        · exact (norm_coprimeTotientKernel_le_sharp (W x) (one_div_pos.2 hlx) (kernelArg_re x ξ)
            (kernelArg_re x ξ')).trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (zetaSeries_nonneg _) hZ 3) (by positivity))
    _ = 8 * zetaSeries 2 ^ 6 * Real.log x ^ 4 := by ring

/-! ## The integrand is integrable -/

/-- The normalised totient integrand is integrable for every `x > 1` — the interchange's own
integrability at the totient weight, times a constant. -/
theorem eventually_integrable_mul_coprimeTotientKernel {F G : ℝ → ℝ} (hFd : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hGd : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) :
    ∀ᶠ x : ℝ in atTop, Integrable fun w : ℝ × ℝ ↦
      profileFourier F w.1 * profileFourier G w.2 *
        (wDensity (W x) * (Real.log x : ℂ) *
          coprimeTotientKernel (W x) (kernelArg x w.1) (kernelArg x w.2)) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx1
  refine ((integrable_pairKernel_mul (coprimeTotientWeight_eq_zero (W x)) hFd hFc hGd hGc
    (summable_weightMajorant_coprimeTotientWeight (W x) (one_div_pos.2 (Real.log_pos hx1)))
    ).const_mul (wDensity (W x) * (Real.log x : ℂ))).congr (.of_forall fun w ↦ ?_)
  simp only [coprimeTotientKernel]
  ring

/-! ## The analytic core of Lemma 4.1, and `Gap212.Sieve.Polymath41Totient` -/

/-- **The analytic core of Polymath8b Lemma 4.1 for the totient kernel**: for `F, G` smooth with
compact support,

  `(φ(W(x))/W(x))·\log x · ∫_{ℝ²} f(ξ) g(ξ') K^φ_{W(x)}(ξ,ξ') d(ξ,ξ')
     ⟶ ∫_{ℝ²} f(ξ) g(ξ') limitKernel ξ ξ' d(ξ,ξ')`   as `x → ∞`,

which is the hypothesis `Gap212.Sieve.polymath41Totient_of_tendsto_integral` asks for, up to the
closing identity of `Gap212.Sieve.Polymath41AssembleLimitParseval`.

The *same* limit value as the reciprocal kernel's: the correction that distinguishes the two Euler
products is `Gap212.Sieve.coprimeKpErrorTotient`, and its product tends to `1`. -/
theorem tendsto_mul_integral_coprimeTotientKernel {F G : ℝ → ℝ} (hFd : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hGd : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) :
    Tendsto (fun x : ℝ ↦ ((((W x).totient : ℝ) / (W x : ℝ) * Real.log x : ℝ) : ℂ) *
        ∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 *
          coprimeTotientKernel (W x) (kernelArg x w.1) (kernelArg x w.2)) atTop
      (nhds (∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 * limitKernel w.1 w.2)) := by
  have hb : (0 : ℝ) ≤ 8 * zetaSeries 2 ^ 6 := by positivity
  have hmain := tendsto_integral_of_forall_norm_closeDiff_le hFd hFc hGd hGc
    (P := fun x ξ ξ' ↦ wDensity (W x) * (Real.log x : ℂ) *
      coprimeTotientKernel (W x) (kernelArg x ξ) (kernelArg x ξ'))
    (eventually_integrable_mul_coprimeTotientKernel hFd hFc hGd hGc)
    fun ε hε ↦ eventually_forall_norm_closeDiff_le hFd hFc hGd hGc hb
      eventually_forall_norm_mul_coprimeTotientKernel_le
      (eventually_forall_norm_mul_coprimeTotientKernel_sub_limitKernel_le hε) hε
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx1
  have hW : W x ≠ 0 := (primorial_pos _).ne'
  have hcast : ((((W x).totient : ℝ) / (W x : ℝ) * Real.log x : ℝ) : ℂ)
      = wDensity (W x) * (Real.log x : ℂ) := by
    rw [wDensity_eq_totient_div hW]
    push_cast
    ring
  rw [hcast, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun w ↦ by ring)

/-- **Polymath8b Lemma 4.1 at `k = 1`, `N = 1`, for the totient kernel.**
`Gap212.Sieve.Polymath41Totient`, the `Prop` the numerator asymptotic rests on
(`Gap212.Sieve.numeratorAsymptotic_of_polymath41Totient`). -/
theorem polymath41Totient : Polymath41Totient :=
  polymath41Totient_of_tendsto_integral fun _F _G hFd hFc hGd hGc _ _ _ _ ↦
    tendsto_ofReal_integral_deriv_mul_of_tendsto hFd hFc hGd hGc
      (tendsto_mul_integral_coprimeTotientKernel hFd hFc hGd hGc)

/-- **`Gap212.Sieve.NumeratorAsymptotic 44`**, the numerator asymptotic:
`Gap212.Sieve.numeratorAsymptotic_of_polymath41Totient` at the proved
`Gap212.Sieve.polymath41Totient`. -/
theorem numeratorAsymptotic_44 : NumeratorAsymptotic 44 :=
  numeratorAsymptotic_of_polymath41Totient polymath41Totient

end Gap212.Sieve
