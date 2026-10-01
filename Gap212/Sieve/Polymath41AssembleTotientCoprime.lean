/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssembleRecipCoprime

/-!
# The sieve's coprimality condition, put back into the **totient** kernel's Euler product

`Gap212.Sieve.Polymath41AssembleRecipCoprime` restores the source's condition
"`[d,d'], W, N` coprime" (at `N = 1`) for the reciprocal kernel, and does it
through a layer that is generic in the weight: the restriction
`Gap212.Sieve.coprimeWeight`, the restricted arithmetic function `Gap212.Sieve.restrictCoprime`,
and the three facts that the restriction acts on whole fibres, preserves multiplicativity, and
turns the local factor at `p ∣ W` into `1`. This file instantiates that layer at the **totient**
kernel of the lemma's closing sentence, producing the source's `∏_{p ∤ W} K_p` for
`φ([d,d'])`.

## What is shared and what is not

Shared: everything in the generic layer. `Gap212.Sieve.coprime_lcm_iff` is a statement about `lcm`
and does not see a denominator; `Gap212.Sieve.isMultiplicative_restrictCoprime` is a statement
about an arbitrary `ArithmeticFunction`; `Gap212.Sieve.tsum_restrictCoprime_prime_pow` reads only
`f 1 = 1`.

Not shared, and these are the three places this file does arithmetic of its own:

* the summability that licenses the Euler product comes from the **totient** majorant
  (`Gap212.Sieve.summable_weightMajorant_totientPairWeight`, off
  `Gap212.Sieve.summable_pairTotientMajorant`). The reciprocal kernel's majorant does not dominate
  it — `φ([d,d']) ≤ [d,d']` makes these terms the larger ones — so
  `Gap212.Sieve.summable_norm_restrictCoprime_kernelArith` is of no use here;
* the fibre sum is divided by `φ(n)`, not by `n`, so the coefficient is
  `Gap212.Sieve.kernelCoeffTotient` (`Gap212.Sieve.sum_lcmFibre_pairKernelTerm_totient`);
* the local factor is `Gap212.Sieve.localFactorTotient`, whose value at `u = v = 1` is
  `1 - 1/(p-1)` rather than `1 - 1/p`.

Notably **no oddness hypothesis appears anywhere in this file**. The
`p = 2` obstruction of the totient kernel lives in the *limit* `u, v → 1`, where the local factor
`Gap212.Sieve.localFactorTotient 2 1 1` is `0`
(`Gap212.Sieve.localFactorTotient_two_one_one_eq_zero` below); at the exponents this file works at,
`1/(p-1)` is a perfectly good number at `p = 2` and the majorant behind the product is, at `p = 2`,
the extremal rather than a degenerate prime. See `Gap212.Sieve.Polymath41MajorantTotient`.

## Main definitions

* `Gap212.Sieve.coprimeTotientKernel`: the totient kernel **with** the sieve's coprimality
  condition — the kernel the interchange of
  `Gap212.Sieve.Polymath41AssembleTotientSum` actually produces from
  `Gap212.Sieve.pairSumTotient`.

## Main results

* `Gap212.Sieve.coprimeTotientKernel_eq_tsum`: it is the Dirichlet series of
  `Gap212.Sieve.kernelCoeffTotient` restricted to `n` coprime to `W`.
* `Gap212.Sieve.norm_coprimeTotientKernel_le_sharp`: `‖K^φ_W‖ ≤ Z(2)⁶·Z(1+σ)³`, the source's rate,
  uniform in `ξ,ξ'` — the restriction only removes non-negative terms.
* `Gap212.Sieve.tprod_localFactorTotient_eq_coprimeTotientKernel`: **the source's `∏_{p ∤ W} K_p`**
  with `[d,d']` replaced by `φ([d,d'])`.
* `Gap212.Sieve.localFactorTotient_two_one_one_eq_zero`: the local factor at `p = 2` and
  `u = v = 1` vanishes — where the totient kernel's oddness requirement actually comes from.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset
open scoped ArithmeticFunction.Moebius

/-! ## The totient kernel with the sieve's coprimality condition -/

/-- **The source's kernel at `N = 1` with its coprimality condition, totient denominator**:
`K^φ_W = ∑_{d,d' : ([d,d'],W)=1} μ(d)μ(d')/(φ([d,d']) d^s (d')^{s'})`. This — not
`Gap212.Sieve.totientKernel` — is the kernel the interchange produces from
`Gap212.Sieve.pairSumTotient`, whose summation range is restricted to divisors coprime to `W`. -/
noncomputable def coprimeTotientKernel (W : ℕ) (s s' : ℂ) : ℂ :=
  pairKernel (coprimeWeight W totientPairWeight) s s'

/-- The restricted totient weight vanishes on the degenerate pairs, so the interchange and the
regrouping both apply to it. -/
theorem coprimeTotientWeight_eq_zero (W : ℕ) :
    ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → coprimeWeight W totientPairWeight p = 0 :=
  coprimeWeight_eq_zero totientPairWeight_eq_zero W

/-- Step 2's summability for the restricted totient weight: the totient majorant of
`Gap212.Sieve.Polymath41MajorantTotient`, cut down by the restriction. -/
theorem summable_weightMajorant_coprimeTotientWeight (W : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Summable (weightMajorant (coprimeWeight W totientPairWeight) σ) :=
  summable_weightMajorant_coprimeWeight W (summable_weightMajorant_totientPairWeight hσ)

/-- **`K^φ_W` is the Dirichlet series of `Gap212.Sieve.kernelCoeffTotient` restricted to the `n`
coprime to `W`.** The regrouping of `Gap212.Sieve.Polymath41AssembleDirichlet` with the
restriction riding along on the fibre labels — `Gap212.Sieve.coprime_lcm_iff` is what makes the
condition a condition on the label. -/
theorem coprimeTotientKernel_eq_tsum {W : ℕ} {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ} (hs : s.re = σ)
    (hs' : s'.re = σ) :
    coprimeTotientKernel W s s' = ∑' n : ℕ, restrictCoprime W (kernelArithTotient s s') n := by
  rw [coprimeTotientKernel, pairKernel_eq_tsum_sum_lcmFibre (coprimeTotientWeight_eq_zero W)
    (summable_weightMajorant_coprimeTotientWeight W hσ) hs hs']
  refine tsum_congr fun n ↦ ?_
  rw [sum_lcmFibre_pairKernelTerm_coprimeWeight, sum_lcmFibre_pairKernelTerm_totient,
    restrictCoprime_apply, kernelArithTotient_apply]

/-- `∑_n ‖a^φ(n)·1_{(n,W)=1}‖ < ∞`, dominated by the unrestricted
`Gap212.Sieve.summable_norm_kernelCoeffTotient`. This is the one hypothesis of
`ArithmeticFunction.IsMultiplicative.eulerProduct_tprod` beyond multiplicativity, and it is the
*totient* majorant that supplies it. -/
theorem summable_norm_restrictCoprime_kernelArithTotient (W : ℕ) {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ}
    (hs : s.re = σ) (hs' : s'.re = σ) :
    Summable (‖restrictCoprime W (kernelArithTotient s s') ·‖) := by
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (summable_norm_kernelCoeffTotient hσ hs hs')
  rw [restrictCoprime_apply]
  split <;> simp [kernelArithTotient_apply]

/-- **`K^φ_W` is bounded at the source's rate**, uniformly in `ξ,ξ'`: if both exponents
have real part `σ > 0` then

  `‖K^φ_W(s,s')‖ ≤ Z(2)⁶·Z(1+σ)³`.

The coprimality condition cannot make the kernel larger — it deletes terms from a sum of
non-negative majorant terms — so this is `Gap212.Sieve.norm_totientKernel_le_sharp` with one
comparison in front of it, and in particular the `σ`-rate is the reciprocal kernel's own `Z(1+σ)³`,
i.e. `≪ log³x` at `σ = 1/log x`. -/
theorem norm_coprimeTotientKernel_le_sharp (W : ℕ) {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ} (hs : s.re = σ)
    (hs' : s'.re = σ) :
    ‖coprimeTotientKernel W s s'‖ ≤ zetaSeries 2 ^ 6 * zetaSeries (1 + σ) ^ 3 := by
  rw [coprimeTotientKernel]
  refine (norm_pairKernel_le_tsum (coprimeTotientWeight_eq_zero W)
    (summable_weightMajorant_coprimeTotientWeight W hσ) hs hs').trans ?_
  refine ((summable_weightMajorant_coprimeTotientWeight W hσ).tsum_le_tsum
    (fun p ↦ weightMajorant_coprimeWeight_le W totientPairWeight σ p)
    (summable_weightMajorant_totientPairWeight hσ)).trans ?_
  rw [tsum_congr fun p ↦ weightMajorant_totientPairWeight σ p]
  exact tsum_pairTotientMajorant_le_sharp hσ

/-- **The source's Euler product `K^φ_W = ∏_{p ∤ W} K_p`**, written as a product over all primes
whose factors at `p ∣ W` are `1`:

  `∏_p (if p ∣ W then 1 else Gap212.Sieve.localFactorTotient p (p^{-s}) (p^{-s'})) = K^φ_W(s,s')`.

Every ingredient is derived rather than transported from the reciprocal case: multiplicativity from
`Gap212.Sieve.isMultiplicative_restrictCoprime` applied to
`Gap212.Sieve.isMultiplicative_kernelArithTotient`, the local factor from
`Gap212.Sieve.tsum_restrictCoprime_prime_pow` and `Gap212.Sieve.tsum_kernelArithTotient_prime_pow`
— whose inner series is *exact*, not truncated, because
`Gap212.Sieve.kernelCoeffTotient_prime_pow` kills every `e ≥ 2` — and the summability from the
totient majorant.

This is the totient companion of
`Gap212.Sieve.tprod_localFactorRecip_eq_coprimeRecipKernel`, and the two differ in the one place
the source says they differ: `1/p` against `1/(p-1)`, quantified exactly by
`Gap212.Sieve.localFactorTotient_eq_sub`. -/
theorem tprod_localFactorTotient_eq_coprimeTotientKernel (W : ℕ) {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ}
    (hs : s.re = σ) (hs' : s'.re = σ) :
    ∏' p : Nat.Primes, (if (p : ℕ) ∣ W then 1 else
        localFactorTotient ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s')))
      = coprimeTotientKernel W s s' := by
  rw [coprimeTotientKernel_eq_tsum hσ hs hs', ← (isMultiplicative_restrictCoprime W
    (isMultiplicative_kernelArithTotient s s')).eulerProduct_tprod
    (summable_norm_restrictCoprime_kernelArithTotient W hσ hs hs')]
  refine tprod_congr fun p ↦ ?_
  rw [tsum_restrictCoprime_prime_pow W (isMultiplicative_kernelArithTotient s s') p.2,
    tsum_kernelArithTotient_prime_pow p.2]

/-! ## Where the oddness of the totient kernel comes from -/

/-- **The totient local factor at `p = 2` vanishes in the limit `u, v → 1`.**

  `Gap212.Sieve.localFactorTotient 2 1 1 = 1 - 1/(2-1) = 0`.

This is the whole of the totient kernel's `p = 2` obstruction. Three consequences:

* the kernel's limiting Euler product over `p ∤ W` has a **zero factor** unless `2 ∣ W`, so the
  normalised limit of `Gap212.Sieve.pairSumTotient` would be `0` and not
  `∫₀^∞ F'G'`. The correction product of `Gap212.Sieve.tendsto_tprod_corr_W` records the same fact
  in the same place: its factor `1 - 1/(p-1)²` is `0` at `p = 2`, which is why that theorem is
  proved through `Gap212.Sieve.eventually_dvd_W_of_prime_le` and not for arbitrary moduli;
* it is the same vanishing as `(μ*φ)(2) = 0` (`Gap212.Sieve.moebiusTotient_prime` at `p = 2`), by
  `Gap212.Sieve.localFactorTotient_one_one_mul_mertensFactor`: the local factor at `u = v = 1`
  inverts `1 + 1/(p-2)`, and an inverse of something with a pole is a zero;
* it is **not** an obstruction to anything at the exponents the Euler product above is taken at.
  There `1/(p-1) = 1` is an ordinary number and no hypothesis on `2 ∣ W` is needed — which is why
  `Gap212.Sieve.tprod_localFactorTotient_eq_coprimeTotientKernel` carries none, and why the totient
  majorant of `Gap212.Sieve.Polymath41MajorantTotient` carries none either.

The reciprocal kernel has no analogue: `Gap212.Sieve.localFactorRecip 2 1 1 = 1/2 ≠ 0`. -/
theorem localFactorTotient_two_one_one_eq_zero {K : Type*} [Field K] :
    localFactorTotient (2 : K) 1 1 = 0 := by
  rw [localFactorTotient]
  norm_num

end Gap212.Sieve
