/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssembleTotientSum

/-!
# `Gap212.Sieve.Polymath41Totient`, reduced to the asymptotic of its kernel integral

`Gap212.Sieve.Polymath41AssembleTotientSum` identifies the left-hand side of
`Gap212.Sieve.Polymath41Totient` with the source's double integral (with `[d,d']`
replaced by `φ([d,d'])`). This file draws the consequence: the `Prop` follows from an
asymptotic statement about that integral alone, and **everything arithmetic in the `Prop` is
discharged on the way**.

What is discharged: the truncation at `⌈x^β⌉₊`, the Möbius weights, the coprimality filter to
`W(x)`, and the passage from a finite real sum to an absolutely convergent complex one. None of
them is left in the hypothesis of `Gap212.Sieve.polymath41Totient_of_tendsto_integral`.

What is not: the hypothesis is analysis about `ζ` and about the Fourier transforms of the profiles,
supplied by `Gap212.Sieve.polymath41Totient` in `Gap212.Sieve.Polymath41CloseTotient`. This
file moves the work from a statement about a sieve sum to a statement about an integral of an Euler
product, which is where the source does its own work.

## The totient kernel's one extra move, and where it is

Relative to the reciprocal case the limiting local factor is `1 - 1/(p-1)` rather than `1 - 1/p`
(`Gap212.Sieve.localFactorTotient_one_one`), so the product over `p ∤ W` carries the correction
`∏_{p∤W}(1-1/(p-1)²)` (`Gap212.Sieve.localFactorTotient_one_one_eq_mul`). At `W = W(x)` that
correction tends to `1` (`Gap212.Sieve.tendsto_tprod_corr_W`) and so does **not** appear in the
`Prop`'s normalisation, which is the same `B_x` as the reciprocal case. The correction's factor at
`p = 2` is `0` (`Gap212.Sieve.localFactorTotient_two_one_one_eq_zero`), which is why that limit is
a theorem about the primorials `W(x)` and not about arbitrary moduli.

## Main results

* `Gap212.Sieve.polymath41Totient_of_tendsto_integral`: **the `Prop`, reduced** — Lemma 4.1 for
  the totient kernel from the asymptotic `B_x·∫∫ f g K^φ_{W(x)} ⟶ ∫₀^∞ F'G'`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Gap212.GPY MeasureTheory Real
open scoped FourierTransform ContDiff

/-- **`Gap212.Sieve.Polymath41Totient` follows from the asymptotic of its kernel integral.**

The hypothesis is the analytic core of Polymath8b Lemma 4.1 at `k = 1, N = 1` in the totient kernel:
with `B_x = (φ(W(x))/W(x))·log x` the source's normalization,

  `B_x · ∫_{ℝ²} f(ξ) g(ξ') K^φ_{W(x)}(ξ,ξ') d(ξ,ξ') ⟶ ∫₀^∞ F'G'`,

where `f = Gap212.Sieve.profileFourier F`, `g = Gap212.Sieve.profileFourier G` and `K^φ_W` is
`Gap212.Sieve.coprimeTotientKernel`, whose Euler product over `p ∤ W` is
`Gap212.Sieve.tprod_localFactorTotient_eq_coprimeTotientKernel` and whose size is
`Gap212.Sieve.norm_coprimeTotientKernel_le_sharp`.

**This is a separate reduction from `Gap212.Sieve.polymath41Recip_of_tendsto_integral`, not a
transport of it**: the kernel in the hypothesis is a different function of `(ξ,ξ')`, its Euler
factors are `Gap212.Sieve.localFactorTotient`, and its limiting product carries a correction the
reciprocal kernel's does not. -/
theorem polymath41Totient_of_tendsto_integral
    (h : ∀ F G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → ContDiff ℝ (⊤ : ℕ∞) G →
      HasCompactSupport G → ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) → (∀ t, β ≤ t → G t = 0) →
      Tendsto (fun x : ℝ ↦ ((((W x).totient : ℝ) / (W x : ℝ) * Real.log x : ℝ) : ℂ) *
          ∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 *
            coprimeTotientKernel (W x) (kernelArg x w.1) (kernelArg x w.2)) atTop
        (nhds (((∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t : ℝ) : ℂ)))) :
    Polymath41Totient := by
  intro F G hFd hFc hGd hGc β hβ hFv hGv
  have hcplx := h F G hFd hFc hGd hGc β hβ hFv hGv
  have hre := (Complex.continuous_re.tendsto
    (((∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t : ℝ) : ℂ))).comp hcplx
  rw [Complex.ofReal_re] at hre
  refine hre.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Function.comp_apply, ← ofReal_pairSumTotient_eq_integral hFd hFc hGd hGc hx hFv hGv (W x)
    (Nat.le_ceil _), ← Complex.ofReal_mul, Complex.ofReal_re]

end Gap212.Sieve
