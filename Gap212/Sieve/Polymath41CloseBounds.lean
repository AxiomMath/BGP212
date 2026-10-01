/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssembleLimitParseval
public import Gap212.Sieve.Polymath41PoleUniform

/-!
# The one dominating function of the closing limit of Polymath8b Lemma 4.1

The closing step of Lemma 4.1 compares two integrals over `ℝ²`,

  `B_x · ∫_{ℝ²} f(ξ) g(ξ') K_{W(x)}(ξ,ξ')`  against  `∫_{ℝ²} f(ξ) g(ξ') limitKernel ξ ξ'`,

and the comparison is not uniform in `(ξ,ξ')`: the residue of `ζ` controls the kernel only where
`‖(1+2πiξ)/log x‖` is small, which is the source's truncation `|ξ| ≤ √(log x)`. Outside
it the only bound on the kernel is the crude `Z(1+1/\log x)³ ≍ \log³x` of step 2, and what beats it
is the rapid decay of the transforms.

This file provides the **single** function that dominates the difference of the two integrands on
*both* ranges, so that the closing limit needs no dominated-convergence theorem and no splitting of
the domain of integration:

  `Gap212.Sieve.closeWeight F ξ = (1+ξ²)⁻¹ + ‖(1+2πiξ)·f(ξ)‖`,

taken as a product over the two variables (`Gap212.Sieve.integrable_closeWeight_mul`). Three facts
make it serve both ranges at once:

* it dominates `‖f‖`, `‖(1+2πiξ)f‖` and `(1+ξ²)⁻¹` separately
  (`Gap212.Sieve.norm_profileFourier_le_closeWeight`,
  `Gap212.Sieve.norm_limitNum_mul_profileFourier_le_closeWeight`,
  `Gap212.Sieve.inv_one_add_sq_le_closeWeight`), which is what the truncated range needs;
* on the discarded range it absorbs *any* fixed power of `\log x`
  (`Gap212.Sieve.exists_forall_pow_mul_norm_profileFourier_tail_le`), which is what the crude
  kernel bound needs — the point being that `√(\log x) ≤ |ξ|` converts `\log x` into `(1+|ξ|)²`;
* it is integrable (`Gap212.Sieve.integrable_closeWeight`), the `(1+ξ²)⁻¹` by
  `MeasureTheory.integrable_inv_one_add_sq` and the transform term by
  `Gap212.Sieve.integrable_limitNum_mul_profileFourier`.

## Main definitions

* `Gap212.Sieve.closeWeight`: the dominating function of one variable.

## Main results

* `Gap212.Sieve.norm_limitKernel_le`: `‖limitKernel ξ ξ'‖ ≤ ‖1+2πiξ‖·‖1+2πiξ'‖`.
* `Gap212.Sieve.exists_forall_pow_mul_norm_profileFourier_tail_le`: on `√L ≤ |ξ|` the transform
  absorbs `L^m` at every polynomial order.
* `Gap212.Sieve.integrable_closeWeight_mul`: the dominating function is integrable on `ℝ²`.
* `Gap212.Sieve.integrable_profileFourier_mul_limitKernel`: the limiting integrand is integrable.
-/

@[expose] public section

namespace Gap212.Sieve

open MeasureTheory Real
open scoped FourierTransform ContDiff

/-! ## The size of `1 + 2πiξ` from below, and of the limiting kernel from above -/

/-- `1 ≤ ‖1+2πiξ‖`, the real part being `1`. It is why `Gap212.Sieve.closeWeight` dominates `‖f‖`
as well as `‖(1+2πiξ)f‖`. -/
theorem one_le_norm_limitNum (ξ : ℝ) : 1 ≤ ‖limitNum ξ‖ := by
  simpa [limitNum_re] using Complex.re_le_norm (limitNum ξ)

/-- `‖1+2πiξ‖ ≤ 8(1+|ξ|)`: the numerator's growth is linear, with a constant that needs no `π`. -/
theorem norm_limitNum_le_eight_mul (ξ : ℝ) : ‖limitNum ξ‖ ≤ 8 * (1 + |ξ|) :=
  (norm_limitNum_le ξ).trans (by nlinarith [Real.pi_le_four, abs_nonneg ξ])

/-- **The limiting kernel is at most the product of its two numerators.** Its denominator
`limitNum ξ + limitNum ξ'` has real part `2`, hence modulus at least `1`
(`Gap212.Sieve.limitNum_add_re`). -/
theorem norm_limitKernel_le (ξ ξ' : ℝ) :
    ‖limitKernel ξ ξ'‖ ≤ ‖limitNum ξ‖ * ‖limitNum ξ'‖ := by
  have hden := Complex.re_le_norm (limitNum ξ + limitNum ξ')
  rw [limitNum_add_re] at hden
  rw [limitKernel, norm_div, norm_mul, div_le_iff₀ (by linarith)]
  exact le_mul_of_one_le_right (by positivity) (by linarith)

/-! ## The discarded range absorbs every power of `log x` -/

/-- **On the discarded range `√L ≤ |ξ|` the transform absorbs `L^m`, at every polynomial order.**
For every `m, n` there is a `C` with

  `L^m · (1+|ξ|)^n · ‖f(ξ)‖ ≤ C`  whenever `0 ≤ L` and `√L ≤ |ξ|`.

This is `Gap212.Sieve.profileFourier_decay` at order `2m+n`, the point being that `√L ≤ |ξ|` turns
`L` into `(1+|ξ|)²`: the source's truncation `|ξ| ≤ √(log x)` is *exactly* the trade that lets the
crude kernel bound `≍ \log³x` of step 2 be beaten on the range step 4's residue does not cover. -/
theorem exists_forall_pow_mul_norm_profileFourier_tail_le {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) (m n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L ξ : ℝ, 0 ≤ L → Real.sqrt L ≤ |ξ| →
      L ^ m * ((1 + |ξ|) ^ n * ‖profileFourier F ξ‖) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := profileFourier_decay hF hFc (2 * m + n)
  refine ⟨C, hC0, fun L ξ hL hξ ↦ (hC ξ).trans' ?_⟩
  have hsq : L ≤ (1 + |ξ|) ^ 2 := by
    nlinarith [Real.mul_self_sqrt hL, Real.sqrt_nonneg L, abs_nonneg ξ]
  rw [pow_add, pow_mul, mul_assoc]
  gcongr

/-! ## The dominating function -/

/-- **The dominating function of the closing limit**, in one variable:

  `closeWeight F ξ = (1+ξ²)⁻¹ + ‖(1+2πiξ)·f(ξ)‖`.

The first summand is what the discarded range is compared against — it is the shape
`Gap212.Sieve.exists_forall_pow_mul_norm_profileFourier_tail_le` produces at `n = 2` — and the
second is what the truncated range needs, `‖limitKernel ξ ξ'‖` being at most the product of the two
numerators (`Gap212.Sieve.norm_limitKernel_le`). Both are integrable, so their sum is. -/
noncomputable def closeWeight (F : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (1 + ξ ^ 2)⁻¹ + ‖limitNum ξ * profileFourier F ξ‖

/-- The dominating function `closeWeight F ξ` is nonnegative. -/
theorem closeWeight_nonneg (F : ℝ → ℝ) (ξ : ℝ) : 0 ≤ closeWeight F ξ := by
  rw [closeWeight]; positivity

/-- `(1+ξ²)⁻¹ ≤ closeWeight F ξ`. -/
theorem inv_one_add_sq_le_closeWeight (F : ℝ → ℝ) (ξ : ℝ) :
    (1 + ξ ^ 2)⁻¹ ≤ closeWeight F ξ :=
  le_add_of_nonneg_right (norm_nonneg _)

/-- `‖(1+2πiξ)f(ξ)‖ ≤ closeWeight F ξ`. -/
theorem norm_limitNum_mul_profileFourier_le_closeWeight (F : ℝ → ℝ) (ξ : ℝ) :
    ‖limitNum ξ * profileFourier F ξ‖ ≤ closeWeight F ξ :=
  le_add_of_nonneg_left (by positivity)

/-- `‖f(ξ)‖ ≤ closeWeight F ξ`, because `‖1+2πiξ‖ ≥ 1`. -/
theorem norm_profileFourier_le_closeWeight (F : ℝ → ℝ) (ξ : ℝ) :
    ‖profileFourier F ξ‖ ≤ closeWeight F ξ := by
  refine le_trans ?_ (norm_limitNum_mul_profileFourier_le_closeWeight F ξ)
  rw [norm_mul]
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_norm_limitNum ξ)

/-- The dominating function is integrable: `(1+ξ²)⁻¹` by
`MeasureTheory.integrable_inv_one_add_sq`, the transform term by
`Gap212.Sieve.integrable_limitNum_mul_profileFourier`. -/
theorem integrable_closeWeight {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) : Integrable (closeWeight F) :=
  integrable_inv_one_add_sq.add (integrable_limitNum_mul_profileFourier hF hFc).norm

/-- The dominating function on `ℝ²`, the product of the two one-variable ones. -/
theorem integrable_closeWeight_mul {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) :
    Integrable fun w : ℝ × ℝ ↦ closeWeight F w.1 * closeWeight G w.2 := by
  rw [Measure.volume_eq_prod]
  exact (integrable_closeWeight hF hFc).mul_prod (integrable_closeWeight hG hGc)

/-- The integral of the dominating function is nonnegative — all that the closing estimate needs of
its value. -/
theorem integral_closeWeight_mul_nonneg (F G : ℝ → ℝ) :
    0 ≤ ∫ w : ℝ × ℝ, closeWeight F w.1 * closeWeight G w.2 :=
  integral_nonneg fun w ↦ mul_nonneg (closeWeight_nonneg F w.1) (closeWeight_nonneg G w.2)

/-! ## The limiting integrand is integrable -/

/-- **`f(ξ)g(ξ')·limitKernel ξ ξ'` is integrable on `ℝ²`** — the right-hand side of the closing
limit is an honest integral. Continuity is that of `Gap212.Sieve.limitNum` and of the transforms,
the denominator not vanishing (`Gap212.Sieve.limitNum_add_ne_zero`); the dominating function is
`Gap212.Sieve.integrable_closeWeight_mul`, through `Gap212.Sieve.norm_limitKernel_le`. -/
theorem integrable_profileFourier_mul_limitKernel {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) :
    Integrable fun w : ℝ × ℝ ↦ profileFourier F w.1 * profileFourier G w.2 *
      limitKernel w.1 w.2 := by
  have hcontnum : Continuous limitNum := by unfold limitNum; fun_prop
  have hcf := (contDiff_profileFourier hF hFc).continuous
  have hcg := (contDiff_profileFourier hG hGc).continuous
  have hcont : Continuous fun w : ℝ × ℝ ↦ profileFourier F w.1 * profileFourier G w.2 *
      limitKernel w.1 w.2 := by
    unfold limitKernel
    fun_prop (disch := exact fun w ↦ limitNum_add_ne_zero w.1 w.2)
  refine (integrable_closeWeight_mul hF hFc hG hGc).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun w ↦ ?_)
  rw [norm_mul, norm_mul]
  calc ‖profileFourier F w.1‖ * ‖profileFourier G w.2‖ * ‖limitKernel w.1 w.2‖
      ≤ ‖profileFourier F w.1‖ * ‖profileFourier G w.2‖ *
          (‖limitNum w.1‖ * ‖limitNum w.2‖) :=
        mul_le_mul_of_nonneg_left (norm_limitKernel_le w.1 w.2) (by positivity)
    _ = ‖limitNum w.1 * profileFourier F w.1‖ * ‖limitNum w.2 * profileFourier G w.2‖ := by
        rw [norm_mul, norm_mul]; ring
    _ ≤ closeWeight F w.1 * closeWeight G w.2 :=
        mul_le_mul (norm_limitNum_mul_profileFourier_le_closeWeight F w.1)
          (norm_limitNum_mul_profileFourier_le_closeWeight G w.2) (norm_nonneg _)
          (closeWeight_nonneg F w.1)

end Gap212.Sieve
