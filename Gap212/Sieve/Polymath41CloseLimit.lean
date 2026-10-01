/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41CloseBounds

/-!
# The closing limit of Polymath8b Lemma 4.1, at an arbitrary normalised kernel

The source closes Lemma 4.1 by replacing `B_x·K_{W(x)}(ξ,ξ')` by `Gap212.Sieve.limitKernel ξ ξ'`
under the integral sign, and its last paragraph says the totient kernel
needs "the only change" of one local factor. Accordingly **nothing below mentions a
kernel.** The normalised kernel is an arbitrary family `P : ℝ → ℝ → ℝ → ℂ` and the
only things asked of it are the two estimates the source produces,

* `hcrude`: `‖P x ξ ξ'‖ ≤ b·\log⁴x` for all `ξ, ξ'` — step 2's majorant times the normalisation, at
  whatever constant `b` the kernel's own bound carries;
* `hres`: `‖P x ξ ξ' - limitKernel ξ ξ'‖ ≤ ε·‖1+2πiξ‖·‖1+2πiξ'‖` for `|ξ|, |ξ'| ≤ √(\log x)` — the
  residue of `ζ` on the truncation range.

From those two the closing limit follows
(`Gap212.Sieve.tendsto_integral_of_forall_norm_closeDiff_le`), and the reciprocal and totient
kernels of Lemma 4.1 differ only in which instances of the two hypotheses they supply.

## Why the two estimates suffice, with no dominated convergence

The difference of the two integrands is bounded at **every** `(ξ,ξ')` at once by `ε` times the
fixed integrable `Gap212.Sieve.closeWeight F ξ · closeWeight G ξ'`
(`Gap212.Sieve.eventually_forall_norm_closeDiff_le`), so the limit is
`MeasureTheory.norm_integral_le_integral_norm` followed by `MeasureTheory.integral_mono`, applied
once. On the truncation range that is `hres`; off it, `hcrude` gives only `b\log⁴x`, and
`√(\log x) ≤ |ξ|` lets the transform absorb that whole power and still leave a factor `1/\log x`
(`Gap212.Sieve.pow_four_mul_norm_profileFourier_le`, from
`Gap212.Sieve.exists_forall_pow_mul_norm_profileFourier_tail_le` at order `12`). This is where the
truncation `|ξ| ≤ √(\log x)` is spent, and it is spent on the *integral*;
`Gap212.Sieve.eventually_forall_norm_profileFourier_tail_le` is the pointwise form.

## Main results

* `Gap212.Sieve.pow_four_mul_norm_profileFourier_le`, `..._one_add_abs_...`: the discarded range
  absorbs `\log⁴x` and the linear factor of `Gap212.Sieve.limitKernel`.
* `Gap212.Sieve.norm_closeDiff_le_of_sqrt_le_abs_left`, `..._right`: the estimate off the
  truncation.
* `Gap212.Sieve.eventually_forall_norm_closeDiff_le`: **one pointwise bound on all of `ℝ²`.**
* `Gap212.Sieve.tendsto_integral_of_forall_norm_closeDiff_le`: **the closing limit.**
-/

@[expose] public section

namespace Gap212.Sieve

open Filter MeasureTheory Real
open scoped ContDiff

/-! ## The discarded range -/

/-- The common absorption step: `L(1+|ξ|)²X ≤ C` gives `X ≤ (C/L)·closeWeight F ξ`. -/
private lemma le_div_mul_closeWeight (F : ℝ → ℝ) {L C ξ X : ℝ} (hL : 0 < L) (hX : 0 ≤ X)
    (h : L * ((1 + |ξ|) ^ 2 * X) ≤ C) : X ≤ C / L * closeWeight F ξ := by
  have hC : 0 ≤ C := le_trans (by positivity) h
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (inv_one_add_sq_le_closeWeight F ξ) (by positivity))
  rw [← div_eq_mul_inv, div_div, le_div_iff₀ (by positivity)]
  calc X * (L * (1 + ξ ^ 2)) ≤ X * (L * (1 + |ξ|) ^ 2) := by
        gcongr; nlinarith [sq_abs ξ, abs_nonneg ξ]
    _ = L * ((1 + |ξ|) ^ 2 * X) := by ring
    _ ≤ C := h

/-- `‖limitNum ξ‖ · ‖f(ξ)‖ ≤ closeWeight F ξ`, with the norm of the product split. -/
private lemma norm_limitNum_mul_norm_le_closeWeight (F : ℝ → ℝ) (ξ : ℝ) :
    ‖limitNum ξ‖ * ‖profileFourier F ξ‖ ≤ closeWeight F ξ := by
  simpa only [norm_mul] using norm_limitNum_mul_profileFourier_le_closeWeight F ξ

/-- **The crude power `\log⁴x` is absorbed on the discarded range.** For `√L ≤ |ξ|`,
`L⁴‖f(ξ)‖ ≤ (C/L)·closeWeight F ξ` whenever `L⁵(1+|ξ|)²‖f(ξ)‖ ≤ C` — which
`Gap212.Sieve.exists_forall_pow_mul_norm_profileFourier_tail_le` supplies at `(m,n) = (5,2)`. The
fifth power is what leaves a factor `1/L` over after the fourth has been spent. -/
theorem pow_four_mul_norm_profileFourier_le {F : ℝ → ℝ} {L C ξ : ℝ} (hL : 0 < L)
    (h : L ^ 5 * ((1 + |ξ|) ^ 2 * ‖profileFourier F ξ‖) ≤ C) :
    L ^ 4 * ‖profileFourier F ξ‖ ≤ C / L * closeWeight F ξ :=
  le_div_mul_closeWeight F hL (by positivity) (by linear_combination h)

/-- **The linear factor `1+|ξ|` is absorbed on the discarded range.** For `√L ≤ |ξ|`,
`(1+|ξ|)‖f(ξ)‖ ≤ (C/L)·closeWeight F ξ` whenever `L(1+|ξ|)³‖f(ξ)‖ ≤ C` — the order `(m,n) = (1,3)`
of `Gap212.Sieve.exists_forall_pow_mul_norm_profileFourier_tail_le`. This is what makes the
*limiting* integrand, whose size is linear in each variable, negligible off the truncation too. -/
theorem one_add_abs_mul_norm_profileFourier_le {F : ℝ → ℝ} {L C ξ : ℝ} (hL : 0 < L)
    (h : L ^ 1 * ((1 + |ξ|) ^ 3 * ‖profileFourier F ξ‖) ≤ C) :
    (1 + |ξ|) * ‖profileFourier F ξ‖ ≤ C / L * closeWeight F ξ :=
  le_div_mul_closeWeight F hL (by positivity) (by linear_combination h)

/-- **The discarded range, first coordinate.** Where `√(\log x) ≤ |ξ|` the difference of the two
integrands is at most `(bC₁+8C₂)/\log x` times the dominating function — no residue and no
truncation, only the crude bound `‖P‖ ≤ b\log⁴x` and the rapid decay of `f`. -/
theorem norm_closeDiff_le_of_sqrt_le_abs_left {F G : ℝ → ℝ} {x ξ b C₁ C₂ : ℝ} {P : ℂ} (hx : 1 < x)
    (hb : 0 ≤ b) (hP : ‖P‖ ≤ b * Real.log x ^ 4)
    (hC₁ : Real.log x ^ 5 * ((1 + |ξ|) ^ 2 * ‖profileFourier F ξ‖) ≤ C₁)
    (hC₂ : Real.log x ^ 1 * ((1 + |ξ|) ^ 3 * ‖profileFourier F ξ‖) ≤ C₂) (ξ' : ℝ) :
    ‖profileFourier F ξ * profileFourier G ξ' * (P - limitKernel ξ ξ')‖
      ≤ (b * C₁ + 8 * C₂) / Real.log x * (closeWeight F ξ * closeWeight G ξ') := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hcg : 0 ≤ closeWeight G ξ' := closeWeight_nonneg G ξ'
  have hcf : 0 ≤ closeWeight F ξ := closeWeight_nonneg F ξ
  have hC₁0 : 0 ≤ C₁ := le_trans (by positivity) hC₁
  have hC₂0 : 0 ≤ C₂ := le_trans (by positivity) hC₂
  have hcrude := pow_four_mul_norm_profileFourier_le (F := F) hlx hC₁
  have hlin := one_add_abs_mul_norm_profileFourier_le (F := F) hlx hC₂
  have hgle := norm_profileFourier_le_closeWeight G ξ'
  have hvg := norm_limitNum_mul_norm_le_closeWeight G ξ'
  have hLk : ‖limitKernel ξ ξ'‖ ≤ 8 * (1 + |ξ|) * ‖limitNum ξ'‖ :=
    (norm_limitKernel_le ξ ξ').trans (by gcongr; exact norm_limitNum_le_eight_mul ξ)
  rw [norm_mul, norm_mul]
  calc ‖profileFourier F ξ‖ * ‖profileFourier G ξ'‖ * ‖P - limitKernel ξ ξ'‖
      ≤ ‖profileFourier F ξ‖ * ‖profileFourier G ξ'‖ *
          (b * Real.log x ^ 4 + 8 * (1 + |ξ|) * ‖limitNum ξ'‖) := by
        gcongr; exact (norm_sub_le _ _).trans (add_le_add hP hLk)
    _ = b * (Real.log x ^ 4 * ‖profileFourier F ξ‖) * ‖profileFourier G ξ'‖ +
          8 * ((1 + |ξ|) * ‖profileFourier F ξ‖) *
            (‖limitNum ξ'‖ * ‖profileFourier G ξ'‖) := by ring
    _ ≤ b * (C₁ / Real.log x * closeWeight F ξ) * closeWeight G ξ' +
          8 * (C₂ / Real.log x * closeWeight F ξ) * closeWeight G ξ' := by gcongr
    _ = (b * C₁ + 8 * C₂) / Real.log x * (closeWeight F ξ * closeWeight G ξ') := by
        field_simp

/-- **The discarded range, second coordinate** —
`Gap212.Sieve.norm_closeDiff_le_of_sqrt_le_abs_left` with the roles of the two profiles exchanged.
Stated separately because the dominating function is a product of a function of `ξ` and a function
of `ξ'`, so the two coordinates enter the estimate differently even though the kernel treats them
alike. -/
theorem norm_closeDiff_le_of_sqrt_le_abs_right {F G : ℝ → ℝ} {x ξ' b C₁ C₂ : ℝ} {P : ℂ} (hx : 1 < x)
    (hb : 0 ≤ b) (hP : ‖P‖ ≤ b * Real.log x ^ 4) (ξ : ℝ)
    (hC₁ : Real.log x ^ 5 * ((1 + |ξ'|) ^ 2 * ‖profileFourier G ξ'‖) ≤ C₁)
    (hC₂ : Real.log x ^ 1 * ((1 + |ξ'|) ^ 3 * ‖profileFourier G ξ'‖) ≤ C₂) :
    ‖profileFourier F ξ * profileFourier G ξ' * (P - limitKernel ξ ξ')‖
      ≤ (b * C₁ + 8 * C₂) / Real.log x * (closeWeight F ξ * closeWeight G ξ') := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hcf : 0 ≤ closeWeight F ξ := closeWeight_nonneg F ξ
  have hcg : 0 ≤ closeWeight G ξ' := closeWeight_nonneg G ξ'
  have hC₁0 : 0 ≤ C₁ := le_trans (by positivity) hC₁
  have hC₂0 : 0 ≤ C₂ := le_trans (by positivity) hC₂
  have hcrude := pow_four_mul_norm_profileFourier_le (F := G) hlx hC₁
  have hlin := one_add_abs_mul_norm_profileFourier_le (F := G) hlx hC₂
  have hfle := norm_profileFourier_le_closeWeight F ξ
  have huf := norm_limitNum_mul_norm_le_closeWeight F ξ
  have hLk : ‖limitKernel ξ ξ'‖ ≤ ‖limitNum ξ‖ * (8 * (1 + |ξ'|)) :=
    (norm_limitKernel_le ξ ξ').trans (by gcongr; exact norm_limitNum_le_eight_mul ξ')
  rw [norm_mul, norm_mul]
  calc ‖profileFourier F ξ‖ * ‖profileFourier G ξ'‖ * ‖P - limitKernel ξ ξ'‖
      ≤ ‖profileFourier F ξ‖ * ‖profileFourier G ξ'‖ *
          (b * Real.log x ^ 4 + ‖limitNum ξ‖ * (8 * (1 + |ξ'|))) := by
        gcongr; exact (norm_sub_le _ _).trans (add_le_add hP hLk)
    _ = b * (Real.log x ^ 4 * ‖profileFourier G ξ'‖) * ‖profileFourier F ξ‖ +
          8 * ((1 + |ξ'|) * ‖profileFourier G ξ'‖) *
            (‖limitNum ξ‖ * ‖profileFourier F ξ‖) := by ring
    _ ≤ b * (C₁ / Real.log x * closeWeight G ξ') * closeWeight F ξ +
          8 * (C₂ / Real.log x * closeWeight G ξ') * closeWeight F ξ := by gcongr
    _ = (b * C₁ + 8 * C₂) / Real.log x * (closeWeight F ξ * closeWeight G ξ') := by
        field_simp

/-! ## One pointwise bound on all of `ℝ²` -/

/-- **The difference of the two integrands is uniformly small against one fixed integrable
function.** For every `ε > 0`, once `x` is large enough, at **every** `(ξ,ξ')`,

  `‖f(ξ)g(ξ')·(P x ξ ξ' - limitKernel ξ ξ')‖ ≤ ε·closeWeight F ξ·closeWeight G ξ'`.

Three cases, with the same dominating function in all three: on `|ξ|, |ξ'| ≤ √(\log x)` the residue
hypothesis `hres`, and off it `Gap212.Sieve.norm_closeDiff_le_of_sqrt_le_abs_left` or `..._right`
from the crude hypothesis `hcrude`. That the *same* integrable majorant works on both ranges is
what removes the need for a dominated-convergence argument. -/
theorem eventually_forall_norm_closeDiff_le {F G : ℝ → ℝ} (hFd : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hGd : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G)
    {P : ℝ → ℝ → ℝ → ℂ} {b ε : ℝ} (hb : 0 ≤ b)
    (hcrude : ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ, ‖P x ξ ξ'‖ ≤ b * Real.log x ^ 4)
    (hres : ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ, |ξ| ≤ Real.sqrt (Real.log x) →
      |ξ'| ≤ Real.sqrt (Real.log x) →
      ‖P x ξ ξ' - limitKernel ξ ξ'‖ ≤ ε * (‖limitNum ξ‖ * ‖limitNum ξ'‖))
    (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ w : ℝ × ℝ,
      ‖profileFourier F w.1 * profileFourier G w.2 * (P x w.1 w.2 - limitKernel w.1 w.2)‖
        ≤ ε * (closeWeight F w.1 * closeWeight G w.2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_forall_pow_mul_norm_profileFourier_tail_le hFd hFc 5 2
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_forall_pow_mul_norm_profileFourier_tail_le hFd hFc 1 3
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_forall_pow_mul_norm_profileFourier_tail_le hGd hGc 5 2
  obtain ⟨C₄, hC₄0, hC₄⟩ := exists_forall_pow_mul_norm_profileFourier_tail_le hGd hGc 1 3
  set M : ℝ := b * C₁ + 8 * C₂ + (b * C₃ + 8 * C₄)
  have hlarge : ∀ᶠ x : ℝ in atTop, M / Real.log x ≤ ε :=
    (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop).eventually (ge_mem_nhds hε)
  filter_upwards [hres, hcrude, hlarge, eventually_gt_atTop (1 : ℝ)] with x hr hc hML hx1 w
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hcf : 0 ≤ closeWeight F w.1 := closeWeight_nonneg F w.1
  have hcg : 0 ≤ closeWeight G w.2 := closeWeight_nonneg G w.2
  rcases le_or_gt (Real.sqrt (Real.log x)) |w.1| with h1 | h1
  · refine (norm_closeDiff_le_of_sqrt_le_abs_left (ξ := w.1) hx1 hb (hc w.1 w.2)
      (hC₁ _ _ hlx.le h1) (hC₂ _ _ hlx.le h1) w.2).trans ?_
    gcongr
    exact (div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hlx.le).trans hML
  rcases le_or_gt (Real.sqrt (Real.log x)) |w.2| with h2 | h2
  · refine (norm_closeDiff_le_of_sqrt_le_abs_right (ξ' := w.2) hx1 hb (hc w.1 w.2) w.1
      (hC₃ _ _ hlx.le h2) (hC₄ _ _ hlx.le h2)).trans ?_
    gcongr
    exact (div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hlx.le).trans hML
  · have := norm_limitNum_mul_norm_le_closeWeight F w.1
    have := norm_limitNum_mul_norm_le_closeWeight G w.2
    rw [norm_mul, norm_mul]
    calc ‖profileFourier F w.1‖ * ‖profileFourier G w.2‖ * ‖P x w.1 w.2 - limitKernel w.1 w.2‖
        ≤ ‖profileFourier F w.1‖ * ‖profileFourier G w.2‖ *
            (ε * (‖limitNum w.1‖ * ‖limitNum w.2‖)) := by gcongr; exact hr w.1 w.2 h1.le h2.le
      _ = ε * ((‖limitNum w.1‖ * ‖profileFourier F w.1‖) *
            (‖limitNum w.2‖ * ‖profileFourier G w.2‖)) := by ring
      _ ≤ ε * (closeWeight F w.1 * closeWeight G w.2) := by gcongr

/-! ## The closing limit -/

/-- **The closing limit of Polymath8b Lemma 4.1, at an arbitrary normalised kernel.** If the
integrand is eventually integrable and its difference from the limiting integrand is eventually
bounded by `ε` times one fixed integrable function at every point, then

  `∫_{ℝ²} f(ξ)g(ξ')·P x ξ ξ' ⟶ ∫_{ℝ²} f(ξ)g(ξ')·limitKernel ξ ξ'`.

`MeasureTheory.norm_integral_le_integral_norm` and `MeasureTheory.integral_mono`, applied once: the
whole limit is the single pointwise bound of
`Gap212.Sieve.eventually_forall_norm_closeDiff_le` integrated against
`Gap212.Sieve.integrable_closeWeight_mul`, with `ε` chosen against that integral's value. -/
theorem tendsto_integral_of_forall_norm_closeDiff_le {F G : ℝ → ℝ} (hFd : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hGd : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G)
    {P : ℝ → ℝ → ℝ → ℂ}
    (hPint : ∀ᶠ x : ℝ in atTop, Integrable fun w : ℝ × ℝ ↦
      profileFourier F w.1 * profileFourier G w.2 * P x w.1 w.2)
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ w : ℝ × ℝ,
      ‖profileFourier F w.1 * profileFourier G w.2 * (P x w.1 w.2 - limitKernel w.1 w.2)‖
        ≤ ε * (closeWeight F w.1 * closeWeight G w.2)) :
    Tendsto (fun x : ℝ ↦ ∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 * P x w.1 w.2)
      atTop (nhds (∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 *
        limitKernel w.1 w.2)) := by
  have hΩ : Integrable fun w : ℝ × ℝ ↦ closeWeight F w.1 * closeWeight G w.2 :=
    integrable_closeWeight_mul hFd hFc hGd hGc
  have hLk : Integrable fun w : ℝ × ℝ ↦
      profileFourier F w.1 * profileFourier G w.2 * limitKernel w.1 w.2 :=
    integrable_profileFourier_mul_limitKernel hFd hFc hGd hGc
  have hT0 : 0 ≤ ∫ w : ℝ × ℝ, closeWeight F w.1 * closeWeight G w.2 :=
    integral_closeWeight_mul_nonneg F G
  rw [Metric.tendsto_nhds]
  intro ε' hε'
  have hden : 0 < 2 * ((∫ w : ℝ × ℝ, closeWeight F w.1 * closeWeight G w.2) + 1) := by linarith
  filter_upwards [hbound _ (div_pos hε' hden), hPint] with x hD hPx
  have hDif : Integrable fun w : ℝ × ℝ ↦ profileFourier F w.1 * profileFourier G w.2 *
      (P x w.1 w.2 - limitKernel w.1 w.2) :=
    (hPx.sub hLk).congr (.of_forall fun w ↦ (mul_sub _ _ _).symm)
  rw [dist_eq_norm, ← integral_sub hPx hLk]
  calc ‖∫ w : ℝ × ℝ, (profileFourier F w.1 * profileFourier G w.2 * P x w.1 w.2 -
          profileFourier F w.1 * profileFourier G w.2 * limitKernel w.1 w.2)‖
      = ‖∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 *
          (P x w.1 w.2 - limitKernel w.1 w.2)‖ := by simp only [mul_sub]
    _ ≤ ∫ w : ℝ × ℝ, ‖profileFourier F w.1 * profileFourier G w.2 *
          (P x w.1 w.2 - limitKernel w.1 w.2)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ w : ℝ × ℝ, ε' / (2 * ((∫ w : ℝ × ℝ, closeWeight F w.1 * closeWeight G w.2) + 1)) *
          (closeWeight F w.1 * closeWeight G w.2) :=
        integral_mono hDif.norm (hΩ.const_mul _) hD
    _ = ε' / (2 * ((∫ w : ℝ × ℝ, closeWeight F w.1 * closeWeight G w.2) + 1)) *
          ∫ w : ℝ × ℝ, closeWeight F w.1 * closeWeight G w.2 := integral_const_mul _ _
    _ < ε' := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
        nlinarith

end Gap212.Sieve
