/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.TruncatedPartialSummation

/-!
# Partial summation on a truncated Möbius sum, reciprocal weight

`Gap212.Sieve.truncated_moebius_partial_summation` performs partial summation for the weight
`μ(f)/φ(f)`.
The least-common-multiple main term of the sieve produces `μ(f)/f` instead — the identity
`(d,d') = ∑_{e ∣ (d,d')} φ(e)` leaves a `1/f` and not a `1/φ(f)` — and the two weights must not be
conflated: their generating functions differ, and so do their constants.

The argument is indifferent to the weight, so the identity is proved here once for an arbitrary
`g : ℕ → ℝ`:

  `∑_{f ≤ B/e, (f,e)=1} g(f) F(log_x(ef))
     = -∫_0^∞ F'(log_x e + v) ∑_{f ≤ min(x^v, B/e), (f,e)=1} g(f) dv`,

and then specialised to `g f = μ(f)/f`. Compact support gives `F(t) = -∫_t^∞ F'`, and
`u = log_x e + v` is a *translation*, so `du = dv` and there is no `log x` Jacobian.

## Main definitions

* `Gap212.Sieve.moebiusReciprocalBelow`: `∑_{f ≤ t, (f,e)=1} μ(f)/f`, the partial sum `S_e(w)` for
  the reciprocal weight at `t = min w (B/e)`.

## Main results

* `Gap212.Sieve.truncated_partial_summation_weighted`: the identity for an arbitrary weight.
* `Gap212.Sieve.truncated_moebius_reciprocal_partial_summation`: the identity at `g f = μ(f)/f`.
-/

@[expose] public section

open ArithmeticFunction MeasureTheory Real Set
open scoped ArithmeticFunction.Moebius

namespace Gap212.Sieve

/-- **The truncated Möbius sum with reciprocal weight** `∑_{f ≤ t, (f,e)=1} μ(f)/f`. -/
noncomputable def moebiusReciprocalBelow (e : ℕ) (t : ℝ) : ℝ :=
  ∑ f ∈ coprimeBelow e t, (μ f : ℝ) / (f : ℝ)

/-- Splitting the truncation for an arbitrary weight: a sum up to `min t s` is the sum up to `s`
with the terms above `t` switched off. -/
theorem sum_coprimeBelow_min (e : ℕ) (g : ℕ → ℝ) (t s : ℝ) :
    ∑ f ∈ coprimeBelow e (min t s), g f
      = ∑ f ∈ coprimeBelow e s, if (f : ℝ) ≤ t then g f else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext f
  simp only [Finset.mem_filter, mem_coprimeBelow, le_min_iff]
  tauto

/-- **Partial summation for an arbitrary weight.** For `F` of class `C¹` with compact
support, `x > 1` and `e ≥ 1`,

  `∑_{f ≤ B/e, (f,e)=1} g(f) F(log_x(ef))
     = -∫_0^∞ F'(log_x e + v) ∑_{f ≤ min(x^v, B/e), (f,e)=1} g(f) dv`.

An exact identity: the right-hand side is the left-hand side term by term, after
`F(log_x(ef)) = -∫_{log_x f}^∞ F'(log_x e + v) dv`. `1 ≤ e` is used and cannot be dropped;
`B` is unrestricted.

**Stated at an arbitrary weight `g`**, because nothing in the identity uses any property of `g`
and the sieve needs it
at two weights: `μ(f)/φ(f)` for the totient-denominator inner sum and `μ(f)/f` for the
least-common-multiple one. `Gap212.Sieve.truncated_moebius_partial_summation` is this identity's
`μ(f)/φ(f)` instance. -/
@[gap212 "lem_truncated_moebius_partial_summation"]
theorem truncated_partial_summation_weighted {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {x : ℝ} (hx : 1 < x) {e : ℕ} (he : 1 ≤ e) {B : ℝ} (g : ℕ → ℝ) :
    ∑ f ∈ coprimeBelow e (B / e), g f * F (Notation.logx x (e * f))
      = -∫ v in Ioi (0 : ℝ), deriv F (Notation.logx x e + v)
          * ∑ f ∈ coprimeBelow e (min (x ^ v) (B / e)), g f := by
  have hlogx : 0 < log x := Real.log_pos hx
  have hIci : ∀ h : ℝ → ℝ, ∫ v in Ioi (0 : ℝ), h v = ∫ v in Ici (0 : ℝ), h v := fun _ =>
    setIntegral_congr_set Ioi_ae_eq_Ici
  have hcond : ∀ f : ℕ, f ≠ 0 → ∀ v : ℝ, (Notation.logx x f ≤ v ↔ (f : ℝ) ≤ x ^ v) := by
    intro f hf v
    rw [logx_eq_logb]
    exact Real.logb_le_iff_le_rpow hx (by positivity)
  have hnonneg : ∀ f : ℕ, f ≠ 0 → 0 ≤ Notation.logx x f := fun f hf =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hf)) hlogx.le
  have hsum : ∀ v : ℝ, deriv F (Notation.logx x e + v)
      * ∑ f ∈ coprimeBelow e (min (x ^ v) (B / e)), g f
      = ∑ f ∈ coprimeBelow e (B / e), (Ici (Notation.logx x f)).indicator
          (fun v => g f * deriv F (Notation.logx x e + v)) v := by
    intro v
    rw [sum_coprimeBelow_min, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f hf => ?_
    have hf0 : f ≠ 0 := (mem_coprimeBelow.mp hf).1
    simp only [Set.indicator_apply, mem_Ici, hcond f hf0 v]
    split_ifs <;> ring
  have hcont : Continuous fun v : ℝ => deriv F (Notation.logx x e + v) :=
    (hF.continuous_deriv le_rfl).comp (continuous_const.add continuous_id)
  have hdcs : HasCompactSupport fun v : ℝ => deriv F (Notation.logx x e + v) := by
    simpa [Function.comp_def] using
      hFc.deriv.comp_homeomorph (Homeomorph.addLeft (Notation.logx x e))
  have hint : ∀ f ∈ coprimeBelow e (B / e), IntegrableOn
      ((Ici (Notation.logx x f)).indicator fun v => g f * deriv F (Notation.logx x e + v))
      (Ici (0 : ℝ)) :=
    fun f _ => (((hcont.integrable_of_hasCompactSupport hdcs).const_mul (g f)).indicator
      measurableSet_Ici).integrableOn
  have hexch : ∫ v in Ici (0 : ℝ), deriv F (Notation.logx x e + v)
        * ∑ f ∈ coprimeBelow e (min (x ^ v) (B / e)), g f
      = ∑ f ∈ coprimeBelow e (B / e), ∫ v in Ici (0 : ℝ),
          (Ici (Notation.logx x f)).indicator
            (fun v => g f * deriv F (Notation.logx x e + v)) v := by
    simp_rw [hsum]
    exact integral_finsetSum _ hint
  have hterm : ∀ f ∈ coprimeBelow e (B / e), (∫ v in Ici (0 : ℝ),
        (Ici (Notation.logx x f)).indicator (fun v => g f * deriv F (Notation.logx x e + v)) v)
      = -(g f * F (Notation.logx x (e * f))) := by
    intro f hf
    have hf0 : f ≠ 0 := (mem_coprimeBelow.mp hf).1
    have hshift : Notation.logx x e + Notation.logx x f = Notation.logx x (e * f) := by
      simp only [Notation.logx, Real.log_mul (Nat.cast_ne_zero.mpr (by omega : e ≠ 0))
        (Nat.cast_ne_zero.mpr hf0)]
      ring
    rw [setIntegral_indicator measurableSet_Ici, Ici_inter_Ici, max_eq_right (hnonneg f hf0),
      ← setIntegral_congr_set (Ioi_ae_eq_Ici (a := Notation.logx x f)),
      integral_const_mul, integral_Ioi_deriv_comp_const_add hF hFc, hshift]
    ring
  rw [hIci, hexch, Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, neg_neg]

/-- **Partial summation for the reciprocal weight.** For `F` of class `C¹` with compact support,
`x > 1` and `e ≥ 1`,

  `∑_{f ≤ B/e, (f,e)=1} μ(f) F(log_x(ef))/f = -∫_0^∞ F'(log_x e + v) S_e(min(x^v, B/e)) dv`,

with `S_e(w) = ∑_{f ≤ w, (f,e)=1} μ(f)/f`. This is the reciprocal-weight companion of
`Gap212.Sieve.truncated_moebius_partial_summation`, with `1/φ(f)` replaced by `1/f`; both are
instances of `Gap212.Sieve.truncated_partial_summation_weighted`. -/
theorem truncated_moebius_reciprocal_partial_summation {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {x : ℝ} (hx : 1 < x) {e : ℕ} (he : 1 ≤ e) {B : ℝ} :
    ∑ f ∈ coprimeBelow e (B / e), (μ f : ℝ) * F (Notation.logx x (e * f)) / (f : ℝ)
      = -∫ v in Ioi (0 : ℝ),
          deriv F (Notation.logx x e + v) * moebiusReciprocalBelow e (min (x ^ v) (B / e)) := by
  have h := truncated_partial_summation_weighted hF hFc hx he (B := B)
    (fun f => (μ f : ℝ) / (f : ℝ))
  simp only [moebiusReciprocalBelow]
  rw [← h]
  exact Finset.sum_congr rfl fun f _ => by ring

end Gap212.Sieve
