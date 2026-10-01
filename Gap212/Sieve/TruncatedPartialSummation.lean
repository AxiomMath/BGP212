/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Notation
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Partial summation on a truncated Möbius–totient sum

The sieve's inner sums are `∑_{f ≤ B/e, (f,e)=1} μ(f) F(log_x(ef))/φ(f)` with `F` a `C¹`
compactly-supported cutoff. This file replaces `F` by `F'` against the *truncated* partial sum
`S_e(w) = ∑_{f ≤ min(w, B/e), (f,e)=1} μ(f)/φ(f)`, exactly:

  `∑_{f ≤ B/e, (f,e)=1} μ(f) F(log_x(ef))/φ(f) = -∫_0^∞ F'(log_x e + v) S_e(x^v) dv`.

Nothing is estimated. The mechanism is that compact support gives `F(t) = -∫_t^∞ F'`, and that
the substitution `u = log_x e + v` carries the lower limit `log_x(ef)` to `v = log_x f`; the
`f`-sum at a given `v` is then over the `f ≤ x^v` inside the truncation, which is `S_e(x^v)`.

## The Jacobian is `1`, not `log x`

The substitution is a *translation* of the integration variable, `u = log_x e + v`, so it
contributes no Jacobian: `du = dv`. A factor `log x` would appear only if the integral were
written in the variable `w = x^v` rather than in `v` — there `dw = w log x dv`, and the factor comes
with a compensating `1/w`.

## Main definitions

* `Gap212.Sieve.coprimeBelow`: the positive integers `f ≤ t` coprime to `e`.
* `Gap212.Sieve.moebiusTotientBelow`: `∑_{f ≤ t, (f,e)=1} μ(f)/φ(f)`, from which the truncated
  partial sum `S_e(w)` is `moebiusTotientBelow e (min w (B/e))`.

## Main results

* `Gap212.Sieve.integral_Ioi_deriv_comp_const_add`: `∫_c^∞ F'(a+v) dv = -F(a+c)` for `F` of class
  `C¹` with compact support — the fundamental theorem of calculus in the shifted form used here.
* `Gap212.Sieve.truncated_moebius_partial_summation`: the identity.
-/

@[expose] public section

open ArithmeticFunction MeasureTheory Real Set
open scoped ArithmeticFunction.Moebius

namespace Gap212.Sieve

/-- The positive integers `f ≤ t` that are coprime to `e`. -/
noncomputable def coprimeBelow (e : ℕ) (t : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊t⌋₊).filter fun f => Nat.Coprime f e

/-- **The truncated Möbius–totient sum** `∑_{f ≤ t, (f,e)=1} μ(f)/φ(f)`. The partial sum
`S_e(w)` is this at `t = min w (B/e)`. -/
noncomputable def moebiusTotientBelow (e : ℕ) (t : ℝ) : ℝ :=
  ∑ f ∈ coprimeBelow e t, (μ f : ℝ) / (f.totient : ℝ)

/-- `f ∈ coprimeBelow e t` if and only if `f ≠ 0`, `f ≤ t` and `f` is coprime to `e`. -/
theorem mem_coprimeBelow {e f : ℕ} {t : ℝ} :
    f ∈ coprimeBelow e t ↔ f ≠ 0 ∧ (f : ℝ) ≤ t ∧ Nat.Coprime f e := by
  rw [coprimeBelow, Finset.mem_filter, Finset.mem_Icc]
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [Nat.le_floor_iff' hf]
    simp [Nat.one_le_iff_ne_zero, hf]

/-- Splitting the truncation: a sum up to `min t s` is the sum up to `s` with the terms above `t`
switched off. -/
theorem moebiusTotientBelow_min (e : ℕ) (t s : ℝ) :
    moebiusTotientBelow e (min t s)
      = ∑ f ∈ coprimeBelow e s, if (f : ℝ) ≤ t then (μ f : ℝ) / (f.totient : ℝ) else 0 := by
  rw [← Finset.sum_filter, moebiusTotientBelow]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext f
  simp only [Finset.mem_filter, mem_coprimeBelow, le_min_iff]
  tauto

/-- `log_x` is Mathlib's base-`x` logarithm, so its API applies verbatim. -/
theorem logx_eq_logb (x d : ℝ) : Gap212.Notation.logx x d = logb x d := rfl

/-- **The fundamental theorem of calculus, shifted.** For `F` of class `C¹` with compact support,
`∫_c^∞ F'(a + v) dv = -F(a + c)`. -/
theorem integral_Ioi_deriv_comp_const_add {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) (a c : ℝ) : ∫ v in Ioi c, deriv F (a + v) = -F (a + c) := by
  have hcd : ContDiff ℝ 1 fun v => F (a + v) := hF.comp (contDiff_const.add contDiff_id)
  have hcs : HasCompactSupport fun v => F (a + v) := by
    simpa [Function.comp_def] using hFc.comp_homeomorph (Homeomorph.addLeft a)
  simpa only [deriv_comp_const_add] using HasCompactSupport.integral_Ioi_deriv_eq hcd hcs c

/-- **Partial summation for the truncated Möbius–totient sum.** For `F` of class `C¹` with compact
support, `x > 1`, `e ≥ 1` and `B ≥ 1`,

  `∑_{f ≤ B/e, (f,e)=1} μ(f) F(log_x(ef))/φ(f) = -∫_0^∞ F'(log_x e + v) S_e(x^v) dv`,

with `S_e(w) = ∑_{f ≤ min(w, B/e), (f,e)=1} μ(f)/φ(f)`. An exact identity: the right-hand side is
the left-hand side, term by term, after `F(log_x(ef)) = -∫_{log_x f}^∞ F'(log_x e + v) dv`.

The hypothesis `1 ≤ B` is not used in the proof. `1 ≤ e` is used, and cannot be dropped:
`log_x 0` is not the exponent of `0`.

There is no `log x` in the display: the substitution `u = log_x e + v` is a translation,
`du = dv`. -/
theorem truncated_moebius_partial_summation {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {x : ℝ} (hx : 1 < x) {e : ℕ} (he : 1 ≤ e) {B : ℝ}
    (_hB : 1 ≤ B) :
    ∑ f ∈ coprimeBelow e (B / e), (μ f : ℝ) * F (Notation.logx x (e * f)) / (f.totient : ℝ)
      = -∫ v in Ioi (0 : ℝ),
          deriv F (Notation.logx x e + v) * moebiusTotientBelow e (min (x ^ v) (B / e)) := by
  have hlogx : 0 < log x := Real.log_pos hx
  have hIci : ∀ g : ℝ → ℝ, ∫ v in Ioi (0 : ℝ), g v = ∫ v in Ici (0 : ℝ), g v := fun _ =>
    setIntegral_congr_set Ioi_ae_eq_Ici
  -- The `f`-th term of the integrand is the indicator of `v ≥ log_x f`.
  have hcond : ∀ f : ℕ, f ≠ 0 → ∀ v : ℝ, (Notation.logx x f ≤ v ↔ (f : ℝ) ≤ x ^ v) := by
    intro f hf v
    rw [logx_eq_logb]
    exact Real.logb_le_iff_le_rpow hx (by positivity)
  have hnonneg : ∀ f : ℕ, f ≠ 0 → 0 ≤ Notation.logx x f := by
    intro f hf
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hf))
      hlogx.le
  have hsum : ∀ v : ℝ, deriv F (Notation.logx x e + v)
      * moebiusTotientBelow e (min (x ^ v) (B / e))
      = ∑ f ∈ coprimeBelow e (B / e), (Ici (Notation.logx x f)).indicator
          (fun v => (μ f : ℝ) / (f.totient : ℝ) * deriv F (Notation.logx x e + v)) v := by
    intro v
    rw [moebiusTotientBelow_min, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f hf => ?_
    have hf0 : f ≠ 0 := (mem_coprimeBelow.mp hf).1
    simp only [Set.indicator_apply, mem_Ici, hcond f hf0 v]
    split_ifs <;> ring
  -- Each term is integrable, being a bounded piece of a compactly-supported continuous function.
  have hcont : Continuous fun v : ℝ => deriv F (Notation.logx x e + v) :=
    (hF.continuous_deriv le_rfl).comp (continuous_const.add continuous_id)
  have hdcs : HasCompactSupport fun v : ℝ => deriv F (Notation.logx x e + v) := by
    simpa [Function.comp_def] using
      hFc.deriv.comp_homeomorph (Homeomorph.addLeft (Notation.logx x e))
  have hint : ∀ f ∈ coprimeBelow e (B / e), IntegrableOn
      ((Ici (Notation.logx x f)).indicator
        fun v => (μ f : ℝ) / (f.totient : ℝ) * deriv F (Notation.logx x e + v)) (Ici (0 : ℝ)) :=
    fun f _ => (((hcont.integrable_of_hasCompactSupport hdcs).const_mul
      ((μ f : ℝ) / (f.totient : ℝ))).indicator measurableSet_Ici).integrableOn
  -- Exchange the finite sum with the integral.
  have hexch : ∫ v in Ici (0 : ℝ), deriv F (Notation.logx x e + v)
        * moebiusTotientBelow e (min (x ^ v) (B / e))
      = ∑ f ∈ coprimeBelow e (B / e), ∫ v in Ici (0 : ℝ),
          (Ici (Notation.logx x f)).indicator
            (fun v => (μ f : ℝ) / (f.totient : ℝ) * deriv F (Notation.logx x e + v)) v := by
    simp_rw [hsum]
    exact integral_finsetSum _ hint
  -- Evaluate each term by the shifted fundamental theorem of calculus.
  have hterm : ∀ f ∈ coprimeBelow e (B / e), (∫ v in Ici (0 : ℝ),
        (Ici (Notation.logx x f)).indicator
          (fun v => (μ f : ℝ) / (f.totient : ℝ) * deriv F (Notation.logx x e + v)) v)
      = -((μ f : ℝ) / (f.totient : ℝ) * F (Notation.logx x (e * f))) := by
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
  exact Finset.sum_congr rfl fun f _ => by ring

end Gap212.Sieve
