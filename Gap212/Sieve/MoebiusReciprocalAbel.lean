/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MoebiusReciprocalSeries
public import Gap212.Sieve.TruncatedReciprocalSummation
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Abel integral of the truncated reciprocal-weight Möbius sum

With `S_q(w) = ∑_{f ≤ w, (f,q)=1} μ(f)/f` and
`g_q(s) = ∑_{(f,q)=1} μ(f) f^{-1-s} = ∏_{p ∤ q}(1 - p^{-1-s})`, the Mellin transform of `S_q`
is the Dirichlet series divided by `s`:

  `∫_1^∞ S_q(w) w^{-s-1} dw = g_q(s)/s`   (`s > 0`).

Putting `w = exp u` this is the Abel integral `∫_0^∞ S_q(exp u) e^{-su} du` at the reciprocal
weight, and combining with `Gap212.Sieve.tendsto_moebiusReciprocalSeries_div` it converges, as
`s → 0⁺`, to `q/φ(q)`.

The proof is the exchange of the `f`-sum with the `w`-integral: the `f`-th term of `S_q(w)` is
switched on exactly for `w ≥ f`, so it contributes `(μ(f)/f) ∫_f^∞ w^{-s-1} dw = μ(f) f^{-1-s}/s`,
and the exchange is legitimate because `∑_f f^{-1-s}/s < ∞` for `s > 0`.

## Abel summability

The convergence of `∫_0^∞ S_q(exp u) e^{-su} du` as `s → 0⁺` is Abel summability, weaker than the
convergence of `∫_0^∞ S_q(exp u) du`, which dominated convergence on the `v`-integral of
`Gap212.Sieve.truncated_moebius_reciprocal_partial_summation` needs. The elementary bound
`|S_q| ≤ 1` is not integrable over a range of length `Θ(log x)`; the integrable majorant is
`Gap212.Sieve.MoebiusPartialSumDecay`, proved as `Gap212.Sieve.moebiusPartialSumDecay`, and the
undamped integral is `Gap212.Sieve.integral_moebiusReciprocalBelow_exp`.

## Main definitions

* `Gap212.Sieve.moebiusReciprocalCoeff`: `μ(f)/f` on the `f` coprime to `q`, `0` elsewhere.
* `Gap212.Sieve.mellinPiece`: the `f`-th piece `1_{[f,∞)}(w) (μ(f)/f) w^{-s-1}` of the integrand.

## Main results

* `Gap212.Sieve.integral_mellinPiece`: `∫_1^∞ 1_{[f,∞)}(w) a w^{-s-1} dw = a f^{-s}/s`.
* `Gap212.Sieve.integral_moebiusReciprocalBelow_rpow`: `∫_1^∞ S_q(w) w^{-s-1} dw = g_q(s)/s`.
* `Gap212.Sieve.tendsto_integral_moebiusReciprocalBelow_rpow`: that integral tends to `q/φ(q)`
  as `s → 0⁺`.
-/

@[expose] public section

open ArithmeticFunction Filter MeasureTheory Set Topology
open scoped ArithmeticFunction.Moebius

namespace Gap212.Sieve

/-- `μ(f)/f` on the `f` coprime to `q`, and `0` elsewhere: the coefficient of `S_q`. -/
noncomputable def moebiusReciprocalCoeff (q f : ℕ) : ℝ :=
  if Nat.Coprime f q then (μ f : ℝ) / (f : ℝ) else 0

/-- `moebiusReciprocalCoeff q 0 = 0`. -/
theorem moebiusReciprocalCoeff_zero (q : ℕ) : moebiusReciprocalCoeff q 0 = 0 := by
  simp [moebiusReciprocalCoeff]

/-- `|moebiusReciprocalCoeff q f| ≤ f⁻¹`, with `f⁻¹` written as `(f : ℝ) ^ (-1 : ℝ)`. -/
theorem abs_moebiusReciprocalCoeff_le (q f : ℕ) :
    |moebiusReciprocalCoeff q f| ≤ ((f : ℝ) ^ (-1 : ℝ)) := by
  have hmu : |(μ f : ℝ)| ≤ 1 := mod_cast abs_moebius_le_one
  rw [Real.rpow_neg_one, moebiusReciprocalCoeff]
  split_ifs
  · rw [abs_div, Nat.abs_cast, ← one_div]
    gcongr
  · simp

/-- The `f`-th piece of the Mellin integrand: `w^{-s-1}` scaled by `μ(f)/f` and switched on for
`w ≥ f`. -/
noncomputable def mellinPiece (q : ℕ) (s : ℝ) (f : ℕ) (w : ℝ) : ℝ :=
  (Ici (f : ℝ)).indicator (fun w => moebiusReciprocalCoeff q f * w ^ (-s - 1)) w

/-- The `0`-th piece vanishes identically: `mellinPiece q s 0 = 0`. -/
theorem mellinPiece_zero (q : ℕ) (s : ℝ) : mellinPiece q s 0 = 0 := by
  funext w
  simp [mellinPiece, moebiusReciprocalCoeff_zero, Set.indicator_apply]

/-- `∫_1^∞ 1_{[f,∞)}(w) a w^{-s-1} dw = a f^{-s}/s` for `s > 0`. The lower limit `1` is absorbed:
`f ≥ 1`, so the integration range is `(f, ∞)` up to a null set. -/
theorem integral_indicator_Ici_rpow {s : ℝ} (hs : 0 < s) {f : ℕ} (hf : f ≠ 0) (a : ℝ) :
    (∫ w in Ioi (1 : ℝ), (Ici (f : ℝ)).indicator (fun w => a * w ^ (-s - 1)) w)
      = a * ((f : ℝ) ^ (-s) / s) := by
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := mod_cast Nat.one_le_iff_ne_zero.2 hf
  rw [setIntegral_indicator measurableSet_Ici,
    setIntegral_congr_set ((ae_eq_refl _).inter Ioi_ae_eq_Ici.symm), Ioi_inter_Ioi,
    sup_eq_right.2 hf1, integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) (by linarith),
    show -s - 1 + 1 = -s by ring, neg_div_neg_eq]

/-- Each piece is integrable on `(1, ∞)`. -/
theorem integrableOn_mellinPiece (q : ℕ) {s : ℝ} (hs : 0 < s) (f : ℕ) :
    IntegrableOn (mellinPiece q s f) (Ioi (1 : ℝ)) :=
  ((integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _).indicator measurableSet_Ici

/-- The integral of a piece. -/
theorem integral_mellinPiece (q : ℕ) {s : ℝ} (hs : 0 < s) (f : ℕ) :
    (∫ w in Ioi (1 : ℝ), mellinPiece q s f w)
      = moebiusReciprocalCoeff q f * ((f : ℝ) ^ (-s) / s) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp [mellinPiece_zero, moebiusReciprocalCoeff_zero]
  · exact integral_indicator_Ici_rpow hs hf _

/-- The integral of the norm of a piece. -/
theorem integral_norm_mellinPiece (q : ℕ) {s : ℝ} (hs : 0 < s) (f : ℕ) :
    (∫ w in Ioi (1 : ℝ), ‖mellinPiece q s f w‖)
      = |moebiusReciprocalCoeff q f| * ((f : ℝ) ^ (-s) / s) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp [mellinPiece_zero, moebiusReciprocalCoeff_zero]
  refine (setIntegral_congr_fun measurableSet_Ioi fun w (hw : 1 < w) ↦ ?_).trans
    (integral_indicator_Ici_rpow hs hf _)
  simp only [mellinPiece, indicator_apply]
  split_ifs <;> simp [abs_of_pos (Real.rpow_pos_of_pos (one_pos.trans hw) _)]

/-- The pieces sum pointwise to the integrand:
`S_q(w) w^{-s-1} = ∑_f 1_{[f,∞)}(w) (μ(f)/f) w^{-s-1}`. Both sides are finite sums at each `w`,
so no hypothesis on `w` is needed. -/
theorem tsum_mellinPiece (q : ℕ) (s : ℝ) (w : ℝ) :
    ∑' f : ℕ, mellinPiece q s f w = moebiusReciprocalBelow q w * w ^ (-s - 1) := by
  have h0 : (0 : ℕ) ∉ coprimeBelow q w := fun h => (mem_coprimeBelow.mp h).1 rfl
  have hz : ∀ f ∉ insert 0 (coprimeBelow q w), mellinPiece q s f w = 0 := by
    intro f hf
    simp only [Finset.mem_insert, mem_coprimeBelow, not_or] at hf
    simp only [mellinPiece, indicator_apply, mem_Ici, moebiusReciprocalCoeff]
    split_ifs <;> simp_all
  rw [tsum_eq_sum hz, Finset.sum_insert h0, mellinPiece_zero, Pi.zero_apply, zero_add,
    moebiusReciprocalBelow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun f hf => ?_
  obtain ⟨-, hle, hcop⟩ := mem_coprimeBelow.mp hf
  simp [mellinPiece, moebiusReciprocalCoeff, hle, hcop]

/-- The norms' integrals are summable: they are bounded by `f^{-1-s}/s`. -/
theorem summable_integral_norm_mellinPiece (q : ℕ) {s : ℝ} (hs : 0 < s) :
    Summable fun f : ℕ => ∫ w in Ioi (1 : ℝ), ‖mellinPiece q s f w‖ := by
  have hb : Summable fun f : ℕ => (f : ℝ) ^ (-(1 + s)) / s :=
    (Real.summable_nat_rpow.mpr (by linarith)).div_const s
  refine hb.of_nonneg_of_le (fun f => integral_nonneg fun _ => norm_nonneg _) fun f => ?_
  rw [integral_norm_mellinPiece q hs, neg_add,
    Real.rpow_add' (Nat.cast_nonneg f) (by linarith : -1 + -s < 0).ne, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right (abs_moebiusReciprocalCoeff_le q f) (by positivity)

/-- **The Mellin transform of the truncated reciprocal-weight Möbius sum.** For `s > 0`,

  `∫_1^∞ S_q(w) w^{-s-1} dw = g_q(s)/s`,

with `S_q(w) = ∑_{f ≤ w, (f,q)=1} μ(f)/f` and `g_q(s) = ∑_{(f,q)=1} μ(f) f^{-1-s}`. Putting
`w = exp u` this is the Abel integral `∫_0^∞ S_q(exp u) e^{-su} du`. -/
theorem integral_moebiusReciprocalBelow_rpow (q : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫ w in Ioi (1 : ℝ), moebiusReciprocalBelow q w * w ^ (-s - 1))
      = moebiusReciprocalSeries q s / s := by
  have hterm : ∀ f : ℕ, (∫ w in Ioi (1 : ℝ), mellinPiece q s f w)
      = moebiusCoprimeTerm q s f / s := fun f ↦ by
    rw [integral_mellinPiece q hs f, moebiusReciprocalCoeff, moebiusCoprimeTerm, neg_add,
      Real.rpow_add' (Nat.cast_nonneg f) (by linarith : -1 + -s < 0).ne, Real.rpow_neg_one]
    split_ifs
    · ring
    · simp
  rw [← setIntegral_congr_fun measurableSet_Ioi fun w _ ↦ tsum_mellinPiece q s w,
    ← integral_tsum_of_summable_integral_norm (integrableOn_mellinPiece q hs)
      (summable_integral_norm_mellinPiece q hs)]
  simp only [hterm, tsum_div_const, moebiusReciprocalSeries]

/-- **The Abel constant.** For `q ≥ 1` the Mellin transform above tends to `q/φ(q)` as `s → 0⁺`.

This is `lim_{s→0⁺} g_q(s)/s = q/φ(q)`, an Abel limit. The convergence of the undamped integral
`∫_0^∞ S_q(exp u) du` to the same value is `Gap212.Sieve.integral_moebiusReciprocalBelow_exp`,
which uses the integrable majorant `Gap212.Sieve.MoebiusPartialSumDecay`. -/
theorem tendsto_integral_moebiusReciprocalBelow_rpow {q : ℕ} (hq : 1 ≤ q) :
    Tendsto (fun s : ℝ => ∫ w in Ioi (1 : ℝ), moebiusReciprocalBelow q w * w ^ (-s - 1))
      (nhdsWithin 0 (Ioi 0)) (nhds ((q : ℝ) / (q.totient : ℝ))) := by
  refine (tendsto_moebiusReciprocalSeries_div hq).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (integral_moebiusReciprocalBelow_rpow q (hs : (0 : ℝ) < s)).symm

end Gap212.Sieve
