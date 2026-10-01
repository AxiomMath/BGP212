/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MoebiusReciprocalAbel
public import Gap212.Sieve.MoebiusTotientSeries

/-!
# The Abel integral of the truncated totient-weight Möbius sum

With `T_e(w) = ∑_{f ≤ w, (f,e)=1} μ(f)/φ(f)` and
`h_e(s) = ∑_{(f,e)=1} μ(f)/(φ(f) f^s) = ∏_{p ∤ e}(1 - 1/((p-1)p^s))`, the Mellin transform of
`T_e` is the Dirichlet series divided by `s`:

  `∫_1^∞ T_e(w) w^{-s-1} dw = h_e(s)/s`   (`s > 0`).

Putting `w = exp u` this is the Abel integral `∫_0^∞ T_e(exp u) e^{-su} du` of the totient-weight
inner sum, and combining with `Gap212.Sieve.tendsto_moebiusTotientSeries_div` it converges, as
`s → 0⁺`, to
`c_e = (e/φ(e)) ∏_{p ∤ e}(1 - 1/(p-1)^2)` for even `e`.

The proof is the same exchange of the `f`-sum with the `w`-integral as in
`Gap212.Sieve.MoebiusReciprocalAbel`: the `f`-th term of `T_e(w)` is switched on exactly for
`w ≥ f`, so it contributes `(μ(f)/φ(f)) ∫_f^∞ w^{-s-1} dw = μ(f)/(φ(f) f^s)/s`, and the exchange is
legitimate because `∑_f |μ(f)|/(φ(f) f^s) < ∞` for `s > 0`
(`Gap212.Sieve.summable_abs_moebius_div_totient_mul_rpow`). The elementary bound
`|μ(f)|/φ(f) ≤ 1` would not suffice: it leaves `∑_f f^{-s}`, divergent for `s ≤ 1`.

## Abel summability

The convergence of `∫_0^∞ T_e(exp u) e^{-su} du` as `s → 0⁺` is Abel summability, weaker than the
convergence of `∫_0^∞ T_e(exp u) du`, which dominated convergence on the `v`-integral of
`Gap212.Sieve.truncated_moebius_totient_partial_summation` needs. The passage between them, using
the log-power decay, is `Gap212.Sieve.integral_moebiusTotientBelow_exp` in
`Gap212.Sieve.MoebiusTotientDecay`.

## Main definitions

* `Gap212.Sieve.moebiusTotientCoeff`: `μ(f)/φ(f)` on the `f` coprime to `e`, `0` elsewhere.
* `Gap212.Sieve.mellinPieceTotient`: the `f`-th piece `1_{[f,∞)}(w) (μ(f)/φ(f)) w^{-s-1}` of the
  integrand.

## Main results

* `Gap212.Sieve.integral_mellinPieceTotient`: `∫_1^∞ 1_{[f,∞)}(w) a w^{-s-1} dw = a f^{-s}/s`.
* `Gap212.Sieve.integral_moebiusTotientBelow_rpow`: `∫_1^∞ T_e(w) w^{-s-1} dw = h_e(s)/s`.
* `Gap212.Sieve.tendsto_integral_moebiusTotientBelow_rpow`: that integral tends to `c_e` as
  `s → 0⁺`, for even `e ≥ 1`.
-/

@[expose] public section

open ArithmeticFunction Filter MeasureTheory Set Topology
open scoped ArithmeticFunction.Moebius

namespace Gap212.Sieve

/-- `μ(f)/φ(f)` on the `f` coprime to `e`, and `0` elsewhere: the coefficient of `T_e`. -/
noncomputable def moebiusTotientCoeff (e f : ℕ) : ℝ :=
  if Nat.Coprime f e then (μ f : ℝ) / (f.totient : ℝ) else 0

/-- The coefficient `moebiusTotientCoeff e` vanishes at `0`. -/
theorem moebiusTotientCoeff_zero (e : ℕ) : moebiusTotientCoeff e 0 = 0 := by
  simp [moebiusTotientCoeff]

/-- `|moebiusTotientCoeff e f| ≤ |μ(f)|/φ(f)`. -/
theorem abs_moebiusTotientCoeff_le (e f : ℕ) :
    |moebiusTotientCoeff e f| ≤ |(μ f : ℝ)| / (f.totient : ℝ) := by
  simp only [moebiusTotientCoeff]
  split_ifs
  · rw [abs_div, Nat.abs_cast]
  · rw [abs_zero]
    positivity

/-- The coefficient of the Dirichlet series is the coefficient of `T_e` damped by `f^{-s}`. -/
theorem moebiusTotientCoeff_mul_rpow (e : ℕ) (s : ℝ) (f : ℕ) :
    moebiusTotientCoeff e f * (f : ℝ) ^ (-s) = moebiusTotientCoprimeTerm e s f := by
  rw [moebiusTotientCoeff, moebiusTotientCoprimeTerm, Real.rpow_neg (Nat.cast_nonneg f)]
  split_ifs
  · ring
  · rw [zero_mul]

/-- The `f`-th piece of the Mellin integrand: `w^{-s-1}` scaled by `μ(f)/φ(f)` and switched on for
`w ≥ f`. -/
noncomputable def mellinPieceTotient (e : ℕ) (s : ℝ) (f : ℕ) (w : ℝ) : ℝ :=
  (Ici (f : ℝ)).indicator (fun w => moebiusTotientCoeff e f * w ^ (-s - 1)) w

/-- The `0`-th piece `mellinPieceTotient e s 0` is identically zero. -/
theorem mellinPieceTotient_zero (e : ℕ) (s : ℝ) : mellinPieceTotient e s 0 = 0 := by
  funext w
  simp [mellinPieceTotient, moebiusTotientCoeff_zero, Set.indicator_apply]

/-- Each piece is integrable on `(1, ∞)`. -/
theorem integrableOn_mellinPieceTotient (e : ℕ) {s : ℝ} (hs : 0 < s) (f : ℕ) :
    IntegrableOn (mellinPieceTotient e s f) (Ioi (1 : ℝ)) :=
  ((integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _).indicator measurableSet_Ici

/-- The integral of a piece. -/
theorem integral_mellinPieceTotient (e : ℕ) {s : ℝ} (hs : 0 < s) (f : ℕ) :
    (∫ w in Ioi (1 : ℝ), mellinPieceTotient e s f w)
      = moebiusTotientCoeff e f * ((f : ℝ) ^ (-s) / s) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp [mellinPieceTotient_zero, moebiusTotientCoeff_zero]
  · exact integral_indicator_Ici_rpow hs hf _

/-- The integral of the norm of a piece. -/
theorem integral_norm_mellinPieceTotient (e : ℕ) {s : ℝ} (hs : 0 < s) (f : ℕ) :
    (∫ w in Ioi (1 : ℝ), ‖mellinPieceTotient e s f w‖)
      = |moebiusTotientCoeff e f| * ((f : ℝ) ^ (-s) / s) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp [mellinPieceTotient_zero, moebiusTotientCoeff_zero]
  refine (setIntegral_congr_fun measurableSet_Ioi fun w (hw : 1 < w) ↦ ?_).trans
    (integral_indicator_Ici_rpow hs hf _)
  simp only [mellinPieceTotient, indicator_apply]
  split_ifs <;> simp [abs_of_pos (Real.rpow_pos_of_pos (one_pos.trans hw) _)]

/-- The pieces sum pointwise to the integrand:
`T_e(w) w^{-s-1} = ∑_f 1_{[f,∞)}(w) (μ(f)/φ(f)) w^{-s-1}`. Both sides are finite sums at each `w`,
so no hypothesis on `w` is needed. -/
theorem tsum_mellinPieceTotient (e : ℕ) (s : ℝ) (w : ℝ) :
    ∑' f : ℕ, mellinPieceTotient e s f w = moebiusTotientBelow e w * w ^ (-s - 1) := by
  have h0 : (0 : ℕ) ∉ coprimeBelow e w := fun h => (mem_coprimeBelow.mp h).1 rfl
  have hz : ∀ f ∉ insert 0 (coprimeBelow e w), mellinPieceTotient e s f w = 0 := by
    intro f hf
    simp only [Finset.mem_insert, mem_coprimeBelow, not_or] at hf
    simp only [mellinPieceTotient, indicator_apply, mem_Ici, moebiusTotientCoeff]
    split_ifs <;> simp_all
  rw [tsum_eq_sum hz, Finset.sum_insert h0, mellinPieceTotient_zero, Pi.zero_apply, zero_add,
    moebiusTotientBelow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun f hf => ?_
  obtain ⟨-, hle, hcop⟩ := mem_coprimeBelow.mp hf
  simp [mellinPieceTotient, moebiusTotientCoeff, hle, hcop]

/-- The norms' integrals are summable: the bound is `(|μ(f)|/(φ(f) f^s))/s`, summable by
`Gap212.Sieve.summable_abs_moebius_div_totient_mul_rpow`. -/
theorem summable_integral_norm_mellinPieceTotient (e : ℕ) {s : ℝ} (hs : 0 < s) :
    Summable fun f : ℕ => ∫ w in Ioi (1 : ℝ), ‖mellinPieceTotient e s f w‖ := by
  refine ((summable_abs_moebius_div_totient_mul_rpow hs).div_const s).of_nonneg_of_le
    (fun f => integral_nonneg fun _ => norm_nonneg _) fun f => ?_
  rw [integral_norm_mellinPieceTotient e hs]
  refine (mul_le_mul_of_nonneg_right (abs_moebiusTotientCoeff_le e f) (by positivity)).trans_eq ?_
  rw [Real.rpow_neg (Nat.cast_nonneg f)]
  ring

/-- **The Mellin transform of the truncated totient-weight Möbius sum.** For `s > 0`,

  `∫_1^∞ T_e(w) w^{-s-1} dw = h_e(s)/s`,

with `T_e(w) = ∑_{f ≤ w, (f,e)=1} μ(f)/φ(f)` and `h_e(s) = ∑_{(f,e)=1} μ(f)/(φ(f) f^s)`. Putting
`w = exp u` this is the Abel integral `∫_0^∞ T_e(exp u) e^{-su} du`. -/
theorem integral_moebiusTotientBelow_rpow (e : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫ w in Ioi (1 : ℝ), moebiusTotientBelow e w * w ^ (-s - 1))
      = moebiusTotientSeries e s / s := by
  have hterm : ∀ f : ℕ, (∫ w in Ioi (1 : ℝ), mellinPieceTotient e s f w)
      = moebiusTotientCoprimeTerm e s f / s := fun f ↦ by
    rw [integral_mellinPieceTotient e hs f, ← moebiusTotientCoeff_mul_rpow e s f, mul_div_assoc]
  rw [← setIntegral_congr_fun measurableSet_Ioi fun w _ ↦ tsum_mellinPieceTotient e s w,
    ← integral_tsum_of_summable_integral_norm (integrableOn_mellinPieceTotient e hs)
      (summable_integral_norm_mellinPieceTotient e hs)]
  simp only [hterm, tsum_div_const, moebiusTotientSeries]

/-- **The Abel constant.** For `e ≥ 1` even the Mellin transform above tends to
`c_e = (e/φ(e)) ∏_{p ∤ e}(1 - 1/(p-1)^2)` as `s → 0⁺`.

This is `lim_{s→0⁺} h_e(s)/s = c_e`, an Abel limit. The convergence of the undamped integral
`∫_0^∞ T_e(exp u) du` to `c_e` is `Gap212.Sieve.integral_moebiusTotientBelow_exp`, which uses the
integrable majorant `Gap212.Sieve.MoebiusTotientPartialSumDecay`. -/
theorem tendsto_integral_moebiusTotientBelow_rpow {e : ℕ} (he : 1 ≤ e) (he2 : 2 ∣ e) :
    Tendsto (fun s : ℝ => ∫ w in Ioi (1 : ℝ), moebiusTotientBelow e w * w ^ (-s - 1))
      (nhdsWithin 0 (Ioi 0)) (nhds (((e : ℝ) / (e.totient : ℝ)) *
        ∏' p : ℕ, if p.Prime ∧ ¬ p ∣ e then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)) := by
  refine (tendsto_moebiusTotientSeries_div he he2).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (integral_moebiusTotientBelow_rpow e (hs : (0 : ℝ) < s)).symm

end Gap212.Sieve
