/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.InnerSumReciprocal
public import Gap212.Sieve.MoebiusTotientDecay

/-!
# The truncated inner sum at the totient weight

For `F` of class `C¹` with compact support, `e ≥ 2` *even*, `β > 0` fixed and `B = B(x) ≥ x^β`,

  `log x · Y_F(e) → -F'(0) · c_e`,   `Y_F(e) = ∑_{f ≤ B/e, (f,e)=1} μ(f)/φ(f) · F(log_x(ef))`,

with `c_e = (e/φ(e)) ∏_{p ∤ e}(1 - 1/(p-1)^2)`.

The weight here is `μ(f)/φ(f)`, not the reciprocal weight `μ(f)/f`. The generating function here is
`∏_{p ∤ e}(1 - 1/((p-1)p^s))`, whose factor at `p = 2` vanishes to first order as `s → 0⁺`, so the
zero at `s = 0` is simple only when `2 ∣ e`. Hence the evenness hypothesis, and hence the
correction `∏(1 - 1/(p-1)^2)` in the constant, neither of which has a counterpart at the reciprocal
weight.

## The argument

Substituting `u = v log x` in `Gap212.Sieve.truncated_moebius_totient_partial_summation`
(`Gap212.Sieve.logx_mul_truncated_moebius_totient`),

  `log x · Y_F(e) = -∫_0^∞ F'(log_x e + u/log x) T_e(min(e^u, B/e)) du`,

the substitution being a *scaling* of the integration variable, whose Jacobian is the `log x` on
the left.

The integral is split at `u = log(B/e)`, as at the reciprocal weight: the argument of `T_e` is a
minimum, and where the truncation bites the available bound is the decay at `log(B/e)`, which is
larger than the decay at `u`; since `F'` supported in `[0, T]` confines `u` to `[0, T log x]`, and
for `T > β` the ratio of the two bounds is unbounded, no single majorant in `u` covers the
truncated range.

Below the cut the truncation is inactive and `Gap212.Sieve.MoebiusTotientPartialSumDecay` gives the
majorant `‖F'‖_∞ C_e (1 + u)^{-1-ε}`, integrable on `[0, ∞)`; dominated convergence applies, and
pointwise the first factor tends to `F'(0)` because `log_x e → 0` and `u/log x → 0`. Above the cut
the two partial sums differ by at most `2 C_e (1 + log(B/e))^{-1-ε}` on a range of length at most
`T log x`, so that term is `O(log x · (1 + (β/2) log x)^{-1-ε}) = O((log x)^{-ε}) → 0`
(`Gap212.Sieve.tendsto_integral_truncation_error_totient`). This is where `B ≥ x^β` is used, and it
is used quantitatively rather than only through `B/e → ∞`.

Those two steps are the only ones that use the decay, and each needs no more than summability in
`u = log w`: integrability of the majorant over a `u`-range of length `Θ(log x)`, and
`(log w) · D(w) → 0` for the bound `D`. That is why the hypothesis is a fixed log-power saving and
not the error-term rate; `Gap212.Sieve.MoebiusPartialSumDecay` records why `O(1/log w)` and
`o(1/log w)` are nonetheless both too weak.

The limit is then `-F'(0) ∫_0^∞ T_e(e^u) du`, and that integral is `c_e` by
`Gap212.Sieve.integral_moebiusTotientBelow_exp`.

## Uniformity in `e`

The limit is for fixed `e`. In the Gram sum `e` grows with `x`, `log_x e` running over a fixed
compact interval, and the inner sum is compared with `F'(log_x e)` rather than `F'(0)`; that
averaged statement is `Gap212.Sieve.TotientGramSumLimitOfSupport`.

## Main definitions

* `Gap212.Sieve.innerSumTotientConst`: the constant `c_e`.

## Main results

* `Gap212.Sieve.truncated_moebius_totient_partial_summation`: partial summation at the weight
  `μ(f)/φ(f)`, with no constraint on `B`.
* `Gap212.Sieve.logx_mul_truncated_moebius_totient`: the identity after `u = v log x`.
* `Gap212.Sieve.tendsto_integral_deriv_mul_moebiusTotientBelow_exp`: the untruncated integral's
  limit, `F'(0) c_e`.
* `Gap212.Sieve.tendsto_integral_truncation_error_totient`: the truncation term tends to `0`.
* `Gap212.Sieve.tendsto_logx_mul_innerSumTotient`: the limit `log x · Y_F(e) → -F'(0) c_e`. -/

@[expose] public section

open ArithmeticFunction Filter MeasureTheory Real Set Topology
open scoped ArithmeticFunction.Moebius

namespace Gap212.Sieve

/-! ### The constant -/

/-- **The constant `c_e = (e/φ(e)) ∏_{p ∤ e}(1 - 1/(p-1)^2)`.** It is `e^γ` times the
Möbius–totient limit at `V = e`: the infinite product is literally the one
`Gap212.Sieve.tendsto_log_mul_prod_one_sub_inv_sub_one` converges to, with the Mertens `e^{-γ}`
divided out — that factor being the only difference between the product over the *primes* below `y`
and the Abel integral of the truncated sum over the *integers*. Numerically `c_2 = 1.320324`,
`c_6 = 2.640647`, `c_30 = 3.520863`. It depends on `e` only through which primes divide `e`, so no
squarefreeness is needed. -/
noncomputable def innerSumTotientConst (e : ℕ) : ℝ :=
  (e : ℝ) / (e.totient : ℝ) *
    ∏' p : ℕ, if p.Prime ∧ ¬ p ∣ e then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

/-- `c_e > 0` for even `e ≥ 1`. For *odd* `e` the factor at `p = 2` is
`1 - 1/(2-1)^2 = 0`, so `c_e = 0` — and the true limit there is `0` as well, but of order
`(log x)^{-2}`, which is a different statement. -/
theorem innerSumTotientConst_pos {e : ℕ} (he : 1 ≤ e) (he2 : 2 ∣ e) :
    0 < innerSumTotientConst e := by
  have hφ : (0 : ℝ) < (e.totient : ℝ) := by exact_mod_cast Nat.totient_pos.2 he
  exact mul_pos (div_pos (by exact_mod_cast he) hφ) (tprod_corr_pos he2)

/-! ### Partial summation at the totient weight -/

/-- **Partial summation for the totient weight.** For `F` of class `C¹` with compact support,
`x > 1` and `e ≥ 1`,

  `∑_{f ≤ B/e, (f,e)=1} μ(f) F(log_x(ef))/φ(f) = -∫_0^∞ F'(log_x e + v) T_e(min(x^v, B/e)) dv`,

with `T_e(w) = ∑_{f ≤ w, (f,e)=1} μ(f)/φ(f)`. This is
`Gap212.Sieve.truncated_partial_summation_weighted` at `g f = μ(f)/φ(f)`, and unlike
`Gap212.Sieve.truncated_moebius_partial_summation` it carries no hypothesis on `B` — the identity
never uses one. -/
theorem truncated_moebius_totient_partial_summation {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {x : ℝ} (hx : 1 < x) {e : ℕ} (he : 1 ≤ e) {B : ℝ} :
    ∑ f ∈ coprimeBelow e (B / e), (μ f : ℝ) * F (Notation.logx x (e * f)) / (f.totient : ℝ)
      = -∫ v in Ioi (0 : ℝ),
          deriv F (Notation.logx x e + v) * moebiusTotientBelow e (min (x ^ v) (B / e)) := by
  simp only [moebiusTotientBelow]
  rw [← truncated_partial_summation_weighted hF hFc hx he (B := B) fun f => μ f / f.totient]
  exact Finset.sum_congr rfl fun f _ => by ring

/-- **The partial-summation identity in the `u` variable.** For `x > 1` and `e ≥ 1`,

  `log x · ∑_{f ≤ B/e, (f,e)=1} μ(f) F(log_x(ef))/φ(f)
     = -∫_0^∞ F'(log_x e + u/log x) T_e(min(e^u, B/e)) du`.

This is `Gap212.Sieve.truncated_moebius_totient_partial_summation` after the scaling `u = v log x`,
whose Jacobian is exactly the `log x` on the left; and `x^(u/log x) = e^u`. -/
theorem logx_mul_truncated_moebius_totient {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {x : ℝ} (hx : 1 < x) {e : ℕ} (he : 1 ≤ e) (B : ℝ) :
    Real.log x * ∑ f ∈ coprimeBelow e (B / e),
        (μ f : ℝ) * F (Notation.logx x (e * f)) / (f.totient : ℝ)
      = -∫ u in Ioi (0 : ℝ), deriv F (Notation.logx x e + u / Real.log x)
          * moebiusTotientBelow e (min (exp u) (B / e)) := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have h := integral_comp_mul_left_Ioi (fun v => deriv F (Notation.logx x e + v)
    * moebiusTotientBelow e (min (x ^ v) (B / e))) 0 (inv_pos.2 hL)
  simp only [mul_zero, inv_inv, smul_eq_mul] at h
  rw [truncated_moebius_totient_partial_summation hF hFc hx he (B := B), mul_neg, ← h]
  refine congrArg _ (setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_)
  simp only [inv_mul_eq_div, Real.rpow_def_of_pos (zero_lt_one.trans hx),
    mul_div_cancel₀ _ hL.ne']

/-! ### Integrability of the two integrands -/

/-- The integrands below are measurable. -/
private theorem measurable_deriv_mul_moebiusTotientBelow {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (e : ℕ) (a L : ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable fun u : ℝ => deriv F (a + u / L) * moebiusTotientBelow e (g u) :=
  ((hF.continuous_deriv le_rfl).measurable.comp (measurable_const.add
    (measurable_id.div_const L))).mul ((measurable_moebiusTotientBelow e).comp hg)

/-- The untruncated integrand is integrable on `(0, ∞)`: it is dominated by
`‖F'‖_∞ C (1 + u)^{-1-ε}`. -/
theorem integrableOn_deriv_mul_moebiusTotientBelow_exp {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    {e : ℕ} {ε C M : ℝ} (hε : 0 < ε)
    (hbd : ∀ w : ℝ, 1 ≤ w → |moebiusTotientBelow e w| ≤ C / (1 + Real.log w) ^ (1 + ε))
    (hM : ∀ t : ℝ, ‖deriv F t‖ ≤ M) (a L : ℝ) :
    IntegrableOn (fun u : ℝ => deriv F (a + u / L) * moebiusTotientBelow e (exp u))
      (Ioi (0 : ℝ)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine Integrable.mono' (g := fun u : ℝ => M * (C / (1 + u) ^ (1 + ε)))
    ((integrableOn_const_div_one_add_rpow hε C).const_mul M) ?_ ?_
  · exact (measurable_deriv_mul_moebiusTotientBelow hF e a L
      Real.measurable_exp).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul]
    exact mul_le_mul (hM _) (abs_moebiusTotientBelow_exp_le hbd hu.le) (abs_nonneg _) hM0

/-- The truncated integrand is integrable on `(0, ∞)`: it is bounded by `‖F'‖_∞ C` and vanishes
beyond `T log x`, so `‖F'‖_∞ C exp(T log x - u)` dominates it. -/
theorem integrableOn_deriv_mul_moebiusTotientBelow_min {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    {e : ℕ} {ε C M T L a Be : ℝ} (hε : 0 < ε) (hC : 0 < C) (hL : 0 < L) (ha : 0 ≤ a)
    (hBe : 1 ≤ Be)
    (hbd : ∀ w : ℝ, 1 ≤ w → |moebiusTotientBelow e w| ≤ C / (1 + Real.log w) ^ (1 + ε))
    (hM : ∀ t : ℝ, ‖deriv F t‖ ≤ M)
    (hTsupp : ∀ t : ℝ, T < |t| → deriv F t = 0) :
    IntegrableOn (fun u : ℝ => deriv F (a + u / L) * moebiusTotientBelow e (min (exp u) Be))
      (Ioi (0 : ℝ)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine Integrable.mono' (g := fun u : ℝ => M * C * exp (T * L) * exp (-1 * u))
    ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul _) ?_ ?_
  · exact (measurable_deriv_mul_moebiusTotientBelow hF e a L
      (Real.measurable_exp.min measurable_const)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
    rcases lt_or_ge (T * L) u with hbig | hsmall
    · rw [hTsupp _ (((lt_div_iff₀ hL).2 hbig).trans_le
        ((le_add_of_nonneg_left ha).trans (le_abs_self _))), zero_mul, norm_zero]
      positivity
    · have hmin1 : (1 : ℝ) ≤ min (exp u) Be := le_min (Real.one_le_exp hu.le) hBe
      have hSbd : |moebiusTotientBelow e (min (exp u) Be)| ≤ C := (hbd _ hmin1).trans <|
        div_le_self hC.le (Real.one_le_rpow (by linarith [Real.log_nonneg hmin1]) (by linarith))
      have hexp : (1 : ℝ) ≤ exp (T * L) * exp (-1 * u) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith)
      rw [norm_mul, mul_assoc (M * C)]
      exact (mul_le_mul (hM _) hSbd (abs_nonneg _) hM0).trans
        (le_mul_of_one_le_right (mul_nonneg hM0 hC.le) hexp)

/-! ### The untruncated limit -/

/-- **The untruncated integral's limit.** `∫_0^∞ F'(log_x e + u/log x) T_e(e^u) du → F'(0) c_e`.

Dominated convergence: the majorant is `‖F'‖_∞ C_e (1 + u)^{-1-ε}`, integrable by
`Gap212.Sieve.integrableOn_const_div_one_add_rpow`; pointwise `log_x e → 0` and `u/log x → 0`, so
the first factor tends to `F'(0)`; and `∫_0^∞ T_e(e^u) du = c_e`. -/
theorem tendsto_integral_deriv_mul_moebiusTotientBelow_exp
    (hdecay : MoebiusTotientPartialSumDecay) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {e : ℕ} (he : 1 ≤ e) (he2 : 2 ∣ e) :
    Tendsto (fun x : ℝ => ∫ u in Ioi (0 : ℝ),
        deriv F (Notation.logx x e + u / Real.log x) * moebiusTotientBelow e (exp u))
      atTop (nhds (deriv F 0 * innerSumTotientConst e)) := by
  obtain ⟨ε, hε, C, hC, hbd⟩ := exists_moebiusTotientBelow_decay hdecay he
  obtain ⟨M, hM⟩ := hFc.deriv.exists_bound_of_continuous (hF.continuous_deriv le_rfl)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [innerSumTotientConst, ← integral_moebiusTotientBelow_exp hdecay he he2,
    ← integral_const_mul]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => M * (C / (1 + u) ^ (1 + ε))) (Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_)
    ((integrableOn_const_div_one_add_rpow hε C).const_mul M) ?_
  · exact (measurable_deriv_mul_moebiusTotientBelow hF e _ _
      Real.measurable_exp).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul]
    exact mul_le_mul (hM _) (abs_moebiusTotientBelow_exp_le hbd hu.le) (abs_nonneg _) hM0
  · filter_upwards with u
    have h0 : Tendsto (fun x : ℝ => Notation.logx x e + u / Real.log x) atTop (nhds 0) := by
      simpa [Notation.logx] using (tendsto_log_atTop.const_div_atTop (Real.log e)).add
        (tendsto_log_atTop.const_div_atTop u)
    exact (((hF.continuous_deriv le_rfl).tendsto 0).comp h0).mul_const _

/-! ### The truncation error -/

/-- Truncating `T_e(exp u)` at `Y ≥ 1` changes it by at most `2 C (1 + log Y)^{-1-ε}`. -/
theorem abs_moebiusTotientBelow_min_exp_sub_le {e : ℕ} {ε C : ℝ} (hε : 0 < ε) (hC : 0 < C)
    (hbd : ∀ w : ℝ, 1 ≤ w → |moebiusTotientBelow e w| ≤ C / (1 + Real.log w) ^ (1 + ε))
    {Y u : ℝ} (hY : 1 ≤ Y) (hu : 0 ≤ u) :
    |moebiusTotientBelow e (min (exp u) Y) - moebiusTotientBelow e (exp u)|
      ≤ 2 * C * (1 / (1 + Real.log Y) ^ (1 + ε)) := by
  rcases le_or_gt (exp u) Y with hle | hgt
  · rw [min_eq_left hle, sub_self, abs_zero]
    have := one_add_rpow_pos (ε := ε) (Real.log_nonneg hY)
    positivity
  have hlt : Real.log Y ≤ u := by simpa using Real.log_le_log (by linarith) hgt.le
  have h3 : C / (1 + u) ^ (1 + ε) ≤ C / (1 + Real.log Y) ^ (1 + ε) :=
    div_le_div_of_nonneg_left hC.le (one_add_rpow_pos (Real.log_nonneg hY))
      (Real.rpow_le_rpow (by linarith [Real.log_nonneg hY]) (by linarith) (by linarith))
  rw [min_eq_right hgt.le]
  calc _ ≤ |moebiusTotientBelow e Y| + |moebiusTotientBelow e (exp u)| := abs_sub _ _
    _ ≤ C / (1 + Real.log Y) ^ (1 + ε) + C / (1 + Real.log Y) ^ (1 + ε) :=
      add_le_add (hbd _ hY) ((abs_moebiusTotientBelow_exp_le hbd hu).trans h3)
    _ = 2 * C * (1 / (1 + Real.log Y) ^ (1 + ε)) := by ring

/-- **The truncation term tends to `0`.** Its integrand vanishes unless
`log(B/e) < u ≤ T log x`, where the two partial sums differ by at most
`2 C_e (1 + log(B/e))^{-1-ε}`; so the term is
`O(log x · (1 + (β/2) log x)^{-1-ε}) = O((log x)^{-ε})`, which tends to `0`.

This is the second and last place the decay is spent, and the one that forces the exponent's excess
over `1` to be strictly positive: at an exponent of exactly `1` the product above is the nonzero
constant `2 M C T/β`. `B ≥ x^β` is used quantitatively here, not merely through `B/e → ∞`; see the
module docstring for why no single majorant in `u` can absorb this term instead. -/
theorem tendsto_integral_truncation_error_totient (hdecay : MoebiusTotientPartialSumDecay)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {e : ℕ} (he : 1 ≤ e)
    {β : ℝ} (hβ : 0 < β) {B : ℝ → ℝ} (hB : ∀ᶠ x in atTop, x ^ β ≤ B x) :
    Tendsto (fun x : ℝ => ∫ u in Ioi (0 : ℝ),
        (deriv F (Notation.logx x e + u / Real.log x)
            * moebiusTotientBelow e (min (exp u) (B x / e))
          - deriv F (Notation.logx x e + u / Real.log x) * moebiusTotientBelow e (exp u)))
      atTop (nhds 0) := by
  obtain ⟨ε, hε, C, hC, hbd⟩ := exists_moebiusTotientBelow_decay hdecay he
  obtain ⟨M, hM⟩ := hFc.deriv.exists_bound_of_continuous (hF.continuous_deriv le_rfl)
  obtain ⟨T, hT0, hTsupp⟩ := exists_deriv_support_bound hFc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hloge : 0 ≤ Real.log (e : ℝ) := Real.log_nonneg (by exact_mod_cast he)
  have hβ2 : (0 : ℝ) < β / 2 := by linarith
  refine squeeze_zero_norm' ?_
    (by simpa only [mul_zero, Function.comp_def] using
      (((tendsto_mul_one_div_one_add_rpow hβ2 hε).comp Real.tendsto_log_atTop).const_mul
        (M * (2 * C) * T)))
  filter_upwards [eventually_gt_atTop (1 : ℝ), hB,
    (tendsto_rpow_atTop hβ).eventually_ge_atTop (e : ℝ),
    (Real.tendsto_log_atTop.const_mul_atTop hβ2).eventually_ge_atTop (Real.log e)]
    with x hx hBx hex hlogx
  have hL : 0 < Real.log x := Real.log_pos hx
  have hBe : (1 : ℝ) ≤ B x / e := (one_le_div heR).mpr (hex.trans hBx)
  -- the decay of the truncation, quantitatively
  have hlogBe : β / 2 * Real.log x ≤ Real.log (B x / e) := by
    have h := Real.log_le_log (heR.trans_le hex) hBx
    rw [Real.log_rpow (zero_lt_one.trans hx)] at h
    rw [Real.log_div (heR.trans_le (hex.trans hBx)).ne' heR.ne']
    linarith
  have hDpos : (0 : ℝ) < (1 + Real.log (B x / e)) ^ (1 + ε) :=
    one_add_rpow_pos (Real.log_nonneg hBe)
  set K : ℝ := M * (2 * C * (1 / (1 + Real.log (B x / e)) ^ (1 + ε)))
  set f : ℝ → ℝ := fun u => deriv F (Notation.logx x e + u / Real.log x)
      * moebiusTotientBelow e (min (exp u) (B x / e))
    - deriv F (Notation.logx x e + u / Real.log x) * moebiusTotientBelow e (exp u)
  -- the pointwise bound by an indicator of `Ioc 0 (T log x)`
  have hfbd : ∀ u ∈ Ioi (0 : ℝ),
      ‖f u‖ ≤ (Ioc (0 : ℝ) (T * Real.log x)).indicator (fun _ => K) u := by
    intro u (hu : 0 < u)
    rcases lt_or_ge (T * Real.log x) u with hbig | hsmall
    · have hgt : T < |Notation.logx x e + u / Real.log x| := ((lt_div_iff₀ hL).2 hbig).trans_le
        ((le_add_of_nonneg_left (div_nonneg hloge hL.le)).trans (le_abs_self _))
      simpa [f, hTsupp _ hgt] using Set.indicator_nonneg (fun _ _ => by positivity) u
    rw [Set.indicator_of_mem (Set.mem_Ioc.2 ⟨hu, hsmall⟩)]
    simp only [f, ← mul_sub, norm_mul]
    exact mul_le_mul (hM _) (abs_moebiusTotientBelow_min_exp_sub_le hε hC hbd hBe hu.le)
      (abs_nonneg _) hM0
  -- integrate the bound
  have hindint : Integrable ((Ioc (0 : ℝ) (T * Real.log x)).indicator fun _ => K)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.integrableOn ?_
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (by simp [Real.volume_Ioc])
  calc ‖∫ u in Ioi (0 : ℝ), f u‖ ≤ ∫ u in Ioi (0 : ℝ), ‖f u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi (0 : ℝ), (Ioc (0 : ℝ) (T * Real.log x)).indicator (fun _ => K) u := by
        refine integral_mono_ae ((integrableOn_deriv_mul_moebiusTotientBelow_min hF hε hC hL
          (div_nonneg hloge hL.le) hBe hbd hM hTsupp).sub
          (integrableOn_deriv_mul_moebiusTotientBelow_exp hF hε hbd hM _ _)).norm hindint ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu using hfbd u hu
    _ = M * (2 * C) * T * (Real.log x * (1 / (1 + Real.log (B x / e)) ^ (1 + ε))) := by
        rw [setIntegral_indicator measurableSet_Ioc,
          Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self, setIntegral_const,
          Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (by positivity),
          smul_eq_mul]
        ring
    _ ≤ M * (2 * C) * T * (Real.log x * (1 / (1 + β / 2 * Real.log x) ^ (1 + ε))) := by
        gcongr

/-! ### The limit -/

/-- **The truncated inner sum, totient weight.** For `F` of class `C¹` with compact support,
`e ≥ 2` **even**, `β > 0` and `B = B(x) ≥ x^β`,

  `log x · ∑_{f ≤ B/e, (f,e)=1} μ(f) F(log_x(ef))/φ(f) ⟶ -F'(0) · c_e`   (`x → ∞`),

with `c_e = (e/φ(e)) ∏_{p ∤ e}(1 - 1/(p-1)^2)`.

The hypothesis `Gap212.Sieve.MoebiusTotientPartialSumDecay` is a saving of a fixed power of the
logarithm in the prime number theorem for the `φ`-weighted partial sum, proved as
`Gap212.Sieve.moebiusTotientPartialSumDecay`.

Evenness is needed: for odd `e` the Euler factor at `p = 2` is `1 - 1/(2^{s+1} - 1) ~ 2s log 2`,
the zero of the generating function is double, and the limit is `0`, with
`(log x)^2 Y_F(e) → F''(0) log 2 · c_{2e}` instead. -/
@[gap212 "lem_inner_sum_asymptotic"]
theorem tendsto_logx_mul_innerSumTotient (hdecay : MoebiusTotientPartialSumDecay)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {e : ℕ} (he : 2 ≤ e)
    (he2 : 2 ∣ e) {β : ℝ} (hβ : 0 < β) {B : ℝ → ℝ} (hB : ∀ᶠ x in atTop, x ^ β ≤ B x) :
    Tendsto (fun x : ℝ => Real.log x *
        ∑ f ∈ coprimeBelow e (B x / e), (μ f : ℝ) * F (Notation.logx x (e * f)) / (f.totient : ℝ))
      atTop (nhds (-deriv F 0 * innerSumTotientConst e)) := by
  have he1 : 1 ≤ e := by lia
  obtain ⟨ε, hε, C, hC, hbd⟩ := exists_moebiusTotientBelow_decay hdecay he1
  obtain ⟨M, hM⟩ := hFc.deriv.exists_bound_of_continuous (hF.continuous_deriv le_rfl)
  obtain ⟨T, hT0, hTsupp⟩ := exists_deriv_support_bound hFc
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he1
  have hloge : 0 ≤ Real.log (e : ℝ) := Real.log_nonneg (by exact_mod_cast he1)
  have hGlim : Tendsto (fun x : ℝ => ∫ u in Ioi (0 : ℝ),
      deriv F (Notation.logx x e + u / Real.log x)
        * moebiusTotientBelow e (min (exp u) (B x / e))) atTop
      (nhds (deriv F 0 * innerSumTotientConst e)) := by
    have hsum := (tendsto_integral_deriv_mul_moebiusTotientBelow_exp hdecay hF hFc he1 he2).add
      (tendsto_integral_truncation_error_totient hdecay hF hFc he1 hβ hB)
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ), hB,
      (tendsto_rpow_atTop hβ).eventually_ge_atTop (e : ℝ)] with x hx hBx hex
    have hL : 0 < Real.log x := Real.log_pos hx
    rw [integral_sub (integrableOn_deriv_mul_moebiusTotientBelow_min (a := Notation.logx x e) hF hε
      hC hL (div_nonneg hloge hL.le) ((one_le_div heR).2 (hex.trans hBx)) hbd hM hTsupp)
      (integrableOn_deriv_mul_moebiusTotientBelow_exp hF hε hbd hM (Notation.logx x e) _)]
    ring
  rw [neg_mul]
  refine hGlim.neg.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (logx_mul_truncated_moebius_totient hF hFc hx he1 (B x)).symm

end Gap212.Sieve
