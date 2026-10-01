/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MoebiusPartialSumDecay

/-!
# The truncated inner sum at the reciprocal weight

For `F` of class `C¹` with compact support, `q ≥ 1`, `β > 0` fixed and `B = B(x) ≥ x^β`,

  `log x · Z_F(q) → -F'(0) · q/φ(q)`,   `Z_F(q) = ∑_{f ≤ B/q, (f,q)=1} μ(f)/f · F(log_x(qf))`.

This is the weight `Gap212.Sieve.selberg_progression_sum` needs, and it is *not* the weight of the
totient inner sum: that one carries `μ(f)/φ(f)`, this one `μ(f)/f`. The generating
function here is `∏_{p ∤ q}(1 - p^{-1-s})`, with a *simple* zero at `s = 0` for *every* `q`, so
there is no evenness hypothesis, no `∏(1 - 1/(p-1)²)` correction, and the constant is the bare
`q/φ(q)`; `q = 1` and `q = 3` behave as well as any other.

## The argument, and where the one hypothesis enters

Substituting `u = v log x` in `Gap212.Sieve.truncated_moebius_reciprocal_partial_summation`
(`Gap212.Sieve.logx_mul_truncated_moebius_reciprocal`),

  `log x · Z_F(q) = -∫_0^∞ F'(log_x q + u/log x) S_q(min(e^u, B/q)) du`.

The substitution is a *scaling* of the integration variable, so its Jacobian is the `log x` on the
left; no factor is created or destroyed.

Dominated convergence then needs an `L¹` majorant for `u ↦ S_q(e^u)`, and the elementary bounds do
not give one — that is the whole content of `Gap212.Sieve.MoebiusPartialSumDecay`, the log-power
saving in the prime number theorem, which enters here as a hypothesis and is proved as
`Gap212.Sieve.moebiusPartialSumDecay`. Granting it, the majorant is `‖F'‖_∞ C_q (1 + u)^{-1-ε}`,
and pointwise in `u` the first factor tends to `F'(0)` because `log_x q → 0` and `u/log x → 0`. The
limit is `-F'(0) ∫_0^∞ S_q(e^u) du`, and that integral is `q/φ(q)` by
`Gap212.Sieve.integral_moebiusReciprocalBelow_exp`.

The exponent of the decay has to exceed `1`: over the `u`-range `[0, T log x]` the constant bound
`|S_q| ≤ 1` integrates to `Θ(log x)` and `O(1/u)` to `log(T log x)`, both against a wanted
`o(1)`; `(1 + u)^{-1-ε}` is integrable for every `ε > 0`. See
`Gap212.Sieve.MoebiusPartialSumDecay` for the two places, and for why `O(1/log w)` and
`o(1/log w)` are not enough.

## The truncation term

The argument of `S_q` is `min(e^u, B/q)`, and where the truncation bites the available bound is the
decay at `log(B/q)`, larger than the decay at `u`; since `F'` supported in `[0, T]` confines `u` to
`[0, T log x]`, and with `T > β` the ratio of the two is unbounded, the integrand has no majorant
of the form of the decay at `u`.

So the truncation is split off as its own term
(`Gap212.Sieve.tendsto_integral_truncation_error`). It is supported in
`log(B/q) < u ≤ T log x`, a range of length at most `T log x` on which the difference of the two
partial sums is at most `2 C_q (1 + log(B/q))^{-1-ε}`, and
`log x · (1 + (β/2) log x)^{-1-ε} → 0` — which is where the *strict* inequality `ε > 0` is spent a
second time: at `ε = 0` that product is the nonzero constant `2/β`. That is also where `B ≥ x^β` is
spent, and it is spent quantitatively rather than only through `B/q → ∞`.

## Main results

* `Gap212.Sieve.logx_mul_truncated_moebius_reciprocal`: the identity after `u = v log x`.
* `Gap212.Sieve.tendsto_integral_deriv_mul_moebiusReciprocalBelow_exp`: the untruncated integral's
  limit, `F'(0) q/φ(q)`.
* `Gap212.Sieve.tendsto_integral_truncation_error`: the truncation term tends to `0`.
* `Gap212.Sieve.tendsto_logx_mul_innerSumReciprocal`: the asymptotic.
-/

@[expose] public section

open ArithmeticFunction Filter MeasureTheory Real Set Topology
open scoped ArithmeticFunction.Moebius

namespace Gap212.Sieve

/-! ### Preliminaries on the cutoff's derivative -/

/-- `F'` vanishes outside a symmetric interval, `F` having compact support. This is what confines
the `u`-range of the truncation error to `[0, T log x]`. -/
theorem exists_deriv_support_bound {F : ℝ → ℝ} (hFc : HasCompactSupport F) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T < |t| → deriv F t = 0 := by
  obtain ⟨r, hr⟩ := hFc.deriv.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max r 0, le_max_right _ _, fun t ht => ?_⟩
  by_contra hne
  have h2 := hr (subset_tsupport _ hne)
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h2
  exact absurd ht (not_lt.mpr (h2.trans (le_max_left _ _)))

/-- The integrands below are measurable: `F'` is continuous and the partial sum is measurable. -/
private theorem measurable_deriv_mul_moebiusReciprocalBelow {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (q : ℕ) (a L : ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable fun u : ℝ ↦ deriv F (a + u / L) * moebiusReciprocalBelow q (g u) :=
  ((hF.continuous_deriv le_rfl).measurable.comp
    (measurable_const.add (measurable_id.div_const L))).mul
      ((measurable_moebiusReciprocalBelow q).comp hg)

/-- A product with the bounded factor `F'` is bounded by `‖F'‖_∞` times the other factor's
bound. -/
private theorem norm_deriv_mul_le {F : ℝ → ℝ} {M c y : ℝ} (hM : ∀ t : ℝ, ‖deriv F t‖ ≤ M)
    (t : ℝ) (hy : |y| ≤ c) : ‖deriv F t * y‖ ≤ M * c := by
  rw [norm_mul, Real.norm_eq_abs y]
  exact mul_le_mul (hM t) hy (abs_nonneg _) ((norm_nonneg _).trans (hM 0))

/-! ### The identity after `u = v log x` -/

/-- **The partial-summation identity in the `u` variable.** For `x > 1` and `q ≥ 1`,

  `log x · ∑_{f ≤ B/q, (f,q)=1} μ(f) F(log_x(qf))/f
     = -∫_0^∞ F'(log_x q + u/log x) S_q(min(e^u, B/q)) du`,

with `S_q(w) = ∑_{f ≤ w, (f,q)=1} μ(f)/f`. This is
`Gap212.Sieve.truncated_moebius_reciprocal_partial_summation` after the scaling `u = v log x`,
whose Jacobian is exactly the `log x` on the left; and `x^(u/log x) = e^u`. -/
theorem logx_mul_truncated_moebius_reciprocal {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {x : ℝ} (hx : 1 < x) {q : ℕ} (hq : 1 ≤ q) (B : ℝ) :
    Real.log x * ∑ f ∈ coprimeBelow q (B / q), (μ f : ℝ) * F (Notation.logx x (q * f)) / (f : ℝ)
      = -∫ u in Ioi (0 : ℝ), deriv F (Notation.logx x q + u / Real.log x)
          * moebiusReciprocalBelow q (min (exp u) (B / q)) := by
  have hL : 0 < Real.log x := Real.log_pos hx
  set g : ℝ → ℝ := fun v ↦ deriv F (Notation.logx x q + v)
    * moebiusReciprocalBelow q (min (x ^ v) (B / q))
  have hcov := integral_comp_mul_left_Ioi g 0 (inv_pos.2 hL)
  rw [mul_zero, inv_inv, smul_eq_mul] at hcov
  rw [truncated_moebius_reciprocal_partial_summation hF hFc hx hq (B := B), mul_neg, ← hcov]
  refine congrArg Neg.neg (setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_)
  simp only [g, Real.rpow_def_of_pos (zero_lt_one.trans hx), inv_mul_eq_div,
    mul_div_cancel₀ _ hL.ne']

/-! ### Integrability of the two integrands -/

/-- The untruncated integrand is integrable on `(0, ∞)`: it is dominated by
`‖F'‖_∞ C (1 + u)^{-1-ε}`. -/
theorem integrableOn_deriv_mul_moebiusReciprocalBelow_exp {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    {q : ℕ} {ε C M : ℝ} (hε : 0 < ε)
    (hbd : ∀ w : ℝ, 1 ≤ w → |moebiusReciprocalBelow q w| ≤ C / (1 + Real.log w) ^ (1 + ε))
    (hM : ∀ t : ℝ, ‖deriv F t‖ ≤ M) (a L : ℝ) :
    IntegrableOn (fun u : ℝ => deriv F (a + u / L) * moebiusReciprocalBelow q (exp u))
      (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (g := fun u : ℝ ↦ M * (C / (1 + u) ^ (1 + ε)))
    ((integrableOn_const_div_one_add_rpow hε C).const_mul M)
    (measurable_deriv_mul_moebiusReciprocalBelow hF q a L measurable_exp).aestronglyMeasurable
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact norm_deriv_mul_le hM _ (abs_moebiusReciprocalBelow_exp_le hbd (le_of_lt hu))

/-- The truncated integrand is integrable on `(0, ∞)`: it is bounded by `‖F'‖_∞ C` and vanishes
beyond `T log x`, so `‖F'‖_∞ C exp(T log x - u)` dominates it. -/
theorem integrableOn_deriv_mul_moebiusReciprocalBelow_min {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    {q : ℕ} {ε C M T L a Bq : ℝ} (hε : 0 < ε) (hC : 0 < C) (hL : 0 < L) (ha : 0 ≤ a)
    (hBq : 1 ≤ Bq)
    (hbd : ∀ w : ℝ, 1 ≤ w → |moebiusReciprocalBelow q w| ≤ C / (1 + Real.log w) ^ (1 + ε))
    (hM : ∀ t : ℝ, ‖deriv F t‖ ≤ M)
    (hTsupp : ∀ t : ℝ, T < |t| → deriv F t = 0) :
    IntegrableOn (fun u : ℝ => deriv F (a + u / L) * moebiusReciprocalBelow q (min (exp u) Bq))
      (Ioi (0 : ℝ)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine Integrable.mono' (g := fun u : ℝ => M * C * exp (T * L) * exp (-1 * u))
    ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul _) ?_ ?_
  · exact (measurable_deriv_mul_moebiusReciprocalBelow hF q a L
      (measurable_exp.min measurable_const)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    rcases lt_or_ge (T * L) u with hbig | hsmall
    · have hgt : T < |a + u / L| := by
        rw [abs_of_nonneg (by positivity)]
        linarith [(lt_div_iff₀ hL).mpr hbig]
      rw [hTsupp _ hgt, zero_mul, norm_zero]
      positivity
    · have hmin1 : (1 : ℝ) ≤ min (exp u) Bq := le_min (Real.one_le_exp hu0.le) hBq
      refine (norm_deriv_mul_le hM _ ((hbd _ hmin1).trans (div_le_self hC.le
        (Real.one_le_rpow (by linarith [Real.log_nonneg hmin1]) (by linarith))))).trans ?_
      have hexp : (1 : ℝ) ≤ exp (T * L) * exp (-1 * u) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith)
      nlinarith [mul_nonneg hM0 hC.le]

/-! ### The untruncated limit -/

/-- **The untruncated integral's limit.** `∫_0^∞ F'(log_x q + u/log x) S_q(e^u) du → F'(0) q/φ(q)`.

Dominated convergence: the majorant is `‖F'‖_∞ C_q (1 + u)^{-1-ε}`, integrable by
`Gap212.Sieve.integrableOn_const_div_one_add_rpow`; pointwise `log_x q → 0` and `u/log x → 0`, so
the first factor tends to `F'(0)`; and `∫_0^∞ S_q(e^u) du = q/φ(q)`. -/
theorem tendsto_integral_deriv_mul_moebiusReciprocalBelow_exp (hdecay : MoebiusPartialSumDecay)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {q : ℕ} (hq : 1 ≤ q) :
    Tendsto (fun x : ℝ => ∫ u in Ioi (0 : ℝ),
        deriv F (Notation.logx x q + u / Real.log x) * moebiusReciprocalBelow q (exp u))
      atTop (nhds (deriv F 0 * ((q : ℝ) / (q.totient : ℝ)))) := by
  obtain ⟨ε, hε, C, hC, hbd⟩ := exists_moebiusReciprocalBelow_decay hdecay hq
  obtain ⟨M, hM⟩ := hFc.deriv.exists_bound_of_continuous (hF.continuous_deriv le_rfl)
  rw [← integral_moebiusReciprocalBelow_exp hdecay hq, ← integral_const_mul]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ ↦ M * (C / (1 + u) ^ (1 + ε))) (Eventually.of_forall fun x ↦ ?_)
    (Eventually.of_forall fun x ↦ ?_)
    ((integrableOn_const_div_one_add_rpow hε C).const_mul M) ?_
  · exact (measurable_deriv_mul_moebiusReciprocalBelow hF q _ _
      measurable_exp).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_deriv_mul_le hM _ (abs_moebiusReciprocalBelow_exp_le hbd (le_of_lt hu))
  · filter_upwards with u
    have h0 : Tendsto (fun x : ℝ ↦ Notation.logx x q + u / Real.log x) atTop (nhds 0) := by
      simpa [Notation.logx] using (tendsto_log_atTop.const_div_atTop (Real.log q)).add
        (tendsto_log_atTop.const_div_atTop u)
    exact (((hF.continuous_deriv le_rfl).continuousAt (x := (0 : ℝ))).tendsto.comp h0).mul_const _

/-! ### The truncation error -/

/-- Truncating `S_q(e^u)` at `Bq ≥ 1` changes it by at most `2 C (1 + log Bq)^{-1-ε}`, given the
decay `|S_q(w)| ≤ C (1 + log w)^{-1-ε}` on `w ≥ 1`. -/
theorem abs_moebiusReciprocalBelow_min_exp_sub_le {q : ℕ} {ε C Bq u : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hbd : ∀ w : ℝ, 1 ≤ w → |moebiusReciprocalBelow q w| ≤ C / (1 + Real.log w) ^ (1 + ε))
    (hBq : 1 ≤ Bq) (hu : 0 ≤ u) :
    |moebiusReciprocalBelow q (min (exp u) Bq) - moebiusReciprocalBelow q (exp u)|
      ≤ 2 * C * (1 / (1 + Real.log Bq) ^ (1 + ε)) := by
  have hlogBq : 0 ≤ Real.log Bq := Real.log_nonneg hBq
  have hDpos : (0 : ℝ) < (1 + Real.log Bq) ^ (1 + ε) := one_add_rpow_pos hlogBq
  rcases le_or_gt (exp u) Bq with hle | hgt
  · rw [min_eq_left hle, sub_self, abs_zero]
    exact mul_nonneg (by linarith) (one_div_pos.mpr hDpos).le
  · rw [min_eq_right hgt.le]
    have hlt : Real.log Bq ≤ u := (Real.log_le_iff_le_exp (by linarith)).2 hgt.le
    have h₃ : C / (1 + u) ^ (1 + ε) ≤ C / (1 + Real.log Bq) ^ (1 + ε) :=
      div_le_div_of_nonneg_left hC hDpos
        (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith))
    rw [mul_one_div, mul_div_assoc, two_mul]
    linarith [abs_sub (moebiusReciprocalBelow q Bq) (moebiusReciprocalBelow q (exp u)),
      hbd _ hBq, abs_moebiusReciprocalBelow_exp_le hbd hu]

/-- The truncation integrand at `u > 0` is bounded by `M · 2C (1 + log Bq)^{-1-ε}` on
`(0, T L]` and vanishes beyond, where `|F'| ≤ M` and `F'` is supported in `[-T, T]`. -/
theorem norm_deriv_mul_moebiusReciprocalBelow_min_sub_le {F : ℝ → ℝ} {q : ℕ}
    {ε C M T a L Bq u : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hbd : ∀ w : ℝ, 1 ≤ w → |moebiusReciprocalBelow q w| ≤ C / (1 + Real.log w) ^ (1 + ε))
    (hBq : 1 ≤ Bq) (hM : ∀ t : ℝ, ‖deriv F t‖ ≤ M) (hT : ∀ t : ℝ, T < |t| → deriv F t = 0)
    (ha : 0 ≤ a) (hL : 0 < L) (hu : 0 < u) :
    ‖deriv F (a + u / L) * moebiusReciprocalBelow q (min (exp u) Bq)
        - deriv F (a + u / L) * moebiusReciprocalBelow q (exp u)‖
      ≤ (Ioc (0 : ℝ) (T * L)).indicator
          (fun _ => M * (2 * C * (1 / (1 + Real.log Bq) ^ (1 + ε)))) u := by
  have hdiff := abs_moebiusReciprocalBelow_min_exp_sub_le hε hC hbd hBq hu.le
  rcases lt_or_ge (T * L) u with hbig | hsmall
  · have hgt : T < |a + u / L| := by
      rw [abs_of_nonneg (by positivity)]
      linarith [(lt_div_iff₀ hL).mpr hbig]
    simpa [hT _ hgt] using Set.indicator_nonneg
      (fun _ _ ↦ mul_nonneg ((norm_nonneg _).trans (hM 0)) ((abs_nonneg _).trans hdiff)) u
  · rw [Set.indicator_of_mem (Set.mem_Ioc.2 ⟨hu, hsmall⟩), ← mul_sub]
    exact norm_deriv_mul_le hM _ hdiff

/-- A function on `(0, ∞)` bounded pointwise by `K` on `(0, a]` and vanishing beyond has
integral of norm at most `K a`. -/
theorem norm_setIntegral_Ioi_le_of_le_indicator {f : ℝ → ℝ} {K a : ℝ}
    (hf : Integrable f (volume.restrict (Ioi (0 : ℝ)))) (ha : 0 ≤ a)
    (h : ∀ u ∈ Ioi (0 : ℝ), ‖f u‖ ≤ (Ioc (0 : ℝ) a).indicator (fun _ => K) u) :
    ‖∫ u in Ioi (0 : ℝ), f u‖ ≤ K * a := by
  have hind : Integrable ((Ioc (0 : ℝ) a).indicator fun _ => K)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.integrableOn ?_
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (by simp [Real.volume_Ioc])
  calc ‖∫ u in Ioi (0 : ℝ), f u‖ ≤ ∫ u in Ioi (0 : ℝ), ‖f u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi (0 : ℝ), (Ioc (0 : ℝ) a).indicator (fun _ => K) u :=
        integral_mono_ae hf.norm hind <| by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu using h u hu
    _ = K * a := by
        rw [setIntegral_indicator measurableSet_Ioc,
          Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self, setIntegral_const,
          Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ha, smul_eq_mul, mul_comm]

/-- **The truncation term tends to `0`.** Its integrand vanishes unless
`log(B/q) < u ≤ T log x`, where the two partial sums differ by at most
`2 C_q (1 + log(B/q))^{-1-ε}`; so the term is
`O(log x · (1 + (β/2) log x)^{-1-ε}) = O((log x)^{-ε})`, which tends to `0`.

This is the second and last place the decay is spent, and the one that fixes the exponent's excess
over `1` as *strictly* positive: the bound is the decay at `w = B/q ≥ x^{β/2}` against a `u`-range
of length `T log x`, so an exponent of exactly `1` would leave the nonzero constant `2 M C T/β`
here. `B ≥ x^β` is used quantitatively, not merely through `B/q → ∞`. -/
theorem tendsto_integral_truncation_error (hdecay : MoebiusPartialSumDecay)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {q : ℕ} (hq : 1 ≤ q)
    {β : ℝ} (hβ : 0 < β) {B : ℝ → ℝ} (hB : ∀ᶠ x in atTop, x ^ β ≤ B x) :
    Tendsto (fun x : ℝ => ∫ u in Ioi (0 : ℝ),
        (deriv F (Notation.logx x q + u / Real.log x)
            * moebiusReciprocalBelow q (min (exp u) (B x / q))
          - deriv F (Notation.logx x q + u / Real.log x) * moebiusReciprocalBelow q (exp u)))
      atTop (nhds 0) := by
  obtain ⟨ε, hε, C, hC, hbd⟩ := exists_moebiusReciprocalBelow_decay hdecay hq
  obtain ⟨M, hM⟩ := hFc.deriv.exists_bound_of_continuous (hF.continuous_deriv le_rfl)
  obtain ⟨T, hT0, hTsupp⟩ := exists_deriv_support_bound hFc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hβ2 : (0 : ℝ) < β / 2 := by linarith
  refine squeeze_zero_norm' ?_
    (by simpa only [mul_zero, Function.comp_def] using
      (((tendsto_mul_one_div_one_add_rpow hβ2 hε).comp Real.tendsto_log_atTop).const_mul
        (M * (2 * C) * T)))
  filter_upwards [eventually_gt_atTop (1 : ℝ), hB,
    (tendsto_rpow_atTop hβ).eventually_ge_atTop (q : ℝ),
    (Tendsto.const_mul_atTop hβ2 Real.tendsto_log_atTop).eventually_ge_atTop (Real.log (q : ℝ))]
    with x hx hBx hqx hlogx
  have hL : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hrpos : (0 : ℝ) < x ^ β := Real.rpow_pos_of_pos hx0 β
  have hBq : (1 : ℝ) ≤ B x / q := (one_le_div hqR).mpr (hqx.trans hBx)
  have ha : 0 ≤ Notation.logx x q := div_nonneg hlogq hL.le
  -- the decay of the truncation, quantitatively
  have hlogBq : β / 2 * Real.log x ≤ Real.log (B x / q) := by
    rw [Real.log_div (hrpos.trans_le hBx).ne' hqR.ne']
    linarith [Real.log_le_log hrpos hBx, Real.log_rpow hx0 β]
  have hexpdec : 1 / (1 + Real.log (B x / q)) ^ (1 + ε)
      ≤ 1 / (1 + β / 2 * Real.log x) ^ (1 + ε) :=
    one_div_le_one_div_of_le (one_add_rpow_pos (by positivity))
      (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith))
  -- abbreviations
  set K : ℝ := M * (2 * C * (1 / (1 + Real.log (B x / q)) ^ (1 + ε))) with hKdef
  set f : ℝ → ℝ := fun u ↦ deriv F (Notation.logx x q + u / Real.log x)
      * moebiusReciprocalBelow q (min (exp u) (B x / q))
    - deriv F (Notation.logx x q + u / Real.log x) * moebiusReciprocalBelow q (exp u)
  have hIntf : Integrable f (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_deriv_mul_moebiusReciprocalBelow_min hF hε hC hL ha hBq hbd hM hTsupp (q := q)
      (a := Notation.logx x q) (L := Real.log x) (Bq := B x / q)).sub
    (integrableOn_deriv_mul_moebiusReciprocalBelow_exp hF hε hbd hM (q := q) (Notation.logx x q)
      (Real.log x))
  calc ‖∫ u in Ioi (0 : ℝ), f u‖ ≤ K * (T * Real.log x) :=
        norm_setIntegral_Ioi_le_of_le_indicator hIntf (by positivity) fun u hu ↦
          norm_deriv_mul_moebiusReciprocalBelow_min_sub_le hε.le hC.le hbd hBq hM hTsupp ha hL hu
    _ ≤ M * (2 * C) * T * (Real.log x * (1 / (1 + β / 2 * Real.log x) ^ (1 + ε))) := by
        nlinarith [mul_le_mul_of_nonneg_left hexpdec
          (by positivity : (0 : ℝ) ≤ M * (2 * C) * T * Real.log x)]

/-! ### The asymptotic -/

/-- **The truncated inner sum, reciprocal weight.** For `F` of class `C¹` with compact support,
`q ≥ 1`, `β > 0` and `B = B(x) ≥ x^β`,

  `log x · ∑_{f ≤ B/q, (f,q)=1} μ(f) F(log_x(qf))/f ⟶ -F'(0) · q/φ(q)`   (`x → ∞`).

The hypothesis `Gap212.Sieve.MoebiusPartialSumDecay` is a saving of a fixed power of the logarithm
in the prime number theorem, proved as `Gap212.Sieve.moebiusPartialSumDecay`.

The constant is the bare `q/φ(q)`, with no evenness hypothesis: the generating function
`∏_{p ∤ q}(1 - p^{-1-s})` has a simple zero at `s = 0` for every `q`. -/
@[gap212 "lem_inner_sum_reciprocal_asymptotic"]
theorem tendsto_logx_mul_innerSumReciprocal (hdecay : MoebiusPartialSumDecay)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) {q : ℕ} (hq : 1 ≤ q)
    {β : ℝ} (hβ : 0 < β) {B : ℝ → ℝ} (hB : ∀ᶠ x in atTop, x ^ β ≤ B x) :
    Tendsto (fun x : ℝ => Real.log x *
        ∑ f ∈ coprimeBelow q (B x / q), (μ f : ℝ) * F (Notation.logx x (q * f)) / (f : ℝ))
      atTop (nhds (-deriv F 0 * ((q : ℝ) / (q.totient : ℝ)))) := by
  obtain ⟨ε, hε, C, hC, hbd⟩ := exists_moebiusReciprocalBelow_decay hdecay hq
  obtain ⟨M, hM⟩ := hFc.deriv.exists_bound_of_continuous (hF.continuous_deriv le_rfl)
  obtain ⟨T, hT0, hTsupp⟩ := exists_deriv_support_bound hFc
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hGlim : Tendsto (fun x : ℝ => ∫ u in Ioi (0 : ℝ),
      deriv F (Notation.logx x q + u / Real.log x)
        * moebiusReciprocalBelow q (min (exp u) (B x / q))) atTop
      (nhds (deriv F 0 * ((q : ℝ) / (q.totient : ℝ)))) := by
    have hsum := (tendsto_integral_deriv_mul_moebiusReciprocalBelow_exp hdecay hF hFc hq).add
      (tendsto_integral_truncation_error hdecay hF hFc hq hβ hB)
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ), hB,
      (tendsto_rpow_atTop hβ).eventually_ge_atTop (q : ℝ)] with x hx hBx hqx
    have hL : 0 < Real.log x := Real.log_pos hx
    have hBq : (1 : ℝ) ≤ B x / q := (one_le_div hqR).mpr (hqx.trans hBx)
    have ha : 0 ≤ Notation.logx x q := div_nonneg hlogq hL.le
    have hIntG := integrableOn_deriv_mul_moebiusReciprocalBelow_min hF hε hC hL ha hBq hbd hM
      hTsupp (q := q) (a := Notation.logx x q) (L := Real.log x) (Bq := B x / q)
    have hIntP := integrableOn_deriv_mul_moebiusReciprocalBelow_exp hF hε hbd hM
      (q := q) (Notation.logx x q) (Real.log x)
    rw [integral_sub hIntG hIntP]
    ring
  rw [neg_mul]
  refine hGlim.neg.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (logx_mul_truncated_moebius_reciprocal hF hFc hx hq (B x)).symm

end Gap212.Sieve
