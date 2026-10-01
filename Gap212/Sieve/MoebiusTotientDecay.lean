/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MoebiusPartialSumDecay
public import Gap212.Sieve.MoebiusTotientAbel

/-!
# Log-power decay of the truncated Möbius–totient partial sum

`Gap212.Sieve.MoebiusTotientAbel` evaluates the *damped* integral
`∫_1^∞ T_e(w) w^{-s-1} dw = h_e(s)/s → c_e` as `s → 0⁺`, with
`T_e(w) = ∑_{f ≤ w, (f,e)=1} μ(f)/φ(f)`. Passing from there to the *undamped*
`∫_0^∞ T_e(exp u) du`, which is what the totient-weight inner sum needs, requires an `L¹` majorant
for `u ↦ T_e(exp u)` on `[0, ∞)`, and the elementary bounds do not supply one: `|T_e| ≤ 1` is not
integrable over a range of length `Θ(log x)`.

`Gap212.Sieve.MoebiusTotientPartialSumDecay` is the majorant: an absolute `ε > 0` and a per-`e`
constant with `|T_e(w)| ≤ C_e (1 + log w)^{-1-ε}` for `w ≥ 2`. Then
`|T_e(exp u)| ≤ C_e (1 + u)^{-1-ε}`, which is integrable on
`(0, ∞)`, so dominated convergence applies; the elementary facts about that majorant are shared
with the reciprocal weight and are in `Gap212.Sieve.MoebiusPartialSumDecay`.

## Transfer from the reciprocal weight

`Gap212.Sieve.MoebiusPartialSumDecay` is the same statement for
`S_e(w) = ∑_{f ≤ w, (f,e)=1} μ(f)/f`. Neither implies the other by comparison:
`1/φ(f) = (1/f)·f/φ(f)` with `f/φ(f) = ∏_{p ∣ f}(1 - 1/p)^{-1}`, a factor that is unbounded above
and bounded below by `1`.

`Gap212.Sieve.moebiusTotientPartialSumDecay` (`Gap212.Sieve.MoebiusTotientTransfer`) proves the
decay at `ε = 1` from `Gap212.Sieve.moebiusPartialSumDecay` by a Dirichlet convolution. Write
`b_e(f) = μ(f)/φ(f)` and `m_e(f) = μ(f)/f`, both restricted to `(f,e) = 1`. Then
`b_e = m_e * g_e`, where `g_e = ζ * (id ⬝ μ ⬝ φ⁻¹)` restricted, so that `g_e(p^j) = -1/(p^j(p-1))`.
Summing over the hyperbola gives

  `T_e(w) = ∑_{n ≤ w} g_e(n) · S_e(w/n)`,

with the same modulus `e` on the right. Since `∑_n √n |g_e(n)|` converges — an Euler product
`∏_p (1 + 1/((p-1)(√p - 1)))`, bounded by comparison with `∑ k^{-3/2}` — the terms with `n > √w`
contribute `O(w^{-1/4} log w)`, and for `n ≤ √w` the reciprocal-weight decay gives
`|S_e(w/n)| ≤ 4C_e(1 + log w)^{-2}`. So the decay transfers with a constant factor.

## Main definitions

* `Gap212.Sieve.MoebiusTotientPartialSumDecay`: the log-power decay of `T_e`.

## Main results

* `Gap212.Sieve.moebiusTotientPartialSumDecay_of_subexp`: the error-term prime number theorem
  implies this decay.
* `Gap212.Sieve.measurable_moebiusTotientBelow`: `T_e` is measurable, being a function of `⌊·⌋₊`.
* `Gap212.Sieve.exists_moebiusTotientBelow_decay`: the decay valid from `w ≥ 1` rather than
  `w ≥ 2`, with a positive constant.
* `Gap212.Sieve.integral_moebiusTotientBelow_exp`: the undamped Abel integral,
  `∫_0^∞ T_e(exp u) du = c_e`.
-/
@[expose] public section

open ArithmeticFunction Filter MeasureTheory Real Set Topology
open scoped ArithmeticFunction.Moebius

namespace Gap212.Sieve

/-- **Log-power decay of the truncated Möbius–totient partial sum**: there are an absolute `ε > 0`
and a constant `C_e` with `|T_e(w)| ≤ C_e (1 + log w)^{-1-ε}` for `w ≥ 2`, where
`T_e(w) = ∑_{f ≤ w, (f,e)=1} μ(f)/φ(f)`.

It is proved at `ε = 1` as `Gap212.Sieve.moebiusTotientPartialSumDecay` in
`Gap212.Sieve.MoebiusTotientTransfer`; the totient-weight inner-sum asymptotic takes it as a
hypothesis. It is the analogue of `Gap212.Sieve.MoebiusPartialSumDecay` for the weight `μ(f)/φ(f)`
in place of `μ(f)/f`. -/
@[gap212 "lem_moebius_totient_partial_sum_decay"]
def MoebiusTotientPartialSumDecay : Prop :=
  ∃ ε > (0 : ℝ), ∀ e : ℕ, 1 ≤ e → ∃ C : ℝ, ∀ w : ℝ, 2 ≤ w →
    |moebiusTotientBelow e w| ≤ C / (1 + Real.log w) ^ (1 + ε)

/-- **The error-term prime number theorem implies this decay**, at `ε = 1`, by the comparison
`Gap212.Sieve.exists_const_exp_neg_mul_sqrt_le`: the hypothesis stated here is *weaker* than
`|T_e(w)| ≤ C_e exp(-c√(log w))`. -/
theorem moebiusTotientPartialSumDecay_of_subexp
    (h : ∃ c > (0 : ℝ), ∀ e : ℕ, 1 ≤ e → ∃ C : ℝ, ∀ w : ℝ, 2 ≤ w →
      |moebiusTotientBelow e w| ≤ C * exp (-(c * √(Real.log w)))) :
    MoebiusTotientPartialSumDecay := by
  obtain ⟨c, hc, he⟩ := h
  obtain ⟨K, hK, hKbd⟩ := exists_const_exp_neg_mul_sqrt_le hc
  refine ⟨1, one_pos, fun e he1 => ?_⟩
  obtain ⟨C, hC⟩ := he e he1
  refine ⟨max C 0 * K, fun w hw => ?_⟩
  rw [mul_div_assoc]
  exact (hC w hw).trans <| mul_le_mul (le_max_left _ _)
    (hKbd _ (Real.log_nonneg (by linarith))) (Real.exp_pos _).le (le_max_right _ _)

/-! ### Measurability and the elementary bound below `2` -/

/-- `T_e` is measurable: it depends on its real argument only through `⌊·⌋₊`. -/
theorem measurable_moebiusTotientBelow (e : ℕ) :
    Measurable (moebiusTotientBelow e) := by
  change Measurable ((fun n : ℕ => ∑ f ∈ (Finset.Icc 1 n).filter fun f => Nat.Coprime f e,
    (μ f : ℝ) / (f.totient : ℝ)) ∘ (Nat.floor : ℝ → ℕ))
  exact measurable_from_top.comp Nat.measurable_floor

/-- `|T_e(t)| ≤ 1` for `t < 2`: the only index in range is `f = 1`, where `μ(1)/φ(1) = 1`. -/
theorem abs_moebiusTotientBelow_le_one (e : ℕ) {t : ℝ} (ht : t < 2) :
    |moebiusTotientBelow e t| ≤ 1 := by
  calc |moebiusTotientBelow e t| ≤ ∑ f ∈ coprimeBelow e t, |(μ f : ℝ) / (f.totient : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f ∈ ({1} : Finset ℕ), |(μ f : ℝ) / (f.totient : ℝ)| := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun f hf ↦ ?_) fun _ _ _ => abs_nonneg _
        obtain ⟨hf0, hle, -⟩ := mem_coprimeBelow.mp hf
        have : f < 2 := by exact_mod_cast hle.trans_lt ht
        exact Finset.mem_singleton.mpr (by omega)
    _ = 1 := by simp

/-! ### The decay from `w ≥ 1` -/

/-- **The decay, normalised.** From `Gap212.Sieve.MoebiusTotientPartialSumDecay` one gets a
positive constant and the bound from `w ≥ 1` rather than `w ≥ 2`: below `2` the sum is
`μ(1)/φ(1) = 1`, which the constant `(1 + log 2)^{1+ε}` absorbs. -/
theorem exists_moebiusTotientBelow_decay (hdecay : MoebiusTotientPartialSumDecay) {e : ℕ}
    (he : 1 ≤ e) : ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ w : ℝ, 1 ≤ w →
      |moebiusTotientBelow e w| ≤ C / (1 + Real.log w) ^ (1 + ε) := by
  obtain ⟨ε, hε, he'⟩ := hdecay
  obtain ⟨C, hC⟩ := he' e he
  refine ⟨ε, hε, max C ((1 + Real.log 2) ^ (1 + ε)),
    (one_add_rpow_pos (Real.log_nonneg one_le_two)).trans_le (le_max_right _ _), fun w hw => ?_⟩
  have hlw : 0 ≤ Real.log w := Real.log_nonneg hw
  have hwpos : (0 : ℝ) < (1 + Real.log w) ^ (1 + ε) := one_add_rpow_pos hlw
  rcases le_or_gt 2 w with h2 | h2
  · exact (hC w h2).trans (by gcongr; exact le_max_left _ _)
  · refine (abs_moebiusTotientBelow_le_one e h2).trans ?_
    rw [one_le_div hwpos]
    exact le_trans (by gcongr) (le_max_right C _)

/-- The decay at `w = exp u`, the form the `u`-integral uses: `|T_e(exp u)| ≤ C (1 + u)^{-1-ε}`. -/
theorem abs_moebiusTotientBelow_exp_le {e : ℕ} {ε C : ℝ}
    (h : ∀ w : ℝ, 1 ≤ w → |moebiusTotientBelow e w| ≤ C / (1 + Real.log w) ^ (1 + ε))
    {u : ℝ} (hu : 0 ≤ u) : |moebiusTotientBelow e (exp u)| ≤ C / (1 + u) ^ (1 + ε) := by
  have := h (exp u) (Real.one_le_exp hu)
  rwa [Real.log_exp] at this

/-! ### The undamped Abel integral -/

/-- The change of variables `w = exp u` on the Mellin integral: for `s > 0`,
`∫_1^∞ T_e(w) w^{-s-1} dw = ∫_0^∞ T_e(exp u) e^{-su} du`. -/
theorem integral_moebiusTotientBelow_exp_rpow (e : ℕ) (s : ℝ) :
    (∫ u in Ioi (0 : ℝ), moebiusTotientBelow e (exp u) * exp (-(s * u)))
      = ∫ w in Ioi (1 : ℝ), moebiusTotientBelow e w * w ^ (-s - 1) := by
  have h := integral_comp_exp_Ioi
    (fun w : ℝ => moebiusTotientBelow e w * w ^ (-s - 1)) 0
  rw [Real.exp_zero] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [smul_eq_mul, Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, mul_left_comm,
    ← Real.exp_add]
  ring_nf

/-- **The undamped Abel integral**: `∫_0^∞ T_e(exp u) du = c_e`, for every even `e ≥ 1`.

`Gap212.Sieve.tendsto_integral_moebiusTotientBelow_rpow` gives the *damped* integral's limit, which
is Abel summability and strictly weaker. The decay supplies the majorant `C (1 + u)^{-1-ε}`,
integrable on `(0, ∞)` by `Gap212.Sieve.integrableOn_const_div_one_add_rpow`, so dominated
convergence as `s → 0⁺` identifies the two. -/
theorem integral_moebiusTotientBelow_exp (hdecay : MoebiusTotientPartialSumDecay) {e : ℕ}
    (he : 1 ≤ e) (he2 : 2 ∣ e) :
    (∫ u in Ioi (0 : ℝ), moebiusTotientBelow e (exp u))
      = ((e : ℝ) / (e.totient : ℝ)) *
        ∏' p : ℕ, if p.Prime ∧ ¬ p ∣ e then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 := by
  obtain ⟨ε, hε, C, hC, hbd⟩ := exists_moebiusTotientBelow_decay hdecay he
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable
      (fun u : ℝ => moebiusTotientBelow e (exp u) * exp (-(s * u)))
      (volume.restrict (Ioi (0 : ℝ))) := fun s ↦
    (((measurable_moebiusTotientBelow e).comp Real.measurable_exp).mul
      (by fun_prop)).aestronglyMeasurable.restrict
  have hlim : Tendsto (fun s : ℝ => ∫ u in Ioi (0 : ℝ),
      moebiusTotientBelow e (exp u) * exp (-(s * u))) (𝓝[>] (0 : ℝ))
      (nhds (∫ u in Ioi (0 : ℝ), moebiusTotientBelow e (exp u))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => C / (1 + u) ^ (1 + ε)) (Eventually.of_forall hmeas) ?_
      (integrableOn_const_div_one_add_rpow hε C) ?_
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith))).trans
        (abs_moebiusTotientBelow_exp_le hbd hu.le)
    · filter_upwards with u
      have hcont : ContinuousAt (fun s : ℝ => exp (-(s * u))) 0 := by fun_prop
      simpa using (hcont.continuousWithinAt.tendsto (s := Ioi 0)).const_mul
        (moebiusTotientBelow e (exp u))
  exact tendsto_nhds_unique hlim <| (tendsto_integral_moebiusTotientBelow_rpow he he2).congr
    fun s ↦ (integral_moebiusTotientBelow_exp_rpow e s).symm

end Gap212.Sieve
