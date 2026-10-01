/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MarginalFacts
public import Gap212.Sieve.Certificate
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Algebra.Order.Chebyshev

/-!
# `L²` approximation: dilation, translation, mollification, symmetrization

The retreat that turns the certificate's `L²` function into a fixed smooth one rests on two
approximation facts: continuity of dilation and translation on `L²`, and `L²` convergence of
mollifications. Both are proved here, together with the smaller pieces the retreat needs — a
non-negative smooth `L²` approximation, the symmetrization over the coordinate permutations, and the
measurability of the support `T_k(p)`.

## From Mathlib

The proofs use `MeasureTheory.MemLp.exist_eLpNorm_sub_le` (smooth compactly supported functions are
dense in `L^p`), `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable` (mollifications
of a locally integrable function converge almost everywhere, by Lebesgue differentiation) and the
Haar change of variables `MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg`:

* `Gap212.GPY.tendsto_l2_shrinkTranslate` — `‖Σ_{a,β a}H - H‖₂ → 0` as `a ↓ 0`. A smooth
  representative reduces the claim to the continuous case, where the shrink-translates converge
  pointwise and live in one fixed compact set, so dominated convergence applies; the change of
  variables `Gap212.GPY.integral_comp_shrink` transfers the estimate back, the dilation being an
  `L²` contraction for `a > 0`.
* `Gap212.GPY.tendsto_l2_mollify` — `‖M_{φ,ϱ}H - H‖₂ → 0` as `ϱ ↓ 0`, for `H` bounded,
  measurable and vanishing off a ball. Boundedness takes the place of Young's inequality: it turns
  the almost-everywhere convergence into `L²` convergence by dominated convergence, the
  mollifications being uniformly bounded by `‖H‖_∞` and supported in one fixed compact set.

The mollifier is Mathlib's bump function of radius one, normed;
`Gap212.GPY.mollify_mollKernel_eq` identifies `Gap212.GPY.mollify` at that kernel with the
convolution against the normed bump of radius `ϱ`, which is the form Mathlib's convergence lemma is
stated in. `Gap212.GPY.mollify_shrinkTranslate_comm` separates the two limits when the radius is
tied to the shrink parameter, as the retreat data ties it.

## Main definitions

* `Gap212.GPY.bumpAt`, `Gap212.GPY.mollKernel`: the mollifier bump at radius `ϱ`, and the reference
  kernel — the normed bump of radius one.
* `Gap212.GPY.symmetrize`: the average of a function over the coordinate permutations.

## Main results

* `Gap212.measurableSet_T`: the support `T_k(p)` is measurable.
* `Gap212.GPY.tendsto_l2_shrinkTranslate`, `Gap212.GPY.tendsto_l2_mollify`: the two approximation
  facts.
* `Gap212.GPY.mollify_shrinkTranslate_comm`: mollifying after the shrink-translate is the
  shrink-translate of mollifying at the rescaled radius.
* `Gap212.GPY.integral_sq_symmetrize_sub_le`: symmetrizing does not increase the `L²` distance to a
  symmetric function.
* `Gap212.GPY.exists_nonneg_smooth_approx`: a non-negative function has non-negative smooth
  compactly supported `L²` approximations.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric
open scoped ENNReal Convolution

namespace Gap212

/-- The mass carried by the large coordinates is a measurable function of the point. -/
theorem measurable_sum_large (p : SupportParams) (k : ℕ) :
    Measurable (fun t : Fin k → ℝ ↦ ∑ i ∈ p.large k t, t i) := by
  classical
  simp only [SupportParams.large, Finset.sum_filter]
  exact Finset.measurable_sum _ fun i _ ↦
    Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply i))
      (measurable_pi_apply i) measurable_const

/-- The number of large coordinates is a measurable function of the point. -/
theorem measurable_card_large (p : SupportParams) (k : ℕ) :
    Measurable (fun t : Fin k → ℝ ↦ (p.large k t).card) := by
  classical
  simp only [SupportParams.large, Finset.card_filter]
  exact Finset.measurable_sum _ fun i _ ↦
    Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply i))
      measurable_const measurable_const

/-- The support is measurable. -/
theorem measurableSet_T (p : SupportParams) (k : ℕ) : MeasurableSet (T p k) := by
  classical
  refine MeasurableSet.iUnion fun j ↦ ?_
  have h1 : MeasurableSet {t : Fin k → ℝ | ∀ i, t i ∈ Set.Icc (0 : ℝ) 1} := by
    simpa [Set.pi] using
      MeasurableSet.univ_pi fun _ : Fin k ↦ measurableSet_Icc (a := (0 : ℝ)) (b := 1)
  have h2 : MeasurableSet {t : Fin k → ℝ |
      (∑ i, t i) ∈ Set.Ico (p.A j.castSucc + p.ε) (p.A j.succ + p.ε)} :=
    measurableSet_Ico.preimage (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i)
  have h3 : MeasurableSet {t : Fin k → ℝ |
      ∑ i ∈ p.large k t, t i ≤ p.B j (p.large k t).card} :=
    measurableSet_le (measurable_sum_large p k)
      ((measurable_from_top (f := fun n : ℕ ↦ p.B j n)).comp (measurable_card_large p k))
  convert (h1.inter h2).inter h3 using 1
  ext t
  simp only [SupportParams.stratum, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]

end Gap212

namespace Gap212.GPY

/-! ### The `L²` distance as a real integral -/

/-- The `L²` seminorm as a real integral. -/
theorem sqrt_integral_sq_eq_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) : √(∫ x, f x ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  norm_num

/-- An `eLpNorm` bound on `f - g` is a bound on `√(∫ (f - g)²)`. -/
private theorem sqrt_integral_sub_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} {ε : ℝ} (hε : 0 ≤ ε) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (h : eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal ε) : √(∫ x, (f x - g x) ^ 2 ∂μ) ≤ ε := by
  have e := sqrt_integral_sq_eq_eLpNorm (hf.sub hg)
  simp only [Pi.sub_apply] at e
  exact e ▸ ENNReal.toReal_le_of_le_ofReal hε h

/-- The triangle inequality for `√(∫ (f - g)²)`. -/
theorem sqrt_integral_sub_sq_triangle {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hh : MemLp h 2 μ) :
    √(∫ x, (f x - h x) ^ 2 ∂μ)
      ≤ √(∫ x, (f x - g x) ^ 2 ∂μ) + √(∫ x, (g x - h x) ^ 2 ∂μ) := by
  have e₁ := sqrt_integral_sq_eq_eLpNorm (hf.sub hh)
  have e₂ := sqrt_integral_sq_eq_eLpNorm (hf.sub hg)
  have e₃ := sqrt_integral_sq_eq_eLpNorm (hg.sub hh)
  simp only [Pi.sub_apply] at e₁ e₂ e₃
  rw [e₁, e₂, e₃, ← ENNReal.toReal_add (hf.sub hg).eLpNorm_ne_top (hg.sub hh).eLpNorm_ne_top]
  refine ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨(hf.sub hg).eLpNorm_ne_top, (hg.sub hh).eLpNorm_ne_top⟩) ?_
  simpa using eLpNorm_add_le (hf.sub hg).1 (hg.sub hh).1 one_le_two

/-- Reindexing `t : Fin k → ℝ` along `τ` by `MeasurableEquiv.piCongrLeft` is precomposition with
`τ.symm`. -/
theorem coe_piCongrLeft_perm {k : ℕ} (τ : Equiv.Perm (Fin k)) (t : Fin k → ℝ) :
    (MeasurableEquiv.piCongrLeft (fun _ : Fin k ↦ ℝ) τ) t = t ∘ τ.symm := by
  ext i
  have h := Equiv.piCongrLeft_apply_apply (fun _ : Fin k ↦ ℝ) τ t (τ.symm i)
  simpa [MeasurableEquiv.coe_piCongrLeft] using h

/-- Precomposition `t ↦ t ∘ σ` with a coordinate permutation preserves Lebesgue measure on
`Fin k → ℝ`. -/
theorem measurePreserving_comp_perm {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    MeasurePreserving (fun t : Fin k → ℝ ↦ t ∘ σ) volume volume := by
  convert volume_measurePreserving_piCongrLeft (fun _ : Fin k ↦ ℝ) σ.symm using 1
  funext t
  simp [coe_piCongrLeft_perm]

/-- Permuting coordinates preserves the integral over `Fin k → ℝ`: `∫ f (t ∘ σ) = ∫ f t`. -/
theorem integral_comp_perm {k : ℕ} (σ : Equiv.Perm (Fin k)) (f : (Fin k → ℝ) → ℝ) :
    ∫ t : Fin k → ℝ, f (t ∘ σ) = ∫ t, f t := by
  simpa [coe_piCongrLeft_perm] using
    (volume_measurePreserving_piCongrLeft (fun _ : Fin k ↦ ℝ) σ.symm).integral_comp' f

/-- If `f` is in `L²`, so is `t ↦ f (t ∘ σ)` for any coordinate permutation `σ`. -/
theorem memLp_comp_perm {k : ℕ} {f : (Fin k → ℝ) → ℝ} (σ : Equiv.Perm (Fin k))
    (hf : MemLp f 2 volume) : MemLp (fun t : Fin k → ℝ ↦ f (t ∘ σ)) 2 volume :=
  hf.comp_measurePreserving (measurePreserving_comp_perm σ)

/-- The affine change of variables behind the shrink-translate. -/
theorem integral_comp_shrink {k : ℕ} {r b : ℝ} (hr : 0 < r) (f : (Fin k → ℝ) → ℝ) :
    ∫ t : Fin k → ℝ, f (fun i ↦ (t i - b) / r) = r ^ k * ∫ t, f t := by
  have h := integral_sub_right_eq_self (μ := volume) (fun s ↦ f (r⁻¹ • s)) (fun _ : Fin k ↦ b)
  rw [Measure.integral_comp_inv_smul_of_nonneg volume f hr.le] at h
  convert h using 4 with t
  · funext i; simp [div_eq_inv_mul]
  · simp

/-- The `L²` distance of two shrink-translates. -/
theorem integral_sq_shrinkTranslate {k : ℕ} {a b : ℝ} (ha : a < 1) (G H : (Fin k → ℝ) → ℝ) :
    ∫ t : Fin k → ℝ, (shrinkTranslate a b G t - shrinkTranslate a b H t) ^ 2
      = (1 - a) ^ k * ∫ t, (G t - H t) ^ 2 := by
  simpa [shrinkTranslate] using
    integral_comp_shrink (r := 1 - a) (b := b) (by linarith) fun t ↦ (G t - H t) ^ 2

/-- A bounded measurable function vanishing off a ball is square-integrable. -/
theorem memLp_of_bounded_vanishing {k : ℕ} {p : ℝ≥0∞} {H : (Fin k → ℝ) → ℝ} {M R : ℝ}
    (hmeas : AEStronglyMeasurable H (volume : Measure (Fin k → ℝ)))
    (hM : ∀ t, |H t| ≤ M) (hR : ∀ t, R < ‖t‖ → H t = 0) : MemLp H p volume := by
  refine HasCompactSupport.memLp_of_bound (HasCompactSupport.intro (isCompact_closedBall 0 R)
    (fun t ht ↦ hR t ?_)) hmeas M (Eventually.of_forall fun t ↦ ?_)
  · simpa [mem_closedBall_zero_iff, not_le] using ht
  · simpa [Real.norm_eq_abs] using hM t

/-- The shrink-translate of a function vanishing off a ball vanishes off a slightly larger ball. -/
theorem shrinkTranslate_vanishing {k : ℕ} {H : (Fin k → ℝ) → ℝ} {R a b : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hR : ∀ t, R < ‖t‖ → H t = 0) :
    ∀ t : Fin k → ℝ, R + |b| < ‖t‖ → shrinkTranslate a b H t = 0 := by
  intro t ht
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hb : ‖(fun _ ↦ b : Fin k → ℝ)‖ ≤ |b| :=
    pi_norm_le_iff_of_nonneg (abs_nonneg b) |>.mpr fun i ↦ by simp
  have := norm_sub_norm_le t (fun _ ↦ b : Fin k → ℝ)
  refine hR _ ?_
  rw [show (fun i ↦ (t i - b) / (1 - a)) = (1 - a)⁻¹ • (t - fun _ ↦ b) by
      funext i; simp [div_eq_inv_mul],
    norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos h1a, lt_inv_mul_iff₀ h1a]
  nlinarith [norm_nonneg (t - (fun _ ↦ b : Fin k → ℝ))]



/-- A continuous compactly supported function is bounded and vanishes off a ball. -/
theorem exists_bound_vanishing {k : ℕ} {w : (Fin k → ℝ) → ℝ} (hw : Continuous w)
    (hws : HasCompactSupport w) : ∃ M R : ℝ, (∀ t, |w t| ≤ M) ∧ ∀ t, R < ‖t‖ → w t = 0 := by
  obtain ⟨M, hM⟩ := hws.exists_bound_of_continuous hw
  obtain ⟨R, hR⟩ := (hws.isCompact.isBounded).subset_closedBall 0
  refine ⟨M, R, fun t ↦ by simpa [Real.norm_eq_abs] using hM t, fun t ht ↦ ?_⟩
  exact image_eq_zero_of_notMem_tsupport fun h ↦ by linarith [mem_closedBall_zero_iff.1 (hR h)]

/-- Dominated convergence for `∫ (F a - g)²`, when every `F a` and `g` are bounded by `M` and
vanish off the ball of radius `R`. -/
private theorem tendsto_integral_sq_sub_of_bounded {k : ℕ} {l : Filter ℝ}
    [l.IsCountablyGenerated] {F : ℝ → (Fin k → ℝ) → ℝ} {g : (Fin k → ℝ) → ℝ} {M R : ℝ}
    (hFm : ∀ᶠ a in l, AEStronglyMeasurable (F a) volume) (hgm : AEStronglyMeasurable g volume)
    (hF : ∀ᶠ a in l, ∀ t, |F a t| ≤ M ∧ (R < ‖t‖ → F a t = 0))
    (hg : ∀ t, |g t| ≤ M ∧ (R < ‖t‖ → g t = 0))
    (hlim : ∀ᵐ t, Tendsto (fun a ↦ F a t) l (𝓝 (g t))) :
    Tendsto (fun a ↦ ∫ t, (F a t - g t) ^ 2) l (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    ((closedBall (0 : Fin k → ℝ) R).indicator fun _ ↦ 4 * M ^ 2)
    (hFm.mono fun a ha ↦ (ha.sub hgm).pow 2) ?_ ?_
    (hlim.mono fun t ht ↦ (ht.sub tendsto_const_nhds).pow 2)
  · simpa using h
  · filter_upwards [hF] with a ha
    refine Eventually.of_forall fun t ↦ ?_
    by_cases ht : t ∈ closedBall (0 : Fin k → ℝ) R
    · simp only [Set.indicator_of_mem ht, Pi.pow_apply, Pi.sub_apply, norm_pow, Real.norm_eq_abs]
      have : |F a t - g t| ≤ 2 * M := by linarith [abs_sub (F a t) (g t), (ha t).1, (hg t).1]
      nlinarith [abs_nonneg (F a t - g t)]
    · have hnt : R < ‖t‖ := by simpa using ht
      simp [(ha t).2 hnt, (hg t).2 hnt, Set.indicator_of_notMem ht]
  · rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const measure_closedBall_lt_top.ne

/-- **Dilation and translation are continuous on `L²`: the continuous case.** -/
theorem tendsto_integral_sq_shrinkTranslate_of_continuous {k : ℕ} {w : (Fin k → ℝ) → ℝ}
    (hw : Continuous w) {M R : ℝ} (hM : ∀ t, |w t| ≤ M) (hR : ∀ t, R < ‖t‖ → w t = 0)
    {β : ℝ → ℝ} (hβ : Tendsto β (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun a : ℝ ↦ ∫ t : Fin k → ℝ, (shrinkTranslate a (β a) w t - w t) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hev : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), 0 < a ∧ a < 1 ∧ |β a| ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds one_pos),
      hβ.eventually (closedBall_mem_nhds (0 : ℝ) one_pos)] with a ha ha' hb
    exact ⟨ha, ha', by simpa [Real.dist_eq] using hb⟩
  refine tendsto_integral_sq_sub_of_bounded (R := R + 1)
    (Eventually.of_forall fun a ↦ (hw.comp (continuous_pi fun i ↦
      ((continuous_apply i).sub continuous_const).div_const _)).aestronglyMeasurable)
    hw.aestronglyMeasurable ?_ (fun t ↦ ⟨hM t, fun ht ↦ hR t (by linarith)⟩)
    (Eventually.of_forall fun t ↦ (hw.tendsto t).comp (tendsto_pi_nhds.2 fun i ↦ ?_))
  · filter_upwards [hev] with a ⟨ha0, ha1, hβ1⟩ t
    exact ⟨hM _, fun ht ↦ shrinkTranslate_vanishing ha0 ha1 hR t (by linarith)⟩
  · simpa [Pi.div_def] using (tendsto_const_nhds (x := t i)).sub hβ |>.div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id.mono_left nhdsWithin_le_nhds))
      (by norm_num)

/-- The shrink-translate of a strongly measurable function is strongly measurable. -/
theorem stronglyMeasurable_shrinkTranslate {k : ℕ} {H : (Fin k → ℝ) → ℝ}
    (hmeas : StronglyMeasurable H) (a b : ℝ) : StronglyMeasurable (shrinkTranslate a b H) :=
  hmeas.comp_measurable
    (continuous_pi fun i ↦ ((continuous_apply i).sub continuous_const).div_const _).measurable

/-- **Dilation and translation are continuous on `L²`**, for a bounded measurable function
vanishing off a ball: `‖Σ_{a,β a}H - H‖₂ → 0` as `a ↓ 0`. This is the first of the two
approximation facts. -/
theorem tendsto_l2_shrinkTranslate {k : ℕ} {H : (Fin k → ℝ) → ℝ} {M R : ℝ}
    (hmeas : StronglyMeasurable H) (hM : ∀ t, |H t| ≤ M) (hR : ∀ t, R < ‖t‖ → H t = 0)
    {β : ℝ → ℝ} (hβ : Tendsto β (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun a : ℝ ↦ √(∫ t : Fin k → ℝ, (shrinkTranslate a (β a) H t - H t) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hHL : MemLp H 2 volume := memLp_of_bounded_vanishing hmeas.aestronglyMeasurable hM hR
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨w, hwcs, hwsm, hwle⟩ :=
    hHL.exist_eLpNorm_sub_le (by simp) one_le_two (ε := ε / 4) (by positivity)
  have hwc : Continuous w := hwsm.continuous
  have hwL : MemLp w 2 volume := hwc.memLp_of_hasCompactSupport hwcs
  obtain ⟨M', R', hM', hR'⟩ := exists_bound_vanishing hwc hwcs
  have hdHw := sqrt_integral_sub_sq_le (by positivity) hHL hwL hwle
  have hdwH :=
    sqrt_integral_sub_sq_le (ε := ε / 4) (by positivity) hwL hHL (by rwa [eLpNorm_sub_comm])
  -- the continuous piece tends to zero
  have hsq : Tendsto (fun a : ℝ ↦ √(∫ t : Fin k → ℝ, (shrinkTranslate a (β a) w t - w t) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_integral_sq_shrinkTranslate_of_continuous hwc hM' hR' hβ).sqrt
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds one_pos),
    hsq.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < ε / 4))]
    with a (ha0 : 0 < a) ha1 hb
  have hML : MemLp (shrinkTranslate a (β a) H) 2 volume :=
    memLp_of_bounded_vanishing (stronglyMeasurable_shrinkTranslate hmeas _ _).aestronglyMeasurable
      (fun t ↦ hM _) (shrinkTranslate_vanishing ha0 ha1 hR)
  have hwML : MemLp (shrinkTranslate a (β a) w) 2 volume :=
    memLp_of_bounded_vanishing
      (stronglyMeasurable_shrinkTranslate hwc.stronglyMeasurable _ _).aestronglyMeasurable
      (fun t ↦ hM' _) (shrinkTranslate_vanishing ha0 ha1 hR')
  -- the shrink-translate contracts the `L²` distance
  have hcontract : √(∫ t : Fin k → ℝ,
      (shrinkTranslate a (β a) H t - shrinkTranslate a (β a) w t) ^ 2) ≤ ε / 4 := by
    rw [integral_sq_shrinkTranslate ha1 H w, Real.sqrt_mul (by positivity)]
    exact (mul_le_of_le_one_left (Real.sqrt_nonneg _)
      (Real.sqrt_le_one.mpr (pow_le_one₀ (by linarith) (by linarith)))).trans hdHw
  rw [Real.dist_0_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  linarith [sqrt_integral_sub_sq_triangle hML hwML hHL, sqrt_integral_sub_sq_triangle hwML hwL hHL]

/-- The mollifier bump at radius `ϱ`: inner radius `ϱ/2`, outer radius `ϱ`. -/
noncomputable def bumpAt (k : ℕ) {ϱ : ℝ} (hϱ : 0 < ϱ) : ContDiffBump (0 : Fin k → ℝ) where
  rIn := ϱ / 2
  rOut := ϱ
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The reference mollifier kernel: the normed bump of radius one. -/
noncomputable def mollKernel (k : ℕ) : (Fin k → ℝ) → ℝ :=
  (bumpAt k one_pos).normed volume

/-- The bump of radius `ϱ` is the bump of radius one rescaled: `bumpAt k hϱ y` equals the
radius-one bump at `ϱ⁻¹ • y`. -/
theorem bumpAt_apply {k : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (y : Fin k → ℝ) :
    (bumpAt k hϱ) y = (bumpAt k one_pos) (ϱ⁻¹ • y) := by
  have h1 : ϱ / (ϱ / 2) = (1 : ℝ) / (1 / 2) := by field_simp
  have h2 : ((ϱ / 2)⁻¹ : ℝ) = (1 / 2 : ℝ)⁻¹ * ϱ⁻¹ := by field_simp
  simp only [ContDiffBump.apply, bumpAt, sub_zero, smul_smul, h1, h2]

/-- The integral of the bump of radius `ϱ` is `ϱ ^ k` times that of the bump of radius one. -/
theorem integral_bumpAt {k : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) :
    ∫ y : Fin k → ℝ, (bumpAt k hϱ) y = ϱ ^ k * ∫ y : Fin k → ℝ, (bumpAt k one_pos) y := by
  rw [integral_congr_ae (Eventually.of_forall (bumpAt_apply hϱ)),
    Measure.integral_comp_inv_smul_of_nonneg volume _ hϱ.le]
  simp

/-- The normed bump of radius `ϱ` at `y` is `(ϱ ^ k)⁻¹ * mollKernel k (ϱ⁻¹ • y)`. -/
theorem normed_bumpAt_eq {k : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (y : Fin k → ℝ) :
    ((bumpAt k hϱ).normed volume) y = (ϱ ^ k)⁻¹ * (mollKernel k) (ϱ⁻¹ • y) := by
  have hI : (0 : ℝ) < ∫ y : Fin k → ℝ, (bumpAt k one_pos) y := ContDiffBump.integral_pos _
  rw [ContDiffBump.normed_def, bumpAt_apply hϱ y, integral_bumpAt hϱ, mollKernel,
    ContDiffBump.normed_def]
  field_simp

/-- `Gap212.GPY.mollify` at the reference kernel is convolution with the normed bump of radius
`ϱ`. -/
theorem mollify_mollKernel_eq {k : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (G : (Fin k → ℝ) → ℝ) :
    mollify (mollKernel k) ϱ G
      = ((bumpAt k hϱ).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G := by
  simp only [mollify, ← normed_bumpAt_eq hϱ]

/-- The reference mollifier kernel is nonnegative. -/
theorem mollKernel_nonneg {k : ℕ} (y : Fin k → ℝ) : 0 ≤ mollKernel k y :=
  ContDiffBump.nonneg_normed _ _

/-- The reference mollifier kernel has integral one. -/
theorem integral_mollKernel (k : ℕ) : ∫ y : Fin k → ℝ, mollKernel k y = 1 :=
  ContDiffBump.integral_normed _

/-- The reference mollifier kernel is supported in the closed unit ball. -/
theorem support_mollKernel_subset (k : ℕ) :
    Function.support (mollKernel k) ⊆ closedBall 0 1 := by
  rw [mollKernel, ContDiffBump.support_normed_eq]
  exact ball_subset_closedBall.trans (by simp [bumpAt])

/-- The reference mollifier kernel is smooth. -/
theorem contDiff_mollKernel (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (mollKernel k) :=
  ContDiffBump.contDiff_normed _

/-- The reference mollifier kernel has compact support. -/
theorem hasCompactSupport_mollKernel (k : ℕ) : HasCompactSupport (mollKernel k) :=
  ContDiffBump.hasCompactSupport_normed _

/-- The reference mollifier kernel is integrable. -/
theorem integrable_mollKernel (k : ℕ) : Integrable (mollKernel k) (volume : Measure (Fin k → ℝ)) :=
  ContDiffBump.integrable_normed _



/-- The mollification of a bounded function obeys the same bound. -/
theorem abs_mollify_le {k : ℕ} {H : (Fin k → ℝ) → ℝ} {M ϱ : ℝ} (hϱ : 0 < ϱ)
    (hM : ∀ t, |H t| ≤ M) (t : Fin k → ℝ) : |mollify (mollKernel k) ϱ H t| ≤ M := by
  have hκ := ContDiffBump.nonneg_normed (bumpAt k hϱ) (μ := volume)
  rw [mollify_mollKernel_eq hϱ, convolution_lsmul, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le
    ((ContDiffBump.integrable_normed (bumpAt k hϱ) (μ := volume)).mul_const M)
    (Eventually.of_forall fun y ↦ ?_)).trans_eq ?_
  · rw [norm_smul, Real.norm_of_nonneg (hκ _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM _) (hκ _)
  · rw [integral_mul_const, ContDiffBump.integral_normed, one_mul]

/-- The mollification of a non-negative function is non-negative. -/
theorem mollify_nonneg {k : ℕ} {H : (Fin k → ℝ) → ℝ} {ϱ : ℝ} (hϱ : 0 < ϱ)
    (hH : ∀ t, 0 ≤ H t) (t : Fin k → ℝ) : 0 ≤ mollify (mollKernel k) ϱ H t := by
  rw [mollify_mollKernel_eq hϱ, convolution_lsmul]
  exact integral_nonneg fun y ↦ smul_nonneg (ContDiffBump.nonneg_normed _ _) (hH _)

/-- The mollification of a function vanishing off a ball vanishes off the `ϱ`-thickened ball. -/
theorem mollify_vanishing {k : ℕ} {H : (Fin k → ℝ) → ℝ} {R ϱ : ℝ} (hϱ : 0 < ϱ)
    (hR : ∀ t, R < ‖t‖ → H t = 0) :
    ∀ t : Fin k → ℝ, R + ϱ < ‖t‖ → mollify (mollKernel k) ϱ H t = 0 := by
  intro t ht
  rw [mollify_mollKernel_eq hϱ]
  by_contra hne
  obtain ⟨y, hy, s, hs, rfl⟩ := Set.mem_add.mp (support_convolution_subset
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (Function.mem_support.2 hne))
  rw [ContDiffBump.support_normed_eq, mem_ball_zero_iff] at hy
  have hy' : ‖y‖ < ϱ := by simpa [bumpAt] using hy
  have hs' : ‖s‖ ≤ R := not_lt.1 fun h ↦ hs (hR s h)
  linarith [norm_add_le y s]

/-- The mollification is smooth. -/
theorem contDiff_mollify {k : ℕ} {H : (Fin k → ℝ) → ℝ} {ϱ : ℝ} (hϱ : 0 < ϱ)
    (hH : LocallyIntegrable H (volume : Measure (Fin k → ℝ))) :
    ContDiff ℝ (⊤ : ℕ∞) (mollify (mollKernel k) ϱ H) := by
  rw [mollify_mollKernel_eq hϱ]
  exact HasCompactSupport.contDiff_convolution_left _ (ContDiffBump.hasCompactSupport_normed _)
    (ContDiffBump.contDiff_normed _) hH



/-- The mollifier bump as a total family indexed by the radius. -/
noncomputable def bumpFam (k : ℕ) (r : ℝ) : ContDiffBump (0 : Fin k → ℝ) :=
  bumpAt k (ϱ := if 0 < r then r else 1) (by split_ifs with h; exacts [h, one_pos])

/-- At a positive radius `r`, `bumpFam k r` is the bump `bumpAt k hr`. -/
theorem bumpFam_eq {k : ℕ} {r : ℝ} (hr : 0 < r) : bumpFam k r = bumpAt k hr := by
  simp only [bumpFam, if_pos hr]

/-- At a positive radius `r`, the outer radius of `bumpFam k r` is `r`. -/
theorem rOut_bumpFam {k : ℕ} {r : ℝ} (hr : 0 < r) : (bumpFam k r).rOut = r := by
  rw [bumpFam_eq hr, bumpAt]

/-- At a positive radius `r`, the inner radius of `bumpFam k r` is `r / 2`. -/
theorem rIn_bumpFam {k : ℕ} {r : ℝ} (hr : 0 < r) : (bumpFam k r).rIn = r / 2 := by
  rw [bumpFam_eq hr, bumpAt]

/-- **Mollifications converge almost everywhere**, by Lebesgue differentiation. -/
theorem ae_tendsto_mollify {k : ℕ} {H : (Fin k → ℝ) → ℝ}
    (hH : LocallyIntegrable H (volume : Measure (Fin k → ℝ)))
    {ϱ : ℝ → ℝ} (hϱpos : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < ϱ a) (hϱ : Tendsto ϱ (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ᵐ t : Fin k → ℝ,
      Tendsto (fun a : ℝ ↦ mollify (mollKernel k) (ϱ a) H t) (𝓝[>] (0 : ℝ)) (𝓝 (H t)) := by
  have hfam : Tendsto (fun a : ℝ ↦ (bumpFam k (ϱ a)).rOut) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine hϱ.congr' ?_
    filter_upwards [hϱpos] with a ha using (rOut_bumpFam ha).symm
  have hratio : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
      (bumpFam k (ϱ a)).rOut ≤ 2 * (bumpFam k (ϱ a)).rIn := by
    filter_upwards [hϱpos] with a ha
    rw [rOut_bumpFam ha, rIn_bumpFam ha]
    linarith
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := fun a : ℝ ↦ bumpFam k (ϱ a)) (l := 𝓝[>] (0 : ℝ)) (K := 2) hfam hratio hH
  filter_upwards [hae] with t ht
  refine ht.congr' ?_
  filter_upwards [hϱpos] with a ha
  rw [mollify_mollKernel_eq ha, bumpFam_eq ha]

/-- A bounded measurable function vanishing off a ball is integrable. -/
theorem integrable_of_bounded_vanishing {k : ℕ} {H : (Fin k → ℝ) → ℝ} {M R : ℝ}
    (hmeas : AEStronglyMeasurable H (volume : Measure (Fin k → ℝ)))
    (hM : ∀ t, |H t| ≤ M) (hR : ∀ t, R < ‖t‖ → H t = 0) :
    Integrable H (volume : Measure (Fin k → ℝ)) :=
  memLp_one_iff_integrable.mp (memLp_of_bounded_vanishing hmeas hM hR)

/-- **Mollifications converge in `L²`**, for a bounded measurable function vanishing off a ball.
This is the second of the two approximation facts. -/
theorem tendsto_l2_mollify {k : ℕ} {H : (Fin k → ℝ) → ℝ} {M R : ℝ}
    (hmeas : StronglyMeasurable H) (hM : ∀ t, |H t| ≤ M) (hR : ∀ t, R < ‖t‖ → H t = 0)
    {ϱ : ℝ → ℝ} (hϱpos : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < ϱ a) (hϱ : Tendsto ϱ (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun a : ℝ ↦ √(∫ t : Fin k → ℝ, (mollify (mollKernel k) (ϱ a) H t - H t) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hHloc : LocallyIntegrable H volume :=
    (integrable_of_bounded_vanishing hmeas.aestronglyMeasurable hM hR).locallyIntegrable
  have hϱ1 := hϱ.eventually (eventually_lt_nhds one_pos)
  simpa using (tendsto_integral_sq_sub_of_bounded (R := R + 1)
    (hϱpos.mono fun a ha ↦ (contDiff_mollify ha hHloc).continuous.aestronglyMeasurable)
    hmeas.aestronglyMeasurable
    (by filter_upwards [hϱpos, hϱ1] with a ha ha1 t using
      ⟨abs_mollify_le ha hM t, fun ht ↦ mollify_vanishing ha hR t (by linarith)⟩)
    (fun t ↦ ⟨hM t, fun ht ↦ hR t (by linarith)⟩) (ae_tendsto_mollify hHloc hϱpos hϱ)).sqrt

/-- A dilation inside an integral over `ℝ^k`. -/
theorem integral_eq_smul_integral_comp_smul {k : ℕ} {r : ℝ} (hr : 0 < r)
    (g : (Fin k → ℝ) → ℝ) : ∫ y : Fin k → ℝ, g y = r ^ k * ∫ z : Fin k → ℝ, g (r • z) := by
  rw [Measure.integral_comp_smul, Module.finrank_fin_fun, abs_of_pos (by positivity),
    smul_eq_mul, mul_inv_cancel_left₀ (by positivity)]

/-- **Mollifying commutes with the shrink-translate**, at the rescaled radius: this is what lets
the mollification radius be tied to `a` and still be handled by a fixed-function convergence. -/
theorem mollify_shrinkTranslate_comm {k : ℕ} {a b ϱ : ℝ} (ha : a < 1) (hϱ : 0 < ϱ)
    (H : (Fin k → ℝ) → ℝ) :
    mollify (mollKernel k) ϱ (shrinkTranslate a b H)
      = shrinkTranslate a b (mollify (mollKernel k) (ϱ / (1 - a)) H) := by
  have hr : (0 : ℝ) < 1 - a := by linarith
  funext t
  set c : Fin k → ℝ := fun i ↦ (t i - b) / (1 - a) with hc
  change _ = mollify (mollKernel k) (ϱ / (1 - a)) H c
  simp only [mollify, convolution_lsmul, smul_eq_mul]
  rw [integral_eq_smul_integral_comp_smul hr, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
  have h1 : shrinkTranslate a b H (t - (1 - a) • z) = H (c - z) := by
    simp only [shrinkTranslate]
    congr 1
    funext i
    simp [hc]
    field_simp
    ring
  dsimp only
  rw [h1, smul_smul, show ϱ⁻¹ * (1 - a) = (ϱ / (1 - a))⁻¹ by field_simp, div_pow]
  field_simp

/-! ### Symmetrization -/

/-- **The symmetrization of `G`**: the average of `G` over the coordinate permutations. It is
symmetric, and it moves `G` no further from a symmetric function in `L²`. -/
noncomputable def symmetrize {k : ℕ} (G : (Fin k → ℝ) → ℝ) : (Fin k → ℝ) → ℝ :=
  fun t ↦ (Fintype.card (Equiv.Perm (Fin k)) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin k), G (t ∘ σ)

/-- The symmetrization of any `G` is symmetric. -/
theorem symmetrize_symmetric {k : ℕ} (G : (Fin k → ℝ) → ℝ) : Symmetric (symmetrize G) := by
  intro τ t
  simp only [symmetrize]
  congr 1
  exact Fintype.sum_bijective (τ * ·) (Group.mulLeft_bijective τ) _ _ fun σ ↦ rfl

/-- The symmetrization of a nonnegative function is nonnegative. -/
theorem symmetrize_nonneg {k : ℕ} {G : (Fin k → ℝ) → ℝ} (hG : ∀ t, 0 ≤ G t) (t : Fin k → ℝ) :
    0 ≤ symmetrize G t :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun σ _ ↦ hG _)

/-- The symmetrization of a smooth function is smooth. -/
theorem contDiff_symmetrize {k : ℕ} {G : (Fin k → ℝ) → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (symmetrize G) :=
  contDiff_const.mul <|
    ContDiff.sum fun σ _ ↦ hG.comp (contDiff_pi.2 fun i ↦ contDiff_apply ℝ ℝ (σ i))

/-- If `G (t ∘ σ) = 0` for every coordinate permutation `σ`, then `symmetrize G t = 0`. -/
theorem symmetrize_eq_zero {k : ℕ} {G : (Fin k → ℝ) → ℝ} {t : Fin k → ℝ}
    (h : ∀ σ : Equiv.Perm (Fin k), G (t ∘ σ) = 0) : symmetrize G t = 0 := by
  simp only [symmetrize, h, Finset.sum_const_zero, mul_zero]

/-- **Symmetrization does not increase the `L²` distance to a symmetric function.** -/
theorem integral_sq_symmetrize_sub_le {k : ℕ} {G u : (Fin k → ℝ) → ℝ}
    (hG : MemLp G 2 (volume : Measure (Fin k → ℝ))) (hu : MemLp u 2 volume) (husym : Symmetric u) :
    (∫ t : Fin k → ℝ, (symmetrize G t - u t) ^ 2) ≤ ∫ t : Fin k → ℝ, (G t - u t) ^ 2 := by
  classical
  set N : ℕ := Fintype.card (Equiv.Perm (Fin k)) with hN
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- the integrand is an average of permuted differences
  have hpt : ∀ t : Fin k → ℝ, symmetrize G t - u t
      = (N : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin k), (G (t ∘ σ) - u (t ∘ σ)) := by
    intro t
    rw [Finset.sum_sub_distrib, Finset.sum_congr rfl fun σ _ ↦ husym σ t, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, symmetrize, ← hN]
    field_simp
  -- Chebyshev: the square of an average is at most the average of the squares
  have hsq : ∀ t : Fin k → ℝ, (symmetrize G t - u t) ^ 2
      ≤ (N : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin k), (G (t ∘ σ) - u (t ∘ σ)) ^ 2 := by
    intro t
    have hch := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun σ : Equiv.Perm (Fin k) ↦ G (t ∘ σ) - u (t ∘ σ))
    rw [Finset.card_univ, ← hN] at hch
    rw [hpt t, mul_pow]
    exact (mul_le_mul_of_nonneg_left hch (by positivity)).trans_eq (by field_simp)
  have hpint : ∀ σ : Equiv.Perm (Fin k),
      Integrable (fun t : Fin k → ℝ ↦ (G (t ∘ σ) - u (t ∘ σ)) ^ 2) volume :=
    fun σ ↦ (memLp_comp_perm σ (hG.sub hu)).integrable_sq
  calc (∫ t : Fin k → ℝ, (symmetrize G t - u t) ^ 2)
      ≤ ∫ t : Fin k → ℝ, (N : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin k), (G (t ∘ σ) - u (t ∘ σ)) ^ 2 :=
        integral_mono_of_nonneg (Eventually.of_forall fun t ↦ sq_nonneg _)
          ((integrable_finsetSum _ fun σ _ ↦ hpint σ).const_mul _) (Eventually.of_forall hsq)
    _ = ∫ t : Fin k → ℝ, (G t - u t) ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun σ _ ↦ hpint σ,
          Finset.sum_congr rfl fun σ _ ↦ integral_comp_perm σ fun t ↦ (G t - u t) ^ 2,
          Finset.sum_const, Finset.card_univ, ← hN, nsmul_eq_mul]
        field_simp


/-! ### A non-negative smooth approximation -/

/-- **A non-negative function has non-negative smooth compactly supported `L²` approximations.**
Mathlib's smooth approximation gives no sign; the smooth absolute value `√(w² + η²) - η`, which is
non-negative, vanishes where `w` does and is within `η` of `|w|`, supplies it. -/
theorem exists_nonneg_smooth_approx {k : ℕ} {G : (Fin k → ℝ) → ℝ}
    (hG : MemLp G 2 (volume : Measure (Fin k → ℝ))) (hGnn : ∀ t, 0 ≤ G t) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : (Fin k → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧ HasCompactSupport v ∧ (∀ t, 0 ≤ v t) ∧
      √(∫ t : Fin k → ℝ, (v t - G t) ^ 2) ≤ ε := by
  obtain ⟨w, hwcs, hwsm, hwle⟩ :=
    hG.exist_eLpNorm_sub_le (by simp) one_le_two (ε := ε / 2) (by positivity)
  have hwc : Continuous w := hwsm.continuous
  have hwL : MemLp w 2 (volume : Measure (Fin k → ℝ)) := hwc.memLp_of_hasCompactSupport hwcs
  obtain ⟨M, R, hM, hR⟩ := exists_bound_vanishing hwc hwcs
  -- the distance from `|w|` to `G` is no worse than that from `w`
  have hsub : MemLp (fun t ↦ G t - w t) 2 (volume : Measure (Fin k → ℝ)) := by
    simpa [Pi.sub_def] using hG.sub hwL
  have hdGw := sqrt_integral_sub_sq_le (by positivity) hG hwL hwle
  have habs : √(∫ t : Fin k → ℝ, (|w t| - G t) ^ 2) ≤ ε / 2 := by
    refine le_trans (Real.sqrt_le_sqrt ?_) hdGw
    refine integral_mono_of_nonneg (Eventually.of_forall fun t ↦ sq_nonneg _)
      hsub.integrable_sq (Eventually.of_forall fun t ↦ ?_)
    have h := abs_abs_sub_abs_le_abs_sub (w t) (G t)
    rw [abs_of_nonneg (hGnn t), abs_sub_comm (w t)] at h
    exact sq_le_sq.2 h
  -- the smooth absolute value
  set V : ℝ := (volume (closedBall (0 : Fin k → ℝ) R)).toReal with hV
  have hVnn : 0 ≤ V := ENNReal.toReal_nonneg
  set η : ℝ := (ε / 2) / (√V + 1) with hη
  have hηpos : 0 < η := by positivity
  set v : (Fin k → ℝ) → ℝ := fun t ↦ √(w t ^ 2 + η ^ 2) - η with hv
  have hvsm : ContDiff ℝ (⊤ : ℕ∞) v :=
    ((hwsm.pow 2).add contDiff_const).sqrt (fun t ↦ by positivity) |>.sub contDiff_const
  have hvnn : ∀ t, 0 ≤ v t := fun t ↦
    sub_nonneg.2 <| (le_abs_self η).trans (Real.abs_le_sqrt (le_add_of_nonneg_left (sq_nonneg _)))
  have hvsupp : ∀ t, R < ‖t‖ → v t = 0 := fun t ht ↦ by
    simp [hv, hR t ht, Real.sqrt_sq hηpos.le]
  have hvcs : HasCompactSupport v :=
    HasCompactSupport.intro (isCompact_closedBall 0 R) fun t ht ↦
      hvsupp t (by simpa [mem_closedBall_zero_iff, not_le] using ht)
  have hvL : MemLp v 2 (volume : Measure (Fin k → ℝ)) :=
    hvsm.continuous.memLp_of_hasCompactSupport hvcs
  -- `v` is within `η` of `|w|`, and both vanish off the ball
  have hclose : ∀ t, abs (v t - |w t|) ≤ η := by
    intro t
    have h1 : |w t| ≤ √(w t ^ 2 + η ^ 2) := Real.abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg η))
    have h2 : √(w t ^ 2 + η ^ 2) ≤ |w t| + η :=
      Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [abs_nonneg (w t), sq_abs (w t)]⟩
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hdvw : √(∫ t : Fin k → ℝ, (v t - |w t|) ^ 2) ≤ ε / 2 := by
    have hbint : Integrable ((closedBall (0 : Fin k → ℝ) R).indicator (fun _ ↦ η ^ 2))
        (volume : Measure (Fin k → ℝ)) := by
      rw [integrable_indicator_iff measurableSet_closedBall]
      exact integrableOn_const measure_closedBall_lt_top.ne
    have hle : (∫ t : Fin k → ℝ, (v t - |w t|) ^ 2)
        ≤ ∫ t : Fin k → ℝ, (closedBall (0 : Fin k → ℝ) R).indicator (fun _ ↦ η ^ 2) t := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun t ↦ sq_nonneg _) hbint
        (Eventually.of_forall fun t ↦ ?_)
      beta_reduce
      by_cases htK : t ∈ closedBall (0 : Fin k → ℝ) R
      · rw [Set.indicator_of_mem htK, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hclose t) 2
      · have hnt : R < ‖t‖ := by simpa using htK
        simp [Set.indicator_of_notMem htK, hvsupp t hnt, hR t hnt]
    have hind : (∫ t : Fin k → ℝ,
        (closedBall (0 : Fin k → ℝ) R).indicator (fun _ ↦ η ^ 2) t) = η ^ 2 * V := by
      rw [integral_indicator measurableSet_closedBall, setIntegral_const, hV, smul_eq_mul,
        measureReal_def]
      ring
    refine (Real.sqrt_le_sqrt (hle.trans_eq hind)).trans ?_
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hηpos.le, hη, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity)]
    nlinarith [Real.sqrt_nonneg V]
  -- combine
  refine ⟨v, hvsm, hvcs, hvnn, ?_⟩
  have habsL : MemLp (fun t ↦ |w t|) 2 (volume : Measure (Fin k → ℝ)) := by
    simpa [Pi.abs_def] using hwL.abs
  linarith [sqrt_integral_sub_sq_triangle hvL habsL hG]

/-- `√45 ≤ 7`. -/
theorem sqrt_fortyFive_le : √45 ≤ 7 :=
  Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩


/-- The arithmetic of the final choice: if the square root of `X` sits within `γ` of `A`, that of
`Y` is at least `B - 2γ`, and `γ` is small compared with both `A` and the certificate's slack
`√45·B - A`, then `X` is positive and below `45Y`. -/
theorem gap_of_sqrt_bounds {X Y A B γ : ℝ} (hXnn : 0 ≤ X) (hYnn : 0 ≤ Y)
    (hApos : 0 < A) (hγpos : 0 < γ) (hγA : γ ≤ A / 2) (hγ20 : 20 * γ ≤ √45 * B - A)
    (hsqIlow : A - γ ≤ √X) (hsqI : √X ≤ A + γ) (hsqJ : B - 2 * γ ≤ √Y) :
    0 < X ∧ X < 45 * Y := by
  have h45pos : (0 : ℝ) < √45 := Real.sqrt_pos.mpr (by norm_num)
  have hkey : A + γ < √45 * (B - 2 * γ) := by nlinarith [sqrt_fortyFive_le]
  have hB2γ : 0 < B - 2 * γ := pos_of_mul_pos_right (by linarith) h45pos.le
  refine ⟨Real.sqrt_pos.1 ((half_pos hApos).trans_le (by linarith)), ?_⟩
  have hsq := pow_lt_pow_left₀ hkey (by linarith) two_ne_zero
  rw [mul_pow, Real.sq_sqrt (by norm_num)] at hsq
  linarith [(Real.sq_sqrt hXnn).symm.trans_le (pow_le_pow_left₀ (Real.sqrt_nonneg X) hsqI 2),
    (Real.le_sqrt hB2γ.le hYnn).1 hsqJ]

end Gap212.GPY
