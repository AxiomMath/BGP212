/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.L2Approximation
public import Gap212.Sieve.RetreatFacts
public import Gap212.Sieve.CutoffContinuity
public meta import Gap212.Attr

/-!
# The retreat produces a fixed smooth function

The certificate hands the sieve an `L²` function `F` on `T₄₅(p⋆)` with a variational gap. The sieve
cannot use it: the weights are built from a *smooth* function supported strictly inside the
orthant, and its support has to clear the caps with room to spare. This file performs the retreat
that produces such a function and shows the gap survives it.

The retreat of `H` at `a` is `Gap212.GPY.retreatFun`: shrink-translate by the retreat data at `a`,
mollify at the retreat radius, symmetrize. The approximation facts it rests on — neither of which
Mathlib has — are proved in `Gap212.Sieve.L2Approximation`.

## Two departures from the standard construction

* A *permutation-invariant* mollifier would make the retreat of a symmetric function symmetric.
  Mathlib's bump functions carry no such invariance, so the retreat is
  *symmetrized* instead — averaged over the coordinate permutations, which costs nothing in `L²`
  and preserves smoothness, non-negativity and the support clause, the buffered region being
  permutation-invariant (`Gap212.GPY.mem_bufferedRegion_of_comp_perm`).
* The function fed to the retreat is not `|F|` but a non-negative smooth approximation of it
  truncated to `T₄₅(p⋆)`: bounded and compactly supported, which is what makes the `L²` convergence
  of the mollifications available at all.

## How the gap is chosen

The gap is tracked through square roots, which is the shape of the Lipschitz estimate
`Gap212.GPY.abs_sqrt_marginalForm_sub_le`: with `A = √(I_T(|F|))` and
`B = √(J̃_c(|F|))` the gap reads `A < √45·B`, and `a` is chosen so small that
`√(I_T(F₀)) ≤ A + γ` and `√(J̃_{(1-ε₀)c}(F₀)) ≥ B - 2γ` for a `γ` small against both `A` and the
slack `√45·B - A` (`Gap212.GPY.gap_of_sqrt_bounds`). Three convergences enter: the two legs of the
retreat, and the continuity of the marginal form in the cutoff
(`Gap212.GPY.tendsto_marginalForm_cutoff`), since the retreated cutoff `(1 - ε₀)c` moves with `a`.

## Main definitions

* `Gap212.GPY.retreatShift`, `Gap212.GPY.retreatRadius`: the translation and the mollifier radius
  of the retreat data at `a`, at `k = 45`.
* `Gap212.GPY.retreatFun`: the retreat of `H` at `a`.

## Main results

* `Gap212.GPY.mem_bufferedRegion_of_comp_perm`: the buffered region is permutation-invariant.
* `Gap212.GPY.l2_retreatFun_le`: the `L²` distance from the retreat to a symmetric target, split
  across the mollification, the shrink-translate and the target.
* `Gap212.GPY.exists_retreat_gap`: the retreat produces a fixed symmetric non-negative smooth
  compactly supported function, supported in the buffered region, with the variational gap at the
  retreated cutoff.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric
open scoped ENNReal Convolution

namespace Gap212.GPY

/-! ### The buffered region is permutation-invariant -/

/-- Permuting the coordinates of `t` by `σ` does not change the sum of the coordinates over
`roughAt θ`. -/
theorem sum_roughAt_comp_perm {k : ℕ} (θ : ℝ) (t : Fin k → ℝ) (σ : Equiv.Perm (Fin k)) :
    ∑ i ∈ roughAt θ (t ∘ σ), (t ∘ σ) i = ∑ i ∈ roughAt θ t, t i := by
  classical
  simp only [roughAt, Finset.sum_filter]
  exact Fintype.sum_equiv σ _ _ fun i ↦ rfl

/-- Permuting the coordinates of `t` by `σ` does not change the cardinality of `roughAt θ`. -/
theorem card_roughAt_comp_perm {k : ℕ} (θ : ℝ) (t : Fin k → ℝ) (σ : Equiv.Perm (Fin k)) :
    (roughAt θ (t ∘ σ)).card = (roughAt θ t).card := by
  classical
  simp only [roughAt, Finset.card_filter]
  exact Fintype.sum_equiv σ _ _ fun i ↦ rfl

/-- **The buffered retreat region is invariant under permuting the coordinates**: all three of its
clauses are. -/
theorem mem_bufferedRegion_of_comp_perm {p : SupportParams} {k : ℕ} {j : Fin p.n} {ε₀ ζ₁ κ : ℝ}
    {t : Fin k → ℝ} (σ : Equiv.Perm (Fin k))
    (ht : t ∘ σ ∈ bufferedRegion p k j ε₀ ζ₁ κ) : t ∈ bufferedRegion p k j ε₀ ζ₁ κ := by
  obtain ⟨hcube, htot, hcap⟩ := ht
  refine ⟨fun i ↦ by simpa using hcube (σ.symm i), ?_, fun hne ↦ ?_⟩
  · have hs : ∑ i, (t ∘ σ) i = ∑ i, t i := Fintype.sum_equiv σ _ _ fun i ↦ rfl
    rwa [← hs]
  · have hcard := card_roughAt_comp_perm (p.δ - ζ₁) t σ
    have h := hcap (by rwa [← Finset.card_pos, hcard, Finset.card_pos])
    rwa [sum_roughAt_comp_perm, hcard] at h


/-! ### The retreat -/

/-- Every point of the support has non-negative coordinates of total mass at most one: the
hypothesis under which the marginal-form estimates of `Gap212.Sieve.MarginalFacts` apply. -/
theorem mem_cornerSimplex_of_mem_T {t : Fin 45 → ℝ} (ht : t ∈ T gap212Params 45) :
    (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1 := by
  refine ⟨fun i ↦ (Gap212.mem_unitCube_of_mem_T ht i).1, ?_⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
  linarith [hj.2.1.2, gap212Params_A_succ j]

/-- Every point of the buffered region has non-negative coordinates of total mass at most one. -/
theorem mem_cornerSimplex_of_mem_bufferedRegion {j : Fin gap212Params.n} {ε₀ ζ₁ κ : ℝ}
    (hε₀ : 0 ≤ ε₀) (hζ₁ : 0 ≤ ζ₁) (hκ : 0 ≤ κ) {t : Fin 45 → ℝ}
    (ht : t ∈ bufferedRegion gap212Params 45 j ε₀ ζ₁ κ) :
    (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1 := by
  obtain ⟨hcube, htot, -⟩ := ht
  refine ⟨fun i ↦ le_trans hζ₁ (hcube i).1, ?_⟩
  nlinarith [htot, gap212Params_A_succ j]

/-- Every point of the buffered region lies in the unit ball. -/
theorem norm_le_one_of_mem_bufferedRegion {j : Fin gap212Params.n} {ε₀ ζ₁ κ : ℝ}
    (hζ₁ : 0 ≤ ζ₁) (hκ : 0 ≤ κ) {t : Fin 45 → ℝ}
    (ht : t ∈ bufferedRegion gap212Params 45 j ε₀ ζ₁ κ) : ‖t‖ ≤ 1 := by
  obtain ⟨hcube, -, -⟩ := ht
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i ↦ ?_
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [(hcube i).1], by linarith [(hcube i).2]⟩

/-- The translation `b₀` of the retreat data at `a`, at `k = 45`. -/
noncomputable def retreatShift (a : ℝ) : ℝ := a * gap212Params.δ / 4500

/-- The mollifier radius `ϱ` of the retreat data at `a`, at `k = 45`. -/
noncomputable def retreatRadius (a : ℝ) : ℝ := a * gap212Params.δ / 45000

/-- The retreat data at `a`, at `k = 45`, is
`(retreatShift a, a / 100, a * gap212Params.δ / 2, retreatRadius a)`. -/
theorem retreatData_eq (a : ℝ) : retreatData gap212Params 45 a
    = (retreatShift a, a / 100, a * gap212Params.δ / 2, retreatRadius a) := by
  norm_num [retreatData, retreatShift, retreatRadius]

/-- The retreat translation `retreatShift a` is positive for `a > 0`. -/
theorem retreatShift_pos {a : ℝ} (ha : 0 < a) : 0 < retreatShift a := by
  have := gap212Params.δ_pos
  rw [retreatShift]; positivity

/-- The retreat mollifier radius `retreatRadius a` is positive for `a > 0`. -/
theorem retreatRadius_pos {a : ℝ} (ha : 0 < a) : 0 < retreatRadius a := by
  have := gap212Params.δ_pos
  rw [retreatRadius]; positivity

/-- **The retreat of `H` at `a`**: shrink-translate by the retreat data, mollify at the retreat
radius, symmetrize. In symbols `F_a = M_{φ,ϱ}(Σ_{a,b₀}H)`, symmetrized, the symmetrization doing
the work a permutation-invariant mollifier would do. -/
noncomputable def retreatFun (H : (Fin 45 → ℝ) → ℝ) (a : ℝ) : (Fin 45 → ℝ) → ℝ :=
  symmetrize (mollify (mollKernel 45) (retreatRadius a) (shrinkTranslate a (retreatShift a) H))

section RetreatFun

variable {H : (Fin 45 → ℝ) → ℝ} {M R : ℝ}

/-- The inner (unsymmetrized) retreat is supported in the buffered region. -/
theorem support_mollify_shrinkTranslate_subset (hHT : ∀ t, t ∉ T gap212Params 45 → H t = 0)
    {a κ ζ₁ : ℝ} (ha : 0 < a) (ha' : a < 1 / 2)
    (hκ : κ = a * gap212Params.δ / (200 * 45)) (hζ₁ : ζ₁ = κ / (2 * 45))
    (j : Fin gap212Params.n) {t : Fin 45 → ℝ}
    (ht : mollify (mollKernel 45) (retreatRadius a) (shrinkTranslate a (retreatShift a) H) t ≠ 0) :
    t ∈ bufferedRegion gap212Params 45 j (a / 100) ζ₁ κ :=
  mollify_shrinkTranslate_support_subset ha ha' (retreatData_eq a) hκ hζ₁
    (support_mollKernel_subset 45) hHT j ht

/-- The retreat is supported in the buffered region. -/
theorem support_retreatFun_subset (hHT : ∀ t, t ∉ T gap212Params 45 → H t = 0)
    {a κ ζ₁ : ℝ} (ha : 0 < a) (ha' : a < 1 / 2)
    (hκ : κ = a * gap212Params.δ / (200 * 45)) (hζ₁ : ζ₁ = κ / (2 * 45))
    (j : Fin gap212Params.n) {t : Fin 45 → ℝ} (ht : retreatFun H a t ≠ 0) :
    t ∈ bufferedRegion gap212Params 45 j (a / 100) ζ₁ κ := by
  by_contra hmem
  refine ht (symmetrize_eq_zero fun σ ↦ ?_)
  by_contra hne
  exact hmem (mem_bufferedRegion_of_comp_perm σ
    (support_mollify_shrinkTranslate_subset hHT ha ha' hκ hζ₁ j hne))

/-- The retreat is symmetric. -/
theorem symmetric_retreatFun (a : ℝ) : Symmetric (retreatFun H a) :=
  symmetrize_symmetric _

/-- The retreat is non-negative. -/
theorem retreatFun_nonneg (hnn : ∀ t, 0 ≤ H t) {a : ℝ} (ha : 0 < a) (t : Fin 45 → ℝ) :
    0 ≤ retreatFun H a t :=
  symmetrize_nonneg (fun s ↦ mollify_nonneg (retreatRadius_pos ha) (fun _ ↦ hnn _) s) t

/-- The retreat is smooth. -/
theorem contDiff_retreatFun (hmeas : StronglyMeasurable H) (hM : ∀ t, |H t| ≤ M)
    (hR : ∀ t, R < ‖t‖ → H t = 0) {a : ℝ} (ha : 0 < a) (ha' : a < 1 / 2) :
    ContDiff ℝ (⊤ : ℕ∞) (retreatFun H a) :=
  contDiff_symmetrize (contDiff_mollify (retreatRadius_pos ha)
    (integrable_of_bounded_vanishing (R := R + |retreatShift a|)
      (stronglyMeasurable_shrinkTranslate hmeas _ _).aestronglyMeasurable (fun t ↦ hM _)
      (shrinkTranslate_vanishing ha (by linarith) hR)).locallyIntegrable)

end RetreatFun

section RetreatL2

variable {H : (Fin 45 → ℝ) → ℝ} {M R : ℝ}

/-- The mollification of a bounded measurable function vanishing off a ball is again bounded,
measurable and vanishing off a (larger) ball, hence square-integrable. -/
theorem memLp_mollify (hmeas : StronglyMeasurable H) (hM : ∀ t, |H t| ≤ M)
    (hR : ∀ t, R < ‖t‖ → H t = 0) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    MemLp (mollify (mollKernel 45) ϱ H) 2 (volume : Measure (Fin 45 → ℝ)) :=
  memLp_of_bounded_vanishing (R := R + ϱ) (contDiff_mollify hϱ
      (integrable_of_bounded_vanishing hmeas.aestronglyMeasurable hM hR).locallyIntegrable
    ).continuous.aestronglyMeasurable
    (fun t ↦ abs_mollify_le hϱ hM t) (mollify_vanishing hϱ hR)

/-- **The `L²` distance from the retreat to a symmetric target**, split across the mollification,
the shrink-translate, and the target. Both of the first two legs tend to `0` as `a ↓ 0`. -/
theorem l2_retreatFun_le (hmeas : StronglyMeasurable H) (hM : ∀ t, |H t| ≤ M)
    (hR : ∀ t, R < ‖t‖ → H t = 0) {u : (Fin 45 → ℝ) → ℝ} (husym : Symmetric u)
    (huL : MemLp u 2 (volume : Measure (Fin 45 → ℝ))) {a : ℝ} (ha : 0 < a) (ha' : a < 1 / 2) :
    √(∫ t : Fin 45 → ℝ, (retreatFun H a t - u t) ^ 2)
      ≤ √(∫ t : Fin 45 → ℝ,
            (mollify (mollKernel 45) (retreatRadius a / (1 - a)) H t - H t) ^ 2)
        + √(∫ t : Fin 45 → ℝ, (shrinkTranslate a (retreatShift a) H t - H t) ^ 2)
        + √(∫ t : Fin 45 → ℝ, (H t - u t) ^ 2) := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hϱ : 0 < retreatRadius a := retreatRadius_pos ha
  set S : (Fin 45 → ℝ) → ℝ := shrinkTranslate a (retreatShift a) H with hS
  set Mo : (Fin 45 → ℝ) → ℝ := mollify (mollKernel 45) (retreatRadius a) S with hMo
  -- the pieces are all square-integrable
  have hHL : MemLp H 2 (volume : Measure (Fin 45 → ℝ)) :=
    memLp_of_bounded_vanishing hmeas.aestronglyMeasurable hM hR
  have hSmeas : StronglyMeasurable S := stronglyMeasurable_shrinkTranslate hmeas _ _
  have hSM : ∀ t, |S t| ≤ M := fun t ↦ hM _
  have hSR : ∀ t, R + |retreatShift a| < ‖t‖ → S t = 0 :=
    shrinkTranslate_vanishing ha (by linarith) hR
  have hSL : MemLp S 2 (volume : Measure (Fin 45 → ℝ)) :=
    memLp_of_bounded_vanishing hSmeas.aestronglyMeasurable hSM hSR
  have hMoL : MemLp Mo 2 (volume : Measure (Fin 45 → ℝ)) := memLp_mollify hSmeas hSM hSR hϱ
  -- symmetrization does not hurt
  have hsym : √(∫ t : Fin 45 → ℝ, (retreatFun H a t - u t) ^ 2)
      ≤ √(∫ t : Fin 45 → ℝ, (Mo t - u t) ^ 2) :=
    Real.sqrt_le_sqrt (integral_sq_symmetrize_sub_le hMoL huL husym)
  -- the mollification leg, through the commutation identity
  have hleg1 : √(∫ t : Fin 45 → ℝ, (Mo t - S t) ^ 2)
      ≤ √(∫ t : Fin 45 → ℝ,
        (mollify (mollKernel 45) (retreatRadius a / (1 - a)) H t - H t) ^ 2) := by
    refine Real.sqrt_le_sqrt ?_
    rw [hMo, hS, mollify_shrinkTranslate_comm (by linarith) hϱ,
      integral_sq_shrinkTranslate (by linarith)]
    exact mul_le_of_le_one_left (integral_nonneg fun t ↦ sq_nonneg _)
      (pow_le_one₀ (by linarith) (by linarith))
  -- two triangle inequalities
  have htri1 := sqrt_integral_sub_sq_triangle (μ := (volume : Measure (Fin 45 → ℝ)))
    hMoL hSL huL
  have htri2 := sqrt_integral_sub_sq_triangle (μ := (volume : Measure (Fin 45 → ℝ)))
    hSL hHL huL
  linarith

end RetreatL2

/-- The retreat translation `retreatShift` is continuous in `a`. -/
theorem continuous_retreatShift : Continuous retreatShift := by
  unfold retreatShift; fun_prop

/-- The retreat mollifier radius `retreatRadius` is continuous in `a`. -/
theorem continuous_retreatRadius : Continuous retreatRadius := by
  unfold retreatRadius; fun_prop

/-- The retreat translation `retreatShift a` tends to `0` as `a → 0⁺`. -/
theorem tendsto_retreatShift : Tendsto retreatShift (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa [retreatShift] using (continuous_retreatShift.tendsto 0).mono_left nhdsWithin_le_nhds

/-- The rescaled radius `retreatRadius a / (1 - a)` tends to `0` as `a → 0⁺`. -/
theorem tendsto_retreatRadius_div : Tendsto (fun a : ℝ ↦ retreatRadius a / (1 - a))
    (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h : ContinuousAt (fun a : ℝ ↦ retreatRadius a / (1 - a)) 0 := by
    unfold retreatRadius; fun_prop (disch := norm_num)
  simpa [retreatRadius] using h.tendsto.mono_left nhdsWithin_le_nhds

section RetreatLegs

variable {H : (Fin 45 → ℝ) → ℝ} {M R : ℝ}

/-- The mollification leg of the retreat tends to `0`. -/
theorem tendsto_l2_retreat_mollify_leg (hmeas : StronglyMeasurable H) (hM : ∀ t, |H t| ≤ M)
    (hR : ∀ t, R < ‖t‖ → H t = 0) :
    Tendsto (fun a : ℝ ↦ √(∫ t : Fin 45 → ℝ,
        (mollify (mollKernel 45) (retreatRadius a / (1 - a)) H t - H t) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine tendsto_l2_mollify hmeas hM hR ?_ tendsto_retreatRadius_div
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with a (ha : 0 < a) ha'
  exact div_pos (retreatRadius_pos ha) (by linarith)

/-- The shrink-translate leg of the retreat tends to `0`. -/
theorem tendsto_l2_retreat_shrink_leg (hmeas : StronglyMeasurable H) (hM : ∀ t, |H t| ≤ M)
    (hR : ∀ t, R < ‖t‖ → H t = 0) :
    Tendsto (fun a : ℝ ↦ √(∫ t : Fin 45 → ℝ,
        (shrinkTranslate a (retreatShift a) H t - H t) ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_l2_shrinkTranslate hmeas hM hR tendsto_retreatShift

end RetreatLegs

/-- `√I_T` is `1`-Lipschitz in the `L²` distance. -/
theorem abs_sqrt_Iint_sub_le (p : SupportParams) {k : ℕ} {G F : (Fin k → ℝ) → ℝ}
    (hG : MemLp G 2 (volume : Measure (Fin k → ℝ)))
    (hF : MemLp F 2 (volume : Measure (Fin k → ℝ))) :
    |√(Iint p k G) - √(Iint p k F)| ≤ √(∫ t : Fin k → ℝ, (G t - F t) ^ 2) := by
  have hd : MemLp (fun t : Fin k → ℝ ↦ G t - F t) 2 (volume : Measure (Fin k → ℝ)) := by
    simpa [Pi.sub_def] using hG.sub hF
  exact (abs_sqrt_sub_sqrt_le (μ := (volume : Measure (Fin k → ℝ)).restrict (T p k))
    (hG.restrict _) (hF.restrict _)).trans <| Real.sqrt_le_sqrt
      (setIntegral_le_integral hd.integrable_sq (Eventually.of_forall fun t ↦ sq_nonneg _))

/-- **The retreat produces a fixed smooth function.** Let `F` be symmetric, square-integrable,
vanishing off `T₄₅(p⋆)`, with the variational gap at cutoff `A₁ - ε`. Then there is an
`a ∈ (0, 1/2)` and a symmetric non-negative smooth compactly supported `F₀` vanishing off the
buffered region `R⁺⁺₄₅(1, ε₀, ζ₁, κ)` of the retreat data at `a`, with the variational gap at the
retreated cutoff `(1 - ε₀)(A₁ - ε)`.

The construction: work with `|F|`, shrink-translate it, mollify, and choose `a` small. The
mollified function is *symmetrized* rather than built from a permutation-invariant kernel. The
function fed to the retreat is a non-negative smooth approximation of `|F|`, truncated to
`T₄₅(p⋆)`: bounded and compactly supported, so that the `L²` convergence of the mollifications
follows by dominated convergence. The gap is tracked through square roots, the shape of the
Lipschitz estimate `Gap212.GPY.abs_sqrt_marginalForm_sub_le`. -/
@[gap212 "lem_retreat_gap"]
theorem exists_retreat_gap {F : (Fin 45 → ℝ) → ℝ} (hFsymm : Symmetric F)
    (hF : MemLp F 2 (volume : Measure (Fin 45 → ℝ)))
    (hFoff : ∀ t, t ∉ T gap212Params 45 → F t = 0)
    (hgap : HasVariationalGap gap212Params 44
      (gap212Params.A (⟨0, gap212Params.n_pos⟩ : Fin gap212Params.n).succ - gap212Params.ε) F) :
    ∃ a b₀ ε₀ ζ ϱ κ ζ₁ : ℝ, 0 < a ∧ a < 1 / 2 ∧
      retreatData gap212Params 45 a = (b₀, ε₀, ζ, ϱ) ∧
      κ = a * gap212Params.δ / (200 * 45) ∧ ζ₁ = κ / (2 * 45) ∧
      ∃ F₀ : (Fin 45 → ℝ) → ℝ, Symmetric F₀ ∧ (∀ t, 0 ≤ F₀ t) ∧
        ContDiff ℝ (⊤ : ℕ∞) F₀ ∧ HasCompactSupport F₀ ∧
        (∀ t, F₀ t ≠ 0 →
          t ∈ bufferedRegion gap212Params 45 ⟨0, gap212Params.n_pos⟩ ε₀ ζ₁ κ) ∧
        HasVariationalGap gap212Params 44 ((1 - ε₀) *
          (gap212Params.A (⟨0, gap212Params.n_pos⟩ : Fin gap212Params.n).succ
            - gap212Params.ε)) F₀ := by
  classical
  set j₀ : Fin gap212Params.n := ⟨0, gap212Params.n_pos⟩ with hj₀
  set c : ℝ := gap212Params.A j₀.succ - gap212Params.ε with hc
  -- ## The absolute value
  set Fa : (Fin 45 → ℝ) → ℝ := fun t ↦ |F t| with hFa
  have hFaL : MemLp Fa 2 (volume : Measure (Fin 45 → ℝ)) := by
    simpa [hFa, Pi.abs_def] using hF.abs
  have hFaoff : ∀ t, t ∉ T gap212Params 45 → Fa t = 0 := fun t ht ↦ by simp [hFa, hFoff t ht]
  have hFaoff' : ∀ t : Fin 45 → ℝ, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1) → Fa t = 0 :=
    fun t ht ↦ hFaoff t fun hmem ↦ ht (mem_cornerSimplex_of_mem_T hmem)
  have hFasymm : Symmetric Fa := fun σ t ↦ by simp only [hFa, hFsymm σ t]
  have hFann : ∀ t, 0 ≤ Fa t := fun t ↦ abs_nonneg _
  have hgapA : HasVariationalGap gap212Params 44 c Fa := hasVariationalGap_abs hF hFoff hgap
  obtain ⟨hIpos, hIlt⟩ := hgapA
  set I : ℝ := Iint gap212Params 45 Fa with hI
  set J : ℝ := marginalForm c Fa with hJ
  have hIpos' : 0 < I := hIpos
  have hIlt' : I < 45 * J := hIlt.trans_eq (by norm_num)
  set A : ℝ := √I with hAdef
  set B : ℝ := √J with hBdef
  have hApos : 0 < A := Real.sqrt_pos.mpr hIpos'
  have hAB : A < √45 * B := by
    rw [hAdef, hBdef, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_lt_sqrt hIpos'.le hIlt'
  set γ : ℝ := min ((√45 * B - A) / 20) (A / 2) with hγ
  have hγpos : 0 < γ := lt_min (by linarith) (by linarith)
  have hγ20 : 20 * γ ≤ √45 * B - A := by linarith [min_le_left ((√45 * B - A) / 20) (A / 2)]
  have hγA : γ ≤ A / 2 := min_le_right _ _
  -- ## The non-negative smooth truncated approximation
  obtain ⟨v, hvsm, hvcs, hvnn, hvapprox⟩ :=
    exists_nonneg_smooth_approx hFaL hFann (ε := γ / 2) (by positivity)
  obtain ⟨Mv, Rv, hMv, hRv⟩ := exists_bound_vanishing hvsm.continuous hvcs
  set H : (Fin 45 → ℝ) → ℝ := (T gap212Params 45).indicator v with hH
  have hHmeas : StronglyMeasurable H :=
    hvsm.continuous.stronglyMeasurable.indicator (measurableSet_T gap212Params 45)
  have hHnn : ∀ t, 0 ≤ H t := Set.indicator_nonneg fun s _ ↦ hvnn s
  have hHle : ∀ t, |H t| ≤ Mv := fun t ↦ by
    by_cases ht : t ∈ T gap212Params 45 <;> simp [hH, ht, hMv t, (abs_nonneg _).trans (hMv t)]
  have hHR : ∀ t, Rv < ‖t‖ → H t = 0 := fun t ht ↦
    Set.indicator_apply_eq_zero.2 fun _ ↦ hRv t ht
  have hHT : ∀ t, t ∉ T gap212Params 45 → H t = 0 := fun t ht ↦ Set.indicator_of_notMem ht _
  have hHapprox : √(∫ t : Fin 45 → ℝ, (H t - Fa t) ^ 2) ≤ γ / 2 := by
    refine le_trans (Real.sqrt_le_sqrt ?_) hvapprox
    have hd : MemLp (fun t ↦ v t - Fa t) 2 (volume : Measure (Fin 45 → ℝ)) := by
      simpa [Pi.sub_def] using (hvsm.continuous.memLp_of_hasCompactSupport hvcs).sub hFaL
    refine integral_mono_of_nonneg (Eventually.of_forall fun t ↦ sq_nonneg _)
      hd.integrable_sq (Eventually.of_forall fun t ↦ ?_)
    by_cases htT : t ∈ T gap212Params 45 <;> simp [hH, htT, hFaoff, sq_nonneg]
  -- ## The two limits, and the choice of `a`
  have hleg1 := tendsto_l2_retreat_mollify_leg hHmeas hHle hHR
  have hleg2 := tendsto_l2_retreat_shrink_leg hHmeas hHle hHR
  have hcut : Tendsto (fun a : ℝ ↦ marginalForm ((1 - a / 100) * c) Fa) (𝓝[>] (0 : ℝ)) (𝓝 J) := by
    have hmain := tendsto_marginalForm_cutoff (σ := 1) zero_le_one c hFaL hFaoff'
    refine hmain.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
    · exact ((continuous_id.div_const 100).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
      exact Set.mem_Ioi.mpr (by positivity)
  have hScut : Tendsto (fun a : ℝ ↦ √(marginalForm ((1 - a / 100) * c) Fa))
      (𝓝[>] (0 : ℝ)) (𝓝 B) := by simpa [hBdef] using hcut.sqrt
  obtain ⟨a, ⟨ha0, ha1⟩, hlegsum, hSge⟩ : ∃ a : ℝ, (0 < a ∧ a < 1 / 2) ∧
      (√(∫ t : Fin 45 → ℝ,
          (mollify (mollKernel 45) (retreatRadius a / (1 - a)) H t - H t) ^ 2)
        + √(∫ t : Fin 45 → ℝ, (shrinkTranslate a (retreatShift a) H t - H t) ^ 2) ≤ γ / 2) ∧
      B - γ ≤ √(marginalForm ((1 - a / 100) * c) Fa) := by
    refine Eventually.exists (f := 𝓝[>] (0 : ℝ)) ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds,
      Metric.tendsto_nhds.mp hleg1 (γ / 4) (by positivity),
      Metric.tendsto_nhds.mp hleg2 (γ / 4) (by positivity),
      Metric.tendsto_nhds.mp hScut γ hγpos] with a (h0 : 0 < a) h0' h1 h2 h3
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.sqrt_nonneg _)] at h1 h2
    rw [Real.dist_eq, abs_lt] at h3
    exact ⟨⟨h0, h0'⟩, by linarith, by linarith [h3.1]⟩
  -- ## The retreat data at `a`
  set ε₀ : ℝ := a / 100 with hε₀
  set κ : ℝ := a * gap212Params.δ / (200 * 45) with hκ
  set ζ₁ : ℝ := κ / (2 * 45) with hζ₁
  have hδpos := gap212Params.δ_pos
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hζ₁pos : 0 < ζ₁ := by rw [hζ₁]; positivity
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  set F₀ : (Fin 45 → ℝ) → ℝ := retreatFun H a with hF₀
  -- ## The structural properties of `F₀`
  have hsupp : ∀ t, F₀ t ≠ 0 → t ∈ bufferedRegion gap212Params 45 j₀ ε₀ ζ₁ κ :=
    fun t ht ↦ support_retreatFun_subset hHT ha0 ha1 hκ hζ₁ j₀ ht
  have hF₀nn : ∀ t, 0 ≤ F₀ t := retreatFun_nonneg hHnn ha0
  have hF₀sm : ContDiff ℝ (⊤ : ℕ∞) F₀ := contDiff_retreatFun hHmeas hHle hHR ha0 ha1
  have hF₀sym : Symmetric F₀ := symmetric_retreatFun a
  have hF₀cs : HasCompactSupport F₀ := by
    refine HasCompactSupport.intro (isCompact_closedBall 0 1) fun t ht ↦ ?_
    by_contra hne
    exact ht (mem_closedBall_zero_iff.mpr
      (norm_le_one_of_mem_bufferedRegion hζ₁pos.le hκpos.le (hsupp t hne)))
  have hF₀L : MemLp F₀ 2 (volume : Measure (Fin 45 → ℝ)) :=
    hF₀sm.continuous.memLp_of_hasCompactSupport hF₀cs
  have hF₀off' : ∀ t : Fin 45 → ℝ, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1) → F₀ t = 0 :=
    fun t ht ↦ by_contra fun hne ↦ ht
      (mem_cornerSimplex_of_mem_bufferedRegion hε₀pos.le hζ₁pos.le hκpos.le (hsupp t hne))
  -- ## The `L²` distance from `F₀` to `|F|`
  have hD : √(∫ t : Fin 45 → ℝ, (F₀ t - Fa t) ^ 2) ≤ γ := by
    rw [hF₀]
    linarith [l2_retreatFun_le hHmeas hHle hHR hFasymm hFaL ha0 ha1]
  -- ## `I_T` and `J̃` move by at most `γ`
  have hIint : |√(Iint gap212Params 45 F₀) - A| ≤ γ :=
    (abs_sqrt_Iint_sub_le gap212Params hF₀L hFaL).trans hD
  have hMarg : |√(marginalForm ((1 - ε₀) * c) F₀) - √(marginalForm ((1 - ε₀) * c) Fa)| ≤ γ := by
    have h := abs_sqrt_marginalForm_sub_le (σ := 1) zero_le_one ((1 - ε₀) * c) hF₀L hFaL
      hF₀off' hFaoff'
    rw [Real.sqrt_one, one_mul] at h
    exact h.trans hD
  -- ## The gap survives
  obtain ⟨hpos, hfinal⟩ := gap_of_sqrt_bounds (X := Iint gap212Params 45 F₀)
    (Y := marginalForm ((1 - ε₀) * c) F₀) (integral_nonneg fun t ↦ sq_nonneg _)
    (marginalForm_nonneg _ _) hApos hγpos hγA hγ20 (by linarith [(abs_le.mp hIint).1])
    (by linarith [(abs_le.mp hIint).2]) (by linarith [(abs_le.mp hMarg).1])
  refine ⟨a, retreatShift a, ε₀, a * gap212Params.δ / 2, retreatRadius a, κ, ζ₁, ha0, ha1,
    retreatData_eq a, hκ, hζ₁, F₀, hF₀sym, hF₀nn, hF₀sm, hF₀cs, hsupp, hpos,
    hfinal.trans_eq (by norm_num)⟩


end Gap212.GPY
