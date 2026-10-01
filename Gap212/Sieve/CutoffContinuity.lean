/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.SimplexVolume
public meta import Gap212.Attr

/-!
# Moving the marginal cutoff inward converges

The retreat step picks its function `F₀` against the cutoff `c` and then runs the sieve at the
*retreated* cutoff `(1 - ε₀)c`. Nothing survives that move unless the marginal form is continuous
in the cutoff from the inside, which is what this file proves:
`J̃_{(1-ε₀)c}(G) → J̃_c(G)` as `ε₀ ↓ 0`.

## The convergence idiom

`Filter.Tendsto (fun ε₀ ↦ marginalForm ((1 - ε₀) * c) G) (𝓝[>] 0) (𝓝 (marginalForm c G))` —
Mathlib's one-sided limit, `𝓝[>] 0` being `nhdsWithin 0 (Set.Ioi 0)`. Read through
`Metric.tendsto_nhdsWithin_nhds`, it says that for all small positive `ε₀` the retreated form is
within `η` of the limit.

## The measure-theoretic route

Dominated convergence against the *global* dominating function
`g(u) = (∫_{t>0} G(u,t) dt)²`, not the quantitative strip bound.

`marginalForm a G` is `∫ u, 1_{S a} · g` for the corner simplex `S a = {u ≥ 0 : ∑ uᵢ ≤ a}`, and `g`
is integrable on the whole of `ℝ^{k-1}` by `Gap212.GPY.memLp_marginal` — the fibrewise
Cauchy–Schwarz bound behind `Gap212.GPY.abs_sqrt_marginalForm_sub_le`. So `g` itself dominates
every
`1_{S a} · g`, with no need to compare the regions, and the only remaining point is pointwise
convergence of the indicators. That holds off the hyperplane `∑ uᵢ = c`: at a point of the open
simplex `(1 - ε₀)c` eventually exceeds `∑ uᵢ`, and outside the closed one it eventually does not,
so in both cases the indicator is *eventually constant* along `𝓝[>] 0`. The hyperplane is
Lebesgue-null by `Gap212.GPY.volume_sum_eq_const`.

The quantitative alternative — bound the strip's measure by `Gap212.GPY.volumeReal_strip_le` and
read off an `O(ε₀)` rate — would need `g` bounded above, while square integrability of `G` gives
only `g ∈ L¹`: the fibre bound is `g(u) ≤ Σ ∫ G(u,t)² dt`, whose right side is integrable in `u`
but not bounded.

## Main results

* `Gap212.GPY.marginalForm_eq_integral_indicator`: the marginal form as an integral over the whole
  space of an indicator.
* `Gap212.GPY.tendsto_marginalForm_cutoff`: the convergence.
-/

@[expose] public section

namespace Gap212.GPY

open MeasureTheory Set Filter Topology

/-- The marginal form is the integral over all of `ℝ^{k-1}` of the squared marginal cut off by the
indicator of the corner simplex. This is the shape dominated convergence is applied in: the domain
of integration is fixed and the cutoff sits in the integrand. -/
theorem marginalForm_eq_integral_indicator {m : ℕ} (c : ℝ) (G : (Fin (m + 1) → ℝ) → ℝ) :
    marginalForm c G = ∫ u : Fin m → ℝ,
      {u : Fin m → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c}.indicator
        (fun u ↦ (∫ t in Set.Ioi (0 : ℝ), G (Fin.snoc u t)) ^ 2) u :=
  (integral_indicator (measurableSet_cornerSimplex m c)).symm

/-- The cutoff map `ε₀ ↦ (1 - ε₀)c` tends to `c` as `ε₀ ↓ 0`. -/
theorem tendsto_one_sub_mul (c : ℝ) :
    Tendsto (fun ε₀ : ℝ ↦ (1 - ε₀) * c) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  have h : Tendsto (fun ε₀ : ℝ ↦ (1 - ε₀) * c) (𝓝 (0 : ℝ)) (𝓝 ((1 - 0) * c)) :=
    ((continuous_const.sub continuous_id).mul continuous_const).tendsto 0
  simpa using h.mono_left nhdsWithin_le_nhds

/-- The indicator of the corner simplex at the retreated cutoff converges pointwise to the
indicator at the cutoff itself, off the hyperplane `∑ uᵢ = c`.

Off that hyperplane the indicator is *eventually constant* in `ε₀`, which is why no continuity of
the integrand is needed: either the point is outside the orthant (both indicators vanish
identically), or it is strictly inside the simplex (and `(1 - ε₀)c` eventually exceeds its mass),
or strictly outside (and `(1 - ε₀)c` eventually does not). -/
theorem tendsto_indicator_cornerSimplex {m : ℕ} {c : ℝ} (f : (Fin m → ℝ) → ℝ) {u : Fin m → ℝ}
    (hu : ∑ i, u i ≠ c) :
    Tendsto (fun ε₀ : ℝ ↦ {v : Fin m → ℝ | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ (1 - ε₀) * c}.indicator
        f u) (𝓝[>] (0 : ℝ))
      (𝓝 ({v : Fin m → ℝ | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ c}.indicator f u)) := by
  set S : ℝ → Set (Fin m → ℝ) := fun a ↦ {v : Fin m → ℝ | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ a} with hS
  have hmem : ∀ a : ℝ, u ∈ S a ↔ (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ a := fun a ↦ by
    simp [hS]
  by_cases h0 : ∀ i, 0 ≤ u i
  · rcases hu.lt_or_gt with hlt | hgt
    · rw [Set.indicator_of_mem ((hmem c).mpr ⟨h0, hlt.le⟩)]
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [(tendsto_one_sub_mul c).eventually (eventually_gt_nhds hlt)] with ε₀ hε
      exact (Set.indicator_of_mem ((hmem _).mpr ⟨h0, hε.le⟩) f).symm
    · rw [Set.indicator_of_notMem (fun h ↦ absurd ((hmem c).mp h).2 (not_le.mpr hgt))]
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [(tendsto_one_sub_mul c).eventually (eventually_lt_nhds hgt)] with ε₀ hε
      exact (Set.indicator_of_notMem (fun h ↦ absurd ((hmem _).mp h).2 (not_le.mpr hε)) f).symm
  · rw [Set.indicator_of_notMem (fun h ↦ h0 ((hmem c).mp h).1)]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with ε₀
    exact (Set.indicator_of_notMem (fun h ↦ h0 ((hmem _).mp h).1) f).symm

/-- **Moving the cutoff inward converges.** For `G` square-integrable and vanishing off the part of
the closed orthant of total mass at most `σ`, `J̃_{(1-ε₀)c}(G) → J̃_c(G)` as `ε₀ ↓ 0`.

The proof is dominated convergence, with the squared marginal itself as dominating function.
Only `σ ≥ 0` is assumed (the fibre bound `Gap212.GPY.sq_marginal_le_ae` asks only that), and no
sign of `c`: the dominating function does not depend on the cutoff.

The dimension is `k = n + 2 ≥ 2`, so that the outer integral is over `ℝ^{n+1}`, the dimension range
of `Gap212.GPY.volume_sum_eq_const`. -/
@[gap212 "lem_marginal_cutoff_continuity"]
theorem tendsto_marginalForm_cutoff {n : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) (c : ℝ)
    {G : (Fin (n + 2) → ℝ) → ℝ} (hG : MemLp G 2 volume)
    (hoff : ∀ t, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ σ) → G t = 0) :
    Tendsto (fun ε₀ : ℝ ↦ marginalForm ((1 - ε₀) * c) G) (𝓝[>] (0 : ℝ))
      (𝓝 (marginalForm c G)) := by
  set g : (Fin (n + 1) → ℝ) → ℝ :=
    fun u ↦ (∫ t in Set.Ioi (0 : ℝ), G (Fin.snoc u t)) ^ 2 with hg
  have hgint : Integrable g (volume : Measure (Fin (n + 1) → ℝ)) :=
    (memLp_marginal hσ hG hoff).integrable_sq
  -- The cutoff hyperplane is null, which is the only place the indicators fail to converge.
  have hnull : ∀ᵐ u : Fin (n + 1) → ℝ ∂(volume : Measure (Fin (n + 1) → ℝ)), ∑ i, u i ≠ c := by
    have hcompl : {u : Fin (n + 1) → ℝ | ∑ i, u i ≠ c}ᶜ
        = {u : Fin (n + 1) → ℝ | ∑ i, u i = c} := by
      ext u; simp
    rw [Filter.eventually_iff, mem_ae_iff, hcompl]
    exact volume_sum_eq_const n c
  simp only [marginalForm_eq_integral_indicator, ← hg]
  refine tendsto_integral_filter_of_dominated_convergence g
    (Filter.Eventually.of_forall fun ε₀ ↦
      hgint.aestronglyMeasurable.indicator (measurableSet_cornerSimplex (n + 1) _))
    (Filter.Eventually.of_forall fun ε₀ ↦ Filter.Eventually.of_forall fun u ↦ ?_)
    hgint ?_
  · calc ‖{v : Fin (n + 1) → ℝ | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ (1 - ε₀) * c}.indicator g u‖
        ≤ ‖g u‖ := norm_indicator_le_norm_self _ _
      _ = g u := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  · filter_upwards [hnull] with u hu
    exact tendsto_indicator_cornerSimplex g hu

end Gap212.GPY
