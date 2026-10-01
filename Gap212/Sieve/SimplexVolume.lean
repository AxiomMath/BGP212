/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MarginalFacts
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public meta import Gap212.Attr

/-!
# The volume of a corner simplex

The Lebesgue measure of `{u ∈ [0,∞)^n : ∑ uᵢ ≤ σ}` is `σ^n / n!`, and the measure of the strip
between two such simplices is at most `(c - d) c^{n-1} / (n-1)!`.

## Implementation notes

Mathlib's `stdSimplex` is the probability simplex `{x ≥ 0 : ∑ xᵢ = 1}`, of measure zero in `ℝ^n`,
and `MeasureTheory.volume_sum_rpow_le` gives the volume of the `ℓ^p` ball, whose `p = 1` instance
is the cross-polytope. The corner simplex is neither, so its volume is proved here by induction on
the dimension and Fubini in the last coordinate.

## The strip

The thin-strip estimate `Gap212.GPY.setIntegral_tensorMarginalHigh_sq_le` integrates over
`{u ≥ 0 : d ≤ ∑ uᵢ ≤ c}` — a *closed* strip. That is not the set difference of the two closed
simplices: the two overlap in the hyperplane `∑ uᵢ = d`. The overlap is Lebesgue-null, but that is
a fact needing proof, and `Gap212.GPY.volume_sum_eq_const` is it: Fubini in the last coordinate
turns each fibre into a single point.

## Main results

* `Gap212.GPY.volume_cornerSimplex`: `vol {u ≥ 0 : ∑ uᵢ ≤ σ} = σ^n / n!` for `σ ≥ 0`.
* `Gap212.GPY.volume_sum_eq_const`: a level set of the coordinate sum is null (in dimension `≥ 1`).
* `Gap212.GPY.volumeReal_strip_le`: `vol {u ≥ 0 : d ≤ ∑ uᵢ ≤ c} ≤ (c - d) c^n / n!` in dimension
  `n + 1`.
-/

@[expose] public section

namespace Gap212.GPY

open MeasureTheory Set
open scoped Nat

/-! ### The corner simplex as a measurable set -/

/-- The corner simplex `{u ≥ 0 : ∑ uᵢ ≤ σ}` is measurable: a countable intersection of half-spaces
intersected with one more. -/
theorem measurableSet_cornerSimplex (n : ℕ) (σ : ℝ) :
    MeasurableSet {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ σ} := by
  rw [Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.iInter fun i ↦
    measurableSet_le measurable_const (measurable_pi_apply i)).inter
      (measurableSet_le (by fun_prop) measurable_const)

/-- Below the origin the corner simplex is empty: a non-negative vector has a non-negative
coordinate sum. -/
theorem cornerSimplex_eq_empty (n : ℕ) {σ : ℝ} (hσ : σ < 0) :
    {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ σ} = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun u ⟨h0, h⟩ ↦ ?_
  linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ h0 i]

/-! ### Splitting off the last coordinate -/

/-- Non-negativity of `Fin.snoc u t` splits into non-negativity of `u` and of `t`. -/
theorem forall_nonneg_snoc {n : ℕ} (t : ℝ) (u : Fin n → ℝ) :
    (∀ i, 0 ≤ (Fin.snoc u t : Fin (n + 1) → ℝ) i) ↔ (∀ i, 0 ≤ u i) ∧ 0 ≤ t := by
  simp [Fin.forall_fin_succ']

/-- The coordinate sum of `Fin.snoc u t`. -/
theorem sum_snoc {n : ℕ} (t : ℝ) (u : Fin n → ℝ) :
    ∑ i, (Fin.snoc u t : Fin (n + 1) → ℝ) i = (∑ i, u i) + t := by
  simp [Fin.sum_univ_castSucc]

/-! ### The volume -/

/-- **The volume of a corner simplex**: `vol {u ∈ [0,∞)^n : ∑ uᵢ ≤ σ} = σ^n / n!`.

By induction on `n` with Fubini in the last coordinate: the fibre over `t ∈ [0, σ]` is the corner
simplex of `ℝ^{n-1}` at `σ - t`, the fibres over `t < 0` and `t > σ` are empty, and
`∫_0^σ (σ-t)^{n-1}/(n-1)! dt` is `σ^n/n!`. -/
theorem volume_cornerSimplex (n : ℕ) : ∀ σ : ℝ, 0 ≤ σ →
    volume {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ σ}
      = ENNReal.ofReal (σ ^ n / (n ! : ℝ)) := by
  induction n with
  | zero =>
    intro σ hσ
    simp [hσ, volume_pi]
  | succ n ih =>
    intro σ hσ
    set T : Set (Fin (n + 1) → ℝ) := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ σ} with hT
    set Φ : ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun q ↦ Fin.snoc q.2 q.1 with hΦ
    have hTm : MeasurableSet T := measurableSet_cornerSimplex _ _
    -- The preimage of the simplex under the splitting.
    have hpre : Φ ⁻¹' T
        = {q : ℝ × (Fin n → ℝ) | 0 ≤ q.1 ∧ (∀ i, 0 ≤ q.2 i) ∧ ∑ i, q.2 i ≤ σ - q.1} := by
      ext q
      simp only [hΦ, hT, Set.mem_preimage, Set.mem_ofPred_eq, forall_nonneg_snoc, sum_snoc,
        le_sub_iff_add_le]
      tauto
    have hprem : MeasurableSet (Φ ⁻¹' T) := (measurableEmbedding_snoc n).measurable hTm
    -- Fubini: the volume is the integral of the fibre volumes.
    rw [← (measurePreserving_snoc n).measure_preimage hTm.nullMeasurableSet,
      Measure.prod_apply hprem]
    -- Each fibre volume, by the inductive hypothesis.
    have hfib : (fun t : ℝ ↦ (volume : Measure (Fin n → ℝ)) (Prod.mk t ⁻¹' (Φ ⁻¹' T)))
        = (Set.Icc 0 σ).indicator fun t ↦ ENNReal.ofReal ((σ - t) ^ n / (n ! : ℝ)) := by
      funext t
      by_cases ht0 : 0 ≤ t
      · have hslice : Prod.mk t ⁻¹' (Φ ⁻¹' T)
            = {u : Fin n → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ σ - t} := by
          ext u; simp [hpre, ht0]
        rw [hslice]
        by_cases htσ : t ≤ σ
        · rw [Set.indicator_of_mem (mem_Icc.2 ⟨ht0, htσ⟩), ih (σ - t) (by linarith)]
        · rw [Set.indicator_of_notMem (by simp [htσ]), cornerSimplex_eq_empty n (by linarith),
            measure_empty]
      · have hempty : Prod.mk t ⁻¹' (Φ ⁻¹' T) = ∅ := by ext u; simp [hpre, ht0]
        rw [Set.indicator_of_notMem (by simp [ht0]), hempty, measure_empty]
    rw [hfib, lintegral_indicator measurableSet_Icc]
    -- The remaining one-dimensional integral.
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc 0 σ)] fun t : ℝ ↦ (σ - t) ^ n / (n ! : ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have : 0 ≤ σ - t := by linarith [ht.2]
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal (Continuous.integrableOn_Icc (by fun_prop)) hnn]
    congr 1
    -- `∫_0^σ (σ-t)^n dt = σ^{n+1}/(n+1)`, and dividing by `n!` gives `σ^{n+1}/(n+1)!`.
    rw [integral_div, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hσ,
      intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ n) σ]
    simp only [sub_self, sub_zero, integral_pow, Nat.factorial_succ, zero_pow n.succ_ne_zero]
    push_cast
    field_simp

/-! ### The level sets of the coordinate sum are null -/

/-- **A level set of the coordinate sum is Lebesgue-null**, in dimension at least one: Fubini in
the last coordinate makes every fibre a single point.

This is what lets the closed strip below be compared with a difference of closed simplices — the
two closed simplices overlap exactly in such a level set. -/
theorem volume_sum_eq_const (n : ℕ) (σ : ℝ) :
    volume {u : Fin (n + 1) → ℝ | ∑ i, u i = σ} = 0 := by
  set T : Set (Fin (n + 1) → ℝ) := {u | ∑ i, u i = σ} with hT
  set Φ : ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun q ↦ Fin.snoc q.2 q.1 with hΦ
  have hTm : MeasurableSet T := measurableSet_eq_fun (by fun_prop) measurable_const
  have hprem : MeasurableSet (Φ ⁻¹' T) := (measurableEmbedding_snoc n).measurable hTm
  rw [← (measurePreserving_snoc n).measure_preimage hTm.nullMeasurableSet,
    Measure.prod_apply_symm hprem]
  refine (lintegral_eq_zero_iff (measurable_measure_prodMk_right hprem)).mpr ?_
  filter_upwards with u
  have hsing : (fun t : ℝ ↦ (t, u)) ⁻¹' (Φ ⁻¹' T) = {σ - ∑ i, u i} := by
    ext t
    simp only [hΦ, hT, Set.mem_preimage, Set.mem_ofPred_eq, sum_snoc, Set.mem_singleton_iff,
      eq_sub_iff_add_eq']
  simp [hsing]

/-! ### The strip between two corner simplices -/

/-- `c^{n+1} - d^{n+1} ≤ (n+1)(c-d)c^n` for `0 ≤ d ≤ c`: convexity of `x ↦ x^{n+1}`, proved by
induction on `n`. -/
theorem pow_succ_sub_pow_succ_le (n : ℕ) {c d : ℝ} (hd : 0 ≤ d) (hdc : d ≤ c) :
    c ^ (n + 1) - d ^ (n + 1) ≤ ((n : ℝ) + 1) * (c - d) * c ^ n := by
  have hc : (0 : ℝ) ≤ c := le_trans hd hdc
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    linear_combination mul_le_mul_of_nonneg_left ih hc +
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd hdc (n + 1)) (sub_nonneg.mpr hdc)

/-- **The volume of the closed strip** `{u ≥ 0 : d ≤ ∑ uᵢ ≤ c}` in dimension `n + 1` is at most
`(c - d) c^n / n!`.

The strip is contained in the difference of the two closed corner simplices together with the level
set `∑ uᵢ = d`, which is null by `Gap212.GPY.volume_sum_eq_const`; the difference has volume
`(c^{n+1} - d^{n+1})/(n+1)!`, and `c^{n+1} - d^{n+1} ≤ (n+1)(c-d)c^n`. -/
theorem volumeReal_strip_le (n : ℕ) {c d : ℝ} (hd : 0 ≤ d) (hdc : d ≤ c) :
    volume.real {u : Fin (n + 1) → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c ∧ d ≤ ∑ i, u i}
      ≤ (c - d) * c ^ n / (n ! : ℝ) := by
  have hc : (0 : ℝ) ≤ c := le_trans hd hdc
  have hfac : (0 : ℝ) < (n ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hbound : (0 : ℝ) ≤ (c - d) * c ^ n / (n ! : ℝ) := by
    have := sub_nonneg.mpr hdc
    positivity
  refine ENNReal.toReal_le_of_le_ofReal hbound ?_
  -- The strip sits inside the set difference together with the boundary level set.
  have hsub : {u : Fin (n + 1) → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c ∧ d ≤ ∑ i, u i}
      ⊆ ({u : Fin (n + 1) → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c}
          \ {u : Fin (n + 1) → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ d})
        ∪ {u : Fin (n + 1) → ℝ | ∑ i, u i = d} := by
    rintro u ⟨h0, hle, hge⟩
    by_cases hd' : ∑ i, u i ≤ d
    · exact Or.inr (le_antisymm hd' hge)
    · exact Or.inl ⟨⟨h0, hle⟩, fun h ↦ hd' h.2⟩
  have hdiff : volume ({u : Fin (n + 1) → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c}
      \ {u : Fin (n + 1) → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ d})
      = ENNReal.ofReal ((c ^ (n + 1) - d ^ (n + 1)) / (((n + 1)! : ℕ) : ℝ)) := by
    have hincl : {u : Fin (n + 1) → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ d}
        ⊆ {u : Fin (n + 1) → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c} :=
      fun u hu ↦ ⟨hu.1, le_trans hu.2 hdc⟩
    rw [measure_sdiff hincl (measurableSet_cornerSimplex _ _).nullMeasurableSet
      (by rw [volume_cornerSimplex (n + 1) d hd]; exact ENNReal.ofReal_ne_top),
      volume_cornerSimplex (n + 1) c hc, volume_cornerSimplex (n + 1) d hd,
      ← ENNReal.ofReal_sub _ (by positivity), sub_div]
  calc volume {u : Fin (n + 1) → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c ∧ d ≤ ∑ i, u i}
      ≤ volume (({u : Fin (n + 1) → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c}
          \ {u : Fin (n + 1) → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ d})
        ∪ {u : Fin (n + 1) → ℝ | ∑ i, u i = d}) := measure_mono hsub
    _ ≤ volume ({u : Fin (n + 1) → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c}
          \ {u : Fin (n + 1) → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ d})
        + volume {u : Fin (n + 1) → ℝ | ∑ i, u i = d} := measure_union_le _ _
    _ = ENNReal.ofReal ((c ^ (n + 1) - d ^ (n + 1)) / (((n + 1)! : ℕ) : ℝ)) := by
        rw [hdiff, volume_sum_eq_const n d, add_zero]
    _ ≤ ENNReal.ofReal ((c - d) * c ^ n / (n ! : ℝ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Nat.factorial_succ, Nat.cast_mul, div_le_div_iff₀ (by positivity) hfac]
        push_cast
        linarith [mul_le_mul_of_nonneg_right (pow_succ_sub_pow_succ_le n hd hdc) hfac.le]

end Gap212.GPY
