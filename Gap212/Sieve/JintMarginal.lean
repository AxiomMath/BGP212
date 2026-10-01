/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.SimplexVolume
public meta import Gap212.Attr

/-!
# At a one-band datum `J_T` is the restricted marginal form

The certificate's numerator `J_T` is a double sum over pairs of bands of integrals over a region in
`(u, t, t')`. At a support datum with one band that sum has a single term, its region is symmetric
in `t` and `t'`, and the whole thing collapses to a *restricted square of a marginal* — the shape
`Gap212.GPY.marginalForm`, the only shape under which replacing `G` by `|G|` cannot decrease the
numerator.

## The two steps

* With `n = 1` the double sum defining `J_T` has the single term `j = j' = 1`; the region's first
  clause is `∑_{i<k} u_i ≤ A₁ - ε`, and its two others are the *same* condition on `∑u + t` and on
  `∑u + t'`, namely membership in `[A₀ + ε, A₁ + ε] = [0, A₁ + ε]` — the lower endpoint is `0`
  because the support datum fixes `A₀ = -ε`. Fubini in `(t, t')` then turns the integral of
  `G(u,t)G(u,t')` into the square of `∫ G(u,·)`.
* The inner range is replaced by `[0,∞)` and the outer one gains the orthant condition, both for
  the same reason: on the support of `G` every coordinate is non-negative and `∑u + t < A₁ + ε`, so
  inside the support the two descriptions agree, and outside it every integrand vanishes.

## What the support gives, and where

`Gap212.GPY.jint_eq_marginalForm` needs exactly three consequences of `G` vanishing off `T_k(p)`,
all read off the single stratum: the coordinates are non-negative, the coordinate sum is
non-negative, and the coordinate sum is `< A₁ + ε`. The first kills the points the marginal region
excludes and the negative part of the inner range; the other two kill the points the `J`-region
excludes.

## Integrability

Fubini is not free here. `(u,t,t') ↦ G(u,t)G(u,t')` is *not* a tensor product — both factors see
`u` — so its integrability is proved through `MeasureTheory.integrable_prod_iff`: each
`(t,t')`-fibre is a genuine tensor square of an integrable function, and `u ↦ (∫|G(u,t)|dt)²` is
integrable by the fibrewise Cauchy–Schwarz bound of `Gap212.Sieve.MarginalFacts`. The
measurability half needs the two coordinate maps `(u,t,t') ↦ Fin.snoc u t` and `↦ Fin.snoc u t'` to
be quasi measure preserving, which they are, being measure-preserving `Fin.snoc` after a
projection.

## Main results

* `Gap212.GPY.quasiMeasurePreserving_snocFst`, `quasiMeasurePreserving_snocSnd`: the two coordinate
  maps.
* `Gap212.GPY.jint_eq_marginalForm`: `J_T(G) = J̃_{A₁-ε}(G)` at a one-band datum.
-/

@[expose] public section

namespace Gap212.GPY

open MeasureTheory Set
open scoped Nat

/-! ### The two coordinate maps of the `J`-region -/

/-- `(u, t, t') ↦ Fin.snoc u t` is quasi measure preserving: it is the measure-preserving
`Fin.snoc` composed with the projection forgetting `t'`, and forgetting a factor of a product of
`σ`-finite measures cannot create null sets. -/
theorem quasiMeasurePreserving_snocFst (m : ℕ) :
    Measure.QuasiMeasurePreserving
      (fun q : (Fin m → ℝ) × ℝ × ℝ ↦ (Fin.snoc q.1 q.2.1 : Fin (m + 1) → ℝ))
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (ℝ × ℝ)))
      (volume : Measure (Fin (m + 1) → ℝ)) := by
  have h1 : Measure.QuasiMeasurePreserving
      (Prod.map (id : (Fin m → ℝ) → Fin m → ℝ) (Prod.fst : ℝ × ℝ → ℝ))
      ((volume : Measure (Fin m → ℝ)).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ)))
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.QuasiMeasurePreserving.id (volume : Measure (Fin m → ℝ)))
      Measure.quasiMeasurePreserving_fst
  have h2 : Measure.QuasiMeasurePreserving
      (Prod.swap : (Fin m → ℝ) × ℝ → ℝ × (Fin m → ℝ))
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving
  exact (measurePreserving_snoc m).quasiMeasurePreserving.comp (h2.comp h1)

/-- `(u, t, t') ↦ Fin.snoc u t'` is quasi measure preserving, for the same reason. -/
theorem quasiMeasurePreserving_snocSnd (m : ℕ) :
    Measure.QuasiMeasurePreserving
      (fun q : (Fin m → ℝ) × ℝ × ℝ ↦ (Fin.snoc q.1 q.2.2 : Fin (m + 1) → ℝ))
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (ℝ × ℝ)))
      (volume : Measure (Fin (m + 1) → ℝ)) := by
  have h1 : Measure.QuasiMeasurePreserving
      (Prod.map (id : (Fin m → ℝ) → Fin m → ℝ) (Prod.snd : ℝ × ℝ → ℝ))
      ((volume : Measure (Fin m → ℝ)).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ)))
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.QuasiMeasurePreserving.id (volume : Measure (Fin m → ℝ)))
      Measure.quasiMeasurePreserving_snd
  have h2 : Measure.QuasiMeasurePreserving
      (Prod.swap : (Fin m → ℝ) × ℝ → ℝ × (Fin m → ℝ))
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving
  exact (measurePreserving_snoc m).quasiMeasurePreserving.comp (h2.comp h1)

/-! ### The collapse -/

/-- **At a one-band datum `J_T` is the restricted marginal form.** For a support datum with `n = 1`
and `G` square-integrable and vanishing off `T_k(p)`, `J_T(G) = J̃_{A₁-ε}(G)`, at `k = m + 1`.

The cutoff is written `p.A (Fin.last p.n) - p.ε`, which at `n = 1` is `A₁ - ε`.

No hypothesis `k ≥ 2` is needed. -/
@[gap212 "lem_jint_marginal"]
theorem jint_eq_marginalForm {p : SupportParams} (hn : p.n = 1) {m : ℕ}
    {G : (Fin (m + 1) → ℝ) → ℝ} (hG : MemLp G 2 volume)
    (hoff : ∀ t, t ∉ T p (m + 1) → G t = 0) :
    Jint p m G = marginalForm (p.A (Fin.last p.n) - p.ε) G := by
  classical
  -- The single band, and the two endpoints of its window.
  set j₀ : Fin p.n := ⟨0, p.n_pos⟩ with hj₀
  have huniq : ∀ j : Fin p.n, j = j₀ := by
    intro j
    refine Fin.ext ?_
    have h := j.isLt
    simp only [hj₀]
    omega
  have hcastSucc : j₀.castSucc = (0 : Fin (p.n + 1)) := by
    refine Fin.ext ?_
    simp [hj₀]
  have hsuccLast : j₀.succ = Fin.last p.n := by
    refine Fin.ext ?_
    simp [hj₀, hn]
  set b : ℝ := p.A (Fin.last p.n) + p.ε with hb
  set cc : ℝ := p.A (Fin.last p.n) - p.ε with hcc
  have hlow : p.A j₀.castSucc + p.ε = 0 := by
    rw [hcastSucc, p.A_zero]
    ring
  have hupp : p.A j₀.succ + p.ε = b := by rw [hsuccLast]
  have hcut : p.A j₀.succ - p.ε = cc := by rw [hsuccLast]
  have hb0 : (0 : ℝ) ≤ b := by
    have hmono : p.A j₀.castSucc < p.A j₀.succ := p.A_mono Fin.castSucc_lt_succ
    rw [hcastSucc, p.A_zero, hsuccLast] at hmono
    rw [hb]
    linarith
  -- What the single stratum gives about the support of `G`.
  have hmemT : ∀ t : Fin (m + 1) → ℝ, t ∈ T p (m + 1) →
      (∀ i, 0 ≤ t i) ∧ 0 ≤ ∑ i, t i ∧ ∑ i, t i < b := by
    intro t ht
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
    rw [huniq j] at hj
    simp only [SupportParams.stratum, Set.mem_ofPred_eq] at hj
    obtain ⟨hcube, hsum, -⟩ := hj
    refine ⟨fun i ↦ (hcube i).1, ?_, ?_⟩
    · have h := hsum.1
      rwa [hlow] at h
    · have h := hsum.2
      rwa [hupp] at h
  have hoff' : ∀ t : Fin (m + 1) → ℝ, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ b) → G t = 0 := by
    intro t hnot
    refine hoff t fun ht ↦ hnot ?_
    obtain ⟨h1, -, h3⟩ := hmemT t ht
    exact ⟨h1, le_of_lt h3⟩
  have hGnn : ∀ t : Fin (m + 1) → ℝ, ¬(∀ i, 0 ≤ t i) → G t = 0 :=
    fun t h ↦ hoff' t fun hmem ↦ h hmem.1
  have hGb : ∀ t : Fin (m + 1) → ℝ, b < ∑ i, t i → G t = 0 :=
    fun t h ↦ hoff' t fun hmem ↦ absurd hmem.2 (not_le.mpr h)
  have hGlow : ∀ t : Fin (m + 1) → ℝ, ∑ i, t i < 0 → G t = 0 := by
    intro t h
    exact hoff t fun ht ↦ absurd (hmemT t ht).2.1 (not_le.mpr h)
  have hGsnocNeg : ∀ (u : Fin m → ℝ) (t : ℝ), ¬(∀ s, 0 ≤ u s) → G (Fin.snoc u t) = 0 := by
    intro u t h
    refine hGnn _ fun hall ↦ h fun s ↦ ?_
    have hs := hall s.castSucc
    rwa [Fin.snoc_castSucc] at hs
  have hGsnocIcc : ∀ (u : Fin m → ℝ) (t : ℝ),
      (∑ i, u i) + t ∉ Set.Icc (0 : ℝ) b → G (Fin.snoc u t) = 0 := by
    intro u t h
    rw [Set.mem_Icc, not_and_or] at h
    rcases h with h | h
    · exact hGlow _ (by rw [sum_snoc]; exact not_le.mp h)
    · exact hGb _ (by rw [sum_snoc]; exact not_le.mp h)
  have hfibNeg : ∀ (u : Fin m → ℝ) (t : ℝ), t < 0 → G (Fin.snoc u t) = 0 := by
    intro u t ht
    refine hGnn _ fun hall ↦ ?_
    have hs := hall (Fin.last m)
    rw [Fin.snoc_last] at hs
    exact absurd hs (not_le.mpr ht)
  have hG1 : Integrable G := integrable_of_vanishing hG hoff'
  -- Step 1: the double sum has a single term, and its region is the symmetric one.
  have hJ : Jint p m G
      = ∫ q in {q : (Fin m → ℝ) × ℝ × ℝ | (∑ i, q.1 i) ≤ cc ∧
          (∑ i, q.1 i) + q.2.1 ∈ Set.Icc (0 : ℝ) b ∧
          (∑ i, q.1 i) + q.2.2 ∈ Set.Icc (0 : ℝ) b},
        G (Fin.snoc q.1 q.2.1) * G (Fin.snoc q.1 q.2.2) := by
    have hregion : Jregion p m j₀ j₀
        = {q : (Fin m → ℝ) × ℝ × ℝ | (∑ i, q.1 i) ≤ cc ∧
            (∑ i, q.1 i) + q.2.1 ∈ Set.Icc (0 : ℝ) b ∧
            (∑ i, q.1 i) + q.2.2 ∈ Set.Icc (0 : ℝ) b} := by
      simp only [Jregion, max_self, hlow, hupp, hcut]
    simp only [Jint]
    rw [Finset.sum_eq_single_of_mem j₀ (Finset.mem_univ _)
      fun j _ hj ↦ absurd (huniq j) hj,
      Finset.sum_eq_single_of_mem j₀ (Finset.mem_univ _)
        fun j _ hj ↦ absurd (huniq j) hj, hregion]
  -- Step 2: the region may be replaced by the orthant slab, both integrands vanishing elsewhere.
  have hsumMeas : Measurable fun q : (Fin m → ℝ) × ℝ × ℝ ↦ ∑ i, q.1 i :=
    Finset.measurable_sum _ fun i _ ↦ (measurable_pi_apply i).comp measurable_fst
  have hSMeas : MeasurableSet {q : (Fin m → ℝ) × ℝ × ℝ | (∑ i, q.1 i) ≤ cc ∧
      (∑ i, q.1 i) + q.2.1 ∈ Set.Icc (0 : ℝ) b ∧
      (∑ i, q.1 i) + q.2.2 ∈ Set.Icc (0 : ℝ) b} := by
    rw [Set.ofPred_and, Set.ofPred_and]
    refine (measurableSet_le hsumMeas measurable_const).inter (MeasurableSet.inter ?_ ?_)
    · exact (hsumMeas.add (measurable_fst.comp measurable_snd)) measurableSet_Icc
    · exact (hsumMeas.add (measurable_snd.comp measurable_snd)) measurableSet_Icc
  have hWMeas : MeasurableSet
      ({u : Fin m → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ cc} ×ˢ (Set.univ : Set (ℝ × ℝ))) :=
    (measurableSet_cornerSimplex m cc).prod MeasurableSet.univ
  have hswap : (∫ q in {q : (Fin m → ℝ) × ℝ × ℝ | (∑ i, q.1 i) ≤ cc ∧
        (∑ i, q.1 i) + q.2.1 ∈ Set.Icc (0 : ℝ) b ∧
        (∑ i, q.1 i) + q.2.2 ∈ Set.Icc (0 : ℝ) b},
        G (Fin.snoc q.1 q.2.1) * G (Fin.snoc q.1 q.2.2))
      = ∫ q in {u : Fin m → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ cc} ×ˢ
          (Set.univ : Set (ℝ × ℝ)), G (Fin.snoc q.1 q.2.1) * G (Fin.snoc q.1 q.2.2) := by
    rw [← integral_indicator hSMeas, ← integral_indicator hWMeas]
    congr 1
    funext q
    by_cases h1 : q ∈ {q : (Fin m → ℝ) × ℝ × ℝ | (∑ i, q.1 i) ≤ cc ∧
        (∑ i, q.1 i) + q.2.1 ∈ Set.Icc (0 : ℝ) b ∧
        (∑ i, q.1 i) + q.2.2 ∈ Set.Icc (0 : ℝ) b} <;>
      by_cases h2 : q ∈ {u : Fin m → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ cc} ×ˢ
        (Set.univ : Set (ℝ × ℝ))
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    · -- in the `J`-region but off the orthant: some `u_s` is negative
      rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
      have hneg : ¬ ∀ s, 0 ≤ q.1 s := by
        intro hall
        exact h2 (Set.mk_mem_prod ⟨hall, h1.1⟩ (Set.mem_univ _))
      rw [hGsnocNeg q.1 q.2.1 hneg, zero_mul]
    · -- on the orthant but outside the `J`-region: one of the two windows fails
      rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2]
      obtain ⟨h0, hle⟩ := (Set.mem_prod.mp h2).1
      by_cases hw1 : (∑ i, q.1 i) + q.2.1 ∈ Set.Icc (0 : ℝ) b
      · by_cases hw2 : (∑ i, q.1 i) + q.2.2 ∈ Set.Icc (0 : ℝ) b
        · exact absurd ⟨hle, hw1, hw2⟩ h1
        · rw [hGsnocIcc q.1 q.2.2 hw2, mul_zero]
      · rw [hGsnocIcc q.1 q.2.1 hw1, zero_mul]
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  -- Step 3: integrability of the product, through the fibrewise tensor square.
  have hmeasf : AEStronglyMeasurable
      (fun q : (Fin m → ℝ) × ℝ × ℝ ↦ G (Fin.snoc q.1 q.2.1) * G (Fin.snoc q.1 q.2.2))
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (ℝ × ℝ))) :=
    (hG.aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_snocFst m)).mul
      (hG.aestronglyMeasurable.comp_quasiMeasurePreserving (quasiMeasurePreserving_snocSnd m))
  have hprodMeasure : (volume : Measure (ℝ × ℝ))
      = (volume : Measure ℝ).prod (volume : Measure ℝ) := Measure.volume_eq_prod ℝ ℝ
  have habsLp : MemLp (fun t ↦ |G t|) 2 (volume : Measure (Fin (m + 1) → ℝ)) := hG.abs
  have hoffabs : ∀ t : Fin (m + 1) → ℝ,
      ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ b) → (fun t ↦ |G t|) t = 0 := by
    intro t hnot
    simp only [hoff' t hnot, abs_zero]
  have hmargEq : ∀ u : Fin m → ℝ,
      (∫ t, G (Fin.snoc u t)) = ∫ t in Set.Ioi (0 : ℝ), G (Fin.snoc u t) :=
    fun u ↦ (setIntegral_Ioi_eq_integral fun t ht ↦ hfibNeg u t ht).symm
  have hmargAbsEq : ∀ u : Fin m → ℝ,
      (∫ t, |G (Fin.snoc u t)|) = ∫ t in Set.Ioi (0 : ℝ), |G (Fin.snoc u t)| :=
    fun u ↦ (setIntegral_Ioi_eq_integral fun t ht ↦ by
      rw [hfibNeg u t ht, abs_zero]).symm
  have hIntf : Integrable
      (fun q : (Fin m → ℝ) × ℝ × ℝ ↦ G (Fin.snoc q.1 q.2.1) * G (Fin.snoc q.1 q.2.2))
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (ℝ × ℝ))) := by
    rw [integrable_prod_iff hmeasf]
    refine ⟨?_, ?_⟩
    · filter_upwards [(integrable_comp_snoc hG1).prod_left_ae] with u hu
      rw [hprodMeasure]
      exact hu.mul_prod hu
    · have hnormeq : ∀ u : Fin m → ℝ,
          (∫ y : ℝ × ℝ, ‖G (Fin.snoc u y.1) * G (Fin.snoc u y.2)‖)
            = (∫ t, |G (Fin.snoc u t)|) ^ 2 := by
        intro u
        rw [hprodMeasure, integral_congr_ae (Filter.Eventually.of_forall
          fun y : ℝ × ℝ ↦ by rw [Real.norm_eq_abs, abs_mul]),
          integral_prod_mul (fun t ↦ |G (Fin.snoc u t)|) fun t ↦ |G (Fin.snoc u t)|, sq]
      simp only [hnormeq]
      obtain ⟨hsqint, -⟩ := integral_fibre_sq habsLp hoffabs
      refine Integrable.mono' (hsqint.const_mul b) ?_ ?_
      · exact (((integrable_comp_snoc hG1.abs).integral_prod_right).aestronglyMeasurable).pow 2
      · filter_upwards [sq_marginal_le_ae hb0 habsLp hoffabs] with u hu
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hmargAbsEq u]
        exact hu
  -- Step 4: Fubini in `(t, t')`, and the inner square.
  rw [hJ, hswap, marginalForm]
  rw [show (volume : Measure ((Fin m → ℝ) × ℝ × ℝ))
      = (volume : Measure (Fin m → ℝ)).prod (volume : Measure (ℝ × ℝ)) from
    Measure.volume_eq_prod _ _]
  rw [setIntegral_prod _ hIntf.integrableOn]
  refine setIntegral_congr_fun (measurableSet_cornerSimplex m cc) fun u _ ↦ ?_
  rw [setIntegral_univ, hprodMeasure,
    integral_prod_mul (fun t ↦ G (Fin.snoc u t)) fun t ↦ G (Fin.snoc u t), ← sq, hmargEq u]

end Gap212.GPY
