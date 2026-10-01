/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.TypeIIc
public meta import Gap212.Attr

/-!
# Condition (D), completely: the branch where a rough factor exceeds the reserve

`Gap212.Packing.conditionD_of_all_le_W` closes the branch in which every rough factor fits inside
the reserve `W`. This module closes the other one, and hence condition (D) itself.

## The shape of the argument

The greedy engine `exists_subset_sum_mem_Icc` needs a uniform upper bound on the entries it is
given. So rather than feeding it the whole tuple, feed it only the **small** factors, those with
`yᵢ ≤ W`. If they already carry the deficit `D`, the engine returns a subset with sum in
`[D, D + W]`, and `c₂ - D = W` finishes it exactly as before.

Everything else shows that the remaining case — the small factors *not* carrying `D` — cannot
happen. That is where the four exact rational inequalities are used, one per step of the case
analysis:

* `packing_ineq₃` (`2B₁,₂ ≤ c₁ᵐⁱⁿ`) — if both sides carry at most two factors the total mass is at
  most `2 × 31/200 = 0.31`, already under `c₁`, so `D ≤ 0` and there is nothing to do. Hence **some
  side carries at least three factors.**
* `packing_ineq₂` (`3Wᵐⁱⁿ > 17/100`) — three factors each exceeding `W` would exceed any side's
  rough cap. Hence **every side with three or more factors contains a small factor.**
* `packing_ineq₄` (`B₁,₃ + B₁,₂ - c₁ᵐⁱⁿ < δ`) — if exactly one side carries three or more, the mass
  is at most `0.17 + 0.155`, so `D < δ`. But a single small factor already has mass `≥ δ`, so the
  small factors carry `D` after all.
* `packing_ineq₁` (`17/50 - c₁ᵐⁱⁿ < 2δ`) — in general `D < 2δ`, so at most **one** small factor can
  fail to carry `D`. When both sides carry three or more, each contributes a small factor, giving
  two — a contradiction.

## Implementation notes

The case analysis is organized around which factors are small, using the minimal-cardinality
subset — the same tool that proves the extraction lemmas — rather than an incremental greedy and
its last transferred factor. In particular the bound `D ≤ B₁,₃ + B₁,₂ - c₁ᵐⁱⁿ < δ` is available
only when the two rough caps are the *mixed* pair. When both sides carry three or more factors the
bound is `2B₁,₃ - c₁ᵐⁱⁿ ≈ 0.0278`, which exceeds `δ`, and that case is closed instead by the
counting argument via `packing_ineq₂`.

## Main results

* `Gap212.Packing.card_sideOne`, `card_sideTwo`: the pooled tuple's two groups have sizes `m`,
  `m'`.
* `Gap212.Packing.three_gt_reserve_sum_lb`: three factors above `W` sum to more than `3W`.
* `Gap212.Packing.exists_small_of_three`: a side with three or more factors has a small one.
* `Gap212.Packing.conditionD`: condition (D), all branches.
-/

@[expose] public section

namespace Gap212.Packing

open Finset Gap212.PointA

/-! ## The two sides of a pooled tuple

`Ξ` caps the first `m` coordinates and the last `m'` separately. The two index groups are named
here so the cap case analysis can talk about their sizes. -/

variable {m m' : ℕ}

/-- The indices of the unprimed side of a pooled tuple. -/
def sideOne (m m' : ℕ) : Finset (Fin (m + m')) := {i | (i : ℕ) < m}

/-- The indices of the primed side. -/
def sideTwo (m m' : ℕ) : Finset (Fin (m + m')) := {i | ¬ ((i : ℕ) < m)}

/-- The unprimed side has `m` coordinates. -/
theorem card_sideOne (m m' : ℕ) : (sideOne m m').card = m := by
  rw [sideOne, card_filter, Fin.sum_univ_add]
  simp

/-- The primed side has `m'` coordinates. -/
theorem card_sideTwo (m m' : ℕ) : (sideTwo m m').card = m' := by
  rw [sideTwo, card_filter, Fin.sum_univ_add]
  simp

/-- The two sides are disjoint. -/
theorem sideOne_disjoint_sideTwo (m m' : ℕ) : Disjoint (sideOne m m') (sideTwo m m') :=
  disjoint_filter_filter_not _ _ _

section Field

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [IsStrictOrderedRing 𝕜] in
/-- The unprimed side's mass is capped by `B₁`. -/
theorem sum_sideOne_le {B₁ B₂ d : 𝕜} {y : Fin (m + m') → 𝕜} (hy : y ∈ Xi B₁ B₂ m m' d) :
    ∑ i ∈ sideOne m m', y i ≤ B₁ := hy.2.1

omit [IsStrictOrderedRing 𝕜] in
/-- The primed side's mass is capped by `B₂`. -/
theorem sum_sideTwo_le {B₁ B₂ d : 𝕜} {y : Fin (m + m') → 𝕜} (hy : y ∈ Xi B₁ B₂ m m' d) :
    ∑ i ∈ sideTwo m m', y i ≤ B₂ := hy.2.2

/-! ## Three factors above the reserve overflow a rough cap -/

/-- **Three entries above `w` sum to more than `3w`.** Stated for any index type and any subset of
at least three elements, with nonnegativity used only to discard the rest of the subset. -/
theorem three_gt_reserve_sum_lb {ι : Type*} {y : ι → 𝕜} {w : 𝕜}
    {T : Finset ι} (h3 : 3 ≤ T.card) (hw : ∀ i ∈ T, w < y i) (hnn : ∀ i, 0 ≤ y i) :
    3 * w < ∑ i ∈ T, y i := by
  obtain ⟨T', hT', hc⟩ := exists_subset_card_eq h3
  calc 3 * w = ∑ _i ∈ T', w := by simp [hc]
    _ < ∑ i ∈ T', y i := sum_lt_sum_of_nonempty (card_pos.1 (by lia)) fun i hi ↦ hw i (hT' hi)
    _ ≤ ∑ i ∈ T, y i := sum_le_sum_of_subset_of_nonneg hT' fun i _ _ ↦ hnn i

/-- **A side with three or more factors contains one that fits in the reserve.** Otherwise all its
factors exceed `w`, and three of those already overflow the side's cap `B`. -/
theorem exists_small_of_three {ι : Type*} {y : ι → 𝕜} {w B : 𝕜}
    {T : Finset ι} (h3 : 3 ≤ T.card) (hnn : ∀ i, 0 ≤ y i)
    (hcap : ∑ i ∈ T, y i ≤ B) (hB : B ≤ 3 * w) :
    ∃ i ∈ T, y i ≤ w := by
  by_contra! hcon
  linarith [three_gt_reserve_sum_lb h3 hcon hnn]

end Field

/-! ## The subset-sum engine, restricted to a subset of the indices

The engine of `Gap212.Packing.exists_subset_sum_mem_Icc` bounds every entry of the whole tuple.
Here only the small factors are bounded, so the same minimal-cardinality argument is run inside a
`Finset`. -/

section Engine

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **The subset-sum filling lemma, inside a subset.** If every entry of `S` is at most `w ≥ 0` and
`S` carries at least `D ≥ 0`, some `J ⊆ S` has sum in `[D, D + w]`.

`0 ≤ w` cannot be dropped: with `S = ∅` and `D = 0` the empty subset is forced and the conclusion
reads `0 ≤ w` outright. -/
theorem exists_subset_sum_mem_Icc_of_subset {ι : Type*} (S : Finset ι) (y : ι → 𝕜)
    (w D : 𝕜) (hw : ∀ i ∈ S, y i ≤ w) (hw0 : 0 ≤ w) (hD : 0 ≤ D)
    (htot : D ≤ ∑ i ∈ S, y i) :
    ∃ J ⊆ S, D ≤ ∑ i ∈ J, y i ∧ ∑ i ∈ J, y i ≤ D + w := by
  classical
  obtain ⟨J, hJ, hJmin⟩ := (S.powerset.filter fun J ↦ D ≤ ∑ i ∈ J, y i).exists_min_image card
    ⟨S, by simp [htot]⟩
  simp only [mem_filter, mem_powerset] at hJ hJmin
  obtain ⟨hJsub, hJD⟩ := hJ
  refine ⟨J, hJsub, hJD, ?_⟩
  rcases J.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · -- The empty subset already reaches `D`, so `D ≤ 0`, and with `hD` the sum is `0`.
    simp only [sum_empty] at hJD ⊢
    linarith
  · -- Deleting `i` must drop the sum below `D`, by minimality of the cardinality.
    have hlt : ∑ j ∈ J.erase i, y j < D := by
      by_contra! hcon
      exact (card_erase_lt_of_mem hi).not_ge (hJmin _ ⟨(erase_subset _ _).trans hJsub, hcon⟩)
    linarith [add_sum_erase J y hi, hw i (hJsub hi)]

end Engine

/-! ## The window form of condition (D)

Both branches end the same way: a subset carrying between `D` and `c₂` gives the partition, with
the complement's mass `Y - ∑_J y ≤ Y - D = c₁`. Isolating that step keeps the two branches to their
actual content. -/

section Window

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {ℓ : ℕ}

/-- **Condition (D) from a subset carrying the deficit.** -/
theorem conditionD_of_window {y : Fin ℓ → 𝕜} {γ ω₀ : 𝕜} {J : Finset (Fin ℓ)}
    (hlo : deficit (∑ i, y i) γ ω₀ ≤ ∑ i ∈ J, y i)
    (hhi : ∑ i ∈ J, y i ≤ cap₂ γ ω₀)
    (hω₀ : 0 ≤ ω₀) (h₃ : 0 ≤ cap₃ ω₀) :
    AdmitsPartition₄ y (cap₁ γ ω₀) (cap₂ γ ω₀) (cap₃ ω₀) (cap₄ ω₀) := by
  refine admitsPartition₄_of_partition₂ ⟨univ \ J, ?_, ?_⟩ h₃ (by unfold cap₄; linarith)
  · unfold deficit at hlo
    linarith [sum_sdiff (f := y) (subset_univ J)]
  · rwa [Finset.sdiff_sdiff_eq_self (subset_univ J)]

end Window

/-! ## The cap case analysis at Point A

The four rational inequalities, in the form the case analysis consumes: each bounds the deficit
under a hypothesis about how many factors the two sides carry. -/

/-- Throughout the Type IIc chamber the first capacity is at least `c₁ᵐⁱⁿ - ϵ`. The extra `ϵ`
is because the chamber starts at `γ = ξ₂ - ϵ` while `c₁ᵐⁱⁿ` is evaluated at `γ = ξ₂ = 2/5`. -/
theorem cap₁_lower {γ ω₀ : ℝ} (hγ : (2 / 5 : ℝ) - (ϵ : ℝ) ≤ γ) (hω₀ : ω₀ ≤ (ω : ℝ)) :
    (3121999999 / 10 ^ 10 : ℝ) - (ϵ : ℝ) ≤ cap₁ γ ω₀ := by
  rw [cast_ω] at hω₀
  rw [cast_ϵ] at hγ ⊢
  rw [cap₁, cast_δ, cast_ϵ]
  linarith

/-- **The second capacity is bounded below on the chamber**, by `599/10000 - 4ϵ`. This is where
condition (D)'s *upper* bound on `γ` is used — `γ ≤ 1/3 + 8ω + 7δ/3 + 3ϵ` — and it is needed even
in the no-deficit branch, since `AdmitsPartition₄` requires a nonnegative second capacity. -/
theorem cap₂_lower {γ ω₀ : ℝ}
    (hγ' : γ ≤ 1 / 3 + 8 * ((ω : ℚ) : ℝ) + 7 * ((δ : ℚ) : ℝ) / 3 + 3 * ((ϵ : ℚ) : ℝ))
    (hω₀ : ω₀ ≤ ((ω : ℚ) : ℝ)) :
    (599 / 10000 : ℝ) - 4 * ((ϵ : ℚ) : ℝ) ≤ cap₂ γ ω₀ := by
  rw [cast_ω, cast_δ, cast_ϵ] at hγ'
  rw [cast_ω] at hω₀
  rw [cap₂, cast_ϵ]
  linarith

/-- `B₁,₂ = 31/200`, over `ℝ`. -/
theorem cast_B₁ : ((B₁ : ℚ) : ℝ) = 31 / 200 := by
  norm_num [B₁]

/-- A side with at most two factors has cap `31/200`. -/
private theorem Bcap_of_le_two (h : m ≤ 2) : (Bcap m : ℝ) = 31 / 200 := by
  simp [Bcap, h, cast_B₁]

/-- **`packing_ineq₃` in force: two short sides leave no deficit.** If neither side carries more
than two factors, the total mass is at most `2 × 31/200 = 31/100`, already inside `c₁`. -/
theorem deficit_nonpos_of_both_le_two {γ ω₀ : ℝ} {y : Fin (m + m') → ℝ}
    (hm : m ≤ 2) (hm' : m' ≤ 2) (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (δ : ℝ))
    (hγ : (2 / 5 : ℝ) - (ϵ : ℝ) ≤ γ) (hω₀ : ω₀ ≤ (ω : ℝ)) :
    deficit (∑ i, y i) γ ω₀ ≤ 0 := by
  rw [deficit]
  linarith [total_le hy, Bcap_of_le_two hm, Bcap_of_le_two hm', cap₁_lower hγ hω₀,
    (cast_ϵ : ((ϵ : ℚ) : ℝ) = _)]

/-- **`packing_ineq₄` in force: mixed caps put the deficit under `δ`.** If at least one side
carries at most two factors, the total mass is at most `17/100 + 31/200 = 13/40`, so `D < δ`. -/
theorem deficit_lt_delta_of_mixed {γ ω₀ : ℝ} {y : Fin (m + m') → ℝ}
    (hmix : m ≤ 2 ∨ m' ≤ 2) (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (δ : ℝ))
    (hγ : (2 / 5 : ℝ) - (ϵ : ℝ) ≤ γ) (hω₀ : ω₀ ≤ (ω : ℝ)) :
    deficit (∑ i, y i) γ ω₀ < (δ : ℝ) := by
  have hsum : (Bcap m : ℝ) + (Bcap m' : ℝ) ≤ 17 / 100 + 31 / 200 := by
    rcases hmix with h | h
    · linarith [Bcap_of_le_two h, Bcap_le (𝕜 := ℝ) m']
    · linarith [Bcap_of_le_two h, Bcap_le (𝕜 := ℝ) m]
  rw [deficit, cast_δ]
  linarith [total_le hy, cap₁_lower hγ hω₀, (cast_ϵ : ((ϵ : ℚ) : ℝ) = _)]

/-- **`packing_ineq₁` in force: the deficit is always under `2δ`.** From the global mass bound
`17/50` alone. -/
theorem deficit_lt_two_delta {γ ω₀ : ℝ} {y : Fin (m + m') → ℝ}
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (δ : ℝ))
    (hγ : (2 / 5 : ℝ) - (ϵ : ℝ) ≤ γ) (hω₀ : ω₀ ≤ (ω : ℝ)) :
    deficit (∑ i, y i) γ ω₀ < 2 * (δ : ℝ) := by
  rw [deficit, cast_δ]
  linarith [total_le_pointA hy, cap₁_lower hγ hω₀, (cast_ϵ : ((ϵ : ℚ) : ℝ) = _)]

/-- **`packing_ineq₂` in force: three factors cannot all exceed the reserve.** Every side's rough
cap is at most `17/100`, and `3W > 17/100` throughout the chamber. -/
theorem cap_le_three_reserve {ω₀ Y : ℝ} (hY : Y ≤ 17 / 50) (hω₀ : ω₀ ≤ (ω : ℝ)) :
    (17 / 100 : ℝ) ≤ 3 * reserve Y ω₀ := by
  rw [cast_ω] at hω₀
  rw [reserve, cast_δ, cast_ϵ]
  linarith

/-! ## Condition (D), all branches -/

/-- **The small factors always carry the deficit.** On the chamber `γ ≥ ξ₂ - ϵ`, `ω₀ ≤ ω`, the
factors of mass at most the reserve sum to at least `D`. -/
theorem deficit_le_sum_small {γ ω₀ : ℝ} {y : Fin (m + m') → ℝ}
    (hγ : (2 / 5 : ℝ) - (ϵ : ℝ) ≤ γ) (hω₀ : ω₀ ≤ (ω : ℝ))
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (δ : ℝ)) :
    deficit (∑ i, y i) γ ω₀ ≤
      ∑ i ∈ ({i | y i ≤ reserve (∑ i, y i) ω₀} : Finset (Fin (m + m'))), y i := by
  have hδ0 : (0 : ℝ) ≤ ((δ : ℚ) : ℝ) := by rw [cast_δ]; norm_num
  have hnn : ∀ i, 0 ≤ y i := nonneg_of_mem hδ0 hy
  have hlb : ∀ i, ((δ : ℚ) : ℝ) ≤ y i := fun i ↦ (hy.1 i).1
  set S : Finset (Fin (m + m')) := {i | y i ≤ reserve (∑ i, y i) ω₀}
  have hsmall : ∀ (T : Finset (Fin (m + m'))), 3 ≤ T.card →
      ∑ i ∈ T, y i ≤ 17 / 100 → ∃ i ∈ T, i ∈ S := by
    intro T hT hcap
    obtain ⟨i, hiT, hi⟩ :=
      exists_small_of_three hT hnn hcap (cap_le_three_reserve (total_le_pointA hy) hω₀)
    exact ⟨i, hiT, mem_filter.2 ⟨mem_univ i, hi⟩⟩
  have hcap₁ : ∑ i ∈ sideOne m m', y i ≤ 17 / 100 :=
    (sum_sideOne_le hy).trans (Bcap_le (𝕜 := ℝ) m)
  have hcap₂ : ∑ i ∈ sideTwo m m', y i ≤ 17 / 100 :=
    (sum_sideTwo_le hy).trans (Bcap_le (𝕜 := ℝ) m')
  by_cases hboth : 3 ≤ m ∧ 3 ≤ m'
  · -- Both sides contribute a small factor, so `S` has at least two elements and carries `2δ > D`.
    obtain ⟨i₁, hi₁side, hi₁S⟩ := hsmall (sideOne m m') (by rw [card_sideOne]; lia) hcap₁
    obtain ⟨i₂, hi₂side, hi₂S⟩ := hsmall (sideTwo m m') (by rw [card_sideTwo]; lia) hcap₂
    have hne : i₁ ≠ i₂ := fun h ↦
      disjoint_left.mp (sideOne_disjoint_sideTwo m m') hi₁side (h ▸ hi₂side)
    have h2 : (2 : ℝ) ≤ S.card := by exact_mod_cast one_lt_card.2 ⟨i₁, hi₁S, i₂, hi₂S, hne⟩
    have hcs := card_nsmul_le_sum S y _ fun i _ ↦ hlb i
    rw [nsmul_eq_mul] at hcs
    linarith [mul_le_mul_of_nonneg_right h2 hδ0, deficit_lt_two_delta hy hγ hω₀]
  by_cases h3 : 3 ≤ m ∨ 3 ≤ m'
  · -- Mixed caps: `D < δ`, but the long side's small factor already carries `δ`.
    obtain ⟨i, hiS⟩ : S.Nonempty := by
      rcases h3 with h | h
      · obtain ⟨i, -, hi⟩ := hsmall _ (by rw [card_sideOne]; lia) hcap₁; exact ⟨i, hi⟩
      · obtain ⟨i, -, hi⟩ := hsmall _ (by rw [card_sideTwo]; lia) hcap₂; exact ⟨i, hi⟩
    linarith [deficit_lt_delta_of_mixed (by lia) hy hγ hω₀, hlb i,
      single_le_sum (fun j _ ↦ hnn j) hiS]
  · -- Both sides carry at most two factors, so there is no deficit.
    push Not at h3
    linarith [deficit_nonpos_of_both_le_two (by lia) (by lia) hy hγ hω₀,
      sum_nonneg (fun j (_ : j ∈ S) ↦ hnn j)]

/-- **Condition (D) of Proposition 3, at Point A, over `ℝ`.** For every rough profile the support
admits and every chamber point `γ ≥ ξ₂ - ϵ`, `0 ≤ ω₀ ≤ ω`, the four-block partition exists.

This is the continuum-packing lemma. The `ω₀ ≥ 0` restriction is not a
convenience: `Gap212.Packing.no_partition₄_of_neg_capacity` shows the condition is *unsatisfiable*
below it. -/
theorem conditionD {γ ω₀ : ℝ} {y : Fin (m + m') → ℝ}
    (hγ : (2 / 5 : ℝ) - (ϵ : ℝ) ≤ γ)
    (hγ' : γ ≤ 1 / 3 + 8 * ((ω : ℚ) : ℝ) + 7 * ((δ : ℚ) : ℝ) / 3 + 3 * ((ϵ : ℚ) : ℝ))
    (hω₀0 : 0 ≤ ω₀) (hω₀ : ω₀ ≤ (ω : ℝ))
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (δ : ℝ)) :
    AdmitsPartition₄ y (cap₁ γ ω₀) (cap₂ γ ω₀) (cap₃ ω₀) (cap₄ ω₀) := by
  have hc₃ : (0 : ℝ) ≤ cap₃ ω₀ := by rw [cap₃, cast_δ, cast_ϵ]; linarith
  have hc₂ : (0 : ℝ) ≤ cap₂ γ ω₀ := by
    linarith [cap₂_lower hγ' hω₀, (cast_ϵ : ((ϵ : ℚ) : ℝ) = _)]
  by_cases hD : deficit (∑ i, y i) γ ω₀ ≤ 0
  · exact conditionD_of_D_nonpos_real (by unfold deficit at hD; linarith) hc₂ hω₀0 hc₃
  push Not at hD
  have hW : (0 : ℝ) < reserve (∑ i, y i) ω₀ := reserve_pos (𝕜 := ℝ) (total_le_pointA hy) hω₀
  obtain ⟨J, -, hJlo, hJhi⟩ := exists_subset_sum_mem_Icc_of_subset _ y _ _
    (fun i hi ↦ (mem_filter.1 hi).2) hW.le hD.le (deficit_le_sum_small hγ hω₀ hy)
  refine conditionD_of_window hJlo ?_ hω₀0 hc₃
  linarith [c₂_sub_D (∑ i, y i) γ ω₀]

end Gap212.Packing
