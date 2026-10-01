/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCut
public import Gap212.Packing.SortedCell

/-!
# Six more cells of Condition D, each by one cut at its own threshold

`Gap212.Packing.SortedCellCut` closes cell `(10,10)` over the whole band with the cut
`t = 1/25`. Of the 91 cells, the uncut rank reading covers 62 at every level of the band, nine more
only on a sub-band, and the remaining twenty at no level; besides `(10,10)`, seven of those twenty
are closed in `Gap212.Packing.SortedCellsRest` and `SortedCellsPair`. The other twelve are closed
here and in `SortedCellsGamma`, `SortedCellsMid` and `SortedCellsEight`. Six of them close on the
whole band at a fixed threshold other than `1/25`, by exactly the argument `(10,10)` runs.

    (2,3) at t = 3/40      (3,4) at t = 13/200     (3,5) at t = 2/25
    (4,5) at t = 3/50      (6,7) at t = 3/50       (7,7) at t = 29/500

Each threshold is fixed first, before `γ` and before the level `ω₀`, as
`Gap212.Packing.admitsPartition₄_of_cut` requires; the rank sets and affine majorants below are
what `Gap212.Packing.sum_mem_le_affine_of_antitone'` consumes.

## What the certificates are

For each cell and each half of its cut, a chain of certificates covers the chamber's `γ`-range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`: bin `k` holds the first group's ranks at prefix density
`r k` and the second group's at affine majorant `(s k, q k)`, and carries at most
`#T_k·δ + r_k·(B₁ - m₁δ) + #U_k·δ + s_k·(B₂ - m₂δ) + q_k·(t - δ)`. Those four numbers against
`Gap212.capD`'s four capacities are four affine inequalities in `(γ, ω₀)`, so each certificate's
region is exact and its edges are active-set changes rather than samples. Since a window's floor
rises in `ω₀` at rate `8` while its ceiling falls at rate `2`, cover at the band's top
`ω₀ = 7/1000` gives cover at every smaller level.

## The one cell that needs a level split

`(7,7)` is the exception, and the split is in `ω₀`, not in the threshold: the certificates used here
to cover the chamber's `γ`-range at the band's top carry `161/3125` in bin 3, which asks for
`ω₀ ≥ 161/25000 = 0.00644`, just above the band floor `4/625 = 0.0064`. So the band is cut at
`ω₀ = 131/20000 = 0.00655`, and **both** halves carry a different pair of certificates on the two
sides — the low half too, since `Gap212.admitsPartition₄_cellSevenSeven_under₁`, which reaches below
the chamber's `γ` floor on the lower sub-band, has `γ` floor `4319/12500 + 8ω₀ + ϵ = 0.40152 + ϵ` at
`ω₀ = 7/1000` and so misses `2/5 - ϵ` there. The threshold is `29/500` throughout.

## What this settles

It settles six of those twelve cells over the whole band. The other six take two thresholds each:
`(4,4)`, `(5,5)`, `(5,6)` and `(6,6)` in `Gap212.Packing.SortedCellsGamma`, `(3,3)` in
`Gap212.Packing.SortedCellsMid` and `(8,8)` in `Gap212.Packing.SortedCellsEight`.
-/

@[expose] public section

namespace Gap212

open Finset Gap212.Packing

/-- The rank certificate on the low half of a cut, with the rank sets' cover and disjointness and
every prefix bound stated as integer data, one decidable conjunction. -/
private theorem cut_low_of_int {m₁ m₂ : ℕ} (hm₂ : 0 < m₂) {B₁ B₂ δ t : ℝ}
    {y : Fin (m₁ + m₂) → ℝ} (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) (hδ : 0 ≤ δ)
    (hcut : ∀ i : Fin (m₁ + m₂), m₁ ≤ (i : ℕ) → y i ≤ t)
    (T : Fin 4 → Finset (Fin m₁)) (U : Fin 4 → Finset (Fin m₂))
    (rp rd sp : Fin 4 → ℕ) (sa : Fin 4 → ℤ) (sd : Fin 4 → ℕ)
    (hdec : (∀ j, ∃ k, j ∈ T k) ∧ (∀ k l, k ≠ l → Disjoint (T k) (T l)) ∧
      (∀ j, ∃ k, j ∈ U k) ∧ (∀ k l, k ≠ l → Disjoint (U k) (U l)) ∧
      (∀ k, 0 < rd k) ∧ (∀ k, 0 < sd k) ∧
      (∀ k, ∀ j, j ≤ m₁ → rd k * ((T k).filter (fun i ↦ i.val < j)).card ≤ rp k * j) ∧
      ∀ k, ∀ j : ℕ, j ≤ m₂ → 1 ≤ j →
        ((U k).filter (fun i ↦ i.val < j)).card * (sd k : ℤ) ≤ sp k * j + sa k)
    (r s q c : Fin 4 → ℝ) (hr : ∀ k, (rp k : ℝ) / rd k = r k) (hs : ∀ k, (sp k : ℝ) / sd k = s k)
    (hq : ∀ k, (sa k : ℝ) / sd k = q k) (hq0 : ∀ k, 0 ≤ q k)
    (hcap : ∀ k, ((((T k).card : ℕ) : ℝ) * δ + r k * (B₁ - (m₁ : ℝ) * δ))
        + ((((U k).card : ℕ) : ℝ) * δ + s k * (B₂ - (m₂ : ℝ) * δ) + q k * (t - δ)) ≤ c k) :
    AdmitsPartition₄ y (c 0) (c 1) (c 2) (c 3) := by
  obtain ⟨hTc, hTd, hUc, hUd, hrd, hsd, hrT, hsU⟩ := hdec
  exact admitsPartition₄_of_rank_certificate_cut_low hm₂ hy hδ hcut T U hTc hTd hUc hUd r s q
    (fun k ↦ hr k ▸ by positivity) (fun k ↦ hs k ▸ by positivity) hq0
    (fun k ↦ hr k ▸ prefixDensity_of_nat (T k) _ _ (hrd k) (hrT k))
    (fun k ↦ by simpa only [← hs k, ← hq k, Int.cast_natCast] using
      prefixAffine_of_int (U k) (sp k) (sa k) (sd k) (hsd k) (hsU k)) c hcap

/-- The rank certificate on the high half of a cut, with the rank sets' cover and disjointness
and every prefix bound stated as integer data, one decidable conjunction. -/
private theorem cut_high_of_int {m₁ m₂ : ℕ} (hm₂ : 0 < m₂) {B₁ B₂ δ t : ℝ}
    {y : Fin (m₁ + m₂) → ℝ} (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) (hδ : 0 ≤ δ)
    (hcut : ∃ i : Fin (m₁ + m₂), m₁ ≤ (i : ℕ) ∧ t ≤ y i)
    (T : Fin 4 → Finset (Fin m₁)) (U : Fin 4 → Finset (Fin m₂))
    (rp rd sp : Fin 4 → ℕ) (sa : Fin 4 → ℤ) (sd : Fin 4 → ℕ)
    (hdec : (∀ j, ∃ k, j ∈ T k) ∧ (∀ k l, k ≠ l → Disjoint (T k) (T l)) ∧
      (∀ j, ∃ k, j ∈ U k) ∧ (∀ k l, k ≠ l → Disjoint (U k) (U l)) ∧
      (∀ k, 0 < rd k) ∧ (∀ k, 0 < sd k) ∧
      (∀ k, ∀ j, j ≤ m₁ → rd k * ((T k).filter (fun i ↦ i.val < j)).card ≤ rp k * j) ∧
      ∀ k, ∀ j : ℕ, j ≤ m₂ → 1 ≤ j →
        ((U k).filter (fun i ↦ i.val < j)).card * (sd k : ℤ) ≤ sp k * j + sa k)
    (r s q c : Fin 4 → ℝ) (hr : ∀ k, (rp k : ℝ) / rd k = r k) (hs : ∀ k, (sp k : ℝ) / sd k = s k)
    (hq : ∀ k, (sa k : ℝ) / sd k = q k) (hq0 : ∀ k, q k ≤ 0)
    (hcap : ∀ k, ((((T k).card : ℕ) : ℝ) * δ + r k * (B₁ - (m₁ : ℝ) * δ))
        + ((((U k).card : ℕ) : ℝ) * δ + s k * (B₂ - (m₂ : ℝ) * δ) + q k * (t - δ)) ≤ c k) :
    AdmitsPartition₄ y (c 0) (c 1) (c 2) (c 3) := by
  obtain ⟨hTc, hTd, hUc, hUd, hrd, hsd, hrT, hsU⟩ := hdec
  exact admitsPartition₄_of_rank_certificate_cut_high hm₂ hy hδ hcut T U hTc hTd hUc hUd r s q
    (fun k ↦ hr k ▸ by positivity) (fun k ↦ hs k ▸ by positivity) hq0
    (fun k ↦ hr k ▸ prefixDensity_of_nat (T k) _ _ (hrd k) (hrT k))
    (fun k ↦ by simpa only [← hs k, ← hq k, Int.cast_natCast] using
      prefixAffine_of_int (U k) (sp k) (sa k) (sd k) (hsd k) (hsU k)) c hcap

/-! ## Cell `(2,3)` -/

/-- The first group's rank sets for cell `(2,3)`, the low half's certificate 1. -/
def cutTwoThreeUnder₁LowRanks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutTwoThreeUnder₁LowRanks`. -/
noncomputable def cutTwoThreeUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(2,3)`, the low half's certificate 1. -/
def cutTwoThreeUnder₁Ranks : Fin 4 → Finset (Fin 3) :=
  ![{0, 1}, {2}, ∅, ∅]

/-- The slopes of `Gap212.cutTwoThreeUnder₁Ranks`. -/
noncomputable def cutTwoThreeUnder₁Dens : Fin 4 → ℝ := ![0, 1 / 3, 0, 0]

/-- The constants of `Gap212.cutTwoThreeUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutTwoThreeUnder₁Const : Fin 4 → ℝ := ![2, 0, 0, 0]

/-- The first group's rank sets for cell `(2,3)`, the high half's certificate 1. -/
def cutTwoThreeOver₁LowRanks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutTwoThreeOver₁LowRanks`. -/
noncomputable def cutTwoThreeOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(2,3)`, the high half's certificate 1. -/
def cutTwoThreeOver₁Ranks : Fin 4 → Finset (Fin 3) :=
  ![{0}, {1}, ∅, {2}]

/-- The slopes of `Gap212.cutTwoThreeOver₁Ranks`. -/
noncomputable def cutTwoThreeOver₁Dens : Fin 4 → ℝ := ![1, 1 / 2, 0, 1 / 2]

/-- The constants of `Gap212.cutTwoThreeOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutTwoThreeOver₁Const : Fin 4 → ℝ := ![0, 0, 0, -1 / 2]

/-- The first group's rank sets for cell `(2,3)`, the high half's certificate 2. -/
def cutTwoThreeOver₂LowRanks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutTwoThreeOver₂LowRanks`. -/
noncomputable def cutTwoThreeOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(2,3)`, the high half's certificate 2. -/
def cutTwoThreeOver₂Ranks : Fin 4 → Finset (Fin 3) :=
  ![{0, 1}, ∅, ∅, {2}]

/-- The slopes of `Gap212.cutTwoThreeOver₂Ranks`. -/
noncomputable def cutTwoThreeOver₂Dens : Fin 4 → ℝ := ![1, 0, 0, 1 / 2]

/-- The constants of `Gap212.cutTwoThreeOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutTwoThreeOver₂Const : Fin 4 → ℝ := ![0, 0, 0, -1 / 2]

/-- **Cell `(2,3)`, the low half's certificate 1.**

Block bounds `193 / 625`, `7 / 120`, `0`, `0`.
Valid on `4 / 625 < ω₀` and on
`427 / 1250 + 8ω₀ + ϵ ≤ γ ≤ 53 / 120 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3976000 + ϵ, 0.4276667 - ϵ]`. The cut is at `t = 3 / 40`. -/
theorem admitsPartition₄_cellTwoThree_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 427 / 1250 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 53 / 120 - 2 * ω₀ - slack)
    {y : Fin (2 + 3) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (7 / 40) 2 3 (41 / 2500))
    (hcut : ∀ i : Fin (2 + 3), 2 ≤ (i : ℕ) → y i ≤ 3 / 40) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_int (by norm_num) hy (by norm_num) hcut cutTwoThreeUnder₁LowRanks
    cutTwoThreeUnder₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![0, 1, 0, 0] ![2, 0, 0, 0] ![1, 3, 1, 1]
    (by decide) cutTwoThreeUnder₁LowDens cutTwoThreeUnder₁Dens cutTwoThreeUnder₁Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutTwoThreeUnder₁LowRanks,
    cutTwoThreeUnder₁Ranks, cutTwoThreeUnder₁LowDens, cutTwoThreeUnder₁Dens,
    cutTwoThreeUnder₁Const] <;> linarith

/-- **Cell `(2,3)`, the high half's certificate 1.**

Block bounds `301 / 1000`, `793 / 10000`, `0`, `1 / 20`.
Valid on `4 / 625 < ω₀` and on
`1669 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 4207 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3898000 + ϵ, 0.4067000 - ϵ]`. The cut is at `t = 3 / 40`. -/
theorem admitsPartition₄_cellTwoThree_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1669 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4207 / 10000 - 2 * ω₀ - slack)
    {y : Fin (2 + 3) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (7 / 40) 2 3 (41 / 2500))
    (hcut : ∃ i : Fin (2 + 3), 2 ≤ (i : ℕ) ∧ 3 / 40 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_int (by norm_num) hy (by norm_num) hcut cutTwoThreeOver₁LowRanks
    cutTwoThreeOver₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 0, 1] ![0, 0, 0, -1] ![1, 2, 1, 2]
    (by decide) cutTwoThreeOver₁LowDens cutTwoThreeOver₁Dens cutTwoThreeOver₁Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutTwoThreeOver₁LowRanks,
    cutTwoThreeOver₁Ranks, cutTwoThreeOver₁LowDens, cutTwoThreeOver₁Dens,
    cutTwoThreeOver₁Const] <;> linarith

/-- **Cell `(2,3)`, the high half's certificate 2.**

Block bounds `1587 / 5000`, `0`, `0`, `1 / 20`.
Valid on `4 / 625 < ω₀` and on
`1751 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 1 / 2 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4062000 + ϵ, 0.4860000 - ϵ]`. The cut is at `t = 3 / 40`. -/
theorem admitsPartition₄_cellTwoThree_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1751 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1 / 2 - 2 * ω₀ - slack)
    {y : Fin (2 + 3) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (7 / 40) 2 3 (41 / 2500))
    (hcut : ∃ i : Fin (2 + 3), 2 ≤ (i : ℕ) ∧ 3 / 40 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_int (by norm_num) hy (by norm_num) hcut cutTwoThreeOver₂LowRanks
    cutTwoThreeOver₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 0, 0, 1] ![0, 0, 0, -1] ![1, 1, 1, 2]
    (by decide) cutTwoThreeOver₂LowDens cutTwoThreeOver₂Dens cutTwoThreeOver₂Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutTwoThreeOver₂LowRanks,
    cutTwoThreeOver₂Ranks, cutTwoThreeOver₂LowDens, cutTwoThreeOver₂Dens,
    cutTwoThreeOver₂Const] <;> linarith

/-- **Cell `(2,3)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,2}, B_{1,3}, 2, 3, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 3 / 40`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellTwoThree_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 3) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (7 / 40) 2 3 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_cut (t := 3 / 40) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · exact admitsPartition₄_cellTwoThree_under₁ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (4207 / 10000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellTwoThree_over₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellTwoThree_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(2,3)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellTwoThree_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (2 + 3) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (7 / 40) 2 3 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellTwoThree_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(2,3)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 2 = gap212Cap 2 = 397 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellTwoThree_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 3) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 2) (gap212Params.B j' 3) 2 3
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  simp only [gap212Params, gap212Cap] at hy; norm_num at hy
  exact admitsPartition₄_cellTwoThree_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(3,4)` -/

/-- The first group's rank sets for cell `(3,4)`, the low half's certificate 1. -/
def cutThreeFourUnder₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutThreeFourUnder₁LowRanks`. -/
noncomputable def cutThreeFourUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,4)`, the low half's certificate 1. -/
def cutThreeFourUnder₁Ranks : Fin 4 → Finset (Fin 4) :=
  ![{0, 1}, {2}, ∅, {3}]

/-- The slopes of `Gap212.cutThreeFourUnder₁Ranks`. -/
noncomputable def cutThreeFourUnder₁Dens : Fin 4 → ℝ := ![0, 1 / 3, 0, 1 / 4]

/-- The constants of `Gap212.cutThreeFourUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutThreeFourUnder₁Const : Fin 4 → ℝ := ![2, 0, 0, 0]

/-- The first group's rank sets for cell `(3,4)`, the high half's certificate 1. -/
def cutThreeFourOver₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![{0, 1}, {2}, ∅, ∅]

/-- The prefix densities of `Gap212.cutThreeFourOver₁LowRanks`. -/
noncomputable def cutThreeFourOver₁LowDens : Fin 4 → ℝ := ![1, 1 / 3, 0, 0]

/-- The second group's rank sets for cell `(3,4)`, the high half's certificate 1. -/
def cutThreeFourOver₁Ranks : Fin 4 → Finset (Fin 4) :=
  ![{0, 1}, ∅, {3}, {2}]

/-- The slopes of `Gap212.cutThreeFourOver₁Ranks`. -/
noncomputable def cutThreeFourOver₁Dens : Fin 4 → ℝ := ![1, 0, 1 / 3, 1 / 2]

/-- The constants of `Gap212.cutThreeFourOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutThreeFourOver₁Const : Fin 4 → ℝ := ![0, 0, -1 / 3, -1 / 2]

/-- **Cell `(3,4)`, the low half's certificate 1.**

Block bounds `61 / 200`, `167 / 3000`, `0`, `917 / 20000`.
Valid on `4 / 625 < ω₀` and on
`1689 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 1333 / 3000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3938000 + ϵ, 0.4303333 - ϵ]`. The cut is at `t = 13 / 200`. -/
theorem admitsPartition₄_cellThreeFour_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1689 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1333 / 3000 - 2 * ω₀ - slack)
    {y : Fin (3 + 4) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (917 / 5000) 3 4 (41 / 2500))
    (hcut : ∀ i : Fin (3 + 4), 3 ≤ (i : ℕ) → y i ≤ 13 / 200) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_int (by norm_num) hy (by norm_num) hcut cutThreeFourUnder₁LowRanks
    cutThreeFourUnder₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![0, 1, 0, 1] ![2, 0, 0, 0] ![1, 3, 1, 4]
    (by decide) cutThreeFourUnder₁LowDens cutThreeFourUnder₁Dens cutThreeFourUnder₁Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutThreeFourUnder₁LowRanks,
    cutThreeFourUnder₁Ranks, cutThreeFourUnder₁LowDens, cutThreeFourUnder₁Dens,
    cutThreeFourUnder₁Const] <;> linarith

/-- **Cell `(3,4)`, the high half's certificate 1.**

Block bounds `773 / 2500`, `7 / 120`, `74 / 1875`, `51 / 1000`.
Valid on `4 / 625 < ω₀` and on
`171 / 500 + 8ω₀ + ϵ ≤ γ ≤ 53 / 120 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3980000 + ϵ, 0.4276667 - ϵ]`. The cut is at `t = 13 / 200`. -/
theorem admitsPartition₄_cellThreeFour_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 171 / 500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 53 / 120 - 2 * ω₀ - slack)
    {y : Fin (3 + 4) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (917 / 5000) 3 4 (41 / 2500))
    (hcut : ∃ i : Fin (3 + 4), 3 ≤ (i : ℕ) ∧ 13 / 200 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_int (by norm_num) hy (by norm_num) hcut cutThreeFourOver₁LowRanks
    cutThreeFourOver₁Ranks ![1, 1, 0, 0] ![1, 3, 1, 1] ![1, 0, 1, 1] ![0, 0, -1, -1] ![1, 1, 3, 2]
    (by decide) cutThreeFourOver₁LowDens cutThreeFourOver₁Dens cutThreeFourOver₁Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutThreeFourOver₁LowRanks,
    cutThreeFourOver₁Ranks, cutThreeFourOver₁LowDens, cutThreeFourOver₁Dens,
    cutThreeFourOver₁Const] <;> linarith

/-- **Cell `(3,4)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,3}, B_{1,4}, 3, 4, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 13 / 200`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellThreeFour_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 4) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (917 / 5000) 3 4 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_cut (t := 13 / 200) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · exact admitsPartition₄_cellThreeFour_under₁ hωlo (by linarith) (by linarith) hy hcut
  · exact admitsPartition₄_cellThreeFour_over₁ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(3,4)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellThreeFour_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (3 + 4) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (917 / 5000) 3 4 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellThreeFour_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(3,4)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 3 = gap212Cap 3 = 7 / 40` at every stratum `j`. -/
theorem admitsPartition₄_cellThreeFour_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 4) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 3) (gap212Params.B j' 4) 3 4
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  simp only [gap212Params, gap212Cap] at hy; norm_num at hy
  exact admitsPartition₄_cellThreeFour_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(3,5)` -/

/-- The first group's rank sets for cell `(3,5)`, the low half's certificate 1. -/
def cutThreeFiveUnder₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutThreeFiveUnder₁LowRanks`. -/
noncomputable def cutThreeFiveUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,5)`, the low half's certificate 1. -/
def cutThreeFiveUnder₁Ranks : Fin 4 → Finset (Fin 5) :=
  ![{0, 2}, {1}, {4}, {3}]

/-- The slopes of `Gap212.cutThreeFiveUnder₁Ranks`. -/
noncomputable def cutThreeFiveUnder₁Dens : Fin 4 → ℝ := ![1 / 2, 1 / 2, 1 / 5, 1 / 4]

/-- The constants of `Gap212.cutThreeFiveUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutThreeFiveUnder₁Const : Fin 4 → ℝ := ![1 / 2, 0, 0, 0]

/-- The first group's rank sets for cell `(3,5)`, the low half's certificate 2. -/
def cutThreeFiveUnder₂LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutThreeFiveUnder₂LowRanks`. -/
noncomputable def cutThreeFiveUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,5)`, the low half's certificate 2. -/
def cutThreeFiveUnder₂Ranks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1}, {2}, {4}, {3}]

/-- The slopes of `Gap212.cutThreeFiveUnder₂Ranks`. -/
noncomputable def cutThreeFiveUnder₂Dens : Fin 4 → ℝ := ![1, 1 / 3, 1 / 5, 1 / 4]

/-- The constants of `Gap212.cutThreeFiveUnder₂Ranks`, nonnegative throughout. -/
noncomputable def cutThreeFiveUnder₂Const : Fin 4 → ℝ := ![0, 0, 0, 0]

/-- The first group's rank sets for cell `(3,5)`, the high half's certificate 1. -/
def cutThreeFiveOver₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutThreeFiveOver₁LowRanks`. -/
noncomputable def cutThreeFiveOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,5)`, the high half's certificate 1. -/
def cutThreeFiveOver₁Ranks : Fin 4 → Finset (Fin 5) :=
  ![{0}, {1, 2}, {4}, {3}]

/-- The slopes of `Gap212.cutThreeFiveOver₁Ranks`. -/
noncomputable def cutThreeFiveOver₁Dens : Fin 4 → ℝ := ![1, 1, 1 / 4, 1 / 3]

/-- The constants of `Gap212.cutThreeFiveOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutThreeFiveOver₁Const : Fin 4 → ℝ := ![0, -1, -1 / 4, -1 / 3]

/-- The first group's rank sets for cell `(3,5)`, the high half's certificate 2. -/
def cutThreeFiveOver₂LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutThreeFiveOver₂LowRanks`. -/
noncomputable def cutThreeFiveOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,5)`, the high half's certificate 2. -/
def cutThreeFiveOver₂Ranks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1}, {4}, {3}, {2}]

/-- The slopes of `Gap212.cutThreeFiveOver₂Ranks`. -/
noncomputable def cutThreeFiveOver₂Dens : Fin 4 → ℝ := ![1, 1 / 4, 1 / 3, 1 / 2]

/-- The constants of `Gap212.cutThreeFiveOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutThreeFiveOver₂Const : Fin 4 → ℝ := ![0, -1 / 4, -1 / 3, -1 / 2]

/-- **Cell `(3,5)`, the low half's certificate 1.**

Block bounds `2939 / 10000`, `707 / 10000`, `953 / 25000`, `871 / 20000`.
Valid on `4 / 625 < ω₀` and on
`3267 / 10000 + 8ω₀ + ϵ ≤ γ ≤ 4293 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3827000 + ϵ, 0.4153000 - ϵ]`. The cut is at `t = 2 / 25`. -/
theorem admitsPartition₄_cellThreeFive_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3267 / 10000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4293 / 10000 - 2 * ω₀ - slack)
    {y : Fin (3 + 5) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (953 / 5000) 3 5 (41 / 2500))
    (hcut : ∀ i : Fin (3 + 5), 3 ≤ (i : ℕ) → y i ≤ 2 / 25) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_int (by norm_num) hy (by norm_num) hcut cutThreeFiveUnder₁LowRanks
    cutThreeFiveUnder₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 1, 1] ![1, 0, 0, 0] ![2, 2, 5, 4]
    (by decide) cutThreeFiveUnder₁LowDens cutThreeFiveUnder₁Dens cutThreeFiveUnder₁Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutThreeFiveUnder₁LowRanks,
    cutThreeFiveUnder₁Ranks, cutThreeFiveUnder₁LowDens, cutThreeFiveUnder₁Dens,
    cutThreeFiveUnder₁Const] <;> linarith

/-- **Cell `(3,5)`, the low half's certificate 2.**

Block bounds `791 / 2500`, `263 / 5000`, `953 / 25000`, `871 / 20000`.
Valid on `4 / 625 < ω₀` and on
`873 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 2237 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4052000 + ϵ, 0.4334000 - ϵ]`. The cut is at `t = 2 / 25`. -/
theorem admitsPartition₄_cellThreeFive_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 873 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2237 / 5000 - 2 * ω₀ - slack)
    {y : Fin (3 + 5) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (953 / 5000) 3 5 (41 / 2500))
    (hcut : ∀ i : Fin (3 + 5), 3 ≤ (i : ℕ) → y i ≤ 2 / 25) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_int (by norm_num) hy (by norm_num) hcut cutThreeFiveUnder₂LowRanks
    cutThreeFiveUnder₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 1, 1] ![0, 0, 0, 0] ![1, 3, 5, 4]
    (by decide) cutThreeFiveUnder₂LowDens cutThreeFiveUnder₂Dens cutThreeFiveUnder₂Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutThreeFiveUnder₂LowRanks,
    cutThreeFiveUnder₂Ranks, cutThreeFiveUnder₂LowDens, cutThreeFiveUnder₂Dens,
    cutThreeFiveUnder₂Const] <;> linarith

/-- **Cell `(3,5)`, the high half's certificate 1.**

Block bounds `3 / 10`, `389 / 5000`, `553 / 20000`, `157 / 5000`.
Valid on `4 / 625 < ω₀` and on
`208 / 625 + 8ω₀ + ϵ ≤ γ ≤ 2111 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3888000 + ϵ, 0.4082000 - ϵ]`. The cut is at `t = 2 / 25`. -/
theorem admitsPartition₄_cellThreeFive_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 208 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2111 / 5000 - 2 * ω₀ - slack)
    {y : Fin (3 + 5) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (953 / 5000) 3 5 (41 / 2500))
    (hcut : ∃ i : Fin (3 + 5), 3 ≤ (i : ℕ) ∧ 2 / 25 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_int (by norm_num) hy (by norm_num) hcut cutThreeFiveOver₁LowRanks
    cutThreeFiveOver₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 1, 1] ![0, -1, -1, -1] ![1, 1, 4, 3]
    (by decide) cutThreeFiveOver₁LowDens cutThreeFiveOver₁Dens cutThreeFiveOver₁Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutThreeFiveOver₁LowRanks,
    cutThreeFiveOver₁Ranks, cutThreeFiveOver₁LowDens, cutThreeFiveOver₁Dens,
    cutThreeFiveOver₁Const] <;> linarith

/-- **Cell `(3,5)`, the high half's certificate 2.**

Block bounds `791 / 2500`, `553 / 20000`, `157 / 5000`, `389 / 10000`.
Valid on `4 / 625 < ω₀` and on
`873 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 9447 / 20000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4052000 + ϵ, 0.4583500 - ϵ]`. The cut is at `t = 2 / 25`. -/
theorem admitsPartition₄_cellThreeFive_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 873 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 9447 / 20000 - 2 * ω₀ - slack)
    {y : Fin (3 + 5) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (953 / 5000) 3 5 (41 / 2500))
    (hcut : ∃ i : Fin (3 + 5), 3 ≤ (i : ℕ) ∧ 2 / 25 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_int (by norm_num) hy (by norm_num) hcut cutThreeFiveOver₂LowRanks
    cutThreeFiveOver₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 1, 1] ![0, -1, -1, -1] ![1, 4, 3, 2]
    (by decide) cutThreeFiveOver₂LowDens cutThreeFiveOver₂Dens cutThreeFiveOver₂Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutThreeFiveOver₂LowRanks,
    cutThreeFiveOver₂Ranks, cutThreeFiveOver₂LowDens, cutThreeFiveOver₂Dens,
    cutThreeFiveOver₂Const] <;> linarith

/-- **Cell `(3,5)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,3}, B_{1,5}, 3, 5, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 2 / 25`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellThreeFive_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 5) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (953 / 5000) 3 5 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_cut (t := 2 / 25) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · rcases le_or_gt γ (4293 / 10000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellThreeFive_under₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellThreeFive_under₂ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (2111 / 5000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellThreeFive_over₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellThreeFive_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(3,5)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellThreeFive_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (3 + 5) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (953 / 5000) 3 5 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellThreeFive_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(3,5)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 3 = gap212Cap 3 = 7 / 40` at every stratum `j`. -/
theorem admitsPartition₄_cellThreeFive_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 5) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 3) (gap212Params.B j' 5) 3 5
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  simp only [gap212Params, gap212Cap] at hy; norm_num at hy
  exact admitsPartition₄_cellThreeFive_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(4,5)` -/

/-- The first group's rank sets for cell `(4,5)`, the low half's certificate 1. -/
def cutFourFiveUnder₁LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFourFiveUnder₁LowRanks`. -/
noncomputable def cutFourFiveUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,5)`, the low half's certificate 1. -/
def cutFourFiveUnder₁Ranks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1}, {2}, {4}, {3}]

/-- The slopes of `Gap212.cutFourFiveUnder₁Ranks`. -/
noncomputable def cutFourFiveUnder₁Dens : Fin 4 → ℝ := ![0, 1 / 3, 1 / 5, 1 / 4]

/-- The constants of `Gap212.cutFourFiveUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutFourFiveUnder₁Const : Fin 4 → ℝ := ![2, 0, 0, 0]

/-- The first group's rank sets for cell `(4,5)`, the high half's certificate 1. -/
def cutFourFiveOver₁LowRanks : Fin 4 → Finset (Fin 4) :=
  ![{0, 1, 2}, ∅, ∅, {3}]

/-- The prefix densities of `Gap212.cutFourFiveOver₁LowRanks`. -/
noncomputable def cutFourFiveOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 1 / 4]

/-- The second group's rank sets for cell `(4,5)`, the high half's certificate 1. -/
def cutFourFiveOver₁Ranks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1}, {2, 4}, {3}, ∅]

/-- The slopes of `Gap212.cutFourFiveOver₁Ranks`. -/
noncomputable def cutFourFiveOver₁Dens : Fin 4 → ℝ := ![1, 1 / 2, 1 / 3, 0]

/-- The constants of `Gap212.cutFourFiveOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutFourFiveOver₁Const : Fin 4 → ℝ := ![0, -1 / 2, -1 / 3, 0]

/-- The first group's rank sets for cell `(4,5)`, the high half's certificate 2. -/
def cutFourFiveOver₂LowRanks : Fin 4 → Finset (Fin 4) :=
  ![{0, 1, 2}, ∅, ∅, {3}]

/-- The prefix densities of `Gap212.cutFourFiveOver₂LowRanks`. -/
noncomputable def cutFourFiveOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 1 / 4]

/-- The second group's rank sets for cell `(4,5)`, the high half's certificate 2. -/
def cutFourFiveOver₂Ranks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1, 2}, {4}, {3}, ∅]

/-- The slopes of `Gap212.cutFourFiveOver₂Ranks`. -/
noncomputable def cutFourFiveOver₂Dens : Fin 4 → ℝ := ![1, 1 / 4, 1 / 3, 0]

/-- The constants of `Gap212.cutFourFiveOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutFourFiveOver₂Const : Fin 4 → ℝ := ![0, -1 / 4, -1 / 3, 0]

/-- **Cell `(4,5)`, the low half's certificate 1.**

Block bounds `1517 / 5000`, `263 / 5000`, `953 / 25000`, `871 / 20000`.
Valid on `4 / 625 < ω₀` and on
`1681 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 2237 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3922000 + ϵ, 0.4334000 - ϵ]`. The cut is at `t = 3 / 50`. -/
theorem admitsPartition₄_cellFourFive_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1681 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2237 / 5000 - 2 * ω₀ - slack)
    {y : Fin (4 + 5) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (953 / 5000) 4 5 (41 / 2500))
    (hcut : ∀ i : Fin (4 + 5), 4 ≤ (i : ℕ) → y i ≤ 3 / 50) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_int (by norm_num) hy (by norm_num) hcut cutFourFiveUnder₁LowRanks
    cutFourFiveUnder₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![0, 1, 1, 1] ![2, 0, 0, 0] ![1, 3, 5, 4]
    (by decide) cutFourFiveUnder₁LowDens cutFourFiveUnder₁Dens cutFourFiveUnder₁Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutFourFiveUnder₁LowRanks,
    cutFourFiveUnder₁Ranks, cutFourFiveUnder₁LowDens, cutFourFiveUnder₁Dens,
    cutFourFiveUnder₁Const] <;> linarith

/-- **Cell `(4,5)`, the high half's certificate 1.**

Block bounds `771 / 2500`, `653 / 10000`, `571 / 15000`, `917 / 20000`.
Valid on `4 / 625 < ω₀` and on
`853 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 4347 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3972000 + ϵ, 0.4207000 - ϵ]`. The cut is at `t = 3 / 50`. -/
theorem admitsPartition₄_cellFourFive_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 853 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4347 / 10000 - 2 * ω₀ - slack)
    {y : Fin (4 + 5) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (953 / 5000) 4 5 (41 / 2500))
    (hcut : ∃ i : Fin (4 + 5), 4 ≤ (i : ℕ) ∧ 3 / 50 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_int (by norm_num) hy (by norm_num) hcut cutFourFiveOver₁LowRanks
    cutFourFiveOver₁Ranks ![1, 0, 0, 1] ![1, 1, 1, 4] ![1, 1, 1, 0] ![0, -1, -1, 0] ![1, 2, 3, 1]
    (by decide) cutFourFiveOver₁LowDens cutFourFiveOver₁Dens cutFourFiveOver₁Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutFourFiveOver₁LowRanks,
    cutFourFiveOver₁Ranks, cutFourFiveOver₁LowDens, cutFourFiveOver₁Dens,
    cutFourFiveOver₁Const] <;> linarith

/-- **Cell `(4,5)`, the high half's certificate 2.**

Block bounds `203 / 625`, `653 / 20000`, `571 / 15000`, `917 / 20000`.
Valid on `4 / 625 < ω₀` and on
`447 / 1250 + 8ω₀ + ϵ ≤ γ ≤ 9347 / 20000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4136000 + ϵ, 0.4533500 - ϵ]`. The cut is at `t = 3 / 50`. -/
theorem admitsPartition₄_cellFourFive_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 447 / 1250 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 9347 / 20000 - 2 * ω₀ - slack)
    {y : Fin (4 + 5) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (953 / 5000) 4 5 (41 / 2500))
    (hcut : ∃ i : Fin (4 + 5), 4 ≤ (i : ℕ) ∧ 3 / 50 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_int (by norm_num) hy (by norm_num) hcut cutFourFiveOver₂LowRanks
    cutFourFiveOver₂Ranks ![1, 0, 0, 1] ![1, 1, 1, 4] ![1, 1, 1, 0] ![0, -1, -1, 0] ![1, 4, 3, 1]
    (by decide) cutFourFiveOver₂LowDens cutFourFiveOver₂Dens cutFourFiveOver₂Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutFourFiveOver₂LowRanks,
    cutFourFiveOver₂Ranks, cutFourFiveOver₂LowDens, cutFourFiveOver₂Dens,
    cutFourFiveOver₂Const] <;> linarith

/-- **Cell `(4,5)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,4}, B_{1,5}, 4, 5, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 3 / 50`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellFourFive_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 5) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (953 / 5000) 4 5 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_cut (t := 3 / 50) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · exact admitsPartition₄_cellFourFive_under₁ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (4347 / 10000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellFourFive_over₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellFourFive_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(4,5)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellFourFive_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (4 + 5) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (953 / 5000) 4 5 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellFourFive_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(4,5)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 4 = gap212Cap 4 = 917 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFourFive_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 5) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 4) (gap212Params.B j' 5) 4 5
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  simp only [gap212Params, gap212Cap] at hy; norm_num at hy
  exact admitsPartition₄_cellFourFive_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(6,7)` -/

/-- The first group's rank sets for cell `(6,7)`, the low half's certificate 1. -/
def cutSixSevenUnder₁LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSixSevenUnder₁LowRanks`. -/
noncomputable def cutSixSevenUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,7)`, the low half's certificate 1. -/
def cutSixSevenUnder₁Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 3, 5}, {1, 6}, {4}, {2}]

/-- The slopes of `Gap212.cutSixSevenUnder₁Ranks`. -/
noncomputable def cutSixSevenUnder₁Dens : Fin 4 → ℝ := ![2 / 5, 1 / 5, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutSixSevenUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutSixSevenUnder₁Const : Fin 4 → ℝ := ![3 / 5, 3 / 5, 0, 0]

/-- The first group's rank sets for cell `(6,7)`, the low half's certificate 2. -/
def cutSixSevenUnder₂LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSixSevenUnder₂LowRanks`. -/
noncomputable def cutSixSevenUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,7)`, the low half's certificate 2. -/
def cutSixSevenUnder₂Ranks : Fin 4 → Finset (Fin 7) :=
  ![{1, 3, 5, 6}, {0}, {4}, {2}]

/-- The slopes of `Gap212.cutSixSevenUnder₂Ranks`. -/
noncomputable def cutSixSevenUnder₂Dens : Fin 4 → ℝ := ![4 / 7, 0, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutSixSevenUnder₂Ranks`, nonnegative throughout. -/
noncomputable def cutSixSevenUnder₂Const : Fin 4 → ℝ := ![0, 1, 0, 0]

/-- The first group's rank sets for cell `(6,7)`, the low half's certificate 3. -/
def cutSixSevenUnder₃LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSixSevenUnder₃LowRanks`. -/
noncomputable def cutSixSevenUnder₃LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,7)`, the low half's certificate 3. -/
def cutSixSevenUnder₃Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 5}, {3, 6}, {4}, {2}]

/-- The slopes of `Gap212.cutSixSevenUnder₃Ranks`. -/
noncomputable def cutSixSevenUnder₃Dens : Fin 4 → ℝ := ![1 / 4, 2 / 7, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutSixSevenUnder₃Ranks`, nonnegative throughout. -/
noncomputable def cutSixSevenUnder₃Const : Fin 4 → ℝ := ![3 / 2, 0, 0, 0]

/-- The first group's rank sets for cell `(6,7)`, the high half's certificate 1. -/
def cutSixSevenOver₁LowRanks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2, 3, 4}, ∅, {5}, ∅]

/-- The prefix densities of `Gap212.cutSixSevenOver₁LowRanks`. -/
noncomputable def cutSixSevenOver₁LowDens : Fin 4 → ℝ := ![1, 0, 1 / 6, 0]

/-- The second group's rank sets for cell `(6,7)`, the high half's certificate 1. -/
def cutSixSevenOver₁Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1}, {2, 4, 6}, ∅, {3, 5}]

/-- The slopes of `Gap212.cutSixSevenOver₁Ranks`. -/
noncomputable def cutSixSevenOver₁Dens : Fin 4 → ℝ := ![1, 1 / 2, 0, 2 / 5]

/-- The constants of `Gap212.cutSixSevenOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutSixSevenOver₁Const : Fin 4 → ℝ := ![0, -1 / 2, 0, -2 / 5]

/-- The first group's rank sets for cell `(6,7)`, the high half's certificate 2. -/
def cutSixSevenOver₂LowRanks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2, 3, 4}, ∅, {5}, ∅]

/-- The prefix densities of `Gap212.cutSixSevenOver₂LowRanks`. -/
noncomputable def cutSixSevenOver₂LowDens : Fin 4 → ℝ := ![1, 0, 1 / 6, 0]

/-- The second group's rank sets for cell `(6,7)`, the high half's certificate 2. -/
def cutSixSevenOver₂Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2}, {3, 6}, ∅, {4, 5}]

/-- The slopes of `Gap212.cutSixSevenOver₂Ranks`. -/
noncomputable def cutSixSevenOver₂Dens : Fin 4 → ℝ := ![1, 1 / 3, 0, 2 / 5]

/-- The constants of `Gap212.cutSixSevenOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutSixSevenOver₂Const : Fin 4 → ℝ := ![0, -1 / 3, 0, -2 / 5]

/-- **Cell `(6,7)`, the low half's certificate 1.**

Block bounds `7683 / 25000`, `479 / 6250`, `213 / 6250`, `86 / 1875`.
Valid on `4 / 625 < ω₀` and on
`8503 / 25000 + 8ω₀ + ϵ ≤ γ ≤ 1323 / 3125 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3961200 + ϵ, 0.4093600 - ϵ]`. The cut is at `t = 3 / 50`. -/
theorem admitsPartition₄_cellSixSeven_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 8503 / 25000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1323 / 3125 - 2 * ω₀ - slack)
    {y : Fin (6 + 7) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (127 / 625) 6 7 (41 / 2500))
    (hcut : ∀ i : Fin (6 + 7), 6 ≤ (i : ℕ) → y i ≤ 3 / 50) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_int (by norm_num) hy (by norm_num) hcut cutSixSevenUnder₁LowRanks
    cutSixSevenUnder₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![2, 1, 1, 1] ![3, 3, 0, 0] ![5, 5, 5, 3]
    (by decide) cutSixSevenUnder₁LowDens cutSixSevenUnder₁Dens cutSixSevenUnder₁Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutSixSevenUnder₁LowRanks,
    cutSixSevenUnder₁Ranks, cutSixSevenUnder₁LowDens, cutSixSevenUnder₁Dens,
    cutSixSevenUnder₁Const] <;> linarith

/-- **Cell `(6,7)`, the low half's certificate 2.**

Block bounds `2189 / 7000`, `3 / 50`, `213 / 6250`, `86 / 1875`.
Valid on `4 / 625 < ω₀` and on
`12093 / 35000 + 8ω₀ + ϵ ≤ γ ≤ 11 / 25 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4015143 + ϵ, 0.4260000 - ϵ]`. The cut is at `t = 3 / 50`. -/
theorem admitsPartition₄_cellSixSeven_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 12093 / 35000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 11 / 25 - 2 * ω₀ - slack)
    {y : Fin (6 + 7) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (127 / 625) 6 7 (41 / 2500))
    (hcut : ∀ i : Fin (6 + 7), 6 ≤ (i : ℕ) → y i ≤ 3 / 50) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_int (by norm_num) hy (by norm_num) hcut cutSixSevenUnder₂LowRanks
    cutSixSevenUnder₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![4, 0, 1, 1] ![0, 1, 0, 0] ![7, 1, 5, 3]
    (by decide) cutSixSevenUnder₂LowDens cutSixSevenUnder₂Dens cutSixSevenUnder₂Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutSixSevenUnder₂LowRanks,
    cutSixSevenUnder₂Ranks, cutSixSevenUnder₂LowDens, cutSixSevenUnder₂Dens,
    cutSixSevenUnder₂Const] <;> linarith

/-- **Cell `(6,7)`, the low half's certificate 3.**

Block bounds `3333 / 10000`, `254 / 4375`, `213 / 6250`, `86 / 1875`.
Valid on `4 / 625 < ω₀` and on
`3661 / 10000 + 8ω₀ + ϵ ≤ γ ≤ 3867 / 8750 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4221000 + ϵ, 0.4279429 - ϵ]`. The cut is at `t = 3 / 50`. -/
theorem admitsPartition₄_cellSixSeven_under₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3661 / 10000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 3867 / 8750 - 2 * ω₀ - slack)
    {y : Fin (6 + 7) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (127 / 625) 6 7 (41 / 2500))
    (hcut : ∀ i : Fin (6 + 7), 6 ≤ (i : ℕ) → y i ≤ 3 / 50) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_int (by norm_num) hy (by norm_num) hcut cutSixSevenUnder₃LowRanks
    cutSixSevenUnder₃Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 2, 1, 1] ![6, 0, 0, 0] ![4, 7, 5, 3]
    (by decide) cutSixSevenUnder₃LowDens cutSixSevenUnder₃Dens cutSixSevenUnder₃Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutSixSevenUnder₃LowRanks,
    cutSixSevenUnder₃Ranks, cutSixSevenUnder₃LowDens, cutSixSevenUnder₃Dens,
    cutSixSevenUnder₃Const] <;> linarith

/-- **Cell `(6,7)`, the high half's certificate 1.**

Block bounds `1507 / 5000`, `179 / 2500`, `983 / 30000`, `317 / 6250`.
Valid on `4 / 625 < ω₀` and on
`1671 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 1071 / 2500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3902000 + ϵ, 0.4144000 - ϵ]`. The cut is at `t = 3 / 50`. -/
theorem admitsPartition₄_cellSixSeven_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1671 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1071 / 2500 - 2 * ω₀ - slack)
    {y : Fin (6 + 7) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (127 / 625) 6 7 (41 / 2500))
    (hcut : ∃ i : Fin (6 + 7), 6 ≤ (i : ℕ) ∧ 3 / 50 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_int (by norm_num) hy (by norm_num) hcut cutSixSevenOver₁LowRanks
    cutSixSevenOver₁Ranks ![1, 0, 1, 0] ![1, 1, 6, 1] ![1, 1, 0, 2] ![0, -1, 0, -2] ![1, 2, 1, 5]
    (by decide) cutSixSevenOver₁LowDens cutSixSevenOver₁Dens cutSixSevenOver₁Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutSixSevenOver₁LowRanks,
    cutSixSevenOver₁Ranks, cutSixSevenOver₁LowDens, cutSixSevenOver₁Dens,
    cutSixSevenOver₁Const] <;> linarith

/-- **Cell `(6,7)`, the high half's certificate 2.**

Block bounds `1589 / 5000`, `179 / 3750`, `983 / 30000`, `317 / 6250`.
Valid on `4 / 625 < ω₀` and on
`1753 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 848 / 1875 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4066000 + ϵ, 0.4382667 - ϵ]`. The cut is at `t = 3 / 50`. -/
theorem admitsPartition₄_cellSixSeven_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1753 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 848 / 1875 - 2 * ω₀ - slack)
    {y : Fin (6 + 7) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (127 / 625) 6 7 (41 / 2500))
    (hcut : ∃ i : Fin (6 + 7), 6 ≤ (i : ℕ) ∧ 3 / 50 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_int (by norm_num) hy (by norm_num) hcut cutSixSevenOver₂LowRanks
    cutSixSevenOver₂Ranks ![1, 0, 1, 0] ![1, 1, 6, 1] ![1, 1, 0, 2] ![0, -1, 0, -2] ![1, 3, 1, 5]
    (by decide) cutSixSevenOver₂LowDens cutSixSevenOver₂Dens cutSixSevenOver₂Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutSixSevenOver₂LowRanks,
    cutSixSevenOver₂Ranks, cutSixSevenOver₂LowDens, cutSixSevenOver₂Dens,
    cutSixSevenOver₂Const] <;> linarith

/-- **Cell `(6,7)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,6}, B_{1,7}, 6, 7, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 3 / 50`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellSixSeven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 7) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (127 / 625) 6 7 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_cut (t := 3 / 50) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · rcases le_or_gt γ (1323 / 3125 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellSixSeven_under₁ hωlo (by linarith) h1 hy hcut
    · rcases le_or_gt γ (11 / 25 - 2 * ω₀ - slack) with h2 | h2
      · exact admitsPartition₄_cellSixSeven_under₂ hωlo (by linarith) h2 hy hcut
      · exact admitsPartition₄_cellSixSeven_under₃ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (1071 / 2500 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellSixSeven_over₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellSixSeven_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(6,7)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellSixSeven_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (6 + 7) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (127 / 625) 6 7 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellSixSeven_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(6,7)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 6 = gap212Cap 6 = 983 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellSixSeven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 7) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 6) (gap212Params.B j' 7) 6 7
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  simp only [gap212Params, gap212Cap] at hy; norm_num at hy
  exact admitsPartition₄_cellSixSeven_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(7,7)` -/

/-- The first group's rank sets for cell `(7,7)`, the low half's certificate 1. -/
def cutSevenSevenUnder₁LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenSevenUnder₁LowRanks`. -/
noncomputable def cutSevenSevenUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,7)`, the low half's certificate 1. -/
def cutSevenSevenUnder₁Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 3, 5}, {1, 6}, {4}, {2}]

/-- The slopes of `Gap212.cutSevenSevenUnder₁Ranks`. -/
noncomputable def cutSevenSevenUnder₁Dens : Fin 4 → ℝ := ![2 / 5, 1 / 5, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutSevenSevenUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutSevenSevenUnder₁Const : Fin 4 → ℝ := ![3 / 5, 3 / 5, 0, 0]

/-- The first group's rank sets for cell `(7,7)`, the low half's certificate 2. -/
def cutSevenSevenUnder₂LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenSevenUnder₂LowRanks`. -/
noncomputable def cutSevenSevenUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,7)`, the low half's certificate 2. -/
def cutSevenSevenUnder₂Ranks : Fin 4 → Finset (Fin 7) :=
  ![{1, 3, 5, 6}, {0}, {4}, {2}]

/-- The slopes of `Gap212.cutSevenSevenUnder₂Ranks`. -/
noncomputable def cutSevenSevenUnder₂Dens : Fin 4 → ℝ := ![4 / 7, 0, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutSevenSevenUnder₂Ranks`, nonnegative throughout. -/
noncomputable def cutSevenSevenUnder₂Const : Fin 4 → ℝ := ![0, 1, 0, 0]

/-- The first group's rank sets for cell `(7,7)`, the high half's certificate 1. -/
def cutSevenSevenOver₁LowRanks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2, 3, 4, 5}, ∅, {6}, ∅]

/-- The prefix densities of `Gap212.cutSevenSevenOver₁LowRanks`. -/
noncomputable def cutSevenSevenOver₁LowDens : Fin 4 → ℝ := ![1, 0, 1 / 7, 0]

/-- The second group's rank sets for cell `(7,7)`, the high half's certificate 1. -/
def cutSevenSevenOver₁Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1}, {2, 4, 5}, ∅, {3, 6}]

/-- The slopes of `Gap212.cutSevenSevenOver₁Ranks`. -/
noncomputable def cutSevenSevenOver₁Dens : Fin 4 → ℝ := ![1, 3 / 5, 0, 1 / 3]

/-- The constants of `Gap212.cutSevenSevenOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutSevenSevenOver₁Const : Fin 4 → ℝ := ![0, -3 / 5, 0, -1 / 3]

/-- The first group's rank sets for cell `(7,7)`, the high half's certificate 2. -/
def cutSevenSevenOver₂LowRanks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2, 3, 4, 5}, ∅, {6}, ∅]

/-- The prefix densities of `Gap212.cutSevenSevenOver₂LowRanks`. -/
noncomputable def cutSevenSevenOver₂LowDens : Fin 4 → ℝ := ![1, 0, 1 / 7, 0]

/-- The second group's rank sets for cell `(7,7)`, the high half's certificate 2. -/
def cutSevenSevenOver₂Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2}, {3, 5}, ∅, {4, 6}]

/-- The slopes of `Gap212.cutSevenSevenOver₂Ranks`. -/
noncomputable def cutSevenSevenOver₂Dens : Fin 4 → ℝ := ![1, 2 / 5, 0, 1 / 3]

/-- The constants of `Gap212.cutSevenSevenOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutSevenSevenOver₂Const : Fin 4 → ℝ := ![0, -2 / 5, 0, -1 / 3]

/-- The first group's rank sets for cell `(7,7)`, the low half's certificate 3. -/
def cutSevenSevenUnder₃LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenSevenUnder₃LowRanks`. -/
noncomputable def cutSevenSevenUnder₃LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,7)`, the low half's certificate 3. -/
def cutSevenSevenUnder₃Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 3, 6}, {1, 5}, {4}, {2}]

/-- The slopes of `Gap212.cutSevenSevenUnder₃Ranks`. -/
noncomputable def cutSevenSevenUnder₃Dens : Fin 4 → ℝ := ![1 / 3, 1 / 4, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutSevenSevenUnder₃Ranks`, nonnegative throughout. -/
noncomputable def cutSevenSevenUnder₃Const : Fin 4 → ℝ := ![2 / 3, 1 / 2, 0, 0]

/-- The first group's rank sets for cell `(7,7)`, the low half's certificate 4. -/
def cutSevenSevenUnder₄LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenSevenUnder₄LowRanks`. -/
noncomputable def cutSevenSevenUnder₄LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,7)`, the low half's certificate 4. -/
def cutSevenSevenUnder₄Ranks : Fin 4 → Finset (Fin 7) :=
  ![{1, 3, 5, 6}, {0}, {4}, {2}]

/-- The slopes of `Gap212.cutSevenSevenUnder₄Ranks`. -/
noncomputable def cutSevenSevenUnder₄Dens : Fin 4 → ℝ := ![4 / 7, 0, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutSevenSevenUnder₄Ranks`, nonnegative throughout. -/
noncomputable def cutSevenSevenUnder₄Const : Fin 4 → ℝ := ![0, 1, 0, 0]

/-- The first group's rank sets for cell `(7,7)`, the high half's certificate 3. -/
def cutSevenSevenOver₃LowRanks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2, 3, 4, 5}, ∅, {6}, ∅]

/-- The prefix densities of `Gap212.cutSevenSevenOver₃LowRanks`. -/
noncomputable def cutSevenSevenOver₃LowDens : Fin 4 → ℝ := ![1, 0, 1 / 7, 0]

/-- The second group's rank sets for cell `(7,7)`, the high half's certificate 3. -/
def cutSevenSevenOver₃Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1}, {2, 4, 6}, ∅, {3, 5}]

/-- The slopes of `Gap212.cutSevenSevenOver₃Ranks`. -/
noncomputable def cutSevenSevenOver₃Dens : Fin 4 → ℝ := ![1, 1 / 2, 0, 2 / 5]

/-- The constants of `Gap212.cutSevenSevenOver₃Ranks`, nonpositive throughout. -/
noncomputable def cutSevenSevenOver₃Const : Fin 4 → ℝ := ![0, -1 / 2, 0, -2 / 5]

/-- The first group's rank sets for cell `(7,7)`, the high half's certificate 4. -/
def cutSevenSevenOver₄LowRanks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2, 3, 4, 5}, ∅, {6}, ∅]

/-- The prefix densities of `Gap212.cutSevenSevenOver₄LowRanks`. -/
noncomputable def cutSevenSevenOver₄LowDens : Fin 4 → ℝ := ![1, 0, 1 / 7, 0]

/-- The second group's rank sets for cell `(7,7)`, the high half's certificate 4. -/
def cutSevenSevenOver₄Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2}, {3, 6}, ∅, {4, 5}]

/-- The slopes of `Gap212.cutSevenSevenOver₄Ranks`. -/
noncomputable def cutSevenSevenOver₄Dens : Fin 4 → ℝ := ![1, 1 / 3, 0, 2 / 5]

/-- The constants of `Gap212.cutSevenSevenOver₄Ranks`, nonpositive throughout. -/
noncomputable def cutSevenSevenOver₄Const : Fin 4 → ℝ := ![0, -1 / 3, 0, -2 / 5]

/-- **Cell `(7,7)`, the low half's certificate 1.**

Block bounds `3909 / 12500`, `943 / 12500`, `213 / 6250`, `86 / 1875`.
Valid on `4 / 625 < ω₀` and on
`4319 / 12500 + 8ω₀ + ϵ ≤ γ ≤ 5307 / 12500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4015200 + ϵ, 0.4105600 - ϵ]`. The cut is at `t = 29 / 500`. -/
theorem admitsPartition₄_cellSevenSeven_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 4319 / 12500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 5307 / 12500 - 2 * ω₀ - slack)
    {y : Fin (7 + 7) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (127 / 625) 7 7 (41 / 2500))
    (hcut : ∀ i : Fin (7 + 7), 7 ≤ (i : ℕ) → y i ≤ 29 / 500) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_int (by norm_num) hy (by norm_num) hcut cutSevenSevenUnder₁LowRanks
    cutSevenSevenUnder₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![2, 1, 1, 1] ![3, 3, 0, 0] ![5, 5, 5, 3]
    (by decide) cutSevenSevenUnder₁LowDens cutSevenSevenUnder₁Dens cutSevenSevenUnder₁Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutSevenSevenUnder₁LowRanks,
    cutSevenSevenUnder₁Ranks, cutSevenSevenUnder₁LowDens, cutSevenSevenUnder₁Dens,
    cutSevenSevenUnder₁Const] <;> linarith

/-- **Cell `(7,7)`, the low half's certificate 2.**

Block bounds `1397 / 4375`, `29 / 500`, `213 / 6250`, `86 / 1875`.
Valid on `4 / 625 < ω₀` and on
`3081 / 8750 + 8ω₀ + ϵ ≤ γ ≤ 221 / 500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4081143 + ϵ, 0.4280000 - ϵ]`. The cut is at `t = 29 / 500`. -/
theorem admitsPartition₄_cellSevenSeven_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3081 / 8750 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 221 / 500 - 2 * ω₀ - slack)
    {y : Fin (7 + 7) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (127 / 625) 7 7 (41 / 2500))
    (hcut : ∀ i : Fin (7 + 7), 7 ≤ (i : ℕ) → y i ≤ 29 / 500) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_int (by norm_num) hy (by norm_num) hcut cutSevenSevenUnder₂LowRanks
    cutSevenSevenUnder₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![4, 0, 1, 1] ![0, 1, 0, 0] ![7, 1, 5, 3]
    (by decide) cutSevenSevenUnder₂LowDens cutSevenSevenUnder₂Dens cutSevenSevenUnder₂Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutSevenSevenUnder₂LowRanks,
    cutSevenSevenUnder₂Ranks, cutSevenSevenUnder₂LowDens, cutSevenSevenUnder₂Dens,
    cutSevenSevenUnder₂Const] <;> linarith

/-- **Cell `(7,7)`, the high half's certificate 1.**

Block bounds `77 / 250`, `483 / 6250`, `127 / 4375`, `121 / 2500`.
Valid on `4 / 625 < ω₀` and on
`213 / 625 + 8ω₀ + ϵ ≤ γ ≤ 1321 / 3125 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3968000 + ϵ, 0.4087200 - ϵ]`. The cut is at `t = 29 / 500`. -/
theorem admitsPartition₄_cellSevenSeven_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 213 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1321 / 3125 - 2 * ω₀ - slack)
    {y : Fin (7 + 7) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (127 / 625) 7 7 (41 / 2500))
    (hcut : ∃ i : Fin (7 + 7), 7 ≤ (i : ℕ) ∧ 29 / 500 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_int (by norm_num) hy (by norm_num) hcut cutSevenSevenOver₁LowRanks
    cutSevenSevenOver₁Ranks ![1, 0, 1, 0] ![1, 1, 7, 1] ![1, 3, 0, 1] ![0, -3, 0, -1] ![1, 5, 1, 3]
    (by decide) cutSevenSevenOver₁LowDens cutSevenSevenOver₁Dens cutSevenSevenOver₁Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutSevenSevenOver₁LowRanks,
    cutSevenSevenOver₁Ranks, cutSevenSevenOver₁LowDens, cutSevenSevenOver₁Dens,
    cutSevenSevenOver₁Const] <;> linarith

/-- **Cell `(7,7)`, the high half's certificate 2.**

Block bounds `811 / 2500`, `161 / 3125`, `127 / 4375`, `121 / 2500`.
Valid on `4 / 625 < ω₀` and on
`893 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 2803 / 6250 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4132000 + ϵ, 0.4344800 - ϵ]`. The cut is at `t = 29 / 500`. -/
theorem admitsPartition₄_cellSevenSeven_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 893 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2803 / 6250 - 2 * ω₀ - slack)
    {y : Fin (7 + 7) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (127 / 625) 7 7 (41 / 2500))
    (hcut : ∃ i : Fin (7 + 7), 7 ≤ (i : ℕ) ∧ 29 / 500 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_int (by norm_num) hy (by norm_num) hcut cutSevenSevenOver₂LowRanks
    cutSevenSevenOver₂Ranks ![1, 0, 1, 0] ![1, 1, 7, 1] ![1, 2, 0, 1] ![0, -2, 0, -1] ![1, 5, 1, 3]
    (by decide) cutSevenSevenOver₂LowDens cutSevenSevenOver₂Dens cutSevenSevenOver₂Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutSevenSevenOver₂LowRanks,
    cutSevenSevenOver₂Ranks, cutSevenSevenOver₂LowDens, cutSevenSevenOver₂Dens,
    cutSevenSevenOver₂Const] <;> linarith

/-- **Cell `(7,7)`, the low half's certificate 3.**

Block bounds `387 / 1250`, `757 / 10000`, `213 / 6250`, `86 / 1875`.
Valid on `131 / 20000 < ω₀` and on
`214 / 625 + 8ω₀ + ϵ ≤ γ ≤ 4243 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3984000 + ϵ, 0.4103000 - ϵ]`. The cut is at `t = 29 / 500`. -/
theorem admitsPartition₄_cellSevenSeven_under₃ {γ ω₀ : ℝ} (hωlo : 131 / 20000 < ω₀)
    (hγlo : 214 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4243 / 10000 - 2 * ω₀ - slack)
    {y : Fin (7 + 7) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (127 / 625) 7 7 (41 / 2500))
    (hcut : ∀ i : Fin (7 + 7), 7 ≤ (i : ℕ) → y i ≤ 29 / 500) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_int (by norm_num) hy (by norm_num) hcut cutSevenSevenUnder₃LowRanks
    cutSevenSevenUnder₃Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 1, 1] ![2, 2, 0, 0] ![3, 4, 5, 3]
    (by decide) cutSevenSevenUnder₃LowDens cutSevenSevenUnder₃Dens cutSevenSevenUnder₃Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutSevenSevenUnder₃LowRanks,
    cutSevenSevenUnder₃Ranks, cutSevenSevenUnder₃LowDens, cutSevenSevenUnder₃Dens,
    cutSevenSevenUnder₃Const] <;> linarith

/-- **Cell `(7,7)`, the low half's certificate 4.**

Block bounds `1397 / 4375`, `29 / 500`, `213 / 6250`, `86 / 1875`.
Valid on `131 / 20000 < ω₀` and on
`3081 / 8750 + 8ω₀ + ϵ ≤ γ ≤ 221 / 500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4081143 + ϵ, 0.4280000 - ϵ]`. The cut is at `t = 29 / 500`. -/
theorem admitsPartition₄_cellSevenSeven_under₄ {γ ω₀ : ℝ} (hωlo : 131 / 20000 < ω₀)
    (hγlo : 3081 / 8750 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 221 / 500 - 2 * ω₀ - slack)
    {y : Fin (7 + 7) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (127 / 625) 7 7 (41 / 2500))
    (hcut : ∀ i : Fin (7 + 7), 7 ≤ (i : ℕ) → y i ≤ 29 / 500) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_int (by norm_num) hy (by norm_num) hcut cutSevenSevenUnder₄LowRanks
    cutSevenSevenUnder₄Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![4, 0, 1, 1] ![0, 1, 0, 0] ![7, 1, 5, 3]
    (by decide) cutSevenSevenUnder₄LowDens cutSevenSevenUnder₄Dens cutSevenSevenUnder₄Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutSevenSevenUnder₄LowRanks,
    cutSevenSevenUnder₄Ranks, cutSevenSevenUnder₄LowDens, cutSevenSevenUnder₄Dens,
    cutSevenSevenUnder₄Const] <;> linarith

/-- **Cell `(7,7)`, the high half's certificate 3.**

Block bounds `77 / 250`, `363 / 5000`, `127 / 4375`, `161 / 3125`.
Valid on `131 / 20000 < ω₀` and on
`213 / 625 + 8ω₀ + ϵ ≤ γ ≤ 2137 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3968000 + ϵ, 0.4134000 - ϵ]`. The cut is at `t = 29 / 500`. -/
theorem admitsPartition₄_cellSevenSeven_over₃ {γ ω₀ : ℝ} (hωlo : 131 / 20000 < ω₀)
    (hγlo : 213 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2137 / 5000 - 2 * ω₀ - slack)
    {y : Fin (7 + 7) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (127 / 625) 7 7 (41 / 2500))
    (hcut : ∃ i : Fin (7 + 7), 7 ≤ (i : ℕ) ∧ 29 / 500 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_int (by norm_num) hy (by norm_num) hcut cutSevenSevenOver₃LowRanks
    cutSevenSevenOver₃Ranks ![1, 0, 1, 0] ![1, 1, 7, 1] ![1, 1, 0, 2] ![0, -1, 0, -2] ![1, 2, 1, 5]
    (by decide) cutSevenSevenOver₃LowDens cutSevenSevenOver₃Dens cutSevenSevenOver₃Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutSevenSevenOver₃LowRanks,
    cutSevenSevenOver₃Ranks, cutSevenSevenOver₃LowDens, cutSevenSevenOver₃Dens,
    cutSevenSevenOver₃Const] <;> linarith

/-- **Cell `(7,7)`, the high half's certificate 4.**

Block bounds `811 / 2500`, `121 / 2500`, `127 / 4375`, `161 / 3125`.
Valid on `131 / 20000 < ω₀` and on
`893 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 1129 / 2500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4132000 + ϵ, 0.4376000 - ϵ]`. The cut is at `t = 29 / 500`. -/
theorem admitsPartition₄_cellSevenSeven_over₄ {γ ω₀ : ℝ} (hωlo : 131 / 20000 < ω₀)
    (hγlo : 893 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1129 / 2500 - 2 * ω₀ - slack)
    {y : Fin (7 + 7) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (127 / 625) 7 7 (41 / 2500))
    (hcut : ∃ i : Fin (7 + 7), 7 ≤ (i : ℕ) ∧ 29 / 500 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_int (by norm_num) hy (by norm_num) hcut cutSevenSevenOver₄LowRanks
    cutSevenSevenOver₄Ranks ![1, 0, 1, 0] ![1, 1, 7, 1] ![1, 1, 0, 2] ![0, -1, 0, -2] ![1, 3, 1, 5]
    (by decide) cutSevenSevenOver₄LowDens cutSevenSevenOver₄Dens cutSevenSevenOver₄Const
    (capD γ ω₀ ·) ?_ ?_ ?_ ?_ ?_
  all_goals intro k; fin_cases k <;> simp [capD, hδ, cutSevenSevenOver₄LowRanks,
    cutSevenSevenOver₄Ranks, cutSevenSevenOver₄LowDens, cutSevenSevenOver₄Dens,
    cutSevenSevenOver₄Const] <;> linarith

/-- **Cell `(7,7)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,7}, B_{1,7}, 7, 7, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 29 / 500`, then a `γ` split on each half.
The band itself is split at `ω₀ = 131 / 20000`, because the certificate the
top of the band needs has a bin-3 row above the band floor's capacity `8 · 4/625`. -/
theorem admitsPartition₄_cellSevenSeven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (7 + 7) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (127 / 625) 7 7 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt ω₀ (131 / 20000) with hw1 | hw1
  · refine admitsPartition₄_of_cut (t := 29 / 500) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
    · rcases le_or_gt γ (5307 / 12500 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellSevenSeven_under₁ hωlo (by linarith) h1 hy hcut
      · exact admitsPartition₄_cellSevenSeven_under₂ hωlo (by linarith) (by linarith) hy hcut
    · rcases le_or_gt γ (1321 / 3125 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellSevenSeven_over₁ hωlo (by linarith) h1 hy hcut
      · exact admitsPartition₄_cellSevenSeven_over₂ hωlo (by linarith) (by linarith) hy hcut
  · refine admitsPartition₄_of_cut (t := 29 / 500) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
    · rcases le_or_gt γ (4243 / 10000 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellSevenSeven_under₃ hw1 (by linarith) h1 hy hcut
      · exact admitsPartition₄_cellSevenSeven_under₄ hw1 (by linarith) (by linarith) hy hcut
    · rcases le_or_gt γ (2137 / 5000 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellSevenSeven_over₃ hw1 (by linarith) h1 hy hcut
      · exact admitsPartition₄_cellSevenSeven_over₄ hw1 (by linarith) (by linarith) hy hcut

/-- **Cell `(7,7)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellSevenSeven_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (7 + 7) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (127 / 625) 7 7 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellSevenSeven_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(7,7)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 7 = gap212Cap 7 = 127 / 625` at every stratum `j`. -/
theorem admitsPartition₄_cellSevenSeven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (7 + 7) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 7) (gap212Params.B j' 7) 7 7
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  simp only [gap212Params, gap212Cap] at hy; norm_num at hy
  exact admitsPartition₄_cellSevenSeven_band hωlo hωhi hγlo hγhi hy

/-- The hypotheses of the band theorems above are satisfiable: the chamber point `ω₀ = 7/1000`,
`γ = 2/5` and the constant profile `δ = 41/2500` meet all of them. -/
theorem cellsCut_hypotheses_satisfiable :
    (4 / 625 < (7 / 1000 : ℝ) ∧ (2 / 5 - slack : ℝ) ≤ 2 / 5 ∧
        (2 / 5 : ℝ) ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (397 / 2500 : ℝ) (7 / 40) 2 3 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (7 / 40 : ℝ) (917 / 5000) 3 4 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (7 / 40 : ℝ) (953 / 5000) 3 5 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (917 / 5000 : ℝ) (953 / 5000) 4 5 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (983 / 5000 : ℝ) (127 / 625) 6 7 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (127 / 625 : ℝ) (127 / 625) 7 7 (41 / 2500) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine ⟨⟨by norm_num, by rw [hsv]; norm_num, by rw [hδ, hsv]; norm_num⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals exact ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
    by rw [Finset.sum_const, card_lowGroup]; norm_num,
    by rw [Finset.sum_const, card_highGroup]; norm_num⟩

end Gap212
