/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCut
public import Gap212.Packing.SortedCell

/-!
# Three cells closed by a single cut

Three of the twenty cells that the uncut rank reading covers at no level of the band close on the
whole band by one cut at one threshold:

    (6,8) at t = 1/25      (8,9) at t = 9/200      (9,9) at t = 9/200

`(6,8)` closes band-wide at `t = 1/25`, the same numeral that closes `(10,10)` in
`Gap212.Packing.SortedCellCut`. `t = 1/25` covers `(8,9)` and `(9,9)` only on the sub-band
`[267500001/40000000000, 7/1000]`; at `t = 9/200` both close everywhere, `(8,9)` with two
certificates on each half and `(9,9)` with three on the low half and two on the high, and neither
needs a case analysis in `ω₀`.

## The instrument

`Gap212.Packing.admitsPartition₄_of_cut` splits on the second group's largest coordinate against
the threshold, which is fixed before `γ` and before the level. On the low half every coordinate of
that group is at most `t`, so a bin's affine majorant may carry a nonnegative constant; on the high
half some coordinate is at least `t`, so the constant must be nonpositive. Each half then chains
rank certificates across the chamber's `γ`-range `[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`.

`(8,9)`'s low half is where the cut earns its keep visibly: its first certificate puts the second
group's ranks `{0,8}` in bin 1 at slope `1/8` and constant `7/8`, a majorant that is worthless
without the cut — the constant is paid at `t - δ`, which is `0` when `t = δ` — and worth
`7/8 · (t - δ)` with it.

## The twenty-nine cells the uncut reading misses

Sixteen are in `Gap212.Packing.SortedCellCut`, `SortedCellsCut`, `SortedCellsGamma`,
`SortedCellsMid` and `SortedCellsRest`, three are here, nine are in
`Gap212.Packing.SortedCellsSub`, and `(8,8)` is in `Gap212.Packing.SortedCellsEight`. No
single threshold on the largest coordinate closes `(8,8)`: two points of the level `13/2000` have
disjoint closing windows, so no threshold serves both.
-/

@[expose] public section

namespace Gap212

open Finset Gap212.Packing


/-! ## Cell `(6,8)` -/

/-- The first group's rank sets for cell `(6,8)`, the low half's certificate 1. -/
def cutSixEightUnder₁LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSixEightUnder₁LowRanks`. -/
noncomputable def cutSixEightUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,8)`, the low half's certificate 1. -/
def cutSixEightUnder₁Ranks : Fin 4 → Finset (Fin 8) :=
  ![{1, 3, 5, 6}, {4, 7}, {0}, {2}]

/-- The slopes of `Gap212.cutSixEightUnder₁Ranks`. -/
noncomputable def cutSixEightUnder₁Dens : Fin 4 → ℝ := ![4 / 7, 1 / 4, 0, 0]

/-- The constants of `Gap212.cutSixEightUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutSixEightUnder₁Const : Fin 4 → ℝ := ![0, 0, 1, 1]

/-- The first group's rank sets for cell `(6,8)`, the high half's certificate 1. -/
def cutSixEightOver₁LowRanks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2, 3, 4}, ∅, {5}, ∅]

/-- The prefix densities of `Gap212.cutSixEightOver₁LowRanks`. -/
noncomputable def cutSixEightOver₁LowDens : Fin 4 → ℝ := ![1, 0, 1 / 6, 0]

/-- The second group's rank sets for cell `(6,8)`, the high half's certificate 1. -/
def cutSixEightOver₁Ranks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1, 2}, {3, 5, 7}, ∅, {4, 6}]

/-- The slopes of `Gap212.cutSixEightOver₁Ranks`. -/
noncomputable def cutSixEightOver₁Dens : Fin 4 → ℝ := ![1, 3 / 7, 0, 1 / 3]

/-- The constants of `Gap212.cutSixEightOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutSixEightOver₁Const : Fin 4 → ℝ := ![0, -3 / 7, 0, -1 / 3]

/-- The first group's rank sets for cell `(6,8)`, the high half's certificate 2. -/
def cutSixEightOver₂LowRanks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2, 3, 4}, ∅, {5}, ∅]

/-- The prefix densities of `Gap212.cutSixEightOver₂LowRanks`. -/
noncomputable def cutSixEightOver₂LowDens : Fin 4 → ℝ := ![1, 0, 1 / 6, 0]

/-- The second group's rank sets for cell `(6,8)`, the high half's certificate 2. -/
def cutSixEightOver₂Ranks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1, 2, 3}, {4, 7}, ∅, {5, 6}]

/-- The slopes of `Gap212.cutSixEightOver₂Ranks`. -/
noncomputable def cutSixEightOver₂Dens : Fin 4 → ℝ := ![1, 2 / 7, 0, 1 / 3]

/-- The constants of `Gap212.cutSixEightOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutSixEightOver₂Const : Fin 4 → ℝ := ![0, -2 / 7, 0, -1 / 3]

/-- **Cell `(6,8)`, the low half's certificate 1.**

Block bounds `10721 / 35000`, `521 / 10000`, `1 / 25`, `1 / 25`.
Valid on `4 / 625 < ω₀` and on
`11869 / 35000 + 8ω₀ + ϵ ≤ γ ≤ 4479 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3951143 + ϵ, 0.4339000 - ϵ]`. The cut is at `t = 1 / 25`. -/
theorem admitsPartition₄_cellSixEight_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 11869 / 35000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4479 / 10000 - 2 * ω₀ - slack)
    {y : Fin (6 + 8) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (521 / 2500) 6 8 (41 / 2500))
    (hcut : ∀ i : Fin (6 + 8), 6 ≤ (i : ℕ) → y i ≤ 1 / 25) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutSixEightUnder₁LowRanks cutSixEightUnder₁Ranks ?_ ?_ ?_ ?_
    cutSixEightUnder₁LowDens cutSixEightUnder₁Dens cutSixEightUnder₁Const ?_ ?_ ?_ ?_ ?_
    (capD γ ω₀) ?_
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · intro k; fin_cases k <;> norm_num [cutSixEightUnder₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutSixEightUnder₁Dens]
  · intro k; fin_cases k <;> norm_num [cutSixEightUnder₁Const]
  · intro k; fin_cases k
    · simpa [cutSixEightUnder₁LowRanks, cutSixEightUnder₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSixEightUnder₁LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutSixEightUnder₁LowRanks, cutSixEightUnder₁LowDens]
  · intro k; fin_cases k
    · simpa [cutSixEightUnder₁Ranks, cutSixEightUnder₁Dens, cutSixEightUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSixEightUnder₁Ranks 0) 4 0 7 (by norm_num) (by decide)
    · simpa [cutSixEightUnder₁Ranks, cutSixEightUnder₁Dens, cutSixEightUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSixEightUnder₁Ranks 1) 1 0 4 (by norm_num) (by decide)
    · simpa [cutSixEightUnder₁Ranks, cutSixEightUnder₁Dens, cutSixEightUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSixEightUnder₁Ranks 2) 0 1 1 (by norm_num) (by decide)
    · simpa [cutSixEightUnder₁Ranks, cutSixEightUnder₁Dens, cutSixEightUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSixEightUnder₁Ranks 3) 0 1 1 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutSixEightUnder₁LowRanks, cutSixEightUnder₁Ranks,
      cutSixEightUnder₁LowDens, cutSixEightUnder₁Dens, cutSixEightUnder₁Const] <;> linarith

/-- **Cell `(6,8)`, the high half's certificate 1.**

Block bounds `1533 / 5000`, `1263 / 17500`, `983 / 30000`, `19 / 375`.
Valid on `4 / 625 < ω₀` and on
`1697 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 7487 / 17500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3954000 + ϵ, 0.4138286 - ϵ]`. The cut is at `t = 1 / 25`. -/
theorem admitsPartition₄_cellSixEight_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1697 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 7487 / 17500 - 2 * ω₀ - slack)
    {y : Fin (6 + 8) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (521 / 2500) 6 8 (41 / 2500))
    (hcut : ∃ i : Fin (6 + 8), 6 ≤ (i : ℕ) ∧ 1 / 25 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutSixEightOver₁LowRanks cutSixEightOver₁Ranks ?_ ?_ ?_ ?_
    cutSixEightOver₁LowDens cutSixEightOver₁Dens cutSixEightOver₁Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · intro k; fin_cases k <;> norm_num [cutSixEightOver₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutSixEightOver₁Dens]
  · intro k; fin_cases k <;> norm_num [cutSixEightOver₁Const]
  · intro k; fin_cases k
    · simpa [cutSixEightOver₁LowRanks, cutSixEightOver₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSixEightOver₁LowRanks 0) 1 1 (by norm_num) (by decide)
    · simp [cutSixEightOver₁LowRanks, cutSixEightOver₁LowDens]
    · simpa [cutSixEightOver₁LowRanks, cutSixEightOver₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSixEightOver₁LowRanks 2) 1 6 (by norm_num) (by decide)
    all_goals simp [cutSixEightOver₁LowRanks, cutSixEightOver₁LowDens]
  · intro k; fin_cases k
    · simpa [cutSixEightOver₁Ranks, cutSixEightOver₁Dens, cutSixEightOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSixEightOver₁Ranks 0) 1 0 1 (by norm_num) (by decide)
    · simpa [cutSixEightOver₁Ranks, cutSixEightOver₁Dens, cutSixEightOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSixEightOver₁Ranks 1) 3 (-3) 7 (by norm_num) (by decide)
    · simp [cutSixEightOver₁Ranks, cutSixEightOver₁Dens, cutSixEightOver₁Const]
    · simpa [cutSixEightOver₁Ranks, cutSixEightOver₁Dens, cutSixEightOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSixEightOver₁Ranks 3) 1 (-1) 3 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutSixEightOver₁LowRanks, cutSixEightOver₁Ranks,
      cutSixEightOver₁LowDens, cutSixEightOver₁Dens, cutSixEightOver₁Const] <;> linarith

/-- **Cell `(6,8)`, the high half's certificate 2.**

Block bounds `323 / 1000`, `421 / 8750`, `983 / 30000`, `19 / 375`.
Valid on `4 / 625 < ω₀` and on
`1779 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 1977 / 4375 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4118000 + ϵ, 0.4378857 - ϵ]`. The cut is at `t = 1 / 25`. -/
theorem admitsPartition₄_cellSixEight_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1779 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1977 / 4375 - 2 * ω₀ - slack)
    {y : Fin (6 + 8) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (521 / 2500) 6 8 (41 / 2500))
    (hcut : ∃ i : Fin (6 + 8), 6 ≤ (i : ℕ) ∧ 1 / 25 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutSixEightOver₂LowRanks cutSixEightOver₂Ranks ?_ ?_ ?_ ?_
    cutSixEightOver₂LowDens cutSixEightOver₂Dens cutSixEightOver₂Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · intro k; fin_cases k <;> norm_num [cutSixEightOver₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutSixEightOver₂Dens]
  · intro k; fin_cases k <;> norm_num [cutSixEightOver₂Const]
  · intro k; fin_cases k
    · simpa [cutSixEightOver₂LowRanks, cutSixEightOver₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSixEightOver₂LowRanks 0) 1 1 (by norm_num) (by decide)
    · simp [cutSixEightOver₂LowRanks, cutSixEightOver₂LowDens]
    · simpa [cutSixEightOver₂LowRanks, cutSixEightOver₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSixEightOver₂LowRanks 2) 1 6 (by norm_num) (by decide)
    all_goals simp [cutSixEightOver₂LowRanks, cutSixEightOver₂LowDens]
  · intro k; fin_cases k
    · simpa [cutSixEightOver₂Ranks, cutSixEightOver₂Dens, cutSixEightOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSixEightOver₂Ranks 0) 1 0 1 (by norm_num) (by decide)
    · simpa [cutSixEightOver₂Ranks, cutSixEightOver₂Dens, cutSixEightOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSixEightOver₂Ranks 1) 2 (-2) 7 (by norm_num) (by decide)
    · simp [cutSixEightOver₂Ranks, cutSixEightOver₂Dens, cutSixEightOver₂Const]
    · simpa [cutSixEightOver₂Ranks, cutSixEightOver₂Dens, cutSixEightOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSixEightOver₂Ranks 3) 1 (-1) 3 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutSixEightOver₂LowRanks, cutSixEightOver₂Ranks,
      cutSixEightOver₂LowDens, cutSixEightOver₂Dens, cutSixEightOver₂Const] <;> linarith

/-- **Cell `(6,8)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,6}, B_{1,8}, 6, 8, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 1 / 25`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellSixEight_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 8) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (521 / 2500) 6 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_cut (t := 1 / 25) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · exact admitsPartition₄_cellSixEight_under₁ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (7487 / 17500 - 2 * ω₀ - slack) with h₁ | h₁
    · exact admitsPartition₄_cellSixEight_over₁ hωlo (by linarith) h₁ hy hcut
    · exact admitsPartition₄_cellSixEight_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(6,8)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellSixEight_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (6 + 8) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (521 / 2500) 6 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) :=
  admitsPartition₄_cellSixEight_band hp.2.2.1 hp.2.2.2 hp.1 hp.2.1 hy

/-- **Cell `(6,8)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 6 = gap212Cap 6 = 983 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellSixEight_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 8) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 6) (gap212Params.B j' 8) 6 8
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  change y ∈ Xi (gap212Cap 6) (gap212Cap 8) 6 8 (41 / 2500) at hy
  norm_num [gap212Cap] at hy
  exact admitsPartition₄_cellSixEight_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(8,9)` -/

/-- The first group's rank sets for cell `(8,9)`, the low half's certificate 1. -/
def cutEightNineUnder₁LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutEightNineUnder₁LowRanks`. -/
noncomputable def cutEightNineUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,9)`, the low half's certificate 1. -/
def cutEightNineUnder₁Ranks : Fin 4 → Finset (Fin 9) :=
  ![{1, 3, 5, 6}, {0, 8}, {2}, {4, 7}]

/-- The slopes of `Gap212.cutEightNineUnder₁Ranks`. -/
noncomputable def cutEightNineUnder₁Dens : Fin 4 → ℝ := ![4 / 7, 1 / 8, 1 / 3, 1 / 4]

/-- The constants of `Gap212.cutEightNineUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutEightNineUnder₁Const : Fin 4 → ℝ := ![0, 7 / 8, 0, 0]

/-- The first group's rank sets for cell `(8,9)`, the low half's certificate 2. -/
def cutEightNineUnder₂LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutEightNineUnder₂LowRanks`. -/
noncomputable def cutEightNineUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,9)`, the low half's certificate 2. -/
def cutEightNineUnder₂Ranks : Fin 4 → Finset (Fin 9) :=
  ![{1, 3, 5, 6, 8}, {0}, {2}, {4, 7}]

/-- The slopes of `Gap212.cutEightNineUnder₂Ranks`. -/
noncomputable def cutEightNineUnder₂Dens : Fin 4 → ℝ := ![4 / 7, 0, 1 / 3, 1 / 4]

/-- The constants of `Gap212.cutEightNineUnder₂Ranks`, nonnegative throughout. -/
noncomputable def cutEightNineUnder₂Const : Fin 4 → ℝ := ![0, 1, 0, 0]

/-- The first group's rank sets for cell `(8,9)`, the high half's certificate 1. -/
def cutEightNineOver₁LowRanks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1, 2, 3, 4, 5, 6}, ∅, ∅, {7}]

/-- The prefix densities of `Gap212.cutEightNineOver₁LowRanks`. -/
noncomputable def cutEightNineOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 1 / 8]

/-- The second group's rank sets for cell `(8,9)`, the high half's certificate 1. -/
def cutEightNineOver₁Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2}, {3, 5, 7}, {4, 8}, {6}]

/-- The slopes of `Gap212.cutEightNineOver₁Ranks`. -/
noncomputable def cutEightNineOver₁Dens : Fin 4 → ℝ := ![1, 3 / 7, 1 / 4, 1 / 6]

/-- The constants of `Gap212.cutEightNineOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutEightNineOver₁Const : Fin 4 → ℝ := ![0, -3 / 7, -1 / 4, -1 / 6]

/-- The first group's rank sets for cell `(8,9)`, the high half's certificate 2. -/
def cutEightNineOver₂LowRanks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1, 2, 3, 4, 5, 6}, ∅, ∅, {7}]

/-- The prefix densities of `Gap212.cutEightNineOver₂LowRanks`. -/
noncomputable def cutEightNineOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 1 / 8]

/-- The second group's rank sets for cell `(8,9)`, the high half's certificate 2. -/
def cutEightNineOver₂Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2, 3}, {4, 7}, {5, 8}, {6}]

/-- The slopes of `Gap212.cutEightNineOver₂Ranks`. -/
noncomputable def cutEightNineOver₂Dens : Fin 4 → ℝ := ![1, 2 / 7, 1 / 4, 1 / 6]

/-- The constants of `Gap212.cutEightNineOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutEightNineOver₂Const : Fin 4 → ℝ := ![0, -2 / 7, -1 / 4, -1 / 6]

/-- **Cell `(8,9)`, the low half's certificate 1.**

Block bounds `1089 / 3500`, `1319 / 20000`, `571 / 15000`, `981 / 20000`.
Valid on `4 / 625 < ω₀` and on
`6019 / 17500 + 8ω₀ + ϵ ≤ γ ≤ 8681 / 20000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3999429 + ϵ, 0.4200500 - ϵ]`. The cut is at `t = 9 / 200`. -/
theorem admitsPartition₄_cellEightNine_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 6019 / 17500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 8681 / 20000 - 2 * ω₀ - slack)
    {y : Fin (8 + 9) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1063 / 5000) 8 9 (41 / 2500))
    (hcut : ∀ i : Fin (8 + 9), 8 ≤ (i : ℕ) → y i ≤ 9 / 200) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutEightNineUnder₁LowRanks cutEightNineUnder₁Ranks ?_ ?_ ?_ ?_
    cutEightNineUnder₁LowDens cutEightNineUnder₁Dens cutEightNineUnder₁Const ?_ ?_ ?_ ?_ ?_
    (capD γ ω₀) ?_
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · intro k; fin_cases k <;> norm_num [cutEightNineUnder₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutEightNineUnder₁Dens]
  · intro k; fin_cases k <;> norm_num [cutEightNineUnder₁Const]
  · intro k; fin_cases k
    · simpa [cutEightNineUnder₁LowRanks, cutEightNineUnder₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutEightNineUnder₁LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutEightNineUnder₁LowRanks, cutEightNineUnder₁LowDens]
  · intro k; fin_cases k
    · simpa [cutEightNineUnder₁Ranks, cutEightNineUnder₁Dens, cutEightNineUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineUnder₁Ranks 0) 4 0 7 (by norm_num) (by decide)
    · simpa [cutEightNineUnder₁Ranks, cutEightNineUnder₁Dens, cutEightNineUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineUnder₁Ranks 1) 1 7 8 (by norm_num) (by decide)
    · simpa [cutEightNineUnder₁Ranks, cutEightNineUnder₁Dens, cutEightNineUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineUnder₁Ranks 2) 1 0 3 (by norm_num) (by decide)
    · simpa [cutEightNineUnder₁Ranks, cutEightNineUnder₁Dens, cutEightNineUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineUnder₁Ranks 3) 1 0 4 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutEightNineUnder₁LowRanks, cutEightNineUnder₁Ranks,
      cutEightNineUnder₁LowDens, cutEightNineUnder₁Dens, cutEightNineUnder₁Const] <;> linarith

/-- **Cell `(8,9)`, the low half's certificate 2.**

Block bounds `1433 / 4375`, `9 / 200`, `571 / 15000`, `981 / 20000`.
Valid on `4 / 625 < ω₀` and on
`3153 / 8750 + 8ω₀ + ϵ ≤ γ ≤ 91 / 200 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4163429 + ϵ, 0.4410000 - ϵ]`. The cut is at `t = 9 / 200`. -/
theorem admitsPartition₄_cellEightNine_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3153 / 8750 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 91 / 200 - 2 * ω₀ - slack)
    {y : Fin (8 + 9) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1063 / 5000) 8 9 (41 / 2500))
    (hcut : ∀ i : Fin (8 + 9), 8 ≤ (i : ℕ) → y i ≤ 9 / 200) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutEightNineUnder₂LowRanks cutEightNineUnder₂Ranks ?_ ?_ ?_ ?_
    cutEightNineUnder₂LowDens cutEightNineUnder₂Dens cutEightNineUnder₂Const ?_ ?_ ?_ ?_ ?_
    (capD γ ω₀) ?_
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · intro k; fin_cases k <;> norm_num [cutEightNineUnder₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutEightNineUnder₂Dens]
  · intro k; fin_cases k <;> norm_num [cutEightNineUnder₂Const]
  · intro k; fin_cases k
    · simpa [cutEightNineUnder₂LowRanks, cutEightNineUnder₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutEightNineUnder₂LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutEightNineUnder₂LowRanks, cutEightNineUnder₂LowDens]
  · intro k; fin_cases k
    · simpa [cutEightNineUnder₂Ranks, cutEightNineUnder₂Dens, cutEightNineUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineUnder₂Ranks 0) 4 0 7 (by norm_num) (by decide)
    · simpa [cutEightNineUnder₂Ranks, cutEightNineUnder₂Dens, cutEightNineUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineUnder₂Ranks 1) 0 1 1 (by norm_num) (by decide)
    · simpa [cutEightNineUnder₂Ranks, cutEightNineUnder₂Dens, cutEightNineUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineUnder₂Ranks 2) 1 0 3 (by norm_num) (by decide)
    · simpa [cutEightNineUnder₂Ranks, cutEightNineUnder₂Dens, cutEightNineUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineUnder₂Ranks 3) 1 0 4 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutEightNineUnder₂LowRanks, cutEightNineUnder₂Ranks,
      cutEightNineUnder₂LowDens, cutEightNineUnder₂Dens, cutEightNineUnder₂Const] <;> linarith

/-- **Cell `(8,9)`, the high half's certificate 1.**

Block bounds `1531 / 5000`, `81 / 1250`, `419 / 10000`, `2911 / 60000`.
Valid on `4 / 625 < ω₀` and on
`339 / 1000 + 8ω₀ + ϵ ≤ γ ≤ 272 / 625 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3950000 + ϵ, 0.4212000 - ϵ]`. The cut is at `t = 9 / 200`. -/
theorem admitsPartition₄_cellEightNine_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 339 / 1000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 272 / 625 - 2 * ω₀ - slack)
    {y : Fin (8 + 9) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1063 / 5000) 8 9 (41 / 2500))
    (hcut : ∃ i : Fin (8 + 9), 8 ≤ (i : ℕ) ∧ 9 / 200 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutEightNineOver₁LowRanks cutEightNineOver₁Ranks ?_ ?_ ?_ ?_
    cutEightNineOver₁LowDens cutEightNineOver₁Dens cutEightNineOver₁Const ?_ ?_ ?_ ?_ ?_
    (capD γ ω₀) ?_
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · intro k; fin_cases k <;> norm_num [cutEightNineOver₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutEightNineOver₁Dens]
  · intro k; fin_cases k <;> norm_num [cutEightNineOver₁Const]
  · intro k; fin_cases k
    · simpa [cutEightNineOver₁LowRanks, cutEightNineOver₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutEightNineOver₁LowRanks 0) 1 1 (by norm_num) (by decide)
    · simp [cutEightNineOver₁LowRanks, cutEightNineOver₁LowDens]
    · simp [cutEightNineOver₁LowRanks, cutEightNineOver₁LowDens]
    · simpa [cutEightNineOver₁LowRanks, cutEightNineOver₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutEightNineOver₁LowRanks 3) 1 8 (by norm_num) (by decide)
  · intro k; fin_cases k
    · simpa [cutEightNineOver₁Ranks, cutEightNineOver₁Dens, cutEightNineOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineOver₁Ranks 0) 1 0 1 (by norm_num) (by decide)
    · simpa [cutEightNineOver₁Ranks, cutEightNineOver₁Dens, cutEightNineOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineOver₁Ranks 1) 3 (-3) 7 (by norm_num) (by decide)
    · simpa [cutEightNineOver₁Ranks, cutEightNineOver₁Dens, cutEightNineOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineOver₁Ranks 2) 1 (-1) 4 (by norm_num) (by decide)
    · simpa [cutEightNineOver₁Ranks, cutEightNineOver₁Dens, cutEightNineOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineOver₁Ranks 3) 1 (-1) 6 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutEightNineOver₁LowRanks, cutEightNineOver₁Ranks,
      cutEightNineOver₁LowDens, cutEightNineOver₁Dens, cutEightNineOver₁Const] <;> linarith

/-- **Cell `(8,9)`, the high half's certificate 2.**

Block bounds `1613 / 5000`, `27 / 625`, `419 / 10000`, `2911 / 60000`.
Valid on `4 / 625 < ω₀` and on
`1777 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 571 / 1250 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4114000 + ϵ, 0.4428000 - ϵ]`. The cut is at `t = 9 / 200`. -/
theorem admitsPartition₄_cellEightNine_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1777 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 571 / 1250 - 2 * ω₀ - slack)
    {y : Fin (8 + 9) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1063 / 5000) 8 9 (41 / 2500))
    (hcut : ∃ i : Fin (8 + 9), 8 ≤ (i : ℕ) ∧ 9 / 200 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutEightNineOver₂LowRanks cutEightNineOver₂Ranks ?_ ?_ ?_ ?_
    cutEightNineOver₂LowDens cutEightNineOver₂Dens cutEightNineOver₂Const ?_ ?_ ?_ ?_ ?_
    (capD γ ω₀) ?_
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · intro k; fin_cases k <;> norm_num [cutEightNineOver₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutEightNineOver₂Dens]
  · intro k; fin_cases k <;> norm_num [cutEightNineOver₂Const]
  · intro k; fin_cases k
    · simpa [cutEightNineOver₂LowRanks, cutEightNineOver₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutEightNineOver₂LowRanks 0) 1 1 (by norm_num) (by decide)
    · simp [cutEightNineOver₂LowRanks, cutEightNineOver₂LowDens]
    · simp [cutEightNineOver₂LowRanks, cutEightNineOver₂LowDens]
    · simpa [cutEightNineOver₂LowRanks, cutEightNineOver₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutEightNineOver₂LowRanks 3) 1 8 (by norm_num) (by decide)
  · intro k; fin_cases k
    · simpa [cutEightNineOver₂Ranks, cutEightNineOver₂Dens, cutEightNineOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineOver₂Ranks 0) 1 0 1 (by norm_num) (by decide)
    · simpa [cutEightNineOver₂Ranks, cutEightNineOver₂Dens, cutEightNineOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineOver₂Ranks 1) 2 (-2) 7 (by norm_num) (by decide)
    · simpa [cutEightNineOver₂Ranks, cutEightNineOver₂Dens, cutEightNineOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineOver₂Ranks 2) 1 (-1) 4 (by norm_num) (by decide)
    · simpa [cutEightNineOver₂Ranks, cutEightNineOver₂Dens, cutEightNineOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutEightNineOver₂Ranks 3) 1 (-1) 6 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutEightNineOver₂LowRanks, cutEightNineOver₂Ranks,
      cutEightNineOver₂LowDens, cutEightNineOver₂Dens, cutEightNineOver₂Const] <;> linarith

/-- **Cell `(8,9)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,8}, B_{1,9}, 8, 9, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 9 / 200`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellEightNine_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (8 + 9) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1063 / 5000) 8 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_cut (t := 9 / 200) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · rcases le_or_gt γ (8681 / 20000 - 2 * ω₀ - slack) with h₁ | h₁
    · exact admitsPartition₄_cellEightNine_under₁ hωlo (by linarith) h₁ hy hcut
    · exact admitsPartition₄_cellEightNine_under₂ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (272 / 625 - 2 * ω₀ - slack) with h₁ | h₁
    · exact admitsPartition₄_cellEightNine_over₁ hωlo (by linarith) h₁ hy hcut
    · exact admitsPartition₄_cellEightNine_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(8,9)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellEightNine_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (8 + 9) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1063 / 5000) 8 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) :=
  admitsPartition₄_cellEightNine_band hp.2.2.1 hp.2.2.2 hp.1 hp.2.1 hy

/-- **Cell `(8,9)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 8 = gap212Cap 8 = 521 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellEightNine_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (8 + 9) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 8) (gap212Params.B j' 9) 8 9
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  change y ∈ Xi (gap212Cap 8) (gap212Cap 9) 8 9 (41 / 2500) at hy
  norm_num [gap212Cap] at hy
  exact admitsPartition₄_cellEightNine_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(9,9)` -/

/-- The first group's rank sets for cell `(9,9)`, the low half's certificate 1. -/
def cutNineNineUnder₁LowRanks : Fin 4 → Finset (Fin 9) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutNineNineUnder₁LowRanks`. -/
noncomputable def cutNineNineUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(9,9)`, the low half's certificate 1. -/
def cutNineNineUnder₁Ranks : Fin 4 → Finset (Fin 9) :=
  ![{1, 3, 5, 7}, {0, 6}, {2}, {4, 8}]

/-- The slopes of `Gap212.cutNineNineUnder₁Ranks`. -/
noncomputable def cutNineNineUnder₁Dens : Fin 4 → ℝ := ![1 / 2, 1 / 6, 1 / 3, 2 / 9]

/-- The constants of `Gap212.cutNineNineUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutNineNineUnder₁Const : Fin 4 → ℝ := ![0, 5 / 6, 0, 0]

/-- The first group's rank sets for cell `(9,9)`, the low half's certificate 2. -/
def cutNineNineUnder₂LowRanks : Fin 4 → Finset (Fin 9) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutNineNineUnder₂LowRanks`. -/
noncomputable def cutNineNineUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(9,9)`, the low half's certificate 2. -/
def cutNineNineUnder₂Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 2, 4, 6}, {1, 8}, {5}, {3, 7}]

/-- The slopes of `Gap212.cutNineNineUnder₂Ranks`. -/
noncomputable def cutNineNineUnder₂Dens : Fin 4 → ℝ := ![1 / 2, 1 / 7, 1 / 6, 1 / 4]

/-- The constants of `Gap212.cutNineNineUnder₂Ranks`, nonnegative throughout. -/
noncomputable def cutNineNineUnder₂Const : Fin 4 → ℝ := ![1 / 2, 5 / 7, 0, 0]

/-- The first group's rank sets for cell `(9,9)`, the low half's certificate 3. -/
def cutNineNineUnder₃LowRanks : Fin 4 → Finset (Fin 9) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutNineNineUnder₃LowRanks`. -/
noncomputable def cutNineNineUnder₃LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(9,9)`, the low half's certificate 3. -/
def cutNineNineUnder₃Ranks : Fin 4 → Finset (Fin 9) :=
  ![{1, 3, 5, 6, 8}, {0}, {2}, {4, 7}]

/-- The slopes of `Gap212.cutNineNineUnder₃Ranks`. -/
noncomputable def cutNineNineUnder₃Dens : Fin 4 → ℝ := ![4 / 7, 0, 1 / 3, 1 / 4]

/-- The constants of `Gap212.cutNineNineUnder₃Ranks`, nonnegative throughout. -/
noncomputable def cutNineNineUnder₃Const : Fin 4 → ℝ := ![0, 1, 0, 0]

/-- The first group's rank sets for cell `(9,9)`, the high half's certificate 1. -/
def cutNineNineOver₁LowRanks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2, 3, 4, 5, 6}, ∅, ∅, {7, 8}]

/-- The prefix densities of `Gap212.cutNineNineOver₁LowRanks`. -/
noncomputable def cutNineNineOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 2 / 9]

/-- The second group's rank sets for cell `(9,9)`, the high half's certificate 1. -/
def cutNineNineOver₁Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2, 3}, {4, 5, 7}, {6, 8}, ∅]

/-- The slopes of `Gap212.cutNineNineOver₁Ranks`. -/
noncomputable def cutNineNineOver₁Dens : Fin 4 → ℝ := ![1, 3 / 7, 1 / 4, 0]

/-- The constants of `Gap212.cutNineNineOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutNineNineOver₁Const : Fin 4 → ℝ := ![0, -3 / 7, -1 / 4, 0]

/-- The first group's rank sets for cell `(9,9)`, the high half's certificate 2. -/
def cutNineNineOver₂LowRanks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2, 3, 4, 5, 6}, ∅, ∅, {7, 8}]

/-- The prefix densities of `Gap212.cutNineNineOver₂LowRanks`. -/
noncomputable def cutNineNineOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 2 / 9]

/-- The second group's rank sets for cell `(9,9)`, the high half's certificate 2. -/
def cutNineNineOver₂Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2, 3, 4}, {5, 7}, {6, 8}, ∅]

/-- The slopes of `Gap212.cutNineNineOver₂Ranks`. -/
noncomputable def cutNineNineOver₂Dens : Fin 4 → ℝ := ![1, 2 / 7, 1 / 4, 0]

/-- The constants of `Gap212.cutNineNineOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutNineNineOver₂Const : Fin 4 → ℝ := ![0, -2 / 7, -1 / 4, 0]

/-- **Cell `(9,9)`, the low half's certificate 1.**

Block bounds `3107 / 10000`, `253 / 3750`, `571 / 15000`, `1063 / 22500`.
Valid on `4 / 625 < ω₀` and on
`687 / 2000 + 8ω₀ + ϵ ≤ γ ≤ 811 / 1875 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3995000 + ϵ, 0.4185333 - ϵ]`. The cut is at `t = 9 / 200`. -/
theorem admitsPartition₄_cellNineNine_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 687 / 2000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 811 / 1875 - 2 * ω₀ - slack)
    {y : Fin (9 + 9) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1063 / 5000) 9 9 (41 / 2500))
    (hcut : ∀ i : Fin (9 + 9), 9 ≤ (i : ℕ) → y i ≤ 9 / 200) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutNineNineUnder₁LowRanks cutNineNineUnder₁Ranks ?_ ?_ ?_ ?_
    cutNineNineUnder₁LowDens cutNineNineUnder₁Dens cutNineNineUnder₁Const ?_ ?_ ?_ ?_ ?_
    (capD γ ω₀) ?_
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · intro k; fin_cases k <;> norm_num [cutNineNineUnder₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutNineNineUnder₁Dens]
  · intro k; fin_cases k <;> norm_num [cutNineNineUnder₁Const]
  · intro k; fin_cases k
    · simpa [cutNineNineUnder₁LowRanks, cutNineNineUnder₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutNineNineUnder₁LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutNineNineUnder₁LowRanks, cutNineNineUnder₁LowDens]
  · intro k; fin_cases k
    · simpa [cutNineNineUnder₁Ranks, cutNineNineUnder₁Dens, cutNineNineUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineUnder₁Ranks 0) 1 0 2 (by norm_num) (by decide)
    · simpa [cutNineNineUnder₁Ranks, cutNineNineUnder₁Dens, cutNineNineUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineUnder₁Ranks 1) 1 5 6 (by norm_num) (by decide)
    · simpa [cutNineNineUnder₁Ranks, cutNineNineUnder₁Dens, cutNineNineUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineUnder₁Ranks 2) 1 0 3 (by norm_num) (by decide)
    · simpa [cutNineNineUnder₁Ranks, cutNineNineUnder₁Dens, cutNineNineUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineUnder₁Ranks 3) 2 0 9 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutNineNineUnder₁LowRanks, cutNineNineUnder₁Ranks,
      cutNineNineUnder₁LowDens, cutNineNineUnder₁Dens, cutNineNineUnder₁Const] <;> linarith

/-- **Cell `(9,9)`, the low half's certificate 2.**

Block bounds `13 / 40`, `547 / 8750`, `817 / 30000`, `981 / 20000`.
Valid on `4 / 625 < ω₀` and on
`1789 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 1914 / 4375 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4138000 + ϵ, 0.4234857 - ϵ]`. The cut is at `t = 9 / 200`. -/
theorem admitsPartition₄_cellNineNine_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1789 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1914 / 4375 - 2 * ω₀ - slack)
    {y : Fin (9 + 9) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1063 / 5000) 9 9 (41 / 2500))
    (hcut : ∀ i : Fin (9 + 9), 9 ≤ (i : ℕ) → y i ≤ 9 / 200) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutNineNineUnder₂LowRanks cutNineNineUnder₂Ranks ?_ ?_ ?_ ?_
    cutNineNineUnder₂LowDens cutNineNineUnder₂Dens cutNineNineUnder₂Const ?_ ?_ ?_ ?_ ?_
    (capD γ ω₀) ?_
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · intro k; fin_cases k <;> norm_num [cutNineNineUnder₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutNineNineUnder₂Dens]
  · intro k; fin_cases k <;> norm_num [cutNineNineUnder₂Const]
  · intro k; fin_cases k
    · simpa [cutNineNineUnder₂LowRanks, cutNineNineUnder₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutNineNineUnder₂LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutNineNineUnder₂LowRanks, cutNineNineUnder₂LowDens]
  · intro k; fin_cases k
    · simpa [cutNineNineUnder₂Ranks, cutNineNineUnder₂Dens, cutNineNineUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineUnder₂Ranks 0) 1 1 2 (by norm_num) (by decide)
    · simpa [cutNineNineUnder₂Ranks, cutNineNineUnder₂Dens, cutNineNineUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineUnder₂Ranks 1) 1 5 7 (by norm_num) (by decide)
    · simpa [cutNineNineUnder₂Ranks, cutNineNineUnder₂Dens, cutNineNineUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineUnder₂Ranks 2) 1 0 6 (by norm_num) (by decide)
    · simpa [cutNineNineUnder₂Ranks, cutNineNineUnder₂Dens, cutNineNineUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineUnder₂Ranks 3) 1 0 4 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutNineNineUnder₂LowRanks, cutNineNineUnder₂Ranks,
      cutNineNineUnder₂LowDens, cutNineNineUnder₂Dens, cutNineNineUnder₂Const] <;> linarith

/-- **Cell `(9,9)`, the low half's certificate 3.**

Block bounds `11611 / 35000`, `9 / 200`, `571 / 15000`, `981 / 20000`.
Valid on `4 / 625 < ω₀` and on
`12759 / 35000 + 8ω₀ + ϵ ≤ γ ≤ 91 / 200 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4205429 + ϵ, 0.4410000 - ϵ]`. The cut is at `t = 9 / 200`. -/
theorem admitsPartition₄_cellNineNine_under₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 12759 / 35000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 91 / 200 - 2 * ω₀ - slack)
    {y : Fin (9 + 9) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1063 / 5000) 9 9 (41 / 2500))
    (hcut : ∀ i : Fin (9 + 9), 9 ≤ (i : ℕ) → y i ≤ 9 / 200) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutNineNineUnder₃LowRanks cutNineNineUnder₃Ranks ?_ ?_ ?_ ?_
    cutNineNineUnder₃LowDens cutNineNineUnder₃Dens cutNineNineUnder₃Const ?_ ?_ ?_ ?_ ?_
    (capD γ ω₀) ?_
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · intro k; fin_cases k <;> norm_num [cutNineNineUnder₃LowDens]
  · intro k; fin_cases k <;> norm_num [cutNineNineUnder₃Dens]
  · intro k; fin_cases k <;> norm_num [cutNineNineUnder₃Const]
  · intro k; fin_cases k
    · simpa [cutNineNineUnder₃LowRanks, cutNineNineUnder₃LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutNineNineUnder₃LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutNineNineUnder₃LowRanks, cutNineNineUnder₃LowDens]
  · intro k; fin_cases k
    · simpa [cutNineNineUnder₃Ranks, cutNineNineUnder₃Dens, cutNineNineUnder₃Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineUnder₃Ranks 0) 4 0 7 (by norm_num) (by decide)
    · simpa [cutNineNineUnder₃Ranks, cutNineNineUnder₃Dens, cutNineNineUnder₃Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineUnder₃Ranks 1) 0 1 1 (by norm_num) (by decide)
    · simpa [cutNineNineUnder₃Ranks, cutNineNineUnder₃Dens, cutNineNineUnder₃Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineUnder₃Ranks 2) 1 0 3 (by norm_num) (by decide)
    · simpa [cutNineNineUnder₃Ranks, cutNineNineUnder₃Dens, cutNineNineUnder₃Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineUnder₃Ranks 3) 1 0 4 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutNineNineUnder₃LowRanks, cutNineNineUnder₃Ranks,
      cutNineNineUnder₃LowDens, cutNineNineUnder₃Dens, cutNineNineUnder₃Const] <;> linarith

/-- **Cell `(9,9)`, the high half's certificate 1.**

Block bounds `194 / 625`, `81 / 1250`, `419 / 10000`, `1063 / 22500`.
Valid on `4 / 625 < ω₀` and on
`429 / 1250 + 8ω₀ + ϵ ≤ γ ≤ 272 / 625 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3992000 + ϵ, 0.4212000 - ϵ]`. The cut is at `t = 9 / 200`. -/
theorem admitsPartition₄_cellNineNine_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 429 / 1250 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 272 / 625 - 2 * ω₀ - slack)
    {y : Fin (9 + 9) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1063 / 5000) 9 9 (41 / 2500))
    (hcut : ∃ i : Fin (9 + 9), 9 ≤ (i : ℕ) ∧ 9 / 200 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutNineNineOver₁LowRanks cutNineNineOver₁Ranks ?_ ?_ ?_ ?_
    cutNineNineOver₁LowDens cutNineNineOver₁Dens cutNineNineOver₁Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · intro k; fin_cases k <;> norm_num [cutNineNineOver₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutNineNineOver₁Dens]
  · intro k; fin_cases k <;> norm_num [cutNineNineOver₁Const]
  · intro k; fin_cases k
    · simpa [cutNineNineOver₁LowRanks, cutNineNineOver₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutNineNineOver₁LowRanks 0) 1 1 (by norm_num) (by decide)
    · simp [cutNineNineOver₁LowRanks, cutNineNineOver₁LowDens]
    · simp [cutNineNineOver₁LowRanks, cutNineNineOver₁LowDens]
    · simpa [cutNineNineOver₁LowRanks, cutNineNineOver₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutNineNineOver₁LowRanks 3) 2 9 (by norm_num) (by decide)
  · intro k; fin_cases k
    · simpa [cutNineNineOver₁Ranks, cutNineNineOver₁Dens, cutNineNineOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineOver₁Ranks 0) 1 0 1 (by norm_num) (by decide)
    · simpa [cutNineNineOver₁Ranks, cutNineNineOver₁Dens, cutNineNineOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineOver₁Ranks 1) 3 (-3) 7 (by norm_num) (by decide)
    · simpa [cutNineNineOver₁Ranks, cutNineNineOver₁Dens, cutNineNineOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineOver₁Ranks 2) 1 (-1) 4 (by norm_num) (by decide)
    · simp [cutNineNineOver₁Ranks, cutNineNineOver₁Dens, cutNineNineOver₁Const]
  · intro k; fin_cases k <;> simp [capD, hδ, cutNineNineOver₁LowRanks, cutNineNineOver₁Ranks,
      cutNineNineOver₁LowDens, cutNineNineOver₁Dens, cutNineNineOver₁Const] <;> linarith

/-- **Cell `(9,9)`, the high half's certificate 2.**

Block bounds `817 / 2500`, `27 / 625`, `419 / 10000`, `1063 / 22500`.
Valid on `4 / 625 < ω₀` and on
`899 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 571 / 1250 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4156000 + ϵ, 0.4428000 - ϵ]`. The cut is at `t = 9 / 200`. -/
theorem admitsPartition₄_cellNineNine_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 899 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 571 / 1250 - 2 * ω₀ - slack)
    {y : Fin (9 + 9) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1063 / 5000) 9 9 (41 / 2500))
    (hcut : ∃ i : Fin (9 + 9), 9 ≤ (i : ℕ) ∧ 9 / 200 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutNineNineOver₂LowRanks cutNineNineOver₂Ranks ?_ ?_ ?_ ?_
    cutNineNineOver₂LowDens cutNineNineOver₂Dens cutNineNineOver₂Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · decide
  · intro k l hkl; rw [Finset.disjoint_iff_inter_eq_empty]; revert hkl k l; decide
  · intro k; fin_cases k <;> norm_num [cutNineNineOver₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutNineNineOver₂Dens]
  · intro k; fin_cases k <;> norm_num [cutNineNineOver₂Const]
  · intro k; fin_cases k
    · simpa [cutNineNineOver₂LowRanks, cutNineNineOver₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutNineNineOver₂LowRanks 0) 1 1 (by norm_num) (by decide)
    · simp [cutNineNineOver₂LowRanks, cutNineNineOver₂LowDens]
    · simp [cutNineNineOver₂LowRanks, cutNineNineOver₂LowDens]
    · simpa [cutNineNineOver₂LowRanks, cutNineNineOver₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutNineNineOver₂LowRanks 3) 2 9 (by norm_num) (by decide)
  · intro k; fin_cases k
    · simpa [cutNineNineOver₂Ranks, cutNineNineOver₂Dens, cutNineNineOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineOver₂Ranks 0) 1 0 1 (by norm_num) (by decide)
    · simpa [cutNineNineOver₂Ranks, cutNineNineOver₂Dens, cutNineNineOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineOver₂Ranks 1) 2 (-2) 7 (by norm_num) (by decide)
    · simpa [cutNineNineOver₂Ranks, cutNineNineOver₂Dens, cutNineNineOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutNineNineOver₂Ranks 2) 1 (-1) 4 (by norm_num) (by decide)
    · simp [cutNineNineOver₂Ranks, cutNineNineOver₂Dens, cutNineNineOver₂Const]
  · intro k; fin_cases k <;> simp [capD, hδ, cutNineNineOver₂LowRanks, cutNineNineOver₂Ranks,
      cutNineNineOver₂LowDens, cutNineNineOver₂Dens, cutNineNineOver₂Const] <;> linarith

/-- **Cell `(9,9)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,9}, B_{1,9}, 9, 9, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 9 / 200`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellNineNine_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (9 + 9) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1063 / 5000) 9 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_cut (t := 9 / 200) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · rcases le_or_gt γ (811 / 1875 - 2 * ω₀ - slack) with h₁ | h₁
    · exact admitsPartition₄_cellNineNine_under₁ hωlo (by linarith) h₁ hy hcut
    · rcases le_or_gt γ (1914 / 4375 - 2 * ω₀ - slack) with h₂ | h₂
      · exact admitsPartition₄_cellNineNine_under₂ hωlo (by linarith) h₂ hy hcut
      · exact admitsPartition₄_cellNineNine_under₃ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (272 / 625 - 2 * ω₀ - slack) with h₁ | h₁
    · exact admitsPartition₄_cellNineNine_over₁ hωlo (by linarith) h₁ hy hcut
    · exact admitsPartition₄_cellNineNine_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(9,9)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellNineNine_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (9 + 9) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1063 / 5000) 9 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) :=
  admitsPartition₄_cellNineNine_band hp.2.2.1 hp.2.2.2 hp.1 hp.2.1 hy

/-- **Cell `(9,9)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 9 = gap212Cap 9 = 1063 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellNineNine_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (9 + 9) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 9) (gap212Params.B j' 9) 9 9
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  change y ∈ Xi (gap212Cap 9) (gap212Cap 9) 9 9 (41 / 2500) at hy
  norm_num [gap212Cap] at hy
  exact admitsPartition₄_cellNineNine_band hωlo hωhi hγlo hγhi hy

/-- The hypotheses of the band theorems above are satisfiable: the chamber point `ω₀ = 7/1000`,
`γ = 2/5` and the constant profile `δ = 41/2500` meet all of them. -/
theorem cellsPair_hypotheses_satisfiable :
    (4 / 625 < (7 / 1000 : ℝ) ∧ (2 / 5 - slack : ℝ) ≤ 2 / 5 ∧
        (2 / 5 : ℝ) ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (983 / 5000 : ℝ) (521 / 2500) 6 8 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (521 / 2500 : ℝ) (1063 / 5000) 8 9 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (1063 / 5000 : ℝ) (1063 / 5000) 9 9 (41 / 2500) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine ⟨⟨by norm_num, by norm_num [hsv], by norm_num [hδ, hsv]⟩, ?_, ?_, ?_⟩ <;>
    exact ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩, by rw [Finset.sum_const, card_lowGroup]; norm_num,
      by rw [Finset.sum_const, card_highGroup]; norm_num⟩

end Gap212
