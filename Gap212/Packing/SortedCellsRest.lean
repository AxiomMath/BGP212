/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCut
public import Gap212.Packing.SortedCell

/-!
# Four cells the uncut reading covers nowhere

The uncut rank reading of `Gap212.Packing.SortedCone` covers 62 of the 91 cells at every level
of the band and nine more on a sub-band; twenty it covers at no level at all. `(10,10)` of those
twenty is `Gap212.admitsPartition₄_cellTenTen_band`, eleven more are
`Gap212.Packing.SortedCellsCut`, `SortedCellsGamma` and `SortedCellsMid`, `(6,8)`, `(8,9)` and
`(9,9)` are `Gap212.Packing.SortedCellsPair`, `(8,8)` is
`Gap212.Packing.SortedCellsEight`, and these are the other four:

    (4,7) (5,7) (7,8) (7,9)

Each closes the whole band `(4/625, 7/1000]` over the whole chamber `γ`-range by the same
instrument: `Gap212.Packing.admitsPartition₄_of_cut` on the second group's largest coordinate at a
threshold fixed first, then a `γ` chain of rank certificates on each half. The thresholds are
`1/20` at `(4,7)`, `53/1000` at `(5,7)` and `9/200` at `(7,9)`; at `(7,8)` the threshold depends
on the region of `γ`, `31/500` below `γ = 7299/17500 - 2ω₀ - ϵ` and `51/1000` above it.
-/

@[expose] public section

namespace Gap212

open Finset Gap212.Packing


/-! ## Cell `(4,7)` -/

/-- The first group's rank sets for cell `(4,7)`, the low half's certificate 1. -/
def cutFourSevenUnder₁LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFourSevenUnder₁LowRanks`. -/
noncomputable def cutFourSevenUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,7)`, the low half's certificate 1. -/
def cutFourSevenUnder₁Ranks : Fin 4 → Finset (Fin 7) :=
  ![{1, 2, 4, 5}, {6}, {3}, {0}]

/-- The slopes of `Gap212.cutFourSevenUnder₁Ranks`. -/
noncomputable def cutFourSevenUnder₁Dens : Fin 4 → ℝ := ![2 / 3, 1 / 7, 1 / 4, 0]

/-- The constants of `Gap212.cutFourSevenUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutFourSevenUnder₁Const : Fin 4 → ℝ := ![0, 0, 0, 1]

/-- The first group's rank sets for cell `(4,7)`, the high half's certificate 1. -/
def cutFourSevenOver₁LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFourSevenOver₁LowRanks`. -/
noncomputable def cutFourSevenOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,7)`, the high half's certificate 1. -/
def cutFourSevenOver₁Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1}, {2, 4}, {5}, {3, 6}]

/-- The slopes of `Gap212.cutFourSevenOver₁Ranks`. -/
noncomputable def cutFourSevenOver₁Dens : Fin 4 → ℝ := ![1, 1 / 2, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutFourSevenOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutFourSevenOver₁Const : Fin 4 → ℝ := ![0, -1 / 2, -1 / 5, -1 / 3]

/-- The first group's rank sets for cell `(4,7)`, the high half's certificate 2. -/
def cutFourSevenOver₂LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFourSevenOver₂LowRanks`. -/
noncomputable def cutFourSevenOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,7)`, the high half's certificate 2. -/
def cutFourSevenOver₂Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2}, {5}, {4}, {3, 6}]

/-- The slopes of `Gap212.cutFourSevenOver₂Ranks`. -/
noncomputable def cutFourSevenOver₂Dens : Fin 4 → ℝ := ![1, 1 / 5, 1 / 4, 1 / 3]

/-- The constants of `Gap212.cutFourSevenOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutFourSevenOver₂Const : Fin 4 → ℝ := ![0, -1 / 5, -1 / 4, -1 / 3]

/-- **Cell `(4,7)`, the low half's certificate 1.**

Block bounds `4619 / 15000`, `127 / 4375`, `77 / 2000`, `1 / 20`.
Valid on `4 / 625 < ω₀` and on
`5111 / 15000 + 8ω₀ + ϵ ≤ γ ≤ 4121 / 8750 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3967333 + ϵ, 0.4569714 - ϵ]`. The cut is at `t = 1 / 20`. -/
theorem admitsPartition₄_cellFourSeven_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 5111 / 15000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4121 / 8750 - 2 * ω₀ - slack)
    {y : Fin (4 + 7) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (127 / 625) 4 7 (41 / 2500))
    (hcut : ∀ i : Fin (4 + 7), 4 ≤ (i : ℕ) → y i ≤ 1 / 20) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutFourSevenUnder₁LowRanks cutFourSevenUnder₁Ranks (by decide) (by decide) (by decide)
    (by decide) cutFourSevenUnder₁LowDens cutFourSevenUnder₁Dens cutFourSevenUnder₁Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFourSevenUnder₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutFourSevenUnder₁Dens]
  · intro k; fin_cases k <;> norm_num [cutFourSevenUnder₁Const]
  · intro k; fin_cases k
    · simpa [cutFourSevenUnder₁LowRanks, cutFourSevenUnder₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutFourSevenUnder₁LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutFourSevenUnder₁LowRanks, cutFourSevenUnder₁LowDens]
  · intro k; fin_cases k
    · simpa [cutFourSevenUnder₁Ranks, cutFourSevenUnder₁Dens, cutFourSevenUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFourSevenUnder₁Ranks 0) 2 0 3 (by norm_num) (by decide)
    · simpa [cutFourSevenUnder₁Ranks, cutFourSevenUnder₁Dens, cutFourSevenUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFourSevenUnder₁Ranks 1) 1 0 7 (by norm_num) (by decide)
    · simpa [cutFourSevenUnder₁Ranks, cutFourSevenUnder₁Dens, cutFourSevenUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFourSevenUnder₁Ranks 2) 1 0 4 (by norm_num) (by decide)
    · simpa [cutFourSevenUnder₁Ranks, cutFourSevenUnder₁Dens, cutFourSevenUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFourSevenUnder₁Ranks 3) 0 1 1 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutFourSevenUnder₁LowRanks, cutFourSevenUnder₁Ranks,
      cutFourSevenUnder₁LowDens, cutFourSevenUnder₁Dens, cutFourSevenUnder₁Const] <;> linarith

/-- **Cell `(4,7)`, the high half's certificate 1.**

Block bounds `1523 / 5000`, `301 / 5000`, `171 / 6250`, `383 / 7500`.
Valid on `4 / 625 < ω₀` and on
`1687 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 2199 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3934000 + ϵ, 0.4258000 - ϵ]`. The cut is at `t = 1 / 20`. -/
theorem admitsPartition₄_cellFourSeven_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1687 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2199 / 5000 - 2 * ω₀ - slack)
    {y : Fin (4 + 7) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (127 / 625) 4 7 (41 / 2500))
    (hcut : ∃ i : Fin (4 + 7), 4 ≤ (i : ℕ) ∧ 1 / 20 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutFourSevenOver₁LowRanks cutFourSevenOver₁Ranks (by decide) (by decide) (by decide)
    (by decide) cutFourSevenOver₁LowDens cutFourSevenOver₁Dens cutFourSevenOver₁Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFourSevenOver₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutFourSevenOver₁Dens]
  · intro k; fin_cases k <;> norm_num [cutFourSevenOver₁Const]
  · intro k; fin_cases k
    · simpa [cutFourSevenOver₁LowRanks, cutFourSevenOver₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutFourSevenOver₁LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutFourSevenOver₁LowRanks, cutFourSevenOver₁LowDens]
  · intro k; fin_cases k
    · simpa [cutFourSevenOver₁Ranks, cutFourSevenOver₁Dens, cutFourSevenOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFourSevenOver₁Ranks 0) 1 0 1 (by norm_num) (by decide)
    · simpa [cutFourSevenOver₁Ranks, cutFourSevenOver₁Dens, cutFourSevenOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFourSevenOver₁Ranks 1) 1 (-1) 2 (by norm_num) (by decide)
    · simpa [cutFourSevenOver₁Ranks, cutFourSevenOver₁Dens, cutFourSevenOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFourSevenOver₁Ranks 2) 1 (-1) 5 (by norm_num) (by decide)
    · simpa [cutFourSevenOver₁Ranks, cutFourSevenOver₁Dens, cutFourSevenOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFourSevenOver₁Ranks 3) 1 (-1) 3 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutFourSevenOver₁LowRanks, cutFourSevenOver₁Ranks,
      cutFourSevenOver₁LowDens, cutFourSevenOver₁Dens, cutFourSevenOver₁Const] <;> linarith

/-- **Cell `(4,7)`, the high half's certificate 2.**

Block bounds `321 / 1000`, `171 / 6250`, `301 / 10000`, `383 / 7500`.
Valid on `4 / 625 < ω₀` and on
`1769 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 1477 / 3125 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4098000 + ϵ, 0.4586400 - ϵ]`. The cut is at `t = 1 / 20`. -/
theorem admitsPartition₄_cellFourSeven_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1769 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1477 / 3125 - 2 * ω₀ - slack)
    {y : Fin (4 + 7) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (127 / 625) 4 7 (41 / 2500))
    (hcut : ∃ i : Fin (4 + 7), 4 ≤ (i : ℕ) ∧ 1 / 20 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutFourSevenOver₂LowRanks cutFourSevenOver₂Ranks (by decide) (by decide) (by decide)
    (by decide) cutFourSevenOver₂LowDens cutFourSevenOver₂Dens cutFourSevenOver₂Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFourSevenOver₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutFourSevenOver₂Dens]
  · intro k; fin_cases k <;> norm_num [cutFourSevenOver₂Const]
  · intro k; fin_cases k
    · simpa [cutFourSevenOver₂LowRanks, cutFourSevenOver₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutFourSevenOver₂LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutFourSevenOver₂LowRanks, cutFourSevenOver₂LowDens]
  · intro k; fin_cases k
    · simpa [cutFourSevenOver₂Ranks, cutFourSevenOver₂Dens, cutFourSevenOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFourSevenOver₂Ranks 0) 1 0 1 (by norm_num) (by decide)
    · simpa [cutFourSevenOver₂Ranks, cutFourSevenOver₂Dens, cutFourSevenOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFourSevenOver₂Ranks 1) 1 (-1) 5 (by norm_num) (by decide)
    · simpa [cutFourSevenOver₂Ranks, cutFourSevenOver₂Dens, cutFourSevenOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFourSevenOver₂Ranks 2) 1 (-1) 4 (by norm_num) (by decide)
    · simpa [cutFourSevenOver₂Ranks, cutFourSevenOver₂Dens, cutFourSevenOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFourSevenOver₂Ranks 3) 1 (-1) 3 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutFourSevenOver₂LowRanks, cutFourSevenOver₂Ranks,
      cutFourSevenOver₂LowDens, cutFourSevenOver₂Dens, cutFourSevenOver₂Const] <;> linarith

/-- **Cell `(4,7)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,4}, B_{1,7}, 4, 7, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 1 / 20`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellFourSeven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 7) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (127 / 625) 4 7 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_cut (t := 1 / 20) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · exact admitsPartition₄_cellFourSeven_under₁ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (2199 / 5000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellFourSeven_over₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellFourSeven_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(4,7)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellFourSeven_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (4 + 7) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (127 / 625) 4 7 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellFourSeven_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(4,7)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 4 = gap212Cap 4 = 917 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFourSeven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 7) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 4) (gap212Params.B j' 7) 4 7
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  simp only [gap212Params] at hy; norm_num [gap212Cap] at hy
  exact admitsPartition₄_cellFourSeven_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(5,7)` -/

/-- The first group's rank sets for cell `(5,7)`, the low half's certificate 1. -/
def cutFiveSevenUnder₁LowRanks : Fin 4 → Finset (Fin 5) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFiveSevenUnder₁LowRanks`. -/
noncomputable def cutFiveSevenUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(5,7)`, the low half's certificate 1. -/
def cutFiveSevenUnder₁Ranks : Fin 4 → Finset (Fin 7) :=
  ![{1, 3, 5, 6}, {0}, {4}, {2}]

/-- The slopes of `Gap212.cutFiveSevenUnder₁Ranks`. -/
noncomputable def cutFiveSevenUnder₁Dens : Fin 4 → ℝ := ![4 / 7, 0, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutFiveSevenUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutFiveSevenUnder₁Const : Fin 4 → ℝ := ![0, 1, 0, 0]

/-- The first group's rank sets for cell `(5,7)`, the high half's certificate 1. -/
def cutFiveSevenOver₁LowRanks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1, 2, 3}, ∅, {4}, ∅]

/-- The prefix densities of `Gap212.cutFiveSevenOver₁LowRanks`. -/
noncomputable def cutFiveSevenOver₁LowDens : Fin 4 → ℝ := ![1, 0, 1 / 5, 0]

/-- The second group's rank sets for cell `(5,7)`, the high half's certificate 1. -/
def cutFiveSevenOver₁Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1}, {2, 4, 5}, ∅, {3, 6}]

/-- The slopes of `Gap212.cutFiveSevenOver₁Ranks`. -/
noncomputable def cutFiveSevenOver₁Dens : Fin 4 → ℝ := ![1, 3 / 5, 0, 1 / 3]

/-- The constants of `Gap212.cutFiveSevenOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutFiveSevenOver₁Const : Fin 4 → ℝ := ![0, -3 / 5, 0, -1 / 3]

/-- The first group's rank sets for cell `(5,7)`, the high half's certificate 2. -/
def cutFiveSevenOver₂LowRanks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1, 2, 3}, ∅, {4}, ∅]

/-- The prefix densities of `Gap212.cutFiveSevenOver₂LowRanks`. -/
noncomputable def cutFiveSevenOver₂LowDens : Fin 4 → ℝ := ![1, 0, 1 / 5, 0]

/-- The second group's rank sets for cell `(5,7)`, the high half's certificate 2. -/
def cutFiveSevenOver₂Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2}, {3, 5}, ∅, {4, 6}]

/-- The slopes of `Gap212.cutFiveSevenOver₂Ranks`. -/
noncomputable def cutFiveSevenOver₂Dens : Fin 4 → ℝ := ![1, 2 / 5, 0, 1 / 3]

/-- The constants of `Gap212.cutFiveSevenOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutFiveSevenOver₂Const : Fin 4 → ℝ := ![0, -2 / 5, 0, -1 / 3]

/-- **Cell `(5,7)`, the low half's certificate 1.**

Block bounds `2147 / 7000`, `53 / 1000`, `213 / 6250`, `86 / 1875`.
Valid on `4 / 625 < ω₀` and on
`11883 / 35000 + 8ω₀ + ϵ ≤ γ ≤ 447 / 1000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3955143 + ϵ, 0.4330000 - ϵ]`. The cut is at `t = 53 / 1000`. -/
theorem admitsPartition₄_cellFiveSeven_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 11883 / 35000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 447 / 1000 - 2 * ω₀ - slack)
    {y : Fin (5 + 7) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (127 / 625) 5 7 (41 / 2500))
    (hcut : ∀ i : Fin (5 + 7), 5 ≤ (i : ℕ) → y i ≤ 53 / 1000) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutFiveSevenUnder₁LowRanks cutFiveSevenUnder₁Ranks (by decide) (by decide) (by decide)
    (by decide) cutFiveSevenUnder₁LowDens cutFiveSevenUnder₁Dens cutFiveSevenUnder₁Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFiveSevenUnder₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutFiveSevenUnder₁Dens]
  · intro k; fin_cases k <;> norm_num [cutFiveSevenUnder₁Const]
  · intro k; fin_cases k
    · simpa [cutFiveSevenUnder₁LowRanks, cutFiveSevenUnder₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutFiveSevenUnder₁LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutFiveSevenUnder₁LowRanks, cutFiveSevenUnder₁LowDens]
  · intro k; fin_cases k
    · simpa [cutFiveSevenUnder₁Ranks, cutFiveSevenUnder₁Dens, cutFiveSevenUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFiveSevenUnder₁Ranks 0) 4 0 7 (by norm_num) (by decide)
    · simpa [cutFiveSevenUnder₁Ranks, cutFiveSevenUnder₁Dens, cutFiveSevenUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFiveSevenUnder₁Ranks 1) 0 1 1 (by norm_num) (by decide)
    · simpa [cutFiveSevenUnder₁Ranks, cutFiveSevenUnder₁Dens, cutFiveSevenUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFiveSevenUnder₁Ranks 2) 1 0 5 (by norm_num) (by decide)
    · simpa [cutFiveSevenUnder₁Ranks, cutFiveSevenUnder₁Dens, cutFiveSevenUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFiveSevenUnder₁Ranks 3) 1 0 3 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutFiveSevenUnder₁LowRanks, cutFiveSevenUnder₁Ranks,
      cutFiveSevenUnder₁LowDens, cutFiveSevenUnder₁Dens, cutFiveSevenUnder₁Const] <;> linarith

/-- **Cell `(5,7)`, the high half's certificate 1.**

Block bounds `1477 / 5000`, `2007 / 25000`, `953 / 25000`, `751 / 15000`.
Valid on `4 / 625 < ω₀` and on
`1641 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 10493 / 25000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3842000 + ϵ, 0.4057200 - ϵ]`. The cut is at `t = 53 / 1000`. -/
theorem admitsPartition₄_cellFiveSeven_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1641 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 10493 / 25000 - 2 * ω₀ - slack)
    {y : Fin (5 + 7) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (127 / 625) 5 7 (41 / 2500))
    (hcut : ∃ i : Fin (5 + 7), 5 ≤ (i : ℕ) ∧ 53 / 1000 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutFiveSevenOver₁LowRanks cutFiveSevenOver₁Ranks (by decide) (by decide) (by decide)
    (by decide) cutFiveSevenOver₁LowDens cutFiveSevenOver₁Dens cutFiveSevenOver₁Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFiveSevenOver₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutFiveSevenOver₁Dens]
  · intro k; fin_cases k <;> norm_num [cutFiveSevenOver₁Const]
  · intro k; fin_cases k
    · simpa [cutFiveSevenOver₁LowRanks, cutFiveSevenOver₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutFiveSevenOver₁LowRanks 0) 1 1 (by norm_num) (by decide)
    · simp [cutFiveSevenOver₁LowRanks, cutFiveSevenOver₁LowDens]
    · simpa [cutFiveSevenOver₁LowRanks, cutFiveSevenOver₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutFiveSevenOver₁LowRanks 2) 1 5 (by norm_num) (by decide)
    · simp [cutFiveSevenOver₁LowRanks, cutFiveSevenOver₁LowDens]
  · intro k; fin_cases k
    · simpa [cutFiveSevenOver₁Ranks, cutFiveSevenOver₁Dens, cutFiveSevenOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFiveSevenOver₁Ranks 0) 1 0 1 (by norm_num) (by decide)
    · simpa [cutFiveSevenOver₁Ranks, cutFiveSevenOver₁Dens, cutFiveSevenOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFiveSevenOver₁Ranks 1) 3 (-3) 5 (by norm_num) (by decide)
    · simp [cutFiveSevenOver₁Ranks, cutFiveSevenOver₁Dens, cutFiveSevenOver₁Const]
    · simpa [cutFiveSevenOver₁Ranks, cutFiveSevenOver₁Dens, cutFiveSevenOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFiveSevenOver₁Ranks 3) 1 (-1) 3 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutFiveSevenOver₁LowRanks, cutFiveSevenOver₁Ranks,
      cutFiveSevenOver₁LowDens, cutFiveSevenOver₁Dens, cutFiveSevenOver₁Const] <;> linarith

/-- **Cell `(5,7)`, the high half's certificate 2.**

Block bounds `1559 / 5000`, `669 / 12500`, `953 / 25000`, `751 / 15000`.
Valid on `4 / 625 < ω₀` and on
`1723 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 5581 / 12500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4006000 + ϵ, 0.4324800 - ϵ]`. The cut is at `t = 53 / 1000`. -/
theorem admitsPartition₄_cellFiveSeven_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1723 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 5581 / 12500 - 2 * ω₀ - slack)
    {y : Fin (5 + 7) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (127 / 625) 5 7 (41 / 2500))
    (hcut : ∃ i : Fin (5 + 7), 5 ≤ (i : ℕ) ∧ 53 / 1000 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutFiveSevenOver₂LowRanks cutFiveSevenOver₂Ranks (by decide) (by decide) (by decide)
    (by decide) cutFiveSevenOver₂LowDens cutFiveSevenOver₂Dens cutFiveSevenOver₂Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFiveSevenOver₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutFiveSevenOver₂Dens]
  · intro k; fin_cases k <;> norm_num [cutFiveSevenOver₂Const]
  · intro k; fin_cases k
    · simpa [cutFiveSevenOver₂LowRanks, cutFiveSevenOver₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutFiveSevenOver₂LowRanks 0) 1 1 (by norm_num) (by decide)
    · simp [cutFiveSevenOver₂LowRanks, cutFiveSevenOver₂LowDens]
    · simpa [cutFiveSevenOver₂LowRanks, cutFiveSevenOver₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutFiveSevenOver₂LowRanks 2) 1 5 (by norm_num) (by decide)
    · simp [cutFiveSevenOver₂LowRanks, cutFiveSevenOver₂LowDens]
  · intro k; fin_cases k
    · simpa [cutFiveSevenOver₂Ranks, cutFiveSevenOver₂Dens, cutFiveSevenOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFiveSevenOver₂Ranks 0) 1 0 1 (by norm_num) (by decide)
    · simpa [cutFiveSevenOver₂Ranks, cutFiveSevenOver₂Dens, cutFiveSevenOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFiveSevenOver₂Ranks 1) 2 (-2) 5 (by norm_num) (by decide)
    · simp [cutFiveSevenOver₂Ranks, cutFiveSevenOver₂Dens, cutFiveSevenOver₂Const]
    · simpa [cutFiveSevenOver₂Ranks, cutFiveSevenOver₂Dens, cutFiveSevenOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutFiveSevenOver₂Ranks 3) 1 (-1) 3 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutFiveSevenOver₂LowRanks, cutFiveSevenOver₂Ranks,
      cutFiveSevenOver₂LowDens, cutFiveSevenOver₂Dens, cutFiveSevenOver₂Const] <;> linarith

/-- **Cell `(5,7)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,5}, B_{1,7}, 5, 7, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 53 / 1000`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellFiveSeven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 7) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (127 / 625) 5 7 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_cut (t := 53 / 1000) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · exact admitsPartition₄_cellFiveSeven_under₁ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (10493 / 25000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellFiveSeven_over₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellFiveSeven_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(5,7)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellFiveSeven_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (5 + 7) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (127 / 625) 5 7 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellFiveSeven_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(5,7)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 5 = gap212Cap 5 = 953 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFiveSeven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 7) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 5) (gap212Params.B j' 7) 5 7
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  simp only [gap212Params] at hy; norm_num [gap212Cap] at hy
  exact admitsPartition₄_cellFiveSeven_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(7,8)` -/

/-- The first group's rank sets for cell `(7,8)`, the low half's certificate 1. -/
def cutSevenEightUnder₁LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenEightUnder₁LowRanks`. -/
noncomputable def cutSevenEightUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,8)`, the low half's certificate 1. -/
def cutSevenEightUnder₁Ranks : Fin 4 → Finset (Fin 8) :=
  ![{1, 3, 5, 7}, {0, 6}, {4}, {2}]

/-- The slopes of `Gap212.cutSevenEightUnder₁Ranks`. -/
noncomputable def cutSevenEightUnder₁Dens : Fin 4 → ℝ := ![1 / 2, 1 / 6, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutSevenEightUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutSevenEightUnder₁Const : Fin 4 → ℝ := ![0, 5 / 6, 0, 0]

/-- The first group's rank sets for cell `(7,8)`, the low half's certificate 2. -/
def cutSevenEightUnder₂LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenEightUnder₂LowRanks`. -/
noncomputable def cutSevenEightUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,8)`, the low half's certificate 2. -/
def cutSevenEightUnder₂Ranks : Fin 4 → Finset (Fin 8) :=
  ![{1, 3, 5, 6}, {0, 7}, {4}, {2}]

/-- The slopes of `Gap212.cutSevenEightUnder₂Ranks`. -/
noncomputable def cutSevenEightUnder₂Dens : Fin 4 → ℝ := ![4 / 7, 1 / 7, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutSevenEightUnder₂Ranks`, nonnegative throughout. -/
noncomputable def cutSevenEightUnder₂Const : Fin 4 → ℝ := ![0, 6 / 7, 0, 0]

/-- The first group's rank sets for cell `(7,8)`, the high half's certificate 1. -/
def cutSevenEightOver₁LowRanks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2, 3, 4, 5}, ∅, ∅, {6}]

/-- The prefix densities of `Gap212.cutSevenEightOver₁LowRanks`. -/
noncomputable def cutSevenEightOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 1 / 7]

/-- The second group's rank sets for cell `(7,8)`, the high half's certificate 1. -/
def cutSevenEightOver₁Ranks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1}, {2, 3, 5}, {4, 7}, {6}]

/-- The slopes of `Gap212.cutSevenEightOver₁Ranks`. -/
noncomputable def cutSevenEightOver₁Dens : Fin 4 → ℝ := ![1, 2 / 3, 2 / 7, 1 / 6]

/-- The constants of `Gap212.cutSevenEightOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutSevenEightOver₁Const : Fin 4 → ℝ := ![0, -2 / 3, -2 / 7, -1 / 6]

/-- The first group's rank sets for cell `(7,8)`, the low half's certificate 3. -/
def cutSevenEightUnder₃LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenEightUnder₃LowRanks`. -/
noncomputable def cutSevenEightUnder₃LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,8)`, the low half's certificate 3. -/
def cutSevenEightUnder₃Ranks : Fin 4 → Finset (Fin 8) :=
  ![{1, 3, 5, 7}, {2, 6}, {4}, {0}]

/-- The slopes of `Gap212.cutSevenEightUnder₃Ranks`. -/
noncomputable def cutSevenEightUnder₃Dens : Fin 4 → ℝ := ![1 / 2, 1 / 3, 1 / 5, 0]

/-- The constants of `Gap212.cutSevenEightUnder₃Ranks`, nonnegative throughout. -/
noncomputable def cutSevenEightUnder₃Const : Fin 4 → ℝ := ![0, 0, 0, 1]

/-- The first group's rank sets for cell `(7,8)`, the low half's certificate 4. -/
def cutSevenEightUnder₄LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenEightUnder₄LowRanks`. -/
noncomputable def cutSevenEightUnder₄LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,8)`, the low half's certificate 4. -/
def cutSevenEightUnder₄Ranks : Fin 4 → Finset (Fin 8) :=
  ![{1, 2, 4, 5, 7}, {6}, {3}, {0}]

/-- The slopes of `Gap212.cutSevenEightUnder₄Ranks`. -/
noncomputable def cutSevenEightUnder₄Dens : Fin 4 → ℝ := ![2 / 3, 1 / 7, 1 / 4, 0]

/-- The constants of `Gap212.cutSevenEightUnder₄Ranks`, nonnegative throughout. -/
noncomputable def cutSevenEightUnder₄Const : Fin 4 → ℝ := ![0, 0, 0, 1]

/-- The first group's rank sets for cell `(7,8)`, the high half's certificate 2. -/
def cutSevenEightOver₂LowRanks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2, 3, 4, 5}, ∅, {6}, ∅]

/-- The prefix densities of `Gap212.cutSevenEightOver₂LowRanks`. -/
noncomputable def cutSevenEightOver₂LowDens : Fin 4 → ℝ := ![1, 0, 1 / 7, 0]

/-- The second group's rank sets for cell `(7,8)`, the high half's certificate 2. -/
def cutSevenEightOver₂Ranks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1, 2}, {3, 5, 7}, ∅, {4, 6}]

/-- The slopes of `Gap212.cutSevenEightOver₂Ranks`. -/
noncomputable def cutSevenEightOver₂Dens : Fin 4 → ℝ := ![1, 3 / 7, 0, 1 / 3]

/-- The constants of `Gap212.cutSevenEightOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutSevenEightOver₂Const : Fin 4 → ℝ := ![0, -3 / 7, 0, -1 / 3]

/-- The first group's rank sets for cell `(7,8)`, the high half's certificate 3. -/
def cutSevenEightOver₃LowRanks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2, 3, 4, 5}, ∅, {6}, ∅]

/-- The prefix densities of `Gap212.cutSevenEightOver₃LowRanks`. -/
noncomputable def cutSevenEightOver₃LowDens : Fin 4 → ℝ := ![1, 0, 1 / 7, 0]

/-- The second group's rank sets for cell `(7,8)`, the high half's certificate 3. -/
def cutSevenEightOver₃Ranks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1, 2, 3}, {4, 7}, ∅, {5, 6}]

/-- The slopes of `Gap212.cutSevenEightOver₃Ranks`. -/
noncomputable def cutSevenEightOver₃Dens : Fin 4 → ℝ := ![1, 2 / 7, 0, 1 / 3]

/-- The constants of `Gap212.cutSevenEightOver₃Ranks`, nonpositive throughout. -/
noncomputable def cutSevenEightOver₃Const : Fin 4 → ℝ := ![0, -2 / 7, 0, -1 / 3]

/-- **Cell `(7,8)`, the low half's certificate 1.**

Block bounds `1537 / 5000`, `251 / 3000`, `199 / 6250`, `79 / 1875`.
Valid on `4 / 625 < ω₀` and on
`1701 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 1249 / 3000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3962000 + ϵ, 0.4023333 - ϵ]`. The cut is at `t = 31 / 500`. -/
theorem admitsPartition₄_cellSevenEight_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1701 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1249 / 3000 - 2 * ω₀ - slack)
    {y : Fin (7 + 8) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (521 / 2500) 7 8 (41 / 2500))
    (hcut : ∀ i : Fin (7 + 8), 7 ≤ (i : ℕ) → y i ≤ 31 / 500) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutSevenEightUnder₁LowRanks cutSevenEightUnder₁Ranks (by decide) (by decide) (by decide)
    (by decide) cutSevenEightUnder₁LowDens cutSevenEightUnder₁Dens cutSevenEightUnder₁Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSevenEightUnder₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutSevenEightUnder₁Dens]
  · intro k; fin_cases k <;> norm_num [cutSevenEightUnder₁Const]
  · intro k; fin_cases k
    · simpa [cutSevenEightUnder₁LowRanks, cutSevenEightUnder₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSevenEightUnder₁LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutSevenEightUnder₁LowRanks, cutSevenEightUnder₁LowDens]
  · intro k; fin_cases k
    · simpa [cutSevenEightUnder₁Ranks, cutSevenEightUnder₁Dens, cutSevenEightUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₁Ranks 0) 1 0 2 (by norm_num) (by decide)
    · simpa [cutSevenEightUnder₁Ranks, cutSevenEightUnder₁Dens, cutSevenEightUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₁Ranks 1) 1 5 6 (by norm_num) (by decide)
    · simpa [cutSevenEightUnder₁Ranks, cutSevenEightUnder₁Dens, cutSevenEightUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₁Ranks 2) 1 0 5 (by norm_num) (by decide)
    · simpa [cutSevenEightUnder₁Ranks, cutSevenEightUnder₁Dens, cutSevenEightUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₁Ranks 3) 1 0 3 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutSevenEightUnder₁LowRanks, cutSevenEightUnder₁Ranks,
      cutSevenEightUnder₁LowDens, cutSevenEightUnder₁Dens, cutSevenEightUnder₁Const] <;> linarith

/-- **Cell `(7,8)`, the low half's certificate 2.**

Block bounds `1369 / 4375`, `1451 / 17500`, `199 / 6250`, `79 / 1875`.
Valid on `4 / 625 < ω₀` and on
`121 / 350 + 8ω₀ + ϵ ≤ γ ≤ 7299 / 17500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4017143 + ϵ, 0.4030857 - ϵ]`. The cut is at `t = 31 / 500`. -/
theorem admitsPartition₄_cellSevenEight_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 121 / 350 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 7299 / 17500 - 2 * ω₀ - slack)
    {y : Fin (7 + 8) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (521 / 2500) 7 8 (41 / 2500))
    (hcut : ∀ i : Fin (7 + 8), 7 ≤ (i : ℕ) → y i ≤ 31 / 500) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutSevenEightUnder₂LowRanks cutSevenEightUnder₂Ranks (by decide) (by decide) (by decide)
    (by decide) cutSevenEightUnder₂LowDens cutSevenEightUnder₂Dens cutSevenEightUnder₂Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSevenEightUnder₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutSevenEightUnder₂Dens]
  · intro k; fin_cases k <;> norm_num [cutSevenEightUnder₂Const]
  · intro k; fin_cases k
    · simpa [cutSevenEightUnder₂LowRanks, cutSevenEightUnder₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSevenEightUnder₂LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutSevenEightUnder₂LowRanks, cutSevenEightUnder₂LowDens]
  · intro k; fin_cases k
    · simpa [cutSevenEightUnder₂Ranks, cutSevenEightUnder₂Dens, cutSevenEightUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₂Ranks 0) 4 0 7 (by norm_num) (by decide)
    · simpa [cutSevenEightUnder₂Ranks, cutSevenEightUnder₂Dens, cutSevenEightUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₂Ranks 1) 1 6 7 (by norm_num) (by decide)
    · simpa [cutSevenEightUnder₂Ranks, cutSevenEightUnder₂Dens, cutSevenEightUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₂Ranks 2) 1 0 5 (by norm_num) (by decide)
    · simpa [cutSevenEightUnder₂Ranks, cutSevenEightUnder₂Dens, cutSevenEightUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₂Ranks 3) 1 0 3 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutSevenEightUnder₂LowRanks, cutSevenEightUnder₂Ranks,
      cutSevenEightUnder₂LowDens, cutSevenEightUnder₂Dens, cutSevenEightUnder₂Const] <;> linarith

/-- **Cell `(7,8)`, the high half's certificate 1.**

Block bounds `371 / 1250`, `527 / 7500`, `183 / 4375`, `5323 / 105000`.
Valid on `4 / 625 < ω₀` and on
`206 / 625 + 8ω₀ + ϵ ≤ γ ≤ 3223 / 7500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3856000 + ϵ, 0.4157333 - ϵ]`. The cut is at `t = 31 / 500`. -/
theorem admitsPartition₄_cellSevenEight_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 206 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 3223 / 7500 - 2 * ω₀ - slack)
    {y : Fin (7 + 8) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (521 / 2500) 7 8 (41 / 2500))
    (hcut : ∃ i : Fin (7 + 8), 7 ≤ (i : ℕ) ∧ 31 / 500 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutSevenEightOver₁LowRanks cutSevenEightOver₁Ranks (by decide) (by decide) (by decide)
    (by decide) cutSevenEightOver₁LowDens cutSevenEightOver₁Dens cutSevenEightOver₁Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSevenEightOver₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutSevenEightOver₁Dens]
  · intro k; fin_cases k <;> norm_num [cutSevenEightOver₁Const]
  · intro k; fin_cases k
    · simpa [cutSevenEightOver₁LowRanks, cutSevenEightOver₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSevenEightOver₁LowRanks 0) 1 1 (by norm_num) (by decide)
    · simp [cutSevenEightOver₁LowRanks, cutSevenEightOver₁LowDens]
    · simp [cutSevenEightOver₁LowRanks, cutSevenEightOver₁LowDens]
    · simpa [cutSevenEightOver₁LowRanks, cutSevenEightOver₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSevenEightOver₁LowRanks 3) 1 7 (by norm_num) (by decide)
  · intro k; fin_cases k
    · simpa [cutSevenEightOver₁Ranks, cutSevenEightOver₁Dens, cutSevenEightOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightOver₁Ranks 0) 1 0 1 (by norm_num) (by decide)
    · simpa [cutSevenEightOver₁Ranks, cutSevenEightOver₁Dens, cutSevenEightOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightOver₁Ranks 1) 2 (-2) 3 (by norm_num) (by decide)
    · simpa [cutSevenEightOver₁Ranks, cutSevenEightOver₁Dens, cutSevenEightOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightOver₁Ranks 2) 2 (-2) 7 (by norm_num) (by decide)
    · simpa [cutSevenEightOver₁Ranks, cutSevenEightOver₁Dens, cutSevenEightOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightOver₁Ranks 3) 1 (-1) 6 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutSevenEightOver₁LowRanks, cutSevenEightOver₁Ranks,
      cutSevenEightOver₁LowDens, cutSevenEightOver₁Dens, cutSevenEightOver₁Const] <;> linarith

/-- **Cell `(7,8)`, the low half's certificate 3.**

Block bounds `1537 / 5000`, `439 / 7500`, `199 / 6250`, `51 / 1000`.
Valid on `4 / 625 < ω₀` and on
`1701 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 3311 / 7500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3962000 + ϵ, 0.4274667 - ϵ]`. The cut is at `t = 51 / 1000`. -/
theorem admitsPartition₄_cellSevenEight_under₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1701 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 3311 / 7500 - 2 * ω₀ - slack)
    {y : Fin (7 + 8) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (521 / 2500) 7 8 (41 / 2500))
    (hcut : ∀ i : Fin (7 + 8), 7 ≤ (i : ℕ) → y i ≤ 51 / 1000) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutSevenEightUnder₃LowRanks cutSevenEightUnder₃Ranks (by decide) (by decide) (by decide)
    (by decide) cutSevenEightUnder₃LowDens cutSevenEightUnder₃Dens cutSevenEightUnder₃Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSevenEightUnder₃LowDens]
  · intro k; fin_cases k <;> norm_num [cutSevenEightUnder₃Dens]
  · intro k; fin_cases k <;> norm_num [cutSevenEightUnder₃Const]
  · intro k; fin_cases k
    · simpa [cutSevenEightUnder₃LowRanks, cutSevenEightUnder₃LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSevenEightUnder₃LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutSevenEightUnder₃LowRanks, cutSevenEightUnder₃LowDens]
  · intro k; fin_cases k
    · simpa [cutSevenEightUnder₃Ranks, cutSevenEightUnder₃Dens, cutSevenEightUnder₃Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₃Ranks 0) 1 0 2 (by norm_num) (by decide)
    · simpa [cutSevenEightUnder₃Ranks, cutSevenEightUnder₃Dens, cutSevenEightUnder₃Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₃Ranks 1) 1 0 3 (by norm_num) (by decide)
    · simpa [cutSevenEightUnder₃Ranks, cutSevenEightUnder₃Dens, cutSevenEightUnder₃Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₃Ranks 2) 1 0 5 (by norm_num) (by decide)
    · simpa [cutSevenEightUnder₃Ranks, cutSevenEightUnder₃Dens, cutSevenEightUnder₃Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₃Ranks 3) 0 1 1 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutSevenEightUnder₃LowRanks, cutSevenEightUnder₃Ranks,
      cutSevenEightUnder₃LowDens, cutSevenEightUnder₃Dens, cutSevenEightUnder₃Const] <;> linarith

/-- **Cell `(7,8)`, the low half's certificate 4.**

Block bounds `101 / 300`, `24 / 875`, `357 / 10000`, `51 / 1000`.
Valid on `4 / 625 < ω₀` and on
`2771 / 7500 + 8ω₀ + ϵ ≤ γ ≤ 827 / 1750 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4254667 + ϵ, 0.4585714 - ϵ]`. The cut is at `t = 51 / 1000`. -/
theorem admitsPartition₄_cellSevenEight_under₄ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 2771 / 7500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 827 / 1750 - 2 * ω₀ - slack)
    {y : Fin (7 + 8) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (521 / 2500) 7 8 (41 / 2500))
    (hcut : ∀ i : Fin (7 + 8), 7 ≤ (i : ℕ) → y i ≤ 51 / 1000) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutSevenEightUnder₄LowRanks cutSevenEightUnder₄Ranks (by decide) (by decide) (by decide)
    (by decide) cutSevenEightUnder₄LowDens cutSevenEightUnder₄Dens cutSevenEightUnder₄Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSevenEightUnder₄LowDens]
  · intro k; fin_cases k <;> norm_num [cutSevenEightUnder₄Dens]
  · intro k; fin_cases k <;> norm_num [cutSevenEightUnder₄Const]
  · intro k; fin_cases k
    · simpa [cutSevenEightUnder₄LowRanks, cutSevenEightUnder₄LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSevenEightUnder₄LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutSevenEightUnder₄LowRanks, cutSevenEightUnder₄LowDens]
  · intro k; fin_cases k
    · simpa [cutSevenEightUnder₄Ranks, cutSevenEightUnder₄Dens, cutSevenEightUnder₄Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₄Ranks 0) 2 0 3 (by norm_num) (by decide)
    · simpa [cutSevenEightUnder₄Ranks, cutSevenEightUnder₄Dens, cutSevenEightUnder₄Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₄Ranks 1) 1 0 7 (by norm_num) (by decide)
    · simpa [cutSevenEightUnder₄Ranks, cutSevenEightUnder₄Dens, cutSevenEightUnder₄Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₄Ranks 2) 1 0 4 (by norm_num) (by decide)
    · simpa [cutSevenEightUnder₄Ranks, cutSevenEightUnder₄Dens, cutSevenEightUnder₄Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightUnder₄Ranks 3) 0 1 1 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutSevenEightUnder₄LowRanks, cutSevenEightUnder₄Ranks,
      cutSevenEightUnder₄LowDens, cutSevenEightUnder₄Dens, cutSevenEightUnder₄Const] <;> linarith

/-- **Cell `(7,8)`, the high half's certificate 2.**

Block bounds `783 / 2500`, `2361 / 35000`, `127 / 4375`, `47 / 1000`.
Valid on `4 / 625 < ω₀` and on
`173 / 500 + 8ω₀ + ϵ ≤ γ ≤ 15139 / 35000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4020000 + ϵ, 0.4185429 - ϵ]`. The cut is at `t = 51 / 1000`. -/
theorem admitsPartition₄_cellSevenEight_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 173 / 500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 15139 / 35000 - 2 * ω₀ - slack)
    {y : Fin (7 + 8) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (521 / 2500) 7 8 (41 / 2500))
    (hcut : ∃ i : Fin (7 + 8), 7 ≤ (i : ℕ) ∧ 51 / 1000 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutSevenEightOver₂LowRanks cutSevenEightOver₂Ranks (by decide) (by decide) (by decide)
    (by decide) cutSevenEightOver₂LowDens cutSevenEightOver₂Dens cutSevenEightOver₂Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSevenEightOver₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutSevenEightOver₂Dens]
  · intro k; fin_cases k <;> norm_num [cutSevenEightOver₂Const]
  · intro k; fin_cases k
    · simpa [cutSevenEightOver₂LowRanks, cutSevenEightOver₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSevenEightOver₂LowRanks 0) 1 1 (by norm_num) (by decide)
    · simp [cutSevenEightOver₂LowRanks, cutSevenEightOver₂LowDens]
    · simpa [cutSevenEightOver₂LowRanks, cutSevenEightOver₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSevenEightOver₂LowRanks 2) 1 7 (by norm_num) (by decide)
    · simp [cutSevenEightOver₂LowRanks, cutSevenEightOver₂LowDens]
  · intro k; fin_cases k
    · simpa [cutSevenEightOver₂Ranks, cutSevenEightOver₂Dens, cutSevenEightOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightOver₂Ranks 0) 1 0 1 (by norm_num) (by decide)
    · simpa [cutSevenEightOver₂Ranks, cutSevenEightOver₂Dens, cutSevenEightOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightOver₂Ranks 1) 3 (-3) 7 (by norm_num) (by decide)
    · simp [cutSevenEightOver₂Ranks, cutSevenEightOver₂Dens, cutSevenEightOver₂Const]
    · simpa [cutSevenEightOver₂Ranks, cutSevenEightOver₂Dens, cutSevenEightOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightOver₂Ranks 3) 1 (-1) 3 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutSevenEightOver₂LowRanks, cutSevenEightOver₂Ranks,
      cutSevenEightOver₂LowDens, cutSevenEightOver₂Dens, cutSevenEightOver₂Const] <;> linarith

/-- **Cell `(7,8)`, the high half's certificate 3.**

Block bounds `206 / 625`, `787 / 17500`, `127 / 4375`, `47 / 1000`.
Valid on `4 / 625 < ω₀` and on
`453 / 1250 + 8ω₀ + ϵ ≤ γ ≤ 7963 / 17500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4184000 + ϵ, 0.4410286 - ϵ]`. The cut is at `t = 51 / 1000`. -/
theorem admitsPartition₄_cellSevenEight_over₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 453 / 1250 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 7963 / 17500 - 2 * ω₀ - slack)
    {y : Fin (7 + 8) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (521 / 2500) 7 8 (41 / 2500))
    (hcut : ∃ i : Fin (7 + 8), 7 ≤ (i : ℕ) ∧ 51 / 1000 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutSevenEightOver₃LowRanks cutSevenEightOver₃Ranks (by decide) (by decide) (by decide)
    (by decide) cutSevenEightOver₃LowDens cutSevenEightOver₃Dens cutSevenEightOver₃Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSevenEightOver₃LowDens]
  · intro k; fin_cases k <;> norm_num [cutSevenEightOver₃Dens]
  · intro k; fin_cases k <;> norm_num [cutSevenEightOver₃Const]
  · intro k; fin_cases k
    · simpa [cutSevenEightOver₃LowRanks, cutSevenEightOver₃LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSevenEightOver₃LowRanks 0) 1 1 (by norm_num) (by decide)
    · simp [cutSevenEightOver₃LowRanks, cutSevenEightOver₃LowDens]
    · simpa [cutSevenEightOver₃LowRanks, cutSevenEightOver₃LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSevenEightOver₃LowRanks 2) 1 7 (by norm_num) (by decide)
    · simp [cutSevenEightOver₃LowRanks, cutSevenEightOver₃LowDens]
  · intro k; fin_cases k
    · simpa [cutSevenEightOver₃Ranks, cutSevenEightOver₃Dens, cutSevenEightOver₃Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightOver₃Ranks 0) 1 0 1 (by norm_num) (by decide)
    · simpa [cutSevenEightOver₃Ranks, cutSevenEightOver₃Dens, cutSevenEightOver₃Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightOver₃Ranks 1) 2 (-2) 7 (by norm_num) (by decide)
    · simp [cutSevenEightOver₃Ranks, cutSevenEightOver₃Dens, cutSevenEightOver₃Const]
    · simpa [cutSevenEightOver₃Ranks, cutSevenEightOver₃Dens, cutSevenEightOver₃Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenEightOver₃Ranks 3) 1 (-1) 3 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutSevenEightOver₃LowRanks, cutSevenEightOver₃Ranks,
      cutSevenEightOver₃LowDens, cutSevenEightOver₃Dens, cutSevenEightOver₃Const] <;> linarith

/-- **Cell `(7,8)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,7}, B_{1,8}, 7, 8, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate, at the thresholds `31 / 500, 51 / 1000` — one per `γ` region, the region
boundaries being the `γ` ceilings of the certificates that end them — then a `γ`
split inside each region on each half. No single threshold serves the whole `γ`-range:
at one fixed `ω₀` the binding threshold already varies with `γ`, so the missing dimension
is `γ` and not `ω₀`.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellSevenEight_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (7 + 8) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (521 / 2500) 7 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (7299 / 17500 - 2 * ω₀ - slack) with hr1 | hr1
  · refine admitsPartition₄_of_cut (t := 31 / 500) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
    · rcases le_or_gt γ (1249 / 3000 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellSevenEight_under₁ hωlo (by linarith) h1 hy hcut
      · exact admitsPartition₄_cellSevenEight_under₂ hωlo (by linarith) (by linarith) hy hcut
    · exact admitsPartition₄_cellSevenEight_over₁ hωlo (by linarith) (by linarith) hy hcut
  · refine admitsPartition₄_of_cut (t := 51 / 1000) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
    · rcases le_or_gt γ (3311 / 7500 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellSevenEight_under₃ hωlo (by linarith) h1 hy hcut
      · exact admitsPartition₄_cellSevenEight_under₄ hωlo (by linarith) (by linarith) hy hcut
    · rcases le_or_gt γ (15139 / 35000 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellSevenEight_over₂ hωlo (by linarith) h1 hy hcut
      · exact admitsPartition₄_cellSevenEight_over₃ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(7,8)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellSevenEight_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (7 + 8) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (521 / 2500) 7 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellSevenEight_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(7,8)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 7 = gap212Cap 7 = 127 / 625` at every stratum `j`. -/
theorem admitsPartition₄_cellSevenEight_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (7 + 8) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 7) (gap212Params.B j' 8) 7 8
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  simp only [gap212Params] at hy; norm_num [gap212Cap] at hy
  exact admitsPartition₄_cellSevenEight_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(7,9)` -/

/-- The first group's rank sets for cell `(7,9)`, the low half's certificate 1. -/
def cutSevenNineUnder₁LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenNineUnder₁LowRanks`. -/
noncomputable def cutSevenNineUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,9)`, the low half's certificate 1. -/
def cutSevenNineUnder₁Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 3, 6, 8}, {1, 5}, {2}, {4, 7}]

/-- The slopes of `Gap212.cutSevenNineUnder₁Ranks`. -/
noncomputable def cutSevenNineUnder₁Dens : Fin 4 → ℝ := ![3 / 8, 1 / 4, 1 / 3, 1 / 4]

/-- The constants of `Gap212.cutSevenNineUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutSevenNineUnder₁Const : Fin 4 → ℝ := ![5 / 8, 1 / 2, 0, 0]

/-- The first group's rank sets for cell `(7,9)`, the low half's certificate 2. -/
def cutSevenNineUnder₂LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenNineUnder₂LowRanks`. -/
noncomputable def cutSevenNineUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,9)`, the low half's certificate 2. -/
def cutSevenNineUnder₂Ranks : Fin 4 → Finset (Fin 9) :=
  ![{1, 3, 5, 6, 8}, {0}, {2}, {4, 7}]

/-- The slopes of `Gap212.cutSevenNineUnder₂Ranks`. -/
noncomputable def cutSevenNineUnder₂Dens : Fin 4 → ℝ := ![4 / 7, 0, 1 / 3, 1 / 4]

/-- The constants of `Gap212.cutSevenNineUnder₂Ranks`, nonnegative throughout. -/
noncomputable def cutSevenNineUnder₂Const : Fin 4 → ℝ := ![0, 1, 0, 0]

/-- The first group's rank sets for cell `(7,9)`, the high half's certificate 1. -/
def cutSevenNineOver₁LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenNineOver₁LowRanks`. -/
noncomputable def cutSevenNineOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,9)`, the high half's certificate 1. -/
def cutSevenNineOver₁Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1}, {3, 5, 7}, {4, 8}, {2, 6}]

/-- The slopes of `Gap212.cutSevenNineOver₁Ranks`. -/
noncomputable def cutSevenNineOver₁Dens : Fin 4 → ℝ := ![1, 3 / 7, 1 / 4, 1 / 2]

/-- The constants of `Gap212.cutSevenNineOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutSevenNineOver₁Const : Fin 4 → ℝ := ![0, -3 / 7, -1 / 4, -1 / 2]

/-- The first group's rank sets for cell `(7,9)`, the high half's certificate 2. -/
def cutSevenNineOver₂LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenNineOver₂LowRanks`. -/
noncomputable def cutSevenNineOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,9)`, the high half's certificate 2. -/
def cutSevenNineOver₂Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2}, {4, 7}, {5, 8}, {3, 6}]

/-- The slopes of `Gap212.cutSevenNineOver₂Ranks`. -/
noncomputable def cutSevenNineOver₂Dens : Fin 4 → ℝ := ![1, 2 / 7, 1 / 4, 1 / 3]

/-- The constants of `Gap212.cutSevenNineOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutSevenNineOver₂Const : Fin 4 → ℝ := ![0, -2 / 7, -1 / 4, -1 / 3]

/-- **Cell `(7,9)`, the low half's certificate 1.**

Block bounds `6221 / 20000`, `1267 / 20000`, `571 / 15000`, `981 / 20000`.
Valid on `4 / 625 < ω₀` and on
`6877 / 20000 + 8ω₀ + ϵ ≤ γ ≤ 8733 / 20000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3998500 + ϵ, 0.4226500 - ϵ]`. The cut is at `t = 9 / 200`. -/
theorem admitsPartition₄_cellSevenNine_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 6877 / 20000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 8733 / 20000 - 2 * ω₀ - slack)
    {y : Fin (7 + 9) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1063 / 5000) 7 9 (41 / 2500))
    (hcut : ∀ i : Fin (7 + 9), 7 ≤ (i : ℕ) → y i ≤ 9 / 200) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutSevenNineUnder₁LowRanks cutSevenNineUnder₁Ranks (by decide) (by decide) (by decide)
    (by decide) cutSevenNineUnder₁LowDens cutSevenNineUnder₁Dens cutSevenNineUnder₁Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSevenNineUnder₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutSevenNineUnder₁Dens]
  · intro k; fin_cases k <;> norm_num [cutSevenNineUnder₁Const]
  · intro k; fin_cases k
    · simpa [cutSevenNineUnder₁LowRanks, cutSevenNineUnder₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSevenNineUnder₁LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutSevenNineUnder₁LowRanks, cutSevenNineUnder₁LowDens]
  · intro k; fin_cases k
    · simpa [cutSevenNineUnder₁Ranks, cutSevenNineUnder₁Dens, cutSevenNineUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineUnder₁Ranks 0) 3 5 8 (by norm_num) (by decide)
    · simpa [cutSevenNineUnder₁Ranks, cutSevenNineUnder₁Dens, cutSevenNineUnder₁Const,
        show (2 : ℝ) / 4 = 2⁻¹ by norm_num] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineUnder₁Ranks 1) 1 2 4 (by norm_num) (by decide)
    · simpa [cutSevenNineUnder₁Ranks, cutSevenNineUnder₁Dens, cutSevenNineUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineUnder₁Ranks 2) 1 0 3 (by norm_num) (by decide)
    · simpa [cutSevenNineUnder₁Ranks, cutSevenNineUnder₁Dens, cutSevenNineUnder₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineUnder₁Ranks 3) 1 0 4 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutSevenNineUnder₁LowRanks, cutSevenNineUnder₁Ranks,
      cutSevenNineUnder₁LowDens, cutSevenNineUnder₁Dens, cutSevenNineUnder₁Const] <;> linarith

/-- **Cell `(7,9)`, the low half's certificate 2.**

Block bounds `5641 / 17500`, `9 / 200`, `571 / 15000`, `981 / 20000`.
Valid on `4 / 625 < ω₀` and on
`1243 / 3500 + 8ω₀ + ϵ ≤ γ ≤ 91 / 200 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4111429 + ϵ, 0.4410000 - ϵ]`. The cut is at `t = 9 / 200`. -/
theorem admitsPartition₄_cellSevenNine_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1243 / 3500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 91 / 200 - 2 * ω₀ - slack)
    {y : Fin (7 + 9) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1063 / 5000) 7 9 (41 / 2500))
    (hcut : ∀ i : Fin (7 + 9), 7 ≤ (i : ℕ) → y i ≤ 9 / 200) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutSevenNineUnder₂LowRanks cutSevenNineUnder₂Ranks (by decide) (by decide) (by decide)
    (by decide) cutSevenNineUnder₂LowDens cutSevenNineUnder₂Dens cutSevenNineUnder₂Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSevenNineUnder₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutSevenNineUnder₂Dens]
  · intro k; fin_cases k <;> norm_num [cutSevenNineUnder₂Const]
  · intro k; fin_cases k
    · simpa [cutSevenNineUnder₂LowRanks, cutSevenNineUnder₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSevenNineUnder₂LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutSevenNineUnder₂LowRanks, cutSevenNineUnder₂LowDens]
  · intro k; fin_cases k
    · simpa [cutSevenNineUnder₂Ranks, cutSevenNineUnder₂Dens, cutSevenNineUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineUnder₂Ranks 0) 4 0 7 (by norm_num) (by decide)
    · simpa [cutSevenNineUnder₂Ranks, cutSevenNineUnder₂Dens, cutSevenNineUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineUnder₂Ranks 1) 0 1 1 (by norm_num) (by decide)
    · simpa [cutSevenNineUnder₂Ranks, cutSevenNineUnder₂Dens, cutSevenNineUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineUnder₂Ranks 2) 1 0 3 (by norm_num) (by decide)
    · simpa [cutSevenNineUnder₂Ranks, cutSevenNineUnder₂Dens, cutSevenNineUnder₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineUnder₂Ranks 3) 1 0 4 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutSevenNineUnder₂LowRanks, cutSevenNineUnder₂Ranks,
      cutSevenNineUnder₂LowDens, cutSevenNineUnder₂Dens, cutSevenNineUnder₂Const] <;> linarith

/-- **Cell `(7,9)`, the high half's certificate 1.**

Block bounds `301 / 1000`, `81 / 1250`, `419 / 10000`, `51 / 1000`.
Valid on `4 / 625 < ω₀` and on
`1669 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 272 / 625 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3898000 + ϵ, 0.4212000 - ϵ]`. The cut is at `t = 9 / 200`. -/
theorem admitsPartition₄_cellSevenNine_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1669 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 272 / 625 - 2 * ω₀ - slack)
    {y : Fin (7 + 9) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1063 / 5000) 7 9 (41 / 2500))
    (hcut : ∃ i : Fin (7 + 9), 7 ≤ (i : ℕ) ∧ 9 / 200 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutSevenNineOver₁LowRanks cutSevenNineOver₁Ranks (by decide) (by decide) (by decide)
    (by decide) cutSevenNineOver₁LowDens cutSevenNineOver₁Dens cutSevenNineOver₁Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSevenNineOver₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutSevenNineOver₁Dens]
  · intro k; fin_cases k <;> norm_num [cutSevenNineOver₁Const]
  · intro k; fin_cases k
    · simpa [cutSevenNineOver₁LowRanks, cutSevenNineOver₁LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSevenNineOver₁LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutSevenNineOver₁LowRanks, cutSevenNineOver₁LowDens]
  · intro k; fin_cases k
    · simpa [cutSevenNineOver₁Ranks, cutSevenNineOver₁Dens, cutSevenNineOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineOver₁Ranks 0) 1 0 1 (by norm_num) (by decide)
    · simpa [cutSevenNineOver₁Ranks, cutSevenNineOver₁Dens, cutSevenNineOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineOver₁Ranks 1) 3 (-3) 7 (by norm_num) (by decide)
    · simpa [cutSevenNineOver₁Ranks, cutSevenNineOver₁Dens, cutSevenNineOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineOver₁Ranks 2) 1 (-1) 4 (by norm_num) (by decide)
    · simpa [cutSevenNineOver₁Ranks, cutSevenNineOver₁Dens, cutSevenNineOver₁Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineOver₁Ranks 3) 1 (-1) 2 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutSevenNineOver₁LowRanks, cutSevenNineOver₁Ranks,
      cutSevenNineOver₁LowDens, cutSevenNineOver₁Dens, cutSevenNineOver₁Const] <;> linarith

/-- **Cell `(7,9)`, the high half's certificate 2.**

Block bounds `1587 / 5000`, `27 / 625`, `419 / 10000`, `337 / 7500`.
Valid on `4 / 625 < ω₀` and on
`1751 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 571 / 1250 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4062000 + ϵ, 0.4428000 - ϵ]`. The cut is at `t = 9 / 200`. -/
theorem admitsPartition₄_cellSevenNine_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1751 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 571 / 1250 - 2 * ω₀ - slack)
    {y : Fin (7 + 9) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1063 / 5000) 7 9 (41 / 2500))
    (hcut : ∃ i : Fin (7 + 9), 7 ≤ (i : ℕ) ∧ 9 / 200 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutSevenNineOver₂LowRanks cutSevenNineOver₂Ranks (by decide) (by decide) (by decide)
    (by decide) cutSevenNineOver₂LowDens cutSevenNineOver₂Dens cutSevenNineOver₂Const
    ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSevenNineOver₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutSevenNineOver₂Dens]
  · intro k; fin_cases k <;> norm_num [cutSevenNineOver₂Const]
  · intro k; fin_cases k
    · simpa [cutSevenNineOver₂LowRanks, cutSevenNineOver₂LowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cutSevenNineOver₂LowRanks 0) 1 1 (by norm_num) (by decide)
    all_goals simp [cutSevenNineOver₂LowRanks, cutSevenNineOver₂LowDens]
  · intro k; fin_cases k
    · simpa [cutSevenNineOver₂Ranks, cutSevenNineOver₂Dens, cutSevenNineOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineOver₂Ranks 0) 1 0 1 (by norm_num) (by decide)
    · simpa [cutSevenNineOver₂Ranks, cutSevenNineOver₂Dens, cutSevenNineOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineOver₂Ranks 1) 2 (-2) 7 (by norm_num) (by decide)
    · simpa [cutSevenNineOver₂Ranks, cutSevenNineOver₂Dens, cutSevenNineOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineOver₂Ranks 2) 1 (-1) 4 (by norm_num) (by decide)
    · simpa [cutSevenNineOver₂Ranks, cutSevenNineOver₂Dens, cutSevenNineOver₂Const] using
        prefixAffine_of_int (𝕜 := ℝ) (cutSevenNineOver₂Ranks 3) 1 (-1) 3 (by norm_num) (by decide)
  · intro k; fin_cases k <;> simp [capD, hδ, cutSevenNineOver₂LowRanks, cutSevenNineOver₂Ranks,
      cutSevenNineOver₂LowDens, cutSevenNineOver₂Dens, cutSevenNineOver₂Const] <;> linarith

/-- **Cell `(7,9)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,7}, B_{1,9}, 7, 9, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 9 / 200`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellSevenNine_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (7 + 9) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1063 / 5000) 7 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_cut (t := 9 / 200) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · rcases le_or_gt γ (8733 / 20000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellSevenNine_under₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellSevenNine_under₂ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (272 / 625 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellSevenNine_over₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellSevenNine_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(7,9)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellSevenNine_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (7 + 9) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1063 / 5000) 7 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellSevenNine_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(7,9)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 7 = gap212Cap 7 = 127 / 625` at every stratum `j`. -/
theorem admitsPartition₄_cellSevenNine_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (7 + 9) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 7) (gap212Params.B j' 9) 7 9
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  simp only [gap212Params] at hy; norm_num [gap212Cap] at hy
  exact admitsPartition₄_cellSevenNine_band hωlo hωhi hγlo hγhi hy

/-- The hypotheses of the band theorems above are satisfiable: the chamber point `ω₀ = 7/1000`,
`γ = 2/5` and the constant profile `δ = 41/2500` meet all of them. -/
theorem cellsRest_hypotheses_satisfiable :
    (4 / 625 < (7 / 1000 : ℝ) ∧ (2 / 5 - slack : ℝ) ≤ 2 / 5 ∧
        (2 / 5 : ℝ) ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (917 / 5000 : ℝ) (127 / 625) 4 7 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (953 / 5000 : ℝ) (127 / 625) 5 7 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (127 / 625 : ℝ) (521 / 2500) 7 8 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (127 / 625 : ℝ) (1063 / 5000) 7 9 (41 / 2500) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine ⟨⟨by norm_num, by rw [hsv]; norm_num, by rw [hδ, hsv]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 4 7]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 4 7]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 5 7]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 5 7]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 7 8]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 7 8]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 7 9]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 7 9]; norm_num⟩⟩

end Gap212
