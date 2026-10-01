/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCell

/-!
# The uncut rank certificates, part 1: the cells with one or two ranks on the low side

`Gap212.Packing.admitsPartition₄_of_rank_certificate` bounds each of the four bins by
`#T_k·δ + r_k·(B₁ - m₁δ) + #U_k·δ + s_k·(B₂ - m₂δ)`, with `r_k` and `s_k` the prefix densities of
the two rank sets the bin holds. No cut, no threshold, no hypothesis on the profile beyond `Ξ`: this
is the *uncut* reading, and it closes 62 of the 91 cells `1 ≤ m ≤ m' ≤ 13` on the whole band
`ω₀ ∈ (4/625, 7/1000]` and the whole chamber `γ`-range.

This file carries 23 of them, the cells with one or two ranks on the low side:

    (1,1)  (1,2)  (1,4)  (1,5)  (1,6)  (1,7)  (1,8)  (1,9)
    (1,10)  (1,11)  (1,12)  (1,13)  (2,2)  (2,4)  (2,5)  (2,6)
    (2,7)  (2,8)  (2,9)  (2,10)  (2,11)  (2,12)  (2,13)

## Why one check at the top of the band serves the whole band

Bin `k`'s check is `row_k ≤ capD γ ω₀ k`. In `ω₀` the two large capacities *fall*
(`capD 0 = γ - 2δ - 8ω₀ - ϵ`, `capD 1 = 1/2 - γ - 2ω₀ - ϵ`) and the two small ones *rise*
(`capD 2 = 4ω₀ + δ - ϵ`, `capD 3 = 8ω₀`). So a certificate is hardest for bins 0 and 1 at the top of
the band and hardest for bins 2 and 3 at the floor, and a certificate whose bin-2 and bin-3 rows fit
under the floor's capacities and whose `γ` window is computed at `ω₀ = 7/1000` is valid at every
level of the band. That is why no cell here needs a case analysis in `ω₀`.

The `γ` window of a certificate with block bounds `(b₀, b₁, b₂, b₃)` is
`[b₀ + 2δ + 8ω₀ + ϵ, 1/2 - b₁ - 2ω₀ - ϵ]`: its floor rises in `ω₀` at rate `8` and its ceiling
falls at rate `2`, so a chain of certificates that covers `[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]` at
`ω₀ = 7/1000` covers it at every smaller level too.

## The other cells

The other twenty-nine cells are not covered by the uncut reading on the whole band and need a cut;
they are in `Gap212.Packing.SortedCellCut`, `SortedCellsCut`, `SortedCellsGamma`,
`SortedCellsMid`, `SortedCellsRest`, `SortedCellsPair`, `SortedCellsSub` and `SortedCellsEight`.
Every certificate, cut or uncut, is stated for the ordered pair `(m, m')` with `m ≤ m'`, while
`Gap212.PackingCertificate` quantifies over both orders;
`Gap212.Packing.admitsPartition₄_transpose_of` carries each off-diagonal cell to its transpose.
-/

@[expose] public section

namespace Gap212

open Finset Gap212.Packing

/-- The low-side prefix densities of the all-in-bin-0 rank sets `![univ, ∅, ∅, ∅]`. -/
private theorem prefixDensity_univ {N : ℕ} :
    ∀ k, ∀ j : ℕ, ((((![Finset.univ, ∅, ∅, ∅] : Fin 4 → Finset (Fin N)) k).filter
      (fun i ↦ i.val < j)).card : ℝ) ≤ (![1, 0, 0, 0] : Fin 4 → ℝ) k * j := by
  intro k j; fin_cases k
  · simpa using (Nat.cast_le (α := ℝ)).2 ((card_le_card_of_injOn Fin.val
      (fun i hi ↦ by simpa using hi) Fin.val_injective.injOn).trans (card_range j).le)
  all_goals simp

private theorem gap212Cap_two : gap212Cap 2 = (397 / 2500 : ℝ) := by norm_num [gap212Cap]

private theorem gap212Cap_seven : gap212Cap 7 = (127 / 625 : ℝ) := by norm_num [gap212Cap]

private theorem gap212Cap_eight : gap212Cap 8 = (521 / 2500 : ℝ) := by norm_num [gap212Cap]


/-! ## Cell `(1,1)` -/

/-- The first group's rank sets for cell `(1,1)`, certificate 1. -/
def uncOneOne₁LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneOne₁LowRanks`. -/
noncomputable def uncOneOne₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,1)`, certificate 1. -/
def uncOneOne₁Ranks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneOne₁Ranks`. -/
noncomputable def uncOneOne₁Dens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- **Cell `(1,1)`, certificate 1.**

Block bounds `777 / 2500`, `0`, `0`, `0`; no cut.
Valid on `4 / 625 < ω₀` and on
`859 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 1 / 2 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3996000 + ϵ, 0.4860000 - ϵ]`. -/
theorem admitsPartition₄_cellOneOne_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 859 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1 / 2 - 2 * ω₀ - slack)
    {y : Fin (1 + 1) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (777 / 5000) 1 1 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncOneOne₁LowRanks uncOneOne₁Ranks ?_ ?_ ?_ ?_
    uncOneOne₁LowDens uncOneOne₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncOneOne₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncOneOne₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncOneOne₁Ranks, uncOneOne₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneOne₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simp [uncOneOne₁Ranks, uncOneOne₁Dens]
    · simp [uncOneOne₁Ranks, uncOneOne₁Dens]
    · simp [uncOneOne₁Ranks, uncOneOne₁Dens]
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncOneOne₁LowRanks, uncOneOne₁Ranks,
          uncOneOne₁LowDens, uncOneOne₁Dens]
        all_goals linarith

/-- **Cell `(1,1)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,1}, B_{1,1}, 1, 1, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellOneOne_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 1) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (777 / 5000) 1 1 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellOneOne_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(1,1)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 1 = gap212Cap 1 = 777 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellOneOne_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 1) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 1) (gap212Params.B j' 1) 1 1
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellOneOne_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(1,2)` -/

/-- The first group's rank sets for cell `(1,2)`, certificate 1. -/
def uncOneTwo₁LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneTwo₁LowRanks`. -/
noncomputable def uncOneTwo₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,2)`, certificate 1. -/
def uncOneTwo₁Ranks : Fin 4 → Finset (Fin 2) :=
  ![{0}, {1}, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneTwo₁Ranks`. -/
noncomputable def uncOneTwo₁Dens : Fin 4 → ℝ := ![1, 1 / 2, 0, 0]

/-- The first group's rank sets for cell `(1,2)`, certificate 2. -/
def uncOneTwo₂LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneTwo₂LowRanks`. -/
noncomputable def uncOneTwo₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,2)`, certificate 2. -/
def uncOneTwo₂Ranks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneTwo₂Ranks`. -/
noncomputable def uncOneTwo₂Dens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- **Cell `(1,2)`, certificate 1.**

Block bounds `1489 / 5000`, `397 / 5000`, `0`, `0`; no cut.
Valid on `4 / 625 < ω₀` and on
`1653 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 2103 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3866000 + ϵ, 0.4066000 - ϵ]`. -/
theorem admitsPartition₄_cellOneTwo_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1653 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2103 / 5000 - 2 * ω₀ - slack)
    {y : Fin (1 + 2) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (397 / 2500) 1 2 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncOneTwo₁LowRanks uncOneTwo₁Ranks ?_ ?_ ?_ ?_
    uncOneTwo₁LowDens uncOneTwo₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncOneTwo₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncOneTwo₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncOneTwo₁Ranks, uncOneTwo₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneTwo₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncOneTwo₁Ranks, uncOneTwo₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneTwo₁Ranks 1) 1 2 (by norm_num) (by decide)
    · simp [uncOneTwo₁Ranks, uncOneTwo₁Dens]
    · simp [uncOneTwo₁Ranks, uncOneTwo₁Dens]
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncOneTwo₁LowRanks, uncOneTwo₁Ranks,
          uncOneTwo₁LowDens, uncOneTwo₁Dens]
        all_goals linarith

/-- **Cell `(1,2)`, certificate 2.**

Block bounds `1571 / 5000`, `0`, `0`, `0`; no cut.
Valid on `4 / 625 < ω₀` and on
`347 / 1000 + 8ω₀ + ϵ ≤ γ ≤ 1 / 2 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4030000 + ϵ, 0.4860000 - ϵ]`. -/
theorem admitsPartition₄_cellOneTwo_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 347 / 1000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1 / 2 - 2 * ω₀ - slack)
    {y : Fin (1 + 2) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (397 / 2500) 1 2 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncOneTwo₂LowRanks uncOneTwo₂Ranks ?_ ?_ ?_ ?_
    uncOneTwo₂LowDens uncOneTwo₂Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncOneTwo₂LowDens]
  · intro k; fin_cases k <;> norm_num [uncOneTwo₂Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncOneTwo₂Ranks, uncOneTwo₂Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneTwo₂Ranks 0) 1 1 (by norm_num) (by decide)
    · simp [uncOneTwo₂Ranks, uncOneTwo₂Dens]
    · simp [uncOneTwo₂Ranks, uncOneTwo₂Dens]
    · simp [uncOneTwo₂Ranks, uncOneTwo₂Dens]
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncOneTwo₂LowRanks, uncOneTwo₂Ranks,
          uncOneTwo₂LowDens, uncOneTwo₂Dens]
        all_goals linarith

/-- **Cell `(1,2)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,1}, B_{1,2}, 1, 2, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 2 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellOneTwo_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 2) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (397 / 2500) 1 2 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (2103 / 5000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellOneTwo_unc₁ hωlo (by linarith) h1 hy
  · exact admitsPartition₄_cellOneTwo_unc₂ hωlo (by linarith) (by linarith) hy

/-- **Cell `(1,2)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 1 = gap212Cap 1 = 777 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellOneTwo_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 2) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 1) (gap212Params.B j' 2) 1 2
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellOneTwo_band hωlo hωhi hγlo hγhi (gap212Cap_two ▸ hy)

/-! ## Cell `(1,4)` -/

/-- The first group's rank sets for cell `(1,4)`, certificate 1. -/
def uncOneFour₁LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneFour₁LowRanks`. -/
noncomputable def uncOneFour₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,4)`, certificate 1. -/
def uncOneFour₁Ranks : Fin 4 → Finset (Fin 4) :=
  ![{0, 1}, {2}, ∅, {3}]

/-- The prefix densities of `Gap212.uncOneFour₁Ranks`. -/
noncomputable def uncOneFour₁Dens : Fin 4 → ℝ := ![1, 1 / 3, 0, 1 / 4]

/-- **Cell `(1,4)`, certificate 1.**

Block bounds `153 / 500`, `167 / 3000`, `0`, `917 / 20000`; no cut.
Valid on `4 / 625 < ω₀` and on
`847 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 1333 / 3000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3948000 + ϵ, 0.4303333 - ϵ]`. -/
theorem admitsPartition₄_cellOneFour_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 847 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1333 / 3000 - 2 * ω₀ - slack)
    {y : Fin (1 + 4) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (917 / 5000) 1 4 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncOneFour₁LowRanks uncOneFour₁Ranks ?_ ?_ ?_ ?_
    uncOneFour₁LowDens uncOneFour₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncOneFour₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncOneFour₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncOneFour₁Ranks, uncOneFour₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneFour₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncOneFour₁Ranks, uncOneFour₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneFour₁Ranks 1) 1 3 (by norm_num) (by decide)
    · simp [uncOneFour₁Ranks, uncOneFour₁Dens]
    · simpa [uncOneFour₁Ranks, uncOneFour₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneFour₁Ranks 3) 1 4 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncOneFour₁LowRanks, uncOneFour₁Ranks,
          uncOneFour₁LowDens, uncOneFour₁Dens]
        all_goals linarith

/-- **Cell `(1,4)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,1}, B_{1,4}, 1, 4, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellOneFour_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 4) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (917 / 5000) 1 4 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellOneFour_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(1,4)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 1 = gap212Cap 1 = 777 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellOneFour_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 4) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 1) (gap212Params.B j' 4) 1 4
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellOneFour_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(1,5)` -/

/-- The first group's rank sets for cell `(1,5)`, certificate 1. -/
def uncOneFive₁LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneFive₁LowRanks`. -/
noncomputable def uncOneFive₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,5)`, certificate 1. -/
def uncOneFive₁Ranks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1}, {2}, {4}, {3}]

/-- The prefix densities of `Gap212.uncOneFive₁Ranks`. -/
noncomputable def uncOneFive₁Dens : Fin 4 → ℝ := ![1, 1 / 3, 1 / 5, 1 / 4]

/-- **Cell `(1,5)`, certificate 1.**

Block bounds `371 / 1250`, `263 / 5000`, `953 / 25000`, `871 / 20000`; no cut.
Valid on `4 / 625 < ω₀` and on
`206 / 625 + 8ω₀ + ϵ ≤ γ ≤ 2237 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3856000 + ϵ, 0.4334000 - ϵ]`. -/
theorem admitsPartition₄_cellOneFive_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 206 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2237 / 5000 - 2 * ω₀ - slack)
    {y : Fin (1 + 5) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (953 / 5000) 1 5 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncOneFive₁LowRanks uncOneFive₁Ranks ?_ ?_ ?_ ?_
    uncOneFive₁LowDens uncOneFive₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncOneFive₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncOneFive₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncOneFive₁Ranks, uncOneFive₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneFive₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncOneFive₁Ranks, uncOneFive₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneFive₁Ranks 1) 1 3 (by norm_num) (by decide)
    · simpa [uncOneFive₁Ranks, uncOneFive₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneFive₁Ranks 2) 1 5 (by norm_num) (by decide)
    · simpa [uncOneFive₁Ranks, uncOneFive₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneFive₁Ranks 3) 1 4 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncOneFive₁LowRanks, uncOneFive₁Ranks,
          uncOneFive₁LowDens, uncOneFive₁Dens]
        all_goals linarith

/-- **Cell `(1,5)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,1}, B_{1,5}, 1, 5, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellOneFive_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 5) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (953 / 5000) 1 5 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellOneFive_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(1,5)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 1 = gap212Cap 1 = 777 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellOneFive_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 5) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 1) (gap212Params.B j' 5) 1 5
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellOneFive_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(1,6)` -/

/-- The first group's rank sets for cell `(1,6)`, certificate 1. -/
def uncOneSix₁LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneSix₁LowRanks`. -/
noncomputable def uncOneSix₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,6)`, certificate 1. -/
def uncOneSix₁Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2}, {5}, {4}, {3}]

/-- The prefix densities of `Gap212.uncOneSix₁Ranks`. -/
noncomputable def uncOneSix₁Dens : Fin 4 → ℝ := ![1, 1 / 6, 1 / 5, 1 / 4]

/-- **Cell `(1,6)`, certificate 1.**

Block bounds `757 / 2500`, `983 / 30000`, `901 / 25000`, `819 / 20000`; no cut.
Valid on `4 / 625 < ω₀` and on
`839 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 14017 / 30000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3916000 + ϵ, 0.4532333 - ϵ]`. -/
theorem admitsPartition₄_cellOneSix_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 839 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 14017 / 30000 - 2 * ω₀ - slack)
    {y : Fin (1 + 6) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (983 / 5000) 1 6 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncOneSix₁LowRanks uncOneSix₁Ranks ?_ ?_ ?_ ?_
    uncOneSix₁LowDens uncOneSix₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncOneSix₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncOneSix₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncOneSix₁Ranks, uncOneSix₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneSix₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncOneSix₁Ranks, uncOneSix₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneSix₁Ranks 1) 1 6 (by norm_num) (by decide)
    · simpa [uncOneSix₁Ranks, uncOneSix₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneSix₁Ranks 2) 1 5 (by norm_num) (by decide)
    · simpa [uncOneSix₁Ranks, uncOneSix₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneSix₁Ranks 3) 1 4 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncOneSix₁LowRanks, uncOneSix₁Ranks,
          uncOneSix₁LowDens, uncOneSix₁Dens]
        all_goals linarith

/-- **Cell `(1,6)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,1}, B_{1,6}, 1, 6, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellOneSix_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 6) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (983 / 5000) 1 6 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellOneSix_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(1,6)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 1 = gap212Cap 1 = 777 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellOneSix_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 6) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 1) (gap212Params.B j' 6) 1 6
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellOneSix_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(1,7)` -/

/-- The first group's rank sets for cell `(1,7)`, certificate 1. -/
def uncOneSeven₁LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneSeven₁LowRanks`. -/
noncomputable def uncOneSeven₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,7)`, certificate 1. -/
def uncOneSeven₁Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2, 3}, {6}, {5}, {4}]

/-- The prefix densities of `Gap212.uncOneSeven₁Ranks`. -/
noncomputable def uncOneSeven₁Dens : Fin 4 → ℝ := ![1, 1 / 7, 1 / 6, 1 / 5]

/-- **Cell `(1,7)`, certificate 1.**

Block bounds `1547 / 5000`, `127 / 4375`, `467 / 15000`, `213 / 6250`; no cut.
Valid on `4 / 625 < ω₀` and on
`1711 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 4121 / 8750 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3982000 + ϵ, 0.4569714 - ϵ]`. -/
theorem admitsPartition₄_cellOneSeven_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1711 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4121 / 8750 - 2 * ω₀ - slack)
    {y : Fin (1 + 7) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (127 / 625) 1 7 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncOneSeven₁LowRanks uncOneSeven₁Ranks ?_ ?_ ?_ ?_
    uncOneSeven₁LowDens uncOneSeven₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncOneSeven₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncOneSeven₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncOneSeven₁Ranks, uncOneSeven₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneSeven₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncOneSeven₁Ranks, uncOneSeven₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneSeven₁Ranks 1) 1 7 (by norm_num) (by decide)
    · simpa [uncOneSeven₁Ranks, uncOneSeven₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneSeven₁Ranks 2) 1 6 (by norm_num) (by decide)
    · simpa [uncOneSeven₁Ranks, uncOneSeven₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneSeven₁Ranks 3) 1 5 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncOneSeven₁LowRanks, uncOneSeven₁Ranks,
          uncOneSeven₁LowDens, uncOneSeven₁Dens]
        all_goals linarith

/-- **Cell `(1,7)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,1}, B_{1,7}, 1, 7, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellOneSeven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 7) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (127 / 625) 1 7 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellOneSeven_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(1,7)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 1 = gap212Cap 1 = 777 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellOneSeven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 7) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 1) (gap212Params.B j' 7) 1 7
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellOneSeven_band hωlo hωhi hγlo hγhi (gap212Cap_seven ▸ hy)

/-! ## Cell `(1,8)` -/

/-- The first group's rank sets for cell `(1,8)`, certificate 1. -/
def uncOneEight₁LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneEight₁LowRanks`. -/
noncomputable def uncOneEight₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,8)`, certificate 1. -/
def uncOneEight₁Ranks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1, 2, 3}, {4, 7}, {6}, {5}]

/-- The prefix densities of `Gap212.uncOneEight₁Ranks`. -/
noncomputable def uncOneEight₁Dens : Fin 4 → ℝ := ![1, 1 / 4, 1 / 7, 1 / 6]

/-- **Cell `(1,8)`, certificate 1.**

Block bounds `1491 / 5000`, `521 / 10000`, `24 / 875`, `439 / 15000`; no cut.
Valid on `4 / 625 < ω₀` and on
`331 / 1000 + 8ω₀ + ϵ ≤ γ ≤ 4479 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3870000 + ϵ, 0.4339000 - ϵ]`. -/
theorem admitsPartition₄_cellOneEight_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 331 / 1000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4479 / 10000 - 2 * ω₀ - slack)
    {y : Fin (1 + 8) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (521 / 2500) 1 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncOneEight₁LowRanks uncOneEight₁Ranks ?_ ?_ ?_ ?_
    uncOneEight₁LowDens uncOneEight₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncOneEight₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncOneEight₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncOneEight₁Ranks, uncOneEight₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneEight₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncOneEight₁Ranks, uncOneEight₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneEight₁Ranks 1) 1 4 (by norm_num) (by decide)
    · simpa [uncOneEight₁Ranks, uncOneEight₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneEight₁Ranks 2) 1 7 (by norm_num) (by decide)
    · simpa [uncOneEight₁Ranks, uncOneEight₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneEight₁Ranks 3) 1 6 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncOneEight₁LowRanks, uncOneEight₁Ranks,
          uncOneEight₁LowDens, uncOneEight₁Dens]
        all_goals linarith

/-- **Cell `(1,8)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,1}, B_{1,8}, 1, 8, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellOneEight_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 8) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (521 / 2500) 1 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellOneEight_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(1,8)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 1 = gap212Cap 1 = 777 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellOneEight_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 8) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 1) (gap212Params.B j' 8) 1 8
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellOneEight_band hωlo hωhi hγlo hγhi (gap212Cap_eight ▸ hy)

/-! ## Cell `(1,9)` -/

/-- The first group's rank sets for cell `(1,9)`, certificate 1. -/
def uncOneNine₁LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneNine₁LowRanks`. -/
noncomputable def uncOneNine₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,9)`, certificate 1. -/
def uncOneNine₁Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2, 3, 4}, {8}, {6}, {5, 7}]

/-- The prefix densities of `Gap212.uncOneNine₁Ranks`. -/
noncomputable def uncOneNine₁Dens : Fin 4 → ℝ := ![1, 1 / 9, 1 / 7, 1 / 4]

/-- **Cell `(1,9)`, certificate 1.**

Block bounds `189 / 625`, `1063 / 45000`, `899 / 35000`, `981 / 20000`; no cut.
Valid on `4 / 625 < ω₀` and on
`419 / 1250 + 8ω₀ + ϵ ≤ γ ≤ 21437 / 45000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3912000 + ϵ, 0.4623778 - ϵ]`. -/
theorem admitsPartition₄_cellOneNine_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 419 / 1250 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 21437 / 45000 - 2 * ω₀ - slack)
    {y : Fin (1 + 9) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (1063 / 5000) 1 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncOneNine₁LowRanks uncOneNine₁Ranks ?_ ?_ ?_ ?_
    uncOneNine₁LowDens uncOneNine₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncOneNine₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncOneNine₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncOneNine₁Ranks, uncOneNine₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneNine₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncOneNine₁Ranks, uncOneNine₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneNine₁Ranks 1) 1 9 (by norm_num) (by decide)
    · simpa [uncOneNine₁Ranks, uncOneNine₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneNine₁Ranks 2) 1 7 (by norm_num) (by decide)
    · simpa [uncOneNine₁Ranks, uncOneNine₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneNine₁Ranks 3) 1 4 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncOneNine₁LowRanks, uncOneNine₁Ranks,
          uncOneNine₁LowDens, uncOneNine₁Dens]
        all_goals linarith

/-- **Cell `(1,9)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,1}, B_{1,9}, 1, 9, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellOneNine_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 9) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (1063 / 5000) 1 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellOneNine_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(1,9)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 1 = gap212Cap 1 = 777 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellOneNine_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 9) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 1) (gap212Params.B j' 9) 1 9
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellOneNine_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(1,10)` -/

/-- The first group's rank sets for cell `(1,10)`, certificate 1. -/
def uncOneTen₁LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneTen₁LowRanks`. -/
noncomputable def uncOneTen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,10)`, certificate 1. -/
def uncOneTen₁Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3, 4, 5}, {9}, {7}, {6, 8}]

/-- The prefix densities of `Gap212.uncOneTen₁Ranks`. -/
noncomputable def uncOneTen₁Dens : Fin 4 → ℝ := ![1, 1 / 10, 1 / 8, 2 / 9]

/-- **Cell `(1,10)`, certificate 1.**

Block bounds `153 / 500`, `1081 / 50000`, `917 / 40000`, `111 / 2500`; no cut.
Valid on `4 / 625 < ω₀` and on
`847 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 23919 / 50000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3948000 + ϵ, 0.4643800 - ϵ]`. -/
theorem admitsPartition₄_cellOneTen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 847 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 23919 / 50000 - 2 * ω₀ - slack)
    {y : Fin (1 + 10) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (1081 / 5000) 1 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncOneTen₁LowRanks uncOneTen₁Ranks ?_ ?_ ?_ ?_
    uncOneTen₁LowDens uncOneTen₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncOneTen₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncOneTen₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncOneTen₁Ranks, uncOneTen₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneTen₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncOneTen₁Ranks, uncOneTen₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneTen₁Ranks 1) 1 10 (by norm_num) (by decide)
    · simpa [uncOneTen₁Ranks, uncOneTen₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneTen₁Ranks 2) 1 8 (by norm_num) (by decide)
    · simpa [uncOneTen₁Ranks, uncOneTen₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneTen₁Ranks 3) 2 9 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncOneTen₁LowRanks, uncOneTen₁Ranks,
          uncOneTen₁LowDens, uncOneTen₁Dens]
        all_goals linarith

/-- **Cell `(1,10)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,1}, B_{1,10}, 1, 10, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellOneTen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 10) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (1081 / 5000) 1 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellOneTen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(1,10)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 1 = gap212Cap 1 = 777 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellOneTen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 10) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 1) (gap212Params.B j' 10) 1 10
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellOneTen_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(1,11)` -/

/-- The first group's rank sets for cell `(1,11)`, certificate 1. -/
def uncOneEleven₁LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneEleven₁LowRanks`. -/
noncomputable def uncOneEleven₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,11)`, certificate 1. -/
def uncOneEleven₁Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3, 4, 5, 6}, ∅, {8, 10}, {7, 9}]

/-- The prefix densities of `Gap212.uncOneEleven₁Ranks`. -/
noncomputable def uncOneEleven₁Dens : Fin 4 → ℝ := ![1, 0, 2 / 11, 1 / 5]

/-- **Cell `(1,11)`, certificate 1.**

Block bounds `153 / 500`, `0`, `1081 / 27500`, `999 / 25000`; no cut.
Valid on `4 / 625 < ω₀` and on
`847 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 1 / 2 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3948000 + ϵ, 0.4860000 - ϵ]`. -/
theorem admitsPartition₄_cellOneEleven_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 847 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1 / 2 - 2 * ω₀ - slack)
    {y : Fin (1 + 11) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (1081 / 5000) 1 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncOneEleven₁LowRanks uncOneEleven₁Ranks ?_ ?_ ?_ ?_
    uncOneEleven₁LowDens uncOneEleven₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncOneEleven₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncOneEleven₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncOneEleven₁Ranks, uncOneEleven₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneEleven₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simp [uncOneEleven₁Ranks, uncOneEleven₁Dens]
    · simpa [uncOneEleven₁Ranks, uncOneEleven₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneEleven₁Ranks 2) 2 11 (by norm_num) (by decide)
    · simpa [uncOneEleven₁Ranks, uncOneEleven₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneEleven₁Ranks 3) 1 5 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncOneEleven₁LowRanks, uncOneEleven₁Ranks,
          uncOneEleven₁LowDens, uncOneEleven₁Dens]
        all_goals linarith

/-- **Cell `(1,11)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,1}, B_{1,11}, 1, 11, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellOneEleven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 11) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (1081 / 5000) 1 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellOneEleven_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(1,11)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 1 = gap212Cap 1 = 777 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellOneEleven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 11) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 1) (gap212Params.B j' 11) 1 11
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellOneEleven_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(1,12)` -/

/-- The first group's rank sets for cell `(1,12)`, certificate 1. -/
def uncOneTwelve₁LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneTwelve₁LowRanks`. -/
noncomputable def uncOneTwelve₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,12)`, certificate 1. -/
def uncOneTwelve₁Ranks : Fin 4 → Finset (Fin 12) :=
  ![{0, 1, 2, 3, 4, 5, 6, 7}, ∅, {9, 11}, {8, 10}]

/-- The prefix densities of `Gap212.uncOneTwelve₁Ranks`. -/
noncomputable def uncOneTwelve₁Dens : Fin 4 → ℝ := ![1, 0, 1 / 6, 2 / 11]

/-- **Cell `(1,12)`, certificate 1.**

Block bounds `153 / 500`, `0`, `1081 / 30000`, `999 / 27500`; no cut.
Valid on `4 / 625 < ω₀` and on
`847 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 1 / 2 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3948000 + ϵ, 0.4860000 - ϵ]`. -/
theorem admitsPartition₄_cellOneTwelve_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 847 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1 / 2 - 2 * ω₀ - slack)
    {y : Fin (1 + 12) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (1081 / 5000) 1 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncOneTwelve₁LowRanks uncOneTwelve₁Ranks ?_ ?_ ?_ ?_
    uncOneTwelve₁LowDens uncOneTwelve₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncOneTwelve₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncOneTwelve₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncOneTwelve₁Ranks, uncOneTwelve₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneTwelve₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simp [uncOneTwelve₁Ranks, uncOneTwelve₁Dens]
    · simpa [uncOneTwelve₁Ranks, uncOneTwelve₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneTwelve₁Ranks 2) 1 6 (by norm_num) (by decide)
    · simpa [uncOneTwelve₁Ranks, uncOneTwelve₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneTwelve₁Ranks 3) 2 11 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncOneTwelve₁LowRanks, uncOneTwelve₁Ranks,
          uncOneTwelve₁LowDens, uncOneTwelve₁Dens]
        all_goals linarith

/-- **Cell `(1,12)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,1}, B_{1,12}, 1, 12, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellOneTwelve_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 12) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (1081 / 5000) 1 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellOneTwelve_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(1,12)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 1 = gap212Cap 1 = 777 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellOneTwelve_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 12) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 1) (gap212Params.B j' 12) 1 12
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellOneTwelve_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(1,13)` -/

/-- The first group's rank sets for cell `(1,13)`, certificate 1. -/
def uncOneThirteen₁LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncOneThirteen₁LowRanks`. -/
noncomputable def uncOneThirteen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,13)`, certificate 1. -/
def uncOneThirteen₁Ranks : Fin 4 → Finset (Fin 13) :=
  ![{2, 3, 5, 6, 8, 9, 11, 12}, ∅, {0, 1}, {4, 7, 10}]

/-- The prefix densities of `Gap212.uncOneThirteen₁Ranks`. -/
noncomputable def uncOneThirteen₁Dens : Fin 4 → ℝ := ![8 / 13, 0, 1, 3 / 11]

/-- **Cell `(1,13)`, certificate 1.**

Block bounds `18749 / 65000`, `0`, `179 / 5000`, `2751 / 55000`; no cut.
Valid on `4 / 625 < ω₀` and on
`20881 / 65000 + 8ω₀ + ϵ ≤ γ ≤ 1 / 2 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3772462 + ϵ, 0.4860000 - ϵ]`. -/
theorem admitsPartition₄_cellOneThirteen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 20881 / 65000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1 / 2 - 2 * ω₀ - slack)
    {y : Fin (1 + 13) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (1081 / 5000) 1 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncOneThirteen₁LowRanks uncOneThirteen₁Ranks ?_ ?_ ?_ ?_
    uncOneThirteen₁LowDens uncOneThirteen₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncOneThirteen₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncOneThirteen₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncOneThirteen₁Ranks, uncOneThirteen₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneThirteen₁Ranks 0) 8 13 (by norm_num) (by decide)
    · simp [uncOneThirteen₁Ranks, uncOneThirteen₁Dens]
    · simpa [uncOneThirteen₁Ranks, uncOneThirteen₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneThirteen₁Ranks 2) 1 1 (by norm_num) (by decide)
    · simpa [uncOneThirteen₁Ranks, uncOneThirteen₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncOneThirteen₁Ranks 3) 3 11 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncOneThirteen₁LowRanks, uncOneThirteen₁Ranks,
          uncOneThirteen₁LowDens, uncOneThirteen₁Dens]
        all_goals linarith

/-- **Cell `(1,13)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,1}, B_{1,13}, 1, 13, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellOneThirteen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 13) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (1081 / 5000) 1 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellOneThirteen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(1,13)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 1 = gap212Cap 1 = 777 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellOneThirteen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 13) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 1) (gap212Params.B j' 13) 1 13
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellOneThirteen_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(2,2)` -/

/-- The first group's rank sets for cell `(2,2)`, certificate 1. -/
def uncTwoTwo₁LowRanks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwoTwo₁LowRanks`. -/
noncomputable def uncTwoTwo₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(2,2)`, certificate 1. -/
def uncTwoTwo₁Ranks : Fin 4 → Finset (Fin 2) :=
  ![{0}, {1}, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwoTwo₁Ranks`. -/
noncomputable def uncTwoTwo₁Dens : Fin 4 → ℝ := ![1, 1 / 2, 0, 0]

/-- The first group's rank sets for cell `(2,2)`, certificate 2. -/
def uncTwoTwo₂LowRanks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwoTwo₂LowRanks`. -/
noncomputable def uncTwoTwo₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(2,2)`, certificate 2. -/
def uncTwoTwo₂Ranks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwoTwo₂Ranks`. -/
noncomputable def uncTwoTwo₂Dens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- **Cell `(2,2)`, certificate 1.**

Block bounds `753 / 2500`, `397 / 5000`, `0`, `0`; no cut.
Valid on `4 / 625 < ω₀` and on
`167 / 500 + 8ω₀ + ϵ ≤ γ ≤ 2103 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3900000 + ϵ, 0.4066000 - ϵ]`. -/
theorem admitsPartition₄_cellTwoTwo_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 167 / 500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2103 / 5000 - 2 * ω₀ - slack)
    {y : Fin (2 + 2) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (397 / 2500) 2 2 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncTwoTwo₁LowRanks uncTwoTwo₁Ranks ?_ ?_ ?_ ?_
    uncTwoTwo₁LowDens uncTwoTwo₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncTwoTwo₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncTwoTwo₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncTwoTwo₁Ranks, uncTwoTwo₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoTwo₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncTwoTwo₁Ranks, uncTwoTwo₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoTwo₁Ranks 1) 1 2 (by norm_num) (by decide)
    · simp [uncTwoTwo₁Ranks, uncTwoTwo₁Dens]
    · simp [uncTwoTwo₁Ranks, uncTwoTwo₁Dens]
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncTwoTwo₁LowRanks, uncTwoTwo₁Ranks,
          uncTwoTwo₁LowDens, uncTwoTwo₁Dens]
        all_goals linarith

/-- **Cell `(2,2)`, certificate 2.**

Block bounds `397 / 1250`, `0`, `0`, `0`; no cut.
Valid on `4 / 625 < ω₀` and on
`219 / 625 + 8ω₀ + ϵ ≤ γ ≤ 1 / 2 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4064000 + ϵ, 0.4860000 - ϵ]`. -/
theorem admitsPartition₄_cellTwoTwo_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 219 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1 / 2 - 2 * ω₀ - slack)
    {y : Fin (2 + 2) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (397 / 2500) 2 2 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncTwoTwo₂LowRanks uncTwoTwo₂Ranks ?_ ?_ ?_ ?_
    uncTwoTwo₂LowDens uncTwoTwo₂Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncTwoTwo₂LowDens]
  · intro k; fin_cases k <;> norm_num [uncTwoTwo₂Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncTwoTwo₂Ranks, uncTwoTwo₂Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoTwo₂Ranks 0) 1 1 (by norm_num) (by decide)
    · simp [uncTwoTwo₂Ranks, uncTwoTwo₂Dens]
    · simp [uncTwoTwo₂Ranks, uncTwoTwo₂Dens]
    · simp [uncTwoTwo₂Ranks, uncTwoTwo₂Dens]
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncTwoTwo₂LowRanks, uncTwoTwo₂Ranks,
          uncTwoTwo₂LowDens, uncTwoTwo₂Dens]
        all_goals linarith

/-- **Cell `(2,2)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,2}, B_{1,2}, 2, 2, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 2 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellTwoTwo_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 2) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (397 / 2500) 2 2 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (2103 / 5000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellTwoTwo_unc₁ hωlo (by linarith) h1 hy
  · exact admitsPartition₄_cellTwoTwo_unc₂ hωlo (by linarith) (by linarith) hy

/-- **Cell `(2,2)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 2 = gap212Cap 2 = 397 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellTwoTwo_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 2) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 2) (gap212Params.B j' 2) 2 2
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTwoTwo_band hωlo hωhi hγlo hγhi (gap212Cap_two ▸ hy)

/-! ## Cell `(2,4)` -/

/-- The first group's rank sets for cell `(2,4)`, certificate 1. -/
def uncTwoFour₁LowRanks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwoFour₁LowRanks`. -/
noncomputable def uncTwoFour₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(2,4)`, certificate 1. -/
def uncTwoFour₁Ranks : Fin 4 → Finset (Fin 4) :=
  ![{0, 1}, {2}, ∅, {3}]

/-- The prefix densities of `Gap212.uncTwoFour₁Ranks`. -/
noncomputable def uncTwoFour₁Dens : Fin 4 → ℝ := ![1, 1 / 3, 0, 1 / 4]

/-- **Cell `(2,4)`, certificate 1.**

Block bounds `1547 / 5000`, `167 / 3000`, `0`, `917 / 20000`; no cut.
Valid on `4 / 625 < ω₀` and on
`1711 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 1333 / 3000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3982000 + ϵ, 0.4303333 - ϵ]`. -/
theorem admitsPartition₄_cellTwoFour_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1711 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1333 / 3000 - 2 * ω₀ - slack)
    {y : Fin (2 + 4) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (917 / 5000) 2 4 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncTwoFour₁LowRanks uncTwoFour₁Ranks ?_ ?_ ?_ ?_
    uncTwoFour₁LowDens uncTwoFour₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncTwoFour₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncTwoFour₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncTwoFour₁Ranks, uncTwoFour₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoFour₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncTwoFour₁Ranks, uncTwoFour₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoFour₁Ranks 1) 1 3 (by norm_num) (by decide)
    · simp [uncTwoFour₁Ranks, uncTwoFour₁Dens]
    · simpa [uncTwoFour₁Ranks, uncTwoFour₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoFour₁Ranks 3) 1 4 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncTwoFour₁LowRanks, uncTwoFour₁Ranks,
          uncTwoFour₁LowDens, uncTwoFour₁Dens]
        all_goals linarith

/-- **Cell `(2,4)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,2}, B_{1,4}, 2, 4, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellTwoFour_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 4) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (917 / 5000) 2 4 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellTwoFour_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(2,4)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 2 = gap212Cap 2 = 397 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellTwoFour_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 4) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 2) (gap212Params.B j' 4) 2 4
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTwoFour_band hωlo hωhi hγlo hγhi (gap212Cap_two ▸ hy)

/-! ## Cell `(2,5)` -/

/-- The first group's rank sets for cell `(2,5)`, certificate 1. -/
def uncTwoFive₁LowRanks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwoFive₁LowRanks`. -/
noncomputable def uncTwoFive₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(2,5)`, certificate 1. -/
def uncTwoFive₁Ranks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1}, {2}, {4}, {3}]

/-- The prefix densities of `Gap212.uncTwoFive₁Ranks`. -/
noncomputable def uncTwoFive₁Dens : Fin 4 → ℝ := ![1, 1 / 3, 1 / 5, 1 / 4]

/-- **Cell `(2,5)`, certificate 1.**

Block bounds `1501 / 5000`, `263 / 5000`, `953 / 25000`, `871 / 20000`; no cut.
Valid on `4 / 625 < ω₀` and on
`333 / 1000 + 8ω₀ + ϵ ≤ γ ≤ 2237 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3890000 + ϵ, 0.4334000 - ϵ]`. -/
theorem admitsPartition₄_cellTwoFive_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 333 / 1000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2237 / 5000 - 2 * ω₀ - slack)
    {y : Fin (2 + 5) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (953 / 5000) 2 5 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncTwoFive₁LowRanks uncTwoFive₁Ranks ?_ ?_ ?_ ?_
    uncTwoFive₁LowDens uncTwoFive₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncTwoFive₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncTwoFive₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncTwoFive₁Ranks, uncTwoFive₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoFive₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncTwoFive₁Ranks, uncTwoFive₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoFive₁Ranks 1) 1 3 (by norm_num) (by decide)
    · simpa [uncTwoFive₁Ranks, uncTwoFive₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoFive₁Ranks 2) 1 5 (by norm_num) (by decide)
    · simpa [uncTwoFive₁Ranks, uncTwoFive₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoFive₁Ranks 3) 1 4 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncTwoFive₁LowRanks, uncTwoFive₁Ranks,
          uncTwoFive₁LowDens, uncTwoFive₁Dens]
        all_goals linarith

/-- **Cell `(2,5)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,2}, B_{1,5}, 2, 5, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellTwoFive_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 5) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (953 / 5000) 2 5 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellTwoFive_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(2,5)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 2 = gap212Cap 2 = 397 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellTwoFive_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 5) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 2) (gap212Params.B j' 5) 2 5
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTwoFive_band hωlo hωhi hγlo hγhi (gap212Cap_two ▸ hy)

/-! ## Cell `(2,6)` -/

/-- The first group's rank sets for cell `(2,6)`, certificate 1. -/
def uncTwoSix₁LowRanks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwoSix₁LowRanks`. -/
noncomputable def uncTwoSix₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(2,6)`, certificate 1. -/
def uncTwoSix₁Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2}, {5}, {4}, {3}]

/-- The prefix densities of `Gap212.uncTwoSix₁Ranks`. -/
noncomputable def uncTwoSix₁Dens : Fin 4 → ℝ := ![1, 1 / 6, 1 / 5, 1 / 4]

/-- **Cell `(2,6)`, certificate 1.**

Block bounds `1531 / 5000`, `983 / 30000`, `901 / 25000`, `819 / 20000`; no cut.
Valid on `4 / 625 < ω₀` and on
`339 / 1000 + 8ω₀ + ϵ ≤ γ ≤ 14017 / 30000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3950000 + ϵ, 0.4532333 - ϵ]`. -/
theorem admitsPartition₄_cellTwoSix_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 339 / 1000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 14017 / 30000 - 2 * ω₀ - slack)
    {y : Fin (2 + 6) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (983 / 5000) 2 6 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncTwoSix₁LowRanks uncTwoSix₁Ranks ?_ ?_ ?_ ?_
    uncTwoSix₁LowDens uncTwoSix₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncTwoSix₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncTwoSix₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncTwoSix₁Ranks, uncTwoSix₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoSix₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncTwoSix₁Ranks, uncTwoSix₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoSix₁Ranks 1) 1 6 (by norm_num) (by decide)
    · simpa [uncTwoSix₁Ranks, uncTwoSix₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoSix₁Ranks 2) 1 5 (by norm_num) (by decide)
    · simpa [uncTwoSix₁Ranks, uncTwoSix₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoSix₁Ranks 3) 1 4 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncTwoSix₁LowRanks, uncTwoSix₁Ranks,
          uncTwoSix₁LowDens, uncTwoSix₁Dens]
        all_goals linarith

/-- **Cell `(2,6)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,2}, B_{1,6}, 2, 6, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellTwoSix_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 6) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (983 / 5000) 2 6 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellTwoSix_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(2,6)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 2 = gap212Cap 2 = 397 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellTwoSix_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 6) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 2) (gap212Params.B j' 6) 2 6
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTwoSix_band hωlo hωhi hγlo hγhi (gap212Cap_two ▸ hy)

/-! ## Cell `(2,7)` -/

/-- The first group's rank sets for cell `(2,7)`, certificate 1. -/
def uncTwoSeven₁LowRanks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwoSeven₁LowRanks`. -/
noncomputable def uncTwoSeven₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(2,7)`, certificate 1. -/
def uncTwoSeven₁Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2}, {3, 6}, {5}, {4}]

/-- The prefix densities of `Gap212.uncTwoSeven₁Ranks`. -/
noncomputable def uncTwoSeven₁Dens : Fin 4 → ℝ := ![1, 2 / 7, 1 / 6, 1 / 5]

/-- **Cell `(2,7)`, certificate 1.**

Block bounds `741 / 2500`, `254 / 4375`, `467 / 15000`, `213 / 6250`; no cut.
Valid on `4 / 625 < ω₀` and on
`823 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 3867 / 8750 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3852000 + ϵ, 0.4279429 - ϵ]`. -/
theorem admitsPartition₄_cellTwoSeven_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 823 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 3867 / 8750 - 2 * ω₀ - slack)
    {y : Fin (2 + 7) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (127 / 625) 2 7 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncTwoSeven₁LowRanks uncTwoSeven₁Ranks ?_ ?_ ?_ ?_
    uncTwoSeven₁LowDens uncTwoSeven₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncTwoSeven₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncTwoSeven₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncTwoSeven₁Ranks, uncTwoSeven₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoSeven₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncTwoSeven₁Ranks, uncTwoSeven₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoSeven₁Ranks 1) 2 7 (by norm_num) (by decide)
    · simpa [uncTwoSeven₁Ranks, uncTwoSeven₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoSeven₁Ranks 2) 1 6 (by norm_num) (by decide)
    · simpa [uncTwoSeven₁Ranks, uncTwoSeven₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoSeven₁Ranks 3) 1 5 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncTwoSeven₁LowRanks, uncTwoSeven₁Ranks,
          uncTwoSeven₁LowDens, uncTwoSeven₁Dens]
        all_goals linarith

/-- **Cell `(2,7)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,2}, B_{1,7}, 2, 7, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellTwoSeven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 7) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (127 / 625) 2 7 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellTwoSeven_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(2,7)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 2 = gap212Cap 2 = 397 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellTwoSeven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 7) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 2) (gap212Params.B j' 7) 2 7
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTwoSeven_band hωlo hωhi hγlo hγhi
    (gap212Cap_two ▸ gap212Cap_seven ▸ hy)

/-! ## Cell `(2,8)` -/

/-- The first group's rank sets for cell `(2,8)`, certificate 1. -/
def uncTwoEight₁LowRanks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwoEight₁LowRanks`. -/
noncomputable def uncTwoEight₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(2,8)`, certificate 1. -/
def uncTwoEight₁Ranks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1, 2, 3}, {4, 7}, {6}, {5}]

/-- The prefix densities of `Gap212.uncTwoEight₁Ranks`. -/
noncomputable def uncTwoEight₁Dens : Fin 4 → ℝ := ![1, 1 / 4, 1 / 7, 1 / 6]

/-- **Cell `(2,8)`, certificate 1.**

Block bounds `377 / 1250`, `521 / 10000`, `24 / 875`, `439 / 15000`; no cut.
Valid on `4 / 625 < ω₀` and on
`209 / 625 + 8ω₀ + ϵ ≤ γ ≤ 4479 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3904000 + ϵ, 0.4339000 - ϵ]`. -/
theorem admitsPartition₄_cellTwoEight_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 209 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4479 / 10000 - 2 * ω₀ - slack)
    {y : Fin (2 + 8) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (521 / 2500) 2 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncTwoEight₁LowRanks uncTwoEight₁Ranks ?_ ?_ ?_ ?_
    uncTwoEight₁LowDens uncTwoEight₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncTwoEight₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncTwoEight₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncTwoEight₁Ranks, uncTwoEight₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoEight₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncTwoEight₁Ranks, uncTwoEight₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoEight₁Ranks 1) 1 4 (by norm_num) (by decide)
    · simpa [uncTwoEight₁Ranks, uncTwoEight₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoEight₁Ranks 2) 1 7 (by norm_num) (by decide)
    · simpa [uncTwoEight₁Ranks, uncTwoEight₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoEight₁Ranks 3) 1 6 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncTwoEight₁LowRanks, uncTwoEight₁Ranks,
          uncTwoEight₁LowDens, uncTwoEight₁Dens]
        all_goals linarith

/-- **Cell `(2,8)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,2}, B_{1,8}, 2, 8, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellTwoEight_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 8) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (521 / 2500) 2 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellTwoEight_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(2,8)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 2 = gap212Cap 2 = 397 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellTwoEight_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 8) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 2) (gap212Params.B j' 8) 2 8
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTwoEight_band hωlo hωhi hγlo hγhi
    (gap212Cap_two ▸ gap212Cap_eight ▸ hy)

/-! ## Cell `(2,9)` -/

/-- The first group's rank sets for cell `(2,9)`, certificate 1. -/
def uncTwoNine₁LowRanks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwoNine₁LowRanks`. -/
noncomputable def uncTwoNine₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(2,9)`, certificate 1. -/
def uncTwoNine₁Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2, 3, 4}, {8}, {6}, {5, 7}]

/-- The prefix densities of `Gap212.uncTwoNine₁Ranks`. -/
noncomputable def uncTwoNine₁Dens : Fin 4 → ℝ := ![1, 1 / 9, 1 / 7, 1 / 4]

/-- **Cell `(2,9)`, certificate 1.**

Block bounds `1529 / 5000`, `1063 / 45000`, `899 / 35000`, `981 / 20000`; no cut.
Valid on `4 / 625 < ω₀` and on
`1693 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 21437 / 45000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3946000 + ϵ, 0.4623778 - ϵ]`. -/
theorem admitsPartition₄_cellTwoNine_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1693 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 21437 / 45000 - 2 * ω₀ - slack)
    {y : Fin (2 + 9) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (1063 / 5000) 2 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncTwoNine₁LowRanks uncTwoNine₁Ranks ?_ ?_ ?_ ?_
    uncTwoNine₁LowDens uncTwoNine₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncTwoNine₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncTwoNine₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncTwoNine₁Ranks, uncTwoNine₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoNine₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncTwoNine₁Ranks, uncTwoNine₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoNine₁Ranks 1) 1 9 (by norm_num) (by decide)
    · simpa [uncTwoNine₁Ranks, uncTwoNine₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoNine₁Ranks 2) 1 7 (by norm_num) (by decide)
    · simpa [uncTwoNine₁Ranks, uncTwoNine₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoNine₁Ranks 3) 1 4 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncTwoNine₁LowRanks, uncTwoNine₁Ranks,
          uncTwoNine₁LowDens, uncTwoNine₁Dens]
        all_goals linarith

/-- **Cell `(2,9)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,2}, B_{1,9}, 2, 9, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellTwoNine_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 9) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (1063 / 5000) 2 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellTwoNine_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(2,9)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 2 = gap212Cap 2 = 397 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellTwoNine_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 9) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 2) (gap212Params.B j' 9) 2 9
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTwoNine_band hωlo hωhi hγlo hγhi (gap212Cap_two ▸ hy)

/-! ## Cell `(2,10)` -/

/-- The first group's rank sets for cell `(2,10)`, certificate 1. -/
def uncTwoTen₁LowRanks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwoTen₁LowRanks`. -/
noncomputable def uncTwoTen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(2,10)`, certificate 1. -/
def uncTwoTen₁Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3, 4, 5}, {9}, {7}, {6, 8}]

/-- The prefix densities of `Gap212.uncTwoTen₁Ranks`. -/
noncomputable def uncTwoTen₁Dens : Fin 4 → ℝ := ![1, 1 / 10, 1 / 8, 2 / 9]

/-- **Cell `(2,10)`, certificate 1.**

Block bounds `1547 / 5000`, `1081 / 50000`, `917 / 40000`, `111 / 2500`; no cut.
Valid on `4 / 625 < ω₀` and on
`1711 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 23919 / 50000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3982000 + ϵ, 0.4643800 - ϵ]`. -/
theorem admitsPartition₄_cellTwoTen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1711 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 23919 / 50000 - 2 * ω₀ - slack)
    {y : Fin (2 + 10) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (1081 / 5000) 2 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncTwoTen₁LowRanks uncTwoTen₁Ranks ?_ ?_ ?_ ?_
    uncTwoTen₁LowDens uncTwoTen₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncTwoTen₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncTwoTen₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncTwoTen₁Ranks, uncTwoTen₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoTen₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simpa [uncTwoTen₁Ranks, uncTwoTen₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoTen₁Ranks 1) 1 10 (by norm_num) (by decide)
    · simpa [uncTwoTen₁Ranks, uncTwoTen₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoTen₁Ranks 2) 1 8 (by norm_num) (by decide)
    · simpa [uncTwoTen₁Ranks, uncTwoTen₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoTen₁Ranks 3) 2 9 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncTwoTen₁LowRanks, uncTwoTen₁Ranks,
          uncTwoTen₁LowDens, uncTwoTen₁Dens]
        all_goals linarith

/-- **Cell `(2,10)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,2}, B_{1,10}, 2, 10, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellTwoTen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 10) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (1081 / 5000) 2 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellTwoTen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(2,10)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 2 = gap212Cap 2 = 397 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellTwoTen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 10) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 2) (gap212Params.B j' 10) 2 10
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTwoTen_band hωlo hωhi hγlo hγhi (gap212Cap_two ▸ hy)

/-! ## Cell `(2,11)` -/

/-- The first group's rank sets for cell `(2,11)`, certificate 1. -/
def uncTwoEleven₁LowRanks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwoEleven₁LowRanks`. -/
noncomputable def uncTwoEleven₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(2,11)`, certificate 1. -/
def uncTwoEleven₁Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3, 4, 5, 6}, ∅, {8, 10}, {7, 9}]

/-- The prefix densities of `Gap212.uncTwoEleven₁Ranks`. -/
noncomputable def uncTwoEleven₁Dens : Fin 4 → ℝ := ![1, 0, 2 / 11, 1 / 5]

/-- **Cell `(2,11)`, certificate 1.**

Block bounds `1547 / 5000`, `0`, `1081 / 27500`, `999 / 25000`; no cut.
Valid on `4 / 625 < ω₀` and on
`1711 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 1 / 2 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3982000 + ϵ, 0.4860000 - ϵ]`. -/
theorem admitsPartition₄_cellTwoEleven_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1711 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1 / 2 - 2 * ω₀ - slack)
    {y : Fin (2 + 11) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (1081 / 5000) 2 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncTwoEleven₁LowRanks uncTwoEleven₁Ranks ?_ ?_ ?_ ?_
    uncTwoEleven₁LowDens uncTwoEleven₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncTwoEleven₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncTwoEleven₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncTwoEleven₁Ranks, uncTwoEleven₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoEleven₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simp [uncTwoEleven₁Ranks, uncTwoEleven₁Dens]
    · simpa [uncTwoEleven₁Ranks, uncTwoEleven₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoEleven₁Ranks 2) 2 11 (by norm_num) (by decide)
    · simpa [uncTwoEleven₁Ranks, uncTwoEleven₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoEleven₁Ranks 3) 1 5 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncTwoEleven₁LowRanks, uncTwoEleven₁Ranks,
          uncTwoEleven₁LowDens, uncTwoEleven₁Dens]
        all_goals linarith

/-- **Cell `(2,11)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,2}, B_{1,11}, 2, 11, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellTwoEleven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 11) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (1081 / 5000) 2 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellTwoEleven_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(2,11)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 2 = gap212Cap 2 = 397 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellTwoEleven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 11) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 2) (gap212Params.B j' 11) 2 11
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTwoEleven_band hωlo hωhi hγlo hγhi (gap212Cap_two ▸ hy)

/-! ## Cell `(2,12)` -/

/-- The first group's rank sets for cell `(2,12)`, certificate 1. -/
def uncTwoTwelve₁LowRanks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwoTwelve₁LowRanks`. -/
noncomputable def uncTwoTwelve₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(2,12)`, certificate 1. -/
def uncTwoTwelve₁Ranks : Fin 4 → Finset (Fin 12) :=
  ![{0, 1, 2, 3, 4, 5, 6, 7}, ∅, {9, 11}, {8, 10}]

/-- The prefix densities of `Gap212.uncTwoTwelve₁Ranks`. -/
noncomputable def uncTwoTwelve₁Dens : Fin 4 → ℝ := ![1, 0, 1 / 6, 2 / 11]

/-- **Cell `(2,12)`, certificate 1.**

Block bounds `1547 / 5000`, `0`, `1081 / 30000`, `999 / 27500`; no cut.
Valid on `4 / 625 < ω₀` and on
`1711 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 1 / 2 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3982000 + ϵ, 0.4860000 - ϵ]`. -/
theorem admitsPartition₄_cellTwoTwelve_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1711 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1 / 2 - 2 * ω₀ - slack)
    {y : Fin (2 + 12) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (1081 / 5000) 2 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncTwoTwelve₁LowRanks uncTwoTwelve₁Ranks ?_ ?_ ?_ ?_
    uncTwoTwelve₁LowDens uncTwoTwelve₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncTwoTwelve₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncTwoTwelve₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncTwoTwelve₁Ranks, uncTwoTwelve₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoTwelve₁Ranks 0) 1 1 (by norm_num) (by decide)
    · simp [uncTwoTwelve₁Ranks, uncTwoTwelve₁Dens]
    · simpa [uncTwoTwelve₁Ranks, uncTwoTwelve₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoTwelve₁Ranks 2) 1 6 (by norm_num) (by decide)
    · simpa [uncTwoTwelve₁Ranks, uncTwoTwelve₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoTwelve₁Ranks 3) 2 11 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncTwoTwelve₁LowRanks, uncTwoTwelve₁Ranks,
          uncTwoTwelve₁LowDens, uncTwoTwelve₁Dens]
        all_goals linarith

/-- **Cell `(2,12)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,2}, B_{1,12}, 2, 12, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellTwoTwelve_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 12) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (1081 / 5000) 2 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellTwoTwelve_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(2,12)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 2 = gap212Cap 2 = 397 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellTwoTwelve_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 12) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 2) (gap212Params.B j' 12) 2 12
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTwoTwelve_band hωlo hωhi hγlo hγhi (gap212Cap_two ▸ hy)

/-! ## Cell `(2,13)` -/

/-- The first group's rank sets for cell `(2,13)`, certificate 1. -/
def uncTwoThirteen₁LowRanks : Fin 4 → Finset (Fin 2) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwoThirteen₁LowRanks`. -/
noncomputable def uncTwoThirteen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(2,13)`, certificate 1. -/
def uncTwoThirteen₁Ranks : Fin 4 → Finset (Fin 13) :=
  ![{2, 3, 5, 6, 8, 9, 11, 12}, ∅, {0, 1}, {4, 7, 10}]

/-- The prefix densities of `Gap212.uncTwoThirteen₁Ranks`. -/
noncomputable def uncTwoThirteen₁Dens : Fin 4 → ℝ := ![8 / 13, 0, 1, 3 / 11]

/-- **Cell `(2,13)`, certificate 1.**

Block bounds `1897 / 6500`, `0`, `179 / 5000`, `2751 / 55000`; no cut.
Valid on `4 / 625 < ω₀` and on
`10551 / 32500 + 8ω₀ + ϵ ≤ γ ≤ 1 / 2 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3806462 + ϵ, 0.4860000 - ϵ]`. -/
theorem admitsPartition₄_cellTwoThirteen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 10551 / 32500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1 / 2 - 2 * ω₀ - slack)
    {y : Fin (2 + 13) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (1081 / 5000) 2 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    uncTwoThirteen₁LowRanks uncTwoThirteen₁Ranks ?_ ?_ ?_ ?_
    uncTwoThirteen₁LowDens uncTwoThirteen₁Dens ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · decide
  · decide
  · decide
  · intro k; fin_cases k <;> norm_num [uncTwoThirteen₁LowDens]
  · intro k; fin_cases k <;> norm_num [uncTwoThirteen₁Dens]
  · exact prefixDensity_univ
  · intro k; fin_cases k
    · simpa [uncTwoThirteen₁Ranks, uncTwoThirteen₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoThirteen₁Ranks 0) 8 13 (by norm_num) (by decide)
    · simp [uncTwoThirteen₁Ranks, uncTwoThirteen₁Dens]
    · simpa [uncTwoThirteen₁Ranks, uncTwoThirteen₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoThirteen₁Ranks 2) 1 1 (by norm_num) (by decide)
    · simpa [uncTwoThirteen₁Ranks, uncTwoThirteen₁Dens] using
        prefixDensity_of_nat (𝕜 := ℝ) (uncTwoThirteen₁Ranks 3) 3 11 (by norm_num) (by decide)
  · intro k; fin_cases k <;>
      · simp [capD, hδ, uncTwoThirteen₁LowRanks, uncTwoThirteen₁Ranks,
          uncTwoThirteen₁LowDens, uncTwoThirteen₁Dens]
        all_goals linarith

/-- **Cell `(2,13)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,2}, B_{1,13}, 2, 13, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellTwoThirteen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 13) → ℝ}
    (hy : y ∈ Xi (397 / 2500 : ℝ) (1081 / 5000) 2 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellTwoThirteen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(2,13)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 2 = gap212Cap 2 = 397 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellTwoThirteen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (2 + 13) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 2) (gap212Params.B j' 13) 2 13
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTwoThirteen_band hωlo hωhi hγlo hγhi (gap212Cap_two ▸ hy)

/-- The hypotheses of the band theorems above are satisfiable: the chamber point `ω₀ = 7/1000`,
`γ = 2/5` and the constant profile `δ = 41/2500` meet all of them. -/
theorem cellsUncut1_hypotheses_satisfiable :
    (4 / 625 < (7 / 1000 : ℝ) ∧ (2 / 5 - slack : ℝ) ≤ 2 / 5 ∧
        (2 / 5 : ℝ) ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (777 / 5000 : ℝ) (777 / 5000) 1 1 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (777 / 5000 : ℝ) (397 / 2500) 1 2 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (777 / 5000 : ℝ) (917 / 5000) 1 4 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (777 / 5000 : ℝ) (953 / 5000) 1 5 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (777 / 5000 : ℝ) (983 / 5000) 1 6 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (777 / 5000 : ℝ) (127 / 625) 1 7 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (777 / 5000 : ℝ) (521 / 2500) 1 8 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (777 / 5000 : ℝ) (1063 / 5000) 1 9 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (777 / 5000 : ℝ) (1081 / 5000) 1 10 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (777 / 5000 : ℝ) (1081 / 5000) 1 11 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (777 / 5000 : ℝ) (1081 / 5000) 1 12 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (777 / 5000 : ℝ) (1081 / 5000) 1 13 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (397 / 2500 : ℝ) (397 / 2500) 2 2 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (397 / 2500 : ℝ) (917 / 5000) 2 4 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (397 / 2500 : ℝ) (953 / 5000) 2 5 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (397 / 2500 : ℝ) (983 / 5000) 2 6 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (397 / 2500 : ℝ) (127 / 625) 2 7 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (397 / 2500 : ℝ) (521 / 2500) 2 8 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (397 / 2500 : ℝ) (1063 / 5000) 2 9 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (397 / 2500 : ℝ) (1081 / 5000) 2 10 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (397 / 2500 : ℝ) (1081 / 5000) 2 11 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (397 / 2500 : ℝ) (1081 / 5000) 2 12 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (397 / 2500 : ℝ) (1081 / 5000) 2 13 (41 / 2500) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine ⟨⟨by norm_num, by rw [hsv]; norm_num, by rw [hδ, hsv]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 1 1]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 1 1]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 1 2]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 1 2]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 1 4]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 1 4]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 1 5]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 1 5]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 1 6]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 1 6]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 1 7]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 1 7]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 1 8]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 1 8]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 1 9]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 1 9]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 1 10]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 1 10]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 1 11]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 1 11]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 1 12]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 1 12]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 1 13]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 1 13]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 2 2]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 2 2]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 2 4]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 2 4]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 2 5]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 2 5]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 2 6]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 2 6]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 2 7]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 2 7]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 2 8]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 2 8]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 2 9]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 2 9]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 2 10]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 2 10]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 2 11]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 2 11]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 2 12]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 2 12]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 2 13]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 2 13]; norm_num⟩⟩

end Gap212
