/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCell

/-!
# The uncut rank certificates, part 2: the cells with three, four or five ranks on the low side

`Gap212.Packing.admitsPartition₄_of_rank_certificate` bounds each of the four bins by
`#T_k·δ + r_k·(B₁ - m₁δ) + #U_k·δ + s_k·(B₂ - m₂δ)`, with `r_k` and `s_k` the prefix densities of
the two rank sets the bin holds. No cut, no threshold, no hypothesis on the profile beyond `Ξ`: this
is the *uncut* reading, and it closes 62 of the 91 cells `1 ≤ m ≤ m' ≤ 13` on the whole band
`ω₀ ∈ (4/625, 7/1000]` and the whole chamber `γ`-range.

This file carries 17 of them, the cells with three, four or five ranks on the low side:

    (3,6)  (3,8)  (3,9)  (3,10)  (3,11)  (3,12)  (3,13)  (4,9)
    (4,10)  (4,11)  (4,12)  (4,13)  (5,9)  (5,10)  (5,11)  (5,12)
    (5,13)

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

/-- `Gap212.Packing.admitsPartition₄_of_rank_certificate` with the whole first group in bin 0,
and the second group's densities given as ratios `p k / q k` of naturals, so that every
combinatorial hypothesis is closed by `decide`. -/
private theorem admitsPartition₄_of_uncut {m₁ m₂ : ℕ} {B₁ B₂ δ : ℝ}
    {y : Fin (m₁ + m₂) → ℝ} (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) (hδ : 0 ≤ δ)
    (T : Fin 4 → Finset (Fin m₁)) (U : Fin 4 → Finset (Fin m₂)) (hT : T = ![univ, ∅, ∅, ∅])
    (hUcover : ∀ j, ∃ k, j ∈ U k) (hUdisj : ∀ k l, k ≠ l → U k ∩ U l = ∅)
    (r s : Fin 4 → ℝ) (hr : r = ![1, 0, 0, 0]) (p q : Fin 4 → ℕ) (hq : ∀ k, 0 < q k)
    (hs : ∀ k, s k = p k / q k)
    (hU : ∀ k, ∀ j, j ≤ m₂ → q k * ((U k).filter (fun i ↦ i.val < j)).card ≤ p k * j)
    (c : Fin 4 → ℝ)
    (hcap : ∀ k, ((((T k).card : ℕ) : ℝ) * δ + r k * (B₁ - (m₁ : ℝ) * δ))
        + ((((U k).card : ℕ) : ℝ) * δ + s k * (B₂ - (m₂ : ℝ) * δ)) ≤ c k) :
    AdmitsPartition₄ y (c 0) (c 1) (c 2) (c 3) := by
  subst hT hr
  refine admitsPartition₄_of_rank_certificate hy hδ _ U (fun _ ↦ ⟨0, by simp⟩) ?_ hUcover
    (fun k l hkl ↦ disjoint_iff_inter_eq_empty.2 (hUdisj k l hkl)) _ s
    (fun k ↦ by fin_cases k <;> simp) (fun k ↦ by rw [hs]; positivity) ?_
    (fun k ↦ by rw [hs]; exact prefixDensity_of_nat _ _ _ (hq k) (hU k)) c hcap
  · intro k l hkl; fin_cases k <;> fin_cases l <;> simp_all
  · intro k j; fin_cases k
    · simpa using (Nat.cast_le (α := ℝ)).2 ((card_le_card_of_injOn (t := range j) Fin.val
        (fun i hi ↦ mem_range.2 (mem_filter.1 hi).2) Fin.val_injective.injOn).trans_eq
        (card_range j))
    all_goals simp

private theorem gap212Cap_three : gap212Cap 3 = (7 / 40 : ℝ) := by norm_num [gap212Cap]

private theorem gap212Cap_eight : gap212Cap 8 = (521 / 2500 : ℝ) := by norm_num [gap212Cap]

/-! ## Cell `(3,6)` -/

/-- The first group's rank sets for cell `(3,6)`, certificate 1. -/
def uncThreeSix₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncThreeSix₁LowRanks`. -/
noncomputable def uncThreeSix₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,6)`, certificate 1. -/
def uncThreeSix₁Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1}, {2, 5}, {4}, {3}]

/-- The prefix densities of `Gap212.uncThreeSix₁Ranks`. -/
noncomputable def uncThreeSix₁Dens : Fin 4 → ℝ := ![1, 1 / 3, 1 / 5, 1 / 4]

/-- The first group's rank sets for cell `(3,6)`, certificate 2. -/
def uncThreeSix₂LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncThreeSix₂LowRanks`. -/
noncomputable def uncThreeSix₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,6)`, certificate 2. -/
def uncThreeSix₂Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2}, {5}, {4}, {3}]

/-- The prefix densities of `Gap212.uncThreeSix₂Ranks`. -/
noncomputable def uncThreeSix₂Dens : Fin 4 → ℝ := ![1, 1 / 6, 1 / 5, 1 / 4]

/-- **Cell `(3,6)`, certificate 1.**

Block bounds `153 / 500`, `983 / 15000`, `901 / 25000`, `819 / 20000`; no cut.
Valid on `4 / 625 < ω₀` and on
`847 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 6517 / 15000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3948000 + ϵ, 0.4204667 - ϵ]`. -/
theorem admitsPartition₄_cellThreeSix_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 847 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 6517 / 15000 - 2 * ω₀ - slack)
    {y : Fin (3 + 6) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (983 / 5000) 3 6 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncThreeSix₁LowRanks uncThreeSix₁Ranks rfl
    (by decide) (by decide) uncThreeSix₁LowDens uncThreeSix₁Dens rfl ![1, 1, 1, 1] ![1, 3, 5, 4]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncThreeSix₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncThreeSix₁LowRanks, uncThreeSix₁Ranks, uncThreeSix₁LowDens,
    uncThreeSix₁Dens] <;> linarith

/-- **Cell `(3,6)`, certificate 2.**

Block bounds `403 / 1250`, `983 / 30000`, `901 / 25000`, `819 / 20000`; no cut.
Valid on `4 / 625 < ω₀` and on
`222 / 625 + 8ω₀ + ϵ ≤ γ ≤ 14017 / 30000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4112000 + ϵ, 0.4532333 - ϵ]`. -/
theorem admitsPartition₄_cellThreeSix_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 222 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 14017 / 30000 - 2 * ω₀ - slack)
    {y : Fin (3 + 6) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (983 / 5000) 3 6 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncThreeSix₂LowRanks uncThreeSix₂Ranks rfl
    (by decide) (by decide) uncThreeSix₂LowDens uncThreeSix₂Dens rfl ![1, 1, 1, 1] ![1, 6, 5, 4]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncThreeSix₂Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncThreeSix₂LowRanks, uncThreeSix₂Ranks, uncThreeSix₂LowDens,
    uncThreeSix₂Dens] <;> linarith

/-- **Cell `(3,6)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,3}, B_{1,6}, 3, 6, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 2 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellThreeSix_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 6) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (983 / 5000) 3 6 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (6517 / 15000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellThreeSix_unc₁ hωlo (by linarith) h1 hy
  · exact admitsPartition₄_cellThreeSix_unc₂ hωlo (by linarith) (by linarith) hy

/-- **Cell `(3,6)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 3 = gap212Cap 3 = 7 / 40` at every stratum `j`. -/
theorem admitsPartition₄_cellThreeSix_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 6) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 3) (gap212Params.B j' 6) 3 6
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellThreeSix_band hωlo hωhi hγlo hγhi (gap212Cap_three ▸ hy)

/-! ## Cell `(3,8)` -/

/-- The first group's rank sets for cell `(3,8)`, certificate 1. -/
def uncThreeEight₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncThreeEight₁LowRanks`. -/
noncomputable def uncThreeEight₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,8)`, certificate 1. -/
def uncThreeEight₁Ranks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1, 2}, {3, 5, 7}, {6}, {4}]

/-- The prefix densities of `Gap212.uncThreeEight₁Ranks`. -/
noncomputable def uncThreeEight₁Dens : Fin 4 → ℝ := ![1, 3 / 8, 1 / 7, 1 / 5]

/-- The first group's rank sets for cell `(3,8)`, certificate 2. -/
def uncThreeEight₂LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncThreeEight₂LowRanks`. -/
noncomputable def uncThreeEight₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,8)`, certificate 2. -/
def uncThreeEight₂Ranks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1, 2, 3}, {4, 7}, {6}, {5}]

/-- The prefix densities of `Gap212.uncThreeEight₂Ranks`. -/
noncomputable def uncThreeEight₂Dens : Fin 4 → ℝ := ![1, 1 / 4, 1 / 7, 1 / 6]

/-- **Cell `(3,8)`, certificate 1.**

Block bounds `1507 / 5000`, `1563 / 20000`, `24 / 875`, `199 / 6250`; no cut.
Valid on `4 / 625 < ω₀` and on
`1671 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 8437 / 20000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3902000 + ϵ, 0.4078500 - ϵ]`. -/
theorem admitsPartition₄_cellThreeEight_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1671 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 8437 / 20000 - 2 * ω₀ - slack)
    {y : Fin (3 + 8) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (521 / 2500) 3 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncThreeEight₁LowRanks uncThreeEight₁Ranks rfl
    (by decide) (by decide) uncThreeEight₁LowDens uncThreeEight₁Dens rfl ![1, 3, 1, 1] ![1, 8, 7, 5]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncThreeEight₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncThreeEight₁LowRanks, uncThreeEight₁Ranks,
    uncThreeEight₁LowDens, uncThreeEight₁Dens] <;> linarith

/-- **Cell `(3,8)`, certificate 2.**

Block bounds `1589 / 5000`, `521 / 10000`, `24 / 875`, `439 / 15000`; no cut.
Valid on `4 / 625 < ω₀` and on
`1753 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 4479 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4066000 + ϵ, 0.4339000 - ϵ]`. -/
theorem admitsPartition₄_cellThreeEight_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1753 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4479 / 10000 - 2 * ω₀ - slack)
    {y : Fin (3 + 8) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (521 / 2500) 3 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncThreeEight₂LowRanks uncThreeEight₂Ranks rfl
    (by decide) (by decide) uncThreeEight₂LowDens uncThreeEight₂Dens rfl ![1, 1, 1, 1] ![1, 4, 7, 6]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncThreeEight₂Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncThreeEight₂LowRanks, uncThreeEight₂Ranks,
    uncThreeEight₂LowDens, uncThreeEight₂Dens] <;> linarith

/-- **Cell `(3,8)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,3}, B_{1,8}, 3, 8, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 2 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellThreeEight_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 8) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (521 / 2500) 3 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (8437 / 20000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellThreeEight_unc₁ hωlo (by linarith) h1 hy
  · exact admitsPartition₄_cellThreeEight_unc₂ hωlo (by linarith) (by linarith) hy

/-- **Cell `(3,8)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 3 = gap212Cap 3 = 7 / 40` at every stratum `j`. -/
theorem admitsPartition₄_cellThreeEight_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 8) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 3) (gap212Params.B j' 8) 3 8
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellThreeEight_band hωlo hωhi hγlo hγhi
    (gap212Cap_three ▸ gap212Cap_eight ▸ hy)

/-! ## Cell `(3,9)` -/

/-- The first group's rank sets for cell `(3,9)`, certificate 1. -/
def uncThreeNine₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncThreeNine₁LowRanks`. -/
noncomputable def uncThreeNine₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,9)`, certificate 1. -/
def uncThreeNine₁Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2, 3}, {5, 8}, {6}, {4, 7}]

/-- The prefix densities of `Gap212.uncThreeNine₁Ranks`. -/
noncomputable def uncThreeNine₁Dens : Fin 4 → ℝ := ![1, 2 / 9, 1 / 7, 1 / 4]

/-- **Cell `(3,9)`, certificate 1.**

Block bounds `191 / 625`, `1063 / 22500`, `899 / 35000`, `981 / 20000`; no cut.
Valid on `4 / 625 < ω₀` and on
`423 / 1250 + 8ω₀ + ϵ ≤ γ ≤ 10187 / 22500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3944000 + ϵ, 0.4387556 - ϵ]`. -/
theorem admitsPartition₄_cellThreeNine_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 423 / 1250 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 10187 / 22500 - 2 * ω₀ - slack)
    {y : Fin (3 + 9) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (1063 / 5000) 3 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncThreeNine₁LowRanks uncThreeNine₁Ranks rfl
    (by decide) (by decide) uncThreeNine₁LowDens uncThreeNine₁Dens rfl ![1, 2, 1, 1] ![1, 9, 7, 4]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncThreeNine₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncThreeNine₁LowRanks, uncThreeNine₁Ranks, uncThreeNine₁LowDens,
    uncThreeNine₁Dens] <;> linarith

/-- **Cell `(3,9)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,3}, B_{1,9}, 3, 9, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellThreeNine_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 9) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (1063 / 5000) 3 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellThreeNine_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(3,9)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 3 = gap212Cap 3 = 7 / 40` at every stratum `j`. -/
theorem admitsPartition₄_cellThreeNine_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 9) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 3) (gap212Params.B j' 9) 3 9
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellThreeNine_band hωlo hωhi hγlo hγhi (gap212Cap_three ▸ hy)

/-! ## Cell `(3,10)` -/

/-- The first group's rank sets for cell `(3,10)`, certificate 1. -/
def uncThreeTen₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncThreeTen₁LowRanks`. -/
noncomputable def uncThreeTen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,10)`, certificate 1. -/
def uncThreeTen₁Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3, 4}, {6, 9}, {7}, {5, 8}]

/-- The prefix densities of `Gap212.uncThreeTen₁Ranks`. -/
noncomputable def uncThreeTen₁Dens : Fin 4 → ℝ := ![1, 1 / 5, 1 / 8, 2 / 9]

/-- **Cell `(3,10)`, certificate 1.**

Block bounds `773 / 2500`, `1081 / 25000`, `917 / 40000`, `111 / 2500`; no cut.
Valid on `4 / 625 < ω₀` and on
`171 / 500 + 8ω₀ + ϵ ≤ γ ≤ 11419 / 25000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3980000 + ϵ, 0.4427600 - ϵ]`. -/
theorem admitsPartition₄_cellThreeTen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 171 / 500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 11419 / 25000 - 2 * ω₀ - slack)
    {y : Fin (3 + 10) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (1081 / 5000) 3 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncThreeTen₁LowRanks uncThreeTen₁Ranks rfl
    (by decide) (by decide) uncThreeTen₁LowDens uncThreeTen₁Dens rfl ![1, 1, 1, 2] ![1, 5, 8, 9]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncThreeTen₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncThreeTen₁LowRanks, uncThreeTen₁Ranks, uncThreeTen₁LowDens,
    uncThreeTen₁Dens] <;> linarith

/-- **Cell `(3,10)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,3}, B_{1,10}, 3, 10, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellThreeTen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 10) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (1081 / 5000) 3 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellThreeTen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(3,10)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 3 = gap212Cap 3 = 7 / 40` at every stratum `j`. -/
theorem admitsPartition₄_cellThreeTen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 10) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 3) (gap212Params.B j' 10) 3 10
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellThreeTen_band hωlo hωhi hγlo hγhi (gap212Cap_three ▸ hy)

/-! ## Cell `(3,11)` -/

/-- The first group's rank sets for cell `(3,11)`, certificate 1. -/
def uncThreeEleven₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncThreeEleven₁LowRanks`. -/
noncomputable def uncThreeEleven₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,11)`, certificate 1. -/
def uncThreeEleven₁Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3, 4, 5}, {10}, {7, 9}, {6, 8}]

/-- The prefix densities of `Gap212.uncThreeEleven₁Ranks`. -/
noncomputable def uncThreeEleven₁Dens : Fin 4 → ℝ := ![1, 1 / 11, 1 / 5, 2 / 9]

/-- **Cell `(3,11)`, certificate 1.**

Block bounds `773 / 2500`, `1081 / 55000`, `999 / 25000`, `917 / 22500`; no cut.
Valid on `4 / 625 < ω₀` and on
`171 / 500 + 8ω₀ + ϵ ≤ γ ≤ 26419 / 55000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3980000 + ϵ, 0.4663455 - ϵ]`. -/
theorem admitsPartition₄_cellThreeEleven_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 171 / 500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 26419 / 55000 - 2 * ω₀ - slack)
    {y : Fin (3 + 11) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (1081 / 5000) 3 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncThreeEleven₁LowRanks uncThreeEleven₁Ranks rfl
    (by decide) (by decide) uncThreeEleven₁LowDens uncThreeEleven₁Dens rfl ![1, 1, 1, 2]
    ![1, 11, 5, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncThreeEleven₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncThreeEleven₁LowRanks, uncThreeEleven₁Ranks,
    uncThreeEleven₁LowDens, uncThreeEleven₁Dens] <;> linarith

/-- **Cell `(3,11)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,3}, B_{1,11}, 3, 11, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellThreeEleven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 11) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (1081 / 5000) 3 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellThreeEleven_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(3,11)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 3 = gap212Cap 3 = 7 / 40` at every stratum `j`. -/
theorem admitsPartition₄_cellThreeEleven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 11) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 3) (gap212Params.B j' 11) 3 11
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellThreeEleven_band hωlo hωhi hγlo hγhi (gap212Cap_three ▸ hy)

/-! ## Cell `(3,12)` -/

/-- The first group's rank sets for cell `(3,12)`, certificate 1. -/
def uncThreeTwelve₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncThreeTwelve₁LowRanks`. -/
noncomputable def uncThreeTwelve₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,12)`, certificate 1. -/
def uncThreeTwelve₁Ranks : Fin 4 → Finset (Fin 12) :=
  ![{0, 1, 2, 3, 4, 5, 6}, {11}, {8, 10}, {7, 9}]

/-- The prefix densities of `Gap212.uncThreeTwelve₁Ranks`. -/
noncomputable def uncThreeTwelve₁Dens : Fin 4 → ℝ := ![1, 1 / 12, 2 / 11, 1 / 5]

/-- **Cell `(3,12)`, certificate 1.**

Block bounds `773 / 2500`, `1081 / 60000`, `999 / 27500`, `917 / 25000`; no cut.
Valid on `4 / 625 < ω₀` and on
`171 / 500 + 8ω₀ + ϵ ≤ γ ≤ 28919 / 60000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3980000 + ϵ, 0.4679833 - ϵ]`. -/
theorem admitsPartition₄_cellThreeTwelve_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 171 / 500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 28919 / 60000 - 2 * ω₀ - slack)
    {y : Fin (3 + 12) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (1081 / 5000) 3 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncThreeTwelve₁LowRanks uncThreeTwelve₁Ranks rfl
    (by decide) (by decide) uncThreeTwelve₁LowDens uncThreeTwelve₁Dens rfl ![1, 1, 2, 1]
    ![1, 12, 11, 5] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncThreeTwelve₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncThreeTwelve₁LowRanks, uncThreeTwelve₁Ranks,
    uncThreeTwelve₁LowDens, uncThreeTwelve₁Dens] <;> linarith

/-- **Cell `(3,12)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,3}, B_{1,12}, 3, 12, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellThreeTwelve_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 12) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (1081 / 5000) 3 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellThreeTwelve_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(3,12)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 3 = gap212Cap 3 = 7 / 40` at every stratum `j`. -/
theorem admitsPartition₄_cellThreeTwelve_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 12) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 3) (gap212Params.B j' 12) 3 12
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellThreeTwelve_band hωlo hωhi hγlo hγhi (gap212Cap_three ▸ hy)

/-! ## Cell `(3,13)` -/

/-- The first group's rank sets for cell `(3,13)`, certificate 1. -/
def uncThreeThirteen₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncThreeThirteen₁LowRanks`. -/
noncomputable def uncThreeThirteen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,13)`, certificate 1. -/
def uncThreeThirteen₁Ranks : Fin 4 → Finset (Fin 13) :=
  ![{2, 3, 5, 6, 8, 9, 11, 12}, ∅, {0, 1}, {4, 7, 10}]

/-- The prefix densities of `Gap212.uncThreeThirteen₁Ranks`. -/
noncomputable def uncThreeThirteen₁Dens : Fin 4 → ℝ := ![8 / 13, 0, 1, 3 / 11]

/-- **Cell `(3,13)`, certificate 1.**

Block bounds `20023 / 65000`, `0`, `179 / 5000`, `2751 / 55000`; no cut.
Valid on `4 / 625 < ω₀` and on
`4431 / 13000 + 8ω₀ + ϵ ≤ γ ≤ 1 / 2 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3968462 + ϵ, 0.4860000 - ϵ]`. -/
theorem admitsPartition₄_cellThreeThirteen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 4431 / 13000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1 / 2 - 2 * ω₀ - slack)
    {y : Fin (3 + 13) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (1081 / 5000) 3 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncThreeThirteen₁LowRanks uncThreeThirteen₁Ranks
    rfl (by decide) (by decide) uncThreeThirteen₁LowDens uncThreeThirteen₁Dens rfl ![8, 0, 1, 3]
    ![13, 1, 1, 11] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncThreeThirteen₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncThreeThirteen₁LowRanks, uncThreeThirteen₁Ranks,
    uncThreeThirteen₁LowDens, uncThreeThirteen₁Dens] <;> linarith

/-- **Cell `(3,13)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,3}, B_{1,13}, 3, 13, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellThreeThirteen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 13) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (1081 / 5000) 3 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellThreeThirteen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(3,13)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 3 = gap212Cap 3 = 7 / 40` at every stratum `j`. -/
theorem admitsPartition₄_cellThreeThirteen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 13) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 3) (gap212Params.B j' 13) 3 13
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellThreeThirteen_band hωlo hωhi hγlo hγhi (gap212Cap_three ▸ hy)

/-! ## Cell `(4,9)` -/

/-- The first group's rank sets for cell `(4,9)`, certificate 1. -/
def uncFourNine₁LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncFourNine₁LowRanks`. -/
noncomputable def uncFourNine₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,9)`, certificate 1. -/
def uncFourNine₁Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2}, {3, 5, 8}, {6}, {4, 7}]

/-- The prefix densities of `Gap212.uncFourNine₁Ranks`. -/
noncomputable def uncFourNine₁Dens : Fin 4 → ℝ := ![1, 1 / 3, 1 / 7, 1 / 4]

/-- The first group's rank sets for cell `(4,9)`, certificate 2. -/
def uncFourNine₂LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncFourNine₂LowRanks`. -/
noncomputable def uncFourNine₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,9)`, certificate 2. -/
def uncFourNine₂Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2, 3}, {5, 8}, {6}, {4, 7}]

/-- The prefix densities of `Gap212.uncFourNine₂Ranks`. -/
noncomputable def uncFourNine₂Dens : Fin 4 → ℝ := ![1, 2 / 9, 1 / 7, 1 / 4]

/-- **Cell `(4,9)`, certificate 1.**

Block bounds `186 / 625`, `1063 / 15000`, `899 / 35000`, `981 / 20000`; no cut.
Valid on `4 / 625 < ω₀` and on
`413 / 1250 + 8ω₀ + ϵ ≤ γ ≤ 6437 / 15000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3864000 + ϵ, 0.4151333 - ϵ]`. -/
theorem admitsPartition₄_cellFourNine_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 413 / 1250 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 6437 / 15000 - 2 * ω₀ - slack)
    {y : Fin (4 + 9) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (1063 / 5000) 4 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncFourNine₁LowRanks uncFourNine₁Ranks rfl
    (by decide) (by decide) uncFourNine₁LowDens uncFourNine₁Dens rfl ![1, 1, 1, 1] ![1, 3, 7, 4]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncFourNine₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncFourNine₁LowRanks, uncFourNine₁Ranks, uncFourNine₁LowDens,
    uncFourNine₁Dens] <;> linarith

/-- **Cell `(4,9)`, certificate 2.**

Block bounds `157 / 500`, `1063 / 22500`, `899 / 35000`, `981 / 20000`; no cut.
Valid on `4 / 625 < ω₀` and on
`867 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 10187 / 22500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4028000 + ϵ, 0.4387556 - ϵ]`. -/
theorem admitsPartition₄_cellFourNine_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 867 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 10187 / 22500 - 2 * ω₀ - slack)
    {y : Fin (4 + 9) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (1063 / 5000) 4 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncFourNine₂LowRanks uncFourNine₂Ranks rfl
    (by decide) (by decide) uncFourNine₂LowDens uncFourNine₂Dens rfl ![1, 2, 1, 1] ![1, 9, 7, 4]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncFourNine₂Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncFourNine₂LowRanks, uncFourNine₂Ranks, uncFourNine₂LowDens,
    uncFourNine₂Dens] <;> linarith

/-- **Cell `(4,9)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,4}, B_{1,9}, 4, 9, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 2 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellFourNine_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 9) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (1063 / 5000) 4 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (6437 / 15000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellFourNine_unc₁ hωlo (by linarith) h1 hy
  · exact admitsPartition₄_cellFourNine_unc₂ hωlo (by linarith) (by linarith) hy

/-- **Cell `(4,9)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 4 = gap212Cap 4 = 917 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFourNine_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 9) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 4) (gap212Params.B j' 9) 4 9
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellFourNine_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(4,10)` -/

/-- The first group's rank sets for cell `(4,10)`, certificate 1. -/
def uncFourTen₁LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncFourTen₁LowRanks`. -/
noncomputable def uncFourTen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,10)`, certificate 1. -/
def uncFourTen₁Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3}, {4, 6, 9}, {7}, {5, 8}]

/-- The prefix densities of `Gap212.uncFourTen₁Ranks`. -/
noncomputable def uncFourTen₁Dens : Fin 4 → ℝ := ![1, 3 / 10, 1 / 8, 2 / 9]

/-- The first group's rank sets for cell `(4,10)`, certificate 2. -/
def uncFourTen₂LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncFourTen₂LowRanks`. -/
noncomputable def uncFourTen₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,10)`, certificate 2. -/
def uncFourTen₂Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3, 4}, {6, 9}, {7}, {5, 8}]

/-- The prefix densities of `Gap212.uncFourTen₂Ranks`. -/
noncomputable def uncFourTen₂Dens : Fin 4 → ℝ := ![1, 1 / 5, 1 / 8, 2 / 9]

/-- **Cell `(4,10)`, certificate 1.**

Block bounds `753 / 2500`, `3243 / 50000`, `917 / 40000`, `111 / 2500`; no cut.
Valid on `4 / 625 < ω₀` and on
`167 / 500 + 8ω₀ + ϵ ≤ γ ≤ 21757 / 50000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3900000 + ϵ, 0.4211400 - ϵ]`. -/
theorem admitsPartition₄_cellFourTen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 167 / 500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 21757 / 50000 - 2 * ω₀ - slack)
    {y : Fin (4 + 10) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (1081 / 5000) 4 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncFourTen₁LowRanks uncFourTen₁Ranks rfl
    (by decide) (by decide) uncFourTen₁LowDens uncFourTen₁Dens rfl ![1, 3, 1, 2] ![1, 10, 8, 9]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncFourTen₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncFourTen₁LowRanks, uncFourTen₁Ranks, uncFourTen₁LowDens,
    uncFourTen₁Dens] <;> linarith

/-- **Cell `(4,10)`, certificate 2.**

Block bounds `397 / 1250`, `1081 / 25000`, `917 / 40000`, `111 / 2500`; no cut.
Valid on `4 / 625 < ω₀` and on
`219 / 625 + 8ω₀ + ϵ ≤ γ ≤ 11419 / 25000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4064000 + ϵ, 0.4427600 - ϵ]`. -/
theorem admitsPartition₄_cellFourTen_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 219 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 11419 / 25000 - 2 * ω₀ - slack)
    {y : Fin (4 + 10) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (1081 / 5000) 4 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncFourTen₂LowRanks uncFourTen₂Ranks rfl
    (by decide) (by decide) uncFourTen₂LowDens uncFourTen₂Dens rfl ![1, 1, 1, 2] ![1, 5, 8, 9]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncFourTen₂Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncFourTen₂LowRanks, uncFourTen₂Ranks, uncFourTen₂LowDens,
    uncFourTen₂Dens] <;> linarith

/-- **Cell `(4,10)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,4}, B_{1,10}, 4, 10, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 2 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellFourTen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 10) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (1081 / 5000) 4 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (21757 / 50000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellFourTen_unc₁ hωlo (by linarith) h1 hy
  · exact admitsPartition₄_cellFourTen_unc₂ hωlo (by linarith) (by linarith) hy

/-- **Cell `(4,10)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 4 = gap212Cap 4 = 917 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFourTen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 10) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 4) (gap212Params.B j' 10) 4 10
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellFourTen_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(4,11)` -/

/-- The first group's rank sets for cell `(4,11)`, certificate 1. -/
def uncFourEleven₁LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncFourEleven₁LowRanks`. -/
noncomputable def uncFourEleven₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,11)`, certificate 1. -/
def uncFourEleven₁Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3, 4}, {7, 10}, {6, 9}, {5, 8}]

/-- The prefix densities of `Gap212.uncFourEleven₁Ranks`. -/
noncomputable def uncFourEleven₁Dens : Fin 4 → ℝ := ![1, 2 / 11, 1 / 5, 2 / 9]

/-- **Cell `(4,11)`, certificate 1.**

Block bounds `753 / 2500`, `1081 / 27500`, `999 / 25000`, `917 / 22500`; no cut.
Valid on `4 / 625 < ω₀` and on
`167 / 500 + 8ω₀ + ϵ ≤ γ ≤ 12669 / 27500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3900000 + ϵ, 0.4466909 - ϵ]`. -/
theorem admitsPartition₄_cellFourEleven_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 167 / 500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 12669 / 27500 - 2 * ω₀ - slack)
    {y : Fin (4 + 11) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (1081 / 5000) 4 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncFourEleven₁LowRanks uncFourEleven₁Ranks rfl
    (by decide) (by decide) uncFourEleven₁LowDens uncFourEleven₁Dens rfl ![1, 2, 1, 2]
    ![1, 11, 5, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncFourEleven₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncFourEleven₁LowRanks, uncFourEleven₁Ranks,
    uncFourEleven₁LowDens, uncFourEleven₁Dens] <;> linarith

/-- **Cell `(4,11)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,4}, B_{1,11}, 4, 11, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellFourEleven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 11) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (1081 / 5000) 4 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellFourEleven_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(4,11)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 4 = gap212Cap 4 = 917 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFourEleven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 11) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 4) (gap212Params.B j' 11) 4 11
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellFourEleven_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(4,12)` -/

/-- The first group's rank sets for cell `(4,12)`, certificate 1. -/
def uncFourTwelve₁LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncFourTwelve₁LowRanks`. -/
noncomputable def uncFourTwelve₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,12)`, certificate 1. -/
def uncFourTwelve₁Ranks : Fin 4 → Finset (Fin 12) :=
  ![{1, 3, 5, 7, 8, 10, 11}, {0}, {4, 9}, {2, 6}]

/-- The prefix densities of `Gap212.uncFourTwelve₁Ranks`. -/
noncomputable def uncFourTwelve₁Dens : Fin 4 → ℝ := ![7 / 12, 1, 1 / 5, 1 / 3]

/-- **Cell `(4,12)`, certificate 1.**

Block bounds `18571 / 60000`, `179 / 5000`, `917 / 25000`, `589 / 15000`; no cut.
Valid on `4 / 625 < ω₀` and on
`20539 / 60000 + 8ω₀ + ϵ ≤ γ ≤ 2321 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3983167 + ϵ, 0.4502000 - ϵ]`. -/
theorem admitsPartition₄_cellFourTwelve_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 20539 / 60000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2321 / 5000 - 2 * ω₀ - slack)
    {y : Fin (4 + 12) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (1081 / 5000) 4 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncFourTwelve₁LowRanks uncFourTwelve₁Ranks rfl
    (by decide) (by decide) uncFourTwelve₁LowDens uncFourTwelve₁Dens rfl ![7, 1, 1, 1]
    ![12, 1, 5, 3] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncFourTwelve₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncFourTwelve₁LowRanks, uncFourTwelve₁Ranks,
    uncFourTwelve₁LowDens, uncFourTwelve₁Dens] <;> linarith

/-- **Cell `(4,12)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,4}, B_{1,12}, 4, 12, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellFourTwelve_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 12) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (1081 / 5000) 4 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellFourTwelve_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(4,12)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 4 = gap212Cap 4 = 917 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFourTwelve_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 12) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 4) (gap212Params.B j' 12) 4 12
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellFourTwelve_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(4,13)` -/

/-- The first group's rank sets for cell `(4,13)`, certificate 1. -/
def uncFourThirteen₁LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncFourThirteen₁LowRanks`. -/
noncomputable def uncFourThirteen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,13)`, certificate 1. -/
def uncFourThirteen₁Ranks : Fin 4 → Finset (Fin 13) :=
  ![{2, 3, 5, 7, 8, 10, 11}, {12}, {0, 1}, {4, 6, 9}]

/-- The prefix densities of `Gap212.uncFourThirteen₁Ranks`. -/
noncomputable def uncFourThirteen₁Dens : Fin 4 → ℝ := ![7 / 12, 1 / 13, 1, 3 / 10]

/-- **Cell `(4,13)`, certificate 1.**

Block bounds `5999 / 20000`, `1081 / 65000`, `179 / 5000`, `501 / 10000`; no cut.
Valid on `4 / 625 < ω₀` and on
`1331 / 4000 + 8ω₀ + ϵ ≤ γ ≤ 31419 / 65000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3887500 + ϵ, 0.4693692 - ϵ]`. -/
theorem admitsPartition₄_cellFourThirteen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1331 / 4000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 31419 / 65000 - 2 * ω₀ - slack)
    {y : Fin (4 + 13) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (1081 / 5000) 4 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncFourThirteen₁LowRanks uncFourThirteen₁Ranks
    rfl (by decide) (by decide) uncFourThirteen₁LowDens uncFourThirteen₁Dens rfl ![7, 1, 1, 3]
    ![12, 13, 1, 10] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncFourThirteen₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncFourThirteen₁LowRanks, uncFourThirteen₁Ranks,
    uncFourThirteen₁LowDens, uncFourThirteen₁Dens] <;> linarith

/-- **Cell `(4,13)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,4}, B_{1,13}, 4, 13, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellFourThirteen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 13) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (1081 / 5000) 4 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellFourThirteen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(4,13)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 4 = gap212Cap 4 = 917 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFourThirteen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 13) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 4) (gap212Params.B j' 13) 4 13
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellFourThirteen_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(5,9)` -/

/-- The first group's rank sets for cell `(5,9)`, certificate 1. -/
def uncFiveNine₁LowRanks : Fin 4 → Finset (Fin 5) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncFiveNine₁LowRanks`. -/
noncomputable def uncFiveNine₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(5,9)`, certificate 1. -/
def uncFiveNine₁Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2}, {3, 5, 8}, {6}, {4, 7}]

/-- The prefix densities of `Gap212.uncFiveNine₁Ranks`. -/
noncomputable def uncFiveNine₁Dens : Fin 4 → ℝ := ![1, 1 / 3, 1 / 7, 1 / 4]

/-- The first group's rank sets for cell `(5,9)`, certificate 2. -/
def uncFiveNine₂LowRanks : Fin 4 → Finset (Fin 5) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncFiveNine₂LowRanks`. -/
noncomputable def uncFiveNine₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(5,9)`, certificate 2. -/
def uncFiveNine₂Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2, 3}, {5, 8}, {6}, {4, 7}]

/-- The prefix densities of `Gap212.uncFiveNine₂Ranks`. -/
noncomputable def uncFiveNine₂Dens : Fin 4 → ℝ := ![1, 2 / 9, 1 / 7, 1 / 4]

/-- **Cell `(5,9)`, certificate 1.**

Block bounds `381 / 1250`, `1063 / 15000`, `899 / 35000`, `981 / 20000`; no cut.
Valid on `4 / 625 < ω₀` and on
`211 / 625 + 8ω₀ + ϵ ≤ γ ≤ 6437 / 15000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3936000 + ϵ, 0.4151333 - ϵ]`. -/
theorem admitsPartition₄_cellFiveNine_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 211 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 6437 / 15000 - 2 * ω₀ - slack)
    {y : Fin (5 + 9) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (1063 / 5000) 5 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncFiveNine₁LowRanks uncFiveNine₁Ranks rfl
    (by decide) (by decide) uncFiveNine₁LowDens uncFiveNine₁Dens rfl ![1, 1, 1, 1] ![1, 3, 7, 4]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncFiveNine₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncFiveNine₁LowRanks, uncFiveNine₁Ranks, uncFiveNine₁LowDens,
    uncFiveNine₁Dens] <;> linarith

/-- **Cell `(5,9)`, certificate 2.**

Block bounds `803 / 2500`, `1063 / 22500`, `899 / 35000`, `981 / 20000`; no cut.
Valid on `4 / 625 < ω₀` and on
`177 / 500 + 8ω₀ + ϵ ≤ γ ≤ 10187 / 22500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4100000 + ϵ, 0.4387556 - ϵ]`. -/
theorem admitsPartition₄_cellFiveNine_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 177 / 500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 10187 / 22500 - 2 * ω₀ - slack)
    {y : Fin (5 + 9) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (1063 / 5000) 5 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncFiveNine₂LowRanks uncFiveNine₂Ranks rfl
    (by decide) (by decide) uncFiveNine₂LowDens uncFiveNine₂Dens rfl ![1, 2, 1, 1] ![1, 9, 7, 4]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncFiveNine₂Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncFiveNine₂LowRanks, uncFiveNine₂Ranks, uncFiveNine₂LowDens,
    uncFiveNine₂Dens] <;> linarith

/-- **Cell `(5,9)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,5}, B_{1,9}, 5, 9, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 2 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellFiveNine_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 9) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (1063 / 5000) 5 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (6437 / 15000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellFiveNine_unc₁ hωlo (by linarith) h1 hy
  · exact admitsPartition₄_cellFiveNine_unc₂ hωlo (by linarith) (by linarith) hy

/-- **Cell `(5,9)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 5 = gap212Cap 5 = 953 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFiveNine_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 9) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 5) (gap212Params.B j' 9) 5 9
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellFiveNine_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(5,10)` -/

/-- The first group's rank sets for cell `(5,10)`, certificate 1. -/
def uncFiveTen₁LowRanks : Fin 4 → Finset (Fin 5) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncFiveTen₁LowRanks`. -/
noncomputable def uncFiveTen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(5,10)`, certificate 1. -/
def uncFiveTen₁Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3}, {4, 6, 9}, {7}, {5, 8}]

/-- The prefix densities of `Gap212.uncFiveTen₁Ranks`. -/
noncomputable def uncFiveTen₁Dens : Fin 4 → ℝ := ![1, 3 / 10, 1 / 8, 2 / 9]

/-- The first group's rank sets for cell `(5,10)`, certificate 2. -/
def uncFiveTen₂LowRanks : Fin 4 → Finset (Fin 5) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncFiveTen₂LowRanks`. -/
noncomputable def uncFiveTen₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(5,10)`, certificate 2. -/
def uncFiveTen₂Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3, 4}, {6, 9}, {7}, {5, 8}]

/-- The prefix densities of `Gap212.uncFiveTen₂Ranks`. -/
noncomputable def uncFiveTen₂Dens : Fin 4 → ℝ := ![1, 1 / 5, 1 / 8, 2 / 9]

/-- **Cell `(5,10)`, certificate 1.**

Block bounds `771 / 2500`, `3243 / 50000`, `917 / 40000`, `111 / 2500`; no cut.
Valid on `4 / 625 < ω₀` and on
`853 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 21757 / 50000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3972000 + ϵ, 0.4211400 - ϵ]`. -/
theorem admitsPartition₄_cellFiveTen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 853 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 21757 / 50000 - 2 * ω₀ - slack)
    {y : Fin (5 + 10) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (1081 / 5000) 5 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncFiveTen₁LowRanks uncFiveTen₁Ranks rfl
    (by decide) (by decide) uncFiveTen₁LowDens uncFiveTen₁Dens rfl ![1, 3, 1, 2] ![1, 10, 8, 9]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncFiveTen₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncFiveTen₁LowRanks, uncFiveTen₁Ranks, uncFiveTen₁LowDens,
    uncFiveTen₁Dens] <;> linarith

/-- **Cell `(5,10)`, certificate 2.**

Block bounds `203 / 625`, `1081 / 25000`, `917 / 40000`, `111 / 2500`; no cut.
Valid on `4 / 625 < ω₀` and on
`447 / 1250 + 8ω₀ + ϵ ≤ γ ≤ 11419 / 25000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4136000 + ϵ, 0.4427600 - ϵ]`. -/
theorem admitsPartition₄_cellFiveTen_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 447 / 1250 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 11419 / 25000 - 2 * ω₀ - slack)
    {y : Fin (5 + 10) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (1081 / 5000) 5 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncFiveTen₂LowRanks uncFiveTen₂Ranks rfl
    (by decide) (by decide) uncFiveTen₂LowDens uncFiveTen₂Dens rfl ![1, 1, 1, 2] ![1, 5, 8, 9]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncFiveTen₂Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncFiveTen₂LowRanks, uncFiveTen₂Ranks, uncFiveTen₂LowDens,
    uncFiveTen₂Dens] <;> linarith

/-- **Cell `(5,10)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,5}, B_{1,10}, 5, 10, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 2 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellFiveTen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 10) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (1081 / 5000) 5 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (21757 / 50000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellFiveTen_unc₁ hωlo (by linarith) h1 hy
  · exact admitsPartition₄_cellFiveTen_unc₂ hωlo (by linarith) (by linarith) hy

/-- **Cell `(5,10)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 5 = gap212Cap 5 = 953 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFiveTen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 10) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 5) (gap212Params.B j' 10) 5 10
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellFiveTen_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(5,11)` -/

/-- The first group's rank sets for cell `(5,11)`, certificate 1. -/
def uncFiveEleven₁LowRanks : Fin 4 → Finset (Fin 5) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncFiveEleven₁LowRanks`. -/
noncomputable def uncFiveEleven₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(5,11)`, certificate 1. -/
def uncFiveEleven₁Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3, 4}, {7, 10}, {6, 9}, {5, 8}]

/-- The prefix densities of `Gap212.uncFiveEleven₁Ranks`. -/
noncomputable def uncFiveEleven₁Dens : Fin 4 → ℝ := ![1, 2 / 11, 1 / 5, 2 / 9]

/-- **Cell `(5,11)`, certificate 1.**

Block bounds `771 / 2500`, `1081 / 27500`, `999 / 25000`, `917 / 22500`; no cut.
Valid on `4 / 625 < ω₀` and on
`853 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 12669 / 27500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3972000 + ϵ, 0.4466909 - ϵ]`. -/
theorem admitsPartition₄_cellFiveEleven_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 853 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 12669 / 27500 - 2 * ω₀ - slack)
    {y : Fin (5 + 11) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (1081 / 5000) 5 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncFiveEleven₁LowRanks uncFiveEleven₁Ranks rfl
    (by decide) (by decide) uncFiveEleven₁LowDens uncFiveEleven₁Dens rfl ![1, 2, 1, 2]
    ![1, 11, 5, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncFiveEleven₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncFiveEleven₁LowRanks, uncFiveEleven₁Ranks,
    uncFiveEleven₁LowDens, uncFiveEleven₁Dens] <;> linarith

/-- **Cell `(5,11)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,5}, B_{1,11}, 5, 11, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellFiveEleven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 11) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (1081 / 5000) 5 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellFiveEleven_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(5,11)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 5 = gap212Cap 5 = 953 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFiveEleven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 11) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 5) (gap212Params.B j' 11) 5 11
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellFiveEleven_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(5,12)` -/

/-- The first group's rank sets for cell `(5,12)`, certificate 1. -/
def uncFiveTwelve₁LowRanks : Fin 4 → Finset (Fin 5) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncFiveTwelve₁LowRanks`. -/
noncomputable def uncFiveTwelve₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(5,12)`, certificate 1. -/
def uncFiveTwelve₁Ranks : Fin 4 → Finset (Fin 12) :=
  ![{0, 1, 2, 3, 4, 5}, {8, 11}, {7, 10}, {6, 9}]

/-- The prefix densities of `Gap212.uncFiveTwelve₁Ranks`. -/
noncomputable def uncFiveTwelve₁Dens : Fin 4 → ℝ := ![1, 1 / 6, 2 / 11, 1 / 5]

/-- **Cell `(5,12)`, certificate 1.**

Block bounds `771 / 2500`, `1081 / 30000`, `999 / 27500`, `917 / 25000`; no cut.
Valid on `4 / 625 < ω₀` and on
`853 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 13919 / 30000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3972000 + ϵ, 0.4499667 - ϵ]`. -/
theorem admitsPartition₄_cellFiveTwelve_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 853 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 13919 / 30000 - 2 * ω₀ - slack)
    {y : Fin (5 + 12) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (1081 / 5000) 5 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncFiveTwelve₁LowRanks uncFiveTwelve₁Ranks rfl
    (by decide) (by decide) uncFiveTwelve₁LowDens uncFiveTwelve₁Dens rfl ![1, 1, 2, 1]
    ![1, 6, 11, 5] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncFiveTwelve₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncFiveTwelve₁LowRanks, uncFiveTwelve₁Ranks,
    uncFiveTwelve₁LowDens, uncFiveTwelve₁Dens] <;> linarith

/-- **Cell `(5,12)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,5}, B_{1,12}, 5, 12, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellFiveTwelve_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 12) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (1081 / 5000) 5 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellFiveTwelve_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(5,12)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 5 = gap212Cap 5 = 953 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFiveTwelve_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 12) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 5) (gap212Params.B j' 12) 5 12
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellFiveTwelve_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(5,13)` -/

/-- The first group's rank sets for cell `(5,13)`, certificate 1. -/
def uncFiveThirteen₁LowRanks : Fin 4 → Finset (Fin 5) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncFiveThirteen₁LowRanks`. -/
noncomputable def uncFiveThirteen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(5,13)`, certificate 1. -/
def uncFiveThirteen₁Ranks : Fin 4 → Finset (Fin 13) :=
  ![{2, 3, 5, 7, 8, 10, 11}, {12}, {0, 1}, {4, 6, 9}]

/-- The prefix densities of `Gap212.uncFiveThirteen₁Ranks`. -/
noncomputable def uncFiveThirteen₁Dens : Fin 4 → ℝ := ![7 / 12, 1 / 13, 1, 3 / 10]

/-- **Cell `(5,13)`, certificate 1.**

Block bounds `6143 / 20000`, `1081 / 65000`, `179 / 5000`, `501 / 10000`; no cut.
Valid on `4 / 625 < ω₀` and on
`6799 / 20000 + 8ω₀ + ϵ ≤ γ ≤ 31419 / 65000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3959500 + ϵ, 0.4693692 - ϵ]`. -/
theorem admitsPartition₄_cellFiveThirteen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 6799 / 20000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 31419 / 65000 - 2 * ω₀ - slack)
    {y : Fin (5 + 13) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (1081 / 5000) 5 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncFiveThirteen₁LowRanks uncFiveThirteen₁Ranks
    rfl (by decide) (by decide) uncFiveThirteen₁LowDens uncFiveThirteen₁Dens rfl ![7, 1, 1, 3]
    ![12, 13, 1, 10] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncFiveThirteen₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncFiveThirteen₁LowRanks, uncFiveThirteen₁Ranks,
    uncFiveThirteen₁LowDens, uncFiveThirteen₁Dens] <;> linarith

/-- **Cell `(5,13)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,5}, B_{1,13}, 5, 13, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellFiveThirteen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 13) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (1081 / 5000) 5 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellFiveThirteen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(5,13)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 5 = gap212Cap 5 = 953 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFiveThirteen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 13) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 5) (gap212Params.B j' 13) 5 13
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellFiveThirteen_band hωlo hωhi hγlo hγhi hy

/-- The hypotheses of the band theorems above are satisfiable: the chamber point `ω₀ = 7/1000`,
`γ = 2/5` and the constant profile `δ = 41/2500` meet all of them. -/
theorem cellsUncut2_hypotheses_satisfiable :
    (4 / 625 < (7 / 1000 : ℝ) ∧ (2 / 5 - slack : ℝ) ≤ 2 / 5 ∧
        (2 / 5 : ℝ) ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (7 / 40 : ℝ) (983 / 5000) 3 6 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (7 / 40 : ℝ) (521 / 2500) 3 8 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (7 / 40 : ℝ) (1063 / 5000) 3 9 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (7 / 40 : ℝ) (1081 / 5000) 3 10 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (7 / 40 : ℝ) (1081 / 5000) 3 11 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (7 / 40 : ℝ) (1081 / 5000) 3 12 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (7 / 40 : ℝ) (1081 / 5000) 3 13 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (917 / 5000 : ℝ) (1063 / 5000) 4 9 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (917 / 5000 : ℝ) (1081 / 5000) 4 10 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (917 / 5000 : ℝ) (1081 / 5000) 4 11 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (917 / 5000 : ℝ) (1081 / 5000) 4 12 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (917 / 5000 : ℝ) (1081 / 5000) 4 13 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (953 / 5000 : ℝ) (1063 / 5000) 5 9 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (953 / 5000 : ℝ) (1081 / 5000) 5 10 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (953 / 5000 : ℝ) (1081 / 5000) 5 11 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (953 / 5000 : ℝ) (1081 / 5000) 5 12 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (953 / 5000 : ℝ) (1081 / 5000) 5 13 (41 / 2500) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine ⟨⟨by norm_num, by rw [hsv]; norm_num, by rw [hδ, hsv]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 3 6]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 3 6]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 3 8]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 3 8]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 3 9]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 3 9]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 3 10]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 3 10]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 3 11]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 3 11]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 3 12]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 3 12]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 3 13]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 3 13]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 4 9]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 4 9]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 4 10]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 4 10]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 4 11]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 4 11]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 4 12]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 4 12]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 4 13]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 4 13]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 5 9]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 5 9]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 5 10]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 5 10]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 5 11]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 5 11]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 5 12]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 5 12]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 5 13]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 5 13]; norm_num⟩⟩

end Gap212
