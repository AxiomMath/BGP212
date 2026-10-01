/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCell

/-!
# The uncut rank certificates, part 4: the cells with ten or more ranks on both sides

`Gap212.Packing.admitsPartition₄_of_rank_certificate` bounds each of the four bins by
`#T_k·δ + r_k·(B₁ - m₁δ) + #U_k·δ + s_k·(B₂ - m₂δ)`, with `r_k` and `s_k` the prefix densities of
the two rank sets the bin holds. No cut, no threshold, no hypothesis on the profile beyond `Ξ`: this
is the *uncut* reading, and it closes 62 of the 91 cells `1 ≤ m ≤ m' ≤ 13` on the whole band
`ω₀ ∈ (4/625, 7/1000]` and the whole chamber `γ`-range.

This file carries 9 of them, the cells with ten or more ranks on both sides:

    (10,11)  (10,12)  (10,13)  (11,11)  (11,12)  (11,13)  (12,12)  (12,13)
    (13,13)

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


/-! ## Cell `(10,11)` -/

/-- The first group's rank sets for cell `(10,11)`, certificate 1. -/
def uncTenEleven₁LowRanks : Fin 4 → Finset (Fin 10) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTenEleven₁LowRanks`. -/
noncomputable def uncTenEleven₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(10,11)`, certificate 1. -/
def uncTenEleven₁Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2}, {3, 5, 8, 10}, {6, 9}, {4, 7}]

/-- The prefix densities of `Gap212.uncTenEleven₁Ranks`. -/
noncomputable def uncTenEleven₁Dens : Fin 4 → ℝ := ![1, 4 / 11, 1 / 5, 1 / 4]

/-- The first group's rank sets for cell `(10,11)`, certificate 2. -/
def uncTenEleven₂LowRanks : Fin 4 → Finset (Fin 10) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTenEleven₂LowRanks`. -/
noncomputable def uncTenEleven₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(10,11)`, certificate 2. -/
def uncTenEleven₂Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3}, {4, 7, 10}, {6, 9}, {5, 8}]

/-- The prefix densities of `Gap212.uncTenEleven₂Ranks`. -/
noncomputable def uncTenEleven₂Dens : Fin 4 → ℝ := ![1, 3 / 11, 1 / 5, 2 / 9]

/-- The first group's rank sets for cell `(10,11)`, certificate 3. -/
def uncTenEleven₃LowRanks : Fin 4 → Finset (Fin 10) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTenEleven₃LowRanks`. -/
noncomputable def uncTenEleven₃LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(10,11)`, certificate 3. -/
def uncTenEleven₃Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3, 4}, {7, 10}, {6, 9}, {5, 8}]

/-- The prefix densities of `Gap212.uncTenEleven₃Ranks`. -/
noncomputable def uncTenEleven₃Dens : Fin 4 → ℝ := ![1, 2 / 11, 1 / 5, 2 / 9]

/-- **Cell `(10,11)`, certificate 1.**

Block bounds `753 / 2500`, `1081 / 13750`, `999 / 25000`, `167 / 4000`; no cut.
Valid on `4 / 625 < ω₀` and on
`167 / 500 + 8ω₀ + ϵ ≤ γ ≤ 2897 / 6875 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3900000 + ϵ, 0.4073818 - ϵ]`. -/
theorem admitsPartition₄_cellTenEleven_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 167 / 500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2897 / 6875 - 2 * ω₀ - slack)
    {y : Fin (10 + 11) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncTenEleven₁LowRanks uncTenEleven₁Ranks rfl
    (by decide) (by decide) uncTenEleven₁LowDens uncTenEleven₁Dens rfl ![1, 4, 1, 1] ![1, 11, 5, 4]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncTenEleven₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncTenEleven₁LowRanks, uncTenEleven₁Ranks, uncTenEleven₁LowDens,
    uncTenEleven₁Dens] <;> linarith

/-- **Cell `(10,11)`, certificate 2.**

Block bounds `397 / 1250`, `3243 / 55000`, `999 / 25000`, `917 / 22500`; no cut.
Valid on `4 / 625 < ω₀` and on
`219 / 625 + 8ω₀ + ϵ ≤ γ ≤ 24257 / 55000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4064000 + ϵ, 0.4270364 - ϵ]`. -/
theorem admitsPartition₄_cellTenEleven_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 219 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 24257 / 55000 - 2 * ω₀ - slack)
    {y : Fin (10 + 11) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncTenEleven₂LowRanks uncTenEleven₂Ranks rfl
    (by decide) (by decide) uncTenEleven₂LowDens uncTenEleven₂Dens rfl ![1, 3, 1, 2] ![1, 11, 5, 9]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncTenEleven₂Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncTenEleven₂LowRanks, uncTenEleven₂Ranks, uncTenEleven₂LowDens,
    uncTenEleven₂Dens] <;> linarith

/-- **Cell `(10,11)`, certificate 3.**

Block bounds `167 / 500`, `1081 / 27500`, `999 / 25000`, `917 / 22500`; no cut.
Valid on `4 / 625 < ω₀` and on
`917 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 12669 / 27500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4228000 + ϵ, 0.4466909 - ϵ]`. -/
theorem admitsPartition₄_cellTenEleven_unc₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 917 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 12669 / 27500 - 2 * ω₀ - slack)
    {y : Fin (10 + 11) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncTenEleven₃LowRanks uncTenEleven₃Ranks rfl
    (by decide) (by decide) uncTenEleven₃LowDens uncTenEleven₃Dens rfl ![1, 2, 1, 2] ![1, 11, 5, 9]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncTenEleven₃Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncTenEleven₃LowRanks, uncTenEleven₃Ranks, uncTenEleven₃LowDens,
    uncTenEleven₃Dens] <;> linarith

/-- **Cell `(10,11)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,10}, B_{1,11}, 10, 11, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 3 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellTenEleven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (10 + 11) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (2897 / 6875 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellTenEleven_unc₁ hωlo (by linarith) h1 hy
  · rcases le_or_gt γ (24257 / 55000 - 2 * ω₀ - slack) with h2 | h2
    · exact admitsPartition₄_cellTenEleven_unc₂ hωlo (by linarith) h2 hy
    · exact admitsPartition₄_cellTenEleven_unc₃ hωlo (by linarith) (by linarith) hy

/-- **Cell `(10,11)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 10 = gap212Cap 10 = 1081 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellTenEleven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (10 + 11) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 10) (gap212Params.B j' 11) 10 11
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTenEleven_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(10,12)` -/

/-- The first group's rank sets for cell `(10,12)`, certificate 1. -/
def uncTenTwelve₁LowRanks : Fin 4 → Finset (Fin 10) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTenTwelve₁LowRanks`. -/
noncomputable def uncTenTwelve₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(10,12)`, certificate 1. -/
def uncTenTwelve₁Ranks : Fin 4 → Finset (Fin 12) :=
  ![{3, 5, 7, 9, 11}, {0, 1, 2}, {6, 10}, {4, 8}]

/-- The prefix densities of `Gap212.uncTenTwelve₁Ranks`. -/
noncomputable def uncTenTwelve₁Dens : Fin 4 → ℝ := ![5 / 12, 1, 2 / 11, 2 / 9]

/-- The first group's rank sets for cell `(10,12)`, certificate 2. -/
def uncTenTwelve₂LowRanks : Fin 4 → Finset (Fin 10) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTenTwelve₂LowRanks`. -/
noncomputable def uncTenTwelve₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(10,12)`, certificate 2. -/
def uncTenTwelve₂Ranks : Fin 4 → Finset (Fin 12) :=
  ![{2, 3, 5, 7, 9, 11}, {0, 1}, {6, 10}, {4, 8}]

/-- The prefix densities of `Gap212.uncTenTwelve₂Ranks`. -/
noncomputable def uncTenTwelve₂Dens : Fin 4 → ℝ := ![1 / 2, 1, 2 / 11, 2 / 9]

/-- **Cell `(10,12)`, certificate 1.**

Block bounds `18377 / 60000`, `343 / 5000`, `999 / 27500`, `167 / 4500`; no cut.
Valid on `4 / 625 < ω₀` and on
`4069 / 12000 + 8ω₀ + ϵ ≤ γ ≤ 2157 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3950833 + ϵ, 0.4174000 - ϵ]`. -/
theorem admitsPartition₄_cellTenTwelve_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 4069 / 12000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2157 / 5000 - 2 * ω₀ - slack)
    {y : Fin (10 + 12) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncTenTwelve₁LowRanks uncTenTwelve₁Ranks rfl
    (by decide) (by decide) uncTenTwelve₁LowDens uncTenTwelve₁Dens rfl ![5, 1, 2, 2] ![12, 1, 11, 9]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncTenTwelve₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncTenTwelve₁LowRanks, uncTenTwelve₁Ranks, uncTenTwelve₁LowDens,
    uncTenTwelve₁Dens] <;> linarith

/-- **Cell `(10,12)`, certificate 2.**

Block bounds `3243 / 10000`, `261 / 5000`, `999 / 27500`, `167 / 4500`; no cut.
Valid on `4 / 625 < ω₀` and on
`3571 / 10000 + 8ω₀ + ϵ ≤ γ ≤ 2239 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4131000 + ϵ, 0.4338000 - ϵ]`. -/
theorem admitsPartition₄_cellTenTwelve_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3571 / 10000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2239 / 5000 - 2 * ω₀ - slack)
    {y : Fin (10 + 12) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncTenTwelve₂LowRanks uncTenTwelve₂Ranks rfl
    (by decide) (by decide) uncTenTwelve₂LowDens uncTenTwelve₂Dens rfl ![1, 1, 2, 2] ![2, 1, 11, 9]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncTenTwelve₂Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncTenTwelve₂LowRanks, uncTenTwelve₂Ranks, uncTenTwelve₂LowDens,
    uncTenTwelve₂Dens] <;> linarith

/-- **Cell `(10,12)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,10}, B_{1,12}, 10, 12, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 2 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellTenTwelve_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (10 + 12) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (2157 / 5000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellTenTwelve_unc₁ hωlo (by linarith) h1 hy
  · exact admitsPartition₄_cellTenTwelve_unc₂ hωlo (by linarith) (by linarith) hy

/-- **Cell `(10,12)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 10 = gap212Cap 10 = 1081 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellTenTwelve_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (10 + 12) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 10) (gap212Params.B j' 12) 10 12
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTenTwelve_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(10,13)` -/

/-- The first group's rank sets for cell `(10,13)`, certificate 1. -/
def uncTenThirteen₁LowRanks : Fin 4 → Finset (Fin 10) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTenThirteen₁LowRanks`. -/
noncomputable def uncTenThirteen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(10,13)`, certificate 1. -/
def uncTenThirteen₁Ranks : Fin 4 → Finset (Fin 13) :=
  ![{2, 5, 7, 9, 11}, {4, 8, 12}, {0, 1}, {3, 6, 10}]

/-- The prefix densities of `Gap212.uncTenThirteen₁Ranks`. -/
noncomputable def uncTenThirteen₁Dens : Fin 4 → ℝ := ![5 / 12, 3 / 13, 1, 2 / 7]

/-- **Cell `(10,13)`, certificate 1.**

Block bounds `5989 / 20000`, `3243 / 65000`, `179 / 5000`, `219 / 4375`; no cut.
Valid on `4 / 625 < ω₀` and on
`1329 / 4000 + 8ω₀ + ϵ ≤ γ ≤ 29257 / 65000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3882500 + ϵ, 0.4361077 - ϵ]`. -/
theorem admitsPartition₄_cellTenThirteen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1329 / 4000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 29257 / 65000 - 2 * ω₀ - slack)
    {y : Fin (10 + 13) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncTenThirteen₁LowRanks uncTenThirteen₁Ranks rfl
    (by decide) (by decide) uncTenThirteen₁LowDens uncTenThirteen₁Dens rfl ![5, 3, 1, 2]
    ![12, 13, 1, 7] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncTenThirteen₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncTenThirteen₁LowRanks, uncTenThirteen₁Ranks,
    uncTenThirteen₁LowDens, uncTenThirteen₁Dens] <;> linarith

/-- **Cell `(10,13)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,10}, B_{1,13}, 10, 13, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellTenThirteen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (10 + 13) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellTenThirteen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(10,13)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 10 = gap212Cap 10 = 1081 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellTenThirteen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (10 + 13) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 10) (gap212Params.B j' 13) 10 13
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTenThirteen_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(11,11)` -/

/-- The first group's rank sets for cell `(11,11)`, certificate 1. -/
def uncElevenEleven₁LowRanks : Fin 4 → Finset (Fin 11) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncElevenEleven₁LowRanks`. -/
noncomputable def uncElevenEleven₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(11,11)`, certificate 1. -/
def uncElevenEleven₁Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2}, {3, 5, 8, 10}, {6, 9}, {4, 7}]

/-- The prefix densities of `Gap212.uncElevenEleven₁Ranks`. -/
noncomputable def uncElevenEleven₁Dens : Fin 4 → ℝ := ![1, 4 / 11, 1 / 5, 1 / 4]

/-- The first group's rank sets for cell `(11,11)`, certificate 2. -/
def uncElevenEleven₂LowRanks : Fin 4 → Finset (Fin 11) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncElevenEleven₂LowRanks`. -/
noncomputable def uncElevenEleven₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(11,11)`, certificate 2. -/
def uncElevenEleven₂Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3}, {4, 7, 10}, {6, 9}, {5, 8}]

/-- The prefix densities of `Gap212.uncElevenEleven₂Ranks`. -/
noncomputable def uncElevenEleven₂Dens : Fin 4 → ℝ := ![1, 3 / 11, 1 / 5, 2 / 9]

/-- The first group's rank sets for cell `(11,11)`, certificate 3. -/
def uncElevenEleven₃LowRanks : Fin 4 → Finset (Fin 11) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncElevenEleven₃LowRanks`. -/
noncomputable def uncElevenEleven₃LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(11,11)`, certificate 3. -/
def uncElevenEleven₃Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3, 4}, {7, 10}, {6, 9}, {5, 8}]

/-- The prefix densities of `Gap212.uncElevenEleven₃Ranks`. -/
noncomputable def uncElevenEleven₃Dens : Fin 4 → ℝ := ![1, 2 / 11, 1 / 5, 2 / 9]

/-- **Cell `(11,11)`, certificate 1.**

Block bounds `753 / 2500`, `1081 / 13750`, `999 / 25000`, `167 / 4000`; no cut.
Valid on `4 / 625 < ω₀` and on
`167 / 500 + 8ω₀ + ϵ ≤ γ ≤ 2897 / 6875 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3900000 + ϵ, 0.4073818 - ϵ]`. -/
theorem admitsPartition₄_cellElevenEleven_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 167 / 500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2897 / 6875 - 2 * ω₀ - slack)
    {y : Fin (11 + 11) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 11 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncElevenEleven₁LowRanks uncElevenEleven₁Ranks
    rfl (by decide) (by decide) uncElevenEleven₁LowDens uncElevenEleven₁Dens rfl ![1, 4, 1, 1]
    ![1, 11, 5, 4] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncElevenEleven₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncElevenEleven₁LowRanks, uncElevenEleven₁Ranks,
    uncElevenEleven₁LowDens, uncElevenEleven₁Dens] <;> linarith

/-- **Cell `(11,11)`, certificate 2.**

Block bounds `397 / 1250`, `3243 / 55000`, `999 / 25000`, `917 / 22500`; no cut.
Valid on `4 / 625 < ω₀` and on
`219 / 625 + 8ω₀ + ϵ ≤ γ ≤ 24257 / 55000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4064000 + ϵ, 0.4270364 - ϵ]`. -/
theorem admitsPartition₄_cellElevenEleven_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 219 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 24257 / 55000 - 2 * ω₀ - slack)
    {y : Fin (11 + 11) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 11 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncElevenEleven₂LowRanks uncElevenEleven₂Ranks
    rfl (by decide) (by decide) uncElevenEleven₂LowDens uncElevenEleven₂Dens rfl ![1, 3, 1, 2]
    ![1, 11, 5, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncElevenEleven₂Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncElevenEleven₂LowRanks, uncElevenEleven₂Ranks,
    uncElevenEleven₂LowDens, uncElevenEleven₂Dens] <;> linarith

/-- **Cell `(11,11)`, certificate 3.**

Block bounds `167 / 500`, `1081 / 27500`, `999 / 25000`, `917 / 22500`; no cut.
Valid on `4 / 625 < ω₀` and on
`917 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 12669 / 27500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4228000 + ϵ, 0.4466909 - ϵ]`. -/
theorem admitsPartition₄_cellElevenEleven_unc₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 917 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 12669 / 27500 - 2 * ω₀ - slack)
    {y : Fin (11 + 11) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 11 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncElevenEleven₃LowRanks uncElevenEleven₃Ranks
    rfl (by decide) (by decide) uncElevenEleven₃LowDens uncElevenEleven₃Dens rfl ![1, 2, 1, 2]
    ![1, 11, 5, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncElevenEleven₃Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncElevenEleven₃LowRanks, uncElevenEleven₃Ranks,
    uncElevenEleven₃LowDens, uncElevenEleven₃Dens] <;> linarith

/-- **Cell `(11,11)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,11}, B_{1,11}, 11, 11, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 3 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellElevenEleven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (11 + 11) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 11 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (2897 / 6875 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellElevenEleven_unc₁ hωlo (by linarith) h1 hy
  · rcases le_or_gt γ (24257 / 55000 - 2 * ω₀ - slack) with h2 | h2
    · exact admitsPartition₄_cellElevenEleven_unc₂ hωlo (by linarith) h2 hy
    · exact admitsPartition₄_cellElevenEleven_unc₃ hωlo (by linarith) (by linarith) hy

/-- **Cell `(11,11)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 11 = gap212Cap 11 = 1081 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellElevenEleven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (11 + 11) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 11) (gap212Params.B j' 11) 11 11
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellElevenEleven_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(11,12)` -/

/-- The first group's rank sets for cell `(11,12)`, certificate 1. -/
def uncElevenTwelve₁LowRanks : Fin 4 → Finset (Fin 11) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncElevenTwelve₁LowRanks`. -/
noncomputable def uncElevenTwelve₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(11,12)`, certificate 1. -/
def uncElevenTwelve₁Ranks : Fin 4 → Finset (Fin 12) :=
  ![{3, 5, 7, 9, 11}, {0, 1, 2}, {6, 10}, {4, 8}]

/-- The prefix densities of `Gap212.uncElevenTwelve₁Ranks`. -/
noncomputable def uncElevenTwelve₁Dens : Fin 4 → ℝ := ![5 / 12, 1, 2 / 11, 2 / 9]

/-- The first group's rank sets for cell `(11,12)`, certificate 2. -/
def uncElevenTwelve₂LowRanks : Fin 4 → Finset (Fin 11) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncElevenTwelve₂LowRanks`. -/
noncomputable def uncElevenTwelve₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(11,12)`, certificate 2. -/
def uncElevenTwelve₂Ranks : Fin 4 → Finset (Fin 12) :=
  ![{2, 3, 5, 7, 9, 11}, {0, 1}, {6, 10}, {4, 8}]

/-- The prefix densities of `Gap212.uncElevenTwelve₂Ranks`. -/
noncomputable def uncElevenTwelve₂Dens : Fin 4 → ℝ := ![1 / 2, 1, 2 / 11, 2 / 9]

/-- **Cell `(11,12)`, certificate 1.**

Block bounds `18377 / 60000`, `343 / 5000`, `999 / 27500`, `167 / 4500`; no cut.
Valid on `4 / 625 < ω₀` and on
`4069 / 12000 + 8ω₀ + ϵ ≤ γ ≤ 2157 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3950833 + ϵ, 0.4174000 - ϵ]`. -/
theorem admitsPartition₄_cellElevenTwelve_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 4069 / 12000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2157 / 5000 - 2 * ω₀ - slack)
    {y : Fin (11 + 12) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 11 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncElevenTwelve₁LowRanks uncElevenTwelve₁Ranks
    rfl (by decide) (by decide) uncElevenTwelve₁LowDens uncElevenTwelve₁Dens rfl ![5, 1, 2, 2]
    ![12, 1, 11, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncElevenTwelve₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncElevenTwelve₁LowRanks, uncElevenTwelve₁Ranks,
    uncElevenTwelve₁LowDens, uncElevenTwelve₁Dens] <;> linarith

/-- **Cell `(11,12)`, certificate 2.**

Block bounds `3243 / 10000`, `261 / 5000`, `999 / 27500`, `167 / 4500`; no cut.
Valid on `4 / 625 < ω₀` and on
`3571 / 10000 + 8ω₀ + ϵ ≤ γ ≤ 2239 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4131000 + ϵ, 0.4338000 - ϵ]`. -/
theorem admitsPartition₄_cellElevenTwelve_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3571 / 10000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2239 / 5000 - 2 * ω₀ - slack)
    {y : Fin (11 + 12) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 11 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncElevenTwelve₂LowRanks uncElevenTwelve₂Ranks
    rfl (by decide) (by decide) uncElevenTwelve₂LowDens uncElevenTwelve₂Dens rfl ![1, 1, 2, 2]
    ![2, 1, 11, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncElevenTwelve₂Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncElevenTwelve₂LowRanks, uncElevenTwelve₂Ranks,
    uncElevenTwelve₂LowDens, uncElevenTwelve₂Dens] <;> linarith

/-- **Cell `(11,12)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,11}, B_{1,12}, 11, 12, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 2 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellElevenTwelve_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (11 + 12) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 11 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (2157 / 5000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellElevenTwelve_unc₁ hωlo (by linarith) h1 hy
  · exact admitsPartition₄_cellElevenTwelve_unc₂ hωlo (by linarith) (by linarith) hy

/-- **Cell `(11,12)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 11 = gap212Cap 11 = 1081 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellElevenTwelve_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (11 + 12) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 11) (gap212Params.B j' 12) 11 12
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellElevenTwelve_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(11,13)` -/

/-- The first group's rank sets for cell `(11,13)`, certificate 1. -/
def uncElevenThirteen₁LowRanks : Fin 4 → Finset (Fin 11) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncElevenThirteen₁LowRanks`. -/
noncomputable def uncElevenThirteen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(11,13)`, certificate 1. -/
def uncElevenThirteen₁Ranks : Fin 4 → Finset (Fin 13) :=
  ![{2, 5, 7, 9, 11}, {4, 8, 12}, {0, 1}, {3, 6, 10}]

/-- The prefix densities of `Gap212.uncElevenThirteen₁Ranks`. -/
noncomputable def uncElevenThirteen₁Dens : Fin 4 → ℝ := ![5 / 12, 3 / 13, 1, 2 / 7]

/-- **Cell `(11,13)`, certificate 1.**

Block bounds `5989 / 20000`, `3243 / 65000`, `179 / 5000`, `219 / 4375`; no cut.
Valid on `4 / 625 < ω₀` and on
`1329 / 4000 + 8ω₀ + ϵ ≤ γ ≤ 29257 / 65000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3882500 + ϵ, 0.4361077 - ϵ]`. -/
theorem admitsPartition₄_cellElevenThirteen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1329 / 4000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 29257 / 65000 - 2 * ω₀ - slack)
    {y : Fin (11 + 13) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 11 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncElevenThirteen₁LowRanks
    uncElevenThirteen₁Ranks rfl (by decide) (by decide) uncElevenThirteen₁LowDens
    uncElevenThirteen₁Dens rfl ![5, 3, 1, 2] ![12, 13, 1, 7] (by decide)
    (fun k ↦ by fin_cases k <;> norm_num [uncElevenThirteen₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncElevenThirteen₁LowRanks, uncElevenThirteen₁Ranks,
    uncElevenThirteen₁LowDens, uncElevenThirteen₁Dens] <;> linarith

/-- **Cell `(11,13)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,11}, B_{1,13}, 11, 13, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellElevenThirteen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (11 + 13) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 11 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellElevenThirteen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(11,13)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 11 = gap212Cap 11 = 1081 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellElevenThirteen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (11 + 13) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 11) (gap212Params.B j' 13) 11 13
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellElevenThirteen_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(12,12)` -/

/-- The first group's rank sets for cell `(12,12)`, certificate 1. -/
def uncTwelveTwelve₁LowRanks : Fin 4 → Finset (Fin 12) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwelveTwelve₁LowRanks`. -/
noncomputable def uncTwelveTwelve₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(12,12)`, certificate 1. -/
def uncTwelveTwelve₁Ranks : Fin 4 → Finset (Fin 12) :=
  ![{3, 5, 7, 9, 11}, {0, 1, 2}, {6, 10}, {4, 8}]

/-- The prefix densities of `Gap212.uncTwelveTwelve₁Ranks`. -/
noncomputable def uncTwelveTwelve₁Dens : Fin 4 → ℝ := ![5 / 12, 1, 2 / 11, 2 / 9]

/-- The first group's rank sets for cell `(12,12)`, certificate 2. -/
def uncTwelveTwelve₂LowRanks : Fin 4 → Finset (Fin 12) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwelveTwelve₂LowRanks`. -/
noncomputable def uncTwelveTwelve₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(12,12)`, certificate 2. -/
def uncTwelveTwelve₂Ranks : Fin 4 → Finset (Fin 12) :=
  ![{2, 3, 5, 7, 9, 11}, {0, 1}, {6, 10}, {4, 8}]

/-- The prefix densities of `Gap212.uncTwelveTwelve₂Ranks`. -/
noncomputable def uncTwelveTwelve₂Dens : Fin 4 → ℝ := ![1 / 2, 1, 2 / 11, 2 / 9]

/-- **Cell `(12,12)`, certificate 1.**

Block bounds `18377 / 60000`, `343 / 5000`, `999 / 27500`, `167 / 4500`; no cut.
Valid on `4 / 625 < ω₀` and on
`4069 / 12000 + 8ω₀ + ϵ ≤ γ ≤ 2157 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3950833 + ϵ, 0.4174000 - ϵ]`. -/
theorem admitsPartition₄_cellTwelveTwelve_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 4069 / 12000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2157 / 5000 - 2 * ω₀ - slack)
    {y : Fin (12 + 12) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 12 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncTwelveTwelve₁LowRanks uncTwelveTwelve₁Ranks
    rfl (by decide) (by decide) uncTwelveTwelve₁LowDens uncTwelveTwelve₁Dens rfl ![5, 1, 2, 2]
    ![12, 1, 11, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncTwelveTwelve₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncTwelveTwelve₁LowRanks, uncTwelveTwelve₁Ranks,
    uncTwelveTwelve₁LowDens, uncTwelveTwelve₁Dens] <;> linarith

/-- **Cell `(12,12)`, certificate 2.**

Block bounds `3243 / 10000`, `261 / 5000`, `999 / 27500`, `167 / 4500`; no cut.
Valid on `4 / 625 < ω₀` and on
`3571 / 10000 + 8ω₀ + ϵ ≤ γ ≤ 2239 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4131000 + ϵ, 0.4338000 - ϵ]`. -/
theorem admitsPartition₄_cellTwelveTwelve_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3571 / 10000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2239 / 5000 - 2 * ω₀ - slack)
    {y : Fin (12 + 12) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 12 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncTwelveTwelve₂LowRanks uncTwelveTwelve₂Ranks
    rfl (by decide) (by decide) uncTwelveTwelve₂LowDens uncTwelveTwelve₂Dens rfl ![1, 1, 2, 2]
    ![2, 1, 11, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncTwelveTwelve₂Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncTwelveTwelve₂LowRanks, uncTwelveTwelve₂Ranks,
    uncTwelveTwelve₂LowDens, uncTwelveTwelve₂Dens] <;> linarith

/-- **Cell `(12,12)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,12}, B_{1,12}, 12, 12, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 2 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellTwelveTwelve_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (12 + 12) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 12 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (2157 / 5000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellTwelveTwelve_unc₁ hωlo (by linarith) h1 hy
  · exact admitsPartition₄_cellTwelveTwelve_unc₂ hωlo (by linarith) (by linarith) hy

/-- **Cell `(12,12)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 12 = gap212Cap 12 = 1081 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellTwelveTwelve_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (12 + 12) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 12) (gap212Params.B j' 12) 12 12
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTwelveTwelve_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(12,13)` -/

/-- The first group's rank sets for cell `(12,13)`, certificate 1. -/
def uncTwelveThirteen₁LowRanks : Fin 4 → Finset (Fin 12) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncTwelveThirteen₁LowRanks`. -/
noncomputable def uncTwelveThirteen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(12,13)`, certificate 1. -/
def uncTwelveThirteen₁Ranks : Fin 4 → Finset (Fin 13) :=
  ![{2, 5, 7, 9, 11}, {4, 8, 12}, {0, 1}, {3, 6, 10}]

/-- The prefix densities of `Gap212.uncTwelveThirteen₁Ranks`. -/
noncomputable def uncTwelveThirteen₁Dens : Fin 4 → ℝ := ![5 / 12, 3 / 13, 1, 2 / 7]

/-- **Cell `(12,13)`, certificate 1.**

Block bounds `5989 / 20000`, `3243 / 65000`, `179 / 5000`, `219 / 4375`; no cut.
Valid on `4 / 625 < ω₀` and on
`1329 / 4000 + 8ω₀ + ϵ ≤ γ ≤ 29257 / 65000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3882500 + ϵ, 0.4361077 - ϵ]`. -/
theorem admitsPartition₄_cellTwelveThirteen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1329 / 4000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 29257 / 65000 - 2 * ω₀ - slack)
    {y : Fin (12 + 13) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 12 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncTwelveThirteen₁LowRanks
    uncTwelveThirteen₁Ranks rfl (by decide) (by decide) uncTwelveThirteen₁LowDens
    uncTwelveThirteen₁Dens rfl ![5, 3, 1, 2] ![12, 13, 1, 7] (by decide)
    (fun k ↦ by fin_cases k <;> norm_num [uncTwelveThirteen₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncTwelveThirteen₁LowRanks, uncTwelveThirteen₁Ranks,
    uncTwelveThirteen₁LowDens, uncTwelveThirteen₁Dens] <;> linarith

/-- **Cell `(12,13)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,12}, B_{1,13}, 12, 13, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellTwelveThirteen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (12 + 13) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 12 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellTwelveThirteen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(12,13)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 12 = gap212Cap 12 = 1081 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellTwelveThirteen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (12 + 13) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 12) (gap212Params.B j' 13) 12 13
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellTwelveThirteen_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(13,13)` -/

/-- The first group's rank sets for cell `(13,13)`, certificate 1. -/
def uncThirteenThirteen₁LowRanks : Fin 4 → Finset (Fin 13) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncThirteenThirteen₁LowRanks`. -/
noncomputable def uncThirteenThirteen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(13,13)`, certificate 1. -/
def uncThirteenThirteen₁Ranks : Fin 4 → Finset (Fin 13) :=
  ![{2, 5, 7, 9, 11}, {4, 8, 12}, {0, 1}, {3, 6, 10}]

/-- The prefix densities of `Gap212.uncThirteenThirteen₁Ranks`. -/
noncomputable def uncThirteenThirteen₁Dens : Fin 4 → ℝ := ![5 / 12, 3 / 13, 1, 2 / 7]

/-- **Cell `(13,13)`, certificate 1.**

Block bounds `5989 / 20000`, `3243 / 65000`, `179 / 5000`, `219 / 4375`; no cut.
Valid on `4 / 625 < ω₀` and on
`1329 / 4000 + 8ω₀ + ϵ ≤ γ ≤ 29257 / 65000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3882500 + ϵ, 0.4361077 - ϵ]`. -/
theorem admitsPartition₄_cellThirteenThirteen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1329 / 4000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 29257 / 65000 - 2 * ω₀ - slack)
    {y : Fin (13 + 13) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 13 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncThirteenThirteen₁LowRanks
    uncThirteenThirteen₁Ranks rfl (by decide) (by decide) uncThirteenThirteen₁LowDens
    uncThirteenThirteen₁Dens rfl ![5, 3, 1, 2] ![12, 13, 1, 7] (by decide)
    (fun k ↦ by fin_cases k <;> norm_num [uncThirteenThirteen₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncThirteenThirteen₁LowRanks, uncThirteenThirteen₁Ranks,
    uncThirteenThirteen₁LowDens, uncThirteenThirteen₁Dens] <;> linarith

/-- **Cell `(13,13)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,13}, B_{1,13}, 13, 13, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellThirteenThirteen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (13 + 13) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 13 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellThirteenThirteen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(13,13)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 13 = gap212Cap 13 = 1081 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellThirteenThirteen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (13 + 13) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 13) (gap212Params.B j' 13) 13 13
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellThirteenThirteen_band hωlo hωhi hγlo hγhi hy

/-- The hypotheses of the band theorems above are satisfiable: the chamber point `ω₀ = 7/1000`,
`γ = 2/5` and the constant profile `δ = 41/2500` meet all of them. -/
theorem cellsUncut4_hypotheses_satisfiable :
    (4 / 625 < (7 / 1000 : ℝ) ∧ (2 / 5 - slack : ℝ) ≤ 2 / 5 ∧
        (2 / 5 : ℝ) ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 11 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 12 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 13 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (1081 / 5000 : ℝ) (1081 / 5000) 11 11 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (1081 / 5000 : ℝ) (1081 / 5000) 11 12 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (1081 / 5000 : ℝ) (1081 / 5000) 11 13 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (1081 / 5000 : ℝ) (1081 / 5000) 12 12 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (1081 / 5000 : ℝ) (1081 / 5000) 12 13 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (1081 / 5000 : ℝ) (1081 / 5000) 13 13 (41 / 2500) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine ⟨⟨by norm_num, by rw [hsv]; norm_num, by rw [hδ, hsv]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 10 11]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 10 11]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 10 12]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 10 12]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 10 13]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 10 13]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 11 11]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 11 11]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 11 12]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 11 12]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 11 13]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 11 13]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 12 12]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 12 12]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 12 13]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 12 13]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 13 13]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 13 13]; norm_num⟩⟩

end Gap212
