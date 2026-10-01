/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCell

/-!
# The uncut rank certificates, part 3: the cells with six to nine ranks on the low side

`Gap212.Packing.admitsPartition₄_of_rank_certificate` bounds each of the four bins by
`#T_k·δ + r_k·(B₁ - m₁δ) + #U_k·δ + s_k·(B₂ - m₂δ)`, with `r_k` and `s_k` the prefix densities of
the two rank sets the bin holds. No cut, no threshold, no hypothesis on the profile beyond `Ξ`: this
is the *uncut* reading, and it closes 62 of the 91 cells `1 ≤ m ≤ m' ≤ 13` on the whole band
`ω₀ ∈ (4/625, 7/1000]` and the whole chamber `γ`-range.

This file carries 13 of them, the cells with six to nine ranks on the low side:

    (6,10)  (6,11)  (6,12)  (6,13)  (7,11)  (7,12)  (7,13)  (8,11)
    (8,12)  (8,13)  (9,11)  (9,12)  (9,13)

## Why one check at the top of the band serves the whole band

Bin `k`'s check is `row_k ≤ capD γ ω₀ k`. In `ω₀` the two large capacities *fall*
(`capD 0 = γ - 2δ - 8ω₀ - ϵ`, `capD 1 = 1/2 - γ - 2ω₀ - ϵ`) and the two small ones *rise*
(`capD 2 = 4ω₀ + δ - ϵ`, `capD 3 = 8ω₀`). So a certificate is hardest for bins 0 and 1 at the top of
the band and hardest for bins 2 and 3 at the floor, and a certificate whose bin-2 and bin-3 rows fit
under the floor's capacities and whose `γ` window is computed at `ω₀ = 7/1000` is valid at every
level of the band. That is why every cell here but one needs no case analysis in `ω₀`: the exception
is `(6,10)`, whose top-of-range certificate needs `ω₀` above `27/4000`.

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

/-- **The low group's prefix-density check, once for all thirteen cells.** Every certificate
below puts the whole low group in bin `0` and nothing in the other three, so the rank sets are
`![univ, ∅, ∅, ∅]` and the densities `![1, 0, 0, 0]`: bin `0`'s prefix count is at most `j`
because `Fin.val` embeds it in `range j`, and the other three prefixes are empty. -/
private theorem uncLow_prefixDensity {m : ℕ} : ∀ k : Fin 4, ∀ j : ℕ,
    (((((![Finset.univ, ∅, ∅, ∅] : Fin 4 → Finset (Fin m)) k).filter
      (fun i ↦ i.val < j)).card : ℕ) : ℝ) ≤ (![1, 0, 0, 0] : Fin 4 → ℝ) k * j := by
  intro k j; fin_cases k
  · simpa using (Nat.cast_le (α := ℝ)).2 ((card_le_card_of_injOn (t := range j) Fin.val
      (fun i hi ↦ mem_range.2 (mem_filter.1 hi).2) Fin.val_injective.injOn).trans_eq
      (card_range j))
  all_goals simp

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
    (fun k ↦ by fin_cases k <;> simp) (fun k ↦ by rw [hs]; positivity) uncLow_prefixDensity
    (fun k ↦ by rw [hs]; exact prefixDensity_of_nat _ _ _ (hq k) (hU k)) c hcap
  intro k l hkl; fin_cases k <;> fin_cases l <;> simp_all

private theorem gap212Cap_seven : gap212Cap 7 = (127 / 625 : ℝ) := by norm_num [gap212Cap]

private theorem gap212Cap_eight : gap212Cap 8 = (521 / 2500 : ℝ) := by norm_num [gap212Cap]

/-! ## Cell `(6,10)` -/

/-- The first group's rank sets for cell `(6,10)`, certificate 1. -/
def uncSixTen₁LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncSixTen₁LowRanks`. -/
noncomputable def uncSixTen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,10)`, certificate 1. -/
def uncSixTen₁Ranks : Fin 4 → Finset (Fin 10) :=
  ![{2, 3, 5, 7, 9}, {0, 1}, {6}, {4, 8}]

/-- The prefix densities of `Gap212.uncSixTen₁Ranks`. -/
noncomputable def uncSixTen₁Dens : Fin 4 → ℝ := ![1 / 2, 1, 1 / 7, 2 / 9]

/-- The first group's rank sets for cell `(6,10)`, certificate 2. -/
def uncSixTen₂LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncSixTen₂LowRanks`. -/
noncomputable def uncSixTen₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,10)`, certificate 2. -/
def uncSixTen₂Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3}, {4, 6, 9}, {7}, {5, 8}]

/-- The prefix densities of `Gap212.uncSixTen₂Ranks`. -/
noncomputable def uncSixTen₂Dens : Fin 4 → ℝ := ![1, 3 / 10, 1 / 8, 2 / 9]

/-- The first group's rank sets for cell `(6,10)`, certificate 3. -/
def uncSixTen₃LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncSixTen₃LowRanks`. -/
noncomputable def uncSixTen₃LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,10)`, certificate 3. -/
def uncSixTen₃Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3, 4}, {6, 9}, {7}, {5, 8}]

/-- The prefix densities of `Gap212.uncSixTen₃Ranks`. -/
noncomputable def uncSixTen₃Dens : Fin 4 → ℝ := ![1, 1 / 5, 1 / 8, 2 / 9]

/-- The first group's rank sets for cell `(6,10)`, certificate 4. -/
def uncSixTen₄LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncSixTen₄LowRanks`. -/
noncomputable def uncSixTen₄LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,10)`, certificate 4. -/
def uncSixTen₄Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2}, {3, 5, 8}, {6, 9}, {4, 7}]

/-- The prefix densities of `Gap212.uncSixTen₄Ranks`. -/
noncomputable def uncSixTen₄Dens : Fin 4 → ℝ := ![1, 1 / 3, 1 / 5, 1 / 4]

/-- The first group's rank sets for cell `(6,10)`, certificate 5. -/
def uncSixTen₅LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncSixTen₅LowRanks`. -/
noncomputable def uncSixTen₅LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,10)`, certificate 5. -/
def uncSixTen₅Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3}, {5, 8}, {6, 9}, {4, 7}]

/-- The prefix densities of `Gap212.uncSixTen₅Ranks`. -/
noncomputable def uncSixTen₅Dens : Fin 4 → ℝ := ![1, 2 / 9, 1 / 5, 1 / 4]

/-- **Cell `(6,10)`, certificate 1.**

Block bounds `3047 / 10000`, `17 / 200`, `167 / 7000`, `111 / 2500`; no cut.
Valid on `4 / 625 < ω₀` and on
`27 / 80 + 8ω₀ + ϵ ≤ γ ≤ 83 / 200 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3935000 + ϵ, 0.4010000 - ϵ]`. -/
theorem admitsPartition₄_cellSixTen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 27 / 80 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 83 / 200 - 2 * ω₀ - slack)
    {y : Fin (6 + 10) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1081 / 5000) 6 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncSixTen₁LowRanks uncSixTen₁Ranks rfl
    (by decide) (by decide) uncSixTen₁LowDens uncSixTen₁Dens rfl ![1, 1, 1, 2] ![2, 1, 7, 9]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncSixTen₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncSixTen₁LowRanks, uncSixTen₁Ranks, uncSixTen₁LowDens,
    uncSixTen₁Dens] <;> linarith

/-- **Cell `(6,10)`, certificate 2.**

Block bounds `393 / 1250`, `3243 / 50000`, `917 / 40000`, `111 / 2500`; no cut.
Valid on `4 / 625 < ω₀` and on
`217 / 625 + 8ω₀ + ϵ ≤ γ ≤ 21757 / 50000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4032000 + ϵ, 0.4211400 - ϵ]`. -/
theorem admitsPartition₄_cellSixTen_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 217 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 21757 / 50000 - 2 * ω₀ - slack)
    {y : Fin (6 + 10) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1081 / 5000) 6 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncSixTen₂LowRanks uncSixTen₂Ranks rfl
    (by decide) (by decide) uncSixTen₂LowDens uncSixTen₂Dens rfl ![1, 3, 1, 2] ![1, 10, 8, 9]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncSixTen₂Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncSixTen₂LowRanks, uncSixTen₂Ranks, uncSixTen₂LowDens,
    uncSixTen₂Dens] <;> linarith

/-- **Cell `(6,10)`, certificate 3.**

Block bounds `827 / 2500`, `1081 / 25000`, `917 / 40000`, `111 / 2500`; no cut.
Valid on `4 / 625 < ω₀` and on
`909 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 11419 / 25000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4196000 + ϵ, 0.4427600 - ϵ]`. -/
theorem admitsPartition₄_cellSixTen_unc₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 909 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 11419 / 25000 - 2 * ω₀ - slack)
    {y : Fin (6 + 10) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1081 / 5000) 6 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncSixTen₃LowRanks uncSixTen₃Ranks rfl
    (by decide) (by decide) uncSixTen₃LowDens uncSixTen₃Dens rfl ![1, 1, 1, 2] ![1, 5, 8, 9]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncSixTen₃Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncSixTen₃LowRanks, uncSixTen₃Ranks, uncSixTen₃LowDens,
    uncSixTen₃Dens] <;> linarith

/-- **Cell `(6,10)`, certificate 4.**

Block bounds `149 / 500`, `333 / 5000`, `1081 / 25000`, `917 / 20000`; no cut.
Valid on `27 / 4000 < ω₀` and on
`827 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 2167 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3868000 + ϵ, 0.4194000 - ϵ]`. -/
theorem admitsPartition₄_cellSixTen_unc₄ {γ ω₀ : ℝ} (hωlo : 27 / 4000 < ω₀)
    (hγlo : 827 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2167 / 5000 - 2 * ω₀ - slack)
    {y : Fin (6 + 10) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1081 / 5000) 6 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncSixTen₄LowRanks uncSixTen₄Ranks rfl
    (by decide) (by decide) uncSixTen₄LowDens uncSixTen₄Dens rfl ![1, 1, 1, 1] ![1, 3, 5, 4]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncSixTen₄Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncSixTen₄LowRanks, uncSixTen₄Ranks, uncSixTen₄LowDens,
    uncSixTen₄Dens] <;> linarith

/-- **Cell `(6,10)`, certificate 5.**

Block bounds `393 / 1250`, `111 / 2500`, `1081 / 25000`, `917 / 20000`; no cut.
Valid on `27 / 4000 < ω₀` and on
`217 / 625 + 8ω₀ + ϵ ≤ γ ≤ 1139 / 2500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4032000 + ϵ, 0.4416000 - ϵ]`. -/
theorem admitsPartition₄_cellSixTen_unc₅ {γ ω₀ : ℝ} (hωlo : 27 / 4000 < ω₀)
    (hγlo : 217 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1139 / 2500 - 2 * ω₀ - slack)
    {y : Fin (6 + 10) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1081 / 5000) 6 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncSixTen₅LowRanks uncSixTen₅Ranks rfl
    (by decide) (by decide) uncSixTen₅LowDens uncSixTen₅Dens rfl ![1, 2, 1, 1] ![1, 9, 5, 4]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncSixTen₅Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncSixTen₅LowRanks, uncSixTen₅Ranks, uncSixTen₅LowDens,
    uncSixTen₅Dens] <;> linarith

/-- **Cell `(6,10)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,6}, B_{1,10}, 6, 10, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 5 rank certificates
with no cut, the band split at `ω₀ = 27 / 4000` because the certificate
the top of the `γ`-range needs has a bin-3 row above the band floor's capacity `8 · 4/625`. -/
theorem admitsPartition₄_cellSixTen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 10) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1081 / 5000) 6 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt ω₀ (27 / 4000) with hw1 | hw1
  · rcases le_or_gt γ (83 / 200 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellSixTen_unc₁ hωlo (by linarith) h1 hy
    · rcases le_or_gt γ (21757 / 50000 - 2 * ω₀ - slack) with h2 | h2
      · exact admitsPartition₄_cellSixTen_unc₂ hωlo (by linarith) h2 hy
      · exact admitsPartition₄_cellSixTen_unc₃ hωlo (by linarith) (by linarith) hy
  · rcases le_or_gt γ (2167 / 5000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellSixTen_unc₄ hw1 (by linarith) h1 hy
    · exact admitsPartition₄_cellSixTen_unc₅ hw1 (by linarith) (by linarith) hy

/-- **Cell `(6,10)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 6 = gap212Cap 6 = 983 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellSixTen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 10) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 6) (gap212Params.B j' 10) 6 10
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellSixTen_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(6,11)` -/

/-- The first group's rank sets for cell `(6,11)`, certificate 1. -/
def uncSixEleven₁LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncSixEleven₁LowRanks`. -/
noncomputable def uncSixEleven₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,11)`, certificate 1. -/
def uncSixEleven₁Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3}, {4, 7, 10}, {6, 9}, {5, 8}]

/-- The prefix densities of `Gap212.uncSixEleven₁Ranks`. -/
noncomputable def uncSixEleven₁Dens : Fin 4 → ℝ := ![1, 3 / 11, 1 / 5, 2 / 9]

/-- The first group's rank sets for cell `(6,11)`, certificate 2. -/
def uncSixEleven₂LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncSixEleven₂LowRanks`. -/
noncomputable def uncSixEleven₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,11)`, certificate 2. -/
def uncSixEleven₂Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3, 4, 5}, {10}, {7, 9}, {6, 8}]

/-- The prefix densities of `Gap212.uncSixEleven₂Ranks`. -/
noncomputable def uncSixEleven₂Dens : Fin 4 → ℝ := ![1, 1 / 11, 1 / 5, 2 / 9]

/-- **Cell `(6,11)`, certificate 1.**

Block bounds `149 / 500`, `3243 / 55000`, `999 / 25000`, `917 / 22500`; no cut.
Valid on `4 / 625 < ω₀` and on
`827 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 24257 / 55000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3868000 + ϵ, 0.4270364 - ϵ]`. -/
theorem admitsPartition₄_cellSixEleven_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 827 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 24257 / 55000 - 2 * ω₀ - slack)
    {y : Fin (6 + 11) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1081 / 5000) 6 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncSixEleven₁LowRanks uncSixEleven₁Ranks rfl
    (by decide) (by decide) uncSixEleven₁LowDens uncSixEleven₁Dens rfl ![1, 3, 1, 2] ![1, 11, 5, 9]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncSixEleven₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncSixEleven₁LowRanks, uncSixEleven₁Ranks, uncSixEleven₁LowDens,
    uncSixEleven₁Dens] <;> linarith

/-- **Cell `(6,11)`, certificate 2.**

Block bounds `827 / 2500`, `1081 / 55000`, `999 / 25000`, `917 / 22500`; no cut.
Valid on `4 / 625 < ω₀` and on
`909 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 26419 / 55000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4196000 + ϵ, 0.4663455 - ϵ]`. -/
theorem admitsPartition₄_cellSixEleven_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 909 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 26419 / 55000 - 2 * ω₀ - slack)
    {y : Fin (6 + 11) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1081 / 5000) 6 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncSixEleven₂LowRanks uncSixEleven₂Ranks rfl
    (by decide) (by decide) uncSixEleven₂LowDens uncSixEleven₂Dens rfl ![1, 1, 1, 2] ![1, 11, 5, 9]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncSixEleven₂Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncSixEleven₂LowRanks, uncSixEleven₂Ranks, uncSixEleven₂LowDens,
    uncSixEleven₂Dens] <;> linarith

/-- **Cell `(6,11)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,6}, B_{1,11}, 6, 11, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 2 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellSixEleven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 11) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1081 / 5000) 6 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (24257 / 55000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellSixEleven_unc₁ hωlo (by linarith) h1 hy
  · exact admitsPartition₄_cellSixEleven_unc₂ hωlo (by linarith) (by linarith) hy

/-- **Cell `(6,11)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 6 = gap212Cap 6 = 983 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellSixEleven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 11) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 6) (gap212Params.B j' 11) 6 11
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellSixEleven_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(6,12)` -/

/-- The first group's rank sets for cell `(6,12)`, certificate 1. -/
def uncSixTwelve₁LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncSixTwelve₁LowRanks`. -/
noncomputable def uncSixTwelve₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,12)`, certificate 1. -/
def uncSixTwelve₁Ranks : Fin 4 → Finset (Fin 12) :=
  ![{2, 3, 5, 7, 9, 11}, {0, 1}, {6, 10}, {4, 8}]

/-- The prefix densities of `Gap212.uncSixTwelve₁Ranks`. -/
noncomputable def uncSixTwelve₁Dens : Fin 4 → ℝ := ![1 / 2, 1, 2 / 11, 2 / 9]

/-- **Cell `(6,12)`, certificate 1.**

Block bounds `3047 / 10000`, `261 / 5000`, `999 / 27500`, `167 / 4500`; no cut.
Valid on `4 / 625 < ω₀` and on
`27 / 80 + 8ω₀ + ϵ ≤ γ ≤ 2239 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3935000 + ϵ, 0.4338000 - ϵ]`. -/
theorem admitsPartition₄_cellSixTwelve_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 27 / 80 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2239 / 5000 - 2 * ω₀ - slack)
    {y : Fin (6 + 12) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1081 / 5000) 6 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncSixTwelve₁LowRanks uncSixTwelve₁Ranks rfl
    (by decide) (by decide) uncSixTwelve₁LowDens uncSixTwelve₁Dens rfl ![1, 1, 2, 2] ![2, 1, 11, 9]
    (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncSixTwelve₁Dens]) (by decide) (capD γ ω₀)
    fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncSixTwelve₁LowRanks, uncSixTwelve₁Ranks, uncSixTwelve₁LowDens,
    uncSixTwelve₁Dens] <;> linarith

/-- **Cell `(6,12)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,6}, B_{1,12}, 6, 12, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellSixTwelve_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 12) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1081 / 5000) 6 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellSixTwelve_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(6,12)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 6 = gap212Cap 6 = 983 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellSixTwelve_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 12) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 6) (gap212Params.B j' 12) 6 12
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellSixTwelve_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(6,13)` -/

/-- The first group's rank sets for cell `(6,13)`, certificate 1. -/
def uncSixThirteen₁LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncSixThirteen₁LowRanks`. -/
noncomputable def uncSixThirteen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,13)`, certificate 1. -/
def uncSixThirteen₁Ranks : Fin 4 → Finset (Fin 13) :=
  ![{2, 3, 5, 7, 9, 11}, {6, 12}, {0, 1}, {4, 8, 10}]

/-- The prefix densities of `Gap212.uncSixThirteen₁Ranks`. -/
noncomputable def uncSixThirteen₁Dens : Fin 4 → ℝ := ![1 / 2, 2 / 13, 1, 3 / 11]

/-- **Cell `(6,13)`, certificate 1.**

Block bounds `593 / 2000`, `1081 / 32500`, `179 / 5000`, `2751 / 55000`; no cut.
Valid on `4 / 625 < ω₀` and on
`3293 / 10000 + 8ω₀ + ϵ ≤ γ ≤ 15169 / 32500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3853000 + ϵ, 0.4527385 - ϵ]`. -/
theorem admitsPartition₄_cellSixThirteen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3293 / 10000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 15169 / 32500 - 2 * ω₀ - slack)
    {y : Fin (6 + 13) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1081 / 5000) 6 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncSixThirteen₁LowRanks uncSixThirteen₁Ranks rfl
    (by decide) (by decide) uncSixThirteen₁LowDens uncSixThirteen₁Dens rfl ![1, 2, 1, 3]
    ![2, 13, 1, 11] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncSixThirteen₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncSixThirteen₁LowRanks, uncSixThirteen₁Ranks,
    uncSixThirteen₁LowDens, uncSixThirteen₁Dens] <;> linarith

/-- **Cell `(6,13)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,6}, B_{1,13}, 6, 13, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellSixThirteen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 13) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1081 / 5000) 6 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellSixThirteen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(6,13)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 6 = gap212Cap 6 = 983 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellSixThirteen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 13) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 6) (gap212Params.B j' 13) 6 13
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellSixThirteen_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(7,11)` -/

/-- The first group's rank sets for cell `(7,11)`, certificate 1. -/
def uncSevenEleven₁LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncSevenEleven₁LowRanks`. -/
noncomputable def uncSevenEleven₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,11)`, certificate 1. -/
def uncSevenEleven₁Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3}, {4, 7, 10}, {6, 9}, {5, 8}]

/-- The prefix densities of `Gap212.uncSevenEleven₁Ranks`. -/
noncomputable def uncSevenEleven₁Dens : Fin 4 → ℝ := ![1, 3 / 11, 1 / 5, 2 / 9]

/-- The first group's rank sets for cell `(7,11)`, certificate 2. -/
def uncSevenEleven₂LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncSevenEleven₂LowRanks`. -/
noncomputable def uncSevenEleven₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,11)`, certificate 2. -/
def uncSevenEleven₂Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3, 4, 5}, {10}, {7, 9}, {6, 8}]

/-- The prefix densities of `Gap212.uncSevenEleven₂Ranks`. -/
noncomputable def uncSevenEleven₂Dens : Fin 4 → ℝ := ![1, 1 / 11, 1 / 5, 2 / 9]

/-- **Cell `(7,11)`, certificate 1.**

Block bounds `1523 / 5000`, `3243 / 55000`, `999 / 25000`, `917 / 22500`; no cut.
Valid on `4 / 625 < ω₀` and on
`1687 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 24257 / 55000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3934000 + ϵ, 0.4270364 - ϵ]`. -/
theorem admitsPartition₄_cellSevenEleven_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1687 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 24257 / 55000 - 2 * ω₀ - slack)
    {y : Fin (7 + 11) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1081 / 5000) 7 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncSevenEleven₁LowRanks uncSevenEleven₁Ranks rfl
    (by decide) (by decide) uncSevenEleven₁LowDens uncSevenEleven₁Dens rfl ![1, 3, 1, 2]
    ![1, 11, 5, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncSevenEleven₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncSevenEleven₁LowRanks, uncSevenEleven₁Ranks,
    uncSevenEleven₁LowDens, uncSevenEleven₁Dens] <;> linarith

/-- **Cell `(7,11)`, certificate 2.**

Block bounds `1687 / 5000`, `1081 / 55000`, `999 / 25000`, `917 / 22500`; no cut.
Valid on `4 / 625 < ω₀` and on
`1851 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 26419 / 55000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4262000 + ϵ, 0.4663455 - ϵ]`. -/
theorem admitsPartition₄_cellSevenEleven_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1851 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 26419 / 55000 - 2 * ω₀ - slack)
    {y : Fin (7 + 11) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1081 / 5000) 7 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncSevenEleven₂LowRanks uncSevenEleven₂Ranks rfl
    (by decide) (by decide) uncSevenEleven₂LowDens uncSevenEleven₂Dens rfl ![1, 1, 1, 2]
    ![1, 11, 5, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncSevenEleven₂Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncSevenEleven₂LowRanks, uncSevenEleven₂Ranks,
    uncSevenEleven₂LowDens, uncSevenEleven₂Dens] <;> linarith

/-- **Cell `(7,11)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,7}, B_{1,11}, 7, 11, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 2 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellSevenEleven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (7 + 11) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1081 / 5000) 7 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (24257 / 55000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellSevenEleven_unc₁ hωlo (by linarith) h1 hy
  · exact admitsPartition₄_cellSevenEleven_unc₂ hωlo (by linarith) (by linarith) hy

/-- **Cell `(7,11)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 7 = gap212Cap 7 = 127 / 625` at every stratum `j`. -/
theorem admitsPartition₄_cellSevenEleven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (7 + 11) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 7) (gap212Params.B j' 11) 7 11
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellSevenEleven_band hωlo hωhi hγlo hγhi (gap212Cap_seven ▸ hy)

/-! ## Cell `(7,12)` -/

/-- The first group's rank sets for cell `(7,12)`, certificate 1. -/
def uncSevenTwelve₁LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncSevenTwelve₁LowRanks`. -/
noncomputable def uncSevenTwelve₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,12)`, certificate 1. -/
def uncSevenTwelve₁Ranks : Fin 4 → Finset (Fin 12) :=
  ![{0, 1, 2, 3, 4}, {5, 8, 11}, {7, 10}, {6, 9}]

/-- The prefix densities of `Gap212.uncSevenTwelve₁Ranks`. -/
noncomputable def uncSevenTwelve₁Dens : Fin 4 → ℝ := ![1, 1 / 4, 2 / 11, 1 / 5]

/-- **Cell `(7,12)`, certificate 1.**

Block bounds `1523 / 5000`, `1081 / 20000`, `999 / 27500`, `917 / 25000`; no cut.
Valid on `4 / 625 < ω₀` and on
`1687 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 8919 / 20000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3934000 + ϵ, 0.4319500 - ϵ]`. -/
theorem admitsPartition₄_cellSevenTwelve_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1687 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 8919 / 20000 - 2 * ω₀ - slack)
    {y : Fin (7 + 12) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1081 / 5000) 7 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncSevenTwelve₁LowRanks uncSevenTwelve₁Ranks rfl
    (by decide) (by decide) uncSevenTwelve₁LowDens uncSevenTwelve₁Dens rfl ![1, 1, 2, 1]
    ![1, 4, 11, 5] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncSevenTwelve₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncSevenTwelve₁LowRanks, uncSevenTwelve₁Ranks,
    uncSevenTwelve₁LowDens, uncSevenTwelve₁Dens] <;> linarith

/-- **Cell `(7,12)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,7}, B_{1,12}, 7, 12, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellSevenTwelve_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (7 + 12) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1081 / 5000) 7 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellSevenTwelve_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(7,12)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 7 = gap212Cap 7 = 127 / 625` at every stratum `j`. -/
theorem admitsPartition₄_cellSevenTwelve_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (7 + 12) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 7) (gap212Params.B j' 12) 7 12
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellSevenTwelve_band hωlo hωhi hγlo hγhi (gap212Cap_seven ▸ hy)

/-! ## Cell `(7,13)` -/

/-- The first group's rank sets for cell `(7,13)`, certificate 1. -/
def uncSevenThirteen₁LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncSevenThirteen₁LowRanks`. -/
noncomputable def uncSevenThirteen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,13)`, certificate 1. -/
def uncSevenThirteen₁Ranks : Fin 4 → Finset (Fin 13) :=
  ![{2, 3, 5, 7, 9, 11}, {6, 12}, {0, 1}, {4, 8, 10}]

/-- The prefix densities of `Gap212.uncSevenThirteen₁Ranks`. -/
noncomputable def uncSevenThirteen₁Dens : Fin 4 → ℝ := ![1 / 2, 2 / 13, 1, 3 / 11]

/-- **Cell `(7,13)`, certificate 1.**

Block bounds `3031 / 10000`, `1081 / 32500`, `179 / 5000`, `2751 / 55000`; no cut.
Valid on `4 / 625 < ω₀` and on
`3359 / 10000 + 8ω₀ + ϵ ≤ γ ≤ 15169 / 32500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3919000 + ϵ, 0.4527385 - ϵ]`. -/
theorem admitsPartition₄_cellSevenThirteen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3359 / 10000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 15169 / 32500 - 2 * ω₀ - slack)
    {y : Fin (7 + 13) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1081 / 5000) 7 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncSevenThirteen₁LowRanks uncSevenThirteen₁Ranks
    rfl (by decide) (by decide) uncSevenThirteen₁LowDens uncSevenThirteen₁Dens rfl ![1, 2, 1, 3]
    ![2, 13, 1, 11] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncSevenThirteen₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncSevenThirteen₁LowRanks, uncSevenThirteen₁Ranks,
    uncSevenThirteen₁LowDens, uncSevenThirteen₁Dens] <;> linarith

/-- **Cell `(7,13)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,7}, B_{1,13}, 7, 13, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellSevenThirteen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (7 + 13) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1081 / 5000) 7 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellSevenThirteen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(7,13)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 7 = gap212Cap 7 = 127 / 625` at every stratum `j`. -/
theorem admitsPartition₄_cellSevenThirteen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (7 + 13) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 7) (gap212Params.B j' 13) 7 13
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellSevenThirteen_band hωlo hωhi hγlo hγhi (gap212Cap_seven ▸ hy)

/-! ## Cell `(8,11)` -/

/-- The first group's rank sets for cell `(8,11)`, certificate 1. -/
def uncEightEleven₁LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncEightEleven₁LowRanks`. -/
noncomputable def uncEightEleven₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,11)`, certificate 1. -/
def uncEightEleven₁Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3}, {4, 7, 10}, {6, 9}, {5, 8}]

/-- The prefix densities of `Gap212.uncEightEleven₁Ranks`. -/
noncomputable def uncEightEleven₁Dens : Fin 4 → ℝ := ![1, 3 / 11, 1 / 5, 2 / 9]

/-- The first group's rank sets for cell `(8,11)`, certificate 2. -/
def uncEightEleven₂LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncEightEleven₂LowRanks`. -/
noncomputable def uncEightEleven₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,11)`, certificate 2. -/
def uncEightEleven₂Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3, 4}, {7, 10}, {6, 9}, {5, 8}]

/-- The prefix densities of `Gap212.uncEightEleven₂Ranks`. -/
noncomputable def uncEightEleven₂Dens : Fin 4 → ℝ := ![1, 2 / 11, 1 / 5, 2 / 9]

/-- **Cell `(8,11)`, certificate 1.**

Block bounds `1549 / 5000`, `3243 / 55000`, `999 / 25000`, `917 / 22500`; no cut.
Valid on `4 / 625 < ω₀` and on
`1713 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 24257 / 55000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3986000 + ϵ, 0.4270364 - ϵ]`. -/
theorem admitsPartition₄_cellEightEleven_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1713 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 24257 / 55000 - 2 * ω₀ - slack)
    {y : Fin (8 + 11) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1081 / 5000) 8 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncEightEleven₁LowRanks uncEightEleven₁Ranks rfl
    (by decide) (by decide) uncEightEleven₁LowDens uncEightEleven₁Dens rfl ![1, 3, 1, 2]
    ![1, 11, 5, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncEightEleven₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncEightEleven₁LowRanks, uncEightEleven₁Ranks,
    uncEightEleven₁LowDens, uncEightEleven₁Dens] <;> linarith

/-- **Cell `(8,11)`, certificate 2.**

Block bounds `1631 / 5000`, `1081 / 27500`, `999 / 25000`, `917 / 22500`; no cut.
Valid on `4 / 625 < ω₀` and on
`359 / 1000 + 8ω₀ + ϵ ≤ γ ≤ 12669 / 27500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4150000 + ϵ, 0.4466909 - ϵ]`. -/
theorem admitsPartition₄_cellEightEleven_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 359 / 1000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 12669 / 27500 - 2 * ω₀ - slack)
    {y : Fin (8 + 11) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1081 / 5000) 8 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncEightEleven₂LowRanks uncEightEleven₂Ranks rfl
    (by decide) (by decide) uncEightEleven₂LowDens uncEightEleven₂Dens rfl ![1, 2, 1, 2]
    ![1, 11, 5, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncEightEleven₂Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncEightEleven₂LowRanks, uncEightEleven₂Ranks,
    uncEightEleven₂LowDens, uncEightEleven₂Dens] <;> linarith

/-- **Cell `(8,11)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,8}, B_{1,11}, 8, 11, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 2 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellEightEleven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (8 + 11) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1081 / 5000) 8 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (24257 / 55000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellEightEleven_unc₁ hωlo (by linarith) h1 hy
  · exact admitsPartition₄_cellEightEleven_unc₂ hωlo (by linarith) (by linarith) hy

/-- **Cell `(8,11)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 8 = gap212Cap 8 = 521 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellEightEleven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (8 + 11) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 8) (gap212Params.B j' 11) 8 11
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellEightEleven_band hωlo hωhi hγlo hγhi (gap212Cap_eight ▸ hy)

/-! ## Cell `(8,12)` -/

/-- The first group's rank sets for cell `(8,12)`, certificate 1. -/
def uncEightTwelve₁LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncEightTwelve₁LowRanks`. -/
noncomputable def uncEightTwelve₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,12)`, certificate 1. -/
def uncEightTwelve₁Ranks : Fin 4 → Finset (Fin 12) :=
  ![{0, 1, 2, 3, 4}, {5, 8, 11}, {7, 10}, {6, 9}]

/-- The prefix densities of `Gap212.uncEightTwelve₁Ranks`. -/
noncomputable def uncEightTwelve₁Dens : Fin 4 → ℝ := ![1, 1 / 4, 2 / 11, 1 / 5]

/-- **Cell `(8,12)`, certificate 1.**

Block bounds `1549 / 5000`, `1081 / 20000`, `999 / 27500`, `917 / 25000`; no cut.
Valid on `4 / 625 < ω₀` and on
`1713 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 8919 / 20000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3986000 + ϵ, 0.4319500 - ϵ]`. -/
theorem admitsPartition₄_cellEightTwelve_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1713 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 8919 / 20000 - 2 * ω₀ - slack)
    {y : Fin (8 + 12) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1081 / 5000) 8 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncEightTwelve₁LowRanks uncEightTwelve₁Ranks rfl
    (by decide) (by decide) uncEightTwelve₁LowDens uncEightTwelve₁Dens rfl ![1, 1, 2, 1]
    ![1, 4, 11, 5] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncEightTwelve₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncEightTwelve₁LowRanks, uncEightTwelve₁Ranks,
    uncEightTwelve₁LowDens, uncEightTwelve₁Dens] <;> linarith

/-- **Cell `(8,12)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,8}, B_{1,12}, 8, 12, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellEightTwelve_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (8 + 12) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1081 / 5000) 8 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellEightTwelve_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(8,12)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 8 = gap212Cap 8 = 521 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellEightTwelve_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (8 + 12) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 8) (gap212Params.B j' 12) 8 12
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellEightTwelve_band hωlo hωhi hγlo hγhi (gap212Cap_eight ▸ hy)

/-! ## Cell `(8,13)` -/

/-- The first group's rank sets for cell `(8,13)`, certificate 1. -/
def uncEightThirteen₁LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncEightThirteen₁LowRanks`. -/
noncomputable def uncEightThirteen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,13)`, certificate 1. -/
def uncEightThirteen₁Ranks : Fin 4 → Finset (Fin 13) :=
  ![{2, 3, 5, 7, 9, 11}, {6, 12}, {0, 1}, {4, 8, 10}]

/-- The prefix densities of `Gap212.uncEightThirteen₁Ranks`. -/
noncomputable def uncEightThirteen₁Dens : Fin 4 → ℝ := ![1 / 2, 2 / 13, 1, 3 / 11]

/-- **Cell `(8,13)`, certificate 1.**

Block bounds `3083 / 10000`, `1081 / 32500`, `179 / 5000`, `2751 / 55000`; no cut.
Valid on `4 / 625 < ω₀` and on
`3411 / 10000 + 8ω₀ + ϵ ≤ γ ≤ 15169 / 32500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3971000 + ϵ, 0.4527385 - ϵ]`. -/
theorem admitsPartition₄_cellEightThirteen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3411 / 10000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 15169 / 32500 - 2 * ω₀ - slack)
    {y : Fin (8 + 13) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1081 / 5000) 8 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncEightThirteen₁LowRanks uncEightThirteen₁Ranks
    rfl (by decide) (by decide) uncEightThirteen₁LowDens uncEightThirteen₁Dens rfl ![1, 2, 1, 3]
    ![2, 13, 1, 11] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncEightThirteen₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncEightThirteen₁LowRanks, uncEightThirteen₁Ranks,
    uncEightThirteen₁LowDens, uncEightThirteen₁Dens] <;> linarith

/-- **Cell `(8,13)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,8}, B_{1,13}, 8, 13, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellEightThirteen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (8 + 13) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1081 / 5000) 8 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellEightThirteen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(8,13)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 8 = gap212Cap 8 = 521 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellEightThirteen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (8 + 13) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 8) (gap212Params.B j' 13) 8 13
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellEightThirteen_band hωlo hωhi hγlo hγhi (gap212Cap_eight ▸ hy)

/-! ## Cell `(9,11)` -/

/-- The first group's rank sets for cell `(9,11)`, certificate 1. -/
def uncNineEleven₁LowRanks : Fin 4 → Finset (Fin 9) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncNineEleven₁LowRanks`. -/
noncomputable def uncNineEleven₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(9,11)`, certificate 1. -/
def uncNineEleven₁Ranks : Fin 4 → Finset (Fin 11) :=
  ![{2, 4, 6, 8, 10}, {0, 1}, {5, 9}, {3, 7}]

/-- The prefix densities of `Gap212.uncNineEleven₁Ranks`. -/
noncomputable def uncNineEleven₁Dens : Fin 4 → ℝ := ![5 / 11, 1, 1 / 5, 1 / 4]

/-- The first group's rank sets for cell `(9,11)`, certificate 2. -/
def uncNineEleven₂LowRanks : Fin 4 → Finset (Fin 9) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncNineEleven₂LowRanks`. -/
noncomputable def uncNineEleven₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(9,11)`, certificate 2. -/
def uncNineEleven₂Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3}, {4, 7, 10}, {6, 9}, {5, 8}]

/-- The prefix densities of `Gap212.uncNineEleven₂Ranks`. -/
noncomputable def uncNineEleven₂Dens : Fin 4 → ℝ := ![1, 3 / 11, 1 / 5, 2 / 9]

/-- The first group's rank sets for cell `(9,11)`, certificate 3. -/
def uncNineEleven₃LowRanks : Fin 4 → Finset (Fin 9) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncNineEleven₃LowRanks`. -/
noncomputable def uncNineEleven₃LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(9,11)`, certificate 3. -/
def uncNineEleven₃Ranks : Fin 4 → Finset (Fin 11) :=
  ![{0, 1, 2, 3, 4}, {7, 10}, {6, 9}, {5, 8}]

/-- The prefix densities of `Gap212.uncNineEleven₃Ranks`. -/
noncomputable def uncNineEleven₃Dens : Fin 4 → ℝ := ![1, 2 / 11, 1 / 5, 2 / 9]

/-- **Cell `(9,11)`, certificate 1.**

Block bounds `8549 / 27500`, `343 / 5000`, `999 / 25000`, `167 / 4000`; no cut.
Valid on `4 / 625 < ω₀` and on
`9451 / 27500 + 8ω₀ + ϵ ≤ γ ≤ 2157 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3996727 + ϵ, 0.4174000 - ϵ]`. -/
theorem admitsPartition₄_cellNineEleven_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 9451 / 27500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2157 / 5000 - 2 * ω₀ - slack)
    {y : Fin (9 + 11) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncNineEleven₁LowRanks uncNineEleven₁Ranks rfl
    (by decide) (by decide) uncNineEleven₁LowDens uncNineEleven₁Dens rfl ![5, 1, 1, 1]
    ![11, 1, 5, 4] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncNineEleven₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncNineEleven₁LowRanks, uncNineEleven₁Ranks,
    uncNineEleven₁LowDens, uncNineEleven₁Dens] <;> linarith

/-- **Cell `(9,11)`, certificate 2.**

Block bounds `157 / 500`, `3243 / 55000`, `999 / 25000`, `917 / 22500`; no cut.
Valid on `4 / 625 < ω₀` and on
`867 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 24257 / 55000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4028000 + ϵ, 0.4270364 - ϵ]`. -/
theorem admitsPartition₄_cellNineEleven_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 867 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 24257 / 55000 - 2 * ω₀ - slack)
    {y : Fin (9 + 11) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncNineEleven₂LowRanks uncNineEleven₂Ranks rfl
    (by decide) (by decide) uncNineEleven₂LowDens uncNineEleven₂Dens rfl ![1, 3, 1, 2]
    ![1, 11, 5, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncNineEleven₂Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncNineEleven₂LowRanks, uncNineEleven₂Ranks,
    uncNineEleven₂LowDens, uncNineEleven₂Dens] <;> linarith

/-- **Cell `(9,11)`, certificate 3.**

Block bounds `413 / 1250`, `1081 / 27500`, `999 / 25000`, `917 / 22500`; no cut.
Valid on `4 / 625 < ω₀` and on
`227 / 625 + 8ω₀ + ϵ ≤ γ ≤ 12669 / 27500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4192000 + ϵ, 0.4466909 - ϵ]`. -/
theorem admitsPartition₄_cellNineEleven_unc₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 227 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 12669 / 27500 - 2 * ω₀ - slack)
    {y : Fin (9 + 11) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncNineEleven₃LowRanks uncNineEleven₃Ranks rfl
    (by decide) (by decide) uncNineEleven₃LowDens uncNineEleven₃Dens rfl ![1, 2, 1, 2]
    ![1, 11, 5, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncNineEleven₃Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncNineEleven₃LowRanks, uncNineEleven₃Ranks,
    uncNineEleven₃LowDens, uncNineEleven₃Dens] <;> linarith

/-- **Cell `(9,11)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,9}, B_{1,11}, 9, 11, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 3 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellNineEleven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (9 + 11) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 11 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (2157 / 5000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellNineEleven_unc₁ hωlo (by linarith) h1 hy
  · rcases le_or_gt γ (24257 / 55000 - 2 * ω₀ - slack) with h2 | h2
    · exact admitsPartition₄_cellNineEleven_unc₂ hωlo (by linarith) h2 hy
    · exact admitsPartition₄_cellNineEleven_unc₃ hωlo (by linarith) (by linarith) hy

/-- **Cell `(9,11)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 9 = gap212Cap 9 = 1063 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellNineEleven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (9 + 11) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 9) (gap212Params.B j' 11) 9 11
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellNineEleven_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(9,12)` -/

/-- The first group's rank sets for cell `(9,12)`, certificate 1. -/
def uncNineTwelve₁LowRanks : Fin 4 → Finset (Fin 9) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncNineTwelve₁LowRanks`. -/
noncomputable def uncNineTwelve₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(9,12)`, certificate 1. -/
def uncNineTwelve₁Ranks : Fin 4 → Finset (Fin 12) :=
  ![{3, 5, 7, 9, 11}, {0, 1, 2}, {6, 10}, {4, 8}]

/-- The prefix densities of `Gap212.uncNineTwelve₁Ranks`. -/
noncomputable def uncNineTwelve₁Dens : Fin 4 → ℝ := ![5 / 12, 1, 2 / 11, 2 / 9]

/-- The first group's rank sets for cell `(9,12)`, certificate 2. -/
def uncNineTwelve₂LowRanks : Fin 4 → Finset (Fin 9) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncNineTwelve₂LowRanks`. -/
noncomputable def uncNineTwelve₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(9,12)`, certificate 2. -/
def uncNineTwelve₂Ranks : Fin 4 → Finset (Fin 12) :=
  ![{2, 3, 5, 7, 9, 11}, {0, 1}, {6, 10}, {4, 8}]

/-- The prefix densities of `Gap212.uncNineTwelve₂Ranks`. -/
noncomputable def uncNineTwelve₂Dens : Fin 4 → ℝ := ![1 / 2, 1, 2 / 11, 2 / 9]

/-- **Cell `(9,12)`, certificate 1.**

Block bounds `18161 / 60000`, `343 / 5000`, `999 / 27500`, `167 / 4500`; no cut.
Valid on `4 / 625 < ω₀` and on
`20129 / 60000 + 8ω₀ + ϵ ≤ γ ≤ 2157 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3914833 + ϵ, 0.4174000 - ϵ]`. -/
theorem admitsPartition₄_cellNineTwelve_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 20129 / 60000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2157 / 5000 - 2 * ω₀ - slack)
    {y : Fin (9 + 12) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncNineTwelve₁LowRanks uncNineTwelve₁Ranks rfl
    (by decide) (by decide) uncNineTwelve₁LowDens uncNineTwelve₁Dens rfl ![5, 1, 2, 2]
    ![12, 1, 11, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncNineTwelve₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncNineTwelve₁LowRanks, uncNineTwelve₁Ranks,
    uncNineTwelve₁LowDens, uncNineTwelve₁Dens] <;> linarith

/-- **Cell `(9,12)`, certificate 2.**

Block bounds `3207 / 10000`, `261 / 5000`, `999 / 27500`, `167 / 4500`; no cut.
Valid on `4 / 625 < ω₀` and on
`707 / 2000 + 8ω₀ + ϵ ≤ γ ≤ 2239 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4095000 + ϵ, 0.4338000 - ϵ]`. -/
theorem admitsPartition₄_cellNineTwelve_unc₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 707 / 2000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2239 / 5000 - 2 * ω₀ - slack)
    {y : Fin (9 + 12) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncNineTwelve₂LowRanks uncNineTwelve₂Ranks rfl
    (by decide) (by decide) uncNineTwelve₂LowDens uncNineTwelve₂Dens rfl ![1, 1, 2, 2]
    ![2, 1, 11, 9] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncNineTwelve₂Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncNineTwelve₂LowRanks, uncNineTwelve₂Ranks,
    uncNineTwelve₂LowDens, uncNineTwelve₂Dens] <;> linarith

/-- **Cell `(9,12)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,9}, B_{1,12}, 9, 12, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is a `γ` chain of 2 rank certificates
with no cut and no case analysis in `ω₀`. -/
theorem admitsPartition₄_cellNineTwelve_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (9 + 12) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 12 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rcases le_or_gt γ (2157 / 5000 - 2 * ω₀ - slack) with h1 | h1
  · exact admitsPartition₄_cellNineTwelve_unc₁ hωlo (by linarith) h1 hy
  · exact admitsPartition₄_cellNineTwelve_unc₂ hωlo (by linarith) (by linarith) hy

/-- **Cell `(9,12)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 9 = gap212Cap 9 = 1063 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellNineTwelve_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (9 + 12) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 9) (gap212Params.B j' 12) 9 12
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellNineTwelve_band hωlo hωhi hγlo hγhi hy

/-! ## Cell `(9,13)` -/

/-- The first group's rank sets for cell `(9,13)`, certificate 1. -/
def uncNineThirteen₁LowRanks : Fin 4 → Finset (Fin 9) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.uncNineThirteen₁LowRanks`. -/
noncomputable def uncNineThirteen₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(9,13)`, certificate 1. -/
def uncNineThirteen₁Ranks : Fin 4 → Finset (Fin 13) :=
  ![{2, 5, 7, 9, 11}, {4, 8, 12}, {0, 1}, {3, 6, 10}]

/-- The prefix densities of `Gap212.uncNineThirteen₁Ranks`. -/
noncomputable def uncNineThirteen₁Dens : Fin 4 → ℝ := ![5 / 12, 3 / 13, 1, 2 / 7]

/-- **Cell `(9,13)`, certificate 1.**

Block bounds `5917 / 20000`, `3243 / 65000`, `179 / 5000`, `219 / 4375`; no cut.
Valid on `4 / 625 < ω₀` and on
`6573 / 20000 + 8ω₀ + ϵ ≤ γ ≤ 29257 / 65000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3846500 + ϵ, 0.4361077 - ϵ]`. -/
theorem admitsPartition₄_cellNineThirteen_unc₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 6573 / 20000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 29257 / 65000 - 2 * ω₀ - slack)
    {y : Fin (9 + 13) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_uncut hy (by norm_num) uncNineThirteen₁LowRanks uncNineThirteen₁Ranks
    rfl (by decide) (by decide) uncNineThirteen₁LowDens uncNineThirteen₁Dens rfl ![5, 3, 1, 2]
    ![12, 13, 1, 7] (by decide) (fun k ↦ by fin_cases k <;> norm_num [uncNineThirteen₁Dens])
    (by decide) (capD γ ω₀) fun k ↦ ?_
  fin_cases k <;> simp [capD, hδ, uncNineThirteen₁LowRanks, uncNineThirteen₁Ranks,
    uncNineThirteen₁LowDens, uncNineThirteen₁Dens] <;> linarith

/-- **Cell `(9,13)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,9}, B_{1,13}, 9, 13, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

One rank certificate covers the whole chamber: no case analysis at all. -/
theorem admitsPartition₄_cellNineThirteen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (9 + 13) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 13 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  exact admitsPartition₄_cellNineThirteen_unc₁ hωlo (by linarith) (by linarith) hy

/-- **Cell `(9,13)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 9 = gap212Cap 9 = 1063 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellNineThirteen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (9 + 13) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 9) (gap212Params.B j' 13) 9 13
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellNineThirteen_band hωlo hωhi hγlo hγhi hy

/-- The hypotheses of the band theorems above are satisfiable: the chamber point `ω₀ = 7/1000`,
`γ = 2/5` and the constant profile `δ = 41/2500` meet all of them. -/
theorem cellsUncut3_hypotheses_satisfiable :
    (4 / 625 < (7 / 1000 : ℝ) ∧ (2 / 5 - slack : ℝ) ≤ 2 / 5 ∧
        (2 / 5 : ℝ) ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (983 / 5000 : ℝ) (1081 / 5000) 6 10 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (983 / 5000 : ℝ) (1081 / 5000) 6 11 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (983 / 5000 : ℝ) (1081 / 5000) 6 12 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (983 / 5000 : ℝ) (1081 / 5000) 6 13 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (127 / 625 : ℝ) (1081 / 5000) 7 11 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (127 / 625 : ℝ) (1081 / 5000) 7 12 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (127 / 625 : ℝ) (1081 / 5000) 7 13 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (521 / 2500 : ℝ) (1081 / 5000) 8 11 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (521 / 2500 : ℝ) (1081 / 5000) 8 12 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (521 / 2500 : ℝ) (1081 / 5000) 8 13 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 11 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 12 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 13 (41 / 2500) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine ⟨⟨by norm_num, by rw [hsv]; norm_num, by rw [hδ, hsv]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 6 10]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 6 10]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 6 11]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 6 11]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 6 12]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 6 12]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 6 13]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 6 13]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 7 11]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 7 11]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 7 12]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 7 12]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 7 13]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 7 13]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 8 11]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 8 11]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 8 12]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 8 12]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 8 13]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 8 13]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 9 11]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 9 11]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 9 12]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 9 12]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 9 13]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 9 13]; norm_num⟩⟩

end Gap212
