/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCut
public import Gap212.Packing.SortedCell

/-!
# Four cells that need a threshold per region of the exponent

`Gap212.Packing.SortedCellsCut` closes six of the twelve cells `t = 1/25` misses, each at one
fixed threshold over the whole band. Four more — `(4,4)`, `(5,5)`, `(5,6)` and `(6,6)` — are
closed here with a threshold per region of `γ`, and the obstruction is not the level:

> At one fixed `ω₀` the threshold that closes a point already varies with `γ`.

So no tiling of the band in `ω₀` alone serves them, however fine. What does serve them is a case
split on `γ`, which is what `Gap212.Defs.ConditionD` permits: it quantifies over the chamber and
then asks for a partition, so a proof may fix a different threshold in each region of `(γ, ω₀)`.

Two thresholds suffice at each of the four:

    (4,4): t = 11/125 then 29/500      (5,5): t = 41/500 then 61/1000
    (5,6): t = 69/1000 then 1/20       (6,6): t = 37/500 then 3/50

In each cell the first threshold serves `γ` up to the `γ` ceiling of the certificate that ends its
region and the second serves the rest, and both regions run over the whole band `(4/625, 7/1000]`
with no case analysis in `ω₀` at all. The quantifier order is the one
`Gap212.Packing.admitsPartition₄_of_cut` needs: inside a region the threshold is a numeral, fixed
before `γ` and before `ω₀`.

## What this settles

With the six of `Gap212.Packing.SortedCellsCut` this closes ten of the twelve cells the cut
`t = 1/25` misses, each on the whole band. The other two, `(3,3)` and `(8,8)`, take two nested
thresholds and are closed in `Gap212.Packing.SortedCellsMid` and `Gap212.Packing.SortedCellsEight`.
-/

@[expose] public section

namespace Gap212

open Finset Gap212.Packing


/-! ## Cell `(4,4)` -/

/-- The first group's rank sets for cell `(4,4)`, the low half's certificate 1. -/
def cutFourFourUnder₁LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFourFourUnder₁LowRanks`. -/
noncomputable def cutFourFourUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,4)`, the low half's certificate 1. -/
def cutFourFourUnder₁Ranks : Fin 4 → Finset (Fin 4) :=
  ![{0, 2}, {1}, ∅, {3}]

/-- The slopes of `Gap212.cutFourFourUnder₁Ranks`. -/
noncomputable def cutFourFourUnder₁Dens : Fin 4 → ℝ := ![1 / 2, 1 / 2, 0, 1 / 4]

/-- The constants of `Gap212.cutFourFourUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutFourFourUnder₁Const : Fin 4 → ℝ := ![1 / 2, 0, 0, 0]

/-- The first group's rank sets for cell `(4,4)`, the high half's certificate 1. -/
def cutFourFourOver₁LowRanks : Fin 4 → Finset (Fin 4) :=
  ![{0, 1, 2}, ∅, ∅, {3}]

/-- The prefix densities of `Gap212.cutFourFourOver₁LowRanks`. -/
noncomputable def cutFourFourOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 1 / 4]

/-- The second group's rank sets for cell `(4,4)`, the high half's certificate 1. -/
def cutFourFourOver₁Ranks : Fin 4 → Finset (Fin 4) :=
  ![{0}, {1, 2}, {3}, ∅]

/-- The slopes of `Gap212.cutFourFourOver₁Ranks`. -/
noncomputable def cutFourFourOver₁Dens : Fin 4 → ℝ := ![1, 1, 1 / 3, 0]

/-- The constants of `Gap212.cutFourFourOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutFourFourOver₁Const : Fin 4 → ℝ := ![0, -1, -1 / 3, 0]

/-- The first group's rank sets for cell `(4,4)`, the high half's certificate 2. -/
def cutFourFourOver₂LowRanks : Fin 4 → Finset (Fin 4) :=
  ![{0, 1, 2}, ∅, ∅, {3}]

/-- The prefix densities of `Gap212.cutFourFourOver₂LowRanks`. -/
noncomputable def cutFourFourOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 1 / 4]

/-- The second group's rank sets for cell `(4,4)`, the high half's certificate 2. -/
def cutFourFourOver₂Ranks : Fin 4 → Finset (Fin 4) :=
  ![{0, 1}, {3}, {2}, ∅]

/-- The slopes of `Gap212.cutFourFourOver₂Ranks`. -/
noncomputable def cutFourFourOver₂Dens : Fin 4 → ℝ := ![1, 1 / 3, 1 / 2, 0]

/-- The constants of `Gap212.cutFourFourOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutFourFourOver₂Const : Fin 4 → ℝ := ![0, -1 / 3, -1 / 2, 0]

/-- The first group's rank sets for cell `(4,4)`, the low half's certificate 2. -/
def cutFourFourUnder₂LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFourFourUnder₂LowRanks`. -/
noncomputable def cutFourFourUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,4)`, the low half's certificate 2. -/
def cutFourFourUnder₂Ranks : Fin 4 → Finset (Fin 4) :=
  ![{0, 1}, {2}, ∅, {3}]

/-- The slopes of `Gap212.cutFourFourUnder₂Ranks`. -/
noncomputable def cutFourFourUnder₂Dens : Fin 4 → ℝ := ![0, 1 / 3, 0, 1 / 4]

/-- The constants of `Gap212.cutFourFourUnder₂Ranks`, nonnegative throughout. -/
noncomputable def cutFourFourUnder₂Const : Fin 4 → ℝ := ![2, 0, 0, 0]

/-- The first group's rank sets for cell `(4,4)`, the high half's certificate 3. -/
def cutFourFourOver₃LowRanks : Fin 4 → Finset (Fin 4) :=
  ![{0, 1, 2}, ∅, ∅, {3}]

/-- The prefix densities of `Gap212.cutFourFourOver₃LowRanks`. -/
noncomputable def cutFourFourOver₃LowDens : Fin 4 → ℝ := ![1, 0, 0, 1 / 4]

/-- The second group's rank sets for cell `(4,4)`, the high half's certificate 3. -/
def cutFourFourOver₃Ranks : Fin 4 → Finset (Fin 4) :=
  ![{0, 1}, {2}, {3}, ∅]

/-- The slopes of `Gap212.cutFourFourOver₃Ranks`. -/
noncomputable def cutFourFourOver₃Dens : Fin 4 → ℝ := ![1, 1 / 2, 1 / 3, 0]

/-- The constants of `Gap212.cutFourFourOver₃Ranks`, nonpositive throughout. -/
noncomputable def cutFourFourOver₃Const : Fin 4 → ℝ := ![0, -1 / 2, -1 / 3, 0]

/-- **Cell `(4,4)`, the low half's certificate 1.**

Block bounds `3109 / 10000`, `753 / 10000`, `0`, `917 / 20000`.
Valid on `4 / 625 < ω₀` and on
`3437 / 10000 + 8ω₀ + ϵ ≤ γ ≤ 4247 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3997000 + ϵ, 0.4107000 - ϵ]`. The cut is at `t = 11 / 125`. -/
theorem admitsPartition₄_cellFourFour_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3437 / 10000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4247 / 10000 - 2 * ω₀ - slack)
    {y : Fin (4 + 4) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (917 / 5000) 4 4 (41 / 2500))
    (hcut : ∀ i : Fin (4 + 4), 4 ≤ (i : ℕ) → y i ≤ 11 / 125) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutFourFourUnder₁LowRanks cutFourFourUnder₁Ranks (by decide) (by decide) (by decide) (by decide)
    cutFourFourUnder₁LowDens cutFourFourUnder₁Dens cutFourFourUnder₁Const ?_ ?_ ?_ ?_ ?_
    (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFourFourUnder₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutFourFourUnder₁Dens]
  · intro k; fin_cases k <;> norm_num [cutFourFourUnder₁Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFourFourUnder₁LowDens])
    all_goals exact fun j ↦ by simp [cutFourFourUnder₁LowRanks, cutFourFourUnder₁LowDens]
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 1 2 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFourFourUnder₁Dens, cutFourFourUnder₁Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 2 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFourFourUnder₁Dens, cutFourFourUnder₁Const])
    · intro j _ _; simp [cutFourFourUnder₁Ranks, cutFourFourUnder₁Dens, cutFourFourUnder₁Const]
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 4 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFourFourUnder₁Dens, cutFourFourUnder₁Const])
  · intro k; fin_cases k <;> simp [capD, hδ, cutFourFourUnder₁LowRanks, cutFourFourUnder₁Ranks,
      cutFourFourUnder₁LowDens, cutFourFourUnder₁Dens, cutFourFourUnder₁Const] <;> linarith

/-- **Cell `(4,4)`, the high half's certificate 1.**

Block bounds `753 / 2500`, `79 / 1000`, `159 / 5000`, `917 / 20000`.
Valid on `4 / 625 < ω₀` and on
`167 / 500 + 8ω₀ + ϵ ≤ γ ≤ 421 / 1000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3900000 + ϵ, 0.4070000 - ϵ]`. The cut is at `t = 11 / 125`. -/
theorem admitsPartition₄_cellFourFour_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 167 / 500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 421 / 1000 - 2 * ω₀ - slack)
    {y : Fin (4 + 4) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (917 / 5000) 4 4 (41 / 2500))
    (hcut : ∃ i : Fin (4 + 4), 4 ≤ (i : ℕ) ∧ 11 / 125 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutFourFourOver₁LowRanks cutFourFourOver₁Ranks (by decide) (by decide) (by decide) (by decide)
    cutFourFourOver₁LowDens cutFourFourOver₁Dens cutFourFourOver₁Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFourFourOver₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutFourFourOver₁Dens]
  · intro k; fin_cases k <;> norm_num [cutFourFourOver₁Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFourFourOver₁LowDens])
    · exact fun j ↦ by simp [cutFourFourOver₁LowRanks, cutFourFourOver₁LowDens]
    · exact fun j ↦ by simp [cutFourFourOver₁LowRanks, cutFourFourOver₁LowDens]
    · exact fun j ↦ (prefixDensity_of_nat _ 1 4 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFourFourOver₁LowDens])
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFourFourOver₁Dens, cutFourFourOver₁Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 (-1) 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFourFourOver₁Dens, cutFourFourOver₁Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 (-1) 3 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFourFourOver₁Dens, cutFourFourOver₁Const])
    · intro j _ _; simp [cutFourFourOver₁Ranks, cutFourFourOver₁Dens, cutFourFourOver₁Const]
  · intro k; fin_cases k <;> simp [capD, hδ, cutFourFourOver₁LowRanks, cutFourFourOver₁Ranks,
      cutFourFourOver₁LowDens, cutFourFourOver₁Dens, cutFourFourOver₁Const] <;> linarith

/-- **Cell `(4,4)`, the high half's certificate 2.**

Block bounds `397 / 1250`, `159 / 5000`, `79 / 2000`, `917 / 20000`.
Valid on `4 / 625 < ω₀` and on
`219 / 625 + 8ω₀ + ϵ ≤ γ ≤ 2341 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4064000 + ϵ, 0.4542000 - ϵ]`. The cut is at `t = 11 / 125`. -/
theorem admitsPartition₄_cellFourFour_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 219 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2341 / 5000 - 2 * ω₀ - slack)
    {y : Fin (4 + 4) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (917 / 5000) 4 4 (41 / 2500))
    (hcut : ∃ i : Fin (4 + 4), 4 ≤ (i : ℕ) ∧ 11 / 125 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutFourFourOver₂LowRanks cutFourFourOver₂Ranks (by decide) (by decide) (by decide) (by decide)
    cutFourFourOver₂LowDens cutFourFourOver₂Dens cutFourFourOver₂Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFourFourOver₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutFourFourOver₂Dens]
  · intro k; fin_cases k <;> norm_num [cutFourFourOver₂Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFourFourOver₂LowDens])
    · exact fun j ↦ by simp [cutFourFourOver₂LowRanks, cutFourFourOver₂LowDens]
    · exact fun j ↦ by simp [cutFourFourOver₂LowRanks, cutFourFourOver₂LowDens]
    · exact fun j ↦ (prefixDensity_of_nat _ 1 4 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFourFourOver₂LowDens])
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFourFourOver₂Dens, cutFourFourOver₂Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 (-1) 3 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFourFourOver₂Dens, cutFourFourOver₂Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 (-1) 2 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFourFourOver₂Dens, cutFourFourOver₂Const])
    · intro j _ _; simp [cutFourFourOver₂Ranks, cutFourFourOver₂Dens, cutFourFourOver₂Const]
  · intro k; fin_cases k <;> simp [capD, hδ, cutFourFourOver₂LowRanks, cutFourFourOver₂Ranks,
      cutFourFourOver₂LowDens, cutFourFourOver₂Dens, cutFourFourOver₂Const] <;> linarith

/-- **Cell `(4,4)`, the low half's certificate 2.**

Block bounds `1497 / 5000`, `167 / 3000`, `0`, `917 / 20000`.
Valid on `4 / 625 < ω₀` and on
`1661 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 1333 / 3000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3882000 + ϵ, 0.4303333 - ϵ]`. The cut is at `t = 29 / 500`. -/
theorem admitsPartition₄_cellFourFour_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1661 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1333 / 3000 - 2 * ω₀ - slack)
    {y : Fin (4 + 4) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (917 / 5000) 4 4 (41 / 2500))
    (hcut : ∀ i : Fin (4 + 4), 4 ≤ (i : ℕ) → y i ≤ 29 / 500) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutFourFourUnder₂LowRanks cutFourFourUnder₂Ranks (by decide) (by decide) (by decide) (by decide)
    cutFourFourUnder₂LowDens cutFourFourUnder₂Dens cutFourFourUnder₂Const ?_ ?_ ?_ ?_ ?_
    (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFourFourUnder₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutFourFourUnder₂Dens]
  · intro k; fin_cases k <;> norm_num [cutFourFourUnder₂Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFourFourUnder₂LowDens])
    all_goals exact fun j ↦ by simp [cutFourFourUnder₂LowRanks, cutFourFourUnder₂LowDens]
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 0 2 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFourFourUnder₂Dens, cutFourFourUnder₂Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 3 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFourFourUnder₂Dens, cutFourFourUnder₂Const])
    · intro j _ _; simp [cutFourFourUnder₂Ranks, cutFourFourUnder₂Dens, cutFourFourUnder₂Const]
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 4 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFourFourUnder₂Dens, cutFourFourUnder₂Const])
  · intro k; fin_cases k <;> simp [capD, hδ, cutFourFourUnder₂LowRanks, cutFourFourUnder₂Ranks,
      cutFourFourUnder₂LowDens, cutFourFourUnder₂Dens, cutFourFourUnder₂Const] <;> linarith

/-- **Cell `(4,4)`, the high half's certificate 3.**

Block bounds `397 / 1250`, `109 / 2000`, `209 / 5000`, `917 / 20000`.
Valid on `4 / 625 < ω₀` and on
`219 / 625 + 8ω₀ + ϵ ≤ γ ≤ 891 / 2000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4064000 + ϵ, 0.4315000 - ϵ]`. The cut is at `t = 29 / 500`. -/
theorem admitsPartition₄_cellFourFour_over₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 219 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 891 / 2000 - 2 * ω₀ - slack)
    {y : Fin (4 + 4) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (917 / 5000) 4 4 (41 / 2500))
    (hcut : ∃ i : Fin (4 + 4), 4 ≤ (i : ℕ) ∧ 29 / 500 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutFourFourOver₃LowRanks cutFourFourOver₃Ranks (by decide) (by decide) (by decide) (by decide)
    cutFourFourOver₃LowDens cutFourFourOver₃Dens cutFourFourOver₃Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFourFourOver₃LowDens]
  · intro k; fin_cases k <;> norm_num [cutFourFourOver₃Dens]
  · intro k; fin_cases k <;> norm_num [cutFourFourOver₃Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFourFourOver₃LowDens])
    · exact fun j ↦ by simp [cutFourFourOver₃LowRanks, cutFourFourOver₃LowDens]
    · exact fun j ↦ by simp [cutFourFourOver₃LowRanks, cutFourFourOver₃LowDens]
    · exact fun j ↦ (prefixDensity_of_nat _ 1 4 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFourFourOver₃LowDens])
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFourFourOver₃Dens, cutFourFourOver₃Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 (-1) 2 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFourFourOver₃Dens, cutFourFourOver₃Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 (-1) 3 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFourFourOver₃Dens, cutFourFourOver₃Const])
    · intro j _ _; simp [cutFourFourOver₃Ranks, cutFourFourOver₃Dens, cutFourFourOver₃Const]
  · intro k; fin_cases k <;> simp [capD, hδ, cutFourFourOver₃LowRanks, cutFourFourOver₃Ranks,
      cutFourFourOver₃LowDens, cutFourFourOver₃Dens, cutFourFourOver₃Const] <;> linarith

/-- **Cell `(4,4)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,4}, B_{1,4}, 4, 4, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate, at the thresholds `11 / 125, 29 / 500` — one per `γ` region, the region
boundaries being the `γ` ceilings of the certificates that end them — then a `γ`
split inside each region on each half. No single threshold serves the whole `γ`-range:
at one fixed `ω₀` the binding threshold already varies with `γ`, so the missing dimension
is `γ` and not `ω₀`.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellFourFour_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 4) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (917 / 5000) 4 4 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rw [hδ] at hγhi
  rcases le_or_gt γ (4247 / 10000 - 2 * ω₀ - slack) with hr1 | hr1
  · refine admitsPartition₄_of_cut (t := 11 / 125) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
    · exact admitsPartition₄_cellFourFour_under₁ hωlo (by linarith) (by linarith) hy hcut
    · rcases le_or_gt γ (421 / 1000 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellFourFour_over₁ hωlo (by linarith) h1 hy hcut
      · exact admitsPartition₄_cellFourFour_over₂ hωlo (by linarith) (by linarith) hy hcut
  · refine admitsPartition₄_of_cut (t := 29 / 500) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
    · exact admitsPartition₄_cellFourFour_under₂ hωlo (by linarith) (by linarith) hy hcut
    · exact admitsPartition₄_cellFourFour_over₃ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(4,4)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellFourFour_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (4 + 4) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (917 / 5000) 4 4 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellFourFour_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(4,4)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 4 = gap212Cap 4 = 917 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFourFour_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 4) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 4) (gap212Params.B j' 4) 4 4
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hB : gap212Cap 4 = (917 / 5000 : ℝ) := by norm_num [gap212Cap]
  exact admitsPartition₄_cellFourFour_band hωlo hωhi hγlo hγhi (hB ▸ hy)

/-! ## Cell `(5,5)` -/

/-- The first group's rank sets for cell `(5,5)`, the low half's certificate 1. -/
def cutFiveFiveUnder₁LowRanks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1, 2, 3}, ∅, {4}, ∅]

/-- The prefix densities of `Gap212.cutFiveFiveUnder₁LowRanks`. -/
noncomputable def cutFiveFiveUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 1 / 5, 0]

/-- The second group's rank sets for cell `(5,5)`, the low half's certificate 1. -/
def cutFiveFiveUnder₁Ranks : Fin 4 → Finset (Fin 5) :=
  ![{0, 2, 4}, {1}, ∅, {3}]

/-- The slopes of `Gap212.cutFiveFiveUnder₁Ranks`. -/
noncomputable def cutFiveFiveUnder₁Dens : Fin 4 → ℝ := ![1 / 2, 1 / 2, 0, 1 / 4]

/-- The constants of `Gap212.cutFiveFiveUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutFiveFiveUnder₁Const : Fin 4 → ℝ := ![1 / 2, 0, 0, 0]

/-- The first group's rank sets for cell `(5,5)`, the high half's certificate 1. -/
def cutFiveFiveOver₁LowRanks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1, 2}, ∅, {4}, {3}]

/-- The prefix densities of `Gap212.cutFiveFiveOver₁LowRanks`. -/
noncomputable def cutFiveFiveOver₁LowDens : Fin 4 → ℝ := ![1, 0, 1 / 5, 1 / 4]

/-- The second group's rank sets for cell `(5,5)`, the high half's certificate 1. -/
def cutFiveFiveOver₁Ranks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1}, {2, 3, 4}, ∅, ∅]

/-- The slopes of `Gap212.cutFiveFiveOver₁Ranks`. -/
noncomputable def cutFiveFiveOver₁Dens : Fin 4 → ℝ := ![1, 3 / 4, 0, 0]

/-- The constants of `Gap212.cutFiveFiveOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutFiveFiveOver₁Const : Fin 4 → ℝ := ![0, -3 / 4, 0, 0]

/-- The first group's rank sets for cell `(5,5)`, the high half's certificate 2. -/
def cutFiveFiveOver₂LowRanks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1, 2}, ∅, {4}, {3}]

/-- The prefix densities of `Gap212.cutFiveFiveOver₂LowRanks`. -/
noncomputable def cutFiveFiveOver₂LowDens : Fin 4 → ℝ := ![1, 0, 1 / 5, 1 / 4]

/-- The second group's rank sets for cell `(5,5)`, the high half's certificate 2. -/
def cutFiveFiveOver₂Ranks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1, 2}, {3, 4}, ∅, ∅]

/-- The slopes of `Gap212.cutFiveFiveOver₂Ranks`. -/
noncomputable def cutFiveFiveOver₂Dens : Fin 4 → ℝ := ![1, 1 / 2, 0, 0]

/-- The constants of `Gap212.cutFiveFiveOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutFiveFiveOver₂Const : Fin 4 → ℝ := ![0, -1 / 2, 0, 0]

/-- The first group's rank sets for cell `(5,5)`, the low half's certificate 2. -/
def cutFiveFiveUnder₂LowRanks : Fin 4 → Finset (Fin 5) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFiveFiveUnder₂LowRanks`. -/
noncomputable def cutFiveFiveUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(5,5)`, the low half's certificate 2. -/
def cutFiveFiveUnder₂Ranks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1}, {2}, {4}, {3}]

/-- The slopes of `Gap212.cutFiveFiveUnder₂Ranks`. -/
noncomputable def cutFiveFiveUnder₂Dens : Fin 4 → ℝ := ![0, 1 / 3, 1 / 5, 1 / 4]

/-- The constants of `Gap212.cutFiveFiveUnder₂Ranks`, nonnegative throughout. -/
noncomputable def cutFiveFiveUnder₂Const : Fin 4 → ℝ := ![2, 0, 0, 0]

/-- The first group's rank sets for cell `(5,5)`, the high half's certificate 3. -/
def cutFiveFiveOver₃LowRanks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1, 2}, ∅, {4}, {3}]

/-- The prefix densities of `Gap212.cutFiveFiveOver₃LowRanks`. -/
noncomputable def cutFiveFiveOver₃LowDens : Fin 4 → ℝ := ![1, 0, 1 / 5, 1 / 4]

/-- The second group's rank sets for cell `(5,5)`, the high half's certificate 3. -/
def cutFiveFiveOver₃Ranks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1, 2}, {3, 4}, ∅, ∅]

/-- The slopes of `Gap212.cutFiveFiveOver₃Ranks`. -/
noncomputable def cutFiveFiveOver₃Dens : Fin 4 → ℝ := ![1, 1 / 2, 0, 0]

/-- The constants of `Gap212.cutFiveFiveOver₃Ranks`, nonpositive throughout. -/
noncomputable def cutFiveFiveOver₃Const : Fin 4 → ℝ := ![0, -1 / 2, 0, 0]

/-- The first group's rank sets for cell `(5,5)`, the high half's certificate 4. -/
def cutFiveFiveOver₄LowRanks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1, 2}, ∅, {4}, {3}]

/-- The prefix densities of `Gap212.cutFiveFiveOver₄LowRanks`. -/
noncomputable def cutFiveFiveOver₄LowDens : Fin 4 → ℝ := ![1, 0, 1 / 5, 1 / 4]

/-- The second group's rank sets for cell `(5,5)`, the high half's certificate 4. -/
def cutFiveFiveOver₄Ranks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1, 2, 3}, {4}, ∅, ∅]

/-- The slopes of `Gap212.cutFiveFiveOver₄Ranks`. -/
noncomputable def cutFiveFiveOver₄Dens : Fin 4 → ℝ := ![1, 1 / 4, 0, 0]

/-- The constants of `Gap212.cutFiveFiveOver₄Ranks`, nonpositive throughout. -/
noncomputable def cutFiveFiveOver₄Const : Fin 4 → ℝ := ![0, -1 / 4, 0, 0]

/-- **Cell `(5,5)`, the low half's certificate 1.**

Block bounds `621 / 2000`, `707 / 10000`, `953 / 25000`, `871 / 20000`.
Valid on `4 / 625 < ω₀` and on
`3433 / 10000 + 8ω₀ + ϵ ≤ γ ≤ 4293 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3993000 + ϵ, 0.4153000 - ϵ]`. The cut is at `t = 41 / 500`. -/
theorem admitsPartition₄_cellFiveFive_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3433 / 10000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4293 / 10000 - 2 * ω₀ - slack)
    {y : Fin (5 + 5) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (953 / 5000) 5 5 (41 / 2500))
    (hcut : ∀ i : Fin (5 + 5), 5 ≤ (i : ℕ) → y i ≤ 41 / 500) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutFiveFiveUnder₁LowRanks cutFiveFiveUnder₁Ranks (by decide) (by decide) (by decide) (by decide)
    cutFiveFiveUnder₁LowDens cutFiveFiveUnder₁Dens cutFiveFiveUnder₁Const ?_ ?_ ?_ ?_ ?_
    (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFiveFiveUnder₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutFiveFiveUnder₁Dens]
  · intro k; fin_cases k <;> norm_num [cutFiveFiveUnder₁Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveFiveUnder₁LowDens])
    · exact fun j ↦ by simp [cutFiveFiveUnder₁LowRanks, cutFiveFiveUnder₁LowDens]
    · exact fun j ↦ (prefixDensity_of_nat _ 1 5 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveFiveUnder₁LowDens])
    · exact fun j ↦ by simp [cutFiveFiveUnder₁LowRanks, cutFiveFiveUnder₁LowDens]
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 1 2 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveFiveUnder₁Dens, cutFiveFiveUnder₁Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 2 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveFiveUnder₁Dens, cutFiveFiveUnder₁Const])
    · intro j _ _; simp [cutFiveFiveUnder₁Ranks, cutFiveFiveUnder₁Dens, cutFiveFiveUnder₁Const]
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 4 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveFiveUnder₁Dens, cutFiveFiveUnder₁Const])
  · intro k; fin_cases k <;> simp [capD, hδ, cutFiveFiveUnder₁LowRanks, cutFiveFiveUnder₁Ranks,
      cutFiveFiveUnder₁LowDens, cutFiveFiveUnder₁Dens, cutFiveFiveUnder₁Const] <;> linarith

/-- **Cell `(5,5)`, the high half's certificate 1.**

Block bounds `187 / 625`, `1629 / 20000`, `953 / 25000`, `871 / 20000`.
Valid on `4 / 625 < ω₀` and on
`83 / 250 + 8ω₀ + ϵ ≤ γ ≤ 8371 / 20000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3880000 + ϵ, 0.4045500 - ϵ]`. The cut is at `t = 41 / 500`. -/
theorem admitsPartition₄_cellFiveFive_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 83 / 250 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 8371 / 20000 - 2 * ω₀ - slack)
    {y : Fin (5 + 5) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (953 / 5000) 5 5 (41 / 2500))
    (hcut : ∃ i : Fin (5 + 5), 5 ≤ (i : ℕ) ∧ 41 / 500 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutFiveFiveOver₁LowRanks cutFiveFiveOver₁Ranks (by decide) (by decide) (by decide) (by decide)
    cutFiveFiveOver₁LowDens cutFiveFiveOver₁Dens cutFiveFiveOver₁Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFiveFiveOver₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutFiveFiveOver₁Dens]
  · intro k; fin_cases k <;> norm_num [cutFiveFiveOver₁Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveFiveOver₁LowDens])
    · exact fun j ↦ by simp [cutFiveFiveOver₁LowRanks, cutFiveFiveOver₁LowDens]
    · exact fun j ↦ (prefixDensity_of_nat _ 1 5 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveFiveOver₁LowDens])
    · exact fun j ↦ (prefixDensity_of_nat _ 1 4 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveFiveOver₁LowDens])
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveFiveOver₁Dens, cutFiveFiveOver₁Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 3 (-3) 4 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveFiveOver₁Dens, cutFiveFiveOver₁Const])
    · intro j _ _; simp [cutFiveFiveOver₁Ranks, cutFiveFiveOver₁Dens, cutFiveFiveOver₁Const]
    · intro j _ _; simp [cutFiveFiveOver₁Ranks, cutFiveFiveOver₁Dens, cutFiveFiveOver₁Const]
  · intro k; fin_cases k <;> simp [capD, hδ, cutFiveFiveOver₁LowRanks, cutFiveFiveOver₁Ranks,
      cutFiveFiveOver₁LowDens, cutFiveFiveOver₁Dens, cutFiveFiveOver₁Const] <;> linarith

/-- **Cell `(5,5)`, the high half's certificate 2.**

Block bounds `789 / 2500`, `543 / 10000`, `953 / 25000`, `871 / 20000`.
Valid on `4 / 625 < ω₀` and on
`871 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 4457 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4044000 + ϵ, 0.4317000 - ϵ]`. The cut is at `t = 41 / 500`. -/
theorem admitsPartition₄_cellFiveFive_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 871 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4457 / 10000 - 2 * ω₀ - slack)
    {y : Fin (5 + 5) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (953 / 5000) 5 5 (41 / 2500))
    (hcut : ∃ i : Fin (5 + 5), 5 ≤ (i : ℕ) ∧ 41 / 500 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutFiveFiveOver₂LowRanks cutFiveFiveOver₂Ranks (by decide) (by decide) (by decide) (by decide)
    cutFiveFiveOver₂LowDens cutFiveFiveOver₂Dens cutFiveFiveOver₂Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFiveFiveOver₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutFiveFiveOver₂Dens]
  · intro k; fin_cases k <;> norm_num [cutFiveFiveOver₂Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveFiveOver₂LowDens])
    · exact fun j ↦ by simp [cutFiveFiveOver₂LowRanks, cutFiveFiveOver₂LowDens]
    · exact fun j ↦ (prefixDensity_of_nat _ 1 5 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveFiveOver₂LowDens])
    · exact fun j ↦ (prefixDensity_of_nat _ 1 4 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveFiveOver₂LowDens])
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveFiveOver₂Dens, cutFiveFiveOver₂Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 (-1) 2 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveFiveOver₂Dens, cutFiveFiveOver₂Const])
    · intro j _ _; simp [cutFiveFiveOver₂Ranks, cutFiveFiveOver₂Dens, cutFiveFiveOver₂Const]
    · intro j _ _; simp [cutFiveFiveOver₂Ranks, cutFiveFiveOver₂Dens, cutFiveFiveOver₂Const]
  · intro k; fin_cases k <;> simp [capD, hδ, cutFiveFiveOver₂LowRanks, cutFiveFiveOver₂Ranks,
      cutFiveFiveOver₂LowDens, cutFiveFiveOver₂Dens, cutFiveFiveOver₂Const] <;> linarith

/-- **Cell `(5,5)`, the low half's certificate 2.**

Block bounds `1563 / 5000`, `263 / 5000`, `953 / 25000`, `871 / 20000`.
Valid on `4 / 625 < ω₀` and on
`1727 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 2237 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4014000 + ϵ, 0.4334000 - ϵ]`. The cut is at `t = 61 / 1000`. -/
theorem admitsPartition₄_cellFiveFive_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1727 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2237 / 5000 - 2 * ω₀ - slack)
    {y : Fin (5 + 5) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (953 / 5000) 5 5 (41 / 2500))
    (hcut : ∀ i : Fin (5 + 5), 5 ≤ (i : ℕ) → y i ≤ 61 / 1000) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutFiveFiveUnder₂LowRanks cutFiveFiveUnder₂Ranks (by decide) (by decide) (by decide) (by decide)
    cutFiveFiveUnder₂LowDens cutFiveFiveUnder₂Dens cutFiveFiveUnder₂Const ?_ ?_ ?_ ?_ ?_
    (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFiveFiveUnder₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutFiveFiveUnder₂Dens]
  · intro k; fin_cases k <;> norm_num [cutFiveFiveUnder₂Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveFiveUnder₂LowDens])
    all_goals exact fun j ↦ by simp [cutFiveFiveUnder₂LowRanks, cutFiveFiveUnder₂LowDens]
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 0 2 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveFiveUnder₂Dens, cutFiveFiveUnder₂Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 3 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveFiveUnder₂Dens, cutFiveFiveUnder₂Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 5 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveFiveUnder₂Dens, cutFiveFiveUnder₂Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 4 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveFiveUnder₂Dens, cutFiveFiveUnder₂Const])
  · intro k; fin_cases k <;> simp [capD, hδ, cutFiveFiveUnder₂LowRanks, cutFiveFiveUnder₂Ranks,
      cutFiveFiveUnder₂LowDens, cutFiveFiveUnder₂Dens, cutFiveFiveUnder₂Const] <;> linarith

/-- **Cell `(5,5)`, the high half's certificate 3.**

Block bounds `789 / 2500`, `81 / 1250`, `953 / 25000`, `871 / 20000`.
Valid on `4 / 625 < ω₀` and on
`871 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 272 / 625 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4044000 + ϵ, 0.4212000 - ϵ]`. The cut is at `t = 61 / 1000`. -/
theorem admitsPartition₄_cellFiveFive_over₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 871 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 272 / 625 - 2 * ω₀ - slack)
    {y : Fin (5 + 5) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (953 / 5000) 5 5 (41 / 2500))
    (hcut : ∃ i : Fin (5 + 5), 5 ≤ (i : ℕ) ∧ 61 / 1000 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutFiveFiveOver₃LowRanks cutFiveFiveOver₃Ranks (by decide) (by decide) (by decide) (by decide)
    cutFiveFiveOver₃LowDens cutFiveFiveOver₃Dens cutFiveFiveOver₃Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFiveFiveOver₃LowDens]
  · intro k; fin_cases k <;> norm_num [cutFiveFiveOver₃Dens]
  · intro k; fin_cases k <;> norm_num [cutFiveFiveOver₃Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveFiveOver₃LowDens])
    · exact fun j ↦ by simp [cutFiveFiveOver₃LowRanks, cutFiveFiveOver₃LowDens]
    · exact fun j ↦ (prefixDensity_of_nat _ 1 5 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveFiveOver₃LowDens])
    · exact fun j ↦ (prefixDensity_of_nat _ 1 4 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveFiveOver₃LowDens])
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveFiveOver₃Dens, cutFiveFiveOver₃Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 (-1) 2 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveFiveOver₃Dens, cutFiveFiveOver₃Const])
    · intro j _ _; simp [cutFiveFiveOver₃Ranks, cutFiveFiveOver₃Dens, cutFiveFiveOver₃Const]
    · intro j _ _; simp [cutFiveFiveOver₃Ranks, cutFiveFiveOver₃Dens, cutFiveFiveOver₃Const]
  · intro k; fin_cases k <;> simp [capD, hδ, cutFiveFiveOver₃LowRanks, cutFiveFiveOver₃Ranks,
      cutFiveFiveOver₃LowDens, cutFiveFiveOver₃Dens, cutFiveFiveOver₃Const] <;> linarith

/-- **Cell `(5,5)`, the high half's certificate 4.**

Block bounds `83 / 250`, `81 / 2500`, `953 / 25000`, `871 / 20000`.
Valid on `4 / 625 < ω₀` and on
`228 / 625 + 8ω₀ + ϵ ≤ γ ≤ 1169 / 2500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4208000 + ϵ, 0.4536000 - ϵ]`. The cut is at `t = 61 / 1000`. -/
theorem admitsPartition₄_cellFiveFive_over₄ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 228 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1169 / 2500 - 2 * ω₀ - slack)
    {y : Fin (5 + 5) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (953 / 5000) 5 5 (41 / 2500))
    (hcut : ∃ i : Fin (5 + 5), 5 ≤ (i : ℕ) ∧ 61 / 1000 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutFiveFiveOver₄LowRanks cutFiveFiveOver₄Ranks (by decide) (by decide) (by decide) (by decide)
    cutFiveFiveOver₄LowDens cutFiveFiveOver₄Dens cutFiveFiveOver₄Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFiveFiveOver₄LowDens]
  · intro k; fin_cases k <;> norm_num [cutFiveFiveOver₄Dens]
  · intro k; fin_cases k <;> norm_num [cutFiveFiveOver₄Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveFiveOver₄LowDens])
    · exact fun j ↦ by simp [cutFiveFiveOver₄LowRanks, cutFiveFiveOver₄LowDens]
    · exact fun j ↦ (prefixDensity_of_nat _ 1 5 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveFiveOver₄LowDens])
    · exact fun j ↦ (prefixDensity_of_nat _ 1 4 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveFiveOver₄LowDens])
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveFiveOver₄Dens, cutFiveFiveOver₄Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 (-1) 4 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveFiveOver₄Dens, cutFiveFiveOver₄Const])
    · intro j _ _; simp [cutFiveFiveOver₄Ranks, cutFiveFiveOver₄Dens, cutFiveFiveOver₄Const]
    · intro j _ _; simp [cutFiveFiveOver₄Ranks, cutFiveFiveOver₄Dens, cutFiveFiveOver₄Const]
  · intro k; fin_cases k <;> simp [capD, hδ, cutFiveFiveOver₄LowRanks, cutFiveFiveOver₄Ranks,
      cutFiveFiveOver₄LowDens, cutFiveFiveOver₄Dens, cutFiveFiveOver₄Const] <;> linarith

/-- **Cell `(5,5)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,5}, B_{1,5}, 5, 5, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate, at the thresholds `41 / 500, 61 / 1000` — one per `γ` region, the region
boundaries being the `γ` ceilings of the certificates that end them — then a `γ`
split inside each region on each half. No single threshold serves the whole `γ`-range:
at one fixed `ω₀` the binding threshold already varies with `γ`, so the missing dimension
is `γ` and not `ω₀`.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellFiveFive_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 5) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (953 / 5000) 5 5 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rw [hδ] at hγhi
  rcases le_or_gt γ (4293 / 10000 - 2 * ω₀ - slack) with hr1 | hr1
  · refine admitsPartition₄_of_cut (t := 41 / 500) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
    · exact admitsPartition₄_cellFiveFive_under₁ hωlo (by linarith) (by linarith) hy hcut
    · rcases le_or_gt γ (8371 / 20000 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellFiveFive_over₁ hωlo (by linarith) h1 hy hcut
      · exact admitsPartition₄_cellFiveFive_over₂ hωlo (by linarith) (by linarith) hy hcut
  · refine admitsPartition₄_of_cut (t := 61 / 1000) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
    · exact admitsPartition₄_cellFiveFive_under₂ hωlo (by linarith) (by linarith) hy hcut
    · rcases le_or_gt γ (272 / 625 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellFiveFive_over₃ hωlo (by linarith) h1 hy hcut
      · exact admitsPartition₄_cellFiveFive_over₄ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(5,5)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellFiveFive_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (5 + 5) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (953 / 5000) 5 5 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellFiveFive_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(5,5)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 5 = gap212Cap 5 = 953 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFiveFive_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 5) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 5) (gap212Params.B j' 5) 5 5
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hB : gap212Cap 5 = (953 / 5000 : ℝ) := by norm_num [gap212Cap]
  exact admitsPartition₄_cellFiveFive_band hωlo hωhi hγlo hγhi (hB ▸ hy)

/-! ## Cell `(5,6)` -/

/-- The first group's rank sets for cell `(5,6)`, the low half's certificate 1. -/
def cutFiveSixUnder₁LowRanks : Fin 4 → Finset (Fin 5) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFiveSixUnder₁LowRanks`. -/
noncomputable def cutFiveSixUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(5,6)`, the low half's certificate 1. -/
def cutFiveSixUnder₁Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 3, 5}, {1}, {4}, {2}]

/-- The slopes of `Gap212.cutFiveSixUnder₁Ranks`. -/
noncomputable def cutFiveSixUnder₁Dens : Fin 4 → ℝ := ![2 / 5, 1 / 2, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutFiveSixUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutFiveSixUnder₁Const : Fin 4 → ℝ := ![3 / 5, 0, 0, 0]

/-- The first group's rank sets for cell `(5,6)`, the high half's certificate 1. -/
def cutFiveSixOver₁LowRanks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1, 2, 3}, ∅, {4}, ∅]

/-- The prefix densities of `Gap212.cutFiveSixOver₁LowRanks`. -/
noncomputable def cutFiveSixOver₁LowDens : Fin 4 → ℝ := ![1, 0, 1 / 5, 0]

/-- The second group's rank sets for cell `(5,6)`, the high half's certificate 1. -/
def cutFiveSixOver₁Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1}, {2, 4}, ∅, {3, 5}]

/-- The slopes of `Gap212.cutFiveSixOver₁Ranks`. -/
noncomputable def cutFiveSixOver₁Dens : Fin 4 → ℝ := ![1, 1 / 2, 0, 2 / 5]

/-- The constants of `Gap212.cutFiveSixOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutFiveSixOver₁Const : Fin 4 → ℝ := ![0, -1 / 2, 0, -2 / 5]

/-- The first group's rank sets for cell `(5,6)`, the low half's certificate 2. -/
def cutFiveSixUnder₂LowRanks : Fin 4 → Finset (Fin 5) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFiveSixUnder₂LowRanks`. -/
noncomputable def cutFiveSixUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(5,6)`, the low half's certificate 2. -/
def cutFiveSixUnder₂Ranks : Fin 4 → Finset (Fin 6) :=
  ![{1, 2, 4, 5}, ∅, {3}, {0}]

/-- The slopes of `Gap212.cutFiveSixUnder₂Ranks`. -/
noncomputable def cutFiveSixUnder₂Dens : Fin 4 → ℝ := ![2 / 3, 0, 1 / 4, 0]

/-- The constants of `Gap212.cutFiveSixUnder₂Ranks`, nonnegative throughout. -/
noncomputable def cutFiveSixUnder₂Const : Fin 4 → ℝ := ![0, 0, 0, 1]

/-- The first group's rank sets for cell `(5,6)`, the high half's certificate 2. -/
def cutFiveSixOver₂LowRanks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1, 2}, ∅, {4}, {3}]

/-- The prefix densities of `Gap212.cutFiveSixOver₂LowRanks`. -/
noncomputable def cutFiveSixOver₂LowDens : Fin 4 → ℝ := ![1, 0, 1 / 5, 1 / 4]

/-- The second group's rank sets for cell `(5,6)`, the high half's certificate 2. -/
def cutFiveSixOver₂Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2, 3}, {4, 5}, ∅, ∅]

/-- The slopes of `Gap212.cutFiveSixOver₂Ranks`. -/
noncomputable def cutFiveSixOver₂Dens : Fin 4 → ℝ := ![1, 2 / 5, 0, 0]

/-- The constants of `Gap212.cutFiveSixOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutFiveSixOver₂Const : Fin 4 → ℝ := ![0, -2 / 5, 0, 0]

/-- The first group's rank sets for cell `(5,6)`, the high half's certificate 3. -/
def cutFiveSixOver₃LowRanks : Fin 4 → Finset (Fin 5) :=
  ![{0, 1, 2}, ∅, {4}, {3}]

/-- The prefix densities of `Gap212.cutFiveSixOver₃LowRanks`. -/
noncomputable def cutFiveSixOver₃LowDens : Fin 4 → ℝ := ![1, 0, 1 / 5, 1 / 4]

/-- The second group's rank sets for cell `(5,6)`, the high half's certificate 3. -/
def cutFiveSixOver₃Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2, 3, 4}, {5}, ∅, ∅]

/-- The slopes of `Gap212.cutFiveSixOver₃Ranks`. -/
noncomputable def cutFiveSixOver₃Dens : Fin 4 → ℝ := ![1, 1 / 5, 0, 0]

/-- The constants of `Gap212.cutFiveSixOver₃Ranks`, nonpositive throughout. -/
noncomputable def cutFiveSixOver₃Const : Fin 4 → ℝ := ![0, -1 / 5, 0, 0]

/-- **Cell `(5,6)`, the low half's certificate 1.**

Block bounds `3883 / 12500`, `131 / 2000`, `901 / 25000`, `737 / 15000`.
Valid on `4 / 625 < ω₀` and on
`4293 / 12500 + 8ω₀ + ϵ ≤ γ ≤ 869 / 2000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3994400 + ϵ, 0.4205000 - ϵ]`. The cut is at `t = 69 / 1000`. -/
theorem admitsPartition₄_cellFiveSix_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 4293 / 12500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 869 / 2000 - 2 * ω₀ - slack)
    {y : Fin (5 + 6) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (983 / 5000) 5 6 (41 / 2500))
    (hcut : ∀ i : Fin (5 + 6), 5 ≤ (i : ℕ) → y i ≤ 69 / 1000) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutFiveSixUnder₁LowRanks cutFiveSixUnder₁Ranks (by decide) (by decide) (by decide) (by decide)
    cutFiveSixUnder₁LowDens cutFiveSixUnder₁Dens cutFiveSixUnder₁Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFiveSixUnder₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutFiveSixUnder₁Dens]
  · intro k; fin_cases k <;> norm_num [cutFiveSixUnder₁Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveSixUnder₁LowDens])
    all_goals exact fun j ↦ by simp [cutFiveSixUnder₁LowRanks, cutFiveSixUnder₁LowDens]
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 2 3 5 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveSixUnder₁Dens, cutFiveSixUnder₁Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 2 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveSixUnder₁Dens, cutFiveSixUnder₁Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 5 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveSixUnder₁Dens, cutFiveSixUnder₁Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 3 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveSixUnder₁Dens, cutFiveSixUnder₁Const])
  · intro k; fin_cases k <;> simp [capD, hδ, cutFiveSixUnder₁LowRanks, cutFiveSixUnder₁Ranks,
      cutFiveSixUnder₁LowDens, cutFiveSixUnder₁Dens, cutFiveSixUnder₁Const] <;> linarith

/-- **Cell `(5,6)`, the high half's certificate 1.**

Block bounds `763 / 2500`, `139 / 2500`, `953 / 25000`, `319 / 6250`.
Valid on `4 / 625 < ω₀` and on
`169 / 500 + 8ω₀ + ϵ ≤ γ ≤ 1111 / 2500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3940000 + ϵ, 0.4304000 - ϵ]`. The cut is at `t = 69 / 1000`. -/
theorem admitsPartition₄_cellFiveSix_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 169 / 500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1111 / 2500 - 2 * ω₀ - slack)
    {y : Fin (5 + 6) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (983 / 5000) 5 6 (41 / 2500))
    (hcut : ∃ i : Fin (5 + 6), 5 ≤ (i : ℕ) ∧ 69 / 1000 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutFiveSixOver₁LowRanks cutFiveSixOver₁Ranks (by decide) (by decide) (by decide) (by decide)
    cutFiveSixOver₁LowDens cutFiveSixOver₁Dens cutFiveSixOver₁Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFiveSixOver₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutFiveSixOver₁Dens]
  · intro k; fin_cases k <;> norm_num [cutFiveSixOver₁Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveSixOver₁LowDens])
    · exact fun j ↦ by simp [cutFiveSixOver₁LowRanks, cutFiveSixOver₁LowDens]
    · exact fun j ↦ (prefixDensity_of_nat _ 1 5 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveSixOver₁LowDens])
    · exact fun j ↦ by simp [cutFiveSixOver₁LowRanks, cutFiveSixOver₁LowDens]
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveSixOver₁Dens, cutFiveSixOver₁Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 (-1) 2 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveSixOver₁Dens, cutFiveSixOver₁Const])
    · intro j _ _; simp [cutFiveSixOver₁Ranks, cutFiveSixOver₁Dens, cutFiveSixOver₁Const]
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 2 (-2) 5 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveSixOver₁Dens, cutFiveSixOver₁Const])
  · intro k; fin_cases k <;> simp [capD, hδ, cutFiveSixOver₁LowRanks, cutFiveSixOver₁Ranks,
      cutFiveSixOver₁LowDens, cutFiveSixOver₁Dens, cutFiveSixOver₁Const] <;> linarith

/-- **Cell `(5,6)`, the low half's certificate 2.**

Block bounds `193 / 600`, `0`, `819 / 20000`, `1 / 20`.
Valid on `4 / 625 < ω₀` and on
`5317 / 15000 + 8ω₀ + ϵ ≤ γ ≤ 1 / 2 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4104667 + ϵ, 0.4860000 - ϵ]`. The cut is at `t = 1 / 20`. -/
theorem admitsPartition₄_cellFiveSix_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 5317 / 15000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1 / 2 - 2 * ω₀ - slack)
    {y : Fin (5 + 6) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (983 / 5000) 5 6 (41 / 2500))
    (hcut : ∀ i : Fin (5 + 6), 5 ≤ (i : ℕ) → y i ≤ 1 / 20) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutFiveSixUnder₂LowRanks cutFiveSixUnder₂Ranks (by decide) (by decide) (by decide) (by decide)
    cutFiveSixUnder₂LowDens cutFiveSixUnder₂Dens cutFiveSixUnder₂Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFiveSixUnder₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutFiveSixUnder₂Dens]
  · intro k; fin_cases k <;> norm_num [cutFiveSixUnder₂Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveSixUnder₂LowDens])
    all_goals exact fun j ↦ by simp [cutFiveSixUnder₂LowRanks, cutFiveSixUnder₂LowDens]
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 2 0 3 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveSixUnder₂Dens, cutFiveSixUnder₂Const])
    · intro j _ _; simp [cutFiveSixUnder₂Ranks, cutFiveSixUnder₂Dens, cutFiveSixUnder₂Const]
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 4 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveSixUnder₂Dens, cutFiveSixUnder₂Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 0 1 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveSixUnder₂Dens, cutFiveSixUnder₂Const])
  · intro k; fin_cases k <;> simp [capD, hδ, cutFiveSixUnder₂LowRanks, cutFiveSixUnder₂Ranks,
      cutFiveSixUnder₂LowDens, cutFiveSixUnder₂Dens, cutFiveSixUnder₂Const] <;> linarith

/-- **Cell `(5,6)`, the high half's certificate 2.**

Block bounds `201 / 625`, `733 / 12500`, `953 / 25000`, `871 / 20000`.
Valid on `4 / 625 < ω₀` and on
`443 / 1250 + 8ω₀ + ϵ ≤ γ ≤ 5517 / 12500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4104000 + ϵ, 0.4273600 - ϵ]`. The cut is at `t = 1 / 20`. -/
theorem admitsPartition₄_cellFiveSix_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 443 / 1250 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 5517 / 12500 - 2 * ω₀ - slack)
    {y : Fin (5 + 6) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (983 / 5000) 5 6 (41 / 2500))
    (hcut : ∃ i : Fin (5 + 6), 5 ≤ (i : ℕ) ∧ 1 / 20 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutFiveSixOver₂LowRanks cutFiveSixOver₂Ranks (by decide) (by decide) (by decide) (by decide)
    cutFiveSixOver₂LowDens cutFiveSixOver₂Dens cutFiveSixOver₂Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFiveSixOver₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutFiveSixOver₂Dens]
  · intro k; fin_cases k <;> norm_num [cutFiveSixOver₂Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveSixOver₂LowDens])
    · exact fun j ↦ by simp [cutFiveSixOver₂LowRanks, cutFiveSixOver₂LowDens]
    · exact fun j ↦ (prefixDensity_of_nat _ 1 5 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveSixOver₂LowDens])
    · exact fun j ↦ (prefixDensity_of_nat _ 1 4 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveSixOver₂LowDens])
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveSixOver₂Dens, cutFiveSixOver₂Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 2 (-2) 5 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveSixOver₂Dens, cutFiveSixOver₂Const])
    · intro j _ _; simp [cutFiveSixOver₂Ranks, cutFiveSixOver₂Dens, cutFiveSixOver₂Const]
    · intro j _ _; simp [cutFiveSixOver₂Ranks, cutFiveSixOver₂Dens, cutFiveSixOver₂Const]
  · intro k; fin_cases k <;> simp [capD, hδ, cutFiveSixOver₂LowRanks, cutFiveSixOver₂Ranks,
      cutFiveSixOver₂LowDens, cutFiveSixOver₂Dens, cutFiveSixOver₂Const] <;> linarith

/-- **Cell `(5,6)`, the high half's certificate 3.**

Block bounds `169 / 500`, `733 / 25000`, `953 / 25000`, `871 / 20000`.
Valid on `4 / 625 < ω₀` and on
`927 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 11767 / 25000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4268000 + ϵ, 0.4566800 - ϵ]`. The cut is at `t = 1 / 20`. -/
theorem admitsPartition₄_cellFiveSix_over₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 927 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 11767 / 25000 - 2 * ω₀ - slack)
    {y : Fin (5 + 6) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (983 / 5000) 5 6 (41 / 2500))
    (hcut : ∃ i : Fin (5 + 6), 5 ≤ (i : ℕ) ∧ 1 / 20 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutFiveSixOver₃LowRanks cutFiveSixOver₃Ranks (by decide) (by decide) (by decide) (by decide)
    cutFiveSixOver₃LowDens cutFiveSixOver₃Dens cutFiveSixOver₃Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutFiveSixOver₃LowDens]
  · intro k; fin_cases k <;> norm_num [cutFiveSixOver₃Dens]
  · intro k; fin_cases k <;> norm_num [cutFiveSixOver₃Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveSixOver₃LowDens])
    · exact fun j ↦ by simp [cutFiveSixOver₃LowRanks, cutFiveSixOver₃LowDens]
    · exact fun j ↦ (prefixDensity_of_nat _ 1 5 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveSixOver₃LowDens])
    · exact fun j ↦ (prefixDensity_of_nat _ 1 4 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutFiveSixOver₃LowDens])
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveSixOver₃Dens, cutFiveSixOver₃Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 (-1) 5 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutFiveSixOver₃Dens, cutFiveSixOver₃Const])
    · intro j _ _; simp [cutFiveSixOver₃Ranks, cutFiveSixOver₃Dens, cutFiveSixOver₃Const]
    · intro j _ _; simp [cutFiveSixOver₃Ranks, cutFiveSixOver₃Dens, cutFiveSixOver₃Const]
  · intro k; fin_cases k <;> simp [capD, hδ, cutFiveSixOver₃LowRanks, cutFiveSixOver₃Ranks,
      cutFiveSixOver₃LowDens, cutFiveSixOver₃Dens, cutFiveSixOver₃Const] <;> linarith

/-- **Cell `(5,6)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,5}, B_{1,6}, 5, 6, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate, at the thresholds `1 / 20, 69 / 1000` — one per `γ` region, the region
boundaries being the `γ` ceilings of the certificates that end them — then a `γ`
split inside each region on each half. No single threshold serves the whole `γ`-range:
at one fixed `ω₀` the binding threshold already varies with `γ`, so the missing dimension
is `γ` and not `ω₀`.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellFiveSix_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 6) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (983 / 5000) 5 6 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rw [hδ] at hγhi
  rcases le_or_gt γ (869 / 2000 - 2 * ω₀ - slack) with hr1 | hr1
  · refine admitsPartition₄_of_cut (t := 69 / 1000) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
    · exact admitsPartition₄_cellFiveSix_under₁ hωlo (by linarith) (by linarith) hy hcut
    · exact admitsPartition₄_cellFiveSix_over₁ hωlo (by linarith) (by linarith) hy hcut
  · refine admitsPartition₄_of_cut (t := 1 / 20) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
    · exact admitsPartition₄_cellFiveSix_under₂ hωlo (by linarith) (by linarith) hy hcut
    · rcases le_or_gt γ (5517 / 12500 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellFiveSix_over₂ hωlo (by linarith) h1 hy hcut
      · exact admitsPartition₄_cellFiveSix_over₃ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(5,6)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellFiveSix_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (5 + 6) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (983 / 5000) 5 6 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellFiveSix_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(5,6)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 5 = gap212Cap 5 = 953 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFiveSix_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 6) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 5) (gap212Params.B j' 6) 5 6
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hB₁ : gap212Cap 5 = (953 / 5000 : ℝ) := by norm_num [gap212Cap]
  have hB₂ : gap212Cap 6 = (983 / 5000 : ℝ) := by norm_num [gap212Cap]
  exact admitsPartition₄_cellFiveSix_band hωlo hωhi hγlo hγhi (hB₁ ▸ hB₂ ▸ hy)

/-! ## Cell `(6,6)` -/

/-- The first group's rank sets for cell `(6,6)`, the low half's certificate 1. -/
def cutSixSixUnder₁LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSixSixUnder₁LowRanks`. -/
noncomputable def cutSixSixUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,6)`, the low half's certificate 1. -/
def cutSixSixUnder₁Ranks : Fin 4 → Finset (Fin 6) :=
  ![{1, 3, 5}, {0}, {4}, {2}]

/-- The slopes of `Gap212.cutSixSixUnder₁Ranks`. -/
noncomputable def cutSixSixUnder₁Dens : Fin 4 → ℝ := ![1 / 2, 0, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutSixSixUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutSixSixUnder₁Const : Fin 4 → ℝ := ![0, 1, 0, 0]

/-- The first group's rank sets for cell `(6,6)`, the low half's certificate 2. -/
def cutSixSixUnder₂LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSixSixUnder₂LowRanks`. -/
noncomputable def cutSixSixUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,6)`, the low half's certificate 2. -/
def cutSixSixUnder₂Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 3, 5}, {1}, {4}, {2}]

/-- The slopes of `Gap212.cutSixSixUnder₂Ranks`. -/
noncomputable def cutSixSixUnder₂Dens : Fin 4 → ℝ := ![2 / 5, 1 / 2, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutSixSixUnder₂Ranks`, nonnegative throughout. -/
noncomputable def cutSixSixUnder₂Const : Fin 4 → ℝ := ![3 / 5, 0, 0, 0]

/-- The first group's rank sets for cell `(6,6)`, the high half's certificate 1. -/
def cutSixSixOver₁LowRanks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2, 3}, {5}, {4}, ∅]

/-- The prefix densities of `Gap212.cutSixSixOver₁LowRanks`. -/
noncomputable def cutSixSixOver₁LowDens : Fin 4 → ℝ := ![1, 1 / 6, 1 / 5, 0]

/-- The second group's rank sets for cell `(6,6)`, the high half's certificate 1. -/
def cutSixSixOver₁Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1}, {2, 4}, ∅, {3, 5}]

/-- The slopes of `Gap212.cutSixSixOver₁Ranks`. -/
noncomputable def cutSixSixOver₁Dens : Fin 4 → ℝ := ![1, 1 / 2, 0, 2 / 5]

/-- The constants of `Gap212.cutSixSixOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutSixSixOver₁Const : Fin 4 → ℝ := ![0, -1 / 2, 0, -2 / 5]

/-- The first group's rank sets for cell `(6,6)`, the high half's certificate 2. -/
def cutSixSixOver₂LowRanks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2, 3, 4}, ∅, {5}, ∅]

/-- The prefix densities of `Gap212.cutSixSixOver₂LowRanks`. -/
noncomputable def cutSixSixOver₂LowDens : Fin 4 → ℝ := ![1, 0, 1 / 6, 0]

/-- The second group's rank sets for cell `(6,6)`, the high half's certificate 2. -/
def cutSixSixOver₂Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1}, {2, 4}, ∅, {3, 5}]

/-- The slopes of `Gap212.cutSixSixOver₂Ranks`. -/
noncomputable def cutSixSixOver₂Dens : Fin 4 → ℝ := ![1, 1 / 2, 0, 2 / 5]

/-- The constants of `Gap212.cutSixSixOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutSixSixOver₂Const : Fin 4 → ℝ := ![0, -1 / 2, 0, -2 / 5]

/-- The first group's rank sets for cell `(6,6)`, the low half's certificate 3. -/
def cutSixSixUnder₃LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSixSixUnder₃LowRanks`. -/
noncomputable def cutSixSixUnder₃LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,6)`, the low half's certificate 3. -/
def cutSixSixUnder₃Ranks : Fin 4 → Finset (Fin 6) :=
  ![{1, 3, 5}, {0}, {4}, {2}]

/-- The slopes of `Gap212.cutSixSixUnder₃Ranks`. -/
noncomputable def cutSixSixUnder₃Dens : Fin 4 → ℝ := ![1 / 2, 0, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutSixSixUnder₃Ranks`, nonnegative throughout. -/
noncomputable def cutSixSixUnder₃Const : Fin 4 → ℝ := ![0, 1, 0, 0]

/-- The first group's rank sets for cell `(6,6)`, the low half's certificate 4. -/
def cutSixSixUnder₄LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSixSixUnder₄LowRanks`. -/
noncomputable def cutSixSixUnder₄LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,6)`, the low half's certificate 4. -/
def cutSixSixUnder₄Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 4}, {5}, {3}, {2}]

/-- The slopes of `Gap212.cutSixSixUnder₄Ranks`. -/
noncomputable def cutSixSixUnder₄Dens : Fin 4 → ℝ := ![1 / 3, 1 / 6, 1 / 4, 1 / 3]

/-- The constants of `Gap212.cutSixSixUnder₄Ranks`, nonnegative throughout. -/
noncomputable def cutSixSixUnder₄Const : Fin 4 → ℝ := ![4 / 3, 0, 0, 0]

/-- The first group's rank sets for cell `(6,6)`, the high half's certificate 3. -/
def cutSixSixOver₃LowRanks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2, 3}, ∅, {5}, {4}]

/-- The prefix densities of `Gap212.cutSixSixOver₃LowRanks`. -/
noncomputable def cutSixSixOver₃LowDens : Fin 4 → ℝ := ![1, 0, 1 / 6, 1 / 5]

/-- The second group's rank sets for cell `(6,6)`, the high half's certificate 3. -/
def cutSixSixOver₃Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2, 3}, {4, 5}, ∅, ∅]

/-- The slopes of `Gap212.cutSixSixOver₃Ranks`. -/
noncomputable def cutSixSixOver₃Dens : Fin 4 → ℝ := ![1, 2 / 5, 0, 0]

/-- The constants of `Gap212.cutSixSixOver₃Ranks`, nonpositive throughout. -/
noncomputable def cutSixSixOver₃Const : Fin 4 → ℝ := ![0, -2 / 5, 0, 0]

/-- **Cell `(6,6)`, the low half's certificate 1.**

Block bounds `2949 / 10000`, `37 / 500`, `901 / 25000`, `737 / 15000`.
Valid on `4 / 625 < ω₀` and on
`3277 / 10000 + 8ω₀ + ϵ ≤ γ ≤ 213 / 500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3837000 + ϵ, 0.4120000 - ϵ]`. The cut is at `t = 37 / 500`. -/
theorem admitsPartition₄_cellSixSix_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3277 / 10000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 213 / 500 - 2 * ω₀ - slack)
    {y : Fin (6 + 6) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (983 / 5000) 6 6 (41 / 2500))
    (hcut : ∀ i : Fin (6 + 6), 6 ≤ (i : ℕ) → y i ≤ 37 / 500) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutSixSixUnder₁LowRanks cutSixSixUnder₁Ranks (by decide) (by decide) (by decide) (by decide)
    cutSixSixUnder₁LowDens cutSixSixUnder₁Dens cutSixSixUnder₁Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSixSixUnder₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutSixSixUnder₁Dens]
  · intro k; fin_cases k <;> norm_num [cutSixSixUnder₁Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutSixSixUnder₁LowDens])
    all_goals exact fun j ↦ by simp [cutSixSixUnder₁LowRanks, cutSixSixUnder₁LowDens]
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 2 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₁Dens, cutSixSixUnder₁Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 0 1 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₁Dens, cutSixSixUnder₁Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 5 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₁Dens, cutSixSixUnder₁Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 3 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₁Dens, cutSixSixUnder₁Const])
  · intro k; fin_cases k <;> simp [capD, hδ, cutSixSixUnder₁LowRanks, cutSixSixUnder₁Ranks,
      cutSixSixUnder₁LowDens, cutSixSixUnder₁Dens, cutSixSixUnder₁Const] <;> linarith

/-- **Cell `(6,6)`, the low half's certificate 2.**

Block bounds `7991 / 25000`, `131 / 2000`, `901 / 25000`, `737 / 15000`.
Valid on `4 / 625 < ω₀` and on
`8811 / 25000 + 8ω₀ + ϵ ≤ γ ≤ 869 / 2000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4084400 + ϵ, 0.4205000 - ϵ]`. The cut is at `t = 37 / 500`. -/
theorem admitsPartition₄_cellSixSix_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 8811 / 25000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 869 / 2000 - 2 * ω₀ - slack)
    {y : Fin (6 + 6) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (983 / 5000) 6 6 (41 / 2500))
    (hcut : ∀ i : Fin (6 + 6), 6 ≤ (i : ℕ) → y i ≤ 37 / 500) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutSixSixUnder₂LowRanks cutSixSixUnder₂Ranks (by decide) (by decide) (by decide) (by decide)
    cutSixSixUnder₂LowDens cutSixSixUnder₂Dens cutSixSixUnder₂Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSixSixUnder₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutSixSixUnder₂Dens]
  · intro k; fin_cases k <;> norm_num [cutSixSixUnder₂Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutSixSixUnder₂LowDens])
    all_goals exact fun j ↦ by simp [cutSixSixUnder₂LowRanks, cutSixSixUnder₂LowDens]
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 2 3 5 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₂Dens, cutSixSixUnder₂Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 2 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₂Dens, cutSixSixUnder₂Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 5 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₂Dens, cutSixSixUnder₂Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 3 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₂Dens, cutSixSixUnder₂Const])
  · intro k; fin_cases k <;> simp [capD, hδ, cutSixSixUnder₂LowRanks, cutSixSixUnder₂Ranks,
      cutSixSixUnder₂LowDens, cutSixSixUnder₂Dens, cutSixSixUnder₂Const] <;> linarith

/-- **Cell `(6,6)`, the high half's certificate 1.**

Block bounds `737 / 2500`, `161 / 1875`, `901 / 25000`, `613 / 12500`.
Valid on `4 / 625 < ω₀` and on
`819 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 1553 / 3750 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3836000 + ϵ, 0.4001333 - ϵ]`. The cut is at `t = 37 / 500`. -/
theorem admitsPartition₄_cellSixSix_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 819 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1553 / 3750 - 2 * ω₀ - slack)
    {y : Fin (6 + 6) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (983 / 5000) 6 6 (41 / 2500))
    (hcut : ∃ i : Fin (6 + 6), 6 ≤ (i : ℕ) ∧ 37 / 500 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutSixSixOver₁LowRanks cutSixSixOver₁Ranks (by decide) (by decide) (by decide) (by decide)
    cutSixSixOver₁LowDens cutSixSixOver₁Dens cutSixSixOver₁Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSixSixOver₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutSixSixOver₁Dens]
  · intro k; fin_cases k <;> norm_num [cutSixSixOver₁Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutSixSixOver₁LowDens])
    · exact fun j ↦ (prefixDensity_of_nat _ 1 6 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutSixSixOver₁LowDens])
    · exact fun j ↦ (prefixDensity_of_nat _ 1 5 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutSixSixOver₁LowDens])
    · exact fun j ↦ by simp [cutSixSixOver₁LowRanks, cutSixSixOver₁LowDens]
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixOver₁Dens, cutSixSixOver₁Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 (-1) 2 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixOver₁Dens, cutSixSixOver₁Const])
    · intro j _ _; simp [cutSixSixOver₁Ranks, cutSixSixOver₁Dens, cutSixSixOver₁Const]
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 2 (-2) 5 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixOver₁Dens, cutSixSixOver₁Const])
  · intro k; fin_cases k <;> simp [capD, hδ, cutSixSixOver₁LowRanks, cutSixSixOver₁Ranks,
      cutSixSixOver₁LowDens, cutSixSixOver₁Dens, cutSixSixOver₁Const] <;> linarith

/-- **Cell `(6,6)`, the high half's certificate 2.**

Block bounds `389 / 1250`, `531 / 10000`, `983 / 30000`, `613 / 12500`.
Valid on `4 / 625 < ω₀` and on
`43 / 125 + 8ω₀ + ϵ ≤ γ ≤ 4469 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4000000 + ϵ, 0.4329000 - ϵ]`. The cut is at `t = 37 / 500`. -/
theorem admitsPartition₄_cellSixSix_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 43 / 125 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4469 / 10000 - 2 * ω₀ - slack)
    {y : Fin (6 + 6) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (983 / 5000) 6 6 (41 / 2500))
    (hcut : ∃ i : Fin (6 + 6), 6 ≤ (i : ℕ) ∧ 37 / 500 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutSixSixOver₂LowRanks cutSixSixOver₂Ranks (by decide) (by decide) (by decide) (by decide)
    cutSixSixOver₂LowDens cutSixSixOver₂Dens cutSixSixOver₂Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSixSixOver₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutSixSixOver₂Dens]
  · intro k; fin_cases k <;> norm_num [cutSixSixOver₂Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutSixSixOver₂LowDens])
    · exact fun j ↦ by simp [cutSixSixOver₂LowRanks, cutSixSixOver₂LowDens]
    · exact fun j ↦ (prefixDensity_of_nat _ 1 6 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutSixSixOver₂LowDens])
    · exact fun j ↦ by simp [cutSixSixOver₂LowRanks, cutSixSixOver₂LowDens]
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixOver₂Dens, cutSixSixOver₂Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 (-1) 2 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixOver₂Dens, cutSixSixOver₂Const])
    · intro j _ _; simp [cutSixSixOver₂Ranks, cutSixSixOver₂Dens, cutSixSixOver₂Const]
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 2 (-2) 5 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixOver₂Dens, cutSixSixOver₂Const])
  · intro k; fin_cases k <;> simp [capD, hδ, cutSixSixOver₂LowRanks, cutSixSixOver₂Ranks,
      cutSixSixOver₂LowDens, cutSixSixOver₂Dens, cutSixSixOver₂Const] <;> linarith

/-- **Cell `(6,6)`, the low half's certificate 3.**

Block bounds `2949 / 10000`, `3 / 50`, `901 / 25000`, `737 / 15000`.
Valid on `4 / 625 < ω₀` and on
`3277 / 10000 + 8ω₀ + ϵ ≤ γ ≤ 11 / 25 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3837000 + ϵ, 0.4260000 - ϵ]`. The cut is at `t = 3 / 50`. -/
theorem admitsPartition₄_cellSixSix_under₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3277 / 10000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 11 / 25 - 2 * ω₀ - slack)
    {y : Fin (6 + 6) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (983 / 5000) 6 6 (41 / 2500))
    (hcut : ∀ i : Fin (6 + 6), 6 ≤ (i : ℕ) → y i ≤ 3 / 50) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutSixSixUnder₃LowRanks cutSixSixUnder₃Ranks (by decide) (by decide) (by decide) (by decide)
    cutSixSixUnder₃LowDens cutSixSixUnder₃Dens cutSixSixUnder₃Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSixSixUnder₃LowDens]
  · intro k; fin_cases k <;> norm_num [cutSixSixUnder₃Dens]
  · intro k; fin_cases k <;> norm_num [cutSixSixUnder₃Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutSixSixUnder₃LowDens])
    all_goals exact fun j ↦ by simp [cutSixSixUnder₃LowRanks, cutSixSixUnder₃LowDens]
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 2 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₃Dens, cutSixSixUnder₃Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 0 1 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₃Dens, cutSixSixUnder₃Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 5 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₃Dens, cutSixSixUnder₃Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 3 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₃Dens, cutSixSixUnder₃Const])
  · intro k; fin_cases k <;> simp [capD, hδ, cutSixSixUnder₃LowRanks, cutSixSixUnder₃Ranks,
      cutSixSixUnder₃LowDens, cutSixSixUnder₃Dens, cutSixSixUnder₃Const] <;> linarith

/-- **Cell `(6,6)`, the low half's certificate 4.**

Block bounds `101 / 300`, `983 / 30000`, `819 / 20000`, `737 / 15000`.
Valid on `4 / 625 < ω₀` and on
`2771 / 7500 + 8ω₀ + ϵ ≤ γ ≤ 14017 / 30000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4254667 + ϵ, 0.4532333 - ϵ]`. The cut is at `t = 3 / 50`. -/
theorem admitsPartition₄_cellSixSix_under₄ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 2771 / 7500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 14017 / 30000 - 2 * ω₀ - slack)
    {y : Fin (6 + 6) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (983 / 5000) 6 6 (41 / 2500))
    (hcut : ∀ i : Fin (6 + 6), 6 ≤ (i : ℕ) → y i ≤ 3 / 50) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutSixSixUnder₄LowRanks cutSixSixUnder₄Ranks (by decide) (by decide) (by decide) (by decide)
    cutSixSixUnder₄LowDens cutSixSixUnder₄Dens cutSixSixUnder₄Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSixSixUnder₄LowDens]
  · intro k; fin_cases k <;> norm_num [cutSixSixUnder₄Dens]
  · intro k; fin_cases k <;> norm_num [cutSixSixUnder₄Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutSixSixUnder₄LowDens])
    all_goals exact fun j ↦ by simp [cutSixSixUnder₄LowRanks, cutSixSixUnder₄LowDens]
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 4 3 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₄Dens, cutSixSixUnder₄Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 6 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₄Dens, cutSixSixUnder₄Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 4 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₄Dens, cutSixSixUnder₄Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 3 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixUnder₄Dens, cutSixSixUnder₄Const])
  · intro k; fin_cases k <;> simp [capD, hδ, cutSixSixUnder₄LowRanks, cutSixSixUnder₄Ranks,
      cutSixSixUnder₄LowDens, cutSixSixUnder₄Dens, cutSixSixUnder₄Const] <;> linarith

/-- **Cell `(6,6)`, the high half's certificate 3.**

Block bounds `819 / 2500`, `683 / 12500`, `983 / 30000`, `901 / 25000`.
Valid on `4 / 625 < ω₀` and on
`901 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 5567 / 12500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4164000 + ϵ, 0.4313600 - ϵ]`. The cut is at `t = 3 / 50`. -/
theorem admitsPartition₄_cellSixSix_over₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 901 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 5567 / 12500 - 2 * ω₀ - slack)
    {y : Fin (6 + 6) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (983 / 5000) 6 6 (41 / 2500))
    (hcut : ∃ i : Fin (6 + 6), 6 ≤ (i : ℕ) ∧ 3 / 50 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutSixSixOver₃LowRanks cutSixSixOver₃Ranks (by decide) (by decide) (by decide) (by decide)
    cutSixSixOver₃LowDens cutSixSixOver₃Dens cutSixSixOver₃Const ?_ ?_ ?_ ?_ ?_ (capD γ ω₀) ?_
  · intro k; fin_cases k <;> norm_num [cutSixSixOver₃LowDens]
  · intro k; fin_cases k <;> norm_num [cutSixSixOver₃Dens]
  · intro k; fin_cases k <;> norm_num [cutSixSixOver₃Const]
  · intro k; fin_cases k
    · exact fun j ↦ (prefixDensity_of_nat _ 1 1 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutSixSixOver₃LowDens])
    · exact fun j ↦ by simp [cutSixSixOver₃LowRanks, cutSixSixOver₃LowDens]
    · exact fun j ↦ (prefixDensity_of_nat _ 1 6 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutSixSixOver₃LowDens])
    · exact fun j ↦ (prefixDensity_of_nat _ 1 5 (by norm_num) (by decide) j)
        |>.trans_eq (by norm_num [cutSixSixOver₃LowDens])
  · intro k; fin_cases k
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 1 0 1 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixOver₃Dens, cutSixSixOver₃Const])
    · exact fun j h₁ h₂ ↦ (prefixAffine_of_int _ 2 (-2) 5 (by norm_num) (by decide) j h₁ h₂)
        |>.trans_eq (by norm_num [cutSixSixOver₃Dens, cutSixSixOver₃Const])
    · intro j _ _; simp [cutSixSixOver₃Ranks, cutSixSixOver₃Dens, cutSixSixOver₃Const]
    · intro j _ _; simp [cutSixSixOver₃Ranks, cutSixSixOver₃Dens, cutSixSixOver₃Const]
  · intro k; fin_cases k <;> simp [capD, hδ, cutSixSixOver₃LowRanks, cutSixSixOver₃Ranks,
      cutSixSixOver₃LowDens, cutSixSixOver₃Dens, cutSixSixOver₃Const] <;> linarith

/-- **Cell `(6,6)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,6}, B_{1,6}, 6, 6, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate, at the thresholds `3 / 50, 37 / 500` — one per `γ` region, the region
boundaries being the `γ` ceilings of the certificates that end them — then a `γ`
split inside each region on each half. No single threshold serves the whole `γ`-range:
at one fixed `ω₀` the binding threshold already varies with `γ`, so the missing dimension
is `γ` and not `ω₀`.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellSixSix_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 6) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (983 / 5000) 6 6 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rw [hδ] at hγhi
  rcases le_or_gt γ (869 / 2000 - 2 * ω₀ - slack) with hr1 | hr1
  · refine admitsPartition₄_of_cut (t := 37 / 500) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
    · rcases le_or_gt γ (213 / 500 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellSixSix_under₁ hωlo (by linarith) h1 hy hcut
      · exact admitsPartition₄_cellSixSix_under₂ hωlo (by linarith) (by linarith) hy hcut
    · rcases le_or_gt γ (1553 / 3750 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellSixSix_over₁ hωlo (by linarith) h1 hy hcut
      · exact admitsPartition₄_cellSixSix_over₂ hωlo (by linarith) (by linarith) hy hcut
  · refine admitsPartition₄_of_cut (t := 3 / 50) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
    · rcases le_or_gt γ (11 / 25 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellSixSix_under₃ hωlo (by linarith) h1 hy hcut
      · exact admitsPartition₄_cellSixSix_under₄ hωlo (by linarith) (by linarith) hy hcut
    · exact admitsPartition₄_cellSixSix_over₃ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(6,6)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellSixSix_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (6 + 6) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (983 / 5000) 6 6 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellSixSix_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(6,6)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 6 = gap212Cap 6 = 983 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellSixSix_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 6) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 6) (gap212Params.B j' 6) 6 6
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hB : gap212Cap 6 = (983 / 5000 : ℝ) := by norm_num [gap212Cap]
  exact admitsPartition₄_cellSixSix_band hωlo hωhi hγlo hγhi (hB ▸ hy)

/-- The hypotheses of the band theorems above are satisfiable: the chamber point `ω₀ = 7/1000`,
`γ = 2/5` and the constant profile `δ = 41/2500` meet all of them. -/
theorem cellsGamma_hypotheses_satisfiable :
    (4 / 625 < (7 / 1000 : ℝ) ∧ (2 / 5 - slack : ℝ) ≤ 2 / 5 ∧
        (2 / 5 : ℝ) ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (917 / 5000 : ℝ) (917 / 5000) 4 4 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (953 / 5000 : ℝ) (953 / 5000) 5 5 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (953 / 5000 : ℝ) (983 / 5000) 5 6 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (983 / 5000 : ℝ) (983 / 5000) 6 6 (41 / 2500) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine ⟨⟨by norm_num, by norm_num [hsv], by norm_num [hδ, hsv]⟩, ?_, ?_, ?_, ?_⟩ <;>
    exact ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩, by rw [Finset.sum_const, card_lowGroup]; norm_num,
      by rw [Finset.sum_const, card_highGroup]; norm_num⟩

end Gap212
