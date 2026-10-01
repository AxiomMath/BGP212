/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCutMid
public import Gap212.Packing.SortedCell

/-!
# Cell `(8,8)`, by two nested thresholds

Of the twenty cells the uncut rank reading covers at no level of the band, `(8,8)` is one of the
two, with `(3,3)`, for which a single threshold on the second group's largest coordinate is not
enough: two points of the level `ω₀ = 13/2000` have disjoint closing windows — the low reading's
supremum `A = 89/2500` at one sits strictly below the high reading's infimum `C = 872000007/2·10¹⁰`
at the other — so no threshold serves both, and no tiling of the band in `ω₀` alone can help either,
since both points lie at one level. The missing dimension is `γ`.

So the instrument here is two thresholds and three branches:
`Gap212.Packing.admitsPartition₄_of_cut` at `t₁ = 11/250`, and then again at `t₂ = 31/500` inside
its own high branch. The outer branches are the ordinary one-sided readings; the middle branch —
every coordinate of the second group at most `t₂`, some coordinate at least `t₁` — is served by
neither one-sided lemma, and `Gap212.Packing.admitsPartition₄_of_rank_certificate_cut_mid` is what
it needs: each bin names the threshold it pays its affine constant at, `t₂` where the constant is
nonnegative and `t₁` where it is nonpositive, with the four signs free to differ. That freedom is
the whole content of the middle branch, and it is why `(3,3)` in
`Gap212.Packing.SortedCellsMid` needed the same lemma.

No case analysis in `γ` or in `ω₀` beyond the three branches is needed: one pair of thresholds
serves the whole band and the whole chamber `γ`-range, with three certificates on the low branch,
three on the middle and two on the top.

`Gap212.Packing.admitsPartition₄_transpose_of` carries each off-diagonal cell to its transpose, so
with this cell the ordered quantifier of `Gap212.PackingCertificate` is covered too.
-/

@[expose] public section

namespace Gap212

open Finset Gap212.Packing


/-! ## Cell `(8,8)` -/

/-- The first group's rank sets for cell `(8,8)`, the bottom branch's certificate 1. -/
def cutEightEightUnder₁LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutEightEightUnder₁LowRanks`. -/
noncomputable def cutEightEightUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,8)`, the bottom branch's certificate 1. -/
def cutEightEightUnder₁Ranks : Fin 4 → Finset (Fin 8) :=
  ![{1, 4, 6}, {2, 5, 7}, {3}, {0}]

/-- The slopes of `Gap212.cutEightEightUnder₁Ranks`. -/
noncomputable def cutEightEightUnder₁Dens : Fin 4 → ℝ := ![2 / 5, 3 / 8, 1 / 4, 0]

/-- The constants of `Gap212.cutEightEightUnder₁Ranks`, nonnegative. -/
noncomputable def cutEightEightUnder₁Const : Fin 4 → ℝ := ![1 / 5, 0, 0, 1]

/-- The first group's rank sets for cell `(8,8)`, the bottom branch's certificate 2. -/
def cutEightEightUnder₂LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutEightEightUnder₂LowRanks`. -/
noncomputable def cutEightEightUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,8)`, the bottom branch's certificate 2. -/
def cutEightEightUnder₂Ranks : Fin 4 → Finset (Fin 8) :=
  ![{1, 3, 5, 7}, {2, 6}, {4}, {0}]

/-- The slopes of `Gap212.cutEightEightUnder₂Ranks`. -/
noncomputable def cutEightEightUnder₂Dens : Fin 4 → ℝ := ![1 / 2, 1 / 3, 1 / 5, 0]

/-- The constants of `Gap212.cutEightEightUnder₂Ranks`, nonnegative. -/
noncomputable def cutEightEightUnder₂Const : Fin 4 → ℝ := ![0, 0, 0, 1]

/-- The first group's rank sets for cell `(8,8)`, the bottom branch's certificate 3. -/
def cutEightEightUnder₃LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutEightEightUnder₃LowRanks`. -/
noncomputable def cutEightEightUnder₃LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,8)`, the bottom branch's certificate 3. -/
def cutEightEightUnder₃Ranks : Fin 4 → Finset (Fin 8) :=
  ![{1, 3, 4, 6, 7}, {2}, {5}, {0}]

/-- The slopes of `Gap212.cutEightEightUnder₃Ranks`. -/
noncomputable def cutEightEightUnder₃Dens : Fin 4 → ℝ := ![5 / 8, 1 / 3, 1 / 6, 0]

/-- The constants of `Gap212.cutEightEightUnder₃Ranks`, nonnegative. -/
noncomputable def cutEightEightUnder₃Const : Fin 4 → ℝ := ![0, 0, 0, 1]

/-- The first group's rank sets for cell `(8,8)`, the middle branch's certificate 1. -/
def cutEightEightMid₁LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutEightEightMid₁LowRanks`. -/
noncomputable def cutEightEightMid₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,8)`, the middle branch's certificate 1. -/
def cutEightEightMid₁Ranks : Fin 4 → Finset (Fin 8) :=
  ![{1, 3, 5}, {0, 7}, {2}, {4, 6}]

/-- The slopes of `Gap212.cutEightEightMid₁Ranks`. -/
noncomputable def cutEightEightMid₁Dens : Fin 4 → ℝ := ![1 / 2, 1 / 7, 1 / 2, 1 / 3]

/-- The constants of `Gap212.cutEightEightMid₁Ranks`, of either sign —
which is exactly what the middle branch buys. -/
noncomputable def cutEightEightMid₁Const : Fin 4 → ℝ := ![0, 6 / 7, -1 / 2, -1 / 3]

/-- The threshold each bin of `Gap212.cutEightEightMid₁Ranks` pays its constant at: the
upper one `31 / 500` where the constant is nonnegative, the lower one `11 / 250` where it is
nonpositive. -/
noncomputable def cutEightEightMid₁Pay : Fin 4 → ℝ := ![31 / 500, 31 / 500, 11 / 250, 11 / 250]

/-- The first group's rank sets for cell `(8,8)`, the middle branch's certificate 2. -/
def cutEightEightMid₂LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutEightEightMid₂LowRanks`. -/
noncomputable def cutEightEightMid₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,8)`, the middle branch's certificate 2. -/
def cutEightEightMid₂Ranks : Fin 4 → Finset (Fin 8) :=
  ![{1, 3, 5, 7}, {0}, {2}, {4, 6}]

/-- The slopes of `Gap212.cutEightEightMid₂Ranks`. -/
noncomputable def cutEightEightMid₂Dens : Fin 4 → ℝ := ![1 / 2, 0, 1 / 2, 1 / 3]

/-- The constants of `Gap212.cutEightEightMid₂Ranks`, of either sign —
which is exactly what the middle branch buys. -/
noncomputable def cutEightEightMid₂Const : Fin 4 → ℝ := ![0, 1, -1 / 2, -1 / 3]

/-- The threshold each bin of `Gap212.cutEightEightMid₂Ranks` pays its constant at: the
upper one `31 / 500` where the constant is nonnegative, the lower one `11 / 250` where it is
nonpositive. -/
noncomputable def cutEightEightMid₂Pay : Fin 4 → ℝ := ![31 / 500, 31 / 500, 11 / 250, 11 / 250]

/-- The first group's rank sets for cell `(8,8)`, the middle branch's certificate 3. -/
def cutEightEightMid₃LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutEightEightMid₃LowRanks`. -/
noncomputable def cutEightEightMid₃LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,8)`, the middle branch's certificate 3. -/
def cutEightEightMid₃Ranks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1, 2}, {4, 7}, {5}, {3, 6}]

/-- The slopes of `Gap212.cutEightEightMid₃Ranks`. -/
noncomputable def cutEightEightMid₃Dens : Fin 4 → ℝ := ![1, 2 / 7, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutEightEightMid₃Ranks`, of either sign —
which is exactly what the middle branch buys. -/
noncomputable def cutEightEightMid₃Const : Fin 4 → ℝ := ![0, -2 / 7, -1 / 5, -1 / 3]

/-- The threshold each bin of `Gap212.cutEightEightMid₃Ranks` pays its constant at: the
upper one `31 / 500` where the constant is nonnegative, the lower one `11 / 250` where it is
nonpositive. -/
noncomputable def cutEightEightMid₃Pay : Fin 4 → ℝ := ![31 / 500, 11 / 250, 11 / 250, 11 / 250]

/-- The first group's rank sets for cell `(8,8)`, the top branch's certificate 1. -/
def cutEightEightOver₁LowRanks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1, 2, 3, 4, 5, 6}, {7}, ∅, ∅]

/-- The prefix densities of `Gap212.cutEightEightOver₁LowRanks`. -/
noncomputable def cutEightEightOver₁LowDens : Fin 4 → ℝ := ![1, 1 / 8, 0, 0]

/-- The second group's rank sets for cell `(8,8)`, the top branch's certificate 1. -/
def cutEightEightOver₁Ranks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1}, {3, 6}, {4, 7}, {2, 5}]

/-- The slopes of `Gap212.cutEightEightOver₁Ranks`. -/
noncomputable def cutEightEightOver₁Dens : Fin 4 → ℝ := ![1, 1 / 3, 2 / 7, 1 / 2]

/-- The constants of `Gap212.cutEightEightOver₁Ranks`, nonpositive. -/
noncomputable def cutEightEightOver₁Const : Fin 4 → ℝ := ![0, -1 / 3, -2 / 7, -1 / 2]

/-- The first group's rank sets for cell `(8,8)`, the top branch's certificate 2. -/
def cutEightEightOver₂LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutEightEightOver₂LowRanks`. -/
noncomputable def cutEightEightOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,8)`, the top branch's certificate 2. -/
def cutEightEightOver₂Ranks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1}, {3, 6}, {4, 7}, {2, 5}]

/-- The slopes of `Gap212.cutEightEightOver₂Ranks`. -/
noncomputable def cutEightEightOver₂Dens : Fin 4 → ℝ := ![1, 1 / 3, 2 / 7, 1 / 2]

/-- The constants of `Gap212.cutEightEightOver₂Ranks`, nonpositive. -/
noncomputable def cutEightEightOver₂Const : Fin 4 → ℝ := ![0, -1 / 3, -2 / 7, -1 / 2]

/-- **Cell `(8,8)`, the bottom branch's certificate 1.**

Block bounds `147 / 500`, `1563 / 20000`, `357 / 10000`, `11 / 250`.
Valid on `4 / 625 < ω₀` and on
`817 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 8437 / 20000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3828000 + ϵ, 0.4078500 - ϵ]`.
The branch is `y i ≤ 11 / 250` throughout the second group. -/
theorem admitsPartition₄_cellEightEight_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 817 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 8437 / 20000 - 2 * ω₀ - slack)
    {y : Fin (8 + 8) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (521 / 2500) 8 8 (41 / 2500))
    (hcut : ∀ i : Fin (8 + 8), 8 ≤ (i : ℕ) → y i ≤ 11 / 250) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutEightEightUnder₁LowRanks cutEightEightUnder₁Ranks ?_ ?_ ?_ ?_
    cutEightEightUnder₁LowDens cutEightEightUnder₁Dens cutEightEightUnder₁Const ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutEightEightUnder₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutEightEightUnder₁Dens]
  · intro k; fin_cases k <;> norm_num [cutEightEightUnder₁Const]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutEightEightUnder₁LowRanks, cutEightEightUnder₁LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutEightEightUnder₁LowRanks 0) 1 1
            (by norm_num) (by decide) j
    · exact fun j ↦ by simp [cutEightEightUnder₁LowRanks, cutEightEightUnder₁LowDens]
    · exact fun j ↦ by simp [cutEightEightUnder₁LowRanks, cutEightEightUnder₁LowDens]
    · exact fun j ↦ by simp [cutEightEightUnder₁LowRanks, cutEightEightUnder₁LowDens]
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightUnder₁Ranks 0)
        2 1 5 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightUnder₁Ranks, cutEightEightUnder₁Dens, cutEightEightUnder₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightUnder₁Ranks 1)
        3 0 8 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightUnder₁Ranks, cutEightEightUnder₁Dens, cutEightEightUnder₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightUnder₁Ranks 2)
        1 0 4 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightUnder₁Ranks, cutEightEightUnder₁Dens, cutEightEightUnder₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightUnder₁Ranks 3)
        0 1 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightUnder₁Ranks, cutEightEightUnder₁Dens, cutEightEightUnder₁Const] at h ⊢
      linarith
  · intro k
    fin_cases k <;>
      · simp [capD, hδ, cutEightEightUnder₁LowRanks, cutEightEightUnder₁Ranks,
          cutEightEightUnder₁LowDens, cutEightEightUnder₁Dens, cutEightEightUnder₁Const]
        all_goals linarith

/-- **Cell `(8,8)`, the bottom branch's certificate 2.**

Block bounds `1563 / 5000`, `439 / 7500`, `199 / 6250`, `11 / 250`.
Valid on `4 / 625 < ω₀` and on
`1727 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 3311 / 7500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4014000 + ϵ, 0.4274667 - ϵ]`.
The branch is `y i ≤ 11 / 250` throughout the second group. -/
theorem admitsPartition₄_cellEightEight_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1727 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 3311 / 7500 - 2 * ω₀ - slack)
    {y : Fin (8 + 8) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (521 / 2500) 8 8 (41 / 2500))
    (hcut : ∀ i : Fin (8 + 8), 8 ≤ (i : ℕ) → y i ≤ 11 / 250) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutEightEightUnder₂LowRanks cutEightEightUnder₂Ranks ?_ ?_ ?_ ?_
    cutEightEightUnder₂LowDens cutEightEightUnder₂Dens cutEightEightUnder₂Const ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutEightEightUnder₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutEightEightUnder₂Dens]
  · intro k; fin_cases k <;> norm_num [cutEightEightUnder₂Const]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutEightEightUnder₂LowRanks, cutEightEightUnder₂LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutEightEightUnder₂LowRanks 0) 1 1
            (by norm_num) (by decide) j
    · exact fun j ↦ by simp [cutEightEightUnder₂LowRanks, cutEightEightUnder₂LowDens]
    · exact fun j ↦ by simp [cutEightEightUnder₂LowRanks, cutEightEightUnder₂LowDens]
    · exact fun j ↦ by simp [cutEightEightUnder₂LowRanks, cutEightEightUnder₂LowDens]
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightUnder₂Ranks 0)
        1 0 2 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightUnder₂Ranks, cutEightEightUnder₂Dens, cutEightEightUnder₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightUnder₂Ranks 1)
        1 0 3 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightUnder₂Ranks, cutEightEightUnder₂Dens, cutEightEightUnder₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightUnder₂Ranks 2)
        1 0 5 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightUnder₂Ranks, cutEightEightUnder₂Dens, cutEightEightUnder₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightUnder₂Ranks 3)
        0 1 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightUnder₂Ranks, cutEightEightUnder₂Dens, cutEightEightUnder₂Const] at h ⊢
      linarith
  · intro k
    fin_cases k <;>
      · simp [capD, hδ, cutEightEightUnder₂LowRanks, cutEightEightUnder₂Ranks,
          cutEightEightUnder₂LowDens, cutEightEightUnder₂Dens, cutEightEightUnder₂Const]
        all_goals linarith

/-- **Cell `(8,8)`, the bottom branch's certificate 3.**

Block bounds `6773 / 20000`, `79 / 1875`, `439 / 15000`, `11 / 250`.
Valid on `4 / 625 < ω₀` and on
`7429 / 20000 + 8ω₀ + ϵ ≤ γ ≤ 1717 / 3750 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4274500 + ϵ, 0.4438667 - ϵ]`.
The branch is `y i ≤ 11 / 250` throughout the second group. -/
theorem admitsPartition₄_cellEightEight_under₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 7429 / 20000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1717 / 3750 - 2 * ω₀ - slack)
    {y : Fin (8 + 8) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (521 / 2500) 8 8 (41 / 2500))
    (hcut : ∀ i : Fin (8 + 8), 8 ≤ (i : ℕ) → y i ≤ 11 / 250) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutEightEightUnder₃LowRanks cutEightEightUnder₃Ranks ?_ ?_ ?_ ?_
    cutEightEightUnder₃LowDens cutEightEightUnder₃Dens cutEightEightUnder₃Const ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutEightEightUnder₃LowDens]
  · intro k; fin_cases k <;> norm_num [cutEightEightUnder₃Dens]
  · intro k; fin_cases k <;> norm_num [cutEightEightUnder₃Const]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutEightEightUnder₃LowRanks, cutEightEightUnder₃LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutEightEightUnder₃LowRanks 0) 1 1
            (by norm_num) (by decide) j
    · exact fun j ↦ by simp [cutEightEightUnder₃LowRanks, cutEightEightUnder₃LowDens]
    · exact fun j ↦ by simp [cutEightEightUnder₃LowRanks, cutEightEightUnder₃LowDens]
    · exact fun j ↦ by simp [cutEightEightUnder₃LowRanks, cutEightEightUnder₃LowDens]
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightUnder₃Ranks 0)
        5 0 8 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightUnder₃Ranks, cutEightEightUnder₃Dens, cutEightEightUnder₃Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightUnder₃Ranks 1)
        1 0 3 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightUnder₃Ranks, cutEightEightUnder₃Dens, cutEightEightUnder₃Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightUnder₃Ranks 2)
        1 0 6 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightUnder₃Ranks, cutEightEightUnder₃Dens, cutEightEightUnder₃Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightUnder₃Ranks 3)
        0 1 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightUnder₃Ranks, cutEightEightUnder₃Dens, cutEightEightUnder₃Const] at h ⊢
      linarith
  · intro k
    fin_cases k <;>
      · simp [capD, hδ, cutEightEightUnder₃LowRanks, cutEightEightUnder₃Ranks,
          cutEightEightUnder₃LowDens, cutEightEightUnder₃Dens, cutEightEightUnder₃Const]
        all_goals linarith

/-- **Cell `(8,8)`, the middle branch's certificate 1.**

Block bounds `1481 / 5000`, `1451 / 17500`, `103 / 2500`, `37 / 750`.
Valid on `4 / 625 < ω₀` and on
`329 / 1000 + 8ω₀ + ϵ ≤ γ ≤ 7299 / 17500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3850000 + ϵ, 0.4030857 - ϵ]`.
The branch is `11 / 250 ≤ y (e₂ 0) ≤ 31 / 500`, and the bins pay their constants at
`Gap212.cutEightEightMid₁Pay`. -/
theorem admitsPartition₄_cellEightEight_mid₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 329 / 1000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 7299 / 17500 - 2 * ω₀ - slack)
    {y : Fin (8 + 8) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (521 / 2500) 8 8 (41 / 2500))
    (hcutle : ∀ i : Fin (8 + 8), 8 ≤ (i : ℕ) → y i ≤ 31 / 500)
    (hcutge : ∃ i : Fin (8 + 8), 8 ≤ (i : ℕ) ∧ 11 / 250 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_mid (by norm_num) hy (by norm_num) hcutle hcutge
    cutEightEightMid₁LowRanks cutEightEightMid₁Ranks ?_ ?_ ?_ ?_
    cutEightEightMid₁LowDens cutEightEightMid₁Dens cutEightEightMid₁Const
    cutEightEightMid₁Pay ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutEightEightMid₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutEightEightMid₁Dens]
  · intro k; fin_cases k <;> norm_num [cutEightEightMid₁Const, cutEightEightMid₁Pay]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutEightEightMid₁LowRanks, cutEightEightMid₁LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutEightEightMid₁LowRanks 0) 1 1
            (by norm_num) (by decide) j
    · exact fun j ↦ by simp [cutEightEightMid₁LowRanks, cutEightEightMid₁LowDens]
    · exact fun j ↦ by simp [cutEightEightMid₁LowRanks, cutEightEightMid₁LowDens]
    · exact fun j ↦ by simp [cutEightEightMid₁LowRanks, cutEightEightMid₁LowDens]
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightMid₁Ranks 0)
        1 0 2 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightMid₁Ranks, cutEightEightMid₁Dens, cutEightEightMid₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightMid₁Ranks 1)
        1 6 7 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightMid₁Ranks, cutEightEightMid₁Dens, cutEightEightMid₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightMid₁Ranks 2)
        1 (-1) 2 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightMid₁Ranks, cutEightEightMid₁Dens, cutEightEightMid₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightMid₁Ranks 3)
        1 (-1) 3 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightMid₁Ranks, cutEightEightMid₁Dens, cutEightEightMid₁Const] at h ⊢
      linarith
  · intro k
    fin_cases k <;>
      · simp [capD, hδ, cutEightEightMid₁LowRanks, cutEightEightMid₁Ranks,
          cutEightEightMid₁LowDens, cutEightEightMid₁Dens, cutEightEightMid₁Const,
          cutEightEightMid₁Pay]
        all_goals linarith

/-- **Cell `(8,8)`, the middle branch's certificate 2.**

Block bounds `1563 / 5000`, `31 / 500`, `103 / 2500`, `37 / 750`.
Valid on `4 / 625 < ω₀` and on
`1727 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 219 / 500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4014000 + ϵ, 0.4240000 - ϵ]`.
The branch is `11 / 250 ≤ y (e₂ 0) ≤ 31 / 500`, and the bins pay their constants at
`Gap212.cutEightEightMid₂Pay`. -/
theorem admitsPartition₄_cellEightEight_mid₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1727 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 219 / 500 - 2 * ω₀ - slack)
    {y : Fin (8 + 8) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (521 / 2500) 8 8 (41 / 2500))
    (hcutle : ∀ i : Fin (8 + 8), 8 ≤ (i : ℕ) → y i ≤ 31 / 500)
    (hcutge : ∃ i : Fin (8 + 8), 8 ≤ (i : ℕ) ∧ 11 / 250 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_mid (by norm_num) hy (by norm_num) hcutle hcutge
    cutEightEightMid₂LowRanks cutEightEightMid₂Ranks ?_ ?_ ?_ ?_
    cutEightEightMid₂LowDens cutEightEightMid₂Dens cutEightEightMid₂Const
    cutEightEightMid₂Pay ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutEightEightMid₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutEightEightMid₂Dens]
  · intro k; fin_cases k <;> norm_num [cutEightEightMid₂Const, cutEightEightMid₂Pay]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutEightEightMid₂LowRanks, cutEightEightMid₂LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutEightEightMid₂LowRanks 0) 1 1
            (by norm_num) (by decide) j
    · exact fun j ↦ by simp [cutEightEightMid₂LowRanks, cutEightEightMid₂LowDens]
    · exact fun j ↦ by simp [cutEightEightMid₂LowRanks, cutEightEightMid₂LowDens]
    · exact fun j ↦ by simp [cutEightEightMid₂LowRanks, cutEightEightMid₂LowDens]
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightMid₂Ranks 0)
        1 0 2 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightMid₂Ranks, cutEightEightMid₂Dens, cutEightEightMid₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightMid₂Ranks 1)
        0 1 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightMid₂Ranks, cutEightEightMid₂Dens, cutEightEightMid₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightMid₂Ranks 2)
        1 (-1) 2 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightMid₂Ranks, cutEightEightMid₂Dens, cutEightEightMid₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightMid₂Ranks 3)
        1 (-1) 3 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightMid₂Ranks, cutEightEightMid₂Dens, cutEightEightMid₂Const] at h ⊢
      linarith
  · intro k
    fin_cases k <;>
      · simp [capD, hδ, cutEightEightMid₂LowRanks, cutEightEightMid₂Ranks,
          cutEightEightMid₂LowDens, cutEightEightMid₂Dens, cutEightEightMid₂Const,
          cutEightEightMid₂Pay]
        all_goals linarith

/-- **Cell `(8,8)`, the middle branch's certificate 3.**

Block bounds `837 / 2500`, `411 / 8750`, `329 / 12500`, `37 / 750`.
Valid on `4 / 625 < ω₀` and on
`919 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 1982 / 4375 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4236000 + ϵ, 0.4390286 - ϵ]`.
The branch is `11 / 250 ≤ y (e₂ 0) ≤ 31 / 500`, and the bins pay their constants at
`Gap212.cutEightEightMid₃Pay`. -/
theorem admitsPartition₄_cellEightEight_mid₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 919 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1982 / 4375 - 2 * ω₀ - slack)
    {y : Fin (8 + 8) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (521 / 2500) 8 8 (41 / 2500))
    (hcutle : ∀ i : Fin (8 + 8), 8 ≤ (i : ℕ) → y i ≤ 31 / 500)
    (hcutge : ∃ i : Fin (8 + 8), 8 ≤ (i : ℕ) ∧ 11 / 250 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_mid (by norm_num) hy (by norm_num) hcutle hcutge
    cutEightEightMid₃LowRanks cutEightEightMid₃Ranks ?_ ?_ ?_ ?_
    cutEightEightMid₃LowDens cutEightEightMid₃Dens cutEightEightMid₃Const
    cutEightEightMid₃Pay ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutEightEightMid₃LowDens]
  · intro k; fin_cases k <;> norm_num [cutEightEightMid₃Dens]
  · intro k; fin_cases k <;> norm_num [cutEightEightMid₃Const, cutEightEightMid₃Pay]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutEightEightMid₃LowRanks, cutEightEightMid₃LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutEightEightMid₃LowRanks 0) 1 1
            (by norm_num) (by decide) j
    · exact fun j ↦ by simp [cutEightEightMid₃LowRanks, cutEightEightMid₃LowDens]
    · exact fun j ↦ by simp [cutEightEightMid₃LowRanks, cutEightEightMid₃LowDens]
    · exact fun j ↦ by simp [cutEightEightMid₃LowRanks, cutEightEightMid₃LowDens]
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightMid₃Ranks 0)
        1 0 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightMid₃Ranks, cutEightEightMid₃Dens, cutEightEightMid₃Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightMid₃Ranks 1)
        2 (-2) 7 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightMid₃Ranks, cutEightEightMid₃Dens, cutEightEightMid₃Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightMid₃Ranks 2)
        1 (-1) 5 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightMid₃Ranks, cutEightEightMid₃Dens, cutEightEightMid₃Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightMid₃Ranks 3)
        1 (-1) 3 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightMid₃Ranks, cutEightEightMid₃Dens, cutEightEightMid₃Const] at h ⊢
      linarith
  · intro k
    fin_cases k <;>
      · simp [capD, hδ, cutEightEightMid₃LowRanks, cutEightEightMid₃Ranks,
          cutEightEightMid₃LowDens, cutEightEightMid₃Dens, cutEightEightMid₃Const,
          cutEightEightMid₃Pay]
        all_goals linarith

/-- **Cell `(8,8)`, the top branch's certificate 1.**

Block bounds `151 / 500`, `4163 / 60000`, `183 / 4375`, `243 / 5000`.
Valid on `4 / 625 < ω₀` and on
`837 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 25837 / 60000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3908000 + ϵ, 0.4166167 - ϵ]`.
The branch is `31 / 500 ≤ y i` for some `i` of the second group. -/
theorem admitsPartition₄_cellEightEight_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 837 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 25837 / 60000 - 2 * ω₀ - slack)
    {y : Fin (8 + 8) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (521 / 2500) 8 8 (41 / 2500))
    (hcut : ∃ i : Fin (8 + 8), 8 ≤ (i : ℕ) ∧ 31 / 500 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutEightEightOver₁LowRanks cutEightEightOver₁Ranks ?_ ?_ ?_ ?_
    cutEightEightOver₁LowDens cutEightEightOver₁Dens cutEightEightOver₁Const ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutEightEightOver₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutEightEightOver₁Dens]
  · intro k; fin_cases k <;> norm_num [cutEightEightOver₁Const]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutEightEightOver₁LowRanks, cutEightEightOver₁LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutEightEightOver₁LowRanks 0) 1 1
            (by norm_num) (by decide) j
    · exact fun j ↦ by
        simpa [cutEightEightOver₁LowRanks, cutEightEightOver₁LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutEightEightOver₁LowRanks 1) 1 8
            (by norm_num) (by decide) j
    · exact fun j ↦ by simp [cutEightEightOver₁LowRanks, cutEightEightOver₁LowDens]
    · exact fun j ↦ by simp [cutEightEightOver₁LowRanks, cutEightEightOver₁LowDens]
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightOver₁Ranks 0)
        1 0 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightOver₁Ranks, cutEightEightOver₁Dens, cutEightEightOver₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightOver₁Ranks 1)
        1 (-1) 3 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightOver₁Ranks, cutEightEightOver₁Dens, cutEightEightOver₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightOver₁Ranks 2)
        2 (-2) 7 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightOver₁Ranks, cutEightEightOver₁Dens, cutEightEightOver₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightOver₁Ranks 3)
        1 (-1) 2 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightOver₁Ranks, cutEightEightOver₁Dens, cutEightEightOver₁Const] at h ⊢
      linarith
  · intro k
    fin_cases k <;>
      · simp [capD, hδ, cutEightEightOver₁LowRanks, cutEightEightOver₁Ranks,
          cutEightEightOver₁LowDens, cutEightEightOver₁Dens, cutEightEightOver₁Const]
        all_goals linarith

/-- **Cell `(8,8)`, the top branch's certificate 2.**

Block bounds `199 / 625`, `13 / 300`, `183 / 4375`, `243 / 5000`.
Valid on `4 / 625 < ω₀` and on
`439 / 1250 + 8ω₀ + ϵ ≤ γ ≤ 137 / 300 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4072000 + ϵ, 0.4426667 - ϵ]`.
The branch is `31 / 500 ≤ y i` for some `i` of the second group. -/
theorem admitsPartition₄_cellEightEight_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 439 / 1250 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 137 / 300 - 2 * ω₀ - slack)
    {y : Fin (8 + 8) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (521 / 2500) 8 8 (41 / 2500))
    (hcut : ∃ i : Fin (8 + 8), 8 ≤ (i : ℕ) ∧ 31 / 500 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutEightEightOver₂LowRanks cutEightEightOver₂Ranks ?_ ?_ ?_ ?_
    cutEightEightOver₂LowDens cutEightEightOver₂Dens cutEightEightOver₂Const ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutEightEightOver₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutEightEightOver₂Dens]
  · intro k; fin_cases k <;> norm_num [cutEightEightOver₂Const]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutEightEightOver₂LowRanks, cutEightEightOver₂LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutEightEightOver₂LowRanks 0) 1 1
            (by norm_num) (by decide) j
    · exact fun j ↦ by simp [cutEightEightOver₂LowRanks, cutEightEightOver₂LowDens]
    · exact fun j ↦ by simp [cutEightEightOver₂LowRanks, cutEightEightOver₂LowDens]
    · exact fun j ↦ by simp [cutEightEightOver₂LowRanks, cutEightEightOver₂LowDens]
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightOver₂Ranks 0)
        1 0 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightOver₂Ranks, cutEightEightOver₂Dens, cutEightEightOver₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightOver₂Ranks 1)
        1 (-1) 3 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightOver₂Ranks, cutEightEightOver₂Dens, cutEightEightOver₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightOver₂Ranks 2)
        2 (-2) 7 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightOver₂Ranks, cutEightEightOver₂Dens, cutEightEightOver₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutEightEightOver₂Ranks 3)
        1 (-1) 2 (by norm_num) (by decide) j hj1 hj2
      simp [cutEightEightOver₂Ranks, cutEightEightOver₂Dens, cutEightEightOver₂Const] at h ⊢
      linarith
  · intro k
    fin_cases k <;>
      · simp [capD, hδ, cutEightEightOver₂LowRanks, cutEightEightOver₂Ranks,
          cutEightEightOver₂LowDens, cutEightEightOver₂Dens, cutEightEightOver₂Const]
        all_goals linarith

/-- **Cell `(8,8)` is discharged on the whole band, by a two-threshold cut.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,8}, B_{1,8}, 8, 8, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` twice over — at `t₁ = 11 / 250`
and then, inside its high branch, at `t₂ = 31 / 500` — so the second group's largest
coordinate falls in one of three branches, and the middle one carries *both* hypotheses.
That is what a single threshold cannot do here: the low reading's supremum `A` sits strictly
below the high reading's infimum `C` at this cell, so no one threshold closes it, and by the
argument in `Gap212.Packing.SortedCutMid` the middle branch is served by neither
one-sided lemma — it needs `Gap212.Packing.admitsPartition₄_of_rank_certificate_cut_mid`,
whose bins pay their affine constants at `t₂` or at `t₁` according to each constant's own
sign. -/
theorem admitsPartition₄_cellEightEight_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (8 + 8) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (521 / 2500) 8 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rw [hδ] at hγhi
  refine admitsPartition₄_of_cut (t := 11 / 250) (by norm_num) (fun hcut ↦ ?_) (fun hcutge ↦ ?_)
  · rcases le_or_gt γ (8437 / 20000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellEightEight_under₁ hωlo (by linarith) h1 hy hcut
    · rcases le_or_gt γ (3311 / 7500 - 2 * ω₀ - slack) with h2 | h2
      · exact admitsPartition₄_cellEightEight_under₂ hωlo (by linarith) h2 hy hcut
      · exact admitsPartition₄_cellEightEight_under₃ hωlo (by linarith) (by linarith) hy hcut
  · refine admitsPartition₄_of_cut (t := 31 / 500) (by norm_num) (fun hcutle ↦ ?_) (fun hcut ↦ ?_)
    · rcases le_or_gt γ (7299 / 17500 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellEightEight_mid₁ hωlo (by linarith) h1 hy hcutle hcutge
      · rcases le_or_gt γ (219 / 500 - 2 * ω₀ - slack) with h2 | h2
        · exact admitsPartition₄_cellEightEight_mid₂ hωlo (by linarith) h2 hy hcutle hcutge
        · exact admitsPartition₄_cellEightEight_mid₃ hωlo (by linarith) (by linarith) hy
            hcutle hcutge
    · rcases le_or_gt γ (25837 / 60000 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellEightEight_over₁ hωlo (by linarith) h1 hy hcut
      · exact admitsPartition₄_cellEightEight_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(8,8)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellEightEight_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (8 + 8) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (521 / 2500) 8 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellEightEight_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(8,8)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 8 = gap212Cap 8 = 521 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellEightEight_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (8 + 8) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 8) (gap212Params.B j' 8) 8 8
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hrow1 : gap212Params.B j 8 = gap212Cap 8 := rfl
  have hrow2 : gap212Params.B j' 8 = gap212Cap 8 := rfl
  have hB1 : gap212Cap 8 = (521 / 2500 : ℝ) := by unfold gap212Cap; norm_num
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rw [hrow1, hrow2, hB1, hδ] at hy
  exact admitsPartition₄_cellEightEight_band hωlo hωhi hγlo hγhi hy

/-- The hypotheses of the band theorems above are satisfiable: the chamber point `ω₀ = 7/1000`,
`γ = 2/5` and the constant profile `δ = 41/2500` meet all of them. -/
theorem cellsEight_hypotheses_satisfiable :
    (4 / 625 < (7 / 1000 : ℝ) ∧ (2 / 5 - slack : ℝ) ≤ 2 / 5 ∧
        (2 / 5 : ℝ) ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (521 / 2500 : ℝ) (521 / 2500) 8 8 (41 / 2500) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine ⟨⟨by norm_num, by rw [hsv]; norm_num, by rw [hδ, hsv]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 8 8]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 8 8]; norm_num⟩⟩

end Gap212
