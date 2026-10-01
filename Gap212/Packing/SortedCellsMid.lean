/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCutMid
public import Gap212.Packing.SortedCell

/-!
# Cell `(3,3)`, which needs two thresholds, and the middle branch between them

`Gap212.Packing.SortedCellsCut` and `Gap212.Packing.SortedCellsGamma` close ten of the
twelve cells the cut `t = 1/25` misses, each by one threshold per region of `γ`. The cell here,
`(3,3)`, is one that no single threshold reaches **at one point**, which is a different and
stronger obstruction:

> at this cell the supremum `A` of the thresholds the low reading survives lies strictly below
> the infimum `C` of those the high reading survives.

At `(3,3)`, `γ = 2/5 - ϵ` and `ω₀ = 7/1000`, in the mass variable `T = t - δ`:
`A = 202499999/2500000000 = 0.081 - 4·10⁻¹¹`, forced by bin 0, which must hold a whole group of
three beside the second group's `{0,2}`, whose bound `2δ + E/2 + T/2` grows in `T` at rate `1/2`;
against `C = 431/5000 = 0.0862`, forced by bin 3, where the second group's middle rank costs
`δ + (E - T)` and so *falls* in `T` at rate `1`. The cut buys room in bin 0 at half a unit per
unit of `T` and pays for it in bin 3 at a full unit, and `C - A = 0.0052 > 0`, so no `T` does both.
As thresholds rather than masses that reads `t ≤ 0.0974 - 4·10⁻¹¹` for the low branch against
`t ≥ 513/5000 = 0.1026` for the high one, and the pair used below straddles the gap:
`t₁ = 73/1000 < 0.0974` and `t₂ = 43/400 = 0.1075 > 0.1026`.

So the profile space is split into **three** branches rather than two, by applying
`Gap212.Packing.admitsPartition₄_of_cut` at `t₁` and then again, inside its own high branch, at
`t₂`. The middle branch knows `t₁ ≤ y (e₂ 0) ≤ t₂`, and — as
`Gap212.Packing.SortedCutMid` shows — it is served by neither one-sided certificate: reading
it by the low lemma at `t₂` would need `t₂ ≤ A < C ≤ t₂` and by the high lemma at `t₁` would need
`t₁ ≥ C > A ≥ t₁`. It needs
`Gap212.Packing.admitsPartition₄_of_rank_certificate_cut_mid`, whose bins pay their affine
constants at `t₂` where those are nonnegative and at `t₁` where they are nonpositive, with the four
signs free to differ. The middle certificates below do have mixed signs, which is why they exist.

## What closes

`(3,3)` closes on the whole band `(4/625, 7/1000]` and the whole chamber `γ`-range at the single
pair `(t₁, t₂) = (73/1000, 43/400)`, with no case analysis in `ω₀` and no second `γ` region: two
certificates on the bottom branch, two on the middle, one on the top.
-/

@[expose] public section

namespace Gap212

open Finset Gap212.Packing


/-! ## Cell `(3,3)` -/

/-- The first group's rank sets for cell `(3,3)`, the bottom branch's certificate 1. -/
def cutThreeThreeUnder₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutThreeThreeUnder₁LowRanks`. -/
noncomputable def cutThreeThreeUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,3)`, the bottom branch's certificate 1. -/
def cutThreeThreeUnder₁Ranks : Fin 4 → Finset (Fin 3) :=
  ![{1, 2}, {0}, ∅, ∅]

/-- The slopes of `Gap212.cutThreeThreeUnder₁Ranks`. -/
noncomputable def cutThreeThreeUnder₁Dens : Fin 4 → ℝ := ![2 / 3, 0, 0, 0]

/-- The constants of `Gap212.cutThreeThreeUnder₁Ranks`, nonnegative. -/
noncomputable def cutThreeThreeUnder₁Const : Fin 4 → ℝ := ![0, 1, 0, 0]

/-- The first group's rank sets for cell `(3,3)`, the bottom branch's certificate 2. -/
def cutThreeThreeUnder₂LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutThreeThreeUnder₂LowRanks`. -/
noncomputable def cutThreeThreeUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,3)`, the bottom branch's certificate 2. -/
def cutThreeThreeUnder₂Ranks : Fin 4 → Finset (Fin 3) :=
  ![{0, 1}, {2}, ∅, ∅]

/-- The slopes of `Gap212.cutThreeThreeUnder₂Ranks`. -/
noncomputable def cutThreeThreeUnder₂Dens : Fin 4 → ℝ := ![0, 1 / 3, 0, 0]

/-- The constants of `Gap212.cutThreeThreeUnder₂Ranks`, nonnegative. -/
noncomputable def cutThreeThreeUnder₂Const : Fin 4 → ℝ := ![2, 0, 0, 0]

/-- The first group's rank sets for cell `(3,3)`, the middle branch's certificate 1. -/
def cutThreeThreeMid₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutThreeThreeMid₁LowRanks`. -/
noncomputable def cutThreeThreeMid₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,3)`, the middle branch's certificate 1. -/
def cutThreeThreeMid₁Ranks : Fin 4 → Finset (Fin 3) :=
  ![{0}, {1}, ∅, {2}]

/-- The slopes of `Gap212.cutThreeThreeMid₁Ranks`. -/
noncomputable def cutThreeThreeMid₁Dens : Fin 4 → ℝ := ![0, 1 / 2, 0, 1 / 2]

/-- The constants of `Gap212.cutThreeThreeMid₁Ranks`, of either sign —
which is exactly what the middle branch buys. -/
noncomputable def cutThreeThreeMid₁Const : Fin 4 → ℝ := ![1, 0, 0, -1 / 2]

/-- The threshold each bin of `Gap212.cutThreeThreeMid₁Ranks` pays its constant at: the
upper one `43 / 400` where the constant is nonnegative, the lower one `73 / 1000` where it is
nonpositive. -/
noncomputable def cutThreeThreeMid₁Pay : Fin 4 → ℝ := ![43 / 400, 43 / 400, 43 / 400, 73 / 1000]

/-- The first group's rank sets for cell `(3,3)`, the middle branch's certificate 2. -/
def cutThreeThreeMid₂LowRanks : Fin 4 → Finset (Fin 3) :=
  ![{0, 1}, {2}, ∅, ∅]

/-- The prefix densities of `Gap212.cutThreeThreeMid₂LowRanks`. -/
noncomputable def cutThreeThreeMid₂LowDens : Fin 4 → ℝ := ![1, 1 / 3, 0, 0]

/-- The second group's rank sets for cell `(3,3)`, the middle branch's certificate 2. -/
def cutThreeThreeMid₂Ranks : Fin 4 → Finset (Fin 3) :=
  ![{0, 1}, ∅, ∅, {2}]

/-- The slopes of `Gap212.cutThreeThreeMid₂Ranks`. -/
noncomputable def cutThreeThreeMid₂Dens : Fin 4 → ℝ := ![1, 0, 0, 1 / 2]

/-- The constants of `Gap212.cutThreeThreeMid₂Ranks`, of either sign —
which is exactly what the middle branch buys. -/
noncomputable def cutThreeThreeMid₂Const : Fin 4 → ℝ := ![0, 0, 0, -1 / 2]

/-- The threshold each bin of `Gap212.cutThreeThreeMid₂Ranks` pays its constant at: the
upper one `43 / 400` where the constant is nonnegative, the lower one `73 / 1000` where it is
nonpositive. -/
noncomputable def cutThreeThreeMid₂Pay : Fin 4 → ℝ := ![43 / 400, 43 / 400, 43 / 400, 73 / 1000]

/-- The first group's rank sets for cell `(3,3)`, the top branch's certificate 1. -/
def cutThreeThreeOver₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![{0, 1}, {2}, ∅, ∅]

/-- The prefix densities of `Gap212.cutThreeThreeOver₁LowRanks`. -/
noncomputable def cutThreeThreeOver₁LowDens : Fin 4 → ℝ := ![1, 1 / 3, 0, 0]

/-- The second group's rank sets for cell `(3,3)`, the top branch's certificate 1. -/
def cutThreeThreeOver₁Ranks : Fin 4 → Finset (Fin 3) :=
  ![{0}, ∅, {2}, {1}]

/-- The slopes of `Gap212.cutThreeThreeOver₁Ranks`. -/
noncomputable def cutThreeThreeOver₁Dens : Fin 4 → ℝ := ![1, 0, 1 / 2, 1]

/-- The constants of `Gap212.cutThreeThreeOver₁Ranks`, nonpositive. -/
noncomputable def cutThreeThreeOver₁Const : Fin 4 → ℝ := ![0, 0, -1 / 2, -1]

/-- **Cell `(3,3)`, the bottom branch's certificate 1.**

Block bounds `7 / 24`, `73 / 1000`, `0`, `0`.
Valid on `4 / 625 < ω₀` and on
`4867 / 15000 + 8ω₀ + ϵ ≤ γ ≤ 427 / 1000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3804667 + ϵ, 0.4130000 - ϵ]`.
The branch is `y i ≤ 73 / 1000` throughout the second group. -/
theorem admitsPartition₄_cellThreeThree_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 4867 / 15000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 427 / 1000 - 2 * ω₀ - slack)
    {y : Fin (3 + 3) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (7 / 40) 3 3 (41 / 2500))
    (hcut : ∀ i : Fin (3 + 3), 3 ≤ (i : ℕ) → y i ≤ 73 / 1000) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutThreeThreeUnder₁LowRanks cutThreeThreeUnder₁Ranks ?_ ?_ ?_ ?_
    cutThreeThreeUnder₁LowDens cutThreeThreeUnder₁Dens cutThreeThreeUnder₁Const ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutThreeThreeUnder₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutThreeThreeUnder₁Dens]
  · intro k; fin_cases k <;> norm_num [cutThreeThreeUnder₁Const]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutThreeThreeUnder₁LowRanks, cutThreeThreeUnder₁LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutThreeThreeUnder₁LowRanks 0) 1 1
            (by norm_num) (by decide) j
    · exact fun j ↦ by simp [cutThreeThreeUnder₁LowRanks, cutThreeThreeUnder₁LowDens]
    · exact fun j ↦ by simp [cutThreeThreeUnder₁LowRanks, cutThreeThreeUnder₁LowDens]
    · exact fun j ↦ by simp [cutThreeThreeUnder₁LowRanks, cutThreeThreeUnder₁LowDens]
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutThreeThreeUnder₁Ranks 0)
        2 0 3 (by norm_num) (by decide) j hj1 hj2
      simp [cutThreeThreeUnder₁Ranks, cutThreeThreeUnder₁Dens, cutThreeThreeUnder₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutThreeThreeUnder₁Ranks 1)
        0 1 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutThreeThreeUnder₁Ranks, cutThreeThreeUnder₁Dens, cutThreeThreeUnder₁Const] at h ⊢
      linarith
    · intro j _ _
      simp [cutThreeThreeUnder₁Ranks, cutThreeThreeUnder₁Dens, cutThreeThreeUnder₁Const]
    · intro j _ _
      simp [cutThreeThreeUnder₁Ranks, cutThreeThreeUnder₁Dens, cutThreeThreeUnder₁Const]
  · intro k
    fin_cases k <;>
      · simp [capD, hδ, cutThreeThreeUnder₁LowRanks, cutThreeThreeUnder₁Ranks,
          cutThreeThreeUnder₁LowDens, cutThreeThreeUnder₁Dens, cutThreeThreeUnder₁Const]
        all_goals linarith

/-- **Cell `(3,3)`, the bottom branch's certificate 2.**

Block bounds `321 / 1000`, `7 / 120`, `0`, `0`.
Valid on `4 / 625 < ω₀` and on
`1769 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 53 / 120 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4098000 + ϵ, 0.4276667 - ϵ]`.
The branch is `y i ≤ 73 / 1000` throughout the second group. -/
theorem admitsPartition₄_cellThreeThree_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1769 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 53 / 120 - 2 * ω₀ - slack)
    {y : Fin (3 + 3) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (7 / 40) 3 3 (41 / 2500))
    (hcut : ∀ i : Fin (3 + 3), 3 ≤ (i : ℕ) → y i ≤ 73 / 1000) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cutThreeThreeUnder₂LowRanks cutThreeThreeUnder₂Ranks ?_ ?_ ?_ ?_
    cutThreeThreeUnder₂LowDens cutThreeThreeUnder₂Dens cutThreeThreeUnder₂Const ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutThreeThreeUnder₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutThreeThreeUnder₂Dens]
  · intro k; fin_cases k <;> norm_num [cutThreeThreeUnder₂Const]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutThreeThreeUnder₂LowRanks, cutThreeThreeUnder₂LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutThreeThreeUnder₂LowRanks 0) 1 1
            (by norm_num) (by decide) j
    · exact fun j ↦ by simp [cutThreeThreeUnder₂LowRanks, cutThreeThreeUnder₂LowDens]
    · exact fun j ↦ by simp [cutThreeThreeUnder₂LowRanks, cutThreeThreeUnder₂LowDens]
    · exact fun j ↦ by simp [cutThreeThreeUnder₂LowRanks, cutThreeThreeUnder₂LowDens]
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutThreeThreeUnder₂Ranks 0)
        0 2 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutThreeThreeUnder₂Ranks, cutThreeThreeUnder₂Dens, cutThreeThreeUnder₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutThreeThreeUnder₂Ranks 1)
        1 0 3 (by norm_num) (by decide) j hj1 hj2
      simp [cutThreeThreeUnder₂Ranks, cutThreeThreeUnder₂Dens, cutThreeThreeUnder₂Const] at h ⊢
      linarith
    · intro j _ _
      simp [cutThreeThreeUnder₂Ranks, cutThreeThreeUnder₂Dens, cutThreeThreeUnder₂Const]
    · intro j _ _
      simp [cutThreeThreeUnder₂Ranks, cutThreeThreeUnder₂Dens, cutThreeThreeUnder₂Const]
  · intro k
    fin_cases k <;>
      · simp [capD, hδ, cutThreeThreeUnder₂LowRanks, cutThreeThreeUnder₂Ranks,
          cutThreeThreeUnder₂LowDens, cutThreeThreeUnder₂Dens, cutThreeThreeUnder₂Const]
        all_goals linarith

/-- **Cell `(3,3)`, the middle branch's certificate 1.**

Block bounds `113 / 400`, `793 / 10000`, `0`, `51 / 1000`.
Valid on `4 / 625 < ω₀` and on
`3153 / 10000 + 8ω₀ + ϵ ≤ γ ≤ 4207 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3713000 + ϵ, 0.4067000 - ϵ]`.
The branch is `73 / 1000 ≤ y (e₂ 0) ≤ 43 / 400`, and the bins pay their constants at
`Gap212.cutThreeThreeMid₁Pay`. -/
theorem admitsPartition₄_cellThreeThree_mid₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3153 / 10000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4207 / 10000 - 2 * ω₀ - slack)
    {y : Fin (3 + 3) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (7 / 40) 3 3 (41 / 2500))
    (hcutle : ∀ i : Fin (3 + 3), 3 ≤ (i : ℕ) → y i ≤ 43 / 400)
    (hcutge : ∃ i : Fin (3 + 3), 3 ≤ (i : ℕ) ∧ 73 / 1000 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_mid (by norm_num) hy (by norm_num) hcutle hcutge
    cutThreeThreeMid₁LowRanks cutThreeThreeMid₁Ranks ?_ ?_ ?_ ?_
    cutThreeThreeMid₁LowDens cutThreeThreeMid₁Dens cutThreeThreeMid₁Const
    cutThreeThreeMid₁Pay ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutThreeThreeMid₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutThreeThreeMid₁Dens]
  · intro k; fin_cases k <;> norm_num [cutThreeThreeMid₁Const, cutThreeThreeMid₁Pay]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutThreeThreeMid₁LowRanks, cutThreeThreeMid₁LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutThreeThreeMid₁LowRanks 0) 1 1
            (by norm_num) (by decide) j
    · exact fun j ↦ by simp [cutThreeThreeMid₁LowRanks, cutThreeThreeMid₁LowDens]
    · exact fun j ↦ by simp [cutThreeThreeMid₁LowRanks, cutThreeThreeMid₁LowDens]
    · exact fun j ↦ by simp [cutThreeThreeMid₁LowRanks, cutThreeThreeMid₁LowDens]
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutThreeThreeMid₁Ranks 0)
        0 1 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutThreeThreeMid₁Ranks, cutThreeThreeMid₁Dens, cutThreeThreeMid₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutThreeThreeMid₁Ranks 1)
        1 0 2 (by norm_num) (by decide) j hj1 hj2
      simp [cutThreeThreeMid₁Ranks, cutThreeThreeMid₁Dens, cutThreeThreeMid₁Const] at h ⊢
      linarith
    · intro j _ _
      simp [cutThreeThreeMid₁Ranks, cutThreeThreeMid₁Dens, cutThreeThreeMid₁Const]
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutThreeThreeMid₁Ranks 3)
        1 (-1) 2 (by norm_num) (by decide) j hj1 hj2
      simp [cutThreeThreeMid₁Ranks, cutThreeThreeMid₁Dens, cutThreeThreeMid₁Const] at h ⊢
      linarith
  · intro k
    fin_cases k <;>
      · simp [capD, hδ, cutThreeThreeMid₁LowRanks, cutThreeThreeMid₁Ranks,
          cutThreeThreeMid₁LowDens, cutThreeThreeMid₁Dens, cutThreeThreeMid₁Const,
          cutThreeThreeMid₁Pay]
        all_goals linarith

/-- **Cell `(3,3)`, the middle branch's certificate 2.**

Block bounds `793 / 2500`, `7 / 120`, `0`, `51 / 1000`.
Valid on `4 / 625 < ω₀` and on
`7 / 20 + 8ω₀ + ϵ ≤ γ ≤ 53 / 120 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4060000 + ϵ, 0.4276667 - ϵ]`.
The branch is `73 / 1000 ≤ y (e₂ 0) ≤ 43 / 400`, and the bins pay their constants at
`Gap212.cutThreeThreeMid₂Pay`. -/
theorem admitsPartition₄_cellThreeThree_mid₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 7 / 20 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 53 / 120 - 2 * ω₀ - slack)
    {y : Fin (3 + 3) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (7 / 40) 3 3 (41 / 2500))
    (hcutle : ∀ i : Fin (3 + 3), 3 ≤ (i : ℕ) → y i ≤ 43 / 400)
    (hcutge : ∃ i : Fin (3 + 3), 3 ≤ (i : ℕ) ∧ 73 / 1000 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_mid (by norm_num) hy (by norm_num) hcutle hcutge
    cutThreeThreeMid₂LowRanks cutThreeThreeMid₂Ranks ?_ ?_ ?_ ?_
    cutThreeThreeMid₂LowDens cutThreeThreeMid₂Dens cutThreeThreeMid₂Const
    cutThreeThreeMid₂Pay ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutThreeThreeMid₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutThreeThreeMid₂Dens]
  · intro k; fin_cases k <;> norm_num [cutThreeThreeMid₂Const, cutThreeThreeMid₂Pay]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutThreeThreeMid₂LowRanks, cutThreeThreeMid₂LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutThreeThreeMid₂LowRanks 0) 1 1
            (by norm_num) (by decide) j
    · exact fun j ↦ by
        simpa [cutThreeThreeMid₂LowRanks, cutThreeThreeMid₂LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutThreeThreeMid₂LowRanks 1) 1 3
            (by norm_num) (by decide) j
    · exact fun j ↦ by simp [cutThreeThreeMid₂LowRanks, cutThreeThreeMid₂LowDens]
    · exact fun j ↦ by simp [cutThreeThreeMid₂LowRanks, cutThreeThreeMid₂LowDens]
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutThreeThreeMid₂Ranks 0)
        1 0 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutThreeThreeMid₂Ranks, cutThreeThreeMid₂Dens, cutThreeThreeMid₂Const] at h ⊢
      linarith
    · intro j _ _
      simp [cutThreeThreeMid₂Ranks, cutThreeThreeMid₂Dens, cutThreeThreeMid₂Const]
    · intro j _ _
      simp [cutThreeThreeMid₂Ranks, cutThreeThreeMid₂Dens, cutThreeThreeMid₂Const]
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutThreeThreeMid₂Ranks 3)
        1 (-1) 2 (by norm_num) (by decide) j hj1 hj2
      simp [cutThreeThreeMid₂Ranks, cutThreeThreeMid₂Dens, cutThreeThreeMid₂Const] at h ⊢
      linarith
  · intro k
    fin_cases k <;>
      · simp [capD, hδ, cutThreeThreeMid₂LowRanks, cutThreeThreeMid₂Ranks,
          cutThreeThreeMid₂LowDens, cutThreeThreeMid₂Dens, cutThreeThreeMid₂Const,
          cutThreeThreeMid₂Pay]
        all_goals linarith

/-- **Cell `(3,3)`, the top branch's certificate 1.**

Block bounds `188 / 625`, `7 / 120`, `27 / 800`, `511 / 10000`.
Valid on `4 / 625 < ω₀` and on
`417 / 1250 + 8ω₀ + ϵ ≤ γ ≤ 53 / 120 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3896000 + ϵ, 0.4276667 - ϵ]`.
The branch is `43 / 400 ≤ y i` for some `i` of the second group. -/
theorem admitsPartition₄_cellThreeThree_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 417 / 1250 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 53 / 120 - 2 * ω₀ - slack)
    {y : Fin (3 + 3) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (7 / 40) 3 3 (41 / 2500))
    (hcut : ∃ i : Fin (3 + 3), 3 ≤ (i : ℕ) ∧ 43 / 400 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutThreeThreeOver₁LowRanks cutThreeThreeOver₁Ranks ?_ ?_ ?_ ?_
    cutThreeThreeOver₁LowDens cutThreeThreeOver₁Dens cutThreeThreeOver₁Const ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutThreeThreeOver₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutThreeThreeOver₁Dens]
  · intro k; fin_cases k <;> norm_num [cutThreeThreeOver₁Const]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutThreeThreeOver₁LowRanks, cutThreeThreeOver₁LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutThreeThreeOver₁LowRanks 0) 1 1
            (by norm_num) (by decide) j
    · exact fun j ↦ by
        simpa [cutThreeThreeOver₁LowRanks, cutThreeThreeOver₁LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutThreeThreeOver₁LowRanks 1) 1 3
            (by norm_num) (by decide) j
    · exact fun j ↦ by simp [cutThreeThreeOver₁LowRanks, cutThreeThreeOver₁LowDens]
    · exact fun j ↦ by simp [cutThreeThreeOver₁LowRanks, cutThreeThreeOver₁LowDens]
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutThreeThreeOver₁Ranks 0)
        1 0 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutThreeThreeOver₁Ranks, cutThreeThreeOver₁Dens, cutThreeThreeOver₁Const] at h ⊢
      linarith
    · intro j _ _
      simp [cutThreeThreeOver₁Ranks, cutThreeThreeOver₁Dens, cutThreeThreeOver₁Const]
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutThreeThreeOver₁Ranks 2)
        1 (-1) 2 (by norm_num) (by decide) j hj1 hj2
      simp [cutThreeThreeOver₁Ranks, cutThreeThreeOver₁Dens, cutThreeThreeOver₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutThreeThreeOver₁Ranks 3)
        1 (-1) 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutThreeThreeOver₁Ranks, cutThreeThreeOver₁Dens, cutThreeThreeOver₁Const] at h ⊢
      linarith
  · intro k
    fin_cases k <;>
      · simp [capD, hδ, cutThreeThreeOver₁LowRanks, cutThreeThreeOver₁Ranks,
          cutThreeThreeOver₁LowDens, cutThreeThreeOver₁Dens, cutThreeThreeOver₁Const]
        all_goals linarith

/-- **Cell `(3,3)` is discharged on the whole band, by a two-threshold cut.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,3}, B_{1,3}, 3, 3, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` twice over — at `t₁ = 73 / 1000`
and then, inside its high branch, at `t₂ = 43 / 400` — so the second group's largest
coordinate falls in one of three branches, and the middle one carries *both* hypotheses.
That is what a single threshold cannot do here: the low reading's supremum `A` sits strictly
below the high reading's infimum `C` at this cell, so no one threshold closes it, and by the
argument in `Gap212.Packing.SortedCutMid` the middle branch is served by neither
one-sided lemma — it needs `Gap212.Packing.admitsPartition₄_of_rank_certificate_cut_mid`,
whose bins pay their affine constants at `t₂` or at `t₁` according to each constant's own
sign. -/
theorem admitsPartition₄_cellThreeThree_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 3) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (7 / 40) 3 3 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rw [hδ] at hγhi
  refine admitsPartition₄_of_cut (t := 73 / 1000) (by norm_num) (fun hcut ↦ ?_) (fun hcutge ↦ ?_)
  · rcases le_or_gt γ (427 / 1000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellThreeThree_under₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellThreeThree_under₂ hωlo (by linarith) (by linarith) hy hcut
  · refine admitsPartition₄_of_cut (t := 43 / 400) (by norm_num) (fun hcutle ↦ ?_) (fun hcut ↦ ?_)
    · rcases le_or_gt γ (4207 / 10000 - 2 * ω₀ - slack) with h1 | h1
      · exact admitsPartition₄_cellThreeThree_mid₁ hωlo (by linarith) h1 hy hcutle hcutge
      · exact admitsPartition₄_cellThreeThree_mid₂ hωlo (by linarith) (by linarith) hy
          hcutle hcutge
    · exact admitsPartition₄_cellThreeThree_over₁ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(3,3)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellThreeThree_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (3 + 3) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (7 / 40) 3 3 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellThreeThree_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(3,3)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 3 = gap212Cap 3 = 7 / 40` at every stratum `j`. -/
theorem admitsPartition₄_cellThreeThree_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 3) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 3) (gap212Params.B j' 3) 3 3
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hrow1 : gap212Params.B j 3 = gap212Cap 3 := rfl
  have hrow2 : gap212Params.B j' 3 = gap212Cap 3 := rfl
  have hB1 : gap212Cap 3 = (7 / 40 : ℝ) := by unfold gap212Cap; norm_num
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rw [hrow1, hrow2, hB1, hδ] at hy
  exact admitsPartition₄_cellThreeThree_band hωlo hωhi hγlo hγhi hy

/-- The hypotheses of the band theorems above are satisfiable: the chamber point `ω₀ = 7/1000`,
`γ = 2/5` and the constant profile `δ = 41/2500` meet all of them. -/
theorem cellsMid_hypotheses_satisfiable :
    (4 / 625 < (7 / 1000 : ℝ) ∧ (2 / 5 - slack : ℝ) ≤ 2 / 5 ∧
        (2 / 5 : ℝ) ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (7 / 40 : ℝ) (7 / 40) 3 3 (41 / 2500) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine ⟨⟨by norm_num, by rw [hsv]; norm_num, by rw [hδ, hsv]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 3 3]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 3 3]; norm_num⟩⟩

end Gap212
