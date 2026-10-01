/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Consequences.CheckSetEmptyAboveThirteen
public import Gap212.Packing.DatumFacts
public import Gap212.Packing.PackingCertificate
public import Gap212.Packing.SortedCellCut
public import Gap212.Packing.SortedCellsCut
public import Gap212.Packing.SortedCellsEight
public import Gap212.Packing.SortedCellsGamma
public import Gap212.Packing.SortedCellsMid
public import Gap212.Packing.SortedCellsPair
public import Gap212.Packing.SortedCellsRest
public import Gap212.Packing.SortedCellsSub
public import Gap212.Packing.SortedCellsUncut1
public import Gap212.Packing.SortedCellsUncut2
public import Gap212.Packing.SortedCellsUncut3
public import Gap212.Packing.SortedCellsUncut4
public import Gap212.Packing.SortedTranspose

/-!
# `Gap212.PackingCertificate` is a theorem

`Gap212.PackingCertificate` is Condition D at the chosen datum on the band
`4/625 < ω₀ ≤ ω(1,1) = 7/1000`, for every ordered pair `(m, m')` of side sizes and every profile of
the check set. This file proves it.

Every cell has its own certificate in the files imported above: 62 with no cut at all, 22 with one
cut at a single threshold, five (`(4,4)`, `(5,5)`, `(5,6)`, `(6,6)`, `(7,8)`) with one cut whose
threshold depends on the region of `γ`, and `(3,3)` and `(8,8)` with two nested cuts; and
`Gap212.Packing.admitsPartition₄_transpose_of` carries each off-diagonal cell to its transpose. The
case analysis has exactly three parts.

## The three parts

**Above thirteen the check set is empty.** `Gap212.Xi_nonempty_iff_le_thirteen` is an iff, so the
profile `y` the condition is handed is itself the witness that `m ≤ 13` and `m' ≤ 13`: no
separate emptiness branch is needed, and the quantifier `m, m' ≤ ⌊1/δ⌋₊ = 60` costs nothing. The
two side conditions it wants are that the cap row never exceeds `1081/5000` and that
`m δ ≤ B_{1,m}` up to `m = 13`, both `norm_num` on `Gap212.gap212Cap`.

**An empty side needs no cell.** When `m = 0` the first group contributes nothing and the pooled
mass is at most `B_{1,m'} ≤ 1081/5000 = 0.2162`, while the first capacity
`capD γ ω₀ 0 = γ - 2δ - 8ω₀ - ϵ` is at least `0.3112 - 2ϵ` on the whole chamber. So the whole
tuple goes in the first block and the other three stay empty; that is
`Gap212.admitsPartition₄_emptySide_band` below, and it covers `m = 0` and `m' = 0` at once, in
either order, with no transpose. This is the same edge that
`Gap212.Packing.exists_bins_empty_side_of_exists_bins_one` handles for all six conditions at
once; here the four-block case is two lines from `Gap212.Packing.admitsPartition₄_of_total_le`, so
it is proved directly rather than routed through the `∃ f` interface.

**The 169 live cells.** `1 ≤ m, m' ≤ 13`, dispatched by `interval_cases` twice: the 91 with
`m ≤ m'` to their own `_band_atDatum` theorem, the 78 with `m > m'` to the `_band_atDatum` theorem
of the transposed pair through `Gap212.Packing.admitsPartition₄_transpose_of`.

## Main results

* `Gap212.admitsPartition₄_emptySide_band`: the empty-side edge, four blocks.
* `Gap212.packingCertificate_at_datum`: `Gap212.PackingCertificate`, proved.
-/

@[expose] public section

namespace Gap212

open Finset Gap212.Bridges Gap212.Defs Gap212.Packing

/-- **A cell whose pooled cap fits in the first block alone.**

The whole tuple goes in block one and the other three stay empty. The hypothesis `hB` is what makes
that work: on the chamber `capD γ ω₀ 0 = γ - 2δ - 8ω₀ - ϵ` is at least
`2/5 - ϵ - 2δ - 8·7/1000 - ϵ`, which is `1556/5000 - 2ϵ`, so a pooled cap of `1081/5000` fits with
room to spare. The other three capacities are positive on the chamber:
`1/2 - γ - 2ω₀ - ϵ ≥ 0.0578`, `4ω₀ + δ - ϵ > 0` and `8ω₀ > 0`.

This is the edge case `m = 0` or `m' = 0` of `Gap212.PackingCertificate`, where the empty side's
cap `B_{1,0}` is `0` and the other side's is at most `1081/5000`. It needs no rank certificate and
no group swap: the statement is symmetric in the two sides. -/
theorem admitsPartition₄_emptySide_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {m₁ m₂ : ℕ} {B₁ B₂ : ℝ} (hB : B₁ + B₂ ≤ 1081 / 5000) {y : Fin (m₁ + m₂) → ℝ}
    (hy : y ∈ Xi B₁ B₂ m₁ m₂ gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = (41 / 2500 : ℝ) := rfl
  rw [hδ] at hγhi
  refine admitsPartition₄_of_total_le (((total_le hy).trans hB).trans ?_) ?_ ?_ ?_
  · rw [capD_zero, hδ]; linarith
  · rw [capD_one]; linarith
  · rw [capD_two, hδ]; linarith
  · rw [capD_three]; linarith

/-- **`Gap212.PackingCertificate`, proved.**

Condition D at `p_⋆` on the band `4/625 < ω₀ ≤ ω(1,1)`, for every ordered pair of side sizes and
every profile of the check set. The module docstring above says how the three parts of the case
analysis fit together and where each cell's certificate lives. -/
theorem packingCertificate_at_datum : PackingCertificate := by
  intro j j' m m' _ _
  rw [omegaMax_gap212Params]
  intro p hp y hy
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  have hrow : ∀ (k : Fin gap212Params.n) (i : ℕ), gap212Params.B k i = gap212Cap i := fun _ _ ↦ rfl
  have hδ : gap212Params.δ = (41 / 2500 : ℝ) := rfl
  have hcap : ∀ k, gap212Cap k ≤ (1081 / 5000 : ℝ) := by
    intro k; unfold gap212Cap; split_ifs <;> norm_num
  obtain ⟨hm13, hm13'⟩ : m ≤ 13 ∧ m' ≤ 13 := by
    refine (Xi_nonempty_iff_le_thirteen (B := gap212Cap) hcap ?_ m m').1 ⟨y, ?_⟩
    · intro k hk; interval_cases k <;> (unfold gap212Cap; norm_num)
    · rw [hrow, hrow, hδ] at hy; exact hy
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · refine admitsPartition₄_emptySide_band hωlo hωhi hγlo hγhi ?_ hy
    rw [hrow, hrow, show gap212Cap 0 = (0 : ℝ) from by unfold gap212Cap; norm_num]
    linarith [hcap m']
  rcases Nat.eq_zero_or_pos m' with rfl | hmpos'
  · refine admitsPartition₄_emptySide_band hωlo hωhi hγlo hγhi ?_ hy
    rw [hrow, hrow, show gap212Cap 0 = (0 : ℝ) from by unfold gap212Cap; norm_num]
    linarith [hcap m]
  interval_cases m
  · interval_cases m'
    · exact admitsPartition₄_cellOneOne_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellOneTwo_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellOneThree_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellOneFour_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellOneFive_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellOneSix_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellOneSeven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellOneEight_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellOneNine_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellOneTen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellOneEleven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellOneTwelve_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellOneThirteen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
  · interval_cases m'
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellOneTwo_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · exact admitsPartition₄_cellTwoTwo_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellTwoThree_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellTwoFour_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellTwoFive_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellTwoSix_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellTwoSeven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellTwoEight_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellTwoNine_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellTwoTen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellTwoEleven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellTwoTwelve_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellTwoThirteen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
  · interval_cases m'
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellOneThree_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellTwoThree_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · exact admitsPartition₄_cellThreeThree_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellThreeFour_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellThreeFive_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellThreeSix_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellThreeSeven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellThreeEight_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellThreeNine_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellThreeTen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellThreeEleven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellThreeTwelve_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellThreeThirteen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
  · interval_cases m'
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellOneFour_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellTwoFour_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellThreeFour_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · exact admitsPartition₄_cellFourFour_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFourFive_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFourSix_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFourSeven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFourEight_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFourNine_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFourTen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFourEleven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFourTwelve_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFourThirteen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
  · interval_cases m'
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellOneFive_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellTwoFive_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellThreeFive_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFourFive_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · exact admitsPartition₄_cellFiveFive_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFiveSix_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFiveSeven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFiveEight_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFiveNine_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFiveTen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFiveEleven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFiveTwelve_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellFiveThirteen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
  · interval_cases m'
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellOneSix_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellTwoSix_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellThreeSix_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFourSix_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFiveSix_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · exact admitsPartition₄_cellSixSix_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellSixSeven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellSixEight_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellSixNine_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellSixTen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellSixEleven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellSixTwelve_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellSixThirteen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
  · interval_cases m'
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellOneSeven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellTwoSeven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellThreeSeven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFourSeven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFiveSeven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellSixSeven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · exact admitsPartition₄_cellSevenSeven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellSevenEight_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellSevenNine_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellSevenTen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellSevenEleven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellSevenTwelve_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellSevenThirteen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
  · interval_cases m'
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellOneEight_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellTwoEight_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellThreeEight_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFourEight_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFiveEight_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellSixEight_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellSevenEight_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · exact admitsPartition₄_cellEightEight_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellEightNine_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellEightTen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellEightEleven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellEightTwelve_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellEightThirteen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
  · interval_cases m'
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellOneNine_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellTwoNine_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellThreeNine_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFourNine_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFiveNine_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellSixNine_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellSevenNine_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellEightNine_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · exact admitsPartition₄_cellNineNine_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellNineTen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellNineEleven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellNineTwelve_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellNineThirteen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
  · interval_cases m'
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellOneTen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellTwoTen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellThreeTen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFourTen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFiveTen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellSixTen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellSevenTen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellEightTen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellNineTen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · exact admitsPartition₄_cellTenTen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellTenEleven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellTenTwelve_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellTenThirteen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
  · interval_cases m'
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellOneEleven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellTwoEleven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellThreeEleven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFourEleven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFiveEleven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellSixEleven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellSevenEleven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellEightEleven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellNineEleven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellTenEleven_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · exact admitsPartition₄_cellElevenEleven_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellElevenTwelve_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellElevenThirteen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
  · interval_cases m'
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellOneTwelve_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellTwoTwelve_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellThreeTwelve_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFourTwelve_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFiveTwelve_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellSixTwelve_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellSevenTwelve_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellEightTwelve_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellNineTwelve_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellTenTwelve_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellElevenTwelve_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · exact admitsPartition₄_cellTwelveTwelve_band_atDatum j j' hωlo hωhi hγlo hγhi hy
    · exact admitsPartition₄_cellTwelveThirteen_band_atDatum j j' hωlo hωhi hγlo hγhi hy
  · interval_cases m'
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellOneThirteen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellTwoThirteen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellThreeThirteen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFourThirteen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellFiveThirteen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellSixThirteen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellSevenThirteen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellEightThirteen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellNineThirteen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellTenThirteen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellElevenThirteen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · refine admitsPartition₄_transpose_of (c := fun k ↦ capD p.1 p.2 k) hy ?_
      exact fun _ hz ↦ admitsPartition₄_cellTwelveThirteen_band_atDatum j' j hωlo hωhi hγlo hγhi hz
    · exact admitsPartition₄_cellThirteenThirteen_band_atDatum j j' hωlo hωhi hγlo hγhi hy

end Gap212
