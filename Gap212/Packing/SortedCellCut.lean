/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCut
public import Gap212.Packing.SortedCell

/-!
# Cell `(10,10)` over the whole band, by one cut

`Gap212.Packing.SortedCell` covers parts of cell `(10,10)` by four single sorted assignments, which
leave two windows of `γ` uncovered at the top of the band. The obstruction is not Condition D but
the *single-assignment* sorted reading — a fixed assignment must survive the profile that piles the
group's mass onto its largest coordinate.

A **cut** removes that profile from one of the two halves. With the threshold

    t = 1/25

fixed once and for all, each half of `Gap212.Packing.admitsPartition₄_of_cut` gets its own
certificates, and five of them cover the whole of

    ω₀ ∈ (4/625, 7/1000],   γ ∈ [2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]

— two on the low half `y i ≤ t` throughout the second group, three on the high half where some
coordinate of the second group is at least `t`. That is the whole cell over the whole band.

## The five certificates

`E = B_{1,10} - 10δ = 261/5000` is the mass a group carries above the floor, and
`T = t - δ = 59/2500` the mass its largest coordinate carries above the floor on the low half. A bin
holding first-group ranks `T_k` at density `r_k` and second-group ranks `U_k` at affine majorant
`(s_k, q_k)` carries at most `#T_k·δ + r_k·E + #U_k·δ + s_k·E + q_k·T`.

Writing each certificate as its four bins, first group then second:

* low half, first: `all ten, 1 / {1,4,6,7}, (1/2,0)` — `∅ / {3,8,9}, (3/10,0)` —
  `∅ / {0}, (0,1)` — `∅ / {2,5}, (1/3,0)`.
* low half, second: `all ten, 1 / {1,3,4,6,7}, (5/8,0)` — `∅ / {8,9}, (1/5,0)` —
  `∅ / {0}, (0,1)` — `∅ / {2,5}, (1/3,0)`.
* high half, first: `{0..8}, 1 / {0,1,2}, (1,0)` — `∅ / {4,5,7,9}, (4/9,-4/9)` —
  `∅ / {6,8}, (1/4,-1/4)` — `{9}, 1/10 / {3}, (1/3,-1/3)`.
* high half, second: `{0..7,9}, 1 / {0,1,2,4}, (1,0)` — `∅ / {3,6,9}, (1/3,-1/3)` —
  `∅ / {5,8}, (1/4,-1/4)` — `{8}, 1/9 / {7}, (1/7,-1/7)`.
* high half, third: `{0,1,3,4,6,7,8,9}, 1 / {0,1,2,3,5,8}, (1,0)` — `∅ / {6,9}, (2/9,-2/9)` —
  `∅ / {4,7}, (2/7,-2/7)` — `{2,5}, 1/3 / ∅, (0,0)`.

The bin-2 entry of the low half is the cut doing its work: the second group's *largest* coordinate
sits alone in bin 2, and the only thing known about it is `y ≤ t`, so its block bound is `t = 1/25`
exactly — where the uncut reading would have to allow `B_{1,10} - 9δ = 343/5000`, about one and a
half times the capacity `c₃ ≤ 111/2500`. On the high half the same threshold works in reverse:
`t ≤ y(e 0)` leaves only `E - T = 143/5000` for the ranks below the first, and the deep bins get
their majorants from that.

Where the low half needs the first group untouched — all ten ranks into bin 0 — the high half does
not: it parks one or two of the first group's deepest ranks in bin 3, which bin 3's capacity `8ω₀`
can afford exactly because the second group's deep ranks have become cheap.

## The regions, and why five suffice

Each certificate's four block bounds sit under the four capacities of `Gap212.capD` iff four affine
inequalities in `(γ, ω₀)` hold, and the two that involve `ω₀` alone are met on the whole band:
every one of the five has its bin-2 and bin-3 floors at most `4/625`, the band's own floor. The `γ`
windows, at the band's top `ω₀ = 7/1000` where they are narrowest, are

    low half:   [0.3967, 0.42114] ∪ [0.4196250, 0.442760]
    high half:  [0.390, 0.4076889] ∪ [0.40640, 0.4272667] ∪ [0.42280, 0.4468444]

against the chamber's `[0.4 - ϵ, 0.4276 + 3ϵ]`. Both unions are intervals — the overlaps are
`0.0015` and `0.0013`, `0.0045` — and both contain the chamber range. Since each window's floor
rises in `ω₀` at rate `8` and its ceiling falls at rate `2` while the chamber range is fixed, cover
at `ω₀ = 7/1000` gives cover at every smaller level, so the band needs no case analysis in `ω₀` at
all.

## What this settles

It settles cell `(10,10)` over the whole band.
-/

@[expose] public section

namespace Gap212

open Finset Gap212.Packing

/-! ## The first group's rank sets

The low half of the cut leaves the first group alone, so it reuses `Gap212.cellTenLowRanks` and
`Gap212.cellTenLowDens`. The high half parks the first group's deepest ranks in bin 3, one set per
certificate. -/

/-- The first group's rank sets for the high half's first certificate: the tenth rank to bin 3. -/
def cutTenOver₁LowRanks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3, 4, 5, 6, 7, 8}, ∅, ∅, {9}]

/-- The prefix densities of `Gap212.cutTenOver₁LowRanks`. -/
noncomputable def cutTenOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 1 / 10]

/-- The first group's rank sets for the high half's second certificate: the ninth rank to bin 3. -/
def cutTenOver₂LowRanks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3, 4, 5, 6, 7, 9}, ∅, ∅, {8}]

/-- The prefix densities of `Gap212.cutTenOver₂LowRanks`. -/
noncomputable def cutTenOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 1 / 9]

/-- The first group's rank sets for the high half's third certificate: the third and sixth ranks to
bin 3. -/
def cutTenOver₃LowRanks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 3, 4, 6, 7, 8, 9}, ∅, ∅, {2, 5}]

/-- The prefix densities of `Gap212.cutTenOver₃LowRanks`. -/
noncomputable def cutTenOver₃LowDens : Fin 4 → ℝ := ![1, 0, 0, 1 / 3]

/-! ## The second group's rank sets and affine majorants

Each certificate names four rank sets, four slopes `s` and four constants `q`. On the low half
every `q` is nonnegative and on the high half every `q` is nonpositive; that sign is what decides
which side of the cut the certificate lives on. -/

/-- The second group's rank sets for the low half's first certificate. Rank `0` — the group's
largest coordinate — sits alone in bin 2, where the cut bounds it by `t`. -/
def cutTenUnder₁Ranks : Fin 4 → Finset (Fin 10) := ![{1, 4, 6, 7}, {3, 8, 9}, {0}, {2, 5}]

/-- The slopes of `Gap212.cutTenUnder₁Ranks`. -/
noncomputable def cutTenUnder₁Dens : Fin 4 → ℝ := ![1 / 2, 3 / 10, 0, 1 / 3]

/-- The constants of `Gap212.cutTenUnder₁Ranks`: only bin 2 pays one, and it pays all of it. -/
noncomputable def cutTenUnder₁Const : Fin 4 → ℝ := ![0, 0, 1, 0]

/-- The second group's rank sets for the low half's second certificate. -/
def cutTenUnder₂Ranks : Fin 4 → Finset (Fin 10) := ![{1, 3, 4, 6, 7}, {8, 9}, {0}, {2, 5}]

/-- The slopes of `Gap212.cutTenUnder₂Ranks`. -/
noncomputable def cutTenUnder₂Dens : Fin 4 → ℝ := ![5 / 8, 1 / 5, 0, 1 / 3]

/-- The constants of `Gap212.cutTenUnder₂Ranks`. -/
noncomputable def cutTenUnder₂Const : Fin 4 → ℝ := ![0, 0, 1, 0]

/-- The second group's rank sets for the high half's first certificate. -/
def cutTenOver₁Ranks : Fin 4 → Finset (Fin 10) := ![{0, 1, 2}, {4, 5, 7, 9}, {6, 8}, {3}]

/-- The slopes of `Gap212.cutTenOver₁Ranks`. -/
noncomputable def cutTenOver₁Dens : Fin 4 → ℝ := ![1, 4 / 9, 1 / 4, 1 / 3]

/-- The constants of `Gap212.cutTenOver₁Ranks`, nonpositive throughout: on the high half the
majorant `s·j + q` is bought *below* the uncut density, at the cost of a negative constant. -/
noncomputable def cutTenOver₁Const : Fin 4 → ℝ := ![0, -4 / 9, -1 / 4, -1 / 3]

/-- The second group's rank sets for the high half's second certificate. -/
def cutTenOver₂Ranks : Fin 4 → Finset (Fin 10) := ![{0, 1, 2, 4}, {3, 6, 9}, {5, 8}, {7}]

/-- The slopes of `Gap212.cutTenOver₂Ranks`. -/
noncomputable def cutTenOver₂Dens : Fin 4 → ℝ := ![1, 1 / 3, 1 / 4, 1 / 7]

/-- The constants of `Gap212.cutTenOver₂Ranks`. -/
noncomputable def cutTenOver₂Const : Fin 4 → ℝ := ![0, -1 / 3, -1 / 4, -1 / 7]

/-- The second group's rank sets for the high half's third certificate; bin 3 takes nothing from
the second group, the first group's two parked ranks filling it. -/
def cutTenOver₃Ranks : Fin 4 → Finset (Fin 10) := ![{0, 1, 2, 3, 5, 8}, {6, 9}, {4, 7}, ∅]

/-- The slopes of `Gap212.cutTenOver₃Ranks`. -/
noncomputable def cutTenOver₃Dens : Fin 4 → ℝ := ![1, 2 / 9, 2 / 7, 0]

/-- The constants of `Gap212.cutTenOver₃Ranks`. -/
noncomputable def cutTenOver₃Const : Fin 4 → ℝ := ![0, -2 / 9, -2 / 7, 0]

/-! ## The first group's half, shared by the two low-half certificates -/

private theorem cutLow_cover : ∀ j : Fin 10, ∃ k, j ∈ cellTenLowRanks k := by decide

private theorem cutLow_disj : ∀ k l : Fin 4, k ≠ l →
    Disjoint (cellTenLowRanks k) (cellTenLowRanks l) := by
  intro k l hkl
  rw [Finset.disjoint_iff_inter_eq_empty]
  revert hkl; revert k l; decide

private theorem cutLow_dens_nonneg : ∀ k, 0 ≤ cellTenLowDens k := by
  intro k; fin_cases k <;> simp [cellTenLowDens]

private theorem cutLow_dens : ∀ k, ∀ j : ℕ,
    ((((cellTenLowRanks k).filter (fun i ↦ i.val < j)).card : ℕ) : ℝ) ≤ cellTenLowDens k * j := by
  intro k
  fin_cases k
  · exact fun j ↦ by
      simpa [cellTenLowRanks, cellTenLowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cellTenLowRanks 0) 1 1 one_pos (by decide) j
  · exact fun j ↦ by simp [cellTenLowRanks, cellTenLowDens]
  · exact fun j ↦ by simp [cellTenLowRanks, cellTenLowDens]
  · exact fun j ↦ by simp [cellTenLowRanks, cellTenLowDens]

/-! ## The low half of the cut

Both certificates below assume that *every* coordinate of the second group is at most `t = 1/25`.
Their `γ` windows, at `ω₀ = 7/1000`, are `[0.3967, 0.42114]` and `[0.4196250, 0.442760]`. -/

/-- **The low half of the cut at cell `(10,10)`, first certificate.**

Block bounds `3079/10000`, `3243/50000`, `1/25`, `251/5000`. Valid on the whole band
`4/625 < ω₀` and on `3407/10000 + 8ω₀ + ϵ ≤ γ ≤ 21757/50000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3967 + ϵ, 0.42114 - ϵ]` — reaching below the chamber's own `γ` floor `2/5 - ϵ`.

The third bin's bound is `t` itself: the second group's largest coordinate sits there alone, and
the cut is the only thing bounding it. -/
theorem admitsPartition₄_cellTenTen_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 3407 / 10000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 21757 / 50000 - 2 * ω₀ - slack)
    {y : Fin (10 + 10) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500))
    (hcut : ∀ i : Fin (10 + 10), 10 ≤ (i : ℕ) → y i ≤ 1 / 25) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cellTenLowRanks cutTenUnder₁Ranks cutLow_cover cutLow_disj ?_ ?_
    cellTenLowDens cutTenUnder₁Dens cutTenUnder₁Const cutLow_dens_nonneg ?_ ?_ cutLow_dens ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutTenUnder₁Dens]
  · intro k; fin_cases k <;> norm_num [cutTenUnder₁Const]
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenUnder₁Ranks 0)
        1 0 2 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenUnder₁Ranks, cutTenUnder₁Dens, cutTenUnder₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenUnder₁Ranks 1)
        3 0 10 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenUnder₁Ranks, cutTenUnder₁Dens, cutTenUnder₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenUnder₁Ranks 2)
        0 1 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenUnder₁Ranks, cutTenUnder₁Dens, cutTenUnder₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenUnder₁Ranks 3)
        1 0 3 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenUnder₁Ranks, cutTenUnder₁Dens, cutTenUnder₁Const] at h ⊢
      linarith
  · intro k
    fin_cases k <;>
      · simp [capD, cellTenLowRanks, cutTenUnder₁Ranks, cellTenLowDens, cutTenUnder₁Dens,
          cutTenUnder₁Const, hδ]
        linarith

/-- **The low half of the cut at cell `(10,10)`, second certificate.**

Block bounds `13233/40000`, `1081/25000`, `1/25`, `251/5000`. Valid on the whole band `4/625 < ω₀`
and on `2909/8000 + 8ω₀ + ϵ ≤ γ ≤ 11419/25000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4196250 + ϵ, 0.442760 - ϵ]` — reaching above the chamber's own `γ` ceiling
`1/3 + 8ω(1,1) + 7δ/3 + 3ϵ = 0.4276`.

Its floor is below the first certificate's ceiling by `0.0015` at the top of the band, so the two
together cover the chamber's whole `γ` range on this half of the cut. -/
theorem admitsPartition₄_cellTenTen_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 2909 / 8000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 11419 / 25000 - 2 * ω₀ - slack)
    {y : Fin (10 + 10) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500))
    (hcut : ∀ i : Fin (10 + 10), 10 ≤ (i : ℕ) → y i ≤ 1 / 25) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_low (by norm_num) hy (by norm_num) hcut
    cellTenLowRanks cutTenUnder₂Ranks cutLow_cover cutLow_disj ?_ ?_
    cellTenLowDens cutTenUnder₂Dens cutTenUnder₂Const cutLow_dens_nonneg ?_ ?_ cutLow_dens ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutTenUnder₂Dens]
  · intro k; fin_cases k <;> norm_num [cutTenUnder₂Const]
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenUnder₂Ranks 0)
        5 0 8 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenUnder₂Ranks, cutTenUnder₂Dens, cutTenUnder₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenUnder₂Ranks 1)
        1 0 5 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenUnder₂Ranks, cutTenUnder₂Dens, cutTenUnder₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenUnder₂Ranks 2)
        0 1 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenUnder₂Ranks, cutTenUnder₂Dens, cutTenUnder₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenUnder₂Ranks 3)
        1 0 3 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenUnder₂Ranks, cutTenUnder₂Dens, cutTenUnder₂Const] at h ⊢
      linarith
  · intro k
    fin_cases k <;>
      · simp [capD, cellTenLowRanks, cutTenUnder₂Ranks, cellTenLowDens, cutTenUnder₂Dens,
          cutTenUnder₂Const, hδ]
        linarith

/-! ## The high half of the cut

Here *some* coordinate of the second group is at least `t = 1/25`, so the group's largest
coordinate is, and the mass left for the ranks below it is at most `E - T = 143/5000`. The three
certificates' `γ` windows at `ω₀ = 7/1000` are `[0.390, 0.4076889]`, `[0.40640, 0.4272667]` and
`[0.42280, 0.4468444]`. -/

/-- **The high half of the cut at cell `(10,10)`, first certificate.**

Block bounds `753/2500`, `881/11250`, `799/20000`, `7133/150000`. Valid on the whole band
`4/625 < ω₀` and on `167/500 + 8ω₀ + ϵ ≤ γ ≤ 2372/5625 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.390 + ϵ, 0.4076889 - ϵ]`. -/
theorem admitsPartition₄_cellTenTen_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 167 / 500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2372 / 5625 - 2 * ω₀ - slack)
    {y : Fin (10 + 10) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500))
    (hcut : ∃ i : Fin (10 + 10), 10 ≤ (i : ℕ) ∧ 1 / 25 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutTenOver₁LowRanks cutTenOver₁Ranks ?_ ?_ ?_ ?_
    cutTenOver₁LowDens cutTenOver₁Dens cutTenOver₁Const ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutTenOver₁LowDens]
  · intro k; fin_cases k <;> norm_num [cutTenOver₁Dens]
  · intro k; fin_cases k <;> norm_num [cutTenOver₁Const]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutTenOver₁LowRanks, cutTenOver₁LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutTenOver₁LowRanks 0) 1 1 one_pos (by decide) j
    · exact fun j ↦ by simp [cutTenOver₁LowRanks, cutTenOver₁LowDens]
    · exact fun j ↦ by simp [cutTenOver₁LowRanks, cutTenOver₁LowDens]
    · exact fun j ↦ by
        simpa [cutTenOver₁LowRanks, cutTenOver₁LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutTenOver₁LowRanks 3) 1 10 (by norm_num) (by decide) j
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenOver₁Ranks 0)
        1 0 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenOver₁Ranks, cutTenOver₁Dens, cutTenOver₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenOver₁Ranks 1)
        4 (-4) 9 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenOver₁Ranks, cutTenOver₁Dens, cutTenOver₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenOver₁Ranks 2)
        1 (-1) 4 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenOver₁Ranks, cutTenOver₁Dens, cutTenOver₁Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenOver₁Ranks 3)
        1 (-1) 3 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenOver₁Ranks, cutTenOver₁Dens, cutTenOver₁Const] at h ⊢
      linarith
  · intro k
    fin_cases k <;>
      · simp [capD, cutTenOver₁LowRanks, cutTenOver₁Ranks, cutTenOver₁LowDens, cutTenOver₁Dens,
          cutTenOver₁Const, hδ]
        linarith

/-- **The high half of the cut at cell `(10,10)`, second certificate.**

Block bounds `397/1250`, `881/15000`, `799/20000`, `747/17500`. Valid on the whole band
`4/625 < ω₀` and on `219/625 + 8ω₀ + ϵ ≤ γ ≤ 6619/15000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.40640 + ϵ, 0.4272667 - ϵ]`. -/
theorem admitsPartition₄_cellTenTen_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 219 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 6619 / 15000 - 2 * ω₀ - slack)
    {y : Fin (10 + 10) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500))
    (hcut : ∃ i : Fin (10 + 10), 10 ≤ (i : ℕ) ∧ 1 / 25 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutTenOver₂LowRanks cutTenOver₂Ranks ?_ ?_ ?_ ?_
    cutTenOver₂LowDens cutTenOver₂Dens cutTenOver₂Const ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutTenOver₂LowDens]
  · intro k; fin_cases k <;> norm_num [cutTenOver₂Dens]
  · intro k; fin_cases k <;> norm_num [cutTenOver₂Const]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutTenOver₂LowRanks, cutTenOver₂LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutTenOver₂LowRanks 0) 1 1 one_pos (by decide) j
    · exact fun j ↦ by simp [cutTenOver₂LowRanks, cutTenOver₂LowDens]
    · exact fun j ↦ by simp [cutTenOver₂LowRanks, cutTenOver₂LowDens]
    · exact fun j ↦ by
        simpa [cutTenOver₂LowRanks, cutTenOver₂LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutTenOver₂LowRanks 3) 1 9 (by norm_num) (by decide) j
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenOver₂Ranks 0)
        1 0 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenOver₂Ranks, cutTenOver₂Dens, cutTenOver₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenOver₂Ranks 1)
        1 (-1) 3 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenOver₂Ranks, cutTenOver₂Dens, cutTenOver₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenOver₂Ranks 2)
        1 (-1) 4 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenOver₂Ranks, cutTenOver₂Dens, cutTenOver₂Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenOver₂Ranks 3)
        1 (-1) 7 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenOver₂Ranks, cutTenOver₂Dens, cutTenOver₂Const] at h ⊢
      linarith
  · intro k
    fin_cases k <;>
      · simp [capD, cutTenOver₂LowRanks, cutTenOver₂Ranks, cutTenOver₂LowDens, cutTenOver₂Dens,
          cutTenOver₂Const, hδ]
        linarith

/-- **The high half of the cut at cell `(10,10)`, third certificate.**

Block bounds `167/500`, `881/22500`, `717/17500`, `251/5000`. Valid on the whole band `4/625 < ω₀`
and on `917/2500 + 8ω₀ + ϵ ≤ γ ≤ 10369/22500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.42280 + ϵ, 0.4468444 - ϵ]` — reaching above the chamber's own `γ` ceiling. -/
theorem admitsPartition₄_cellTenTen_over₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 917 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 10369 / 22500 - 2 * ω₀ - slack)
    {y : Fin (10 + 10) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500))
    (hcut : ∃ i : Fin (10 + 10), 10 ≤ (i : ℕ) ∧ 1 / 25 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate_cut_high (by norm_num) hy (by norm_num) hcut
    cutTenOver₃LowRanks cutTenOver₃Ranks ?_ ?_ ?_ ?_
    cutTenOver₃LowDens cutTenOver₃Dens cutTenOver₃Const ?_ ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cutTenOver₃LowDens]
  · intro k; fin_cases k <;> norm_num [cutTenOver₃Dens]
  · intro k; fin_cases k <;> norm_num [cutTenOver₃Const]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cutTenOver₃LowRanks, cutTenOver₃LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutTenOver₃LowRanks 0) 1 1 one_pos (by decide) j
    · exact fun j ↦ by simp [cutTenOver₃LowRanks, cutTenOver₃LowDens]
    · exact fun j ↦ by simp [cutTenOver₃LowRanks, cutTenOver₃LowDens]
    · exact fun j ↦ by
        simpa [cutTenOver₃LowRanks, cutTenOver₃LowDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cutTenOver₃LowRanks 3) 1 3 (by norm_num) (by decide) j
  · intro k
    fin_cases k
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenOver₃Ranks 0)
        1 0 1 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenOver₃Ranks, cutTenOver₃Dens, cutTenOver₃Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenOver₃Ranks 1)
        2 (-2) 9 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenOver₃Ranks, cutTenOver₃Dens, cutTenOver₃Const] at h ⊢
      linarith
    · intro j hj1 hj2
      have h := prefixAffine_of_int (𝕜 := ℝ) (cutTenOver₃Ranks 2)
        2 (-2) 7 (by norm_num) (by decide) j hj1 hj2
      simp [cutTenOver₃Ranks, cutTenOver₃Dens, cutTenOver₃Const] at h ⊢
      linarith
    · intro j _ _
      simp [cutTenOver₃Ranks, cutTenOver₃Dens, cutTenOver₃Const]
  · intro k
    fin_cases k <;>
      · simp [capD, cutTenOver₃LowRanks, cutTenOver₃Ranks, cutTenOver₃LowDens, cutTenOver₃Dens,
          cutTenOver₃Const, hδ]
        linarith

/-! ## The cell, over the whole band -/

/-- **Cell `(10,10)` is discharged on the whole band, by the single cut `t = 1/25`.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every exponent `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,10}, B_{1,10}, 10, 10, δ)` admits
a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's largest
coordinate against `1/25`, then two `γ` cases on the low half and three on the high; no case
analysis in `ω₀` is needed, since every one of the five certificates holds on the whole band. -/
theorem admitsPartition₄_cellTenTen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (10 + 10) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  have hslpos : (0 : ℝ) < slack := by rw [hsv]; norm_num
  have hslsmall : slack ≤ 1 / 10 ^ 10 := le_of_eq hsv
  rw [hδ] at hγhi
  refine admitsPartition₄_of_cut (t := 1 / 25) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · rcases le_or_gt γ (21757 / 50000 - 2 * ω₀ - slack) with h | h
    · exact admitsPartition₄_cellTenTen_under₁ hωlo (by linarith) h hy hcut
    · exact admitsPartition₄_cellTenTen_under₂ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (2372 / 5625 - 2 * ω₀ - slack) with h | h
    · exact admitsPartition₄_cellTenTen_over₁ hωlo (by linarith) h hy hcut
    · rcases le_or_gt γ (6619 / 15000 - 2 * ω₀ - slack) with h' | h'
      · exact admitsPartition₄_cellTenTen_over₂ hωlo (by linarith) h' hy hcut
      · exact admitsPartition₄_cellTenTen_over₃ hωlo (by linarith) (by linarith) hy hcut

/-- **The same, stated against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.**

`Gap212.chamberDBand (7/1000) (4/625) (7/1000)` is the chamber of
`Gap212.PackingCertificate` at the datum's only band pair, `ω(1,1) = 7/1000` being
`Gap212.omegaMax_gap212Params`. -/
theorem admitsPartition₄_cellTenTen_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (10 + 10) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2) (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellTenTen_band hωlo hωhi hγlo hγhi hy

/-- **The band-wide cell at the datum's own parameters**, so a consumer does not have to unfold the
cap row: `gap212Params.B j 10 = gap212Cap 10 = 1081/5000` at every stratum `j`, and
`gap212Params.δ = 41/2500`. -/
theorem admitsPartition₄_cellTenTen_band_atDatum {γ ω₀ : ℝ} (j j' : Fin gap212Params.n)
    (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000) (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (10 + 10) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 10) (gap212Params.B j' 10) 10 10 gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hB : ∀ i : Fin gap212Params.n, gap212Params.B i 10 = 1081 / 5000 := fun _ ↦
    gap212Cap_of_ten_le le_rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rw [hB j, hB j', hδ] at hy
  exact admitsPartition₄_cellTenTen_band hωlo hωhi hγlo hγhi hy

/-- The hypotheses of the five cut certificates are satisfiable on both halves: at `ω₀ = 7/1000`
and `γ = 2/5`, by the constant profile `δ` on the low half and by the profile raising one
second-group coordinate to `1/25` on the high half. -/
theorem cellTenTenCut_hypotheses_satisfiable :
    (4 / 625 < (7 / 1000 : ℝ) ∧ (2 / 5 - slack : ℝ) ≤ 2 / 5 ∧
        (2 / 5 : ℝ) ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack) ∧
      ((fun _ ↦ (41 / 2500 : ℝ)) ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500) ∧
        ∀ i : Fin (10 + 10), 10 ≤ (i : ℕ) → (fun _ ↦ (41 / 2500 : ℝ)) i ≤ 1 / 25) ∧
      ((fun i : Fin (10 + 10) ↦ if (i : ℕ) = 19 then (1 / 25 : ℝ) else 41 / 2500)
          ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500) ∧
        ∃ i : Fin (10 + 10), 10 ≤ (i : ℕ) ∧
          (1 / 25 : ℝ) ≤ (fun i : Fin (10 + 10) ↦ if (i : ℕ) = 19 then (1 / 25 : ℝ)
            else 41 / 2500) i) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine ⟨⟨by norm_num, by rw [hsv]; norm_num, by rw [hδ, hsv]; norm_num⟩,
    ⟨⟨fun i ↦ ⟨le_rfl, by norm_num⟩, ?_, ?_⟩, fun i _ ↦ by norm_num⟩,
    ⟨fun i ↦ ⟨?_, ?_⟩, ?_, ?_⟩, ⟨19, by norm_num, by norm_num⟩⟩
  · rw [Finset.sum_const, Gap212.Packing.card_lowGroup 10 10]
    norm_num
  · rw [Finset.sum_const, Gap212.Packing.card_highGroup 10 10]
    norm_num
  · dsimp only; split_ifs <;> norm_num
  · dsimp only; split_ifs <;> norm_num
  · rw [Finset.sum_congr rfl (g := fun _ ↦ (41 / 2500 : ℝ)) fun i hi ↦ ?_, Finset.sum_const,
      Gap212.Packing.card_lowGroup 10 10]
    · norm_num
    · have : (i : ℕ) < 10 := (Finset.mem_filter.1 hi).2
      dsimp only
      rw [if_neg (by omega)]
  · have hsplit : (Finset.univ.filter (fun i : Fin (10 + 10) ↦ ¬ ((i : ℕ) < 10)))
        = insert (19 : Fin (10 + 10))
          ((Finset.univ.filter (fun i : Fin (10 + 10) ↦ ¬ ((i : ℕ) < 10))).erase 19) := by
      rw [Finset.insert_erase]
      decide
    rw [hsplit, Finset.sum_insert (Finset.notMem_erase _ _)]
    have hrest : ∀ i ∈ (Finset.univ.filter (fun i : Fin (10 + 10) ↦ ¬ ((i : ℕ) < 10))).erase 19,
        (if (i : ℕ) = 19 then (1 / 25 : ℝ) else 41 / 2500) = 41 / 2500 := by
      intro i hi
      have hne : i ≠ 19 := Finset.ne_of_mem_erase hi
      rw [if_neg fun h ↦ hne (Fin.val_injective (by simpa using h))]
    rw [Finset.sum_congr rfl hrest, Finset.sum_const]
    have hcard : ((Finset.univ.filter (fun i : Fin (10 + 10) ↦ ¬ ((i : ℕ) < 10))).erase 19).card
        = 9 := by decide
    rw [hcard]
    norm_num

end Gap212
