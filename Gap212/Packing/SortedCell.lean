/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCone
public import Gap212.Packing.DatumConditionD

/-!
# The Type IIc packing at cell `(10, 10)`, by single sorted assignments

The seven bands of Condition D at `p_⋆` below `ω₀ = 4/625` run a sort-free argument
(`Gap212.Packing.exists_small_coords`). This file treats the cell `(10, 10)` above that level by
rank instead, using `Gap212.Packing.SortedCone`, on the parts of the band that a single sorted
assignment covers. The first certificate is
eight rank sets and eight prefix densities, and every numeral in it is exact:

| bin | low-group ranks | `r` | high-group ranks | `s` | block bound |
| --- | --- | --- | --- | --- | --- |
| 0 | all ten | `1` | `{1,3,5,7}` | `1/2` | `3079/10000` |
| 1 | none | `0` | `{0,2}` | `1` | `17/200` |
| 2 | none | `0` | `{4,9}` | `1/5` | `1081/25000` |
| 3 | none | `0` | `{6,8}` | `2/9` | `111/2500` |

Ranks are counted from the largest coordinate, so rank `0` is the heaviest. The block bound is
`|T|·δ + r·(B - 10δ) + |U|·δ + s·(B - 10δ)` with `δ = 41/2500`, `B = 1081/5000` and hence
`B - 10δ = 261/5000`.

## The region this certificate covers

A fixed certificate validates exactly where its four block bounds sit under the four capacities,
and those are four affine inequalities in `(γ, ω₀)` — so the edges are active-set changes, not
samples. Writing them out:

* `c₀ ≥ 3079/10000` is `γ ≥ 3407/10000 + 8ω₀ + ϵ`, which is below `2/5 - ϵ` on the whole band, so
  the chamber's own floor binds and this cuts nothing.
* `c₁ ≥ 17/200` is `γ ≤ 83/200 - 2ω₀ - ϵ`. This is the binding edge in `γ`.
* `c₂ ≥ 1081/25000` is `ω₀ ≥ 671/100000 + ϵ/4`. This is the binding edge in `ω₀`.
* `c₃ ≥ 111/2500` is `ω₀ ≥ 111/20000`, weaker than the previous one.

So the certificate covers `671/100000 < ω₀ ≤ 7/1000` and `2/5 - ϵ ≤ γ ≤ 83/200 - 2ω₀ - ϵ`, a
two-dimensional region of the band and not a point. It is *not* the whole cell: the chamber allows
`γ` up to `1/3 + 8ω(1,1) + 7δ/3 + 3ϵ = 0.4276…`, and above `83/200 - 2ω₀ - ϵ` the second bin
overflows and a different certificate is needed. The `ω₀` floor `671/100000` is likewise real and
not an artifact — it is where `c₂` first admits two coordinates of the flat profile, and below it
this certificate genuinely fails.
-/

@[expose] public section

namespace Gap212

open Finset Gap212.Packing

/-! ## The certificate's rank sets -/

/-- The low group's rank sets for cell `(10,10)`: every rank into the first bin. -/
def cellTenLowRanks : Fin 4 → Finset (Fin 10) := ![Finset.univ, ∅, ∅, ∅]

/-- The high group's rank sets for cell `(10,10)`, in nonincreasing order of mass: ranks
`1,3,5,7` to the first bin, `0,2` to the second, `4,9` to the third, `6,8` to the fourth. -/
def cellTenHighRanks : Fin 4 → Finset (Fin 10) := ![{1, 3, 5, 7}, {0, 2}, {4, 9}, {6, 8}]

/-- The low group's prefix densities: `1` for the full set, `0` for the empty ones. -/
noncomputable def cellTenLowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The high group's prefix densities `1/2, 1, 1/5, 2/9`, each the maximum of `|S ∩ [0,j)| / j`
over `j ≤ 10` for the corresponding rank set. -/
noncomputable def cellTenHighDens : Fin 4 → ℝ := ![1 / 2, 1, 1 / 5, 2 / 9]

/-! ## The cell -/

/-! ### The low group's half, shared by all three certificates

Every certificate below puts all ten of the low group's ranks into the first bin, so these four
facts are proved once. -/

private theorem cellTenLow_cover : ∀ j : Fin 10, ∃ k, j ∈ cellTenLowRanks k := by decide

private theorem cellTenLow_disj : ∀ k l : Fin 4, k ≠ l →
    Disjoint (cellTenLowRanks k) (cellTenLowRanks l) := by
  intro k l hkl
  rw [Finset.disjoint_iff_inter_eq_empty]
  revert hkl; revert k l; decide

private theorem cellTenLow_dens_nonneg : ∀ k, 0 ≤ cellTenLowDens k := by
  intro k; fin_cases k <;> simp [cellTenLowDens]

private theorem cellTenLow_dens : ∀ k, ∀ j : ℕ,
    ((((cellTenLowRanks k).filter (fun i ↦ i.val < j)).card : ℕ) : ℝ)
      ≤ cellTenLowDens k * j := by
  intro k
  fin_cases k
  · exact fun j ↦ by
      simpa [cellTenLowRanks, cellTenLowDens] using
        prefixDensity_of_nat (𝕜 := ℝ) (cellTenLowRanks 0) 1 1 one_pos (by decide) j
  · exact fun j ↦ by simp [cellTenLowRanks, cellTenLowDens]
  · exact fun j ↦ by simp [cellTenLowRanks, cellTenLowDens]
  · exact fun j ↦ by simp [cellTenLowRanks, cellTenLowDens]

/-! ### Certificate A: the bottom of the `γ` range -/

/-- **Condition D's partition at cell `(10,10)`, on the top of the residual band.**

For `671/100000 + ϵ ≤ ω₀ ≤ 7/1000` and `2/5 - ϵ ≤ γ ≤ 83/200 - 2ω₀ - ϵ`, every profile of
`Ξ(B_{1,10}, B_{1,10}, 10, 10, δ)` admits a four-block partition meeting `Gap212.capD`'s
capacities, with least slack `10⁻³`, at the second bin.

The four block bounds are `3079/10000`, `17/200`, `1081/25000`, `111/2500`, against capacities
whose values at `γ = 2/5 - ϵ`, `ω₀ = 7/1000` are `3112/10000 - 2ϵ`, `86/1000`, `444/10000 - ϵ` and
`56/1000`. -/
theorem admitsPartition₄_cellTenTen {γ ω₀ : ℝ}
    (hωlo : 671 / 100000 + slack ≤ ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ) (hγhi : γ ≤ 83 / 200 - 2 * ω₀ - slack)
    {y : Fin (10 + 10) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    cellTenLowRanks cellTenHighRanks cellTenLow_cover cellTenLow_disj ?_ ?_
    cellTenLowDens cellTenHighDens cellTenLow_dens_nonneg ?_ cellTenLow_dens ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cellTenHighDens]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cellTenHighRanks, cellTenHighDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanks 0) 1 2 two_pos (by decide) j
    · exact fun j ↦ by
        simpa [cellTenHighRanks, cellTenHighDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanks 1) 1 1 one_pos (by decide) j
    · exact fun j ↦ by
        simpa [cellTenHighRanks, cellTenHighDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanks 2) 1 5 (by norm_num) (by decide) j
    · exact fun j ↦ by
        simpa [cellTenHighRanks, cellTenHighDens] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanks 3) 2 9 (by norm_num) (by decide) j
  · intro k
    fin_cases k <;>
      · simp [capD, cellTenLowRanks, cellTenHighRanks, cellTenLowDens, cellTenHighDens, hδ]
        linarith

/-! ### Certificates B and C: above the first uncovered window

Cell `(10,10)` is **not** closed by one sorted assignment. At `ω₀ = 7/1000` certificates A, B, C
and D below cover

    [2/5 - ϵ, 0.401 - ϵ] ∪ [0.4064 + ϵ, 0.42114 - ϵ] ∪ [0.4228 + ϵ, 0.4276]

of the chamber's `γ`-range and leave two windows uncovered. Certificate D is not redundant against
B even though its `γ` ceiling is higher at this `ω₀`: D's `ω₀` floor is `1371/200000 = 0.006855`
against B's `671/100000 = 0.00671`, so on `0.00671 ≤ ω₀ < 0.006855` only B applies.

The whole cell, over the whole band, is closed by a **cut** of the sorted cone instead:
`Gap212.admitsPartition₄_cellTenTen_band` in `Gap212.Packing.SortedCellCut`, whose instrument is
`Gap212.Packing.sum_mem_le_affine_of_antitone`. -/

/-- Certificate B's high-group rank sets, covering `γ` just above the first uncovered window. -/
def cellTenHighRanksB : Fin 4 → Finset (Fin 10) := ![{0, 1, 2}, {3, 5, 8}, {4, 9}, {6, 7}]

/-- Certificate B's high-group prefix densities `1, 1/3, 1/5, 1/4`. -/
noncomputable def cellTenHighDensB : Fin 4 → ℝ := ![1, 1 / 3, 1 / 5, 1 / 4]

/-- Certificate C's high-group rank sets, covering the top of the `γ` range including the
chamber's own ceiling `1/3 + 8ω(1,1) + 7δ/3 + 3ϵ = 0.4276…`. -/
def cellTenHighRanksC : Fin 4 → Finset (Fin 10) := ![{0, 1, 2, 3}, {4, 5}, {6, 9}, {7, 8}]

/-- Certificate C's high-group prefix densities `1, 1/3, 1/5, 2/9`. -/
noncomputable def cellTenHighDensC : Fin 4 → ℝ := ![1, 1 / 3, 1 / 5, 2 / 9]

/-- **Certificate B at cell `(10,10)`.** Block bounds `397/1250`, `333/5000`, `1081/25000`,
`917/20000`. Valid on `219/625 + 8ω₀ + ϵ ≤ γ ≤ 2167/5000 - 2ω₀ - ϵ` with
`671/100000 + ϵ ≤ ω₀`; at `ω₀ = 7/1000` that is `γ ∈ [0.4064 + ϵ, 0.4194 - ϵ]`. Its `γ`
floor is exactly the right endpoint of the first uncovered window, so nothing is lost between them.

The fourth bin's bound `917/20000` forces only `ω₀ ≥ 917/160000 = 0.00573`, weaker than the third
bin's `671/100000`, so the `ω₀` floor is the same as certificates A and C. Unlike certificate A
this one needs no band *ceiling*: its `γ` hypotheses carry `ω₀` explicitly, so it holds above
`7/1000` too, and stating `ω₀ ≤ 7/1000` would only narrow it. -/
theorem admitsPartition₄_cellTenTen_B {γ ω₀ : ℝ}
    (hωlo : 671 / 100000 + slack ≤ ω₀)
    (hγlo : 219 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2167 / 5000 - 2 * ω₀ - slack)
    {y : Fin (10 + 10) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    cellTenLowRanks cellTenHighRanksB cellTenLow_cover cellTenLow_disj ?_ ?_
    cellTenLowDens cellTenHighDensB cellTenLow_dens_nonneg ?_ cellTenLow_dens ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cellTenHighDensB]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cellTenHighRanksB, cellTenHighDensB] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanksB 0) 1 1 one_pos (by decide) j
    · exact fun j ↦ by
        simpa [cellTenHighRanksB, cellTenHighDensB] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanksB 1) 1 3 (by norm_num) (by decide) j
    · exact fun j ↦ by
        simpa [cellTenHighRanksB, cellTenHighDensB] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanksB 2) 1 5 (by norm_num) (by decide) j
    · exact fun j ↦ by
        simpa [cellTenHighRanksB, cellTenHighDensB] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanksB 3) 1 4 (by norm_num) (by decide) j
  · intro k
    fin_cases k <;>
      · simp [capD, cellTenLowRanks, cellTenHighRanksB, cellTenLowDens, cellTenHighDensB, hδ]
        linarith

/-- **Certificate C at cell `(10,10)`.** Block bounds `167/500`, `251/5000`, `1081/25000`,
`111/2500`. Valid on `917/2500 + 8ω₀ + ϵ ≤ γ ≤ 2249/5000 - 2ω₀ - ϵ` with
`671/100000 + ϵ ≤ ω₀`; at `ω₀ = 7/1000` that is `γ ∈ [0.4228 + ϵ, 0.4358 - ϵ]`, whose
upper end is above the chamber's own `γ` ceiling, so this certificate reaches the top corner of
the chamber. -/
theorem admitsPartition₄_cellTenTen_C {γ ω₀ : ℝ}
    (hωlo : 671 / 100000 + slack ≤ ω₀)
    (hγlo : 917 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2249 / 5000 - 2 * ω₀ - slack)
    {y : Fin (10 + 10) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    cellTenLowRanks cellTenHighRanksC cellTenLow_cover cellTenLow_disj ?_ ?_
    cellTenLowDens cellTenHighDensC cellTenLow_dens_nonneg ?_ cellTenLow_dens ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cellTenHighDensC]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cellTenHighRanksC, cellTenHighDensC] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanksC 0) 1 1 one_pos (by decide) j
    · exact fun j ↦ by
        simpa [cellTenHighRanksC, cellTenHighDensC] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanksC 1) 1 3 (by norm_num) (by decide) j
    · exact fun j ↦ by
        simpa [cellTenHighRanksC, cellTenHighDensC] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanksC 2) 1 5 (by norm_num) (by decide) j
    · exact fun j ↦ by
        simpa [cellTenHighRanksC, cellTenHighDensC] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanksC 3) 2 9 (by norm_num) (by decide) j
  · intro k
    fin_cases k <;>
      · simp [capD, cellTenLowRanks, cellTenHighRanksC, cellTenLowDens, cellTenHighDensC, hδ]
        linarith

/-! ### Certificate D: the stretch between B and the second uncovered window

This one does **not** share the low-group half above: it sends the low group's tenth rank to the
third bin at density `1/10`. Its `γ` ceiling `21757/50000 - 2ω₀ - ϵ` is `0.42114 - ϵ` at
`ω₀ = 7/1000`, exactly the left edge of the second uncovered window, which certificate B (ceiling
`0.4194 - ϵ`) does not reach. Its `ω₀` floor is `1371/200000 = 0.006855`, higher than the other
three, because its third bin carries `2191/50000` rather than `1081/25000`. -/

/-- Certificate D's low-group rank sets: the first nine ranks to the first bin, the tenth to the
third. -/
def cellTenLowRanksD : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3, 4, 5, 6, 7, 8}, ∅, {9}, ∅]

/-- Certificate D's low-group prefix densities `1, 0, 1/10, 0`. -/
noncomputable def cellTenLowDensD : Fin 4 → ℝ := ![1, 0, 1 / 10, 0]

/-- Certificate D's high-group rank sets. -/
def cellTenHighRanksD : Fin 4 → Finset (Fin 10) := ![{0, 1, 2, 3}, {4, 6, 9}, {8}, {5, 7}]

/-- Certificate D's high-group prefix densities `1, 3/10, 1/9, 1/4`. -/
noncomputable def cellTenHighDensD : Fin 4 → ℝ := ![1, 3 / 10, 1 / 9, 1 / 4]

/-- **Certificate D at cell `(10,10)`.** Block bounds `397/1250`, `3243/50000`, `2191/50000`,
`917/20000`. Valid on `219/625 + 8ω₀ + ϵ ≤ γ ≤ 21757/50000 - 2ω₀ - ϵ` with
`1371/200000 + ϵ ≤ ω₀`; at `ω₀ = 7/1000` that is `γ ∈ [0.4064 + ϵ, 0.42114 - ϵ]`. -/
theorem admitsPartition₄_cellTenTen_D {γ ω₀ : ℝ}
    (hωlo : 1371 / 200000 + slack ≤ ω₀)
    (hγlo : 219 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 21757 / 50000 - 2 * ω₀ - slack)
    {y : Fin (10 + 10) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine admitsPartition₄_of_rank_certificate hy (by norm_num)
    cellTenLowRanksD cellTenHighRanksD ?_ ?_ ?_ ?_
    cellTenLowDensD cellTenHighDensD ?_ ?_ ?_ ?_
    (fun k ↦ capD γ ω₀ k) ?_
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · decide
  · intro k l hkl
    rw [Finset.disjoint_iff_inter_eq_empty]
    revert hkl; revert k l; decide
  · intro k; fin_cases k <;> norm_num [cellTenLowDensD]
  · intro k; fin_cases k <;> norm_num [cellTenHighDensD]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cellTenLowRanksD, cellTenLowDensD] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenLowRanksD 0) 1 1 one_pos (by decide) j
    · exact fun j ↦ by simp [cellTenLowRanksD, cellTenLowDensD]
    · exact fun j ↦ by
        simpa [cellTenLowRanksD, cellTenLowDensD] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenLowRanksD 2) 1 10 (by norm_num) (by decide) j
    · exact fun j ↦ by simp [cellTenLowRanksD, cellTenLowDensD]
  · intro k
    fin_cases k
    · exact fun j ↦ by
        simpa [cellTenHighRanksD, cellTenHighDensD] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanksD 0) 1 1 one_pos (by decide) j
    · exact fun j ↦ by
        simpa [cellTenHighRanksD, cellTenHighDensD] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanksD 1) 3 10 (by norm_num) (by decide) j
    · exact fun j ↦ by
        simpa [cellTenHighRanksD, cellTenHighDensD] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanksD 2) 1 9 (by norm_num) (by decide) j
    · exact fun j ↦ by
        simpa [cellTenHighRanksD, cellTenHighDensD] using
          prefixDensity_of_nat (𝕜 := ℝ) (cellTenHighRanksD 3) 1 4 (by norm_num) (by decide) j
  · intro k
    fin_cases k <;>
      · simp [capD, cellTenLowRanksD, cellTenHighRanksD, cellTenLowDensD, cellTenHighDensD, hδ]
        linarith

/-- The hypotheses of `Gap212.admitsPartition₄_cellTenTen` are satisfiable: `ω₀ = 7/1000`,
`γ = 2/5` and the constant profile `δ = 41/2500` meet all of them. -/
theorem cellTenTen_hypotheses_satisfiable :
    671 / 100000 + slack ≤ (7 / 1000 : ℝ) ∧
      (2 / 5 - slack : ℝ) ≤ 2 / 5 ∧
      (2 / 5 : ℝ) ≤ 83 / 200 - 2 * (7 / 1000) - slack ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  refine ⟨by rw [hsv]; norm_num, by rw [hsv]; norm_num, by rw [hsv]; norm_num,
    fun i ↦ ⟨le_rfl, by norm_num⟩, ?_, ?_⟩
  · rw [Finset.sum_const, Gap212.Packing.card_lowGroup 10 10]
    norm_num
  · rw [Finset.sum_const, Gap212.Packing.card_highGroup 10 10]
    norm_num

/-- **The same cell, stated at the datum's own parameters**, so a consumer wiring this into
`Gap212.Defs.ConditionD` at `p_⋆` does not have to unfold the cap row: `gap212Params.B j 10` is
`gap212Cap 10 = 1081/5000` for every stratum `j`, and `gap212Params.δ` is `41/2500`. -/
theorem admitsPartition₄_cellTenTen_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n)
    (hωlo : 671 / 100000 + slack ≤ ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ) (hγhi : γ ≤ 83 / 200 - 2 * ω₀ - slack)
    {y : Fin (10 + 10) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 10) (gap212Params.B j' 10) 10 10 gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hB : ∀ i : Fin gap212Params.n, gap212Params.B i 10 = 1081 / 5000 := fun _ ↦
    gap212Cap_of_ten_le le_rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rw [hB j, hB j', hδ] at hy
  exact admitsPartition₄_cellTenTen hωlo hωhi hγlo hγhi hy

/-- **Certificates B and C have nonempty regions too**, and C's reaches the chamber's own `γ`
ceiling. Witnesses at `ω₀ = 7/1000 = ω(1,1)`: `γ = 41/100` for B, and for C the ceiling itself,
`γ = 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ = 3207/7500 + 3ϵ`, so the top corner of the chamber in both
coordinates is inside certificate C. The profile is again the constant one at the floor. -/
theorem cellTenTen_regions_nonempty :
    (219 / 625 + 8 * (7 / 1000 : ℝ) + slack ≤ 41 / 100 ∧
        (41 / 100 : ℝ) ≤ 2167 / 5000 - 2 * (7 / 1000) - slack) ∧
      (917 / 2500 + 8 * (7 / 1000 : ℝ) + slack ≤ 3207 / 7500 + 3 * slack ∧
        (3207 / 7500 + 3 * slack : ℝ) ≤ 2249 / 5000 - 2 * (7 / 1000) - slack) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  refine ⟨⟨by rw [hsv]; norm_num, by rw [hsv]; norm_num⟩,
    ⟨by rw [hsv]; norm_num, by rw [hsv]; norm_num⟩,
    fun i ↦ ⟨le_rfl, by norm_num⟩, ?_, ?_⟩
  · rw [Finset.sum_const, Gap212.Packing.card_lowGroup 10 10]
    norm_num
  · rw [Finset.sum_const, Gap212.Packing.card_highGroup 10 10]
    norm_num

/-- **Certificate D's region is nonempty**, at `ω₀ = 7/1000 = ω(1,1)` and `γ = 21/50`, with the
constant profile at the floor. Included separately from `Gap212.cellTenTen_regions_nonempty`
because D's `ω₀` floor is the higher `1371/200000`. -/
theorem cellTenTen_regionD_nonempty :
    1371 / 200000 + slack ≤ (7 / 1000 : ℝ) ∧
      219 / 625 + 8 * (7 / 1000 : ℝ) + slack ≤ 21 / 50 ∧
      (21 / 50 : ℝ) ≤ 21757 / 50000 - 2 * (7 / 1000) - slack ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈ Xi (1081 / 5000 : ℝ) (1081 / 5000) 10 10 (41 / 2500) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  refine ⟨by rw [hsv]; norm_num, by rw [hsv]; norm_num, by rw [hsv]; norm_num,
    fun i ↦ ⟨le_rfl, by norm_num⟩, ?_, ?_⟩
  · rw [Finset.sum_const, Gap212.Packing.card_lowGroup 10 10]
    norm_num
  · rw [Finset.sum_const, Gap212.Packing.card_highGroup 10 10]
    norm_num

end Gap212
