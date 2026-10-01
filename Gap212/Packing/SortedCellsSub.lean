/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCut
public import Gap212.Packing.SortedCell

/-!
# The cells the uncut reading covers on a sub-band only

`Gap212.Packing.SortedCellsUncut1` and its three siblings close 62 of the 91 cells with no
cut. Nine of the remaining twenty-nine are the cells the uncut reading covers on a *proper
sub-band* of `ω₀ ∈ (4/625, 7/1000]` and nowhere else. All nine are here:

    (1,3) at t = 73/1000  (3,7) at t = 7/200  (4,6) at t = 59/1000
    (4,8) at t = 3/100  (5,8) at t = 4/125  (6,9) at t = 13/500
    (7,10) at t = 7/250  (8,10) at t = 7/250  (9,10) at t = 4/125

Each closes the **whole** band and the whole chamber `γ`-range at the single threshold shown, by
`Gap212.Packing.admitsPartition₄_of_cut` on the second group's largest coordinate and a `γ` chain
of rank certificates on each half, as in the six cells of `Gap212.Packing.SortedCellsCut`.

## What this leaves of the 91

The uncut reading covers 62; `Gap212.Packing.SortedCellCut`, `SortedCellsCut`,
`SortedCellsGamma`, `SortedCellsMid` and `SortedCellsRest` carry 16; `SortedCellsPair` carries
`(6,8)`, `(8,9)` and `(9,9)`; `SortedCellsEight` carries `(8,8)` on two thresholds; and these nine
are the rest. Ordered pairs are handled once and for all by
`Gap212.Packing.admitsPartition₄_transpose_of`.
-/

@[expose] public section

namespace Gap212

open Finset Gap212.Packing

/-- The prefix checks of a rank certificate, from integer data that `decide` settles. -/
private theorem prefix_of_data {m₁ m₂ : ℕ} (T : Fin 4 → Finset (Fin m₁))
    (U : Fin 4 → Finset (Fin m₂)) (rp rq : Fin 4 → ℕ) (p a : Fin 4 → ℤ) (d : Fin 4 → ℕ)
    {r s q : Fin 4 → ℝ} (hrq : ∀ k, 0 < rq k) (hd : ∀ k, 0 < d k) (hp : ∀ k, 0 ≤ p k)
    (hT : ∀ k, ∀ j, j ≤ m₁ → rq k * ((T k).filter (fun i ↦ i.val < j)).card ≤ rp k * j)
    (hU : ∀ k, ∀ j : ℕ, j ≤ m₂ → 1 ≤ j →
      (((U k).filter (fun i ↦ i.val < j)).card : ℤ) * (d k : ℤ) ≤ p k * j + a k)
    (hreal : ∀ k, r k = rp k / rq k ∧ s k = p k / d k ∧ q k = a k / d k) :
    (∀ k, 0 ≤ r k) ∧ (∀ k, 0 ≤ s k) ∧
    (∀ k, ∀ j : ℕ, ((((T k).filter (fun i ↦ i.val < j)).card : ℕ) : ℝ) ≤ r k * j) ∧
    ∀ k, ∀ j : ℕ, 1 ≤ j → j ≤ m₂ →
      ((((U k).filter (fun i ↦ i.val < j)).card : ℕ) : ℝ) ≤ s k * j + q k := by
  refine ⟨fun k ↦ ?_, fun k ↦ ?_, fun k ↦ ?_, fun k ↦ ?_⟩ <;> obtain ⟨hr, hs, hq⟩ := hreal k
  · rw [hr]; positivity
  · rw [hs]; exact div_nonneg (by exact_mod_cast hp k) (Nat.cast_nonneg _)
  · rw [hr]; exact prefixDensity_of_nat (T k) (rp k) (rq k) (hrq k) (hT k)
  · rw [hs, hq]; exact prefixAffine_of_int (U k) (p k) (a k) (d k) (hd k) (hU k)

/-- The decidable half of a rank certificate: covers, disjointness, and the integer prefix
checks. -/
private abbrev CertData {m₁ m₂ : ℕ} (T : Fin 4 → Finset (Fin m₁)) (U : Fin 4 → Finset (Fin m₂))
    (rp rq : Fin 4 → ℕ) (p a : Fin 4 → ℤ) (d : Fin 4 → ℕ) : Prop :=
  (∀ j, ∃ k, j ∈ T k) ∧ (∀ k l, k ≠ l → Disjoint (T k) (T l)) ∧
    (∀ j, ∃ k, j ∈ U k) ∧ (∀ k l, k ≠ l → Disjoint (U k) (U l)) ∧
    (∀ k, 0 < rq k) ∧ (∀ k, 0 < d k) ∧ (∀ k, 0 ≤ p k) ∧
    (∀ k, ∀ j, j ≤ m₁ → rq k * ((T k).filter (fun i ↦ i.val < j)).card ≤ rp k * j) ∧
    ∀ k, ∀ j : ℕ, j ≤ m₂ → 1 ≤ j →
      (((U k).filter (fun i ↦ i.val < j)).card : ℤ) * (d k : ℤ) ≤ p k * j + a k

/-- `Gap212.Packing.admitsPartition₄_of_rank_certificate_cut_low`, with the slopes and
constants given as fractions of integers and the combinatorial checks bundled for `decide`. -/
private theorem cut_low_of_data {m₁ m₂ : ℕ} (hm₂ : 0 < m₂) {B₁ B₂ δ t : ℝ}
    {y : Fin (m₁ + m₂) → ℝ} (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) (hδ : 0 ≤ δ)
    (hcut : ∀ i : Fin (m₁ + m₂), m₁ ≤ (i : ℕ) → y i ≤ t)
    (T : Fin 4 → Finset (Fin m₁)) (U : Fin 4 → Finset (Fin m₂))
    (rp rq : Fin 4 → ℕ) (p a : Fin 4 → ℤ) (d : Fin 4 → ℕ)
    (hdec : CertData T U rp rq p a d ∧ ∀ k, 0 ≤ a k)
    (r s q : Fin 4 → ℝ) (hreal : ∀ k, r k = rp k / rq k ∧ s k = p k / d k ∧ q k = a k / d k)
    (c : Fin 4 → ℝ)
    (hcap : ∀ k, ((((T k).card : ℕ) : ℝ) * δ + r k * (B₁ - (m₁ : ℝ) * δ))
        + ((((U k).card : ℕ) : ℝ) * δ + s k * (B₂ - (m₂ : ℝ) * δ) + q k * (t - δ)) ≤ c k) :
    AdmitsPartition₄ y (c 0) (c 1) (c 2) (c 3) := by
  obtain ⟨⟨hTc, hTd, hUc, hUd, hrq, hd, hp, hT, hU⟩, ha⟩ := hdec
  obtain ⟨hr0, hs0, hr, hs⟩ := prefix_of_data T U rp rq p a d hrq hd hp hT hU hreal
  refine admitsPartition₄_of_rank_certificate_cut_low hm₂ hy hδ hcut T U hTc hTd hUc hUd r s q
    hr0 hs0 (fun k ↦ ?_) hr hs c hcap
  rw [(hreal k).2.2]
  exact div_nonneg (by exact_mod_cast ha k) (Nat.cast_nonneg _)

/-- `Gap212.Packing.admitsPartition₄_of_rank_certificate_cut_high`, with the slopes and
constants given as fractions of integers and the combinatorial checks bundled for `decide`. -/
private theorem cut_high_of_data {m₁ m₂ : ℕ} (hm₂ : 0 < m₂) {B₁ B₂ δ t : ℝ}
    {y : Fin (m₁ + m₂) → ℝ} (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) (hδ : 0 ≤ δ)
    (hcut : ∃ i : Fin (m₁ + m₂), m₁ ≤ (i : ℕ) ∧ t ≤ y i)
    (T : Fin 4 → Finset (Fin m₁)) (U : Fin 4 → Finset (Fin m₂))
    (rp rq : Fin 4 → ℕ) (p a : Fin 4 → ℤ) (d : Fin 4 → ℕ)
    (hdec : CertData T U rp rq p a d ∧ ∀ k, a k ≤ 0)
    (r s q : Fin 4 → ℝ) (hreal : ∀ k, r k = rp k / rq k ∧ s k = p k / d k ∧ q k = a k / d k)
    (c : Fin 4 → ℝ)
    (hcap : ∀ k, ((((T k).card : ℕ) : ℝ) * δ + r k * (B₁ - (m₁ : ℝ) * δ))
        + ((((U k).card : ℕ) : ℝ) * δ + s k * (B₂ - (m₂ : ℝ) * δ) + q k * (t - δ)) ≤ c k) :
    AdmitsPartition₄ y (c 0) (c 1) (c 2) (c 3) := by
  obtain ⟨⟨hTc, hTd, hUc, hUd, hrq, hd, hp, hT, hU⟩, ha⟩ := hdec
  obtain ⟨hr0, hs0, hr, hs⟩ := prefix_of_data T U rp rq p a d hrq hd hp hT hU hreal
  refine admitsPartition₄_of_rank_certificate_cut_high hm₂ hy hδ hcut T U hTc hTd hUc hUd r s q
    hr0 hs0 (fun k ↦ ?_) hr hs c hcap
  rw [(hreal k).2.2]
  exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast ha k) (Nat.cast_nonneg _)

/-- A profile at the datum's own parameters, with the two cap values read off. -/
private theorem xi_atDatum {m n : ℕ} {B₁ B₂ : ℝ} (j j' : Fin gap212Params.n)
    (h₁ : gap212Cap m = B₁) (h₂ : gap212Cap n = B₂) {y : Fin (m + n) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j m) (gap212Params.B j' n) m n gap212Params.δ) :
    y ∈ Xi B₁ B₂ m n (41 / 2500) :=
  h₁ ▸ h₂ ▸ hy


/-! ## Cell `(1,3)` -/

/-- The first group's rank sets for cell `(1,3)`, the low half's certificate 1. -/
def cutOneThreeUnder₁LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutOneThreeUnder₁LowRanks`. -/
noncomputable def cutOneThreeUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,3)`, the low half's certificate 1. -/
def cutOneThreeUnder₁Ranks : Fin 4 → Finset (Fin 3) :=
  ![{0, 1}, {2}, ∅, ∅]

/-- The slopes of `Gap212.cutOneThreeUnder₁Ranks`. -/
noncomputable def cutOneThreeUnder₁Dens : Fin 4 → ℝ := ![0, 1 / 3, 0, 0]

/-- The constants of `Gap212.cutOneThreeUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutOneThreeUnder₁Const : Fin 4 → ℝ := ![2, 0, 0, 0]

/-- The first group's rank sets for cell `(1,3)`, the high half's certificate 1. -/
def cutOneThreeOver₁LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutOneThreeOver₁LowRanks`. -/
noncomputable def cutOneThreeOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,3)`, the high half's certificate 1. -/
def cutOneThreeOver₁Ranks : Fin 4 → Finset (Fin 3) :=
  ![{0}, {1}, ∅, {2}]

/-- The slopes of `Gap212.cutOneThreeOver₁Ranks`. -/
noncomputable def cutOneThreeOver₁Dens : Fin 4 → ℝ := ![1, 1 / 2, 0, 1 / 2]

/-- The constants of `Gap212.cutOneThreeOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutOneThreeOver₁Const : Fin 4 → ℝ := ![0, 0, 0, -1 / 2]

/-- The first group's rank sets for cell `(1,3)`, the high half's certificate 2. -/
def cutOneThreeOver₂LowRanks : Fin 4 → Finset (Fin 1) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutOneThreeOver₂LowRanks`. -/
noncomputable def cutOneThreeOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(1,3)`, the high half's certificate 2. -/
def cutOneThreeOver₂Ranks : Fin 4 → Finset (Fin 3) :=
  ![{0, 1}, ∅, ∅, {2}]

/-- The slopes of `Gap212.cutOneThreeOver₂Ranks`. -/
noncomputable def cutOneThreeOver₂Dens : Fin 4 → ℝ := ![1, 0, 0, 1 / 2]

/-- The constants of `Gap212.cutOneThreeOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutOneThreeOver₂Const : Fin 4 → ℝ := ![0, 0, 0, -1 / 2]

/-- **Cell `(1,3)`, the low half's certificate 1.**

Block bounds `1507 / 5000`, `7 / 120`, `0`, `0`.
Valid on `4 / 625 < ω₀` and on
`1671 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 53 / 120 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3902000 + ϵ, 0.4276667 - ϵ]`. The cut is at `t = 73 / 1000`. -/
theorem admitsPartition₄_cellOneThree_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1671 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 53 / 120 - 2 * ω₀ - slack)
    {y : Fin (1 + 3) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (7 / 40) 1 3 (41 / 2500))
    (hcut : ∀ i : Fin (1 + 3), 1 ≤ (i : ℕ) → y i ≤ 73 / 1000) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_data (by norm_num) hy (by norm_num) hcut cutOneThreeUnder₁LowRanks
    cutOneThreeUnder₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![0, 1, 0, 0] ![2, 0, 0, 0] ![1, 3, 1, 1]
    (by decide) cutOneThreeUnder₁LowDens cutOneThreeUnder₁Dens cutOneThreeUnder₁Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutOneThreeUnder₁LowRanks,
    cutOneThreeUnder₁Ranks, cutOneThreeUnder₁LowDens, cutOneThreeUnder₁Dens, cutOneThreeUnder₁Const]
    <;> linarith

/-- **Cell `(1,3)`, the high half's certificate 1.**

Block bounds `186 / 625`, `793 / 10000`, `0`, `51 / 1000`.
Valid on `4 / 625 < ω₀` and on
`413 / 1250 + 8ω₀ + ϵ ≤ γ ≤ 4207 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3864000 + ϵ, 0.4067000 - ϵ]`. The cut is at `t = 73 / 1000`. -/
theorem admitsPartition₄_cellOneThree_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 413 / 1250 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4207 / 10000 - 2 * ω₀ - slack)
    {y : Fin (1 + 3) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (7 / 40) 1 3 (41 / 2500))
    (hcut : ∃ i : Fin (1 + 3), 1 ≤ (i : ℕ) ∧ 73 / 1000 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutOneThreeOver₁LowRanks
    cutOneThreeOver₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 0, 1] ![0, 0, 0, -1] ![1, 2, 1, 2]
    (by decide) cutOneThreeOver₁LowDens cutOneThreeOver₁Dens cutOneThreeOver₁Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutOneThreeOver₁LowRanks,
    cutOneThreeOver₁Ranks, cutOneThreeOver₁LowDens, cutOneThreeOver₁Dens, cutOneThreeOver₁Const] <;>
    linarith

/-- **Cell `(1,3)`, the high half's certificate 2.**

Block bounds `157 / 500`, `0`, `0`, `51 / 1000`.
Valid on `4 / 625 < ω₀` and on
`867 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 1 / 2 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4028000 + ϵ, 0.4860000 - ϵ]`. The cut is at `t = 73 / 1000`. -/
theorem admitsPartition₄_cellOneThree_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 867 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 1 / 2 - 2 * ω₀ - slack)
    {y : Fin (1 + 3) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (7 / 40) 1 3 (41 / 2500))
    (hcut : ∃ i : Fin (1 + 3), 1 ≤ (i : ℕ) ∧ 73 / 1000 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutOneThreeOver₂LowRanks
    cutOneThreeOver₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 0, 0, 1] ![0, 0, 0, -1] ![1, 1, 1, 2]
    (by decide) cutOneThreeOver₂LowDens cutOneThreeOver₂Dens cutOneThreeOver₂Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutOneThreeOver₂LowRanks,
    cutOneThreeOver₂Ranks, cutOneThreeOver₂LowDens, cutOneThreeOver₂Dens, cutOneThreeOver₂Const] <;>
    linarith

/-- **Cell `(1,3)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,1}, B_{1,3}, 1, 3, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 73 / 1000`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellOneThree_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 3) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (7 / 40) 1 3 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  rw [show gap212Params.δ = 41 / 2500 from rfl] at hγhi
  refine admitsPartition₄_of_cut (t := 73 / 1000) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · exact admitsPartition₄_cellOneThree_under₁ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (4207 / 10000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellOneThree_over₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellOneThree_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(1,3)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellOneThree_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (1 + 3) → ℝ}
    (hy : y ∈ Xi (777 / 5000 : ℝ) (7 / 40) 1 3 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellOneThree_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(1,3)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 1 = gap212Cap 1 = 777 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellOneThree_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (1 + 3) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 1) (gap212Params.B j' 3) 1 3
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellOneThree_band hωlo hωhi hγlo hγhi
    (xi_atDatum j j' (by norm_num [gap212Cap]) (by norm_num [gap212Cap]) hy)

/-! ## Cell `(3,7)` -/

/-- The first group's rank sets for cell `(3,7)`, the low half's certificate 1. -/
def cutThreeSevenUnder₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutThreeSevenUnder₁LowRanks`. -/
noncomputable def cutThreeSevenUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,7)`, the low half's certificate 1. -/
def cutThreeSevenUnder₁Ranks : Fin 4 → Finset (Fin 7) :=
  ![{1, 2, 4, 5}, {6}, {0}, {3}]

/-- The slopes of `Gap212.cutThreeSevenUnder₁Ranks`. -/
noncomputable def cutThreeSevenUnder₁Dens : Fin 4 → ℝ := ![2 / 3, 1 / 7, 0, 0]

/-- The constants of `Gap212.cutThreeSevenUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutThreeSevenUnder₁Const : Fin 4 → ℝ := ![0, 0, 1, 1]

/-- The first group's rank sets for cell `(3,7)`, the high half's certificate 1. -/
def cutThreeSevenOver₁LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutThreeSevenOver₁LowRanks`. -/
noncomputable def cutThreeSevenOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,7)`, the high half's certificate 1. -/
def cutThreeSevenOver₁Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1}, {2, 4, 6}, {5}, {3}]

/-- The slopes of `Gap212.cutThreeSevenOver₁Ranks`. -/
noncomputable def cutThreeSevenOver₁Dens : Fin 4 → ℝ := ![1, 1 / 2, 1 / 5, 1 / 4]

/-- The constants of `Gap212.cutThreeSevenOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutThreeSevenOver₁Const : Fin 4 → ℝ := ![0, -1 / 2, -1 / 5, 0]

/-- The first group's rank sets for cell `(3,7)`, the high half's certificate 2. -/
def cutThreeSevenOver₂LowRanks : Fin 4 → Finset (Fin 3) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutThreeSevenOver₂LowRanks`. -/
noncomputable def cutThreeSevenOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(3,7)`, the high half's certificate 2. -/
def cutThreeSevenOver₂Ranks : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2}, {3, 6}, {5}, {4}]

/-- The slopes of `Gap212.cutThreeSevenOver₂Ranks`. -/
noncomputable def cutThreeSevenOver₂Dens : Fin 4 → ℝ := ![1, 1 / 3, 1 / 5, 1 / 4]

/-- The constants of `Gap212.cutThreeSevenOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutThreeSevenOver₂Const : Fin 4 → ℝ := ![0, -1 / 3, -1 / 5, -1 / 4]

/-- **Cell `(3,7)`, the low half's certificate 1.**

Block bounds `4493 / 15000`, `127 / 4375`, `7 / 200`, `7 / 200`.
Valid on `4 / 625 < ω₀` and on
`997 / 3000 + 8ω₀ + ϵ ≤ γ ≤ 4121 / 8750 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3883333 + ϵ, 0.4569714 - ϵ]`. The cut is at `t = 7 / 200`. -/
theorem admitsPartition₄_cellThreeSeven_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 997 / 3000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4121 / 8750 - 2 * ω₀ - slack)
    {y : Fin (3 + 7) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (127 / 625) 3 7 (41 / 2500))
    (hcut : ∀ i : Fin (3 + 7), 3 ≤ (i : ℕ) → y i ≤ 7 / 200) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_data (by norm_num) hy (by norm_num) hcut cutThreeSevenUnder₁LowRanks
    cutThreeSevenUnder₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![2, 1, 0, 0] ![0, 0, 1, 1] ![3, 7, 1, 1]
    (by decide) cutThreeSevenUnder₁LowDens cutThreeSevenUnder₁Dens cutThreeSevenUnder₁Const
    (fun k ↦ ?_) (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutThreeSevenUnder₁LowRanks,
    cutThreeSevenUnder₁Ranks, cutThreeSevenUnder₁LowDens, cutThreeSevenUnder₁Dens,
    cutThreeSevenUnder₁Const] <;> linarith

/-- **Cell `(3,7)`, the high half's certificate 1.**

Block bounds `1481 / 5000`, `841 / 10000`, `759 / 25000`, `77 / 2000`.
Valid on `4 / 625 < ω₀` and on
`329 / 1000 + 8ω₀ + ϵ ≤ γ ≤ 4159 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3850000 + ϵ, 0.4019000 - ϵ]`. The cut is at `t = 7 / 200`. -/
theorem admitsPartition₄_cellThreeSeven_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 329 / 1000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4159 / 10000 - 2 * ω₀ - slack)
    {y : Fin (3 + 7) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (127 / 625) 3 7 (41 / 2500))
    (hcut : ∃ i : Fin (3 + 7), 3 ≤ (i : ℕ) ∧ 7 / 200 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutThreeSevenOver₁LowRanks
    cutThreeSevenOver₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 1, 1] ![0, -1, -1, 0] ![1, 2, 5, 4]
    (by decide) cutThreeSevenOver₁LowDens cutThreeSevenOver₁Dens cutThreeSevenOver₁Const
    (fun k ↦ ?_) (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutThreeSevenOver₁LowRanks,
    cutThreeSevenOver₁Ranks, cutThreeSevenOver₁LowDens, cutThreeSevenOver₁Dens,
    cutThreeSevenOver₁Const] <;> linarith

/-- **Cell `(3,7)`, the high half's certificate 2.**

Block bounds `1563 / 5000`, `841 / 15000`, `759 / 25000`, `677 / 20000`.
Valid on `4 / 625 < ω₀` and on
`1727 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 6659 / 15000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4014000 + ϵ, 0.4299333 - ϵ]`. The cut is at `t = 7 / 200`. -/
theorem admitsPartition₄_cellThreeSeven_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1727 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 6659 / 15000 - 2 * ω₀ - slack)
    {y : Fin (3 + 7) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (127 / 625) 3 7 (41 / 2500))
    (hcut : ∃ i : Fin (3 + 7), 3 ≤ (i : ℕ) ∧ 7 / 200 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutThreeSevenOver₂LowRanks
    cutThreeSevenOver₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 1, 1] ![0, -1, -1, -1] ![1, 3, 5, 4]
    (by decide) cutThreeSevenOver₂LowDens cutThreeSevenOver₂Dens cutThreeSevenOver₂Const
    (fun k ↦ ?_) (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutThreeSevenOver₂LowRanks,
    cutThreeSevenOver₂Ranks, cutThreeSevenOver₂LowDens, cutThreeSevenOver₂Dens,
    cutThreeSevenOver₂Const] <;> linarith

/-- **Cell `(3,7)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,3}, B_{1,7}, 3, 7, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 7 / 200`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellThreeSeven_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 7) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (127 / 625) 3 7 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  rw [show gap212Params.δ = 41 / 2500 from rfl] at hγhi
  refine admitsPartition₄_of_cut (t := 7 / 200) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · exact admitsPartition₄_cellThreeSeven_under₁ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (4159 / 10000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellThreeSeven_over₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellThreeSeven_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(3,7)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellThreeSeven_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (3 + 7) → ℝ}
    (hy : y ∈ Xi (7 / 40 : ℝ) (127 / 625) 3 7 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellThreeSeven_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(3,7)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 3 = gap212Cap 3 = 7 / 40` at every stratum `j`. -/
theorem admitsPartition₄_cellThreeSeven_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (3 + 7) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 3) (gap212Params.B j' 7) 3 7
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellThreeSeven_band hωlo hωhi hγlo hγhi
    (xi_atDatum j j' (by norm_num [gap212Cap]) (by norm_num [gap212Cap]) hy)

/-! ## Cell `(4,6)` -/

/-- The first group's rank sets for cell `(4,6)`, the low half's certificate 1. -/
def cutFourSixUnder₁LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFourSixUnder₁LowRanks`. -/
noncomputable def cutFourSixUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,6)`, the low half's certificate 1. -/
def cutFourSixUnder₁Ranks : Fin 4 → Finset (Fin 6) :=
  ![{1, 3, 5}, {0}, {4}, {2}]

/-- The slopes of `Gap212.cutFourSixUnder₁Ranks`. -/
noncomputable def cutFourSixUnder₁Dens : Fin 4 → ℝ := ![1 / 2, 0, 1 / 5, 1 / 3]

/-- The constants of `Gap212.cutFourSixUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutFourSixUnder₁Const : Fin 4 → ℝ := ![0, 1, 0, 0]

/-- The first group's rank sets for cell `(4,6)`, the low half's certificate 2. -/
def cutFourSixUnder₂LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFourSixUnder₂LowRanks`. -/
noncomputable def cutFourSixUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,6)`, the low half's certificate 2. -/
def cutFourSixUnder₂Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 4}, {5}, {3}, {2}]

/-- The slopes of `Gap212.cutFourSixUnder₂Ranks`. -/
noncomputable def cutFourSixUnder₂Dens : Fin 4 → ℝ := ![1 / 3, 1 / 6, 1 / 4, 1 / 3]

/-- The constants of `Gap212.cutFourSixUnder₂Ranks`, nonnegative throughout. -/
noncomputable def cutFourSixUnder₂Const : Fin 4 → ℝ := ![4 / 3, 0, 0, 0]

/-- The first group's rank sets for cell `(4,6)`, the high half's certificate 1. -/
def cutFourSixOver₁LowRanks : Fin 4 → Finset (Fin 4) :=
  ![{0, 1, 2}, ∅, ∅, {3}]

/-- The prefix densities of `Gap212.cutFourSixOver₁LowRanks`. -/
noncomputable def cutFourSixOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 1 / 4]

/-- The second group's rank sets for cell `(4,6)`, the high half's certificate 1. -/
def cutFourSixOver₁Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1}, {2, 4, 5}, {3}, ∅]

/-- The slopes of `Gap212.cutFourSixOver₁Ranks`. -/
noncomputable def cutFourSixOver₁Dens : Fin 4 → ℝ := ![1, 3 / 5, 1 / 3, 0]

/-- The constants of `Gap212.cutFourSixOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutFourSixOver₁Const : Fin 4 → ℝ := ![0, -3 / 5, -1 / 3, 0]

/-- The first group's rank sets for cell `(4,6)`, the high half's certificate 2. -/
def cutFourSixOver₂LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFourSixOver₂LowRanks`. -/
noncomputable def cutFourSixOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,6)`, the high half's certificate 2. -/
def cutFourSixOver₂Ranks : Fin 4 → Finset (Fin 6) :=
  ![{0, 1}, {3, 5}, {4}, {2}]

/-- The slopes of `Gap212.cutFourSixOver₂Ranks`. -/
noncomputable def cutFourSixOver₂Dens : Fin 4 → ℝ := ![1, 2 / 5, 1 / 4, 1 / 2]

/-- The constants of `Gap212.cutFourSixOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutFourSixOver₂Const : Fin 4 → ℝ := ![0, -2 / 5, -1 / 4, -1 / 2]

/-- **Cell `(4,6)`, the low half's certificate 1.**

Block bounds `2817 / 10000`, `59 / 1000`, `901 / 25000`, `737 / 15000`.
Valid on `4 / 625 < ω₀` and on
`629 / 2000 + 8ω₀ + ϵ ≤ γ ≤ 441 / 1000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3705000 + ϵ, 0.4270000 - ϵ]`. The cut is at `t = 59 / 1000`. -/
theorem admitsPartition₄_cellFourSix_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 629 / 2000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 441 / 1000 - 2 * ω₀ - slack)
    {y : Fin (4 + 6) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (983 / 5000) 4 6 (41 / 2500))
    (hcut : ∀ i : Fin (4 + 6), 4 ≤ (i : ℕ) → y i ≤ 59 / 1000) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_data (by norm_num) hy (by norm_num) hcut cutFourSixUnder₁LowRanks
    cutFourSixUnder₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 0, 1, 1] ![0, 1, 0, 0] ![2, 1, 5, 3]
    (by decide) cutFourSixUnder₁LowDens cutFourSixUnder₁Dens cutFourSixUnder₁Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutFourSixUnder₁LowRanks,
    cutFourSixUnder₁Ranks, cutFourSixUnder₁LowDens, cutFourSixUnder₁Dens, cutFourSixUnder₁Const] <;>
    linarith

/-- **Cell `(4,6)`, the low half's certificate 2.**

Block bounds `604 / 1875`, `983 / 30000`, `819 / 20000`, `737 / 15000`.
Valid on `4 / 625 < ω₀` and on
`1331 / 3750 + 8ω₀ + ϵ ≤ γ ≤ 14017 / 30000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4109333 + ϵ, 0.4532333 - ϵ]`. The cut is at `t = 59 / 1000`. -/
theorem admitsPartition₄_cellFourSix_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1331 / 3750 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 14017 / 30000 - 2 * ω₀ - slack)
    {y : Fin (4 + 6) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (983 / 5000) 4 6 (41 / 2500))
    (hcut : ∀ i : Fin (4 + 6), 4 ≤ (i : ℕ) → y i ≤ 59 / 1000) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_data (by norm_num) hy (by norm_num) hcut cutFourSixUnder₂LowRanks
    cutFourSixUnder₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 1, 1] ![4, 0, 0, 0] ![3, 6, 4, 3]
    (by decide) cutFourSixUnder₂LowDens cutFourSixUnder₂Dens cutFourSixUnder₂Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutFourSixUnder₂LowRanks,
    cutFourSixUnder₂Ranks, cutFourSixUnder₂LowDens, cutFourSixUnder₂Dens, cutFourSixUnder₂Const] <;>
    linarith

/-- **Cell `(4,6)`, the high half's certificate 1.**

Block bounds `149 / 500`, `258 / 3125`, `131 / 3750`, `917 / 20000`.
Valid on `4 / 625 < ω₀` and on
`827 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 2609 / 6250 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3868000 + ϵ, 0.4034400 - ϵ]`. The cut is at `t = 59 / 1000`. -/
theorem admitsPartition₄_cellFourSix_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 827 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2609 / 6250 - 2 * ω₀ - slack)
    {y : Fin (4 + 6) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (983 / 5000) 4 6 (41 / 2500))
    (hcut : ∃ i : Fin (4 + 6), 4 ≤ (i : ℕ) ∧ 59 / 1000 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutFourSixOver₁LowRanks
    cutFourSixOver₁Ranks ![1, 0, 0, 1] ![1, 1, 1, 4] ![1, 3, 1, 0] ![0, -3, -1, 0] ![1, 5, 3, 1]
    (by decide) cutFourSixOver₁LowDens cutFourSixOver₁Dens cutFourSixOver₁Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutFourSixOver₁LowRanks,
    cutFourSixOver₁Ranks, cutFourSixOver₁LowDens, cutFourSixOver₁Dens, cutFourSixOver₁Const] <;>
    linarith

/-- **Cell `(4,6)`, the high half's certificate 2.**

Block bounds `393 / 1250`, `172 / 3125`, `303 / 10000`, `221 / 5000`.
Valid on `4 / 625 < ω₀` and on
`217 / 625 + 8ω₀ + ϵ ≤ γ ≤ 2781 / 6250 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4032000 + ϵ, 0.4309600 - ϵ]`. The cut is at `t = 59 / 1000`. -/
theorem admitsPartition₄_cellFourSix_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 217 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2781 / 6250 - 2 * ω₀ - slack)
    {y : Fin (4 + 6) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (983 / 5000) 4 6 (41 / 2500))
    (hcut : ∃ i : Fin (4 + 6), 4 ≤ (i : ℕ) ∧ 59 / 1000 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutFourSixOver₂LowRanks
    cutFourSixOver₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 2, 1, 1] ![0, -2, -1, -1] ![1, 5, 4, 2]
    (by decide) cutFourSixOver₂LowDens cutFourSixOver₂Dens cutFourSixOver₂Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutFourSixOver₂LowRanks,
    cutFourSixOver₂Ranks, cutFourSixOver₂LowDens, cutFourSixOver₂Dens, cutFourSixOver₂Const] <;>
    linarith

/-- **Cell `(4,6)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,4}, B_{1,6}, 4, 6, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 59 / 1000`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellFourSix_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 6) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (983 / 5000) 4 6 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  rw [show gap212Params.δ = 41 / 2500 from rfl] at hγhi
  refine admitsPartition₄_of_cut (t := 59 / 1000) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · rcases le_or_gt γ (441 / 1000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellFourSix_under₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellFourSix_under₂ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (2609 / 6250 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellFourSix_over₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellFourSix_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(4,6)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellFourSix_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (4 + 6) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (983 / 5000) 4 6 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellFourSix_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(4,6)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 4 = gap212Cap 4 = 917 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFourSix_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 6) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 4) (gap212Params.B j' 6) 4 6
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellFourSix_band hωlo hωhi hγlo hγhi
    (xi_atDatum j j' (by norm_num [gap212Cap]) (by norm_num [gap212Cap]) hy)

/-! ## Cell `(4,8)` -/

/-- The first group's rank sets for cell `(4,8)`, the low half's certificate 1. -/
def cutFourEightUnder₁LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFourEightUnder₁LowRanks`. -/
noncomputable def cutFourEightUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,8)`, the low half's certificate 1. -/
def cutFourEightUnder₁Ranks : Fin 4 → Finset (Fin 8) :=
  ![{1, 3, 5, 6}, {4, 7}, {0}, {2}]

/-- The slopes of `Gap212.cutFourEightUnder₁Ranks`. -/
noncomputable def cutFourEightUnder₁Dens : Fin 4 → ℝ := ![4 / 7, 1 / 4, 0, 0]

/-- The constants of `Gap212.cutFourEightUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutFourEightUnder₁Const : Fin 4 → ℝ := ![0, 0, 1, 1]

/-- The first group's rank sets for cell `(4,8)`, the high half's certificate 1. -/
def cutFourEightOver₁LowRanks : Fin 4 → Finset (Fin 4) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFourEightOver₁LowRanks`. -/
noncomputable def cutFourEightOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(4,8)`, the high half's certificate 1. -/
def cutFourEightOver₁Ranks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1, 2}, {3, 6}, {5}, {4, 7}]

/-- The slopes of `Gap212.cutFourEightOver₁Ranks`. -/
noncomputable def cutFourEightOver₁Dens : Fin 4 → ℝ := ![1, 1 / 3, 1 / 5, 2 / 7]

/-- The constants of `Gap212.cutFourEightOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutFourEightOver₁Const : Fin 4 → ℝ := ![0, -1 / 3, -1 / 5, -2 / 7]

/-- **Cell `(4,8)`, the low half's certificate 1.**

Block bounds `10259 / 35000`, `521 / 10000`, `3 / 100`, `3 / 100`.
Valid on `4 / 625 < ω₀` and on
`11407 / 35000 + 8ω₀ + ϵ ≤ γ ≤ 4479 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3819143 + ϵ, 0.4339000 - ϵ]`. The cut is at `t = 3 / 100`. -/
theorem admitsPartition₄_cellFourEight_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 11407 / 35000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4479 / 10000 - 2 * ω₀ - slack)
    {y : Fin (4 + 8) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (521 / 2500) 4 8 (41 / 2500))
    (hcut : ∀ i : Fin (4 + 8), 4 ≤ (i : ℕ) → y i ≤ 3 / 100) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_data (by norm_num) hy (by norm_num) hcut cutFourEightUnder₁LowRanks
    cutFourEightUnder₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![4, 1, 0, 0] ![0, 0, 1, 1] ![7, 4, 1, 1]
    (by decide) cutFourEightUnder₁LowDens cutFourEightUnder₁Dens cutFourEightUnder₁Const
    (fun k ↦ ?_) (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutFourEightUnder₁LowRanks,
    cutFourEightUnder₁Ranks, cutFourEightUnder₁LowDens, cutFourEightUnder₁Dens,
    cutFourEightUnder₁Const] <;> linarith

/-- **Cell `(4,8)`, the high half's certificate 1.**

Block bounds `1549 / 5000`, `27 / 500`, `91 / 3125`, `223 / 4375`.
Valid on `4 / 625 < ω₀` and on
`1713 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 223 / 500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3986000 + ϵ, 0.4320000 - ϵ]`. The cut is at `t = 3 / 100`. -/
theorem admitsPartition₄_cellFourEight_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1713 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 223 / 500 - 2 * ω₀ - slack)
    {y : Fin (4 + 8) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (521 / 2500) 4 8 (41 / 2500))
    (hcut : ∃ i : Fin (4 + 8), 4 ≤ (i : ℕ) ∧ 3 / 100 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutFourEightOver₁LowRanks
    cutFourEightOver₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 1, 2] ![0, -1, -1, -2] ![1, 3, 5, 7]
    (by decide) cutFourEightOver₁LowDens cutFourEightOver₁Dens cutFourEightOver₁Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutFourEightOver₁LowRanks,
    cutFourEightOver₁Ranks, cutFourEightOver₁LowDens, cutFourEightOver₁Dens, cutFourEightOver₁Const]
    <;> linarith

/-- **Cell `(4,8)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,4}, B_{1,8}, 4, 8, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 3 / 100`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellFourEight_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 8) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (521 / 2500) 4 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  rw [show gap212Params.δ = 41 / 2500 from rfl] at hγhi
  refine admitsPartition₄_of_cut (t := 3 / 100) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · exact admitsPartition₄_cellFourEight_under₁ hωlo (by linarith) (by linarith) hy hcut
  · exact admitsPartition₄_cellFourEight_over₁ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(4,8)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellFourEight_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (4 + 8) → ℝ}
    (hy : y ∈ Xi (917 / 5000 : ℝ) (521 / 2500) 4 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellFourEight_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(4,8)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 4 = gap212Cap 4 = 917 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFourEight_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (4 + 8) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 4) (gap212Params.B j' 8) 4 8
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellFourEight_band hωlo hωhi hγlo hγhi
    (xi_atDatum j j' (by norm_num [gap212Cap]) (by norm_num [gap212Cap]) hy)

/-! ## Cell `(5,8)` -/

/-- The first group's rank sets for cell `(5,8)`, the low half's certificate 1. -/
def cutFiveEightUnder₁LowRanks : Fin 4 → Finset (Fin 5) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFiveEightUnder₁LowRanks`. -/
noncomputable def cutFiveEightUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(5,8)`, the low half's certificate 1. -/
def cutFiveEightUnder₁Ranks : Fin 4 → Finset (Fin 8) :=
  ![{1, 3, 5, 6}, {4, 7}, {0}, {2}]

/-- The slopes of `Gap212.cutFiveEightUnder₁Ranks`. -/
noncomputable def cutFiveEightUnder₁Dens : Fin 4 → ℝ := ![4 / 7, 1 / 4, 0, 0]

/-- The constants of `Gap212.cutFiveEightUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutFiveEightUnder₁Const : Fin 4 → ℝ := ![0, 0, 1, 1]

/-- The first group's rank sets for cell `(5,8)`, the high half's certificate 1. -/
def cutFiveEightOver₁LowRanks : Fin 4 → Finset (Fin 5) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFiveEightOver₁LowRanks`. -/
noncomputable def cutFiveEightOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(5,8)`, the high half's certificate 1. -/
def cutFiveEightOver₁Ranks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1}, {2, 4, 6}, {3}, {5, 7}]

/-- The slopes of `Gap212.cutFiveEightOver₁Ranks`. -/
noncomputable def cutFiveEightOver₁Dens : Fin 4 → ℝ := ![1, 1 / 2, 1 / 4, 2 / 7]

/-- The constants of `Gap212.cutFiveEightOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutFiveEightOver₁Const : Fin 4 → ℝ := ![0, -1 / 2, 0, -2 / 7]

/-- The first group's rank sets for cell `(5,8)`, the high half's certificate 2. -/
def cutFiveEightOver₂LowRanks : Fin 4 → Finset (Fin 5) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutFiveEightOver₂LowRanks`. -/
noncomputable def cutFiveEightOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(5,8)`, the high half's certificate 2. -/
def cutFiveEightOver₂Ranks : Fin 4 → Finset (Fin 8) :=
  ![{0, 1, 2}, {3, 6}, {5}, {4, 7}]

/-- The slopes of `Gap212.cutFiveEightOver₂Ranks`. -/
noncomputable def cutFiveEightOver₂Dens : Fin 4 → ℝ := ![1, 1 / 3, 1 / 5, 2 / 7]

/-- The constants of `Gap212.cutFiveEightOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutFiveEightOver₂Const : Fin 4 → ℝ := ![0, -1 / 3, -1 / 5, -2 / 7]

/-- **Cell `(5,8)`, the low half's certificate 1.**

Block bounds `10511 / 35000`, `521 / 10000`, `4 / 125`, `4 / 125`.
Valid on `4 / 625 < ω₀` and on
`11659 / 35000 + 8ω₀ + ϵ ≤ γ ≤ 4479 / 10000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3891143 + ϵ, 0.4339000 - ϵ]`. The cut is at `t = 4 / 125`. -/
theorem admitsPartition₄_cellFiveEight_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 11659 / 35000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 4479 / 10000 - 2 * ω₀ - slack)
    {y : Fin (5 + 8) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (521 / 2500) 5 8 (41 / 2500))
    (hcut : ∀ i : Fin (5 + 8), 5 ≤ (i : ℕ) → y i ≤ 4 / 125) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_data (by norm_num) hy (by norm_num) hcut cutFiveEightUnder₁LowRanks
    cutFiveEightUnder₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![4, 1, 0, 0] ![0, 0, 1, 1] ![7, 4, 1, 1]
    (by decide) cutFiveEightUnder₁LowDens cutFiveEightUnder₁Dens cutFiveEightUnder₁Const
    (fun k ↦ ?_) (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutFiveEightUnder₁LowRanks,
    cutFiveEightUnder₁Ranks, cutFiveEightUnder₁LowDens, cutFiveEightUnder₁Dens,
    cutFiveEightUnder₁Const] <;> linarith

/-- **Cell `(5,8)`, the high half's certificate 1.**

Block bounds `1503 / 5000`, `2 / 25`, `357 / 10000`, `63 / 1250`.
Valid on `4 / 625 < ω₀` and on
`1667 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 21 / 50 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3894000 + ϵ, 0.4060000 - ϵ]`. The cut is at `t = 4 / 125`. -/
theorem admitsPartition₄_cellFiveEight_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1667 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 21 / 50 - 2 * ω₀ - slack)
    {y : Fin (5 + 8) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (521 / 2500) 5 8 (41 / 2500))
    (hcut : ∃ i : Fin (5 + 8), 5 ≤ (i : ℕ) ∧ 4 / 125 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutFiveEightOver₁LowRanks
    cutFiveEightOver₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 1, 2] ![0, -1, 0, -2] ![1, 2, 4, 7]
    (by decide) cutFiveEightOver₁LowDens cutFiveEightOver₁Dens cutFiveEightOver₁Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutFiveEightOver₁LowRanks,
    cutFiveEightOver₁Ranks, cutFiveEightOver₁LowDens, cutFiveEightOver₁Dens, cutFiveEightOver₁Const]
    <;> linarith

/-- **Cell `(5,8)`, the high half's certificate 2.**

Block bounds `317 / 1000`, `4 / 75`, `359 / 12500`, `63 / 1250`.
Valid on `4 / 625 < ω₀` and on
`1749 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 67 / 150 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4058000 + ϵ, 0.4326667 - ϵ]`. The cut is at `t = 4 / 125`. -/
theorem admitsPartition₄_cellFiveEight_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1749 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 67 / 150 - 2 * ω₀ - slack)
    {y : Fin (5 + 8) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (521 / 2500) 5 8 (41 / 2500))
    (hcut : ∃ i : Fin (5 + 8), 5 ≤ (i : ℕ) ∧ 4 / 125 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutFiveEightOver₂LowRanks
    cutFiveEightOver₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 1, 2] ![0, -1, -1, -2] ![1, 3, 5, 7]
    (by decide) cutFiveEightOver₂LowDens cutFiveEightOver₂Dens cutFiveEightOver₂Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutFiveEightOver₂LowRanks,
    cutFiveEightOver₂Ranks, cutFiveEightOver₂LowDens, cutFiveEightOver₂Dens, cutFiveEightOver₂Const]
    <;> linarith

/-- **Cell `(5,8)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,5}, B_{1,8}, 5, 8, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 4 / 125`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellFiveEight_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 8) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (521 / 2500) 5 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  rw [show gap212Params.δ = 41 / 2500 from rfl] at hγhi
  refine admitsPartition₄_of_cut (t := 4 / 125) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · exact admitsPartition₄_cellFiveEight_under₁ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (21 / 50 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellFiveEight_over₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellFiveEight_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(5,8)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellFiveEight_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (5 + 8) → ℝ}
    (hy : y ∈ Xi (953 / 5000 : ℝ) (521 / 2500) 5 8 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellFiveEight_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(5,8)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 5 = gap212Cap 5 = 953 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellFiveEight_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (5 + 8) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 5) (gap212Params.B j' 8) 5 8
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellFiveEight_band hωlo hωhi hγlo hγhi
    (xi_atDatum j j' (by norm_num [gap212Cap]) (by norm_num [gap212Cap]) hy)

/-! ## Cell `(6,9)` -/

/-- The first group's rank sets for cell `(6,9)`, the low half's certificate 1. -/
def cutSixNineUnder₁LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSixNineUnder₁LowRanks`. -/
noncomputable def cutSixNineUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,9)`, the low half's certificate 1. -/
def cutSixNineUnder₁Ranks : Fin 4 → Finset (Fin 9) :=
  ![{1, 3, 5, 6}, {4, 8}, {0}, {2, 7}]

/-- The slopes of `Gap212.cutSixNineUnder₁Ranks`. -/
noncomputable def cutSixNineUnder₁Dens : Fin 4 → ℝ := ![4 / 7, 2 / 9, 0, 1 / 5]

/-- The constants of `Gap212.cutSixNineUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutSixNineUnder₁Const : Fin 4 → ℝ := ![0, 0, 1, 2 / 5]

/-- The first group's rank sets for cell `(6,9)`, the high half's certificate 1. -/
def cutSixNineOver₁LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSixNineOver₁LowRanks`. -/
noncomputable def cutSixNineOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,9)`, the high half's certificate 1. -/
def cutSixNineOver₁Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2}, {3, 6, 8}, {5}, {4, 7}]

/-- The slopes of `Gap212.cutSixNineOver₁Ranks`. -/
noncomputable def cutSixNineOver₁Dens : Fin 4 → ℝ := ![1, 3 / 8, 1 / 6, 2 / 7]

/-- The constants of `Gap212.cutSixNineOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutSixNineOver₁Const : Fin 4 → ℝ := ![0, -3 / 8, 0, -2 / 7]

/-- The first group's rank sets for cell `(6,9)`, the high half's certificate 2. -/
def cutSixNineOver₂LowRanks : Fin 4 → Finset (Fin 6) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSixNineOver₂LowRanks`. -/
noncomputable def cutSixNineOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(6,9)`, the high half's certificate 2. -/
def cutSixNineOver₂Ranks : Fin 4 → Finset (Fin 9) :=
  ![{0, 1, 2, 3}, {4, 8}, {6}, {5, 7}]

/-- The slopes of `Gap212.cutSixNineOver₂Ranks`. -/
noncomputable def cutSixNineOver₂Dens : Fin 4 → ℝ := ![1, 1 / 4, 1 / 6, 2 / 7]

/-- The constants of `Gap212.cutSixNineOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutSixNineOver₂Const : Fin 4 → ℝ := ![0, -1 / 4, -1 / 6, -2 / 7]

/-- **Cell `(6,9)`, the low half's certificate 1.**

Block bounds `10477 / 35000`, `1063 / 22500`, `13 / 500`, `1241 / 25000`.
Valid on `4 / 625 < ω₀` and on
`93 / 280 + 8ω₀ + ϵ ≤ γ ≤ 10187 / 22500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3881429 + ϵ, 0.4387556 - ϵ]`. The cut is at `t = 13 / 500`. -/
theorem admitsPartition₄_cellSixNine_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 93 / 280 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 10187 / 22500 - 2 * ω₀ - slack)
    {y : Fin (6 + 9) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1063 / 5000) 6 9 (41 / 2500))
    (hcut : ∀ i : Fin (6 + 9), 6 ≤ (i : ℕ) → y i ≤ 13 / 500) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_data (by norm_num) hy (by norm_num) hcut cutSixNineUnder₁LowRanks
    cutSixNineUnder₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![4, 2, 0, 1] ![0, 0, 1, 2] ![7, 9, 1, 5]
    (by decide) cutSixNineUnder₁LowDens cutSixNineUnder₁Dens cutSixNineUnder₁Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutSixNineUnder₁LowRanks,
    cutSixNineUnder₁Ranks, cutSixNineUnder₁LowDens, cutSixNineUnder₁Dens, cutSixNineUnder₁Const] <;>
    linarith

/-- **Cell `(6,9)`, the high half's certificate 1.**

Block bounds `777 / 2500`, `2799 / 40000`, `817 / 30000`, `851 / 17500`.
Valid on `4 / 625 < ω₀` and on
`859 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 17201 / 40000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3996000 + ϵ, 0.4160250 - ϵ]`. The cut is at `t = 13 / 500`. -/
theorem admitsPartition₄_cellSixNine_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 859 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 17201 / 40000 - 2 * ω₀ - slack)
    {y : Fin (6 + 9) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1063 / 5000) 6 9 (41 / 2500))
    (hcut : ∃ i : Fin (6 + 9), 6 ≤ (i : ℕ) ∧ 13 / 500 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutSixNineOver₁LowRanks
    cutSixNineOver₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 3, 1, 2] ![0, -3, 0, -2] ![1, 8, 6, 7]
    (by decide) cutSixNineOver₁LowDens cutSixNineOver₁Dens cutSixNineOver₁Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutSixNineOver₁LowRanks,
    cutSixNineOver₁Ranks, cutSixNineOver₁LowDens, cutSixNineOver₁Dens, cutSixNineOver₁Const] <;>
    linarith

/-- **Cell `(6,9)`, the high half's certificate 2.**

Block bounds `409 / 1250`, `933 / 20000`, `769 / 30000`, `851 / 17500`.
Valid on `4 / 625 < ω₀` and on
`9 / 25 + 8ω₀ + ϵ ≤ γ ≤ 9067 / 20000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4160000 + ϵ, 0.4393500 - ϵ]`. The cut is at `t = 13 / 500`. -/
theorem admitsPartition₄_cellSixNine_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 9 / 25 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 9067 / 20000 - 2 * ω₀ - slack)
    {y : Fin (6 + 9) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1063 / 5000) 6 9 (41 / 2500))
    (hcut : ∃ i : Fin (6 + 9), 6 ≤ (i : ℕ) ∧ 13 / 500 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutSixNineOver₂LowRanks
    cutSixNineOver₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 1, 2] ![0, -1, -1, -2] ![1, 4, 6, 7]
    (by decide) cutSixNineOver₂LowDens cutSixNineOver₂Dens cutSixNineOver₂Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutSixNineOver₂LowRanks,
    cutSixNineOver₂Ranks, cutSixNineOver₂LowDens, cutSixNineOver₂Dens, cutSixNineOver₂Const] <;>
    linarith

/-- **Cell `(6,9)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,6}, B_{1,9}, 6, 9, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 13 / 500`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellSixNine_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 9) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1063 / 5000) 6 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  rw [show gap212Params.δ = 41 / 2500 from rfl] at hγhi
  refine admitsPartition₄_of_cut (t := 13 / 500) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · exact admitsPartition₄_cellSixNine_under₁ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (17201 / 40000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellSixNine_over₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellSixNine_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(6,9)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellSixNine_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (6 + 9) → ℝ}
    (hy : y ∈ Xi (983 / 5000 : ℝ) (1063 / 5000) 6 9 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellSixNine_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(6,9)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 6 = gap212Cap 6 = 983 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellSixNine_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (6 + 9) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 6) (gap212Params.B j' 9) 6 9
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellSixNine_band hωlo hωhi hγlo hγhi
    (xi_atDatum j j' (by norm_num [gap212Cap]) (by norm_num [gap212Cap]) hy)

/-! ## Cell `(7,10)` -/

/-- The first group's rank sets for cell `(7,10)`, the low half's certificate 1. -/
def cutSevenTenUnder₁LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenTenUnder₁LowRanks`. -/
noncomputable def cutSevenTenUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,10)`, the low half's certificate 1. -/
def cutSevenTenUnder₁Ranks : Fin 4 → Finset (Fin 10) :=
  ![{1, 4, 6, 8}, {3, 7, 9}, {0}, {2, 5}]

/-- The slopes of `Gap212.cutSevenTenUnder₁Ranks`. -/
noncomputable def cutSevenTenUnder₁Dens : Fin 4 → ℝ := ![3 / 7, 3 / 10, 0, 1 / 3]

/-- The constants of `Gap212.cutSevenTenUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutSevenTenUnder₁Const : Fin 4 → ℝ := ![1 / 7, 0, 1, 0]

/-- The first group's rank sets for cell `(7,10)`, the low half's certificate 2. -/
def cutSevenTenUnder₂LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenTenUnder₂LowRanks`. -/
noncomputable def cutSevenTenUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,10)`, the low half's certificate 2. -/
def cutSevenTenUnder₂Ranks : Fin 4 → Finset (Fin 10) :=
  ![{1, 3, 5, 7, 8}, {4, 9}, {0}, {2, 6}]

/-- The slopes of `Gap212.cutSevenTenUnder₂Ranks`. -/
noncomputable def cutSevenTenUnder₂Dens : Fin 4 → ℝ := ![5 / 9, 1 / 5, 0, 1 / 4]

/-- The constants of `Gap212.cutSevenTenUnder₂Ranks`, nonnegative throughout. -/
noncomputable def cutSevenTenUnder₂Const : Fin 4 → ℝ := ![0, 0, 1, 1 / 4]

/-- The first group's rank sets for cell `(7,10)`, the high half's certificate 1. -/
def cutSevenTenOver₁LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenTenOver₁LowRanks`. -/
noncomputable def cutSevenTenOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,10)`, the high half's certificate 1. -/
def cutSevenTenOver₁Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2}, {3, 6, 8}, {5, 9}, {4, 7}]

/-- The slopes of `Gap212.cutSevenTenOver₁Ranks`. -/
noncomputable def cutSevenTenOver₁Dens : Fin 4 → ℝ := ![1, 3 / 8, 2 / 9, 2 / 7]

/-- The constants of `Gap212.cutSevenTenOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutSevenTenOver₁Const : Fin 4 → ℝ := ![0, -3 / 8, -2 / 9, -2 / 7]

/-- The first group's rank sets for cell `(7,10)`, the high half's certificate 2. -/
def cutSevenTenOver₂LowRanks : Fin 4 → Finset (Fin 7) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutSevenTenOver₂LowRanks`. -/
noncomputable def cutSevenTenOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(7,10)`, the high half's certificate 2. -/
def cutSevenTenOver₂Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3}, {4, 8}, {5, 9}, {6, 7}]

/-- The slopes of `Gap212.cutSevenTenOver₂Ranks`. -/
noncomputable def cutSevenTenOver₂Dens : Fin 4 → ℝ := ![1, 1 / 4, 2 / 9, 2 / 7]

/-- The constants of `Gap212.cutSevenTenOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutSevenTenOver₂Const : Fin 4 → ℝ := ![0, -1 / 4, -2 / 9, -2 / 7]

/-- **Cell `(7,10)`, the low half's certificate 1.**

Block bounds `10249 / 35000`, `3243 / 50000`, `7 / 250`, `251 / 5000`.
Valid on `4 / 625 < ω₀` and on
`11397 / 35000 + 8ω₀ + ϵ ≤ γ ≤ 21757 / 50000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3816286 + ϵ, 0.4211400 - ϵ]`. The cut is at `t = 7 / 250`. -/
theorem admitsPartition₄_cellSevenTen_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 11397 / 35000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 21757 / 50000 - 2 * ω₀ - slack)
    {y : Fin (7 + 10) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1081 / 5000) 7 10 (41 / 2500))
    (hcut : ∀ i : Fin (7 + 10), 7 ≤ (i : ℕ) → y i ≤ 7 / 250) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_data (by norm_num) hy (by norm_num) hcut cutSevenTenUnder₁LowRanks
    cutSevenTenUnder₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![3, 3, 0, 1] ![1, 0, 1, 0] ![7, 10, 1, 3]
    (by decide) cutSevenTenUnder₁LowDens cutSevenTenUnder₁Dens cutSevenTenUnder₁Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutSevenTenUnder₁LowRanks,
    cutSevenTenUnder₁Ranks, cutSevenTenUnder₁LowDens, cutSevenTenUnder₁Dens, cutSevenTenUnder₁Const]
    <;> linarith

/-- **Cell `(7,10)`, the low half's certificate 2.**

Block bounds `1571 / 5000`, `1081 / 25000`, `7 / 250`, `39 / 800`.
Valid on `4 / 625 < ω₀` and on
`347 / 1000 + 8ω₀ + ϵ ≤ γ ≤ 11419 / 25000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4030000 + ϵ, 0.4427600 - ϵ]`. The cut is at `t = 7 / 250`. -/
theorem admitsPartition₄_cellSevenTen_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 347 / 1000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 11419 / 25000 - 2 * ω₀ - slack)
    {y : Fin (7 + 10) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1081 / 5000) 7 10 (41 / 2500))
    (hcut : ∀ i : Fin (7 + 10), 7 ≤ (i : ℕ) → y i ≤ 7 / 250) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_data (by norm_num) hy (by norm_num) hcut cutSevenTenUnder₂LowRanks
    cutSevenTenUnder₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![5, 1, 0, 1] ![0, 0, 1, 1] ![9, 5, 1, 4]
    (by decide) cutSevenTenUnder₂LowDens cutSevenTenUnder₂Dens cutSevenTenUnder₂Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutSevenTenUnder₂LowRanks,
    cutSevenTenUnder₂Ranks, cutSevenTenUnder₂LowDens, cutSevenTenUnder₂Dens, cutSevenTenUnder₂Const]
    <;> linarith

/-- **Cell `(7,10)`, the high half's certificate 1.**

Block bounds `1523 / 5000`, `2577 / 40000`, `941 / 22500`, `111 / 2500`.
Valid on `4 / 625 < ω₀` and on
`1687 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 17423 / 40000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3934000 + ϵ, 0.4215750 - ϵ]`. The cut is at `t = 7 / 250`. -/
theorem admitsPartition₄_cellSevenTen_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1687 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 17423 / 40000 - 2 * ω₀ - slack)
    {y : Fin (7 + 10) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1081 / 5000) 7 10 (41 / 2500))
    (hcut : ∃ i : Fin (7 + 10), 7 ≤ (i : ℕ) ∧ 7 / 250 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutSevenTenOver₁LowRanks
    cutSevenTenOver₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 3, 2, 2] ![0, -3, -2, -2] ![1, 8, 9, 7]
    (by decide) cutSevenTenOver₁LowDens cutSevenTenOver₁Dens cutSevenTenOver₁Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutSevenTenOver₁LowRanks,
    cutSevenTenOver₁Ranks, cutSevenTenOver₁LowDens, cutSevenTenOver₁Dens, cutSevenTenOver₁Const] <;>
    linarith

/-- **Cell `(7,10)`, the high half's certificate 2.**

Block bounds `321 / 1000`, `859 / 20000`, `941 / 22500`, `111 / 2500`.
Valid on `4 / 625 < ω₀` and on
`1769 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 9141 / 20000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4098000 + ϵ, 0.4430500 - ϵ]`. The cut is at `t = 7 / 250`. -/
theorem admitsPartition₄_cellSevenTen_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1769 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 9141 / 20000 - 2 * ω₀ - slack)
    {y : Fin (7 + 10) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1081 / 5000) 7 10 (41 / 2500))
    (hcut : ∃ i : Fin (7 + 10), 7 ≤ (i : ℕ) ∧ 7 / 250 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutSevenTenOver₂LowRanks
    cutSevenTenOver₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 2, 2] ![0, -1, -2, -2] ![1, 4, 9, 7]
    (by decide) cutSevenTenOver₂LowDens cutSevenTenOver₂Dens cutSevenTenOver₂Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutSevenTenOver₂LowRanks,
    cutSevenTenOver₂Ranks, cutSevenTenOver₂LowDens, cutSevenTenOver₂Dens, cutSevenTenOver₂Const] <;>
    linarith

/-- **Cell `(7,10)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,7}, B_{1,10}, 7, 10, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 7 / 250`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellSevenTen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (7 + 10) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1081 / 5000) 7 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  rw [show gap212Params.δ = 41 / 2500 from rfl] at hγhi
  refine admitsPartition₄_of_cut (t := 7 / 250) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · rcases le_or_gt γ (21757 / 50000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellSevenTen_under₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellSevenTen_under₂ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (17423 / 40000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellSevenTen_over₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellSevenTen_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(7,10)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellSevenTen_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (7 + 10) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (1081 / 5000) 7 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellSevenTen_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(7,10)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 7 = gap212Cap 7 = 127 / 625` at every stratum `j`. -/
theorem admitsPartition₄_cellSevenTen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (7 + 10) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 7) (gap212Params.B j' 10) 7 10
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellSevenTen_band hωlo hωhi hγlo hγhi
    (xi_atDatum j j' (by norm_num [gap212Cap]) (by norm_num [gap212Cap]) hy)

/-! ## Cell `(8,10)` -/

/-- The first group's rank sets for cell `(8,10)`, the low half's certificate 1. -/
def cutEightTenUnder₁LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutEightTenUnder₁LowRanks`. -/
noncomputable def cutEightTenUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,10)`, the low half's certificate 1. -/
def cutEightTenUnder₁Ranks : Fin 4 → Finset (Fin 10) :=
  ![{1, 4, 6, 8}, {3, 7, 9}, {0}, {2, 5}]

/-- The slopes of `Gap212.cutEightTenUnder₁Ranks`. -/
noncomputable def cutEightTenUnder₁Dens : Fin 4 → ℝ := ![3 / 7, 3 / 10, 0, 1 / 3]

/-- The constants of `Gap212.cutEightTenUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutEightTenUnder₁Const : Fin 4 → ℝ := ![1 / 7, 0, 1, 0]

/-- The first group's rank sets for cell `(8,10)`, the low half's certificate 2. -/
def cutEightTenUnder₂LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutEightTenUnder₂LowRanks`. -/
noncomputable def cutEightTenUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,10)`, the low half's certificate 2. -/
def cutEightTenUnder₂Ranks : Fin 4 → Finset (Fin 10) :=
  ![{1, 3, 5, 7, 8}, {4, 9}, {0}, {2, 6}]

/-- The slopes of `Gap212.cutEightTenUnder₂Ranks`. -/
noncomputable def cutEightTenUnder₂Dens : Fin 4 → ℝ := ![5 / 9, 1 / 5, 0, 1 / 4]

/-- The constants of `Gap212.cutEightTenUnder₂Ranks`, nonnegative throughout. -/
noncomputable def cutEightTenUnder₂Const : Fin 4 → ℝ := ![0, 0, 1, 1 / 4]

/-- The first group's rank sets for cell `(8,10)`, the high half's certificate 1. -/
def cutEightTenOver₁LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutEightTenOver₁LowRanks`. -/
noncomputable def cutEightTenOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,10)`, the high half's certificate 1. -/
def cutEightTenOver₁Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2}, {3, 6, 8}, {5, 9}, {4, 7}]

/-- The slopes of `Gap212.cutEightTenOver₁Ranks`. -/
noncomputable def cutEightTenOver₁Dens : Fin 4 → ℝ := ![1, 3 / 8, 2 / 9, 2 / 7]

/-- The constants of `Gap212.cutEightTenOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutEightTenOver₁Const : Fin 4 → ℝ := ![0, -3 / 8, -2 / 9, -2 / 7]

/-- The first group's rank sets for cell `(8,10)`, the high half's certificate 2. -/
def cutEightTenOver₂LowRanks : Fin 4 → Finset (Fin 8) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutEightTenOver₂LowRanks`. -/
noncomputable def cutEightTenOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(8,10)`, the high half's certificate 2. -/
def cutEightTenOver₂Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3}, {4, 8}, {5, 9}, {6, 7}]

/-- The slopes of `Gap212.cutEightTenOver₂Ranks`. -/
noncomputable def cutEightTenOver₂Dens : Fin 4 → ℝ := ![1, 1 / 4, 2 / 9, 2 / 7]

/-- The constants of `Gap212.cutEightTenOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutEightTenOver₂Const : Fin 4 → ℝ := ![0, -1 / 4, -2 / 9, -2 / 7]

/-- **Cell `(8,10)`, the low half's certificate 1.**

Block bounds `10431 / 35000`, `3243 / 50000`, `7 / 250`, `251 / 5000`.
Valid on `4 / 625 < ω₀` and on
`11579 / 35000 + 8ω₀ + ϵ ≤ γ ≤ 21757 / 50000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3868286 + ϵ, 0.4211400 - ϵ]`. The cut is at `t = 7 / 250`. -/
theorem admitsPartition₄_cellEightTen_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 11579 / 35000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 21757 / 50000 - 2 * ω₀ - slack)
    {y : Fin (8 + 10) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1081 / 5000) 8 10 (41 / 2500))
    (hcut : ∀ i : Fin (8 + 10), 8 ≤ (i : ℕ) → y i ≤ 7 / 250) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_data (by norm_num) hy (by norm_num) hcut cutEightTenUnder₁LowRanks
    cutEightTenUnder₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![3, 3, 0, 1] ![1, 0, 1, 0] ![7, 10, 1, 3]
    (by decide) cutEightTenUnder₁LowDens cutEightTenUnder₁Dens cutEightTenUnder₁Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutEightTenUnder₁LowRanks,
    cutEightTenUnder₁Ranks, cutEightTenUnder₁LowDens, cutEightTenUnder₁Dens, cutEightTenUnder₁Const]
    <;> linarith

/-- **Cell `(8,10)`, the low half's certificate 2.**

Block bounds `1597 / 5000`, `1081 / 25000`, `7 / 250`, `39 / 800`.
Valid on `4 / 625 < ω₀` and on
`1761 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 11419 / 25000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4082000 + ϵ, 0.4427600 - ϵ]`. The cut is at `t = 7 / 250`. -/
theorem admitsPartition₄_cellEightTen_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1761 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 11419 / 25000 - 2 * ω₀ - slack)
    {y : Fin (8 + 10) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1081 / 5000) 8 10 (41 / 2500))
    (hcut : ∀ i : Fin (8 + 10), 8 ≤ (i : ℕ) → y i ≤ 7 / 250) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_data (by norm_num) hy (by norm_num) hcut cutEightTenUnder₂LowRanks
    cutEightTenUnder₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![5, 1, 0, 1] ![0, 0, 1, 1] ![9, 5, 1, 4]
    (by decide) cutEightTenUnder₂LowDens cutEightTenUnder₂Dens cutEightTenUnder₂Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutEightTenUnder₂LowRanks,
    cutEightTenUnder₂Ranks, cutEightTenUnder₂LowDens, cutEightTenUnder₂Dens, cutEightTenUnder₂Const]
    <;> linarith

/-- **Cell `(8,10)`, the high half's certificate 1.**

Block bounds `1549 / 5000`, `2577 / 40000`, `941 / 22500`, `111 / 2500`.
Valid on `4 / 625 < ω₀` and on
`1713 / 5000 + 8ω₀ + ϵ ≤ γ ≤ 17423 / 40000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3986000 + ϵ, 0.4215750 - ϵ]`. The cut is at `t = 7 / 250`. -/
theorem admitsPartition₄_cellEightTen_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 1713 / 5000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 17423 / 40000 - 2 * ω₀ - slack)
    {y : Fin (8 + 10) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1081 / 5000) 8 10 (41 / 2500))
    (hcut : ∃ i : Fin (8 + 10), 8 ≤ (i : ℕ) ∧ 7 / 250 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutEightTenOver₁LowRanks
    cutEightTenOver₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 3, 2, 2] ![0, -3, -2, -2] ![1, 8, 9, 7]
    (by decide) cutEightTenOver₁LowDens cutEightTenOver₁Dens cutEightTenOver₁Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutEightTenOver₁LowRanks,
    cutEightTenOver₁Ranks, cutEightTenOver₁LowDens, cutEightTenOver₁Dens, cutEightTenOver₁Const] <;>
    linarith

/-- **Cell `(8,10)`, the high half's certificate 2.**

Block bounds `1631 / 5000`, `859 / 20000`, `941 / 22500`, `111 / 2500`.
Valid on `4 / 625 < ω₀` and on
`359 / 1000 + 8ω₀ + ϵ ≤ γ ≤ 9141 / 20000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4150000 + ϵ, 0.4430500 - ϵ]`. The cut is at `t = 7 / 250`. -/
theorem admitsPartition₄_cellEightTen_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 359 / 1000 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 9141 / 20000 - 2 * ω₀ - slack)
    {y : Fin (8 + 10) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1081 / 5000) 8 10 (41 / 2500))
    (hcut : ∃ i : Fin (8 + 10), 8 ≤ (i : ℕ) ∧ 7 / 250 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutEightTenOver₂LowRanks
    cutEightTenOver₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 2, 2] ![0, -1, -2, -2] ![1, 4, 9, 7]
    (by decide) cutEightTenOver₂LowDens cutEightTenOver₂Dens cutEightTenOver₂Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutEightTenOver₂LowRanks,
    cutEightTenOver₂Ranks, cutEightTenOver₂LowDens, cutEightTenOver₂Dens, cutEightTenOver₂Const] <;>
    linarith

/-- **Cell `(8,10)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,8}, B_{1,10}, 8, 10, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 7 / 250`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellEightTen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (8 + 10) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1081 / 5000) 8 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  rw [show gap212Params.δ = 41 / 2500 from rfl] at hγhi
  refine admitsPartition₄_of_cut (t := 7 / 250) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · rcases le_or_gt γ (21757 / 50000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellEightTen_under₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellEightTen_under₂ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (17423 / 40000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellEightTen_over₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellEightTen_over₂ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(8,10)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellEightTen_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (8 + 10) → ℝ}
    (hy : y ∈ Xi (521 / 2500 : ℝ) (1081 / 5000) 8 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellEightTen_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(8,10)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 8 = gap212Cap 8 = 521 / 2500` at every stratum `j`. -/
theorem admitsPartition₄_cellEightTen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (8 + 10) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 8) (gap212Params.B j' 10) 8 10
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellEightTen_band hωlo hωhi hγlo hγhi
    (xi_atDatum j j' (by norm_num [gap212Cap]) (by norm_num [gap212Cap]) hy)

/-! ## Cell `(9,10)` -/

/-- The first group's rank sets for cell `(9,10)`, the low half's certificate 1. -/
def cutNineTenUnder₁LowRanks : Fin 4 → Finset (Fin 9) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutNineTenUnder₁LowRanks`. -/
noncomputable def cutNineTenUnder₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(9,10)`, the low half's certificate 1. -/
def cutNineTenUnder₁Ranks : Fin 4 → Finset (Fin 10) :=
  ![{1, 4, 6, 8}, {3, 7, 9}, {0}, {2, 5}]

/-- The slopes of `Gap212.cutNineTenUnder₁Ranks`. -/
noncomputable def cutNineTenUnder₁Dens : Fin 4 → ℝ := ![3 / 7, 3 / 10, 0, 1 / 3]

/-- The constants of `Gap212.cutNineTenUnder₁Ranks`, nonnegative throughout. -/
noncomputable def cutNineTenUnder₁Const : Fin 4 → ℝ := ![1 / 7, 0, 1, 0]

/-- The first group's rank sets for cell `(9,10)`, the low half's certificate 2. -/
def cutNineTenUnder₂LowRanks : Fin 4 → Finset (Fin 9) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutNineTenUnder₂LowRanks`. -/
noncomputable def cutNineTenUnder₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(9,10)`, the low half's certificate 2. -/
def cutNineTenUnder₂Ranks : Fin 4 → Finset (Fin 10) :=
  ![{1, 3, 5, 7, 8}, {4, 9}, {0}, {2, 6}]

/-- The slopes of `Gap212.cutNineTenUnder₂Ranks`. -/
noncomputable def cutNineTenUnder₂Dens : Fin 4 → ℝ := ![5 / 9, 1 / 5, 0, 1 / 4]

/-- The constants of `Gap212.cutNineTenUnder₂Ranks`, nonnegative throughout. -/
noncomputable def cutNineTenUnder₂Const : Fin 4 → ℝ := ![0, 0, 1, 1 / 4]

/-- The first group's rank sets for cell `(9,10)`, the high half's certificate 1. -/
def cutNineTenOver₁LowRanks : Fin 4 → Finset (Fin 9) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutNineTenOver₁LowRanks`. -/
noncomputable def cutNineTenOver₁LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(9,10)`, the high half's certificate 1. -/
def cutNineTenOver₁Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1}, {3, 5, 7, 9}, {4, 8}, {2, 6}]

/-- The slopes of `Gap212.cutNineTenOver₁Ranks`. -/
noncomputable def cutNineTenOver₁Dens : Fin 4 → ℝ := ![1, 4 / 9, 1 / 4, 1 / 3]

/-- The constants of `Gap212.cutNineTenOver₁Ranks`, nonpositive throughout. -/
noncomputable def cutNineTenOver₁Const : Fin 4 → ℝ := ![0, -4 / 9, -1 / 4, 0]

/-- The first group's rank sets for cell `(9,10)`, the high half's certificate 2. -/
def cutNineTenOver₂LowRanks : Fin 4 → Finset (Fin 9) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutNineTenOver₂LowRanks`. -/
noncomputable def cutNineTenOver₂LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(9,10)`, the high half's certificate 2. -/
def cutNineTenOver₂Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2}, {3, 6, 9}, {4, 8}, {5, 7}]

/-- The slopes of `Gap212.cutNineTenOver₂Ranks`. -/
noncomputable def cutNineTenOver₂Dens : Fin 4 → ℝ := ![1, 1 / 3, 1 / 4, 2 / 7]

/-- The constants of `Gap212.cutNineTenOver₂Ranks`, nonpositive throughout. -/
noncomputable def cutNineTenOver₂Const : Fin 4 → ℝ := ![0, -1 / 3, -1 / 4, -2 / 7]

/-- The first group's rank sets for cell `(9,10)`, the high half's certificate 3. -/
def cutNineTenOver₃LowRanks : Fin 4 → Finset (Fin 9) :=
  ![Finset.univ, ∅, ∅, ∅]

/-- The prefix densities of `Gap212.cutNineTenOver₃LowRanks`. -/
noncomputable def cutNineTenOver₃LowDens : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The second group's rank sets for cell `(9,10)`, the high half's certificate 3. -/
def cutNineTenOver₃Ranks : Fin 4 → Finset (Fin 10) :=
  ![{0, 1, 2, 3}, {5, 9}, {4, 8}, {6, 7}]

/-- The slopes of `Gap212.cutNineTenOver₃Ranks`. -/
noncomputable def cutNineTenOver₃Dens : Fin 4 → ℝ := ![1, 2 / 9, 1 / 4, 2 / 7]

/-- The constants of `Gap212.cutNineTenOver₃Ranks`, nonpositive throughout. -/
noncomputable def cutNineTenOver₃Const : Fin 4 → ℝ := ![0, -2 / 9, -1 / 4, -2 / 7]

/-- **Cell `(9,10)`, the low half's certificate 1.**

Block bounds `757 / 2500`, `3243 / 50000`, `4 / 125`, `251 / 5000`.
Valid on `4 / 625 < ω₀` and on
`839 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 21757 / 50000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3916000 + ϵ, 0.4211400 - ϵ]`. The cut is at `t = 4 / 125`. -/
theorem admitsPartition₄_cellNineTen_under₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 839 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 21757 / 50000 - 2 * ω₀ - slack)
    {y : Fin (9 + 10) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 10 (41 / 2500))
    (hcut : ∀ i : Fin (9 + 10), 9 ≤ (i : ℕ) → y i ≤ 4 / 125) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_data (by norm_num) hy (by norm_num) hcut cutNineTenUnder₁LowRanks
    cutNineTenUnder₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![3, 3, 0, 1] ![1, 0, 1, 0] ![7, 10, 1, 3]
    (by decide) cutNineTenUnder₁LowDens cutNineTenUnder₁Dens cutNineTenUnder₁Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutNineTenUnder₁LowRanks,
    cutNineTenUnder₁Ranks, cutNineTenUnder₁LowDens, cutNineTenUnder₁Dens, cutNineTenUnder₁Const] <;>
    linarith

/-- **Cell `(9,10)`, the low half's certificate 2.**

Block bounds `809 / 2500`, `1081 / 25000`, `4 / 125`, `199 / 4000`.
Valid on `4 / 625 < ω₀` and on
`891 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 11419 / 25000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4124000 + ϵ, 0.4427600 - ϵ]`. The cut is at `t = 4 / 125`. -/
theorem admitsPartition₄_cellNineTen_under₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 891 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 11419 / 25000 - 2 * ω₀ - slack)
    {y : Fin (9 + 10) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 10 (41 / 2500))
    (hcut : ∀ i : Fin (9 + 10), 9 ≤ (i : ℕ) → y i ≤ 4 / 125) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_low_of_data (by norm_num) hy (by norm_num) hcut cutNineTenUnder₂LowRanks
    cutNineTenUnder₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![5, 1, 0, 1] ![0, 0, 1, 1] ![9, 5, 1, 4]
    (by decide) cutNineTenUnder₂LowDens cutNineTenUnder₂Dens cutNineTenUnder₂Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutNineTenUnder₂LowRanks,
    cutNineTenUnder₂Ranks, cutNineTenUnder₂LowDens, cutNineTenUnder₂Dens, cutNineTenUnder₂Const] <;>
    linarith

/-- **Cell `(9,10)`, the high half's certificate 1.**

Block bounds `186 / 625`, `307 / 3750`, `839 / 20000`, `251 / 5000`.
Valid on `4 / 625 < ω₀` and on
`413 / 1250 + 8ω₀ + ϵ ≤ γ ≤ 784 / 1875 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.3864000 + ϵ, 0.4041333 - ϵ]`. The cut is at `t = 4 / 125`. -/
theorem admitsPartition₄_cellNineTen_over₁ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 413 / 1250 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 784 / 1875 - 2 * ω₀ - slack)
    {y : Fin (9 + 10) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 10 (41 / 2500))
    (hcut : ∃ i : Fin (9 + 10), 9 ≤ (i : ℕ) ∧ 4 / 125 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutNineTenOver₁LowRanks
    cutNineTenOver₁Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 4, 1, 1] ![0, -4, -1, 0] ![1, 9, 4, 3]
    (by decide) cutNineTenOver₁LowDens cutNineTenOver₁Dens cutNineTenOver₁Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutNineTenOver₁LowRanks,
    cutNineTenOver₁Ranks, cutNineTenOver₁LowDens, cutNineTenOver₁Dens, cutNineTenOver₁Const] <;>
    linarith

/-- **Cell `(9,10)`, the high half's certificate 2.**

Block bounds `157 / 500`, `307 / 5000`, `839 / 20000`, `757 / 17500`.
Valid on `4 / 625 < ω₀` and on
`867 / 2500 + 8ω₀ + ϵ ≤ γ ≤ 2193 / 5000 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4028000 + ϵ, 0.4246000 - ϵ]`. The cut is at `t = 4 / 125`. -/
theorem admitsPartition₄_cellNineTen_over₂ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 867 / 2500 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 2193 / 5000 - 2 * ω₀ - slack)
    {y : Fin (9 + 10) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 10 (41 / 2500))
    (hcut : ∃ i : Fin (9 + 10), 9 ≤ (i : ℕ) ∧ 4 / 125 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutNineTenOver₂LowRanks
    cutNineTenOver₂Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 1, 1, 2] ![0, -1, -1, -2] ![1, 3, 4, 7]
    (by decide) cutNineTenOver₂LowDens cutNineTenOver₂Dens cutNineTenOver₂Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutNineTenOver₂LowRanks,
    cutNineTenOver₂Ranks, cutNineTenOver₂LowDens, cutNineTenOver₂Dens, cutNineTenOver₂Const] <;>
    linarith

/-- **Cell `(9,10)`, the high half's certificate 3.**

Block bounds `413 / 1250`, `307 / 7500`, `839 / 20000`, `757 / 17500`.
Valid on `4 / 625 < ω₀` and on
`227 / 625 + 8ω₀ + ϵ ≤ γ ≤ 3443 / 7500 - 2ω₀ - ϵ`, which at `ω₀ = 7/1000` is
`γ ∈ [0.4192000 + ϵ, 0.4450667 - ϵ]`. The cut is at `t = 4 / 125`. -/
theorem admitsPartition₄_cellNineTen_over₃ {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hγlo : 227 / 625 + 8 * ω₀ + slack ≤ γ) (hγhi : γ ≤ 3443 / 7500 - 2 * ω₀ - slack)
    {y : Fin (9 + 10) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 10 (41 / 2500))
    (hcut : ∃ i : Fin (9 + 10), 9 ≤ (i : ℕ) ∧ 4 / 125 ≤ y i) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine cut_high_of_data (by norm_num) hy (by norm_num) hcut cutNineTenOver₃LowRanks
    cutNineTenOver₃Ranks ![1, 0, 0, 0] ![1, 1, 1, 1] ![1, 2, 1, 2] ![0, -2, -1, -2] ![1, 9, 4, 7]
    (by decide) cutNineTenOver₃LowDens cutNineTenOver₃Dens cutNineTenOver₃Const (fun k ↦ ?_)
    (fun k ↦ capD γ ω₀ k) fun k ↦ ?_
  all_goals fin_cases k <;> norm_num [capD, hδ, Fin.ext_iff, cutNineTenOver₃LowRanks,
    cutNineTenOver₃Ranks, cutNineTenOver₃LowDens, cutNineTenOver₃Dens, cutNineTenOver₃Const] <;>
    linarith

/-- **Cell `(9,10)` is discharged on the whole band.**

For every level `ω₀ ∈ (4/625, 7/1000]` and every `γ` in the chamber's range
`[2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, every profile of `Ξ(B_{1,9}, B_{1,10}, 9, 10, δ)`
admits a four-block partition meeting `Gap212.capD`'s capacities.

The case analysis is `Gap212.Packing.admitsPartition₄_of_cut` on the second group's
largest coordinate against `t = 4 / 125`, then a `γ` split on each half.
No case analysis in `ω₀` is needed: every certificate holds on the whole band. -/
theorem admitsPartition₄_cellNineTen_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (9 + 10) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  rw [show gap212Params.δ = 41 / 2500 from rfl] at hγhi
  refine admitsPartition₄_of_cut (t := 4 / 125) (by norm_num) (fun hcut ↦ ?_) (fun hcut ↦ ?_)
  · rcases le_or_gt γ (21757 / 50000 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellNineTen_under₁ hωlo (by linarith) h1 hy hcut
    · exact admitsPartition₄_cellNineTen_under₂ hωlo (by linarith) (by linarith) hy hcut
  · rcases le_or_gt γ (784 / 1875 - 2 * ω₀ - slack) with h1 | h1
    · exact admitsPartition₄_cellNineTen_over₁ hωlo (by linarith) h1 hy hcut
    · rcases le_or_gt γ (2193 / 5000 - 2 * ω₀ - slack) with h2 | h2
      · exact admitsPartition₄_cellNineTen_over₂ hωlo (by linarith) h2 hy hcut
      · exact admitsPartition₄_cellNineTen_over₃ hωlo (by linarith) (by linarith) hy hcut

/-- **Cell `(9,10)` against the chamber set a consumer of `Gap212.Defs.ConditionD` carries.** -/
theorem admitsPartition₄_cellNineTen_chamberDBand {p : ℝ × ℝ}
    (hp : p ∈ chamberDBand (7 / 1000) (4 / 625) (7 / 1000))
    {y : Fin (9 + 10) → ℝ}
    (hy : y ∈ Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 10 (41 / 2500)) :
    AdmitsPartition₄ y (capD p.1 p.2 0) (capD p.1 p.2 1) (capD p.1 p.2 2)
      (capD p.1 p.2 3) := by
  obtain ⟨hγlo, hγhi, hωlo, hωhi⟩ := hp
  exact admitsPartition₄_cellNineTen_band hωlo hωhi hγlo hγhi hy

/-- **Cell `(9,10)` at the datum's own parameters**, so a consumer does not have to unfold
the cap row: `gap212Params.B j 9 = gap212Cap 9 = 1063 / 5000` at every stratum `j`. -/
theorem admitsPartition₄_cellNineTen_band_atDatum {γ ω₀ : ℝ}
    (j j' : Fin gap212Params.n) (hωlo : 4 / 625 < ω₀) (hωhi : ω₀ ≤ 7 / 1000)
    (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (9 + 10) → ℝ}
    (hy : y ∈ Xi (gap212Params.B j 9) (gap212Params.B j' 10) 9 10
      gap212Params.δ) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_cellNineTen_band hωlo hωhi hγlo hγhi
    (xi_atDatum j j' (by norm_num [gap212Cap]) (by norm_num [gap212Cap]) hy)

/-- The hypotheses of the band theorems above are satisfiable: the chamber point `ω₀ = 7/1000`,
`γ = 2/5` and the constant profile `δ = 41/2500` meet all of them. -/
theorem cellsSub_hypotheses_satisfiable :
    (4 / 625 < (7 / 1000 : ℝ) ∧ (2 / 5 - slack : ℝ) ≤ 2 / 5 ∧
        (2 / 5 : ℝ) ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (777 / 5000 : ℝ) (7 / 40) 1 3 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (7 / 40 : ℝ) (127 / 625) 3 7 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (917 / 5000 : ℝ) (983 / 5000) 4 6 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (917 / 5000 : ℝ) (521 / 2500) 4 8 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (953 / 5000 : ℝ) (521 / 2500) 5 8 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (983 / 5000 : ℝ) (1063 / 5000) 6 9 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (127 / 625 : ℝ) (1081 / 5000) 7 10 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (521 / 2500 : ℝ) (1081 / 5000) 8 10 (41 / 2500) ∧
      (fun _ ↦ (41 / 2500 : ℝ)) ∈
        Xi (1063 / 5000 : ℝ) (1081 / 5000) 9 10 (41 / 2500) := by
  have hsv : slack = 1 / 10 ^ 10 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  refine ⟨⟨by norm_num, by rw [hsv]; norm_num, by rw [hδ, hsv]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 1 3]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 1 3]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 3 7]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 3 7]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 4 6]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 4 6]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 4 8]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 4 8]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 5 8]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 5 8]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 6 9]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 6 9]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 7 10]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 7 10]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 8 10]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 8 10]; norm_num⟩,
    ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩,
      by rw [Finset.sum_const, Gap212.Packing.card_lowGroup 9 10]; norm_num,
      by rw [Finset.sum_const, Gap212.Packing.card_highGroup 9 10]; norm_num⟩⟩

end Gap212
