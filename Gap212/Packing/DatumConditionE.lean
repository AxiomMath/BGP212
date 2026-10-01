/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Defs
public import Gap212.Harman.Challenge
public import Gap212.Packing.DatumFacts
public import Gap212.Packing.TypeIIc
public meta import Gap212.Attr

/-!
# Condition E at the chosen datum, by a genuine split

At `p_⋆` the trivial partition does not discharge Condition E. Its first bin would carry the whole
pooled rough mass, which reaches `1081/2500 = 0.4324` by `Gap212.total_le_datum`, against a first
capacity of `1 - 6ω - 3ξ₃/2 - 8ϵ/3 = 179/500 = 0.358` at `ω(1,1) = 7/1000` and `ξ₃ = 2/5` — short
by `93/1250`. So the mass has to be split, and this module does the splitting.

## The three cases

Write `B m` for the rung `Gap212.gap212Cap m` of the cap row and `T = B m + B m'` for the pooled
bound. Every pair `(m, m')` falls into one of three cases, and the second capacity
`c₂ = 5ω/2 + 3ξ₃/8 - 2ϵ = 67/400 = 0.1675` is what each of them spends:

* `T ≤ c₁`: everything fits in the first bin and the second is empty. This is the trivial
  partition, `Gap212.Packing.admitsPartition₂_of_total_le`.
* `min(B m, B m') ≤ c₂`: the two rough *sides* are already a partition, with sums bounded by `B m`
  and `B m'` by `Gap212.Packing.Xi` itself. Put the larger-bounded side in the first bin — each
  rung is at most `1081/5000 < c₁` — and the smaller in the second. Since the partition predicate
  lets either side be the first bin, both orientations are available, and this covers every pair
  with `m ≤ 2` or `m' ≤ 2`: the third rung is the first to exceed `c₂`, `B 2 = 397/2500 = 0.1588`
  against `0.1675`.
* otherwise `m, m' ≥ 3` and a genuine regrouping is needed. Take the side `k` with the larger count
  and fill the second bin greedily from it. Each of its coordinates is at most
  `M = B k - (k-1)δ`, because the other `k - 1` coordinates of that side are each at least `δ`, so
  the greedy sum overshoots its target `T - c₁` by less than `M` and lands in `[T - c₁, c₂]`. The
  first bin then carries at most `T - (T - c₁) = c₁`.

## What the third case needs, in exact rationals

Two inequalities about the cap row, both slack-free and both proved here by cases on the rung:

    B k - (k-1)δ ≤ 777/5000 = 0.1554          for every k
    3 B k - (k-1)δ ≤ 639/1250 = 0.5112        for every k ≥ 3

The first is attained at `k = 1` and the second at `k = 7`. Against `c₂ = 0.1675` and
`c₁ + c₂ = 1051/2000 = 0.5255` they leave `0.0121` and `0.0143`. Monotonicity of the row turns the
second into the third case's requirement, `B m + B m' + M ≤ c₁ + c₂` at `k = max(m, m')`. The
slack `ϵ = 10⁻¹⁰` is far below every margin here.

## The capacities are the bare ones

Both capacities are `Gap212.Defs.ConditionE`'s as printed, with no inward inset:
`Gap212.Extraction.two_factor_strict` lands its divisor strictly inside the bare open window, the
upper end from the retreat `1 - ε₀` and the lower end from the modulus threshold `ε₁`.

## Main results

* `Gap212.Packing.exists_subset_sum_mem_Icc_subset`: the greedy filling lemma **on a block** — a
  subset of a prescribed `Finset` whose sum lands in `[D, D + w]`. The reusable engine.
* `Gap212.Packing.le_sub_of_mem_Xi_left`, `le_sub_of_mem_Xi_right`: the coordinate bound
  `yᵢ ≤ B - (mₖ - 1)δ` on each side of the check set.
* `Gap212.Packing.admitsPartition₂_of_caps_left`, `admitsPartition₂_of_caps_right`: the free block
  split, in its two orientations.
* `Gap212.Packing.admitsPartition₂_of_block_greedy`: the greedy regrouping, stated for an arbitrary
  block of an arbitrary tuple.
* `Gap212.conditionE_at_datum`: Condition E holds at `p_⋆` for every pair of rough-factor counts.
-/

@[expose] public section

namespace Gap212.Packing

open Finset

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {ℓ m₁ m₂ : ℕ}

/-! ## The greedy engine on a block -/

/-- **The subset-sum filling lemma, on a block.** If every entry of `y` on a `Finset` `S` is at
most `w ≥ 0`, and the mass of `S` reaches `D ≥ 0`, then some subset of `S` has sum in `[D, D + w]`.

`Gap212.Packing.exists_subset_sum_mem_Icc` is the case `S = univ`, and this is the form the packing
arguments need: the bound `w` on one coordinate holds only *within* a single rough side, where the
other coordinates of that side crowd it from below, and never on the whole tuple. The reduction
is by zeroing `y` off `S`, which neither breaks the entry bound (as `0 ≤ w`) nor changes the total,
and intersecting the returned subset with `S`. -/
theorem exists_subset_sum_mem_Icc_subset (S : Finset (Fin ℓ)) (y : Fin ℓ → 𝕜) (w D : 𝕜)
    (hw : ∀ i ∈ S, y i ≤ w) (hw0 : 0 ≤ w) (hD : 0 ≤ D) (htot : D ≤ ∑ i ∈ S, y i) :
    ∃ J ⊆ S, D ≤ ∑ i ∈ J, y i ∧ ∑ i ∈ J, y i ≤ D + w := by
  classical
  set z : Fin ℓ → 𝕜 := fun i ↦ if i ∈ S then y i else 0 with hz
  have hzS : ∀ I : Finset (Fin ℓ), ∑ i ∈ I, z i = ∑ i ∈ I ∩ S, y i := by
    intro I
    simp only [hz]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
  have hzw : ∀ i, z i ≤ w := by
    intro i
    simp only [hz]
    split_ifs with h
    · exact hw i h
    · exact hw0
  have htot' : D ≤ ∑ i, z i := by
    rw [hzS univ, Finset.univ_inter]
    exact htot
  obtain ⟨I, h1, h2⟩ := exists_subset_sum_mem_Icc z w D hzw hw0 hD htot'
  refine ⟨I ∩ S, Finset.inter_subset_right, ?_, ?_⟩
  · rw [← hzS I]; exact h1
  · rw [← hzS I]; exact h2

/-! ## The coordinate bound

A single coordinate of a rough side cannot be larger than that side's cap less what the side's
other coordinates must carry, each of them being at least `δ`. -/

/-- **The coordinate bound on the first rough side.** For a tuple of the check set, a coordinate
indexed below `m₁` is at most `B₁ - (m₁ - 1)δ`: the other `m₁ - 1` coordinates of that side are
each at least `δ`, and the whole side is capped by `B₁`. -/
theorem le_sub_of_mem_Xi_left {B₁ B₂ δ : 𝕜} {y : Fin (m₁ + m₂) → 𝕜}
    (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) {i : Fin (m₁ + m₂)} (hi : (i : ℕ) < m₁) :
    y i ≤ B₁ - ((m₁ - 1 : ℕ) : 𝕜) * δ := by
  classical
  set T : Finset (Fin (m₁ + m₂)) := univ.filter (fun j : Fin (m₁ + m₂) ↦ (j : ℕ) < m₁) with hT
  have hiT : i ∈ T := by simp [hT, hi]
  have hcard : T.card = m₁ := by
    rw [hT, Fin.card_filter_val_lt]
    omega
  have hcard' : (T.erase i).card = m₁ - 1 := by rw [Finset.card_erase_of_mem hiT, hcard]
  have hlow : ((m₁ - 1 : ℕ) : 𝕜) * δ ≤ ∑ j ∈ T.erase i, y j := by
    have h := Finset.card_nsmul_le_sum (T.erase i) y δ fun j _ ↦ (hy.1 j).1
    rw [hcard'] at h
    simpa [nsmul_eq_mul] using h
  have hsplit : ∑ j ∈ T, y j = y i + ∑ j ∈ T.erase i, y j := (Finset.add_sum_erase T y hiT).symm
  have hcap : ∑ j ∈ T, y j ≤ B₁ := hy.2.1
  linarith

/-- **The coordinate bound on the second rough side**, `yᵢ ≤ B₂ - (m₂ - 1)δ` for an index at or
above `m₁`. -/
theorem le_sub_of_mem_Xi_right {B₁ B₂ δ : 𝕜} {y : Fin (m₁ + m₂) → 𝕜}
    (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) {i : Fin (m₁ + m₂)} (hi : ¬ ((i : ℕ) < m₁)) :
    y i ≤ B₂ - ((m₂ - 1 : ℕ) : 𝕜) * δ := by
  classical
  set T : Finset (Fin (m₁ + m₂)) := univ.filter (fun j : Fin (m₁ + m₂) ↦ ¬ ((j : ℕ) < m₁)) with hT
  have hiT : i ∈ T := by
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  have hcard : T.card = m₂ := by
    have h : T.card + (univ.filter (fun j : Fin (m₁ + m₂) ↦ (j : ℕ) < m₁)).card
        = (univ : Finset (Fin (m₁ + m₂))).card := by
      rw [hT, Finset.filter_not, Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)]
    rw [Fin.card_filter_val_lt] at h
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  have hcard' : (T.erase i).card = m₂ - 1 := by rw [Finset.card_erase_of_mem hiT, hcard]
  have hlow : ((m₂ - 1 : ℕ) : 𝕜) * δ ≤ ∑ j ∈ T.erase i, y j := by
    have h := Finset.card_nsmul_le_sum (T.erase i) y δ fun j _ ↦ (hy.1 j).1
    rw [hcard'] at h
    simpa [nsmul_eq_mul] using h
  have hsplit : ∑ j ∈ T, y j = y i + ∑ j ∈ T.erase i, y j := (Finset.add_sum_erase T y hiT).symm
  have hcap : ∑ j ∈ T, y j ≤ B₂ := hy.2.2
  linarith

/-! ## The free block split

The two rough sides of the check set already *are* a two-block partition, with the two caps as
their bounds. So whenever one cap fits in the second capacity and the other in the first, there is
nothing to compute. `Gap212.Packing.AdmitsPartition₂` places no constraint on which set is the
first bin, so both orientations are available and it is the *smaller* cap that has to clear
`c₂`. -/

omit [IsStrictOrderedRing 𝕜] in
/-- The free split with the first rough side in the first bin: `B₁ ≤ c₁` and `B₂ ≤ c₂`. -/
theorem admitsPartition₂_of_caps_left {B₁ B₂ c₁ c₂ δ : 𝕜} {y : Fin (m₁ + m₂) → 𝕜}
    (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) (h₁ : B₁ ≤ c₁) (h₂ : B₂ ≤ c₂) : AdmitsPartition₂ y c₁ c₂ := by
  classical
  refine ⟨univ.filter (fun i : Fin (m₁ + m₂) ↦ (i : ℕ) < m₁), hy.2.1.trans h₁, ?_⟩
  rw [← Finset.filter_not]
  exact hy.2.2.trans h₂

omit [IsStrictOrderedRing 𝕜] in
/-- The free split with the second rough side in the first bin: `B₂ ≤ c₁` and `B₁ ≤ c₂`. -/
theorem admitsPartition₂_of_caps_right {B₁ B₂ c₁ c₂ δ : 𝕜} {y : Fin (m₁ + m₂) → 𝕜}
    (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) (h₁ : B₂ ≤ c₁) (h₂ : B₁ ≤ c₂) : AdmitsPartition₂ y c₁ c₂ := by
  classical
  refine ⟨univ.filter (fun i : Fin (m₁ + m₂) ↦ ¬ ((i : ℕ) < m₁)), hy.2.2.trans h₁, ?_⟩
  have hcompl : univ \ univ.filter (fun i : Fin (m₁ + m₂) ↦ ¬ ((i : ℕ) < m₁))
      = univ.filter (fun i : Fin (m₁ + m₂) ↦ (i : ℕ) < m₁) := by
    ext j; simp
  rw [hcompl]
  exact hy.2.1.trans h₂

/-! ## The greedy regrouping -/

/-- **The greedy regrouping.** Let `S` be a block of indices carrying mass at most `bin`, whose
complement carries at most `bout`, with every coordinate of `S` at most `w` and every coordinate of
the tuple nonnegative. If `bout ≤ c₁`, `w ≤ c₂` and `bin + bout + w ≤ c₁ + c₂`, the tuple admits
a two-block partition at capacities `c₁`, `c₂`.

The second bin is filled greedily from `S` alone, to the target `D = max 0 (total - c₁)`. The
target is reachable inside `S` because the complement's mass `bout` already fits in `c₁`, and the
greedy sum overshoots it by less than `w`, so it stays within `c₂` — by `w ≤ c₂` if the target is
`0`, and by `bin + bout + w ≤ c₁ + c₂` otherwise. The first bin is the rest, carrying
`total - D ≤ c₁` by the choice of `D`.

Only the block's *maximal coordinate* enters, never its cardinality, which is what makes this
usable uniformly in the rough-factor counts. -/
theorem admitsPartition₂_of_block_greedy {y : Fin ℓ → 𝕜} {S : Finset (Fin ℓ)}
    {bin bout c₁ c₂ w : 𝕜} (hynn : ∀ i, 0 ≤ y i)
    (hw : ∀ i ∈ S, y i ≤ w) (hw0 : 0 ≤ w) (hwc : w ≤ c₂)
    (hin : ∑ i ∈ S, y i ≤ bin) (hout : ∑ i ∈ univ \ S, y i ≤ bout)
    (hoc : bout ≤ c₁) (hcap : bin + bout + w ≤ c₁ + c₂) :
    AdmitsPartition₂ y c₁ c₂ := by
  classical
  have hsplitS : (∑ i ∈ S, y i) + ∑ i ∈ univ \ S, y i = ∑ i, y i := Finset.sum_add_sum_compl S y
  set D : 𝕜 := max 0 (∑ i, y i - c₁) with hD
  have hD0 : 0 ≤ D := le_max_left _ _
  have hDtot : ∑ i, y i - c₁ ≤ D := le_max_right _ _
  have hDS : D ≤ ∑ i ∈ S, y i := by
    refine max_le (Finset.sum_nonneg fun i _ ↦ hynn i) ?_
    linarith
  obtain ⟨J, hJS, hJ1, hJ2⟩ := exists_subset_sum_mem_Icc_subset S y w D hw hw0 hD0 hDS
  have hsplitJ : (∑ i ∈ J, y i) + ∑ i ∈ univ \ J, y i = ∑ i, y i := Finset.sum_add_sum_compl J y
  have hDw : D + w ≤ c₂ := by
    rcases le_total (∑ i, y i - c₁) 0 with h | h
    · rw [hD, max_eq_left h]; linarith
    · rw [hD, max_eq_right h]; linarith
  -- The second bin is `J`; the first is everything else.
  refine ⟨univ \ J, by linarith, ?_⟩
  have hJJ : univ \ (univ \ J) = J := by simp
  rw [hJJ]
  linarith

end Gap212.Packing

namespace Gap212

open Finset Gap212.Bridges Gap212.Defs Gap212.Packing

/-! ## The cap row against the two capacities

The three cases are driven by facts about the row `Gap212.gap212Cap`, all of them exact rational
arithmetic: it is monotone, it never exceeds `1081/5000` (`Gap212.gap212Cap_le`), its largest
possible coordinate bound is `777/5000`, and the greedy requirement `3 B k - (k-1)δ` never exceeds
`639/1250` from the third rung on. -/

/-- **The largest coordinate a rough side can carry is `777/5000`.** A side with `k` coordinates
capped by `B k` has each coordinate at most `B k - (k-1)δ`, since the other `k - 1` are at least
`δ` each; that quantity is largest at `k = 1`, where it is the first rung `777/5000` itself,
because every later rung rises by less than `δ = 41/2500`. -/
theorem gap212Cap_sub_le (k : ℕ) :
    gap212Cap k - ((k - 1 : ℕ) : ℝ) * (41 / 2500) ≤ 777 / 5000 := by
  by_cases h : 11 ≤ k
  · have hcap : gap212Cap k = 1081 / 5000 := gap212Cap_of_ten_le (by omega)
    have hk : (10 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
      have : (10 : ℕ) ≤ k - 1 := by omega
      exact_mod_cast this
    rw [hcap]
    nlinarith
  · have h' : k < 11 := by omega
    interval_cases k <;> norm_num [gap212Cap]

/-- **The greedy requirement of the third case.** For every rung from the third on,
`3 B k - (k-1)δ ≤ 639/1250 = 0.5112`, with equality at `k = 7`.

This is what makes the greedy fill land inside the second capacity: at `k = max(m, m')` the pooled
bound `B m + B m'` is at most `2 B k` by monotonicity, and the block's maximal coordinate is
`B k - (k-1)δ`, so the three together are at most the left side here — against
`c₁ + c₂ = 1051/2000 = 0.5255`. -/
theorem gap212Cap_triple_sub_le {k : ℕ} (hk : 3 ≤ k) :
    3 * gap212Cap k - ((k - 1 : ℕ) : ℝ) * (41 / 2500) ≤ 639 / 1250 := by
  by_cases h : 11 ≤ k
  · have hcap : gap212Cap k = 1081 / 5000 := gap212Cap_of_ten_le (by omega)
    have hk' : (10 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
      have : (10 : ℕ) ≤ k - 1 := by omega
      exact_mod_cast this
    rw [hcap]
    nlinarith
  · have h' : k < 11 := by omega
    interval_cases k <;> norm_num [gap212Cap]

/-! ## Condition E at the datum -/

/-- **Condition E holds at `p_⋆`, at every pair of rough-factor counts.** The capacities are
`Gap212.Defs.ConditionE`'s own — bare, with no inward inset — at the level `ω(1,1)` of the datum's
only band pair (`Gap212.omegaMax_gap212Params`, `7/1000`), at `ξ₃ = 2/5`, and with
`ϵ = Gap212.slack`. Numerically they are `179/500 = 0.358` and `67/400 = 0.1675`, up to
`ϵ = 10⁻¹⁰`.

The trivial partition does not serve: the pooled rough mass reaches `1081/2500 = 0.4324`, exceeding
the first capacity by `93/1250`. The split is the three-case argument of this module's header — the
trivial partition where the pooled bound fits, the free block split where one rung fits in `c₂`
(which is every pair with `m ≤ 2` or `m' ≤ 2`), and the greedy regrouping inside the larger side
otherwise.

The bound `m, m' ≤ ⌊1/δ⌋` is the range `Gap212.Qstar` quantifies over, and is the range the
condition is usually stated at. It is not used: the row is constant from the tenth rung on and the
coordinate bound only improves as the count grows, so the argument is uniform in `m` and `m'`. -/
@[gap212 "lem_condition_E_at_datum"]
theorem conditionE_at_datum (j j' : Fin gap212Params.n) {ξ₃ : ℝ} (hξ₃ : ξ₃ = 2 / 5) {m m' : ℕ}
    (_hm : m ≤ ⌊1 / gap212Params.δ⌋₊) (_hm' : m' ≤ ⌊1 / gap212Params.δ⌋₊) :
    ConditionE (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      (1 - 6 * omegaMax gap212Params j j' - 3 * ξ₃ / 2 - 8 * slack / 3)
      (5 * omegaMax gap212Params j j' / 2 + 3 * ξ₃ / 8 - 2 * slack) := by
  classical
  have hB : ∀ (k : Fin gap212Params.n) (r : ℕ), gap212Params.B k r = gap212Cap r := fun _ _ ↦ rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  -- The cap row is monotone: it rises through its ten rungs and is constant beyond the tenth.
  have hmono : Monotone gap212Cap := by
    refine monotone_nat_of_le_succ fun r ↦ ?_
    by_cases h : 10 ≤ r
    · exact le_of_eq ((gap212Cap_of_ten_le h).trans
        (gap212Cap_of_ten_le (show 10 ≤ r + 1 by omega)).symm)
    · have h' : r < 10 := by omega
      interval_cases r <;> norm_num [gap212Cap]
  -- The two capacities, with `ω(1,1) = 7/1000` and `ξ₃ = 2/5` substituted.
  have hω := omegaMax_gap212Params j j'
  have he₁ : 1 - 6 * omegaMax gap212Params j j' - 3 * ξ₃ / 2 - 8 * slack / 3
      = 179 / 500 - 8 * slack / 3 := by rw [hω, hξ₃]; ring
  have he₂ : 5 * omegaMax gap212Params j j' / 2 + 3 * ξ₃ / 8 - 2 * slack
      = 67 / 400 - 2 * slack := by rw [hω, hξ₃]; ring
  rw [he₁, he₂]
  -- `ϵ = 10⁻¹⁰` is far below every margin below; only these two bounds on it are used.
  have hs0 : (0 : ℝ) < slack := by rw [slack]; norm_num
  have hs1 : slack ≤ 1 / 10 ^ 9 := by rw [slack]; norm_num
  intro y hy
  simp only [hB, hδ] at hy
  have hynn : ∀ i, 0 ≤ y i := fun i ↦ nonneg_of_mem (by norm_num) hy i
  have hinner : ∑ i ∈ univ.filter (fun i : Fin (m + m') ↦ (i : ℕ) < m), y i ≤ gap212Cap m := hy.2.1
  have houter : ∑ i ∈ univ.filter (fun i : Fin (m + m') ↦ ¬ ((i : ℕ) < m)), y i ≤ gap212Cap m' :=
    hy.2.2
  -- **Case 1.** The pooled bound already fits in the first capacity: everything in the first bin.
  by_cases hsmall : gap212Cap m + gap212Cap m' ≤ 179 / 500 - 8 * slack / 3
  · exact admitsPartition₂_of_total_le ((total_le hy).trans hsmall) (by linarith)
  -- Every single rung fits in the first capacity, which is what the free split needs.
  have htop : ∀ r : ℕ, gap212Cap r ≤ 179 / 500 - 8 * slack / 3 := fun r ↦ by
    have := gap212Cap_le r
    linarith
  have h2val : gap212Cap 2 = 397 / 2500 := by norm_num [gap212Cap]
  -- **Case 2.** One side has at most two rough factors, so its rung fits in the second capacity.
  by_cases hm2 : m ≤ 2
  · refine admitsPartition₂_of_caps_right hy (htop m') ?_
    have h := hmono hm2
    rw [h2val] at h
    linarith
  by_cases hm2' : m' ≤ 2
  · refine admitsPartition₂_of_caps_left hy (htop m) ?_
    have h := hmono hm2'
    rw [h2val] at h
    linarith
  -- **Case 3.** Both sides carry at least three rough factors; fill greedily from the larger one.
  have hm3 : 3 ≤ m := by omega
  have hm3' : 3 ≤ m' := by omega
  have hwc : ∀ k : ℕ, gap212Cap k - ((k - 1 : ℕ) : ℝ) * (41 / 2500) ≤ 67 / 400 - 2 * slack :=
    fun k ↦ by
      have := gap212Cap_sub_le k
      linarith
  rcases le_total m' m with hle | hle
  · -- The first side is the larger one.
    obtain ⟨i₀, hi₀⟩ : ∃ i : Fin (m + m'), (i : ℕ) < m :=
      ⟨⟨0, by omega⟩, show 0 < m by omega⟩
    have hw0 : (0 : ℝ) ≤ gap212Cap m - ((m - 1 : ℕ) : ℝ) * (41 / 2500) := by
      have h1 : (41 / 2500 : ℝ) ≤ y i₀ := (hy.1 i₀).1
      have h2 := le_sub_of_mem_Xi_left hy hi₀
      linarith
    have hout : ∑ i ∈ univ \ univ.filter (fun i : Fin (m + m') ↦ (i : ℕ) < m), y i
        ≤ gap212Cap m' := by
      rw [← Finset.filter_not]
      exact houter
    refine admitsPartition₂_of_block_greedy hynn
      (fun i hi ↦ le_sub_of_mem_Xi_left hy (by simpa using hi)) hw0 (hwc m) hinner hout
      (htop m') ?_
    have h3 := gap212Cap_triple_sub_le hm3
    have := hmono hle
    linarith
  · -- The second side is the larger one.
    obtain ⟨i₀, hi₀⟩ : ∃ i : Fin (m + m'), ¬ ((i : ℕ) < m) :=
      ⟨⟨m, by omega⟩, show ¬ m < m from lt_irrefl m⟩
    have hw0 : (0 : ℝ) ≤ gap212Cap m' - ((m' - 1 : ℕ) : ℝ) * (41 / 2500) := by
      have h1 : (41 / 2500 : ℝ) ≤ y i₀ := (hy.1 i₀).1
      have h2 := le_sub_of_mem_Xi_right hy hi₀
      linarith
    have hout : ∑ i ∈ univ \ univ.filter (fun i : Fin (m + m') ↦ ¬ ((i : ℕ) < m)), y i
        ≤ gap212Cap m := by
      have hcompl : univ \ univ.filter (fun i : Fin (m + m') ↦ ¬ ((i : ℕ) < m))
          = univ.filter (fun i : Fin (m + m') ↦ (i : ℕ) < m) := by
        ext i; simp
      rw [hcompl]
      exact hinner
    refine admitsPartition₂_of_block_greedy hynn
      (fun i hi ↦ le_sub_of_mem_Xi_right hy (by simpa using hi)) hw0 (hwc m') houter hout
      (htop m) ?_
    have h3 := gap212Cap_triple_sub_le hm3'
    have := hmono hle
    linarith

end Gap212
