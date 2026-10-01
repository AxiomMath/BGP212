/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.DatumConditionD

/-!
# Condition D at the datum above `541/100000`: the pair dichotomy

`Gap212.conditionD_at_datum_band_5` reaches `ω₀ = 541/100000` and stops because it has nothing left
to read: at `ω₀ = 271/50000` its high branch is at the cell `(1, 3)`, the level is already pinned
to its only value `0`, and the bound `Y/4` on the smallest coordinate meets the reserve `W` with
equality. This file carries Condition D at `p_⋆` from there to `ω₀ = 4/625`, which with the six
bands below it makes the condition a theorem on `[0, 4/625]` — `32/35` of the chamber `[0, 7/1000]`
— and leaves `4/625 < ω₀ ≤ 7/1000`, a band of length `3/5000`, to `Gap212.PackingCertificate`.

## What changes: the dichotomy runs on pairs

Bands two to five ask, of a single coordinate, whether it fits in a small block. This one asks it
of a **pair**, and the negative answer is an *item count* rather than a mass bound: if no two
coordinates fit in block four together then at most one coordinate is at most `4ω₀`, because two
such would sum to at most `8ω₀ = c₄`. So `N - 1` of the coordinates exceed `4ω₀` — twice the floor
a singleton dichotomy yields — and that is what closes the rungs the fifth band's split-pair branch
loses. It is also what makes a *fourth* parked coordinate available: block four holds two
coordinates at the floor above `ω₀ = δ/4` and so does block three, so a pair in each parks `4δ`.

Three further readings come with it.

* **The `(n+1)`-st smallest coordinate, read on one side.**
  `Gap212.Packing.exists_small_coords_subset` generalises `Gap212.Packing.exists_small_coords` from
  `univ` to a `Finset`, so the bound may be read on a single side of the cell, whose mass the check
  set caps by `B_{1,m}` no matter what the other side carries. At the high branch's cell `(4, 4)`
  the pooled bound `Y/8` on the smallest coordinate walls the whole family at `ω₀ = 0.005455`; the
  side bound `B_{1,4}/4` does not.
* **`v ≤ c₂` in place of `v ≤ W` at level zero.** When what is left of the deficit falls below the
  floor, a single unparked coordinate carries it (`Gap212.Packing.admitsPartition₄_of_single`) and
  the only thing asked of that coordinate is that it fit in `c₂` — not that it fit in `c₂` *together
  with* the deficit, which is what a minimal-cardinality subset has to ask. Uniformly in `γ` that
  reads `v ≤ 181/2500 - 2ω₀ - 4ϵ`, and the high branch's cell `(3, 3)` needs exactly it.
* **The level read from the remaining deficit.** Every branch here computes its level from
  `Y - c₁ - P` at its own floor rather than from the whole deficit at the floor `δ`, which holds
  the level to at most `3` where the fifth band's split-pair branch had `6`.

All six branches run through one engine, `Gap212.Packing.admitsPartition₄_of_floor`, which takes
the two parked blocks, the set the fill draws from, the floor on it and the level, and offers both
readings of the window.

## Where this stops

`4/625` is the round numeral below `ω₀ = 0.0065335…`, where the three-parked branch
`Gap212.datumD_band6_ab1_window` fails at the rung `N = 20` with level `2`, the flat pooled mass
`1081/2500` and a third parked coordinate of mass `t ≈ 0.01997` — the point at which parking more
mass and leaving a weaker floor `c₃ - t` exactly balance. It also clears the single-parked branch,
whose pooled reading of the cell `(4, 5)` at level one fails from `ω₀ = 0.00642` on.

That is a wall of *this* reading of the family and not of the family: above `ω₀ = 123/20000` block
four holds **three** coordinates at the floor, so a triple there together with a pair in block
three parks `5δ`, and nothing in this file uses that.

## Main results

* `Gap212.Packing.exists_small_coords_subset`: the small-coordinate count inside a `Finset`.
* `Gap212.Packing.admitsPartition₄_of_block_sets`, `admitsPartition₄_of_parked_le`,
  `admitsPartition₄_of_single`: the partition from explicit blocks, from parked blocks that already
  cover the deficit, and from one unparked coordinate.
* `Gap212.Packing.admitsPartition₄_of_floor`: the packing step at a chosen floor, parked blocks and
  level — the engine all six branches share.
* `Gap212.gap212Cap_le_four`, `Gap212.side_le_four`, `Gap212.side_le_five_except`: the cap-row and
  side-count bounds this band's floors unlock.
* `Gap212.datumD_band6_aa_window`, `datumD_band6_ab1_window`, `datumD_band6_ab2_window`,
  `datumD_band6_b1a_window`, `datumD_band6_b1b_window`, `datumD_band6_b2_window`: the six branches'
  numerical requirements, one per branch, each verified rung by rung or cell by cell and level by
  level.
* `Gap212.conditionD_at_datum_band_6`: Condition D at `p_⋆` for `541/100000 < ω₀ ≤ 4/625`.
-/

@[expose] public section

namespace Gap212.Packing

open Finset

/-! ## Small coordinates inside a subset, and the parked-block engine -/

/-- **At least `n + 1` coordinates of `T` lie below `v`**, provided the mass of `T` does not exceed
`(κ - n) v + n d` for some `κ ≤ #T` — the mass of a profile on `κ` indices with `κ - n` of them at
`v` and `n` at the floor `d`.

`Gap212.Packing.exists_small_coords` is this with `T = univ` and `κ = ℓ`. The generalisation is
what lets the bound on the `(n+1)`-st smallest coordinate be read on *part* of the profile: on one
side of the cell, whose mass the check set caps by `B_{1,m}` independently of the other side, or on
the coordinates left after the parked ones are removed. Reading it on a side is what
`Gap212.conditionD_at_datum_band_6`'s last two branches need, and a lower bound `κ` on `#T` rather
than the exact cardinality is what lets the caller work with a set whose size it knows only
approximately. -/
theorem exists_small_coords_subset {ℓ : ℕ} {y : Fin ℓ → ℝ} {d v κ : ℝ} {n : ℕ}
    {T : Finset (Fin ℓ)} (hd0 : 0 ≤ d) (hd : ∀ i ∈ T, d ≤ y i) (hdv : d ≤ v)
    (hn : (n : ℝ) < κ) (hκ : κ ≤ (T.card : ℝ))
    (hv : ∑ i ∈ T, y i ≤ (κ - n) * v + n * d) :
    n + 1 ≤ (T.filter (fun i ↦ y i ≤ v)).card := by
  classical
  by_contra! hcon
  have hcard := T.card_filter_add_card_filter_not (fun i ↦ y i ≤ v)
  have hnT : n < T.card := by exact_mod_cast hn.trans_le hκ
  have hTlow := sum_lt_sum_of_nonempty (s := T.filter (fun i ↦ ¬ y i ≤ v)) (f := fun _ ↦ v)
    (card_pos.1 (by omega)) fun i hi ↦ not_le.1 (mem_filter.1 hi).2
  have hSlow := card_nsmul_le_sum (T.filter (fun i ↦ y i ≤ v)) y d
    fun i hi ↦ hd i (mem_filter.1 hi).1
  rw [sum_const, nsmul_eq_mul] at hTlow
  rw [nsmul_eq_mul] at hSlow
  have hab : ((T.filter (fun i ↦ y i ≤ v)).card : ℝ)
      + (T.filter (fun i ↦ ¬ y i ≤ v)).card = T.card := by exact_mod_cast hcard
  have han : ((T.filter (fun i ↦ y i ≤ v)).card : ℝ) ≤ n := by
    exact_mod_cast Nat.lt_succ_iff.1 hcon
  nlinarith [sum_filter_add_sum_filter_not T (fun i ↦ y i ≤ v) y,
    mul_nonneg (sub_nonneg.2 hκ) (hd0.trans hdv), mul_nonneg (sub_nonneg.2 han) (sub_nonneg.2 hdv)]

/-- **A partition from three explicitly given blocks.** `J`, `T₃` and `T₄` pairwise disjoint, with
`J` fitting in `c₂`, `T₃` in `c₃`, `T₄` in `c₄` and the rest of the profile in `c₁`.

This is the construction inside `Gap212.Packing.admitsPartition₄_of_blocks`, stated on its own so
that the subset-sum fill and the single-coordinate fill of `Gap212.conditionD_at_datum_band_6` can
share it. -/
theorem admitsPartition₄_of_block_sets {ℓ : ℕ} {y : Fin ℓ → ℝ} {c₁ c₂ c₃ c₄ : ℝ}
    {J T₃ T₄ : Finset (Fin ℓ)} (hJ₃ : Disjoint J T₃) (hJ₄ : Disjoint J T₄) (hTd : Disjoint T₃ T₄)
    (h₁ : (∑ i, y i) - (∑ i ∈ J, y i) - (∑ i ∈ T₃, y i) - (∑ i ∈ T₄, y i) ≤ c₁)
    (h₂ : (∑ i ∈ J, y i) ≤ c₂) (h₃ : (∑ i ∈ T₃, y i) ≤ c₃) (h₄ : (∑ i ∈ T₄, y i) ≤ c₄) :
    AdmitsPartition₄ y c₁ c₂ c₃ c₄ := by
  classical
  have h₃₄ : Disjoint (J ∪ T₃) T₄ := disjoint_union_left.2 ⟨hJ₄, hTd⟩
  refine ⟨univ \ (J ∪ T₃ ∪ T₄), J, T₃,
    disjoint_sdiff_self_left.mono_right (subset_union_left.trans subset_union_left),
    disjoint_sdiff_self_left.mono_right (subset_union_right.trans subset_union_left), hJ₃, ?_,
    h₂, h₃, ?_⟩
  · rw [sum_sdiff_eq_sub (subset_univ _), sum_union h₃₄, sum_union hJ₃]
    linarith
  · rwa [show univ \ (univ \ (J ∪ T₃ ∪ T₄) ∪ J ∪ T₃) = T₄ by
      ext a
      have : a ∈ J ∪ T₃ → a ∉ T₄ := fun h ↦ disjoint_left.1 h₃₄ h
      simp only [mem_sdiff, mem_union, mem_univ, true_and] at this ⊢
      tauto]

/-- **When the parked blocks already cover the deficit, the second block stays empty.** -/
theorem admitsPartition₄_of_parked_le {ℓ : ℕ} {y : Fin ℓ → ℝ} {c₁ c₂ c₃ c₄ : ℝ}
    {T₃ T₄ : Finset (Fin ℓ)} (hTd : Disjoint T₃ T₄) (hc₂ : 0 ≤ c₂)
    (h₁ : (∑ i, y i) - (∑ i ∈ T₃, y i) - (∑ i ∈ T₄, y i) ≤ c₁)
    (h₃ : (∑ i ∈ T₃, y i) ≤ c₃) (h₄ : (∑ i ∈ T₄, y i) ≤ c₄) :
    AdmitsPartition₄ y c₁ c₂ c₃ c₄ :=
  admitsPartition₄_of_block_sets (J := ∅) (Finset.disjoint_empty_left _)
    (Finset.disjoint_empty_left _) hTd (by simpa using h₁) (by simpa using hc₂) h₃ h₄

/-- **One unparked coordinate carries the deficit.** At level zero the mass still to be placed is
below the floor, so a single coordinate outside the parked blocks already covers it, and the only
thing asked of that coordinate is that it fit in `c₂` — not that it fit in `c₂` *together with* the
deficit, which is what the subset-sum fill of `Gap212.Packing.admitsPartition₄_of_blocks` has to
ask.

That difference is the whole of the `c₂` reading: the fill needs `(Y - c₁ - P) + v ≤ c₂`, i.e.
`v ≤ W + P`, while this needs only `v ≤ c₂`, and `c₂ ≥ 1/2 - γ_max - 2ω₀ - ϵ = 181/2500 - 2ω₀ - 4ϵ`
uniformly in `γ`. -/
theorem admitsPartition₄_of_single {ℓ : ℕ} {y : Fin ℓ → ℝ} {c₁ c₂ c₃ c₄ : ℝ}
    {T₃ T₄ : Finset (Fin ℓ)} {i₀ : Fin ℓ} (hTd : Disjoint T₃ T₄)
    (hi₃ : i₀ ∉ T₃) (hi₄ : i₀ ∉ T₄)
    (hlo : (∑ i, y i) - c₁ - (∑ i ∈ T₃, y i) - (∑ i ∈ T₄, y i) ≤ y i₀) (hhi : y i₀ ≤ c₂)
    (h₃ : (∑ i ∈ T₃, y i) ≤ c₃) (h₄ : (∑ i ∈ T₄, y i) ≤ c₄) :
    AdmitsPartition₄ y c₁ c₂ c₃ c₄ :=
  admitsPartition₄_of_block_sets (J := {i₀}) (disjoint_singleton_left.2 hi₃)
    (disjoint_singleton_left.2 hi₄) hTd (by rw [sum_singleton]; linarith)
    (by rwa [sum_singleton]) h₃ h₄

/-- **The packing step at a chosen floor, parked blocks and level.** `T₃` and `T₄` are parked, `T`
is a set of coordinates disjoint from both on which `f` is a floor, `κ ≤ #T`, and `v` is the bound
on the `(n+1)`-st smallest coordinate of `T` that `κ` and the mass of `T` supply. The level `n` is
the one the remaining deficit `Y - c₁ - P` and the floor `f` determine.

At level zero the window may be read as `v ≤ c₂` (one coordinate carries what is left); at any
level it may be read as `(Y - c₁ - P) + v ≤ c₂` (a minimal-cardinality subset does). All six
branches of `Gap212.conditionD_at_datum_band_6` are this lemma at different `T₃`, `T₄`, `T` and
`f`. -/
theorem admitsPartition₄_of_floor {ℓ : ℕ} {y : Fin ℓ → ℝ} {c₁ c₂ c₃ c₄ f v κ : ℝ}
    {T T₃ T₄ : Finset (Fin ℓ)} {n : ℕ}
    (hTd : Disjoint T₃ T₄) (h₃ : (∑ i ∈ T₃, y i) ≤ c₃) (h₄ : (∑ i ∈ T₄, y i) ≤ c₄)
    (hT₃ : Disjoint T T₃) (hT₄ : Disjoint T T₄)
    (hf0 : 0 ≤ f) (hf : ∀ i ∈ T, f ≤ y i) (hfv : f ≤ v)
    (hκ : κ ≤ (T.card : ℝ)) (hnκ : (n : ℝ) < κ)
    (hMv : (∑ i ∈ T, y i) ≤ (κ - n) * v + n * f) (hc₂ : 0 ≤ c₂)
    (hnhi : (∑ i, y i) - c₁ - (∑ i ∈ T₃, y i) - (∑ i ∈ T₄, y i) < ((n : ℝ) + 1) * f)
    (hwin : (n = 0 ∧ v ≤ c₂) ∨
      ((∑ i, y i) - c₁ - (∑ i ∈ T₃, y i) - (∑ i ∈ T₄, y i)) + v ≤ c₂) :
    AdmitsPartition₄ y c₁ c₂ c₃ c₄ := by
  classical
  have hcard := exists_small_coords_subset hf0 hf hfv hnκ hκ hMv
  have hSsub : T.filter (fun i ↦ y i ≤ v) ⊆ T := filter_subset _ _
  have hSv : ∀ i ∈ T.filter (fun i ↦ y i ≤ v), y i ≤ v := fun i hi ↦ (mem_filter.1 hi).2
  rcases hwin with ⟨rfl, hvc⟩ | hvc
  · obtain ⟨i₀, hi₀⟩ := card_pos.1 (by omega : 0 < (T.filter (fun i ↦ y i ≤ v)).card)
    refine admitsPartition₄_of_single hTd (disjoint_left.1 hT₃ (hSsub hi₀))
      (disjoint_left.1 hT₄ (hSsub hi₀)) ?_ ((hSv i₀ hi₀).trans hvc) h₃ h₄
    push_cast at hnhi
    linarith [hf i₀ (hSsub hi₀)]
  · refine admitsPartition₄_of_blocks hTd h₃ h₄ hSv (hf0.trans hfv) hc₂ ?_ hvc
    rw [sdiff_eq_self_of_disjoint
      (disjoint_union_right.2 ⟨hT₃.mono_left hSsub, hT₄.mono_left hSsub⟩)]
    have h := card_nsmul_le_sum _ y f fun i hi ↦ hf i (hSsub hi)
    have hc : (n : ℝ) + 1 ≤ (T.filter (fun i ↦ y i ≤ v)).card := by exact_mod_cast hcard
    rw [nsmul_eq_mul] at h
    linarith [mul_le_mul_of_nonneg_right hc hf0]

/-- `Gap212.Packing.admitsPartition₄_of_floor` with `v` the average `(∑_T y - n f) / (κ - n)`, so
that the caller supplies only a bound `W` on it, multiplied out. -/
private theorem admitsPartition₄_of_floor_avg {ℓ : ℕ} {y : Fin ℓ → ℝ} {c₁ c₂ c₃ c₄ f W κ : ℝ}
    {T T₃ T₄ : Finset (Fin ℓ)} {n : ℕ}
    (hTd : Disjoint T₃ T₄) (h₃ : (∑ i ∈ T₃, y i) ≤ c₃) (h₄ : (∑ i ∈ T₄, y i) ≤ c₄)
    (hT₃ : Disjoint T T₃) (hT₄ : Disjoint T T₄) (hf0 : 0 ≤ f) (hf : ∀ i ∈ T, f ≤ y i)
    (hκ : κ ≤ (T.card : ℝ)) (hnκ : (n : ℝ) < κ) (hc₂ : 0 ≤ c₂)
    (hnhi : (∑ i, y i) - c₁ - (∑ i ∈ T₃, y i) - (∑ i ∈ T₄, y i) < ((n : ℝ) + 1) * f)
    (hW : (∑ i ∈ T, y i) - n * f ≤ (κ - n) * W)
    (hwin : (n = 0 ∧ W ≤ c₂) ∨
      ((∑ i, y i) - c₁ - (∑ i ∈ T₃, y i) - (∑ i ∈ T₄, y i)) + W ≤ c₂) :
    AdmitsPartition₄ y c₁ c₂ c₃ c₄ := by
  have hsub : 0 < κ - n := sub_pos.2 hnκ
  have hv := mul_div_cancel₀ ((∑ i ∈ T, y i) - n * f) hsub.ne'
  have hvW : ((∑ i ∈ T, y i) - n * f) / (κ - n) ≤ W := (div_le_iff₀' hsub).2 hW
  have hTf := card_nsmul_le_sum T y f hf
  rw [nsmul_eq_mul] at hTf
  refine admitsPartition₄_of_floor hTd h₃ h₄ hT₃ hT₄ hf0 hf
    (le_of_mul_le_mul_left ?_ hsub) hκ hnκ (by linarith) hc₂ hnhi
    (hwin.imp (fun h ↦ ⟨h.1, hvW.trans h.2⟩) fun h ↦ by linarith)
  rw [hv]
  linarith [mul_le_mul_of_nonneg_right hκ hf0]
end Gap212.Packing

namespace Gap212

open Finset Gap212.Bridges Gap212.Defs Gap212.Packing

/-- **`B_{1,m} ≤ 917/5000` for `m ≤ 4`.** -/
theorem gap212Cap_le_four {m : ℕ} (hm : m ≤ 4) : gap212Cap m ≤ 917 / 5000 := by
  interval_cases m <;> norm_num [gap212Cap]

/-- **Above `ω₀ = 541/100000` a side of five or more rough factors cannot clear `c₄`.** -/
theorem side_le_four {m : ℕ} {w : ℝ} (hw0 : 541 / 100000 < w)
    (h : (m : ℝ) * (8 * w) ≤ gap212Cap m) : m ≤ 4 := by
  by_contra hcon
  have hcap := gap212Cap_le m
  obtain rfl | hm : m = 5 ∨ 6 ≤ m := by omega
  · norm_num [gap212Cap] at h
    linarith
  · have : (6 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith

/-- **Above `ω₀ = 541/100000` a side of six or more rough factors cannot clear `c₃` off one
coordinate.** `Gap212.side_le_six_except` sharpened by this band's floor. -/
theorem side_le_five_except {m : ℕ} {w : ℝ} (hw0 : 541 / 100000 < w)
    (h : ((m : ℝ) - 1) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 41 / 2500 ≤ gap212Cap m) :
    m ≤ 5 := by
  by_contra hcon
  have hcap := gap212Cap_le m
  obtain rfl | hm : m = 6 ∨ 7 ≤ m := by omega
  · norm_num [gap212Cap] at h
    linarith
  · have : (7 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith

set_option maxHeartbeats 4000000 in
-- One `linarith` per pair `(N, n)`.
/-- **The four-parked branch's window.** Two coordinates share block four, two more share block
three, so `P ≥ 4δ`, and the floor on the twenty-odd coordinates left is `δ`. The engine draws its
small coordinates from `T = univ \ {i₁, i₂, k, l}`, so `#T ≥ N - 4` and its mass is at most
`Y - 4δ`, and the requirement is `Y - 4δ - nδ ≤ (N - 4 - n)(W + 4δ)`.

Never the binding branch: its least slack over `4 ≤ N ≤ 26` and `n ≤ 3` is `1.20·10⁻²`, at
`N = 20`, `n = 3` and the flat pooled mass. Four parked coordinates is what the pair dichotomy buys
over the three of `Gap212.conditionD_at_datum_band_4`. -/
theorem datumD_band6_aa_window {N nn Y w : ℝ} {k n : ℕ} (hNk : N = k) (hnn : nn = n)
    (hk1 : 3 ≤ k) (hk2 : k ≤ 26) (hnK : n ≤ 3)
    (hlev : nn * (41 / 2500)
      ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) - 4 * (41 / 2500))
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw : w ≤ 4 / 625) :
    n + 4 < k ∧
      Y - 4 * (41 / 2500) - nn * (41 / 2500)
        ≤ (N - 4 - nn)
          * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 4 * (41 / 2500)) := by
  subst hNk hnn
  interval_cases k <;> interval_cases n <;>
    push_cast at hlev hYlo h1 h2 h3 h4 h5 h6 <;>
    refine ⟨?_, ?_⟩ <;> first | omega | (push_cast; linarith)


set_option maxHeartbeats 4000000 in
-- One `linarith` per pair `(N, n)`.
/-- **The three-parked branch's window.** Two coordinates share block four and a third, of mass
`t = y k ∈ [δ, c₃]`, goes into block three, so `P ≥ 2δ + t`; and no *pair* of the remaining
coordinates fits in block three, which with `k` among them says `y k + y l > c₃`, i.e. every
remaining coordinate exceeds `c₃ - t`. So the floor `f` on `T = univ \ {i₁, i₂, k}` obeys both
`δ ≤ f` and `c₃ - t ≤ f`, and the requirement is `Y - 3δ - n f ≤ (N - 3 - n)(W + 2δ + t)`.

The trade-off in `t` is the point: a larger third coordinate parks more mass but leaves a weaker
floor, and both readings are carried, so `t` is a free variable here rather than being fixed at `δ`.
Fixing it at `δ` — window `W + 3δ`, floor `c₃ - δ` — stops this branch at `ω₀ = 0.0060142857`.
**This is the branch that walls the band**: its least slack over `4 ≤ N ≤ 26`, `n ≤ 4` and
`t ∈ [δ, c₃]` is `6.40·10⁻⁴`, at `N = 20`, `n = 2`, `t ≈ 0.01997` and the flat pooled mass, and it
is the first to fail above `ω₀ = 0.0065335`. -/
theorem datumD_band6_ab1_window {N nn Y w t f : ℝ} {k n : ℕ} (hNk : N = k) (hnn : nn = n)
    (hk1 : 3 ≤ k) (hk2 : k ≤ 26) (hnK : n ≤ 4)
    (htlo : 41 / 2500 ≤ t) (hflo : 41 / 2500 ≤ f) (hfc : 4 * w + 41 / 2500 - 1 / 10 ^ 10 - t ≤ f)
    (hlev : nn * f
      ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) - 2 * (41 / 2500) - t)
    (hfar : (N - 3) * (4 * w + 41 / 2500 - 1 / 10 ^ 10 - t) + 3 * (41 / 2500) ≤ Y)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw : w ≤ 4 / 625) :
    n + 3 < k ∧
      Y - 3 * (41 / 2500) - nn * f
        ≤ (N - 3 - nn)
          * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 2 * (41 / 2500) + t) := by
  subst hNk hnn
  interval_cases k <;> interval_cases n <;>
    push_cast at hlev hfar hYlo h1 h2 h3 h4 h5 h6 <;>
    refine ⟨?_, ?_⟩ <;> first | omega | (push_cast; linarith)


set_option maxHeartbeats 4000000 in
-- One `linarith` per pair `(N, n)`.
/-- **The pair-and-floor branch's window.** Two coordinates share block four, block three is empty
and every other coordinate exceeds `c₃`, so `P ≥ 2δ`, the floor on `T = univ \ {i₁, i₂}` is `c₃`,
and the requirement is `Y - 2δ - n c₃ ≤ (N - 2 - n)(W + 2δ)`.

`Gap212.datumD_band4_pairfloor_core` with the level read as an integer from the *remaining* deficit
rather than eliminated continuously from the whole one. Least slack `6.70·10⁻³`, at `N = 6`. -/
theorem datumD_band6_ab2_window {N nn Y w : ℝ} {k n : ℕ} (hNk : N = k) (hnn : nn = n)
    (hk1 : 3 ≤ k) (hk2 : k ≤ 26) (hnK : n ≤ 2)
    (hlev : nn * (4 * w + 41 / 2500 - 1 / 10 ^ 10)
      ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) - 2 * (41 / 2500))
    (hfar : (N - 2) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 2 * (41 / 2500) ≤ Y)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw : w ≤ 4 / 625) :
    n + 2 < k ∧
      Y - 2 * (41 / 2500) - nn * (4 * w + 41 / 2500 - 1 / 10 ^ 10)
        ≤ (N - 2 - nn)
          * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 2 * (41 / 2500)) := by
  subst hNk hnn
  interval_cases k <;> interval_cases n <;>
    push_cast at hlev hfar hYlo h1 h2 h3 h4 h5 h6 <;>
    refine ⟨?_, ?_⟩ <;> first | omega | (push_cast; linarith)


set_option maxHeartbeats 4000000 in
-- One `linarith` per pair `(N, n)`.
/-- **The split-pair branch's window, with the pair chosen by the pair dichotomy.** No two
coordinates fit in block four together, `i₁` fits in block four and `i₂ ≠ i₁` fits in block three,
so `P = y i₁ + y i₂ > c₄`; and *at most one* coordinate is at most `4ω₀`, since two such would sum
to at most `8ω₀ = c₄`. That is the item count: the floor on all but one coordinate is `4ω₀`, twice
the floor `2ω₀` a singleton dichotomy would give and enough to kill the rung `N = 20` outright
above `ω₀ = 0.00615`.

The engine draws from `T = univ \ ({i₁, i₂} ∪ X)` with `X` the at-most-one small coordinate, so
`#T ≥ N - 3` and its mass is at most `Y - 2δ`; the requirement is
`Y - 2δ - n·4ω₀ ≤ (N - 3 - n)(W + 8ω₀)`. Least slack `6.01·10⁻⁵`, at `N = 20`, `n = 3` and
`ω₀ ≈ 0.0054224`. -/
theorem datumD_band6_b1a_window {N nn Y w : ℝ} {k n : ℕ} (hNk : N = k) (hnn : nn = n)
    (hk1 : 3 ≤ k) (hk2 : k ≤ 26) (hnK : n ≤ 3)
    (hlev : nn * (4 * w) ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) - 8 * w)
    (hfar : (N - 1) * (4 * w) + 41 / 2500 ≤ Y)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 541 / 100000 < w) (hw : w ≤ 4 / 625) :
    n + 3 < k ∧
      Y - 2 * (41 / 2500) - nn * (4 * w)
        ≤ (N - 3 - nn)
          * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 8 * w) := by
  subst hNk hnn
  interval_cases k <;> interval_cases n <;>
    push_cast at hlev hfar hYlo h1 h2 h3 h4 h5 h6 <;>
    refine ⟨?_, ?_⟩ <;> first | omega | (push_cast; linarith)

set_option maxHeartbeats 4000000 in
-- One `linarith` per triple `(m, m', n)`.
/-- **The single-parked branch's window.** Only `i₁` is parked, in block four, every other
coordinate exceeds `c₃`, so `P ≥ δ` and the floor on `T = univ \ {i₁}` is `c₃`;
`Gap212.side_le_five_except` caps both side counts at five, so the cell is enumerated and the
pooled mass is the exact cell maximum. The requirement is `Y - δ - n c₃ ≤ (N - 1 - n)(W + δ)`.

`Gap212.datumD_band5_single_window` with the level read from the *remaining* deficit and the floor
`c₃` rather than `δ` — which is what a level of `1` instead of up to `4` buys. Reading it pooled
rather than on a side is enough here and only just: the cell `(4, 5)` at level one fails from
`ω₀ = 0.00642` on, which is why this band stops at `4/625 = 0.0064`. Least slack `1.58·10⁻³`, at
`(5, 5)`, level one, `ω₀ ≈ 0.0060288`. -/
theorem datumD_band6_b1b_window {nn Y w : ℝ} {m m' n : ℕ} (hnn : nn = n) (hm : m ≤ 5)
    (hm' : m' ≤ 5) (hnK : n ≤ 1)
    (hlev : nn * (4 * w + 41 / 2500 - 1 / 10 ^ 10)
      ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) - 41 / 2500)
    (hfar : (((m : ℝ) + (m' : ℝ)) - 1) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 41 / 2500 ≤ Y)
    (hYlo : ((m : ℝ) + (m' : ℝ)) * (41 / 2500) ≤ Y)
    (hYside : Y ≤ gap212Cap m + gap212Cap m')
    (hw : w ≤ 4 / 625) :
    n + 1 < m + m' ∧
      Y - 41 / 2500 - nn * (4 * w + 41 / 2500 - 1 / 10 ^ 10)
        ≤ (((m : ℝ) + (m' : ℝ)) - 1 - nn)
          * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 41 / 2500) := by
  subst hnn
  interval_cases m <;> interval_cases m' <;> interval_cases n <;>
    norm_num [gap212Cap] at hlev hfar hYlo hYside <;>
    refine ⟨?_, ?_⟩ <;> first | omega | (push_cast; linarith)

set_option maxHeartbeats 4000000 in
-- One `linarith` per triple `(m, m', n)`, with four readings to choose from.
/-- **The high branch's window, read on either side and by either route.** Every coordinate exceeds
`c₄ = 8ω₀`, both small blocks are empty, and `Gap212.side_le_four` caps both side counts at four.

Two things are offered here that `Gap212.datumD_band5_high_window` does not have. The bound on the
`(n+1)`-st smallest coordinate is read on a *side*, whose `m` coordinates have mass at most
`B_{1,m}` no matter what the other side carries, rather than pooled over the whole profile. And the
window may be read as `v ≤ c₂` rather than `v ≤ W`: at level zero what is left of the deficit is
below the floor `c₄`, so one coordinate carries it and all that is asked is that it fit in `c₂`,
which is at least `181/2500 - 2ω₀ - 4ϵ` uniformly in `γ`. The cell `(3, 3)` needs that reading —
its `B_{1,3}/3 = 0.0583` exceeds the reserve `W = 0.0532` — while `(2, 2)` needs the other, its
`B_{1,2}/2 = 0.0794` exceeding `c₂`'s guaranteed `0.0596` but not its reserve `0.0856`. So all four
readings are offered and the caller takes whichever holds. Least slack `1.27·10⁻³`, at `(3, 3)`. -/
theorem datumD_band6_b2_window {nn Y w : ℝ} {m m' n : ℕ} (hnn : nn = n) (hm : m ≤ 4)
    (hm' : m' ≤ 4) (hnK : n ≤ 1)
    (hs : (m : ℝ) * (8 * w) ≤ gap212Cap m) (hs' : (m' : ℝ) * (8 * w) ≤ gap212Cap m')
    (hYf : ((m : ℝ) + (m' : ℝ)) * (8 * w) ≤ Y)
    (hYside : Y ≤ gap212Cap m + gap212Cap m')
    (hlev : nn * (8 * w) ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10))
    (hw : w ≤ 4 / 625) :
    (n = 0 ∧ n < m ∧ gap212Cap m - nn * (8 * w)
        ≤ ((m : ℝ) - nn) * (181 / 2500 - 2 * w - 4 / 10 ^ 10)) ∨
      (n < m ∧ gap212Cap m - nn * (8 * w)
        ≤ ((m : ℝ) - nn) * (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)) ∨
      (n = 0 ∧ n < m' ∧ gap212Cap m' - nn * (8 * w)
        ≤ ((m' : ℝ) - nn) * (181 / 2500 - 2 * w - 4 / 10 ^ 10)) ∨
      (n < m' ∧ gap212Cap m' - nn * (8 * w)
        ≤ ((m' : ℝ) - nn) * (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)) := by
  subst hnn
  interval_cases m <;> interval_cases m' <;> interval_cases n <;>
    norm_num [gap212Cap] at hs hs' hYf hYside hlev <;>
    first
      | (refine Or.inl ⟨?_, ?_, ?_⟩ <;>
          first | omega | (norm_num [gap212Cap]; linarith))
      | (refine Or.inr (Or.inl ⟨?_, ?_⟩) <;>
          first | omega | (norm_num [gap212Cap]; linarith))
      | (refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)) <;>
          first | omega | (norm_num [gap212Cap]; linarith))
      | (refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)) <;>
          first | omega | (norm_num [gap212Cap]; linarith))
      | (exfalso; linarith)

set_option maxHeartbeats 2000000 in
-- Six branches, chosen by a dichotomy on *pairs* rather than on singletons, each parking a
-- different set of coordinates and then filling the second block.
/-- **Condition D at `p_⋆` for every cell, every `γ`, and every level `541/100000 < ω₀ ≤ 4/625`.**

`Gap212.conditionD_at_datum_band_5` ends at `ω₀ = 271/50000` because its level is already pinned to
its only value and it has nothing left to read. What this band changes is the *dichotomy*. Bands
two to five ask, of single coordinates, whether one fits in a small block; this one asks it of
**pairs**, and the negative answer is an item count rather than a mass bound: if no two coordinates
fit in block four together then at most one coordinate is at most `4ω₀`, because two such would sum
to at most `8ω₀ = c₄`. So `N - 1` coordinates exceed `4ω₀` — twice the floor a singleton dichotomy
gives — which is what closes the rungs the fifth band's split-pair branch loses.

Three further readings come with it.

* **A fourth parked coordinate.** `c₄ = 8ω₀` holds two coordinates at the floor above `ω₀ = δ/4`,
  and `c₃ = 4ω₀ + δ - ϵ` holds two above `ω₀ = δ/4` as well, so a pair in each block parks `4δ` —
  `Gap212.datumD_band6_aa_window`. The fifth band could park three.
* **The `(n+1)`-st smallest coordinate read on one side.** The check set caps each side's mass by
  `B_{1,m}` no matter what the other side carries, so `Gap212.Packing.exists_small_coords_subset`
  applied to a side bounds the smallest coordinate by `B_{1,m}/m`, which at the high branch's cell
  `(4, 4)` is far below the pooled `Y/8`. Without it that cell walls the family at `ω₀ = 0.005455`.
* **`v ≤ c₂` instead of `v ≤ W` at level zero.** When what is left of the deficit is below the
  floor, one coordinate carries it and the only thing asked of that coordinate is that it fit in
  `c₂` (`Gap212.Packing.admitsPartition₄_of_single`) — not that it fit in `c₂` *together with* the
  deficit, which is what a minimal-cardinality subset has to ask. Uniformly in `γ` that is
  `v ≤ 181/2500 - 2ω₀ - 4ϵ`, and the high branch's cell `(3, 3)` needs exactly this.

The six branches, with `P` the parked mass and `f` the floor on the coordinates the fill draws
from:

| branch | condition | `P` | `f` |
| --- | --- | --- | --- |
| `A-A` | a pair fits block four, a second pair fits block three | `4δ` | `δ` |
| `A-B1` | a pair fits block four, one more `k` fits block three | `2δ + y k` | `c₃ - y k` |
| `A-B2` | a pair fits block four, every other coordinate `> c₃` | `2δ` | `c₃` |
| `B-1a` | no pair fits block four; `i₁` in block four, `i₂` in three | `> c₄` | `4ω₀` |
| `B-1b` | no pair fits block four; `i₁` in block four, rest `> c₃` | `δ` | `c₃` |
| `B-2` | every coordinate exceeds `c₄` | `0` | `c₄` |

All six run through `Gap212.Packing.admitsPartition₄_of_floor`, and the level is in every case read
from the *remaining* deficit `Y - c₁ - P` at the branch's own floor, which is what keeps it as low
as it is: at most `3` where the fifth band's split-pair branch had `6`.

**`4/625` is where this stops, and the wall is `A-B1`.** Its window fails first, at the rung
`N = 20` with level `2`, the flat pooled mass `1081/2500` and a third parked coordinate of mass
`t ≈ 0.01997` — the trade-off between parking more mass and leaving a weaker floor `c₃ - t` is
exactly balanced there. The failure is at `ω₀ = 0.0065335…`; `4/625` is the round numeral below it
that also clears `B-1b`, whose pooled reading of the cell `(4, 5)` at level one fails from
`ω₀ = 0.00642` on. Together with the six bands below, Condition D at `p_⋆` is a theorem on
`[0, 4/625]`, which is `32/35` of the chamber `[0, 7/1000]`; `4/625 < ω₀ ≤ 7/1000`, a band of length
`3/5000`, is `Gap212.PackingCertificate`. -/
theorem conditionD_at_datum_band_6 (j j' : Fin gap212Params.n) {m m' : ℕ} :
    ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      capD (chamberDBand (omegaMax gap212Params j j') (541 / 100000) (4 / 625)) := by
  classical
  rw [omegaMax_gap212Params j j']
  rintro ⟨γ, w⟩ hp y hy
  have hs : slack = 1 / 10 ^ 10 := by rw [slack]
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  have hγ : 2 / 5 - slack ≤ γ := hp.1
  have hγ' : γ ≤ 1 / 3 + 8 * (7 / 1000 : ℝ) + 7 * gap212Params.δ / 3 + 3 * slack := hp.2.1
  have hw0 : (541 / 100000 : ℝ) < w := hp.2.2.1
  have hw : w ≤ (4 / 625 : ℝ) := hp.2.2.2
  rw [hs] at hγ
  rw [hδ, hs] at hγ'
  have hy' : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ) := hy
  change AdmitsPartition₄ y (capD γ w 0) (capD γ w 1) (capD γ w 2) (capD γ w 3)
  rw [capD_zero, capD_one, capD_two, capD_three, hδ, hs]
  have hc₂ : (0 : ℝ) ≤ 1 / 2 - γ - 2 * w - 1 / 10 ^ 10 := by linarith
  have hc₂m : (181 / 2500 : ℝ) - 2 * w - 4 / 10 ^ 10 ≤ 1 / 2 - γ - 2 * w - 1 / 10 ^ 10 := by
    linarith
  have hc₃ : (0 : ℝ) ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10 := by linarith
  have hc₄ : (0 : ℝ) ≤ 8 * w := by linarith
  by_cases hDle : ∑ i, y i ≤ γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10
  · exact admitsPartition₄_of_total_le hDle hc₂ hc₃ hc₄
  push Not at hDle
  have hYcap : ∑ i, y i ≤ 1081 / 2500 := total_le_datum hy'
  have hYaff : ∑ i, y i ≤ (1546 + 36 * ((m : ℝ) + (m' : ℝ))) / 5000 := total_le_affine_datum hy'
  have hYaff₂ : ∑ i, y i ≤ (1748 + 21 * ((m : ℝ) + (m' : ℝ))) / 5000 :=
    total_le_affine_datum₂ hy'
  have hYaff₃ : ∑ i, y i ≤ (1802 + 18 * ((m : ℝ) + (m' : ℝ))) / 5000 :=
    total_le_affine_datum₃ hy'
  have hYaff₄ : ∑ i, y i ≤ (1456 + 49 * ((m : ℝ) + (m' : ℝ))) / 5000 :=
    total_le_affine_datum₄ hy'
  have hYaff₅ : ∑ i, y i ≤ (1598 + 31 * ((m : ℝ) + (m' : ℝ))) / 5000 :=
    total_le_affine_datum₅ hy'
  have hYaff₆ : ∑ i, y i ≤ (1668 + 26 * ((m : ℝ) + (m' : ℝ))) / 5000 :=
    total_le_affine_datum₆ hy'
  have hYlow : ((m : ℝ) + (m' : ℝ)) * (41 / 2500) ≤ ∑ i, y i := card_delta_le_total hy'
  have hδy : ∀ i, (41 / 2500 : ℝ) ≤ y i := fun i ↦ (hy'.1 i).1
  have hcast : ((m + m' : ℕ) : ℝ) = (m : ℝ) + (m' : ℝ) := by push_cast; ring
  have hN3 : 3 ≤ m + m' := by
    by_contra! hcon
    have : (m : ℝ) + m' ≤ 2 := by exact_mod_cast (by omega : m + m' ≤ 2)
    linarith
  have hN26 : m + m' ≤ 26 := by
    by_contra! hcon
    have : (27 : ℝ) ≤ m + m' := by exact_mod_cast (by omega : 27 ≤ m + m')
    linarith
  -- the pieces of bookkeeping every branch needs, for its exception set `E`
  have hEcard : ∀ E : Finset (Fin (m + m')), (((univ \ E).card : ℕ) : ℝ)
      = (m : ℝ) + (m' : ℝ) - ((E.card : ℕ) : ℝ) := by
    intro E
    have hle : E.card ≤ m + m' := by simpa using card_le_univ E
    rw [card_sdiff, inter_univ, card_univ, Fintype.card_fin, Nat.cast_sub hle, hcast]
  have hEsum : ∀ E : Finset (Fin (m + m')),
      (∑ i ∈ univ \ E, y i) + ∑ i ∈ E, y i = ∑ i, y i :=
    fun E ↦ sum_sdiff (subset_univ E)
  have hEdisj : ∀ (E S : Finset (Fin (m + m'))), S ⊆ E → Disjoint (univ \ E) S :=
    fun E S hSE ↦ disjoint_sdiff_self_left.mono_right hSE
  have hTflo : ∀ (E : Finset (Fin (m + m'))) (f : ℝ), (∀ i ∈ univ \ E, f ≤ y i) →
      ((m : ℝ) + (m' : ℝ) - ((E.card : ℕ) : ℝ)) * f ≤ ∑ i ∈ univ \ E, y i := by
    intro E f hf
    have h := card_nsmul_le_sum (univ \ E) y f hf
    rwa [nsmul_eq_mul, hEcard E] at h
  by_cases hpair4 : ∃ a b : Fin (m + m'), a ≠ b ∧ y a + y b ≤ 8 * w
  · -- **Case A.** Some pair fits in block four; park it there.
    obtain ⟨i₁, i₂, hne12, h12⟩ := hpair4
    have hT₄s : ∑ i ∈ ({i₁, i₂} : Finset (Fin (m + m'))), y i = y i₁ + y i₂ := sum_pair hne12
    have hT₄c : (({i₁, i₂} : Finset (Fin (m + m'))).card) = 2 := card_pair hne12
    by_cases hpair3 : ∃ a b : Fin (m + m'), a ≠ b ∧ a ∉ ({i₁, i₂} : Finset (Fin (m + m'))) ∧
        b ∉ ({i₁, i₂} : Finset (Fin (m + m'))) ∧ y a + y b ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10
    · -- **A-A.** A second pair fits in block three: four coordinates parked, floor `δ`.
      obtain ⟨k₁, k₂, hne34, hk1, hk2, h34⟩ := hpair3
      have hT₃s : ∑ i ∈ ({k₁, k₂} : Finset (Fin (m + m'))), y i = y k₁ + y k₂ := sum_pair hne34
      have hTd : Disjoint ({k₁, k₂} : Finset (Fin (m + m'))) {i₁, i₂} :=
        disjoint_insert_left.2 ⟨hk1, disjoint_singleton_left.2 hk2⟩
      have hEc : ({k₁, k₂} ∪ {i₁, i₂} : Finset (Fin (m + m'))).card = 4 := by
        rw [card_union_of_disjoint hTd, card_pair hne34, hT₄c]
      have hE := hEsum ({k₁, k₂} ∪ {i₁, i₂})
      rw [sum_union hTd, hT₃s, hT₄s] at hE
      by_cases hDr : (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10)
          - (y k₁ + y k₂) - (y i₁ + y i₂) ≤ 0
      · exact admitsPartition₄_of_parked_le hTd hc₂ (by rw [hT₃s, hT₄s]; linarith)
          (by rwa [hT₃s]) (by rwa [hT₄s])
      push Not at hDr
      obtain ⟨n, hnlo, hnhi⟩ := exists_nat_mul_le_lt (d := (41 / 2500 : ℝ)) (by norm_num) hDr.le
      have hlev : (n : ℝ) * (41 / 2500)
          ≤ (∑ i, y i) - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
            - 4 * (41 / 2500) := by linarith [hδy k₁, hδy k₂, hδy i₁, hδy i₂]
      have hnK : n ≤ 3 := by
        by_contra hcon
        have : (4 : ℝ) ≤ n := by exact_mod_cast (by omega : 4 ≤ n)
        linarith
      obtain ⟨hroom, hineq⟩ := datumD_band6_aa_window hcast.symm rfl hN3 hN26 hnK hlev hYlow
        hYcap hYaff hYaff₂ hYaff₃ hYaff₄ hYaff₅ hYaff₆ hw
      refine admitsPartition₄_of_floor_avg (n := n) (κ := (m : ℝ) + m' - 4)
        (W := (1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 4 * (41 / 2500))
        hTd (by rwa [hT₃s]) (by rwa [hT₄s]) (hEdisj _ _ subset_union_left)
        (hEdisj _ _ subset_union_right) (by norm_num) (fun i _ ↦ hδy i) ?_ ?_ hc₂
        (by rwa [hT₃s, hT₄s]) ?_
        (Or.inr (by rw [hT₃s, hT₄s]; linarith [hδy k₁, hδy k₂, hδy i₁, hδy i₂]))
      · rw [hEcard, hEc]; push_cast; linarith
      · rw [lt_sub_iff_add_lt]; exact_mod_cast hroom
      · linarith [hδy k₁, hδy k₂, hδy i₁, hδy i₂]
    -- **A-B1** or **A-B2.** No second pair fits in block three.
    have hnop3 : ∀ a b : Fin (m + m'), a ≠ b → a ∉ ({i₁, i₂} : Finset (Fin (m + m'))) →
        b ∉ ({i₁, i₂} : Finset (Fin (m + m'))) → 4 * w + 41 / 2500 - 1 / 10 ^ 10 < y a + y b :=
      fun a b hab ha hb ↦ not_le.1 fun h ↦ hpair3 ⟨a, b, hab, ha, hb, h⟩
    by_cases hsing3 : ∃ a : Fin (m + m'), a ∉ ({i₁, i₂} : Finset (Fin (m + m'))) ∧
        y a ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10
    · -- **A-B1.** A third coordinate `k` goes into block three, and every coordinate outside
      -- `{i₁, i₂, k}` exceeds `c₃ - y k`.
      obtain ⟨k, hkE, hk⟩ := hsing3
      have hTd : Disjoint ({k} : Finset (Fin (m + m'))) {i₁, i₂} :=
        disjoint_singleton_left.2 hkE
      have hEc : ({k} ∪ {i₁, i₂} : Finset (Fin (m + m'))).card = 3 := by
        rw [card_union_of_disjoint hTd, card_singleton, hT₄c]
      have hE := hEsum ({k} ∪ {i₁, i₂})
      rw [sum_union hTd, sum_singleton, hT₄s] at hE
      have hflo : ∀ i ∈ univ \ ({k} ∪ {i₁, i₂} : Finset (Fin (m + m'))),
          4 * w + 41 / 2500 - 1 / 10 ^ 10 - y k ≤ y i := by
        intro i hi
        have hi' := mem_sdiff.1 hi
        linarith [hnop3 k i (fun h ↦ hi'.2 (mem_union_left _ (mem_singleton.2 h.symm))) hkE
          fun h ↦ hi'.2 (mem_union_right _ h)]
      obtain ⟨f, hf1, hf2, hfT⟩ : ∃ f : ℝ, 41 / 2500 ≤ f ∧
          4 * w + 41 / 2500 - 1 / 10 ^ 10 - y k ≤ f ∧
          ∀ i ∈ univ \ ({k} ∪ {i₁, i₂} : Finset (Fin (m + m'))), f ≤ y i :=
        ⟨_, le_max_left _ _, le_max_right _ _, fun i hi ↦ max_le (hδy i) (hflo i hi)⟩
      have hfar : ((m : ℝ) + (m' : ℝ) - 3) * (4 * w + 41 / 2500 - 1 / 10 ^ 10 - y k)
          + 3 * (41 / 2500) ≤ ∑ i, y i := by
        have h := hTflo _ _ hflo
        rw [hEc] at h
        push_cast at h
        linarith [hδy k, hδy i₁, hδy i₂]
      by_cases hDr : (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10)
          - y k - (y i₁ + y i₂) ≤ 0
      · exact admitsPartition₄_of_parked_le hTd hc₂ (by rw [sum_singleton, hT₄s]; linarith)
          (by rwa [sum_singleton]) (by rwa [hT₄s])
      push Not at hDr
      obtain ⟨n, hnlo, hnhi⟩ := exists_nat_mul_le_lt (d := f) (by linarith) hDr.le
      have hlev : (n : ℝ) * f
          ≤ (∑ i, y i) - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
            - 2 * (41 / 2500) - y k := by linarith [hδy i₁, hδy i₂]
      have hnK : n ≤ 4 := by
        by_contra hcon
        have h5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 5 ≤ n)
        nlinarith [hδy k]
      obtain ⟨hroom, hineq⟩ := datumD_band6_ab1_window hcast.symm rfl hN3 hN26 hnK
        (hδy k) hf1 hf2 hlev hfar hYlow hYcap hYaff hYaff₂ hYaff₃ hYaff₄ hYaff₅ hYaff₆ hw
      refine admitsPartition₄_of_floor_avg (n := n) (κ := (m : ℝ) + m' - 3)
        (W := (1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
          + 2 * (41 / 2500) + y k)
        hTd (by rwa [sum_singleton]) (by rwa [hT₄s]) (hEdisj _ _ subset_union_left)
        (hEdisj _ _ subset_union_right) (by linarith) hfT ?_ ?_ hc₂
        (by rwa [sum_singleton, hT₄s]) ?_
        (Or.inr (by rw [sum_singleton, hT₄s]; linarith [hδy i₁, hδy i₂]))
      · rw [hEcard, hEc]; push_cast; linarith
      · rw [lt_sub_iff_add_lt]; exact_mod_cast hroom
      · linarith [hδy k, hδy i₁, hδy i₂]
    -- **A-B2.** Every coordinate outside the parked pair exceeds `c₃`.
    have hflo : ∀ i ∈ univ \ ({i₁, i₂} : Finset (Fin (m + m'))),
        4 * w + 41 / 2500 - 1 / 10 ^ 10 ≤ y i :=
      fun i hi ↦ not_lt.1 fun h ↦ hsing3 ⟨i, (mem_sdiff.1 hi).2, h.le⟩
    have hE := hEsum {i₁, i₂}
    rw [hT₄s] at hE
    have hfar : ((m : ℝ) + (m' : ℝ) - 2) * (4 * w + 41 / 2500 - 1 / 10 ^ 10)
        + 2 * (41 / 2500) ≤ ∑ i, y i := by
      have h := hTflo _ _ hflo
      rw [hT₄c] at h
      push_cast at h
      linarith [hδy i₁, hδy i₂]
    by_cases hDr : (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10)
        - 0 - (y i₁ + y i₂) ≤ 0
    · exact admitsPartition₄_of_parked_le (disjoint_empty_left {i₁, i₂}) hc₂
        (by rw [sum_empty, hT₄s]; linarith) (by rwa [sum_empty]) (by rwa [hT₄s])
    push Not at hDr
    obtain ⟨n, hnlo, hnhi⟩ :=
      exists_nat_mul_le_lt (d := (4 * w + 41 / 2500 - 1 / 10 ^ 10 : ℝ)) (by linarith) hDr.le
    have hlev : (n : ℝ) * (4 * w + 41 / 2500 - 1 / 10 ^ 10)
        ≤ (∑ i, y i) - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
          - 2 * (41 / 2500) := by linarith [hδy i₁, hδy i₂]
    have hnK : n ≤ 2 := by
      by_contra hcon
      have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 3 ≤ n)
      nlinarith
    obtain ⟨hroom, hineq⟩ := datumD_band6_ab2_window hcast.symm rfl hN3 hN26 hnK hlev hfar
      hYlow hYcap hYaff hYaff₂ hYaff₃ hYaff₄ hYaff₅ hYaff₆ hw
    refine admitsPartition₄_of_floor_avg (n := n) (κ := (m : ℝ) + m' - 2)
      (W := (1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 2 * (41 / 2500))
      (disjoint_empty_left {i₁, i₂}) (by rwa [sum_empty]) (by rwa [hT₄s]) (disjoint_empty_right _)
      (hEdisj _ _ subset_rfl) (by linarith) hflo ?_ ?_ hc₂
      (by rw [sum_empty, hT₄s]; linarith) ?_
      (Or.inr (by rw [sum_empty, hT₄s]; linarith [hδy i₁, hδy i₂]))
    · rw [hEcard, hT₄c]; push_cast; linarith
    · rw [lt_sub_iff_add_lt]; exact_mod_cast hroom
    · linarith [hδy i₁, hδy i₂]
  -- **Case B.** No pair fits in block four, so at most one coordinate is at most `4ω₀` — two
  -- such would sum to at most `8ω₀ = c₄`. That item count is the floor the rest of the case runs
  -- on.
  have hnop : ∀ a b : Fin (m + m'), a ≠ b → 8 * w < y a + y b :=
    fun a b hab ↦ not_le.1 fun h ↦ hpair4 ⟨a, b, hab, h⟩
  have hXc : (univ.filter (fun i : Fin (m + m') ↦ y i ≤ 4 * w)).card ≤ 1 :=
    card_le_one.2 fun a ha b hb ↦ by_contra fun hab ↦ by
      linarith [hnop a b hab, (mem_filter.1 ha).2, (mem_filter.1 hb).2]
  have hXcR : (((univ.filter (fun i : Fin (m + m') ↦ y i ≤ 4 * w)).card : ℕ) : ℝ) ≤ 1 := by
    exact_mod_cast hXc
  have hXfl : ∀ i ∈ univ \ (univ.filter (fun i : Fin (m + m') ↦ y i ≤ 4 * w)), 4 * w ≤ y i :=
    fun i hi ↦ not_lt.1 fun h ↦ (mem_sdiff.1 hi).2 (mem_filter.2 ⟨mem_univ i, h.le⟩)
  have hfarX : ((m : ℝ) + (m' : ℝ) - 1) * (4 * w) + 41 / 2500 ≤ ∑ i, y i := by
    have h := hTflo _ _ hXfl
    have h2 := hEsum (univ.filter (fun i : Fin (m + m') ↦ y i ≤ 4 * w))
    have h3 := card_nsmul_le_sum (univ.filter (fun i : Fin (m + m') ↦ y i ≤ 4 * w)) y
      (41 / 2500 : ℝ) fun i _ ↦ hδy i
    rw [nsmul_eq_mul] at h3
    nlinarith [hXcR]
  by_cases hsing4 : ∃ a : Fin (m + m'), y a ≤ 8 * w
  · obtain ⟨i₁, hi₁⟩ := hsing4
    by_cases hsing3 : ∃ a : Fin (m + m'), a ≠ i₁ ∧ y a ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10
    · -- **B-1a.** `i₁` goes into block four and `i₂` into block three; because no pair fits in
      -- block four together, the parked mass exceeds `c₄` outright.
      obtain ⟨i₂, hne21, hi₂⟩ := hsing3
      have hTd : Disjoint ({i₂} : Finset (Fin (m + m'))) {i₁} := disjoint_singleton.2 hne21
      have hP : 8 * w < y i₁ + y i₂ := hnop i₁ i₂ (Ne.symm hne21)
      obtain ⟨E, hEdef⟩ : ∃ E : Finset (Fin (m + m')), E = ({i₂} ∪ {i₁})
        ∪ univ.filter (fun i : Fin (m + m') ↦ y i ≤ 4 * w) := ⟨_, rfl⟩
      have hEcle : ((E.card : ℕ) : ℝ) ≤ 3 := by
        have : E.card ≤ 3 := by
          rw [hEdef]
          refine (card_union_le _ _).trans ?_
          rw [card_union_of_disjoint hTd, card_singleton, card_singleton]
          omega
        exact_mod_cast this
      have hsub₂ : ({i₂} ∪ {i₁} : Finset (Fin (m + m'))) ⊆ E := hEdef ▸ subset_union_left
      have hEmass : y i₁ + y i₂ ≤ ∑ i ∈ E, y i := by
        have := sum_le_sum_of_subset_of_nonneg hsub₂ fun i _ _ ↦
          (by norm_num : (0 : ℝ) ≤ 41 / 2500).trans (hδy i)
        rw [sum_union hTd, sum_singleton, sum_singleton] at this
        linarith
      have hfE : ∀ i ∈ univ \ E, 4 * w ≤ y i := fun i hi ↦ hXfl i (mem_sdiff.2
        ⟨mem_univ i, fun hc ↦ (mem_sdiff.1 hi).2 (hEdef ▸ mem_union_right _ hc)⟩)
      by_cases hDr : (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10)
          - y i₂ - y i₁ ≤ 0
      · exact admitsPartition₄_of_parked_le hTd hc₂
          (by rw [sum_singleton, sum_singleton]; linarith) (by rwa [sum_singleton])
          (by rwa [sum_singleton])
      push Not at hDr
      obtain ⟨n, hnlo, hnhi⟩ := exists_nat_mul_le_lt (d := (4 * w : ℝ)) (by linarith) hDr.le
      have hlev : (n : ℝ) * (4 * w)
          ≤ (∑ i, y i) - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) - 8 * w := by
        linarith
      have hnK : n ≤ 3 := by
        by_contra hcon
        have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 4 ≤ n)
        nlinarith
      obtain ⟨hroom, hineq⟩ := datumD_band6_b1a_window hcast.symm rfl hN3 hN26 hnK hlev hfarX
        hYlow hYcap hYaff hYaff₂ hYaff₃ hYaff₄ hYaff₅ hYaff₆ hw0 hw
      refine admitsPartition₄_of_floor_avg (n := n) (κ := (m : ℝ) + m' - 3)
        (W := (1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 8 * w)
        hTd (by rwa [sum_singleton]) (by rwa [sum_singleton])
        (hEdisj _ _ (subset_union_left.trans hsub₂)) (hEdisj _ _ (subset_union_right.trans hsub₂))
        (by linarith) hfE ?_ ?_ hc₂ (by rwa [sum_singleton, sum_singleton]) ?_
        (Or.inr (by rw [sum_singleton, sum_singleton]; linarith))
      · rw [hEcard]; linarith
      · rw [lt_sub_iff_add_lt]; exact_mod_cast hroom
      · linarith [hEsum E, hδy i₁, hδy i₂]
    -- **B-1b.** `i₁` goes into block four and every other coordinate exceeds `c₃`.
    have hc₃i : ∀ a : Fin (m + m'), a ≠ i₁ → 4 * w + 41 / 2500 - 1 / 10 ^ 10 ≤ y a :=
      fun a ha ↦ not_lt.1 fun h ↦ hsing3 ⟨a, ha, h.le⟩
    obtain ⟨hsd, hsd'⟩ := side_floor_le_cap_except hy' hδy (by linarith) hc₃i
    have hm5 : m ≤ 5 := side_le_five_except hw0 hsd
    have hm5' : m' ≤ 5 := side_le_five_except hw0 hsd'
    have hflo : ∀ i ∈ univ \ ({i₁} : Finset (Fin (m + m'))),
        4 * w + 41 / 2500 - 1 / 10 ^ 10 ≤ y i :=
      fun i hi ↦ hc₃i i fun h ↦ (mem_sdiff.1 hi).2 (mem_singleton.2 h)
    have hE := hEsum {i₁}
    rw [sum_singleton] at hE
    have hfar : (((m : ℝ) + (m' : ℝ)) - 1) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 41 / 2500
        ≤ ∑ i, y i := by
      have h := hTflo _ _ hflo
      rw [card_singleton] at h
      push_cast at h
      linarith [hδy i₁]
    by_cases hDr : (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10)
        - 0 - y i₁ ≤ 0
    · exact admitsPartition₄_of_parked_le (disjoint_empty_left {i₁}) hc₂
        (by rw [sum_empty, sum_singleton]; linarith) (by rwa [sum_empty])
        (by rwa [sum_singleton])
    push Not at hDr
    obtain ⟨n, hnlo, hnhi⟩ :=
      exists_nat_mul_le_lt (d := (4 * w + 41 / 2500 - 1 / 10 ^ 10 : ℝ)) (by linarith) hDr.le
    have hlev : (n : ℝ) * (4 * w + 41 / 2500 - 1 / 10 ^ 10)
        ≤ (∑ i, y i) - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) - 41 / 2500 := by
      linarith [hδy i₁]
    have hnK : n ≤ 1 := by
      by_contra hcon
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
      nlinarith [gap212Cap_le_five hm5, gap212Cap_le_five hm5', total_le hy']
    obtain ⟨hroom, hineq⟩ := datumD_band6_b1b_window rfl hm5 hm5' hnK hlev hfar hYlow
      (total_le hy') hw
    refine admitsPartition₄_of_floor_avg (n := n) (κ := (m : ℝ) + m' - 1)
      (W := (1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 41 / 2500)
      (disjoint_empty_left {i₁}) (by rwa [sum_empty]) (by rwa [sum_singleton])
      (disjoint_empty_right _) (hEdisj _ _ subset_rfl) (by linarith) hflo ?_ ?_ hc₂
      (by rw [sum_empty, sum_singleton]; linarith) ?_
      (Or.inr (by rw [sum_empty, sum_singleton]; linarith [hδy i₁]))
    · rw [hEcard, card_singleton]; push_cast; linarith
    · rw [lt_sub_iff_add_lt]; exact_mod_cast hroom
    · linarith [hδy i₁]
  -- **B-2.** Every coordinate exceeds `c₄`; both small blocks stay empty and the reading is
  -- taken on a side.
  push Not at hsing4
  have hfy : ∀ i, (8 * w : ℝ) ≤ y i := fun i ↦ (hsing4 i).le
  have hYf : ((m : ℝ) + (m' : ℝ)) * (8 * w) ≤ ∑ i, y i := by
    have h := card_nsmul_le_sum (univ : Finset (Fin (m + m'))) y (8 * w : ℝ) fun i _ ↦ hfy i
    rwa [card_univ, Fintype.card_fin, nsmul_eq_mul, hcast] at h
  obtain ⟨hside, hside'⟩ := side_floor_le_cap hy' hfy
  have hm4 : m ≤ 4 := side_le_four hw0 hside
  have hm4' : m' ≤ 4 := side_le_four hw0 hside'
  obtain ⟨n, hnlo, hnhi⟩ :=
    exists_nat_mul_le_lt (d := (8 * w : ℝ)) (by linarith) (by linarith : (0:ℝ) ≤
      (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10))
  have hlev : (n : ℝ) * (8 * w)
      ≤ (∑ i, y i) - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) := by linarith
  have hnK : n ≤ 1 := by
    by_contra hcon
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
    nlinarith [gap212Cap_le_four hm4, gap212Cap_le_four hm4', total_le hy']
  have hS1c : (((univ.filter (fun i : Fin (m + m') ↦ (i : ℕ) < m)).card : ℕ) : ℝ)
      = (m : ℝ) := by rw [Packing.card_side_left]
  have hS2c : (((univ.filter (fun i : Fin (m + m') ↦ ¬ ((i : ℕ) < m))).card : ℕ) : ℝ)
      = (m' : ℝ) := by rw [Packing.card_side_right]
  have hnhi' : (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10)
      - (∑ i ∈ (∅ : Finset (Fin (m + m'))), y i)
      - (∑ i ∈ (∅ : Finset (Fin (m + m'))), y i) < ((n : ℝ) + 1) * (8 * w) := by
    rw [sum_empty]; linarith
  have h₃ : ∑ i ∈ (∅ : Finset (Fin (m + m'))), y i ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10 := by
    rwa [sum_empty]
  have h₄ : ∑ i ∈ (∅ : Finset (Fin (m + m'))), y i ≤ 8 * w := by rwa [sum_empty]
  rcases datumD_band6_b2_window rfl hm4 hm4' hnK hside hside' hYf (total_le hy') hlev hw with
    ⟨hn0, hroom, hineq⟩ | ⟨hroom, hineq⟩ | ⟨hn0, hroom, hineq⟩ | ⟨hroom, hineq⟩
  · -- side one, the `c₂` reading
    exact admitsPartition₄_of_floor_avg (T := univ.filter (fun i : Fin (m + m') ↦ (i : ℕ) < m))
      (κ := m) (disjoint_empty_left _) h₃ h₄ (disjoint_empty_right _) (disjoint_empty_right _)
      (by linarith) (fun i _ ↦ hfy i) hS1c.ge (by exact_mod_cast hroom) hc₂ hnhi'
      (by linarith [hy'.2.1]) (Or.inl ⟨hn0, hc₂m⟩)
  · -- side one, the reserve reading
    exact admitsPartition₄_of_floor_avg (T := univ.filter (fun i : Fin (m + m') ↦ (i : ℕ) < m))
      (κ := m) (W := 1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
      (disjoint_empty_left _) h₃ h₄ (disjoint_empty_right _) (disjoint_empty_right _)
      (by linarith) (fun i _ ↦ hfy i) hS1c.ge (by exact_mod_cast hroom) hc₂ hnhi'
      (by linarith [hy'.2.1]) (Or.inr (by rw [sum_empty]; linarith))
  · -- side two, the `c₂` reading
    exact admitsPartition₄_of_floor_avg
      (T := univ.filter (fun i : Fin (m + m') ↦ ¬ ((i : ℕ) < m)))
      (κ := m') (disjoint_empty_left _) h₃ h₄ (disjoint_empty_right _) (disjoint_empty_right _)
      (by linarith) (fun i _ ↦ hfy i) hS2c.ge (by exact_mod_cast hroom) hc₂ hnhi'
      (by linarith [hy'.2.2]) (Or.inl ⟨hn0, hc₂m⟩)
  · -- side two, the reserve reading
    exact admitsPartition₄_of_floor_avg
      (T := univ.filter (fun i : Fin (m + m') ↦ ¬ ((i : ℕ) < m)))
      (κ := m') (W := 1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
      (disjoint_empty_left _) h₃ h₄ (disjoint_empty_right _) (disjoint_empty_right _)
      (by linarith) (fun i _ ↦ hfy i) hS2c.ge (by exact_mod_cast hroom) hc₂ hnhi'
      (by linarith [hy'.2.2]) (Or.inr (by rw [sum_empty]; linarith))
end Gap212
