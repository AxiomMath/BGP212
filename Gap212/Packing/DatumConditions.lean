/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Defs
public import Gap212.Packing.ConditionD
public import Gap212.Packing.DatumFacts
public meta import Gap212.Attr

/-!
# Conditions A, A′, B and C at the chosen datum

The four Type I and Type II packing conditions of Proposition 3, at `Gap212.gap212Params`: the
datum with `δ = 41/2500`, one band, level `ω(1,1) = 7/1000` by `Gap212.omegaMax_gap212Params`, cap
row `Gap212.gap212Cap`, and `ξ₁ = 19/50`, `ϵ = 10⁻¹⁰` from the challenge file's
`HarmanReduction gap212Params (19/50) (2/5) (2/5)`.

## The pooled mass, and which conditions it settles

`Gap212.total_le_datum` bounds the pooled rough mass of a tuple of `Ξ` by `1081/2500 = 0.4324`, the
sum of two top rungs. Against that:

* **A′** has first capacity `1/2 - 2ω - 2ϵ = 0.4859999998` — the whole tuple fits in the first bin.
* **B** has first capacity `2/5 + (24/5)ω + (7/5)δ - 2ϵ = 0.4565599998` — likewise.
* **A** has first capacity `ξ₁ - 2ϵ = 0.3799999998`, short by `0.0524000002`.
* **C** has first capacity `1/3 + 8ω + (7/3)δ - 4ϵ = 0.4275999996`, short by `0.0048000004`.

So A′ and B are the trivial partition; A and C need a genuine split, and the two need *different*
splits, because their second capacities differ by a factor of almost five: A's is
`1/6 - 4ω - 2ϵ = 0.13866666646…` and C's is `1/10 - (34/5)ω - (7/5)δ - 4ϵ = 0.0294399996`.

## The split for A: greedy inside the longer side

Let `k` be the larger of the two rough counts, so that both caps are at most `B_{1,k}` by
monotonicity of the row and the pooled mass is at most `2B_{1,k}`. Inside the side carrying `k`
coordinates every coordinate is at most `M = B_{1,k} - (k-1)δ`, the rest of that side taking at
least `δ` apiece. Filling the second bin from that side with a subset of minimal cardinality
reaching the deficit `T - c₁` overshoots by less than `M`, so it suffices that

`(2B_{1,k} - c₁) + (B_{1,k} - (k-1)δ) ≤ c₂`, i.e. `3B_{1,k} - (k-1)δ ≤ c₁ + c₂`.

That is `Gap212.cap_greedy_le`: the left side is maximal at `k = 7`, where it is
`639/1250 = 0.5112`, against `c₁ + c₂ = 0.5186666662…`. **One inequality covers every cell**, the
tightest being `(m,m') = (7,7)` with margin `55999997/7500000000 ≈ 0.00746667`.

## The split for C: one coordinate, the smallest of the longer side

C's second capacity is too small for the greedy overshoot — at `k = 10` the bound `M = 0.0686`
already exceeds `0.02944` on its own — so the split is sharper: since the deficit is at most
`0.0048000004 < δ`, a **single** coordinate reaches it, and the smallest coordinate of a side of
`k` coordinates capped by `B_{1,k}` is at most `B_{1,k}/k`. So the cells divide by `k`:

* `k ≤ 9`: `2B_{1,k} ≤ 2·1063/5000 = 0.4252 ≤ c₁`, the trivial partition, margin `0.0023999996`.
* `k ≥ 10`: `B_{1,k} = 1081/5000` and `B_{1,k}/k ≤ 1081/50000 = 0.021620 ≤ c₂`, margin
  `19549999/2500000000 ≈ 0.0078200`.

Both branches are uniform in `k`, so again there is no cell enumeration: every pair `(m, m')` is
covered by these two inequalities, and nothing here needs the check set to be empty above `13`
rough factors — the bounds hold at every `k`.

## Main results

* `Gap212.Packing.admitsPartition₂_of_subset`: a subset carrying the deficit is a partition.
* `Gap212.Packing.admitsPartition₂_of_group`, `admitsPartition₂_of_group_min`: the greedy and the
  single-coordinate discharges, from one capped group of coordinates.
* `Gap212.gap212Cap_mono`, `gap212Cap_le_of_le_nine`, `cap_greedy_le`: the cap row's arithmetic.
* `Gap212.exists_max_side`: the longer side of a pooled tuple, with its three mass bounds.
* `Gap212.conditionA_at_datum`, `conditionA_high_at_datum`, `conditionB_at_datum`,
  `conditionC_at_datum`: the four conditions at `p_⋆`, for every pair of rough counts.
-/

@[expose] public section

namespace Gap212.Packing

open Finset

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {ℓ : ℕ}

/-! ## One subset is already a partition

Both discharges below produce a single set `J` whose mass sits between the deficit `T - c₁` and the
second capacity. Its complement is then the first bin, and the two bounds are exactly the two the
partition predicate asks for. -/

/-- **A subset carrying the deficit gives the two-block partition.** With `T` the total mass, a set
`J` with `T - c₁ ≤ ∑_J y ≤ c₂` serves: the complement carries `T - ∑_J y ≤ c₁`.

This is the only step at which the partition predicate is opened; everything else is about finding
`J`. -/
theorem admitsPartition₂_of_subset {y : Fin ℓ → 𝕜} {c₁ c₂ : 𝕜} (J : Finset (Fin ℓ))
    (hlo : (∑ i, y i) - c₁ ≤ ∑ i ∈ J, y i) (hhi : ∑ i ∈ J, y i ≤ c₂) :
    AdmitsPartition₂ y c₁ c₂ := by
  refine ⟨univ \ J, ?_, ?_⟩
  · have h : (∑ i ∈ univ \ J, y i) + ∑ i ∈ J, y i = ∑ i, y i :=
      Finset.sum_sdiff (Finset.subset_univ J)
    linarith
  · rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ J)]
    exact hhi

omit [IsStrictOrderedRing 𝕜] in
/-- A two-block partition serves as a three-block one when the third capacity is nonnegative: put
the complement's mass in block two and leave block three empty. The three-block analogue of
`Gap212.Packing.admitsPartition₄_of_partition₂`. -/
theorem admitsPartition₃_of_partition₂ {y : Fin ℓ → 𝕜} {b₁ b₂ b₃ : 𝕜}
    (h : AdmitsPartition₂ y b₁ b₂) (hb₃ : 0 ≤ b₃) : AdmitsPartition₃ y b₁ b₂ b₃ := by
  obtain ⟨I, hI₁, hI₂⟩ := h
  refine ⟨I, univ \ I, Finset.disjoint_sdiff, hI₁, hI₂, ?_⟩
  rw [Finset.union_sdiff_of_subset (subset_univ I), sdiff_self]
  simpa using hb₃

/-! ## What a capped group of coordinates forces

A group of `k + 1` coordinates whose mass is capped by `B`, each coordinate being at least `d`,
constrains its coordinates from both ends: none exceeds `B - k d`, and the smallest is at most
`B / (k + 1)`. The two conditions that need a genuine split use one bound apiece. -/

/-- **No coordinate of a capped group exceeds `B - k d`.** The other `k` coordinates of the group
take at least `d` apiece, so they leave at most `B - k d` of the cap for any single one. -/
theorem le_sub_of_mem_group {S : Finset (Fin ℓ)} {k : ℕ} {y : Fin ℓ → 𝕜} {B d : 𝕜} {i : Fin ℓ}
    (hcard : S.card = k + 1) (hlb : ∀ j, d ≤ y j) (hS : ∑ j ∈ S, y j ≤ B) (hi : i ∈ S) :
    y i ≤ B - (k : 𝕜) * d := by
  have hsplit : ∑ j ∈ S, y j = y i + ∑ j ∈ S.erase i, y j := (Finset.add_sum_erase _ _ hi).symm
  have hcard' : (S.erase i).card = k := by
    rw [Finset.card_erase_of_mem hi, hcard, Nat.add_sub_cancel]
  have hlow : (k : 𝕜) * d ≤ ∑ j ∈ S.erase i, y j := by
    have h := Finset.card_nsmul_le_sum (S.erase i) y d fun j _ ↦ hlb j
    rwa [hcard', nsmul_eq_mul] at h
  linarith

/-- **The greedy discharge from one group.** A subset of `S` of minimal cardinality reaching the
deficit `T - c₁` overshoots it by less than the largest coordinate of `S`, which is `B - k d` by
`Gap212.Packing.le_sub_of_mem_group`. The deficit is reachable inside `S` because the complement of
`S` carries at most `c₁`.

`hnum` is the whole numerical content: the deficit plus the overshoot must fit in `c₂`. -/
theorem admitsPartition₂_of_group {S : Finset (Fin ℓ)} {k : ℕ} {y : Fin ℓ → 𝕜} {B d c₁ c₂ : 𝕜}
    (hcard : S.card = k + 1) (hlb : ∀ i, d ≤ y i) (hd : 0 ≤ d) (hS : ∑ i ∈ S, y i ≤ B)
    (hrest : ∑ i ∈ univ \ S, y i ≤ c₁) (hD : 0 ≤ (∑ i, y i) - c₁)
    (hnum : (∑ i, y i) - c₁ + (B - (k : 𝕜) * d) ≤ c₂) :
    AdmitsPartition₂ y c₁ c₂ := by
  have hSne : S.Nonempty := by rw [← Finset.card_pos, hcard]; omega
  obtain ⟨i₀, hi₀⟩ := hSne
  have hM : ∀ i ∈ S, y i ≤ B - (k : 𝕜) * d := fun i hi ↦ le_sub_of_mem_group hcard hlb hS hi
  have hM0 : 0 ≤ B - (k : 𝕜) * d := (hd.trans (hlb i₀)).trans (hM i₀ hi₀)
  have hsplit : (∑ i ∈ univ \ S, y i) + ∑ i ∈ S, y i = ∑ i, y i :=
    Finset.sum_sdiff (Finset.subset_univ S)
  obtain ⟨J, -, hJlo, hJhi⟩ :=
    exists_subset_sum_mem_Icc_of_subset S y (B - (k : 𝕜) * d) ((∑ i, y i) - c₁) hM hM0 hD
      (by linarith)
  exact admitsPartition₂_of_subset J hJlo (hJhi.trans hnum)

/-- **The single-coordinate discharge from one group.** The smallest coordinate of a group of
`k + 1` coordinates capped by `B` is at most `B / (k + 1)`, so `B ≤ (k + 1) c₂` produces one
coordinate fitting in the second bin; and it reaches the deficit as soon as that is at most `d`.

Used where the greedy overshoot is too coarse: the bin is filled by one coordinate chosen for being
small, not by however many the minimal-cardinality subset happens to take. -/
theorem admitsPartition₂_of_group_min {S : Finset (Fin ℓ)} {k : ℕ} {y : Fin ℓ → 𝕜} {B d c₁ c₂ : 𝕜}
    (hcard : S.card = k + 1) (hlb : ∀ i, d ≤ y i) (hS : ∑ i ∈ S, y i ≤ B)
    (hnum : B ≤ ((k : 𝕜) + 1) * c₂) (hD : (∑ i, y i) - c₁ ≤ d) :
    AdmitsPartition₂ y c₁ c₂ := by
  have hSne : S.Nonempty := by rw [← Finset.card_pos, hcard]; omega
  have hconst : ∑ _i ∈ S, c₂ = ((k : 𝕜) + 1) * c₂ := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring
  have hsum : ∑ i ∈ S, y i ≤ ∑ _i ∈ S, c₂ := by rw [hconst]; exact hS.trans hnum
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hSne hsum
  refine admitsPartition₂_of_subset {i} ?_ ?_
  · rw [Finset.sum_singleton]; exact hD.trans (hlb i)
  · rwa [Finset.sum_singleton]

end Gap212.Packing

namespace Gap212

open Finset Gap212.Bridges Gap212.Packing

/-! ## The cap row's arithmetic

Three facts about `Gap212.gap212Cap` beyond the bound `1081/5000` of
`Gap212.gap212Cap_le`: it is monotone, it is at most its ninth rung below the tenth, and it obeys
the greedy inequality that discharges Condition A at every cell. -/

/-- **The cap row is monotone.** It rises through its ten rungs and is constant after, and
`B_{1,0} = 0` sits below all of them. -/
theorem gap212Cap_mono : Monotone gap212Cap := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  by_cases h : 10 ≤ n
  · rw [gap212Cap_of_ten_le h, gap212Cap_of_ten_le (show 10 ≤ n + 1 by omega)]
  · have h' : n < 10 := by omega
    interval_cases n <;> norm_num [gap212Cap]

/-- **Below the tenth rung the row is at most `1063/5000`**, its ninth rung. This is what makes the
trivial partition serve Condition C at every cell with at most nine rough factors on each side:
`2 · 1063/5000 = 0.4252` against a first capacity of `0.4275999996`. -/
theorem gap212Cap_le_of_le_nine {m : ℕ} (hm : m ≤ 9) : gap212Cap m ≤ 1063 / 5000 := by
  interval_cases m <;> norm_num [gap212Cap]

/-- **The greedy inequality of the cap row**: `3 B_{1,k+1} - k δ ≤ 639/1250`.

The left side is the pooled mass `2 B_{1,k+1}` plus the largest coordinate `B_{1,k+1} - k δ` a side
of `k + 1` coordinates can hold. It is largest, `639/1250 = 0.5112`, at `k = 6` — seven rough
factors: from one rung to the next it changes by three times the row's step less `δ`, which is
negative from the seventh rung on, and above the tenth rung the row is constant while `k δ` keeps
growing.

`639/1250` is the exact maximum, attained, and it is below Condition A's `c₁ + c₂ = 0.5186666662…`,
which is why Condition A needs no cell enumeration. -/
theorem cap_greedy_le (k : ℕ) : 3 * gap212Cap (k + 1) - (k : ℝ) * (41 / 2500) ≤ 639 / 1250 := by
  by_cases h : 9 ≤ k
  · rw [gap212Cap_of_ten_le (show 10 ≤ k + 1 by omega)]
    have hk : (9 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
    linarith
  · have h' : k < 9 := by omega
    interval_cases k <;> norm_num [gap212Cap]

/-! ## The longer side of a pooled tuple

Both genuine splits run inside one of the two rough sides, and both want the *longer* one: it is
the side whose cap bounds the other's, and the side whose coordinates are most tightly squeezed by
the `δ` floor on the rest of it. -/

/-- **The longer rough side, with its three mass bounds.** A tuple of the check set at `p_⋆` with
at least one rough factor has a side carrying `k + 1` coordinates such that

* that side's mass is at most `B_{1,k+1}`;
* the other side's mass is at most `1081/5000`, the row's maximum;
* the pooled mass is at most `2 B_{1,k+1}`, by monotonicity of the row.

The third bound is the one that needs `k + 1` to be the *larger* count, and it is what lets every
numeric check below be a statement about a single index. -/
theorem exists_max_side {m m' : ℕ} {y : Fin (m + m') → ℝ}
    (hy : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ)) (hne : m + m' ≠ 0) :
    ∃ (S : Finset (Fin (m + m'))) (k : ℕ), S.card = k + 1 ∧
      (∑ i ∈ S, y i ≤ gap212Cap (k + 1)) ∧ (∑ i ∈ univ \ S, y i ≤ 1081 / 5000) ∧
        ∑ i, y i ≤ 2 * gap212Cap (k + 1) := by
  have hsdiff₁ : (univ : Finset (Fin (m + m'))) \ sideOne m m' = sideTwo m m' :=
    (Finset.filter_not _ univ).symm
  have hsdiff₂ : (univ : Finset (Fin (m + m'))) \ sideTwo m m' = sideOne m m' := by
    rw [← hsdiff₁, Finset.sdiff_sdiff_eq_self (subset_univ _)]
  have htot := total_le hy
  rcases le_or_gt m' m with hle | hlt
  · have hm : m - 1 + 1 = m := by omega
    refine ⟨sideOne m m', m - 1, by rw [card_sideOne, hm], ?_, ?_, ?_⟩
    · rw [hm]; exact sum_sideOne_le hy
    · rw [hsdiff₁]; exact (sum_sideTwo_le hy).trans (gap212Cap_le m')
    · rw [hm]; linarith [gap212Cap_mono hle]
  · have hm : m' - 1 + 1 = m' := by omega
    refine ⟨sideTwo m m', m' - 1, by rw [card_sideTwo, hm], ?_, ?_, ?_⟩
    · rw [hm]; exact sum_sideTwo_le hy
    · rw [hsdiff₂]; exact (sum_sideOne_le hy).trans (gap212Cap_le m)
    · rw [hm]; linarith [gap212Cap_mono hlt.le]

/-! ## The four conditions

Each is stated at `Gap212.gap212Params`, over the band pair `(1,1)` — the only one, `n` being `1` —
with the check set written as `Ξ(B_{j,m}, B_{j',m'}, m, m', δ)`, and the
capacities as their definitions write them, in the level `ω(j,j')` of
`Gap212.Bridges.omegaMax`. The datum's `ξ₁ = 19/50` and the fixed slack `ϵ = 10⁻¹⁰` enter as
hypotheses on the two scalars.

No bound on `m` or `m'` is needed. These are usually stated at `m, m' ≤ ⌊1/δ⌋ = 60`, but the
inequalities that discharge them hold at every index of the cap row, so the restriction plays no
part. -/

/-- **Condition A at the datum.** At `p_⋆` every rough profile splits into two blocks of mass at
most `ξ₁ - 2ϵ = 0.3799999998` and `1/6 - 4ω(1,1) - 2ϵ = 0.13866666646…`.

The trivial partition does not serve: the pooled mass reaches `1081/2500 = 0.4324`, short of the
first capacity by `0.0524000002`. So the second bin is filled greedily from the longer rough side,
by a subset of minimal cardinality reaching the deficit; it overshoots by less than that side's
largest possible coordinate, and `Gap212.cap_greedy_le` says the deficit plus that overshoot fits
in the second capacity at every cell. The tightest cell is `(m,m') = (7,7)`, where the greedy bound
is `639/1250 - (ξ₁ - 2ϵ) = 0.1312…` against `0.1386…`, a margin of `55999997/7500000000`. -/
@[gap212 "lem_condition_A_at_datum"]
theorem conditionA_at_datum {ξ₁ ϵ : ℝ} (hξ₁ : ξ₁ = 19 / 50) (hϵ : ϵ = 1 / 10 ^ 10)
    (j j' : Fin gap212Params.n) (m m' : ℕ) :
    Gap212.Defs.ConditionA (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      (ξ₁ - 2 * ϵ) (1 / 6 - 4 * omegaMax gap212Params j j' - 2 * ϵ) := by
  subst hξ₁
  subst hϵ
  intro y hy
  have hy' : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ) := hy
  rw [omegaMax_gap212Params j j']
  by_cases htriv : ∑ i, y i ≤ 19 / 50 - 2 * (1 / 10 ^ 10 : ℝ)
  · exact admitsPartition₂_of_total_le htriv (by norm_num)
  · push Not at htriv
    have hsum_ne : (∑ i, y i) ≠ 0 := by
      intro h
      rw [h] at htriv
      norm_num at htriv
    obtain ⟨i₀, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
    have hne : m + m' ≠ 0 := by have := i₀.isLt; omega
    obtain ⟨S, k, hcard, hS, hrest, htot⟩ := exists_max_side hy' hne
    refine admitsPartition₂_of_group hcard (fun i ↦ (hy'.1 i).1) (by norm_num) hS
      (by linarith) (by linarith) ?_
    linarith [cap_greedy_le k]

/-- **Condition A′ at the datum.** At `p_⋆` the trivial partition serves: the first capacity
`1/2 - 2ω(1,1) - 2ϵ` is `243/500 - 2·10⁻¹⁰ = 0.4859999998`, above the pooled mass
`1081/2500 = 0.4324` with `0.0535999998` to spare, and the second capacity
`1/14 - (68/14)ω(1,1) - 2ϵ = 131/3500 - 2·10⁻¹⁰` is positive.

This is one of the two conditions generous enough to need no genuine split at this datum; compare
`Gap212.conditionA_at_datum`, where the same partition fails. -/
@[gap212 "lem_condition_A_high_at_datum"]
theorem conditionA_high_at_datum {ϵ : ℝ} (hϵ : ϵ = 1 / 10 ^ 10) (j j' : Fin gap212Params.n)
    (m m' : ℕ) :
    Gap212.Defs.ConditionAHigh
      (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      (1 / 2 - 2 * omegaMax gap212Params j j' - 2 * ϵ)
      (1 / 14 - 68 * omegaMax gap212Params j j' / 14 - 2 * ϵ) := by
  subst hϵ
  intro y hy
  have hy' : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ) := hy
  rw [omegaMax_gap212Params j j']
  exact admitsPartition₂_of_total_le ((total_le_datum hy').trans (by norm_num)) (by norm_num)

/-- **Condition B at the datum.** At `p_⋆` the trivial partition serves: the first capacity
`2/5 + (24/5)ω(1,1) + (7/5)δ - 2ϵ` is `5707/12500 - 2·10⁻¹⁰ = 0.4565599998`, above the pooled mass
`5405/12500 = 0.4324` with `0.0241599998` to spare, and the second capacity
`1/14 - (24/7)ω(1,1) - 2ϵ = 83/1750 - 2·10⁻¹⁰` is positive. -/
@[gap212 "lem_condition_B_at_datum"]
theorem conditionB_at_datum {ϵ : ℝ} (hϵ : ϵ = 1 / 10 ^ 10) (j j' : Fin gap212Params.n)
    (m m' : ℕ) :
    Gap212.Defs.ConditionB (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      (2 / 5 + 24 * omegaMax gap212Params j j' / 5 + 7 * gap212Params.δ / 5 - 2 * ϵ)
      (1 / 14 - 24 * omegaMax gap212Params j j' / 7 - 2 * ϵ) := by
  subst hϵ
  intro y hy
  have hy' : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ) := hy
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rw [omegaMax_gap212Params j j', hδ]
  exact admitsPartition₂_of_total_le ((total_le_datum hy').trans (by norm_num)) (by norm_num)

/-- **Condition C at the datum.** At `p_⋆` every rough profile splits into three blocks of mass at
most `1/3 + 8ω(1,1) + (7/3)δ - 4ϵ = 0.4275999996`,
`1/10 - (34/5)ω(1,1) - (7/5)δ - 4ϵ = 0.0294399996` and `2ω(1,1) + δ - 4ϵ = 0.0303999996`.

The trivial partition does not serve: the pooled mass reaches `1081/2500 = 0.4324`, short of the
first capacity by `0.0048000004`. The third block stays empty even so — its capacity is positive,
and two blocks suffice — but the second must take something, and the greedy overshoot of
`Gap212.conditionA_at_datum` is far too coarse for a capacity of `0.0294…`. Instead, one
coordinate does it: the deficit is below `δ = 0.0164`, so any single coordinate reaches it, and the
smallest coordinate of a side of `k` coordinates capped by `B_{1,k}` is at most `B_{1,k}/k`.

Hence two branches in the longer side's length `k`. For `k ≤ 9` the pooled mass is at most
`2 · 1063/5000 = 0.4252` and the trivial partition serves after all, with margin
`5999999/2500000000 ≈ 0.0024`. For `k ≥ 10` the cap is `1081/5000` and
`1081/5000 ≤ k · 0.0294399996`: the smallest coordinate, at most `1081/50000`, fits in the second
block with margin `19549999/2500000000 ≈ 0.0078` at `k = 10`, the tightest cell being
`(m,m') = (10,10)`. -/
@[gap212 "lem_condition_C_at_datum"]
theorem conditionC_at_datum {ϵ : ℝ} (hϵ : ϵ = 1 / 10 ^ 10) (j j' : Fin gap212Params.n)
    (m m' : ℕ) :
    Gap212.Defs.ConditionC (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      (1 / 3 + 8 * omegaMax gap212Params j j' + 7 * gap212Params.δ / 3 - 4 * ϵ)
      (1 / 10 - 34 * omegaMax gap212Params j j' / 5 - 7 * gap212Params.δ / 5 - 4 * ϵ)
      (2 * omegaMax gap212Params j j' + gap212Params.δ - 4 * ϵ) := by
  subst hϵ
  intro y hy
  have hy' : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ) := hy
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rw [omegaMax_gap212Params j j', hδ]
  refine admitsPartition₃_of_partition₂ ?_ (by norm_num)
  by_cases htriv : ∑ i, y i ≤ 1 / 3 + 8 * (7 / 1000 : ℝ) + 7 * (41 / 2500 : ℝ) / 3 - 4 / 10 ^ 10
  · exact admitsPartition₂_of_total_le (by linarith) (by norm_num)
  · push Not at htriv
    have hsum_ne : (∑ i, y i) ≠ 0 := by
      intro h
      rw [h] at htriv
      norm_num at htriv
    obtain ⟨i₀, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
    have hne : m + m' ≠ 0 := by have := i₀.isLt; omega
    obtain ⟨S, k, hcard, hS, -, htot⟩ := exists_max_side hy' hne
    rcases le_or_gt (k + 1) 9 with hk | hk
    · exact absurd (htot.trans (by linarith [gap212Cap_le_of_le_nine hk])) (not_le.mpr htriv)
    · have hcap : gap212Cap (k + 1) = 1081 / 5000 := gap212Cap_of_ten_le (by omega)
      have hk10 : (9 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 9 ≤ k)
      rw [hcap] at hS htot
      refine admitsPartition₂_of_group_min hcard (fun i ↦ (hy'.1 i).1) hS ?_ (by linarith)
      nlinarith

end Gap212
