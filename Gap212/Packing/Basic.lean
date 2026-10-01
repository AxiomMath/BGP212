/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Parameters.PointA
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Real.Basic
public meta import Gap212.Attr

/-!
# The factor-packing conditions, and their discharge at Point A

Proposition 3 of Stadlmann, *Bounded gaps between primes* (arXiv:2608.31126), asks that every
tuple of pooled rough factors admit a partition into two, three or four blocks whose block sums
obey prescribed capacities — one condition per Type of equidistribution estimate, labelled (A),
(B), (C), (D), (E).

This module formalizes the check set `Ξ` (Definition 10) and the partition predicates, and then
discharges conditions **(A), (B), (C) and (E)** at Point A, for every `m` and `m'` and every tuple.

## Why the coefficient field is general

The tuples Proposition 3 quantifies over are `yᵢ = log_x(fᵢ)`, the logarithmic sizes of the rough
divisors — **real** numbers, not rationals. So everything here is stated over an arbitrary linearly
ordered field and applies at `𝕜 = ℝ`, which is where the argument is used.

The *parameters* on the other hand are exactly rational, and are kept that way: they are defined
over `ℚ` in the namespace `Gap212.PointA`, and enter here through `Rat.cast`. So the razor-thin
comparisons (`typeII_condition_b` has margin `1/10000`) are still settled by exact rational
arithmetic, once, and then transported to `𝕜` by casting rather than re-proved approximately.

## Why four of the five conditions are free

A tuple in `Ξ(B_{j,m}, B_{j',m'}, m, m', δ)` splits its coordinates into two groups whose sums are
capped by `B_{j,m}` and `B_{j',m'}`. So its *total* mass is at most `B_{j,m} + B_{j',m'}`, and at
Point A every cap is at most `17/100`, giving a total of at most `17/50`.

Conditions (A), (B), (C) and (E) each have a first capacity exceeding `17/50` and remaining
capacities that are positive. So the partition putting *everything* in the first block works, with
the later blocks empty, as Stadlmann observes for the parameters used there: in each case all
pooled rough mass fits in the first prescribed bin.

Condition (D), the Type IIc condition, is genuinely different: its fourth capacity is `8ω₀` with
`ω₀` allowed to reach `0`, so the fourth block must be empty *and* the first three capacities must
absorb everything. See `Gap212.Packing.TypeIIc`.

## Main definitions

* `Gap212.Packing.Xi`: the check set `Ξ(B₁, B₂, m₁, m₂, δ)` of Definition 10.
* `Gap212.Packing.AdmitsPartition₂`, `₃`, `₄`: existence of a block decomposition meeting given
  capacities.
* `Gap212.Packing.Bcap`: Point A's cap `B_{1,m}`, namely `31/200` for `m ≤ 2` and `17/100` beyond.

## Main results

* `Gap212.Packing.total_le`: a tuple in `Ξ` has total mass at most `B₁ + B₂`.
* `Gap212.Packing.total_le_pointA`: at Point A that total is at most `17/50`.
* `Gap212.Packing.conditionA`, `conditionB`, `conditionC`, `conditionE`: conditions (A), (B), (C),
  (E) of Proposition 3 hold at Point A for every `m`, `m'` and every tuple of `Ξ`.
-/

@[expose] public section

namespace Gap212.Packing

open Finset

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {ℓ m₁ m₂ : ℕ}

/-! ## The check set `Ξ` -/

/-- **Definition 10.** `Ξ(B₁, B₂, m₁, m₂, δ)` is the set of tuples `(y₁, …, y_{m₁+m₂}) ∈ [δ,1]`
whose first `m₁` coordinates sum to at most `B₁` and whose last `m₂` sum to at most `B₂`.

The two groups are cut by the numeric value of the index, so that the complement of the first
group is literally the second and the two sums add to the total. -/
@[gap212 "def_xi_region"]
def Xi (B₁ B₂ : 𝕜) (m₁ m₂ : ℕ) (δ : 𝕜) : Set (Fin (m₁ + m₂) → 𝕜) :=
  {y | (∀ i, y i ∈ Set.Icc δ 1) ∧
    (∑ i ∈ univ.filter (fun i : Fin (m₁ + m₂) ↦ (i : ℕ) < m₁), y i) ≤ B₁ ∧
    (∑ i ∈ univ.filter (fun i : Fin (m₁ + m₂) ↦ ¬ ((i : ℕ) < m₁)), y i) ≤ B₂}

omit [IsStrictOrderedRing 𝕜] in
/-- Every coordinate of a tuple in `Ξ` is nonnegative, provided `δ` is. -/
theorem nonneg_of_mem {B₁ B₂ δ : 𝕜} (hδ : 0 ≤ δ) {y : Fin (m₁ + m₂) → 𝕜}
    (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) (i : Fin (m₁ + m₂)) : 0 ≤ y i :=
  hδ.trans (hy.1 i).1

/-- **The total mass bound.** The two capped groups partition the index set, so a tuple in `Ξ` has
total mass at most `B₁ + B₂`. This is the only property of `Ξ` that conditions (A), (B), (C) and
(E) need. -/
@[gap212 "lem_xi_total_mass"]
theorem total_le {B₁ B₂ δ : 𝕜} {y : Fin (m₁ + m₂) → 𝕜} (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) :
    ∑ i, y i ≤ B₁ + B₂ := by
  obtain ⟨-, h₁, h₂⟩ := hy
  calc ∑ i, y i
      = (∑ i ∈ univ.filter (fun i : Fin (m₁ + m₂) ↦ (i : ℕ) < m₁), y i) +
          ∑ i ∈ univ.filter (fun i : Fin (m₁ + m₂) ↦ ¬ ((i : ℕ) < m₁)), y i :=
        (sum_filter_add_sum_filter_not univ _ y).symm
    _ ≤ B₁ + B₂ := add_le_add h₁ h₂

/-! ## Partition predicates -/

/-- A two-block partition meeting capacities `b₁`, `b₂`: a set `I` of indices whose mass is at most
`b₁`, with the complement's mass at most `b₂`. -/
def AdmitsPartition₂ (y : Fin ℓ → 𝕜) (b₁ b₂ : 𝕜) : Prop :=
  ∃ I : Finset (Fin ℓ), (∑ i ∈ I, y i) ≤ b₁ ∧ (∑ i ∈ univ \ I, y i) ≤ b₂

/-- A three-block partition meeting capacities `b₁`, `b₂`, `b₃`. -/
def AdmitsPartition₃ (y : Fin ℓ → 𝕜) (b₁ b₂ b₃ : 𝕜) : Prop :=
  ∃ I J : Finset (Fin ℓ), Disjoint I J ∧
    (∑ i ∈ I, y i) ≤ b₁ ∧ (∑ i ∈ J, y i) ≤ b₂ ∧ (∑ i ∈ univ \ (I ∪ J), y i) ≤ b₃

/-- A four-block partition meeting capacities `b₁`, `b₂`, `b₃`, `b₄`. -/
def AdmitsPartition₄ (y : Fin ℓ → 𝕜) (b₁ b₂ b₃ b₄ : 𝕜) : Prop :=
  ∃ I J K : Finset (Fin ℓ), Disjoint I J ∧ Disjoint I K ∧ Disjoint J K ∧
    (∑ i ∈ I, y i) ≤ b₁ ∧ (∑ i ∈ J, y i) ≤ b₂ ∧ (∑ i ∈ K, y i) ≤ b₃ ∧
      (∑ i ∈ univ \ (I ∪ J ∪ K), y i) ≤ b₄

/-! ## The trivial partition

When the first capacity already absorbs the whole tuple, put everything in the first block and
leave the others empty. -/

omit [IsStrictOrderedRing 𝕜] in
/-- If the total mass fits in `b₁` and `b₂` is nonnegative, the trivial two-block partition
works. -/
theorem admitsPartition₂_of_total_le {y : Fin ℓ → 𝕜} {b₁ b₂ : 𝕜}
    (htot : ∑ i, y i ≤ b₁) (hb₂ : 0 ≤ b₂) : AdmitsPartition₂ y b₁ b₂ := by
  refine ⟨univ, by simpa using htot, ?_⟩
  simpa using hb₂

omit [IsStrictOrderedRing 𝕜] in
/-- The three-block analogue. -/
theorem admitsPartition₃_of_total_le {y : Fin ℓ → 𝕜} {b₁ b₂ b₃ : 𝕜}
    (htot : ∑ i, y i ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃) : AdmitsPartition₃ y b₁ b₂ b₃ := by
  refine ⟨univ, ∅, disjoint_empty_right _, by simpa using htot, by simpa using hb₂, ?_⟩
  simpa using hb₃

omit [IsStrictOrderedRing 𝕜] in
/-- The four-block analogue. -/
theorem admitsPartition₄_of_total_le {y : Fin ℓ → 𝕜} {b₁ b₂ b₃ b₄ : 𝕜}
    (htot : ∑ i, y i ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃) (hb₄ : 0 ≤ b₄) :
    AdmitsPartition₄ y b₁ b₂ b₃ b₄ := by
  refine ⟨univ, ∅, ∅, disjoint_empty_right _, disjoint_empty_right _, disjoint_empty_right _,
    by simpa using htot, by simpa using hb₂, by simpa using hb₃, ?_⟩
  simpa using hb₄


/-! ## Monotonicity in the capacities

Conditions (A)–(E) of Proposition 3 state their own capacities, while the extraction lemmas ask for
whatever the target window dictates. These let the former be weakened to the latter. -/

omit [IsStrictOrderedRing 𝕜] in
/-- A two-block partition survives enlarging its capacities. -/
theorem AdmitsPartition₂.mono {y : Fin ℓ → 𝕜} {b₁ b₂ b₁' b₂' : 𝕜}
    (h : AdmitsPartition₂ y b₁ b₂) (h₁ : b₁ ≤ b₁') (h₂ : b₂ ≤ b₂') :
    AdmitsPartition₂ y b₁' b₂' := by
  obtain ⟨I, hI₁, hI₂⟩ := h
  exact ⟨I, le_trans hI₁ h₁, le_trans hI₂ h₂⟩

omit [IsStrictOrderedRing 𝕜] in
/-- The three-block analogue. -/
theorem AdmitsPartition₃.mono {y : Fin ℓ → 𝕜} {b₁ b₂ b₃ b₁' b₂' b₃' : 𝕜}
    (h : AdmitsPartition₃ y b₁ b₂ b₃) (h₁ : b₁ ≤ b₁') (h₂ : b₂ ≤ b₂') (h₃ : b₃ ≤ b₃') :
    AdmitsPartition₃ y b₁' b₂' b₃' := by
  obtain ⟨I, J, hd, hI, hJ, hK⟩ := h
  exact ⟨I, J, hd, le_trans hI h₁, le_trans hJ h₂, le_trans hK h₃⟩

omit [IsStrictOrderedRing 𝕜] in
/-- The four-block analogue. -/
theorem AdmitsPartition₄.mono {y : Fin ℓ → 𝕜} {b₁ b₂ b₃ b₄ b₁' b₂' b₃' b₄' : 𝕜}
    (h : AdmitsPartition₄ y b₁ b₂ b₃ b₄) (h₁ : b₁ ≤ b₁') (h₂ : b₂ ≤ b₂') (h₃ : b₃ ≤ b₃')
    (h₄ : b₄ ≤ b₄') : AdmitsPartition₄ y b₁' b₂' b₃' b₄' := by
  obtain ⟨I, J, K, d₁, d₂, d₃, hI, hJ, hK, hL⟩ := h
  exact ⟨I, J, K, d₁, d₂, d₃, le_trans hI h₁, le_trans hJ h₂, le_trans hK h₃, le_trans hL h₄⟩

/-! ## Point A's caps

The parameters come from `Gap212.PointA` over `ℚ` and are cast into `𝕜`, so the exact rational
arithmetic proved there is reused rather than re-done. -/

open Gap212.PointA

/-! The Point A parameters are rational, and `Gap212.PointA` records their exact values. Here
they appear cast into `𝕜`; these five lemmas evaluate the casts once so that each capacity
comparison below reduces to `norm_num` over `𝕜`. -/

/-- The cast of Point A's `ξ₁` into `𝕜` is `23317/60000`. -/
theorem cast_ξ₁ : ((ξ₁ : ℚ) : 𝕜) = 23317 / 60000 := by rw [ξ₁]; push_cast; ring

/-- The cast of Point A's `ξ₃` into `𝕜` is `2/5`. -/
theorem cast_ξ₃ : ((ξ₃ : ℚ) : 𝕜) = 2 / 5 := by rw [ξ₃]; push_cast; ring

/-- The cast of Point A's `δ` into `𝕜` is `179/10000`. -/
theorem cast_δ : ((δ : ℚ) : 𝕜) = 179 / 10000 := by rw [δ]; push_cast; ring

/-- The cast of Point A's `ω` into `𝕜` is `13/2000`. -/
theorem cast_ω : ((ω : ℚ) : 𝕜) = 13 / 2000 := by rw [ω]; push_cast; ring

/-- The cast of Point A's `ϵ` into `𝕜` is `1/10^10`. -/
theorem cast_ϵ : ((ϵ : ℚ) : 𝕜) = 1 / 10 ^ 10 := by rw [ϵ]; push_cast; ring

/-- Point A's cap `B_{1,m}`: `31/200` for `m ≤ 2`, and `17/100` for `m ≥ 3`. Matches the `B` field
of `Gap212.gap212Params`. -/
def Bcap (m : ℕ) : 𝕜 := if m ≤ 2 then (B₁ : 𝕜) else (B₃ : 𝕜)

/-- Every Point A cap is at most `17/100`. -/
theorem Bcap_le (m : ℕ) : (Bcap m : 𝕜) ≤ 17 / 100 := by
  unfold Bcap
  have h₁ : ((B₁ : ℚ) : 𝕜) = 31 / 200 := by rw [B₁]; push_cast; ring
  have h₃ : ((B₃ : ℚ) : 𝕜) = 17 / 100 := by rw [B₃]; push_cast; ring
  split_ifs
  · rw [h₁]; norm_num
  · rw [h₃]

/-- Hence any two caps sum to at most `17/50`. -/
theorem Bcap_add_le (m m' : ℕ) : (Bcap m : 𝕜) + Bcap m' ≤ 17 / 50 := by
  have h₁ := Bcap_le (𝕜 := 𝕜) m
  have h₂ := Bcap_le (𝕜 := 𝕜) m'
  linarith

/-- **The total mass of any Point A rough-factor tuple is at most `17/50`.** -/
theorem total_le_pointA {m m' : ℕ} {y : Fin (m + m') → 𝕜}
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (δ : 𝕜)) : ∑ i, y i ≤ 17 / 50 :=
  (total_le hy).trans (Bcap_add_le m m')

/-! ## Conditions (A), (B), (C) and (E) at Point A

Each is discharged by the trivial partition: the first capacity exceeds `17/50`, and the remaining
capacities are positive. The comparisons are the cast-up forms of the exact rational facts in
`Gap212.PointA`. -/

/-- **Condition (A)**, the Type I condition of Proposition 3, at Point A: capacities `ξ₁ - 2ϵ` and
`1/6 - 4ω - 2ϵ`. -/
theorem conditionA {m m' : ℕ} {y : Fin (m + m') → 𝕜}
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (δ : 𝕜)) :
    AdmitsPartition₂ y ((ξ₁ : 𝕜) - 2 * (ϵ : 𝕜)) (1 / 6 - 4 * (ω : 𝕜) - 2 * (ϵ : 𝕜)) := by
  have hb₁ : (17 / 50 : 𝕜) ≤ (ξ₁ : 𝕜) - 2 * (ϵ : 𝕜) := by
    rw [cast_ξ₁, cast_ϵ]; norm_num
  have hb₂ : (0 : 𝕜) ≤ 1 / 6 - 4 * (ω : 𝕜) - 2 * (ϵ : 𝕜) := by
    rw [cast_ω, cast_ϵ]; norm_num
  exact admitsPartition₂_of_total_le ((total_le_pointA hy).trans hb₁) hb₂

/-- **Condition (B)**, the Type IIa condition, at Point A. -/
theorem conditionB {m m' : ℕ} {y : Fin (m + m') → 𝕜}
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (δ : 𝕜)) :
    AdmitsPartition₂ y (2 / 5 + 24 * (ω : 𝕜) / 5 + 7 * (δ : 𝕜) / 5 - 2 * (ϵ : 𝕜))
      (1 / 14 - 24 * (ω : 𝕜) / 7 - 2 * (ϵ : 𝕜)) := by
  have hb₁ : (17 / 50 : 𝕜) ≤ 2 / 5 + 24 * (ω : 𝕜) / 5 + 7 * (δ : 𝕜) / 5 - 2 * (ϵ : 𝕜) := by
    rw [cast_ω, cast_δ, cast_ϵ]; norm_num
  have hb₂ : (0 : 𝕜) ≤ 1 / 14 - 24 * (ω : 𝕜) / 7 - 2 * (ϵ : 𝕜) := by
    rw [cast_ω, cast_ϵ]; norm_num
  exact admitsPartition₂_of_total_le ((total_le_pointA hy).trans hb₁) hb₂

/-- **Condition (C)**, the Type IIb condition, at Point A: three capacities. -/
theorem conditionC {m m' : ℕ} {y : Fin (m + m') → 𝕜}
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (δ : 𝕜)) :
    AdmitsPartition₃ y (1 / 3 + 24 * (ω : 𝕜) / 3 + 7 * (δ : 𝕜) / 3 - 4 * (ϵ : 𝕜))
      (1 / 10 - 34 * (ω : 𝕜) / 5 - 7 * (δ : 𝕜) / 5 - 4 * (ϵ : 𝕜))
      (1 / 35 + 22 * (ω : 𝕜) / 35 + 21 * (δ : 𝕜) / 35 - 4 * (ϵ : 𝕜)) := by
  have hb₁ : (17 / 50 : 𝕜) ≤ 1 / 3 + 24 * (ω : 𝕜) / 3 + 7 * (δ : 𝕜) / 3 - 4 * (ϵ : 𝕜) := by
    rw [cast_ω, cast_δ, cast_ϵ]; norm_num
  have hb₂ : (0 : 𝕜) ≤ 1 / 10 - 34 * (ω : 𝕜) / 5 - 7 * (δ : 𝕜) / 5 - 4 * (ϵ : 𝕜) := by
    rw [cast_ω, cast_δ, cast_ϵ]; norm_num
  have hb₃ : (0 : 𝕜) ≤ 1 / 35 + 22 * (ω : 𝕜) / 35 + 21 * (δ : 𝕜) / 35 - 4 * (ϵ : 𝕜) := by
    rw [cast_ω, cast_δ, cast_ϵ]; norm_num
  exact admitsPartition₃_of_total_le ((total_le_pointA hy).trans hb₁) hb₂ hb₃

/-- **Condition (E)**, the Type III condition, at Point A. -/
theorem conditionE {m m' : ℕ} {y : Fin (m + m') → 𝕜}
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (δ : 𝕜)) :
    AdmitsPartition₂ y (1 - 6 * (ω : 𝕜) - 3 * (ξ₃ : 𝕜) / 2 - 2 * (ϵ : 𝕜))
      (5 * (ω : 𝕜) / 2 + 3 * (ξ₃ : 𝕜) / 8 - 2 * (ϵ : 𝕜)) := by
  have hb₁ : (17 / 50 : 𝕜) ≤ 1 - 6 * (ω : 𝕜) - 3 * (ξ₃ : 𝕜) / 2 - 2 * (ϵ : 𝕜) := by
    rw [cast_ω, cast_ξ₃, cast_ϵ]; norm_num
  have hb₂ : (0 : 𝕜) ≤ 5 * (ω : 𝕜) / 2 + 3 * (ξ₃ : 𝕜) / 8 - 2 * (ϵ : 𝕜) := by
    rw [cast_ω, cast_ξ₃, cast_ϵ]; norm_num
  exact admitsPartition₂_of_total_le ((total_le_pointA hy).trans hb₁) hb₂

/-- **Conditions (A), (B), (C) and (E) together**, at Point A, over any linear ordered field — in
particular over `ℝ`, where the rough-factor tuples `yᵢ = log_x(fᵢ)` actually live. Four of the five
factor-packing conditions of Proposition 3. -/
theorem conditions_ABCE {m m' : ℕ} {y : Fin (m + m') → 𝕜}
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (δ : 𝕜)) :
    AdmitsPartition₂ y ((ξ₁ : 𝕜) - 2 * (ϵ : 𝕜)) (1 / 6 - 4 * (ω : 𝕜) - 2 * (ϵ : 𝕜)) ∧
      AdmitsPartition₂ y (2 / 5 + 24 * (ω : 𝕜) / 5 + 7 * (δ : 𝕜) / 5 - 2 * (ϵ : 𝕜))
        (1 / 14 - 24 * (ω : 𝕜) / 7 - 2 * (ϵ : 𝕜)) ∧
      AdmitsPartition₃ y (1 / 3 + 24 * (ω : 𝕜) / 3 + 7 * (δ : 𝕜) / 3 - 4 * (ϵ : 𝕜))
        (1 / 10 - 34 * (ω : 𝕜) / 5 - 7 * (δ : 𝕜) / 5 - 4 * (ϵ : 𝕜))
        (1 / 35 + 22 * (ω : 𝕜) / 35 + 21 * (δ : 𝕜) / 35 - 4 * (ϵ : 𝕜)) ∧
      AdmitsPartition₂ y (1 - 6 * (ω : 𝕜) - 3 * (ξ₃ : 𝕜) / 2 - 2 * (ϵ : 𝕜))
        (5 * (ω : 𝕜) / 2 + 3 * (ξ₃ : 𝕜) / 8 - 2 * (ϵ : 𝕜)) :=
  ⟨conditionA hy, conditionB hy, conditionC hy, conditionE hy⟩

/-! ## Instantiation at `ℝ`

The tuples of Proposition 3 are `yᵢ = log_x(fᵢ)`, so `ℝ` is the field the conditions are used
over. -/

/-- **Condition (A) at Point A over `ℝ`**, the field the rough-factor tuples live in. -/
theorem conditionA_real {m m' : ℕ} {y : Fin (m + m') → ℝ}
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' ((δ : ℚ) : ℝ)) :
    AdmitsPartition₂ y (((ξ₁ : ℚ) : ℝ) - 2 * ((ϵ : ℚ) : ℝ))
      (1 / 6 - 4 * ((ω : ℚ) : ℝ) - 2 * ((ϵ : ℚ) : ℝ)) :=
  conditionA hy

/-- Every Point A rough-factor tuple of reals has total mass at most `17/50`. -/
theorem total_le_pointA_real {m m' : ℕ} {y : Fin (m + m') → ℝ}
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' ((δ : ℚ) : ℝ)) : ∑ i, y i ≤ 17 / 50 :=
  total_le_pointA hy

end Gap212.Packing
