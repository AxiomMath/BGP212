/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public meta import Gap212.Attr

/-!
# The Point A parameters, and the side conditions of [2] at them

This module checks, in exact rational arithmetic, the side conditions that [2] verifies for its
own `H₁ ≤ 240` parameters, at the `k = 45` parameter set called Point A.

Everything here is a statement about explicit rationals, so every proof is `norm_num`. Several of
the inequalities are tight — condition (II) of [2, Proposition 3] holds at Point A with a margin
of `1/10000` — so they are settled by exact arithmetic.

## Scale conventions

All values are in the physical scale of [2, Definition 1], which is also the scale of
`Gap212.gap212Params`.

## Main definitions

* `Gap212.PointA.ξ₁`, `ξ₂`, `ξ₃`: the Harman decomposition parameters, `(23317/60000, 2/5, 2/5)`.
* `Gap212.PointA.A₁`, `δ`, `ε`: the support parameters.
* `Gap212.PointA.ω`: the level parameter `ω(1,1) = A₁ - 1/4`.
* `Gap212.PointA.ϵ`: the fixed slack `10⁻¹⁰` of [2, Definition 9], distinct from `ε`.

## Main results

* `Gap212.PointA.harman_conditions`: the five inequalities of [2, Proposition 2].
* `Gap212.PointA.typeI_condition`, `typeII_condition_a/b`, `typeIII_condition`: conditions (I),
  (II), (III) of [2, Proposition 3].
* `Gap212.PointA.capSum_le`: `B_{1,m} + B_{1,m'} ≤ 17/50` for all `m`, `m'`.
* `Gap212.PointA.trivial_partition_bound_A/B/C/E`: each of conditions (A), (B), (C), (E) has its
  `I₁`-bound strictly above `17/50`, so the whole tuple may be put in `I₁` and `I₂ = ∅`.
* `Gap212.PointA.c₂_eq_zero_condition`: `ξ₂ ≤ 4/10`, which is what forces `c₂ = 0`.
* `Gap212.PointA.gamma₂_empty`, `gammaStar₂_empty`: the two correction sums of [2, Proposition 2]
  have empty index sets at `ξ₂ = 2/5`, which is what forces `c₁ = 0` and `ρ = 1_ℙ`.
-/

@[expose] public section

namespace Gap212.PointA

/-! ## The parameters -/

/-- The fixed slack `ϵ = 10⁻¹⁰` of [2, Definition 9]. Distinct from the support enlargement
`ε`. -/
def ϵ : ℚ := 1 / 10 ^ 10

/-- Harman parameter `ξ₁ = 23317/60000`. -/
def ξ₁ : ℚ := 23317 / 60000

/-- Harman parameter `ξ₂ = 2/5`. The value `4/10` is the exact threshold below which the prime
minorant degenerates to `1_ℙ`; Point A sits *on* it. -/
def ξ₂ : ℚ := 2 / 5

/-- Harman parameter `ξ₃ = 2/5`. -/
def ξ₃ : ℚ := 2 / 5

/-- The single interior node `A₁ = 513/2000 = 0.2565`. Point A has `n = 1`, one stratum. -/
def A₁ : ℚ := 513 / 2000

/-- The smallness threshold `δ = 179/10000 = 0.0179` (physical scale). -/
def δ : ℚ := 179 / 10000

/-- The support enlargement `ε = 17/2000 = 0.0085`. -/
def ε : ℚ := 17 / 2000

/-- The level parameter `ω(1,1) = (A₁ + A₁)/2 - 1/4 = A₁ - 1/4`. With `n = 1` there is only one
value. -/
def ω : ℚ := 13 / 2000

/-- The rough cap `B_{1,1} = B_{1,2} = 31/200 = 0.155` (physical scale). -/
def B₁ : ℚ := 31 / 200

/-- The rough cap `B_{1,m} = 17/100 = 0.17` for `m ≥ 3` (physical scale). -/
def B₃ : ℚ := 17 / 100

/-- The level of distribution `ϑ = 1/2 + 2ω = 513/1000`. -/
def ϑ : ℚ := 513 / 1000

/-! ## Internal consistency of the parameters -/

/-- `ω` really is `A₁ - 1/4`, i.e. the definition above agrees with `ω(1,1)` of [2, Proposition 3]
at `j = j' = 1`. -/
theorem ω_eq : ω = A₁ - 1 / 4 := by norm_num [ω, A₁]

/-- `ϑ = 1/2 + 2ω`, the relation between the level of distribution and `ω`. -/
theorem ϑ_eq : ϑ = 1 / 2 + 2 * ω := by norm_num [ϑ, ω]

/-- `A₁ < 1/2 - ε`: the last node lies below the cutoff required by [2, Definition 1]. -/
theorem A₁_lt : A₁ < 1 / 2 - ε := by norm_num [A₁, ε]

/-- `δ < B₁`, part of the condition of [2, Definition 1] on the bound matrix. -/
theorem δ_lt_B₁ : δ < B₁ := by norm_num [δ, B₁]

/-- `B₃ ≤ B₁ + δ`: the step condition `B_{j,m+1} ≤ B_{j,m} + δ` of [2, Definition 1], at the one
place where the cap increases (`m = 2 → 3`). Here `B₃ - B₁ = 3/200` and `δ = 179/10000`, so the
slack is `29/10000`. -/
theorem B₃_le : B₃ ≤ B₁ + δ := by norm_num [B₃, B₁, δ]

/-! ## [2, Proposition 2]: the five inequalities on `(ξ₁, ξ₂, ξ₃)`

These are the conditions under which Harman's sieve construction yields a prime minorant with the
equidistribution properties the sieve criterion [2, Proposition 1] consumes. The first and third
hold with slack `683/30000` and `683/60000`. -/

/-- `2ξ₁ + 3ξ₂ < 2`: the two sides are `59317/30000` and `60000/30000`. -/
theorem harman_1 : 2 * ξ₁ + 3 * ξ₂ < 2 := by norm_num [ξ₁, ξ₂]

/-- `ξ₂ ≤ ξ₃`. Point A takes them equal; this is the condition that lets Polymath's Type III
estimate be applied inside Harman's sieve construction. -/
theorem harman_2 : ξ₂ ≤ ξ₃ := by norm_num [ξ₂, ξ₃]

/-- `ξ₁ + 9ξ₂ < 4`: `239317/60000` against `240000/60000`. -/
theorem harman_3 : ξ₁ + 9 * ξ₂ < 4 := by norm_num [ξ₁, ξ₂]

/-- `2ξ₁ + ξ₂ > 1`. -/
theorem harman_4 : 1 < 2 * ξ₁ + ξ₂ := by norm_num [ξ₁, ξ₂]

/-- `17ξ₂ < 7`. -/
theorem harman_5 : 17 * ξ₂ < 7 := by norm_num [ξ₂]

/-- All five inequalities of [2, Proposition 2], together. -/
theorem harman_conditions :
    2 * ξ₁ + 3 * ξ₂ < 2 ∧ ξ₂ ≤ ξ₃ ∧ ξ₁ + 9 * ξ₂ < 4 ∧ 1 < 2 * ξ₁ + ξ₂ ∧ 17 * ξ₂ < 7 :=
  ⟨harman_1, harman_2, harman_3, harman_4, harman_5⟩

/-! ## The degeneration of the minorant at `ξ₂ = 2/5`

[2, Proposition 2] sets `c₂ = 24` when `ξ₂ > 4/10` and `c₂ = 0` when `ξ₂ ≤ 4/10`, and remarks
that in the latter case `ρ(n;x)` is simply `1_ℙ(n)`. Point A sits exactly on the threshold.

The reason `ρ` degenerates is that both correction sums have empty index sets. Each demands
exponents `αᵢ > 1 - 2ξ₂` together with a pairwise sum `< ξ₂`; at `ξ₂ = 2/5` we have
`1 - 2ξ₂ = 1/5` and `2 · (1/5) = 2/5 = ξ₂`, so no such pair exists. The two lemmas below are that
argument. -/

/-- `ξ₂ ≤ 4/10`, which is the case distinction in [2, Proposition 2] that gives `c₂ = 0`. -/
theorem c₂_eq_zero_condition : ξ₂ ≤ 4 / 10 := by norm_num [ξ₂]

/-- `1 - 2ξ₂ = 1/5` at Point A. -/
theorem one_sub_two_ξ₂ : 1 - 2 * ξ₂ = 1 / 5 := by norm_num [ξ₂]

/-- **`Γ₂` is empty.** The first correction sum of [2, Proposition 2] ranges over
`n = p₁p₂p₃p₄p₅` with `1 - 2ξ₂ < α₄ < α₃ < α₂ < α₁ < ξ₂` and `α₁ + α₂ < ξ₂`. At `ξ₂ = 2/5` the
constraints `1 - 2ξ₂ < α₂ < α₁` and `α₁ + α₂ < ξ₂` are contradictory, so the sum is empty.

Only the two largest exponents are needed, so the lemma is stated for them alone. -/
theorem gamma₂_empty {α₁ α₂ : ℚ} (h₂ : 1 - 2 * ξ₂ < α₂) (h₂₁ : α₂ < α₁)
    (hsum : α₁ + α₂ < ξ₂) : False := by
  rw [one_sub_two_ξ₂] at h₂
  have hξ : ξ₂ = 2 / 5 := rfl
  rw [hξ] at hsum
  linarith

/-- **`Γ*₂` is empty.** The second correction sum ranges over `n = p₂p₃p₄p₅p₆` with
`1 - 2ξ₂ ≤ αᵢ ≤ 8ξ₂ - 3` for `i ∈ {2,…,6}` and `α₂ + α₄ < ξ₂`. At `ξ₂ = 2/5` the two exponents
`α₂, α₄ ≥ 1/5` already sum to `2/5 = ξ₂`, contradicting `α₂ + α₄ < ξ₂`. -/
theorem gammaStar₂_empty {α₂ α₄ : ℚ} (h₂ : 1 - 2 * ξ₂ ≤ α₂) (h₄ : 1 - 2 * ξ₂ ≤ α₄)
    (hsum : α₂ + α₄ < ξ₂) : False := by
  rw [one_sub_two_ξ₂] at h₂ h₄
  have hξ : ξ₂ = 2 / 5 := rfl
  rw [hξ] at hsum
  linarith

/-- At Point A the window `[1 - 2ξ₂, 8ξ₂ - 3]` constraining every exponent of `Γ*₂` is a single
point: `1 - 2ξ₂ = 8ξ₂ - 3 = 1/5`. This is a second, independent way to see that `Γ*₂` is empty —
five exponents each equal to `1/5` sum to `1`, leaving no room for the sixth factor. -/
theorem gammaStar₂_window_degenerate : 1 - 2 * ξ₂ = 8 * ξ₂ - 3 := by norm_num [ξ₂]

/-! ## Conditions (I), (II), (III) of [2, Proposition 3]

With `n = 1` the only node is `A₁`, so `A_n = A₁` throughout. -/

/-- **Condition (I)**, the Type I condition:
`min{ξ₁ - 4A₁ + 2/3, 9/7 - (34/7)A₁} - 2ϵ > δ`.

The first branch is the binding one: it evaluates to `1757/60000 ≈ 0.029283`, against
`δ = 0.0179`. -/
theorem typeI_condition :
    δ < min (ξ₁ - 4 * A₁ + 2 / 3) (9 / 7 - (34 / 7) * A₁) - 2 * ϵ := by
  rw [lt_sub_iff_add_lt, lt_min_iff]
  refine ⟨by norm_num [δ, ξ₁, A₁, ϵ], by norm_num [δ, A₁, ϵ]⟩

/-- **Condition (II)**, first half: `19/2 - 36A₁ - 13δ - 15ϵ ≥ 0`. Evaluates to
`333/10000 - 15ϵ ≥ 0`, so it holds with a slack of `66599997/2000000000` at `ϵ = 10⁻¹⁰`. -/
theorem typeII_condition_a : 0 ≤ 19 / 2 - 36 * A₁ - 13 * δ - 15 * ϵ := by
  norm_num [A₁, δ, ϵ]

/-- **Condition (II)**, second half:
`min{ξ₂/10 - 32A₁/10 + 8/10, ξ₂/4 + 11/16 - 3A₁} - 2ϵ ≥ δ`.

This is the tightest condition in the whole parameter set. The second branch binds, at
`9/500 = 0.018`, against `δ = 179/10000 = 0.0179`: a margin of `1/10000`. -/
theorem typeII_condition_b :
    δ ≤ min (ξ₂ / 10 - 32 * A₁ / 10 + 8 / 10) (ξ₂ / 4 + 11 / 16 - 3 * A₁) - 2 * ϵ := by
  rw [le_sub_iff_add_le, le_min_iff]
  refine ⟨by norm_num [δ, ξ₂, A₁, ϵ], by norm_num [δ, ξ₂, A₁, ϵ]⟩

/-- **Condition (III)**, the Type III condition: `11/8 - (7/2)A₁ - (9/8)ξ₃ - 2ϵ > δ`. Evaluates to
`109/4000 = 0.02725` against `δ = 0.0179`. -/
theorem typeIII_condition : δ < 11 / 8 - (7 / 2) * A₁ - (9 / 8) * ξ₃ - 2 * ϵ := by
  norm_num [δ, A₁, ξ₃, ϵ]

/-! ## Why conditions (A), (B), (C) and (E) are trivial at Point A

Conditions (A), (B), (C) and (E) of [2, Proposition 3] each ask for a partition of
`{1, …, m+m'}` whose first block has weight at most some bound. A tuple in
`Ξ(B_{1,m}, B_{1,m'}, m, m', δ)` has *total* weight at most `B_{1,m} + B_{1,m'} ≤ 17/50`. So
whenever a condition's `I₁`-bound exceeds `17/50`, the partition `I₁ = {1, …, m+m'}`, `I₂ = ∅`
works, and the remaining blocks carry weight `0`, which is below every bound (each is positive at
Point A).

[2] makes the same observation for its own parameters ("the upper bound on the sum
over `I₁` in each of the conditions (A), (B), (C) and (E) is greater than `0.34`"). It leaves
condition (D) as the only one needing a genuine argument. -/

/-- Every cap is at most `17/100`, so any two sum to at most `17/50`. Since `B_{1,m} ∈ {B₁, B₃}`
for every `m`, this bounds the total weight of any tuple in `Ξ(B_{1,m}, B_{1,m'}, m, m', δ)`. -/
theorem capSum_le {b b' : ℚ} (hb : b = B₁ ∨ b = B₃) (hb' : b' = B₁ ∨ b' = B₃) :
    b + b' ≤ 17 / 50 := by
  rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl <;> norm_num [B₁, B₃]

/-- **(A)** The `I₁`-bound of the Type I condition, `ξ₁ - 2ϵ`, exceeds `17/50`. -/
theorem trivial_partition_bound_A : 17 / 50 < ξ₁ - 2 * ϵ := by norm_num [ξ₁, ϵ]

/-- **(A)** The `I₂`-bound, `1/6 - 4ω - 2ϵ`, is positive, so the empty block satisfies it. -/
theorem trivial_partition_bound_A' : 0 < 1 / 6 - 4 * ω - 2 * ϵ := by norm_num [ω, ϵ]

/-- **(B)** The `I₁`-bound of the Type IIa condition, `2/5 + 24ω/5 + 7δ/5 - 2ϵ ≈ 0.45626`, exceeds
`17/50`. -/
theorem trivial_partition_bound_B : 17 / 50 < 2 / 5 + 24 * ω / 5 + 7 * δ / 5 - 2 * ϵ := by
  norm_num [ω, δ, ϵ]

/-- **(B)** The `I₂`-bound, `1/14 - 24ω/7 - 2ϵ ≈ 0.049143`, is positive. -/
theorem trivial_partition_bound_B' : 0 < 1 / 14 - 24 * ω / 7 - 2 * ϵ := by norm_num [ω, ϵ]

/-- **(C)** The `I₁`-bound of the Type IIb condition, `1/3 + 24ω/3 + 7δ/3 - 4ϵ ≈ 0.4271`, exceeds
`17/50`. -/
theorem trivial_partition_bound_C : 17 / 50 < 1 / 3 + 24 * ω / 3 + 7 * δ / 3 - 4 * ϵ := by
  norm_num [ω, δ, ϵ]

/-- **(C)** The `I₂`- and `I₃`-bounds of the Type IIb condition are positive, so the two empty
blocks satisfy them. -/
theorem trivial_partition_bound_C' :
    0 < 1 / 10 - 34 * ω / 5 - 7 * δ / 5 - 4 * ϵ ∧
      0 < 1 / 35 + 22 * ω / 35 + 21 * δ / 35 - 4 * ϵ := by
  refine ⟨by norm_num [ω, δ, ϵ], by norm_num [ω, δ, ϵ]⟩

/-- **(E)** The `I₁`-bound of the Type III condition, `1 - 6ω - 3ξ₃/2 - 2ϵ = 0.361 - 2ϵ`, exceeds
`17/50`. -/
theorem trivial_partition_bound_E : 17 / 50 < 1 - 6 * ω - 3 * ξ₃ / 2 - 2 * ϵ := by
  norm_num [ω, ξ₃, ϵ]

/-- **(E)** The `I₂`-bound, `5ω/2 + 3ξ₃/8 - 2ϵ`, is positive. -/
theorem trivial_partition_bound_E' : 0 < 5 * ω / 2 + 3 * ξ₃ / 8 - 2 * ϵ := by norm_num [ω, ξ₃, ϵ]

/-! ## Condition (D)

Condition (D), the Type IIc condition, is the one that does not degenerate: its four bounds depend
on an auxiliary `ω₀ ∈ [-ϵ, ω]` and on `γ` ranging over `[ξ₂ - ϵ, 1/3 + 8ω + 7δ/3 + 3ϵ]`, and the
`I₄`-bound `8ω₀` can be as small as `-8ϵ`. So no single trivial partition serves, and a genuine
argument is required. The range of `γ` is recorded here. -/

/-- The upper end of condition (D)'s `γ`-range, `1/3 + 24ω/3 + 7δ/3 + 3ϵ`, lies strictly above the
lower end `ξ₂ - ϵ`, so the range is nonempty and the condition has content. -/
theorem typeIIc_γ_range_nonempty : ξ₂ - ϵ < 1 / 3 + 24 * ω / 3 + 7 * δ / 3 + 3 * ϵ := by
  norm_num [ξ₂, ω, δ, ϵ]

end Gap212.PointA
