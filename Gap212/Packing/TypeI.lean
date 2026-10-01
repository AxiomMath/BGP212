/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.Basic
public meta import Gap212.Attr

/-!
# The Type I route: two `γ`-regimes, and the condition Proposition 3 does not print

The Type I estimate is applied twice, on either side of `γ = 1/2`, with a different window width
each time. Each application needs its own factor-packing condition, and only the first of the two
appears in Proposition 3's lettered list — as condition (A). The second appears nowhere in the
statement: it is introduced inside the proof, as

    ∑_{I₁} yᵢ ≤ 1/2 - 2ω_max - 2ϵ    and    ∑_{I₂} yᵢ ≤ 1/14 - (68/14)ω_max - 2ϵ,

and it is genuinely a sixth condition rather than a consequence of the five. Condition (A)'s second
capacity is `1/6 - 4ω - 2ϵ`, which at Point A is `0.1407`, while this one is `0.0399`; a partition
witnessing (A) therefore need not witness this.
`Gap212.Packing.conditionA_cap₂_gt_conditionA'_cap₂` records that comparison.

So Proposition 3's hypothesis list is incomplete as printed. Below it is called **condition (A′)**
and verified at Point A, where — like (A), (B), (C) and (E) — the trivial partition suffices: the
first capacity is `0.487`, comfortably above the maximum total mass `17/50`.

## The value of the second capacity

Condition (A′)'s second capacity is `1394999993/35000000000`, exceeding `δ` by
`768499993/35000000000`; `Gap212.Packing.conditionA'_cap₂_value` and `conditionA'_cap₂_slack`
record both.

## The two window widths are forced

The estimate's own inequalities turn out to be *identities* at these choices:

    3γ - 12ω - 3δ*₁(γ) = 1 + 3ϵ,        68ω + 14δ*₂ = 1 - 14ϵ.

Neither depends on `γ` or `ω` at all. So `δ*₁` and `δ*₂` are not merely sufficient choices but the
largest widths for which the Type I estimate applies, with the margin spent being exactly `3ϵ`
and `14ϵ`: no window can be widened to make a packing condition easier.

## Main results

* `Gap212.Packing.conditionA'`: the sixth condition, at Point A.
* `Gap212.Packing.typeI_analytic₁`, `typeI_analytic₂`: the two identities.
* `Gap212.Packing.deltaStarI₁_ge_delta`, `deltaStarI₂_ge_delta`: condition (I)'s two branches,
  which are exactly `δ*(γ) ≥ δ` in each regime.
* `Gap212.Packing.conditionA'_cap₂_value`, `conditionA'_cap₂_slack`: the value of condition
  (A′)'s second capacity, and its slack over `δ`.
-/

@[expose] public section

namespace Gap212.Packing

open Finset Gap212.PointA

/-! ## The two window widths -/

section Widths

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The Type I window width in the first `γ`-regime, `γ ≤ 1/2`:
`δ*₁(γ) = γ - 4ω - 1/3 - e`. -/
@[gap212 "def_delta_star_typeI_low"]
def deltaStarI₁ (γ ω e : 𝕜) : 𝕜 := γ - 4 * ω - 1 / 3 - e

/-- The Type I window width in the second `γ`-regime, `1/2 < γ ≤ 1/2 + 2ω + ε'`:
`δ*₂ = 1/14 - (68/14)ω - e`. It does not depend on `γ`. -/
@[gap212 "def_delta_star_typeI_high"]
def deltaStarI₂ (ω e : 𝕜) : 𝕜 := 1 / 14 - 68 * ω / 14 - e

/-- **The first regime's analytic inequality is an identity**: the Type I estimate's hypothesis
`3γ - 12ω - 3δ > 1` becomes `1 + 3e`, independently of `γ` and `ω`. So `δ*₁` is the largest width
the estimate permits, and the margin is exactly `3e`. -/
theorem typeI_analytic₁ (γ ω e : 𝕜) :
    3 * γ - 12 * ω - 3 * deltaStarI₁ γ ω e = 1 + 3 * e := by
  unfold deltaStarI₁; ring

/-- **The second regime's analytic inequality is an identity**: the Type I estimate's hypothesis
`68ω + 14δ < 1` becomes `1 - 14e`. The margin is exactly `14e`. -/
theorem typeI_analytic₂ (ω e : 𝕜) :
    68 * ω + 14 * deltaStarI₂ ω e = 1 - 14 * e := by
  unfold deltaStarI₂; ring

/-- The first regime's hypothesis, in the strict form the Type I estimate wants. -/
@[gap212 "lem_typeI_low_analytic"]
theorem typeI_analytic₁_lt {γ ω e : 𝕜} (he : 0 < e) :
    1 < 3 * γ - 12 * ω - 3 * deltaStarI₁ γ ω e := by
  rw [typeI_analytic₁]; linarith

/-- The second regime's hypothesis, in the strict form the Type I estimate wants. -/
@[gap212 "lem_typeI_high_analytic"]
theorem typeI_analytic₂_lt {ω e : 𝕜} (he : 0 < e) :
    68 * ω + 14 * deltaStarI₂ ω e < 1 := by
  rw [typeI_analytic₂]; linarith

/-- **Condition (A′)'s second capacity is `δ*₂` retreated by one more `e`.** The window width and
the partition capacity differ by exactly `e`, the inward retreat the closed-to-open conversion
costs. -/
theorem conditionA'_cap₂_eq (ω e : 𝕜) :
    1 / 14 - 68 * ω / 14 - 2 * e = deltaStarI₂ ω e - e := by
  unfold deltaStarI₂; ring

end Widths

/-! ## Condition (I) of Proposition 3, both branches

Condition (I) reads `min{ξ₁ - 4A_n + 2/3, 9/7 - (34/7)A_n} - 2ϵ > δ`. With `A_n = ω + 1/4` the two
entries are precisely `δ*₁(ξ₁ - ϵ) + ϵ` and `δ*₂ + ϵ`, so (I) says exactly that each regime's
window is at least as wide as `δ` — which is what the extraction lemmas require. Unlike condition
(A′), this half of the Type I hypotheses *is* printed. -/

/-- The first branch: at the smallest admissible `γ = ξ₁ - ϵ`, the first regime's window still
exceeds `δ`. The margin is about `0.0114`. -/
@[gap212 "lem_delta_star_typeI_low_ge_delta"]
theorem deltaStarI₁_ge_delta {γ : ℚ} (hγ : (ξ₁ : ℚ) - ϵ ≤ γ) : δ ≤ deltaStarI₁ γ ω ϵ := by
  unfold deltaStarI₁
  rw [show (ξ₁ : ℚ) = 23317 / 60000 from rfl] at hγ
  rw [show (δ : ℚ) = 179 / 10000 from rfl, show (ω : ℚ) = 13 / 2000 from rfl,
    show (ϵ : ℚ) = 1 / 10 ^ 10 from rfl] at *
  linarith

/-- The second branch: the second regime's window exceeds `δ`, with margin
`768499993/35000000000 ≈ 0.02196`. -/
@[gap212 "lem_delta_star_typeI_high_ge_delta"]
theorem deltaStarI₂_ge_delta : δ ≤ deltaStarI₂ ω ϵ := by
  unfold deltaStarI₂; norm_num [δ, ω, ϵ]

/-- Condition (I) is the conjunction of the two branches. The `min` of Proposition 3's statement is
this pair. -/
theorem typeI_condition_both {γ : ℚ} (hγ : (ξ₁ : ℚ) - ϵ ≤ γ) :
    δ ≤ deltaStarI₁ γ ω ϵ ∧ δ ≤ deltaStarI₂ ω ϵ :=
  ⟨deltaStarI₁_ge_delta hγ, deltaStarI₂_ge_delta⟩

/-! ## The value of the second capacity

Condition (A′)'s second capacity and its slack over `δ`, exactly. -/

/-- The value of the second capacity: `1/14 - (68/14)ω - 2ϵ = 1394999993/35000000000`. -/
theorem conditionA'_cap₂_value :
    1 / 14 - 68 * ω / 14 - 2 * ϵ = 1394999993 / 35000000000 := by
  norm_num [ω, ϵ]

/-- Its slack: the capacity exceeds `δ` by `768499993/35000000000 ≈ 0.021957142657`. -/
theorem conditionA'_cap₂_slack :
    (1 / 14 - 68 * ω / 14 - 2 * ϵ) - δ = 768499993 / 35000000000 := by
  norm_num [ω, ϵ, δ]

/-! ## Condition (A′) at Point A -/

section PointAConditions

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {m m' : ℕ}

/-- **Condition (A′)**: the Type I condition for the second `γ`-regime, at Point A. Capacities
`1/2 - 2ω - 2ϵ` and `1/14 - (68/14)ω - 2ϵ`.

This is the condition missing from Proposition 3's printed hypothesis list. Like the four that are
printed, it holds at Point A by the trivial partition: the first capacity is `0.487`, against a
maximum total mass of `17/50 = 0.34`. -/
theorem conditionA' {y : Fin (m + m') → 𝕜}
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (δ : 𝕜)) :
    AdmitsPartition₂ y (1 / 2 - 2 * (ω : 𝕜) - 2 * (ϵ : 𝕜))
      (1 / 14 - 68 * (ω : 𝕜) / 14 - 2 * (ϵ : 𝕜)) := by
  have hb₁ : (17 / 50 : 𝕜) ≤ 1 / 2 - 2 * (ω : 𝕜) - 2 * (ϵ : 𝕜) := by
    rw [cast_ω, cast_ϵ]; norm_num
  have hb₂ : (0 : 𝕜) ≤ 1 / 14 - 68 * (ω : 𝕜) / 14 - 2 * (ϵ : 𝕜) := by
    rw [cast_ω, cast_ϵ]; norm_num
  exact admitsPartition₂_of_total_le ((total_le_pointA hy).trans hb₁) hb₂

/-- **Condition (A′) is not condition (A).** Condition (A)'s second capacity strictly exceeds
condition (A′)'s, so the partition (A) provides need not satisfy (A′): a block with mass between
the two bounds witnesses (A) and violates (A′).

This is why (A′) has to be a separate hypothesis rather than a corollary, and hence why Proposition
3's list is incomplete rather than merely terse. -/
theorem conditionA_cap₂_gt_conditionA'_cap₂ :
    1 / 14 - 68 * (ω : 𝕜) / 14 - 2 * (ϵ : 𝕜) < 1 / 6 - 4 * (ω : 𝕜) - 2 * (ϵ : 𝕜) := by
  rw [cast_ω, cast_ϵ]; norm_num

/-- **The three two-block factor-packing conditions of the Type I and Type III routes at Point
A**, (A), (A′) and (E), together. -/
theorem conditions_A_A'_E {y : Fin (m + m') → 𝕜}
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (δ : 𝕜)) :
    AdmitsPartition₂ y ((ξ₁ : 𝕜) - 2 * (ϵ : 𝕜)) (1 / 6 - 4 * (ω : 𝕜) - 2 * (ϵ : 𝕜)) ∧
      AdmitsPartition₂ y (1 / 2 - 2 * (ω : 𝕜) - 2 * (ϵ : 𝕜))
        (1 / 14 - 68 * (ω : 𝕜) / 14 - 2 * (ϵ : 𝕜)) ∧
      AdmitsPartition₂ y (1 - 6 * (ω : 𝕜) - 3 * (ξ₃ : 𝕜) / 2 - 2 * (ϵ : 𝕜))
        (5 * (ω : 𝕜) / 2 + 3 * (ξ₃ : 𝕜) / 8 - 2 * (ϵ : 𝕜)) :=
  ⟨conditionA hy, conditionA' hy, conditionE hy⟩

end PointAConditions

/-- **Condition (A′) at Point A over `ℝ`**, the field the rough-factor tuples live in. -/
theorem conditionA'_real {m m' : ℕ} {y : Fin (m + m') → ℝ}
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (δ : ℝ)) :
    AdmitsPartition₂ y (1 / 2 - 2 * (ω : ℝ) - 2 * (ϵ : ℝ))
      (1 / 14 - 68 * (ω : ℝ) / 14 - 2 * (ϵ : ℝ)) :=
  conditionA' hy

end Gap212.Packing
