/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.Widths
public meta import Gap212.Attr

/-!
# The packing conditions the routes actually need, uniformly in `γ`

The containments of `Gap212.Routing.Containment` ask for a partition at capacities depending on `γ`
through the width `δ*(γ)`. The lettered conditions (A)–(E) of [2, Proposition 3] do not depend on
`γ` at all. So for each route there is something to check: that the stated condition implies the
`γ`-dependent one throughout that route's `γ`-range.

For Type IIa it does not.

## Condition (B) is stated at the bottom of the Type IIa range

The capacity the two-factor extraction needs for its second block is `1/2 - a(γ)`, for `a(γ)` the
window's lower end. Unwinding,

    1/2 - a(γ) = 5/14 - 9γ/14 - 12ω/7 + δ/2 - ε'/2 + 3ε',

which **decreases** in `γ`. Condition (B)'s second capacity `1/14 - 24ω/7 - 2ϵ` is `γ`-independent,
and at Point A the two agree at the bottom of the range and cross over at `γ ≈ 0.4757`:

| `γ` | required `1/2 - a(γ)` | condition (B) gives |
|---|---|---|
| `0.45626` (bottom) | `0.061640` | `0.049143` ✓ |
| `0.5` (top) | `0.033521` | `0.049143` ✗ |

So condition (B) is not sufficient for the Type IIa route above `γ ≈ 0.4757`, and the Type IIa
range runs to `1/2`. `Gap212.Routing.conditionB_insufficient_at_half` records the failure at the
top of the range.

## It is benign at Point A, for a reason worth stating

The condition the route actually needs holds throughout, and by the *trivial* partition: the first
capacity `γ - 3ε' - (δ*(γ) - δ)/2` is increasing in `γ` with minimum `0.45626` at the bottom of the
range, comfortably above the maximum rough mass `17/50 = 0.34`; and the second capacity, though
decreasing, stays positive (`0.0335` at worst). So everything goes into the first block and the
second is empty — `Gap212.Routing.typeIIa_packing`.

That is the same mechanism that discharges (A), (A′), (B), (C) and (E), so nothing new is needed at
Point A. What is needed is the observation that the `γ`-uniform statement, not condition (B), is
what the route consumes. The same holds for Type IIb, whose range is `[0.4271, 0.45626]` and whose
required capacities are `≥ 0.4271` and `≥ 0.0679`.

## Main results

* `Gap212.Routing.typeIIa_packing`, `typeIIb_packing`: the `γ`-uniform conditions, at Point A.
* `Gap212.Routing.conditionB_insufficient_at_half`: condition (B) fails at `γ = 1/2`.
-/

@[expose] public section

namespace Gap212.Routing

open Gap212.PointA Gap212.Packing

/-! ## The window the extraction needs

Named to match `Gap212.Routing.hasDivisorIn_of_qgen`, which runs the extraction on `[a, b]` for a
target window `(a', b')` of width `δ*`: the closed window sits inside the open one by retreating
`(δ* - δ)/2` at each end. -/

/-- The top of the extraction window at width `ds`, retreat `ε'`, threshold `d`. -/
noncomputable def winTop (γ ds ε' d : ℝ) : ℝ := γ - 3 * ε' - (ds - d) / 2

/-- The bottom of the extraction window. -/
noncomputable def winBot (γ ds ε' d : ℝ) : ℝ := γ - 3 * ε' - ds + (ds - d) / 2

/-- The window has width exactly `d`, which is the minimum the extraction accepts. -/
theorem winTop_sub_winBot (γ ds ε' d : ℝ) : winTop γ ds ε' d - winBot γ ds ε' d = d := by
  unfold winTop winBot; ring

/-! ## Type IIa -/

/-- **The Type IIa route's packing condition, uniformly in `γ`.** Throughout
`γ ∈ [2/5 + 24ω/5 + 7δ/5 + 2ϵ, 1/2]` and for any retreat `ε' ≤ ϵ`, every rough profile admits the
two-block partition the containment asks for.

Proved by the trivial partition: the first capacity is at least `0.45626`, above the maximum rough
mass `17/50`, and the second stays positive. -/
theorem typeIIa_packing {m m' : ℕ} {y : Fin (m + m') → ℝ} {γ ε' : ℝ}
    (hγlo : 2 / 5 + 24 * ((ω : ℚ) : ℝ) / 5 + 7 * ((δ : ℚ) : ℝ) / 5 + 2 * ((ϵ : ℚ) : ℝ) ≤ γ)
    (hγhi : γ ≤ 1 / 2) (hε'0 : 0 ≤ ε') (hε' : ε' ≤ ((ϵ : ℚ) : ℝ))
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (((δ : ℚ) : ℝ))) :
    AdmitsPartition₂ y
      (winTop γ (deltaStarIIa γ ((ω : ℚ) : ℝ) ((ϵ : ℚ) : ℝ)) ε' ((δ : ℚ) : ℝ))
      (1 / 2 - winBot γ (deltaStarIIa γ ((ω : ℚ) : ℝ) ((ϵ : ℚ) : ℝ)) ε' ((δ : ℚ) : ℝ)) := by
  have hd : ((δ : ℚ) : ℝ) = 179 / 10000 := cast_δ
  have hw : ((ω : ℚ) : ℝ) = 13 / 2000 := cast_ω
  have he : ((ϵ : ℚ) : ℝ) = 1 / 10 ^ 10 := cast_ϵ
  have htot : ∑ i, y i ≤ 17 / 50 := total_le_pointA hy
  simp only [hd, hw, he] at hγlo hε' ⊢
  unfold winTop winBot deltaStarIIa
  refine admitsPartition₂_of_total_le (le_trans htot ?_) ?_
  · norm_num
    linarith
  · norm_num
    linarith

/-- **Condition (B) does not cover the top of the Type IIa range.** At `γ = 1/2` and zero retreat,
the capacity the extraction needs for its second block is strictly smaller than the one condition
(B) supplies — so a partition witnessing (B) need not witness what the route asks for.

The required value is `1/2 - a(1/2) = 33521.../10⁶ ≈ 0.033521`; condition (B) gives
`1/14 - 24ω/7 - 2ϵ ≈ 0.049143`. -/
theorem conditionB_insufficient_at_half :
    1 / 2 - winBot (1 / 2) (deltaStarIIa (1 / 2) ((ω : ℚ) : ℝ) ((ϵ : ℚ) : ℝ)) 0 ((δ : ℚ) : ℝ)
      < 1 / 14 - 24 * ((ω : ℚ) : ℝ) / 7 - 2 * ((ϵ : ℚ) : ℝ) := by
  have hd : ((δ : ℚ) : ℝ) = 179 / 10000 := cast_δ
  have hw : ((ω : ℚ) : ℝ) = 13 / 2000 := cast_ω
  have he : ((ϵ : ℚ) : ℝ) = 1 / 10 ^ 10 := cast_ϵ
  rw [hd, hw, he]
  unfold winBot deltaStarIIa
  norm_num

/-! ## Type IIb -/

/-- **The Type IIb route's packing condition, uniformly in `γ`**, as a two-block partition at
Point A.

Its range is
`[1/3 + 8ω + 7δ/3 + 3ϵ, 2/5 + 24ω/5 + 7δ/5 + 2ϵ]`, and here both required capacities are
comfortable throughout: at least `0.4271` and at least `0.0679`. -/
theorem typeIIb_packing {m m' : ℕ} {y : Fin (m + m') → ℝ} {γ ε' : ℝ}
    (hγlo : 1 / 3 + 8 * ((ω : ℚ) : ℝ) + 7 * ((δ : ℚ) : ℝ) / 3 + 3 * ((ϵ : ℚ) : ℝ) ≤ γ)
    (hγhi : γ ≤ 2 / 5 + 24 * ((ω : ℚ) : ℝ) / 5 + 7 * ((δ : ℚ) : ℝ) / 5 + 2 * ((ϵ : ℚ) : ℝ))
    (hε'0 : 0 ≤ ε') (hε' : ε' ≤ ((ϵ : ℚ) : ℝ))
    (hy : y ∈ Xi (Bcap m) (Bcap m') m m' (((δ : ℚ) : ℝ))) :
    AdmitsPartition₂ y
      (winTop γ (deltaStarIIb γ ((ω : ℚ) : ℝ) ((ϵ : ℚ) : ℝ)) ε' ((δ : ℚ) : ℝ))
      (1 / 2 - winBot γ (deltaStarIIb γ ((ω : ℚ) : ℝ) ((ϵ : ℚ) : ℝ)) ε' ((δ : ℚ) : ℝ)) := by
  have hd : ((δ : ℚ) : ℝ) = 179 / 10000 := cast_δ
  have hw : ((ω : ℚ) : ℝ) = 13 / 2000 := cast_ω
  have he : ((ϵ : ℚ) : ℝ) = 1 / 10 ^ 10 := cast_ϵ
  have htot : ∑ i, y i ≤ 17 / 50 := total_le_pointA hy
  simp only [hd, hw, he] at hγlo hγhi hε' ⊢
  unfold winTop winBot deltaStarIIb
  refine admitsPartition₂_of_total_le (le_trans htot ?_) ?_
  · norm_num
    linarith
  · norm_num
    linarith

end Gap212.Routing
