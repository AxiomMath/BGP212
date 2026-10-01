/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.TypeI
public meta import Gap212.Attr

/-!
# The window widths of the six routes, and the walls they must clear

Each route of the routing argument picks a divisor-window width `δ*(γ)` and applies its estimate at
`(ω, γ, δ) = (ω_max, γ, δ*(γ))`. Two things then have to be checked: the estimate's own parameter
inequalities — its *walls* — and `δ*(γ) ≥ δ`, which is what the factor-extraction lemmas need. This
module does both, for Type IIa, Type IIb and Type III. Type I's two widths are in
`Gap212.Packing.TypeI`.

## Every first wall is an identity

As with Type I, the choices are not merely sufficient but *exactly* saturating:

    Type IIa:  24ω + 7δ*(γ) - 5γ = -2 - 7e
    Type IIb:  24ω + 7δ*(γ) - 3γ = -1 - 7e

Neither depends on `γ` or `ω`. So each width is the largest the estimate permits, with the margin
spent being exactly `7e`. The second wall of each is a genuine inequality rather than an identity,
and both hold comfortably for `γ ≤ 1/2` — which is all that is needed, since Type II's `α ↔ β` swap
brings `γ` below `1/2`.

## The Type III width does not clear its wall as displayed

Substituting the width `δ*(γ) = 1/2 - (7/2)ω_max - (9/8)ξ₃ - ϵ` displayed in [2] into the
hypothesis `28ω + 9γ + 8δ < 4` of [2, Lemma 7] gives

    28ω + 9γ + 8δ*(γ) = 4 + 9(γ - ξ₃) - 8ϵ,

so the wall demands `9(γ - ξ₃) < 8ϵ`. But the Type III class of [2, Definition 9] admits scales up
to `x^{ξ₃ + ϵ}`, so `γ` can be `ξ₃ + ϵ`, and the left side is then `9ϵ`. The wall fails, by `ϵ`.
`Gap212.Routing.typeIII_wall_fails_as_printed` records this.

Carrying `-2ϵ` instead clears it with margin `7ϵ`, and condition (III) of [2, Proposition 3] is
*already* stated for that corrected width: `11/8 - (7/2)A_n - (9/8)ξ₃ - 2ϵ` equals
`δ*(γ)` with `-2ϵ` exactly, once `A_n = ω_max + 1/4` (`conditionIII_eq_deltaStarIII'`). So the `-ϵ`
in the displayed width is an `ϵ`-bookkeeping slip against the condition of [2], and
the correction costs nothing: at Point A the width is still `109/4000 - 2ϵ ≈ 0.02725`, comfortably
above `δ = 0.0179`.

This is the same species of slip as the `+100ϵ` in condition (II), and like it, it does not
threaten the result.

## The `γ` thresholds are those of [2], with room

`δ*(γ) ≥ δ` cuts each route's `γ`-range. The exact thresholds are `2/5 + 24ω/5 + 7δ/5 + 7ϵ/5` for
Type IIa and `1/3 + 8ω + 7δ/3 + 7ϵ/3` for Type IIb; the source uses `+2ϵ` and `+3ϵ`, both of which
are *stronger*, hence safe. Recorded below so the routing can quote either.

## Main results

* `Gap212.Routing.typeIIa_wall₁`, `typeIIb_wall₁`: the saturating identities.
* `Gap212.Routing.typeIIa_wall₂`, `typeIIb_wall₂`: the second walls, for `γ ≤ 1/2`.
* `Gap212.Routing.typeIII_wall_fails_as_printed`: the failure, as a theorem.
* `Gap212.Routing.typeIII_wall_ok`: the corrected width clears the wall.
* `Gap212.Routing.conditionIII_eq_deltaStarIII'`: condition (III) is the corrected width.
* `Gap212.Routing.deltaStarIIa_ge_delta`, `deltaStarIIb_ge_delta`, `deltaStarIII'_ge_delta`.
-/

@[expose] public section

namespace Gap212.Routing

open Gap212.PointA Gap212.Packing

section Walls

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ## Type IIa -/

/-- The Type IIa window width, `δ*(γ) = 5γ/7 - 2/7 - 24ω/7 - e`. -/
@[gap212 "def_delta_star_typeIIa"]
def deltaStarIIa (γ ω e : 𝕜) : 𝕜 := 5 * γ / 7 - 2 / 7 - 24 * ω / 7 - e

/-- **Type IIa's first wall is an identity**: the `24ω + 7δ - 5γ < -2` of [2, Lemma 3] becomes
`-2 - 7e`, independently of `γ` and `ω`. -/
@[gap212 "lem_typeIIa_analytic_first"]
theorem typeIIa_wall₁ (γ ω e : 𝕜) :
    24 * ω + 7 * deltaStarIIa γ ω e - 5 * γ = -2 - 7 * e := by
  unfold deltaStarIIa; ring

/-- **Type IIa's second wall**, `8ω + 3δ - γ < 0`, holds for `γ ≤ 1/2` and `ω ≥ 0`. Unlike the
first it is a genuine inequality; at `γ = 1/2` the value is `-2/7 - 16ω/7 - 3e`. -/
@[gap212 "lem_typeIIa_analytic_second"]
theorem typeIIa_wall₂ {γ ω e : 𝕜} (hγ : γ ≤ 1 / 2) (hω : 0 ≤ ω) (he : 0 < e) :
    8 * ω + 3 * deltaStarIIa γ ω e - γ < 0 := by
  unfold deltaStarIIa
  have : 8 * ω + 3 * (5 * γ / 7 - 2 / 7 - 24 * ω / 7 - e) - γ
      = 8 * γ / 7 - 16 * ω / 7 - 6 / 7 - 3 * e := by ring
  rw [this]
  linarith

/-! ## Type IIb -/

/-- The Type IIb window width, `δ*(γ) = 3γ/7 - 1/7 - 24ω/7 - e`. -/
@[gap212 "def_delta_star_typeIIb"]
def deltaStarIIb (γ ω e : 𝕜) : 𝕜 := 3 * γ / 7 - 1 / 7 - 24 * ω / 7 - e

/-- **Type IIb's first wall is an identity**: the `24ω + 7δ - 3γ < -1` of [2, Lemma 4] becomes
`-1 - 7e`. -/
@[gap212 "lem_typeIIb_analytic_first"]
theorem typeIIb_wall₁ (γ ω e : 𝕜) :
    24 * ω + 7 * deltaStarIIb γ ω e - 3 * γ = -1 - 7 * e := by
  unfold deltaStarIIb; ring

/-- **Type IIb's second wall**, `8ω + 3δ - γ < 0`, for `γ ≤ 1/2` and `ω ≥ 0`. -/
@[gap212 "lem_typeIIb_analytic_second"]
theorem typeIIb_wall₂ {γ ω e : 𝕜} (hγ : γ ≤ 1 / 2) (hω : 0 ≤ ω) (he : 0 < e) :
    8 * ω + 3 * deltaStarIIb γ ω e - γ < 0 := by
  unfold deltaStarIIb
  have : 8 * ω + 3 * (3 * γ / 7 - 1 / 7 - 24 * ω / 7 - e) - γ
      = 2 * γ / 7 - 16 * ω / 7 - 3 / 7 - 3 * e := by ring
  rw [this]
  linarith

/-! ## Type III, and the wall it does not clear -/

/-- The Type III window width **as displayed in [2]**, `δ* = 1/2 - (7/2)ω - (9/8)ξ₃ - e`. -/
def deltaStarIII (ω ξ₃ e : 𝕜) : 𝕜 := 1 / 2 - 7 * ω / 2 - 9 * ξ₃ / 8 - e

/-- The Type III window width **corrected**, carrying `-2e`. -/
@[gap212 "def_delta_star_typeIII"]
def deltaStarIII' (ω ξ₃ e : 𝕜) : 𝕜 := 1 / 2 - 7 * ω / 2 - 9 * ξ₃ / 8 - 2 * e

/-- Substituting the displayed width into the wall of [2, Lemma 7], `28ω + 9γ + 8δ < 4` leaves
`4 + 9(γ - ξ₃) - 8e`. Note that `ω` cancels entirely. -/
theorem typeIII_wall_eq (γ ω ξ₃ e : 𝕜) :
    28 * ω + 9 * γ + 8 * deltaStarIII ω ξ₃ e = 4 + 9 * (γ - ξ₃) - 8 * e := by
  unfold deltaStarIII; ring

/-- **The displayed width fails the wall.** At the top of the Type III range, `γ = ξ₃ + e`, the
displayed width *violates* the wall of [2, Lemma 7]: the left side is `4 + e`. The Type III class
of [2, Definition 9] does admit this `γ`, since it bounds the scales by `x^{ξ₃ + ϵ}`. -/
theorem typeIII_wall_fails_as_printed {ω ξ₃ e : 𝕜} (he : 0 < e) :
    4 < 28 * ω + 9 * (ξ₃ + e) + 8 * deltaStarIII ω ξ₃ e := by
  rw [typeIII_wall_eq]
  linarith

/-- **The corrected width clears the wall**, with margin `7e` at the top of the range. -/
@[gap212 "lem_typeIII_analytic"]
theorem typeIII_wall_ok {γ ω ξ₃ e : 𝕜} (hγ : γ ≤ ξ₃ + e) (he : 0 < e) :
    28 * ω + 9 * γ + 8 * deltaStarIII' ω ξ₃ e < 4 := by
  unfold deltaStarIII'
  have : 28 * ω + 9 * γ + 8 * (1 / 2 - 7 * ω / 2 - 9 * ξ₃ / 8 - 2 * e)
      = 4 + 9 * (γ - ξ₃) - 16 * e := by ring
  rw [this]
  linarith

/-- **Condition (III) of [2, Proposition 3] is the corrected width.** With `A_n = ω + 1/4`, the
condition `11/8 - (7/2)A_n - (9/8)ξ₃ - 2ϵ` equals `δ*` carrying `-2e` — not the `-e` of the
displayed width. So the condition of [2] already assumes the correction. -/
theorem conditionIII_eq_deltaStarIII' (ω ξ₃ e : 𝕜) :
    11 / 8 - 7 * (ω + 1 / 4) / 2 - 9 * ξ₃ / 8 - 2 * e = deltaStarIII' ω ξ₃ e := by
  unfold deltaStarIII'; ring

end Walls

/-! ## The `γ` thresholds, and the widths at Point A

`δ*(γ) ≥ δ` is what the extraction lemmas need, and it is what cuts each route's `γ`-range. -/

/-- Type IIa's exact `γ` threshold. The source uses `+2ϵ` in place of `+7ϵ/5`, which is stronger
and therefore safe. -/
@[gap212 "lem_delta_star_typeIIa_ge_delta"]
theorem deltaStarIIa_ge_delta {γ : ℚ} (hγ : 2 / 5 + 24 * ω / 5 + 7 * δ / 5 + 7 * ϵ / 5 ≤ γ) :
    δ ≤ deltaStarIIa γ ω ϵ := by
  unfold deltaStarIIa
  rw [show (ω : ℚ) = 13 / 2000 from rfl, show (δ : ℚ) = 179 / 10000 from rfl,
    show (ϵ : ℚ) = 1 / 10 ^ 10 from rfl] at *
  linarith

/-- Type IIb's exact `γ` threshold. The source uses `+3ϵ` in place of `+7ϵ/3` — again stronger. -/
@[gap212 "lem_delta_star_typeIIb_ge_delta"]
theorem deltaStarIIb_ge_delta {γ : ℚ} (hγ : 1 / 3 + 8 * ω + 7 * δ / 3 + 7 * ϵ / 3 ≤ γ) :
    δ ≤ deltaStarIIb γ ω ϵ := by
  unfold deltaStarIIb
  rw [show (ω : ℚ) = 13 / 2000 from rfl, show (δ : ℚ) = 179 / 10000 from rfl,
    show (ϵ : ℚ) = 1 / 10 ^ 10 from rfl] at *
  linarith

/-- The corrected Type III width at Point A is `109/4000 - 2ϵ`, independent of `γ`. -/
theorem deltaStarIII'_pointA : deltaStarIII' ω ξ₃ ϵ = 109 / 4000 - 2 * ϵ := by
  unfold deltaStarIII'
  rw [show (ω : ℚ) = 13 / 2000 from rfl, show (ξ₃ : ℚ) = 2 / 5 from rfl]
  ring

/-- **The correction costs nothing at Point A**: the width still exceeds `δ`, with margin
`46749999/5000000000 ≈ 0.00935`. -/
@[gap212 "lem_delta_star_typeIII_ge_delta"]
theorem deltaStarIII'_ge_delta : δ ≤ deltaStarIII' ω ξ₃ ϵ := by
  rw [deltaStarIII'_pointA]
  norm_num [δ, ϵ]

/-- The margin, exactly. -/
theorem deltaStarIII'_slack : deltaStarIII' ω ξ₃ ϵ - δ = 46749999 / 5000000000 := by
  rw [deltaStarIII'_pointA]
  norm_num [δ, ϵ]

end Gap212.Routing
