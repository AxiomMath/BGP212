/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.RoutePacking
public meta import Gap212.Attr

/-!
# The Type IIb capacities at their worst values

The three Type IIb bin capacities are bounded from below on the `γ`-range the route runs over. By
`Gap212.Routing.typeIIb_capacities` those capacities are, in the limit `ε' → 0`, the affine
functions `γ`, `1/2 - γ - 2ω(j,j')` and `3γ/7 - 1/7 - 10ω(j,j')/7 - ϵ`, so the bound is a statement
about three affine functions of `γ` and nothing more. That is what is proved here, in symbolic
`ω`, `δ` and `ϵ`.

The third bound is attained exactly, which is worth recording because it is what makes the range's
left endpoint the right one: at `γ = 1/3 + 8ω + 7δ/3 + 3ϵ`,

    3γ/7 - 1/7 - 10ω/7 - ϵ = 1/7 + 24ω/7 + δ + 9ϵ/7 - 1/7 - 10ω/7 - ϵ = 2ω + δ + 2ϵ/7,

which is the minimum over the range. The first bound has slack `7ϵ` and the second `2ϵ`.

## Main results

* `Gap212.Routing.typeIIb_worst_values`: the three lower bounds, on the route's `γ`-range.
* `Gap212.Routing.monotone_capIIb_third`: the third capacity increases in `γ`, which is the clause
  that makes "minimum at the left endpoint" meaningful.
-/

@[expose] public section

namespace Gap212.Routing

/-- **The third IIb capacity increases in `γ`.** Its `γ`-coefficient is `3/7 > 0`, which is what
makes evaluating at the range's left endpoint give the minimum. -/
theorem monotone_capIIb_third (ω ϵ : ℝ) :
    Monotone (fun γ : ℝ ↦ 3 * γ / 7 - 1 / 7 - 10 * ω / 7 - ϵ) := by
  intro a b hab
  dsimp only
  linarith

/-- **The IIb capacities at their worst values.** On
`1/3 + 8ω + 7δ/3 + 3ϵ ≤ γ ≤ 2/5 + 24ω/5 + 7δ/5 + 2ϵ`, the three capacities of
`Gap212.Routing.typeIIb_capacities` — which are `γ`, `1/2 - γ - 2ω` and
`3γ/7 - 1/7 - 10ω/7 - ϵ` in the limit `ε' → 0` — are at least `1/3 + 8ω + 7δ/3 - 4ϵ`,
`1/10 - 34ω/5 - 7δ/5 - 4ϵ` and `2ω + δ + 2ϵ/7` respectively.

The third is attained with equality at the left endpoint; the first carries slack `7ϵ` and the
second `2ϵ`, so only the third constrains the range. No hypothesis on `ω` or `δ` is needed, and
`ϵ ≥ 0` is used only for the first two bounds. -/
@[gap212 "lem_typeIIb_worst_values"]
theorem typeIIb_worst_values {γ ω δ ϵ : ℝ} (hϵ : 0 ≤ ϵ)
    (hlo : 1 / 3 + 8 * ω + 7 * δ / 3 + 3 * ϵ ≤ γ)
    (hhi : γ ≤ 2 / 5 + 24 * ω / 5 + 7 * δ / 5 + 2 * ϵ) :
    1 / 3 + 8 * ω + 7 * δ / 3 - 4 * ϵ ≤ γ ∧
      1 / 10 - 34 * ω / 5 - 7 * δ / 5 - 4 * ϵ ≤ 1 / 2 - γ - 2 * ω ∧
      2 * ω + δ + 2 * ϵ / 7 ≤ 3 * γ / 7 - 1 / 7 - 10 * ω / 7 - ϵ :=
  ⟨by linarith, by linarith, by linarith⟩

/-! ## The capacities themselves

The three capacities are named below and evaluated in the limit `ε' → 0`. The identity is proved
as an exact identity in `ε'`, which is stronger: the limit is the `ε' = 0` case. -/

/-- **The IIb bin capacities.** With `b₁ = γ - 3ε'`, `b₂ = 1/2 - γ - 2ω - 6ε'` and
`a₂ = b₂ - δ*_IIb(γ)`, the three capacities of the two-block partition — namely `b₁`, `b₂` and
`1/2 - b₁ - a₂` — are

    γ - 3ε',   1/2 - γ - 2ω - 6ε',   and   3γ/7 - 1/7 - 10ω/7 - ϵ + 9ε',

so in the limit `ε' → 0` they are `γ`, `1/2 - γ - 2ω` and `3γ/7 - 1/7 - 10ω/7 - ϵ`, which is the
form the route uses. Stating the exact `ε'`-dependence rather than only the limit is a
strengthening, and it is what `Gap212.Routing.typeIIb_worst_values` then bounds below.

The third value is where `δ*_IIb` enters: `1/2 - b₁ - a₂ = 2ω + 9ε' + δ*_IIb(γ)`, and
`δ*_IIb(γ) = 3γ/7 - 1/7 - 24ω/7 - ϵ` turns `2ω + δ*_IIb(γ)` into `3γ/7 - 1/7 - 10ω/7 - ϵ` because
`14ω/7 - 24ω/7 = -10ω/7`. That the two agree on the nose is the content.

The variables here are the bare endpoints `b₁`, `a₁`, `b₂`, `a₂`, not `Gap212.Routing.winTop` and
`Gap212.Routing.winBot`, which carry the inward inset `(δ* - δ)/2` at each end. -/
@[gap212 "lem_typeIIb_capacities"]
theorem typeIIb_capacities {γ ω ϵ ε' b₁ b₂ a₂ : ℝ} (hb₁ : b₁ = γ - 3 * ε')
    (hb₂ : b₂ = 1 / 2 - γ - 2 * ω - 6 * ε') (ha₂ : a₂ = b₂ - deltaStarIIb γ ω ϵ) :
    b₁ = γ - 3 * ε' ∧ b₂ = 1 / 2 - γ - 2 * ω - 6 * ε' ∧
      1 / 2 - b₁ - a₂ = 3 * γ / 7 - 1 / 7 - 10 * ω / 7 - ϵ + 9 * ε' := by
  refine ⟨hb₁, hb₂, ?_⟩
  subst hb₁; subst hb₂; subst ha₂
  unfold deltaStarIIb
  ring

end Gap212.Routing
