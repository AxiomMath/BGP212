/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public meta import Gap212.Attr

/-!
# The Type IIc walls, windows and capacities

The Type IIc estimate carries three strict parameter inequalities rather than the one or two the
other types carry, and the level it is invoked at is `δ` itself rather than a `γ`-dependent width.
This module records the three walls, the relations among the four retreated windows, and the four
bin capacities those windows produce.

Everything here is affine arithmetic over an ordered field, closed by `linarith`/`nlinarith`. The
mathematical content sits in the choice of windows, which is made elsewhere; what these lemmas do
is verify that the choice clears the walls and that the capacities come out as the packing
argument expects.

## Why the level is chosen rather than substituted

[2] replaces `δ*` by `δ` at this point and reads it as monotonicity. It is not: the first
bin's capacity `γ - 2δ* - 8ω₀` *decreases* in `δ*` while the third's `4ω₀ + δ*` increases, so a
smaller `δ*` weakens one and strengthens the other. The step is sound only as a *choice* of
`δ* = δ`, which is what the admissibility bounds license, and that is how it is stated here.

## Main results

* `Gap212.Walls.typeIIc_wall_first`, `_second`, `_third`: the three walls hold at an admissible
  level.
* `Gap212.Walls.typeIIc_window_relations`: the four windows satisfy what four-factor extraction
  needs.
* `Gap212.Walls.typeIIc_capacities`: the four bin capacities, computed.
-/

@[expose] public section

namespace Gap212.Walls

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **The first Type IIc wall.** An admissible level clears `8ω + 4δ* + 2γ < 1`, with margin
`4ε`. -/
@[gap212 "lem_typeIIc_analytic_first"]
theorem typeIIc_wall_first {ω γ δs ε : 𝕜} (hε : 0 < ε)
    (h : δs ≤ 1 / 4 - 2 * ω - γ / 2 - ε) :
    8 * ω + 4 * δs + 2 * γ < 1 := by
  nlinarith [h, hε]

/-- **The second Type IIc wall.** An admissible level clears `32ω + 10δ* - γ < 0`, with margin
`10ε`. -/
@[gap212 "lem_typeIIc_analytic_second"]
theorem typeIIc_wall_second {ω γ δs ε : 𝕜} (hε : 0 < ε)
    (h : δs ≤ γ / 10 - 32 * ω / 10 - ε) :
    32 * ω + 10 * δs - γ < 0 := by
  nlinarith [h, hε]

/-- **The third Type IIc wall.** An admissible level clears `48ω + 16δ* - 4γ < -1`, with margin
`16ε`. This is the wall the other types have no analogue of, and the one that confines Type IIc to
the nonnegative-level range. -/
@[gap212 "lem_typeIIc_analytic_third"]
theorem typeIIc_wall_third {ω γ δs ε : 𝕜} (hε : 0 < ε)
    (h : δs ≤ γ / 4 - 1 / 16 - 3 * ω - ε) :
    48 * ω + 16 * δs - 4 * γ < -1 := by
  nlinarith [h, hε]

/-- **The four retreated Type IIc windows satisfy what four-factor extraction needs.** All four
have the same width `d`, which gives `3(b₁ - a₁) + (a₃ - b₃) = 2d ≥ 0` and `b₁ - b₂ = a₁ - a₂`
exactly. Those two are the hypotheses the four-factor lemma cannot do without. -/
@[gap212 "lem_typeIIc_windows"]
theorem typeIIc_window_relations {γ ω₀ d ε' : 𝕜} (hd : 0 ≤ d) :
    let b₁ := γ - 3 * ε'
    let a₁ := b₁ - d
    let b₂ := 1 / 2 - γ - 2 * ω₀ - 6 * ε'
    let a₂ := b₂ - d
    let b₃ := -γ - 52 * ε' - 8 * ω₀
    let a₃ := b₃ - d
    0 ≤ 3 * (b₁ - a₁) + (a₃ - b₃) ∧ b₁ - b₂ = a₁ - a₂ ∧
      b₁ - a₁ = d ∧ b₂ - a₂ = d ∧ b₃ - a₃ = d := by
  intro b₁ a₁ b₂ a₂ b₃ a₃
  refine ⟨by simp only [a₁, a₃]; nlinarith [hd], ?_, ?_, ?_, ?_⟩ <;>
    simp only [a₁, a₂, a₃, b₁, b₂, b₃] <;> ring

/-- **The four Type IIc bin capacities.** Substituting the retreated windows into the four-factor
capacities gives `γ - 2d - 8ω₀ - 58ε'`, `1/2 - γ - 2ω₀ - 6ε'`, `4ω₀ + d + 9ε'` and
`8ω₀ + 55ε'`. As `ε' → 0` these are exactly the four bounds Condition D carries. -/
@[gap212 "lem_typeIIc_capacities"]
theorem typeIIc_capacities (γ ω₀ d ε' : 𝕜) :
    let b₁ := γ - 3 * ε'
    let a₁ := b₁ - d
    let b₂ := 1 / 2 - γ - 2 * ω₀ - 6 * ε'
    let a₂ := b₂ - d
    let b₃ := -γ - 52 * ε' - 8 * ω₀
    let a₃ := b₃ - d
    2 * a₁ + b₃ = γ - 2 * d - 8 * ω₀ - 58 * ε' ∧
      b₂ = 1 / 2 - γ - 2 * ω₀ - 6 * ε' ∧
      (1 / 2 + 2 * ω₀) - b₁ - a₂ = 4 * ω₀ + d + 9 * ε' ∧
      a₁ - 2 * b₁ - a₃ = 8 * ω₀ + 55 * ε' := by
  intro b₁ a₁ b₂ a₂ b₃ a₃
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [a₁, a₂, a₃, b₁, b₂, b₃] <;> ring

/-- **The level `δ` is admissible for the first wall.** Under the first Type II scalar
condition of [2, Proposition 3], and with `γ` in the Type IIc range, `δ` satisfies the first wall's
premise.

Stated as an implication between explicit affine inequalities so it can be discharged at the
chosen datum by rational arithmetic. -/
@[gap212 "lem_delta_typeIIc_first"]
theorem delta_typeIIc_first {ω γ δ ε : 𝕜}
    (h : δ + 2 * ω + γ / 2 + ε ≤ 1 / 4) :
    δ ≤ 1 / 4 - 2 * ω - γ / 2 - ε := by linarith

/-- **The level `δ` is admissible for the two cap walls.** Under the cap conditions of [2,
Proposition 3], `δ` satisfies both remaining premises. -/
@[gap212 "lem_delta_typeIIc_caps"]
theorem delta_typeIIc_caps {ω γ δ ε : 𝕜}
    (h₁ : δ + 32 * ω / 10 + ε ≤ γ / 10)
    (h₂ : δ + 1 / 16 + 3 * ω + ε ≤ γ / 4) :
    δ ≤ γ / 10 - 32 * ω / 10 - ε ∧ δ ≤ γ / 4 - 1 / 16 - 3 * ω - ε :=
  ⟨by linarith, by linarith⟩

/-- **The Type III window capacities.** With the level `δ*_III = 1/2 - 7ω/2 - 9ξ₃/8 - 2ε`
and the window `(a, b)` of width `δ*_III` around `1/3 + 4δ*_III/3 - 4ω/3`, the two capacities the
two-factor extraction needs come out as `1 - 6ω - 3ξ₃/2 - 8ε/3` and `5ω/2 + 3ξ₃/8 + 2ε/3`.

The `ε`-coefficients are `8/3` and `2/3`, not the `4/3` and `1/3` that the width displayed in [2]
would give: `δ*_III` carries `2ε` where that width carries `ε`, and that propagates here. -/
@[gap212 "lem_typeIII_window_capacities"]
theorem typeIII_window_capacities (ω ξ₃ ε : 𝕜) :
    let δs := 1 / 2 - 7 * ω / 2 - 9 * ξ₃ / 8 - 2 * ε
    let b := 1 / 3 + 4 * δs / 3 - 4 * ω / 3
    let a := b - δs
    b = 1 - 6 * ω - 3 * ξ₃ / 2 - 8 * ε / 3 ∧
      1 / 2 - a = 5 * ω / 2 + 3 * ξ₃ / 8 + 2 * ε / 3 := by
  intro δs b a
  refine ⟨?_, ?_⟩ <;> simp only [a, b, δs] <;> ring

end Gap212.Walls
