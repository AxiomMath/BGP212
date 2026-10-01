/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.Containment
public import Gap212.Routing.PointABridge
public meta import Gap212.Attr

/-!
# The Type IIa route, discharged at Point A

The containment `Q ⊆ D_IIa` with every hypothesis supplied from the Point A parameter datum. This
is one of the six routes of the routing argument.

## The width is fixed, not `γ`-dependent

`Gap212.HasEquidistributionFamily` takes a *set* `G` of `γ`-values and a *single* `δ`, because the
sequences it is applied to have `N(x) = x^{γ(x)}` with `γ` varying in `x`. So a route cannot use
`δ*(γ)` pointwise; it must pick one width valid across its whole range. Since Type IIa's first wall
`24ω + 7δ - 5γ < -2` only gets easier as `γ` grows, the width to pick is the one at the *bottom* of
its range — `Gap212.Routing.widthIIa`.

That width is `δ + 3ϵ/7`, exceeding the support's threshold `δ` by `3ϵ/7 ≈ 4.3 × 10⁻¹¹`. Thin, but
the extraction needs only `δ < δ*`, and this is the margin the source's `+2ϵ` in the `γ`-threshold
buys — it is the reason that threshold is `+2ϵ` and not `+ϵ`.

## What the route needs, and where each piece comes from

* the level — `omegaMax_eq_ω`: `(A_j + A_{j'})/2 - 1/4 = ω`, so the containment's level and the
  packing conditions' `ω` are the same number;
* the packing condition — the trivial partition, via `total_le_pointA`: the first capacity exceeds
  `17/50` throughout the range;
* the rough caps — `gap212Params_B_le_one`;
* the mixed caps — `gap212Params_A_add`, whose sum is Point A's `ϑ = 513/1000`.

## Main results

* `Gap212.Routing.widthIIa`: the route's fixed width, and `widthIIa_gt_δ`.
* `Gap212.Routing.mem_moduliIIa_pointA`: the containment, parameterized in the width.
* `Gap212.Routing.mem_moduliIIa_route`: the containment at `widthIIa`, hypotheses reduced to
  `γ ∈ [γ_low, 1/2]` and `0 ≤ ε' ≤ ϵ`.
-/

@[expose] public section

namespace Gap212.Routing

open Gap212.PointA Gap212.Packing

/-! ## The containment, parameterized in the width -/

/-- **`Q ⊆ D_IIa` at Point A.** Every hypothesis of `mem_moduliIIa_of_qgen` about the support is
discharged from the parameter datum; what remains is the two capacity inequalities and the
positivity of the window's lower end, all numeric. -/
theorem mem_moduliIIa_pointA {x ε₀ γ δstar ε' : ℝ} {j j' : Fin gap212ParamsPointA.n}
    {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hδstar : gap212ParamsPointA.δ < δstar)
    (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hcap₁ : (17 / 50 : ℝ) ≤ γ - 3 * ε' - (δstar - gap212ParamsPointA.δ) / 2)
    (hcap₂ : (0 : ℝ) ≤ 1 / 2 - (γ - 3 * ε' - δstar + (δstar - gap212ParamsPointA.δ) / 2))
    (hlow : 0 < γ - 3 * ε' - δstar + (δstar - gap212ParamsPointA.δ) / 2)
    (hq : q ∈ Qgen gap212ParamsPointA x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ * (1 / 2 - (γ - 3 * ε' - δstar + (δstar - gap212ParamsPointA.δ) / 2)))
      ≤ (q : ℝ)) :
    q ∈ moduliIIaFamily x (((ω : ℚ) : ℝ)) γ δstar ε' := by
  rw [← omegaMax_eq_ω j j']
  refine mem_moduliIIa_of_qgen hx gap212Params_δ_pos hε₀ hε₀1 hδstar
    (gap212Params_A_add j j') hlow (gap212Params_B_le_one j m) (gap212Params_B_le_one j' m')
    (fun y hy ↦ ?_) hq hqbig
  rw [gap212Params_Xi j j' hm hm'] at hy
  exact admitsPartition₂_of_total_le ((total_le_pointA hy).trans hcap₁) hcap₂

/-! ## The route's fixed width -/

/-- The bottom of the Type IIa `γ`-range, as the source states it (`+2ϵ`). -/
noncomputable def gammaLoIIa : ℝ :=
  2 / 5 + 24 * ((ω : ℚ) : ℝ) / 5 + 7 * ((δ : ℚ) : ℝ) / 5 + 2 * ((ϵ : ℚ) : ℝ)

/-- **The Type IIa route's width**: `δ*(γ)` evaluated at the bottom of the range, which is the
smallest over the range and hence the one that clears the estimate's walls throughout. -/
noncomputable def widthIIa : ℝ := deltaStarIIa gammaLoIIa ((ω : ℚ) : ℝ) ((ϵ : ℚ) : ℝ)

/-- The width is `δ + 3ϵ/7`, exactly. -/
theorem widthIIa_eq : widthIIa = ((δ : ℚ) : ℝ) + 3 * ((ϵ : ℚ) : ℝ) / 7 := by
  unfold widthIIa gammaLoIIa deltaStarIIa
  ring

/-- **The width exceeds the support's threshold**, by `3ϵ/7`. This is what the source's `+2ϵ` in
the `γ`-threshold buys; with `+ϵ` the margin would vanish. -/
theorem widthIIa_gt_δ : gap212ParamsPointA.δ < widthIIa := by
  rw [widthIIa_eq, gap212Params_δ, cast_ϵ]
  norm_num

/-! ## The route -/

/-- **The Type IIa route.** At the fixed width `widthIIa`, the containment holds for every `γ` in
the route's range and every retreat `ε' ≤ ϵ`, with no numeric side conditions left for the caller.

The three capacity facts are discharged inside: the first capacity is at least `0.4562` (against
`17/50 = 0.34`), the second at least `0.0179`, and the window's lower end at least `0.438`. -/
theorem mem_moduliIIa_route {x ε₀ γ ε' : ℝ} {j j' : Fin gap212ParamsPointA.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hγlo : gammaLoIIa ≤ γ) (hγhi : γ ≤ 1 / 2)
    (hε'0 : 0 ≤ ε') (hε' : ε' ≤ ((ϵ : ℚ) : ℝ))
    (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hq : q ∈ Qgen gap212ParamsPointA x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ *
        (1 / 2 - (γ - 3 * ε' - widthIIa + (widthIIa - gap212ParamsPointA.δ) / 2)))
      ≤ (q : ℝ)) :
    q ∈ moduliIIaFamily x (((ω : ℚ) : ℝ)) γ widthIIa ε' := by
  rw [gammaLoIIa, cast_δ, cast_ω, cast_ϵ] at hγlo
  rw [cast_ϵ] at hε'
  refine mem_moduliIIa_pointA hx hε₀ hε₀1 widthIIa_gt_δ hm hm' ?_ ?_ ?_ hq hqbig <;>
    rw [widthIIa_eq, gap212Params_δ, cast_δ, cast_ϵ] <;> norm_num <;> linarith

end Gap212.Routing
