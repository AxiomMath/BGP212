/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.TypeIIaRoute
public meta import Gap212.Attr

/-!
# The Type I and Type III routes, discharged at Point A

This module gives the Type I routes — both `γ`-regimes —, the Type III route and the Type IIb
route at Point A. The Type IIa route is `Gap212.Routing.TypeIIaRoute`, and the Type IIc route,
whose moduli set asks for three nested divisors, is `Gap212.Routing.TypeIIcRoute`.

## `D_I` needed a containment of its own

`Gap212.Routing.Containment` builds the bridge for `D_IIa`, `D_IIb`, `D_IIc` and `D_III` — but
not for `D_I`, even though its first two branches use the same `HasDivisorIn` condition:
`Gap212.moduliIFamily` is defined by a two-fold `if` on `γ`, so membership needs the branch
resolved before `Finset.mem_filter` applies. Both branches are supplied here.

The first branch's window is `(γ - δ* - 3ε', γ - 3ε')`, literally `D_IIa`'s, so the proof is the
same. The second branch's is `(1 - γ - δ* - 3ε', 1 - γ - 3ε')`: the target sits near `x^{1-γ}`
rather than `x^γ`, so the extraction runs with `γ` replaced by `1 - γ`, and the capacities that
come out are the ones **condition (A′)** was introduced for.

## Both Type I regimes close by the trivial partition

At Point A the first capacity exceeds `17/50` in every regime, so everything goes into the first
block:

| route | width `δ*` | first capacity | second |
|---|---|---|---|
| Type I, `γ ≤ 1/2` | `0.029283 - 2ϵ` | `≥ 0.3829` | `≥ 0.0236` |
| Type I, `γ > 1/2` | `0.039857 - ϵ` | `≥ 0.4760` | `≥ 0.0199` |
| Type III | `0.027250 - 2ϵ` | `≥ 0.3563` | `≥ 0.1616` |

Worth noting for the second Type I regime: the required second capacity is about `0.0199`, while
condition (A′) supplies `0.0399`. So (A′) is, like condition (B) in `Gap212.Routing.RoutePacking`,
stated too generously to be quoted directly at the far end of its range. The trivial partition
covers it regardless.

## Main results

* `Gap212.Routing.mem_moduliI_of_qgen_le_half`, `mem_moduliI_of_qgen_gt_half`: the `D_I`
  containments.
* `Gap212.Routing.mem_moduliI_route_le_half`, `mem_moduliI_route_gt_half`: Type I at Point A.
* `Gap212.Routing.mem_moduliIII_route`: Type III at Point A.
-/

@[expose] public section

namespace Gap212.Routing

open Gap212.PointA Gap212.Packing Gap212.Extraction

/-! ## The two `D_I` containments -/

/-- **`Q ⊆ D_I` for `γ ≤ 1/2`.** The window is `D_IIa`'s, so this is `hasDivisorIn_of_qgen` with
the outer `if` resolved. -/
theorem mem_moduliI_of_qgen_le_half {p : SupportParams} {x ε₀ γ δstar ε' : ℝ}
    {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hδ : 0 < p.δ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hγ : γ ≤ 1 / 2)
    (hApos : 0 ≤ p.A j.succ + p.A j'.succ)
    (hlow : 0 < γ - 3 * ε' - δstar + (δstar - p.δ) / 2)
    (hδstar : p.δ < δstar)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hpack : ∀ y ∈ Xi (p.B j m) (p.B j' m') m m' p.δ,
      AdmitsPartition₂ y (γ - 3 * ε' - (δstar - p.δ) / 2)
        (1 / 2 - (γ - 3 * ε' - δstar + (δstar - p.δ) / 2)))
    (hq : q ∈ Qgen p x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ * (1 / 2 - (γ - 3 * ε' - δstar + (δstar - p.δ) / 2))) ≤ (q : ℝ)) :
    q ∈ moduliIFamily x ((p.A j.succ + p.A j'.succ) / 2 - 1 / 4) γ δstar ε' := by
  classical
  rw [moduliIFamily, if_pos hγ, Finset.mem_filter]
  exact ⟨mem_moduliRange_of_qgen hx hε₀ hApos hq, hasDivisorIn_of_qgen hx hδ hε₀ hε₀1 hlow
    (by linarith) (by linarith) (by linarith) hB hB' hpack hq hqbig⟩

/-- **`Q ⊆ D_I` for `1/2 < γ ≤ 1/2 + 2ω + ε'`.** Here the target window sits near `x^{1-γ}`, so the
extraction runs with `γ` replaced by `1 - γ`. -/
@[gap212 "lem_typeI_trivial_containment"]
theorem mem_moduliI_of_qgen_gt_half {p : SupportParams} {x ε₀ γ δstar ε' : ℝ}
    {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hδ : 0 < p.δ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hγ : ¬ (γ ≤ 1 / 2))
    (hγ' : γ ≤ 1 / 2 + 2 * ((p.A j.succ + p.A j'.succ) / 2 - 1 / 4) + ε')
    (hApos : 0 ≤ p.A j.succ + p.A j'.succ)
    (hlow : 0 < 1 - γ - 3 * ε' - δstar + (δstar - p.δ) / 2)
    (hδstar : p.δ < δstar)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hpack : ∀ y ∈ Xi (p.B j m) (p.B j' m') m m' p.δ,
      AdmitsPartition₂ y (1 - γ - 3 * ε' - (δstar - p.δ) / 2)
        (1 / 2 - (1 - γ - 3 * ε' - δstar + (δstar - p.δ) / 2)))
    (hq : q ∈ Qgen p x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ * (1 / 2 - (1 - γ - 3 * ε' - δstar + (δstar - p.δ) / 2)))
      ≤ (q : ℝ)) :
    q ∈ moduliIFamily x ((p.A j.succ + p.A j'.succ) / 2 - 1 / 4) γ δstar ε' := by
  classical
  rw [moduliIFamily, if_neg hγ, if_pos hγ', Finset.mem_filter]
  exact ⟨mem_moduliRange_of_qgen hx hε₀ hApos hq, hasDivisorIn_of_qgen hx hδ hε₀ hε₀1 hlow
    (by linarith) (by linarith) (by linarith) hB hB' hpack hq hqbig⟩

/-! ## Type I at Point A, first regime -/

/-- The bottom of the Type I range, `ξ₁ - ϵ`. -/
noncomputable def gammaLoI : ℝ := ((ξ₁ : ℚ) : ℝ) - ((ϵ : ℚ) : ℝ)

/-- The Type I first-regime width, at the bottom of the range. -/
noncomputable def widthI₁ : ℝ := deltaStarI₁ gammaLoI ((ω : ℚ) : ℝ) ((ϵ : ℚ) : ℝ)

/-- The width exceeds the threshold: `0.029283 - 2ϵ > 0.0179`. -/
theorem widthI₁_gt_δ : gap212ParamsPointA.δ < widthI₁ := by
  norm_num [widthI₁, gammaLoI, deltaStarI₁, gap212Params_δ, cast_δ, cast_ξ₁, cast_ω, cast_ϵ]

/-- **The Type I route, first regime.** For `γ ∈ [ξ₁ - ϵ, 1/2]` and `0 ≤ ε' ≤ ϵ`. -/
theorem mem_moduliI_route_le_half {x ε₀ γ ε' : ℝ} {j j' : Fin gap212ParamsPointA.n}
    {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hγlo : gammaLoI ≤ γ) (hγhi : γ ≤ 1 / 2)
    (hε'0 : 0 ≤ ε') (hε' : ε' ≤ ((ϵ : ℚ) : ℝ))
    (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hq : q ∈ Qgen gap212ParamsPointA x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ *
        (1 / 2 - (γ - 3 * ε' - widthI₁ + (widthI₁ - gap212ParamsPointA.δ) / 2)))
      ≤ (q : ℝ)) :
    q ∈ moduliIFamily x (((ω : ℚ) : ℝ)) γ widthI₁ ε' := by
  rw [gammaLoI, cast_ξ₁, cast_ϵ] at hγlo
  rw [cast_ϵ] at hε'
  rw [← omegaMax_eq_ω j j']
  refine mem_moduliI_of_qgen_le_half hx gap212Params_δ_pos hε₀ hε₀1 hγhi
    (gap212Params_A_add j j') ?_ widthI₁_gt_δ (gap212Params_B_le_one j m)
    (gap212Params_B_le_one j' m') (fun y hy ↦ admitsPartition₂_of_total_le
      ((total_le_pointA (gap212Params_Xi j j' hm hm' ▸ hy)).trans ?_) ?_) hq hqbig
  all_goals
    rw [widthI₁, gammaLoI, deltaStarI₁, gap212Params_δ, cast_δ, cast_ξ₁, cast_ω, cast_ϵ]
    norm_num; linarith

/-! ## Type I at Point A, second regime -/

/-- The Type I second-regime width, `1/14 - (68/14)ω - ϵ`. Independent of `γ`. -/
noncomputable def widthI₂ : ℝ := deltaStarI₂ ((ω : ℚ) : ℝ) ((ϵ : ℚ) : ℝ)

/-- The width exceeds the threshold: `0.039857 - ϵ > 0.0179`. -/
theorem widthI₂_gt_δ : gap212ParamsPointA.δ < widthI₂ := by
  norm_num [widthI₂, deltaStarI₂, gap212Params_δ, cast_δ, cast_ω, cast_ϵ]

/-- **The Type I route, second regime.** For `1/2 < γ ≤ 1/2 + 2ω + ε'` and `0 ≤ ε' ≤ ϵ`. This is
the regime condition (A′) was introduced for; the capacities that actually arise are `≥ 0.4760` and
`≥ 0.0199`, and (A′) supplies `0.487` and `0.0399` — generous on the first, too generous on the
second to be quoted at the far end, exactly as with condition (B). The trivial partition covers
it. -/
theorem mem_moduliI_route_gt_half {x ε₀ γ ε' : ℝ} {j j' : Fin gap212ParamsPointA.n}
    {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hγlo : ¬ (γ ≤ 1 / 2))
    (hγhi : γ ≤ 1 / 2 + 2 * (((ω : ℚ) : ℝ)) + ε')
    (hε'0 : 0 ≤ ε') (hε' : ε' ≤ ((ϵ : ℚ) : ℝ))
    (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hq : q ∈ Qgen gap212ParamsPointA x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ * (1 / 2 - (1 - γ - 3 * ε' - widthI₂
      + (widthI₂ - gap212ParamsPointA.δ) / 2))) ≤ (q : ℝ)) :
    q ∈ moduliIFamily x (((ω : ℚ) : ℝ)) γ widthI₂ ε' := by
  rw [cast_ω] at hγhi
  rw [cast_ϵ] at hε'
  push Not at hγlo
  rw [← omegaMax_eq_ω j j']
  refine mem_moduliI_of_qgen_gt_half hx gap212Params_δ_pos hε₀ hε₀1 (not_le.2 hγlo) ?_
    (gap212Params_A_add j j') ?_ widthI₂_gt_δ (gap212Params_B_le_one j m)
    (gap212Params_B_le_one j' m') (fun y hy ↦ admitsPartition₂_of_total_le
      ((total_le_pointA (gap212Params_Xi j j' hm hm' ▸ hy)).trans ?_) ?_) hq hqbig
  all_goals
    norm_num [omegaMax_eq_ω j j', widthI₂, deltaStarI₂, gap212Params_δ, cast_δ, cast_ω, cast_ϵ]
    linarith

/-! ## Type III at Point A -/

/-- The Type III width at Point A, `δ*_III = 109/4000 - 2ϵ`, carrying `-2ϵ`. -/
noncomputable def widthIII : ℝ := deltaStarIII' ((ω : ℚ) : ℝ) ((ξ₃ : ℚ) : ℝ) ((ϵ : ℚ) : ℝ)

/-- The width exceeds the threshold: `109/4000 - 2ϵ > 179/10000`. -/
theorem widthIII_gt_δ : gap212ParamsPointA.δ < widthIII := by
  norm_num [widthIII, deltaStarIII', gap212Params_δ, cast_δ, cast_ω, cast_ξ₃, cast_ϵ]

/-- **The Type III route.** The window is `[c - δ*, c]` at `c = 1/3 + 4δ*/3 - 4ω/3 = 0.361`, and
the capacities come out at `0.3563` and `0.1616` — the most comfortable of the three routes. -/
theorem mem_moduliIII_route {x ε₀ γ ε' : ℝ} {j j' : Fin gap212ParamsPointA.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hq : q ∈ Qgen gap212ParamsPointA x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ * (1 / 2 - (1 / 3 + 4 * widthIII / 3
      - 4 * (((ω : ℚ) : ℝ)) / 3 - widthIII + (widthIII - gap212ParamsPointA.δ) / 2))) ≤ (q : ℝ)) :
    q ∈ moduliIIIFamily x (((ω : ℚ) : ℝ)) γ widthIII ε' := by
  rw [← omegaMax_eq_ω j j'] at hqbig ⊢
  refine mem_moduliIII_of_qgen hx gap212Params_δ_pos hε₀ hε₀1 widthIII_gt_δ
    (gap212Params_A_add j j') ?_ (gap212Params_B_le_one j m) (gap212Params_B_le_one j' m')
    (fun y hy ↦ admitsPartition₂_of_total_le
      ((total_le_pointA (gap212Params_Xi j j' hm hm' ▸ hy)).trans ?_) ?_) hq hqbig
  all_goals
    norm_num [omegaMax_eq_ω j j', widthIII, deltaStarIII', gap212Params_δ, cast_δ, cast_ω,
      cast_ξ₃, cast_ϵ]

/-! ## Type IIb at Point A

The first route whose moduli set asks for two divisors, in the nested pattern `r ∣ d`, `u ∣ d/r`.
Three-factor extraction supplies it; the two windows are placed by retreating `(δ* - δ)/2` into
each target, which makes both exactly `δ` wide and makes the extraction's step condition
`b₁ - b₂ ≥ a₁ - a₂` hold with equality — so the caller has nothing to check there. -/

/-- The bottom of the Type IIb `γ`-range, as the source states it (`+3ϵ`). -/
noncomputable def gammaLoIIb : ℝ :=
  1 / 3 + 8 * ((ω : ℚ) : ℝ) + 7 * ((δ : ℚ) : ℝ) / 3 + 3 * ((ϵ : ℚ) : ℝ)

/-- The Type IIb route's width, at the bottom of its range. -/
noncomputable def widthIIb : ℝ := deltaStarIIb gammaLoIIb ((ω : ℚ) : ℝ) ((ϵ : ℚ) : ℝ)

/-- The width is `δ + 2ϵ/7`, exactly — thinner even than Type IIa's `δ + 3ϵ/7`, which is what the
source's `+3ϵ` in this route's `γ`-threshold buys. -/
theorem widthIIb_eq : widthIIb = ((δ : ℚ) : ℝ) + 2 * ((ϵ : ℚ) : ℝ) / 7 := by
  unfold widthIIb gammaLoIIb deltaStarIIb
  ring

/-- The width exceeds the support's threshold. -/
theorem widthIIb_gt_δ : gap212ParamsPointA.δ < widthIIb := by
  norm_num [widthIIb_eq, gap212Params_δ, cast_ϵ]

/-- **The Type IIb route.** For `γ` in `[γ_loIIb, γ_loIIa]` and `0 ≤ ε' ≤ ϵ`, at the fixed width
`widthIIb`, with both windows placed `δ` wide inside their targets.

The thin hypothesis is `0 < a₂`: the second window's lower end is `1/2 - γ - 2ω - 6ε' - δ - ϵ/7`,
which at the top of the range is only about `0.0128`. It is positive throughout, but this is the
tightest of the routes. -/
theorem mem_moduliIIb_route {x ε₀ γ ε' : ℝ} {j j' : Fin gap212ParamsPointA.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hγlo : gammaLoIIb ≤ γ) (hγhi : γ ≤ gammaLoIIa)
    (hε'0 : 0 ≤ ε') (hε' : ε' ≤ ((ϵ : ℚ) : ℝ))
    (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hq : q ∈ Qgen gap212ParamsPointA x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ * (1 / 2
      - (γ - 3 * ε' - widthIIb + (widthIIb - gap212ParamsPointA.δ) / 2 + gap212ParamsPointA.δ)
      - (1 / 2 - γ - 2 * (((ω : ℚ) : ℝ)) - 6 * ε' - widthIIb
          + (widthIIb - gap212ParamsPointA.δ) / 2))) ≤ (q : ℝ)) :
    q ∈ moduliIIbFamily x (((ω : ℚ) : ℝ)) γ widthIIb ε' := by
  rw [gammaLoIIb, cast_δ, cast_ω, cast_ϵ] at hγlo
  rw [gammaLoIIa, cast_δ, cast_ω, cast_ϵ] at hγhi
  rw [cast_ϵ] at hε'
  -- The level, kept as an abbreviation so the two windows and the goal all mention the same term.
  rw [← omegaMax_eq_ω j j'] at hqbig ⊢
  set W : ℝ := (gap212ParamsPointA.A j.succ + gap212ParamsPointA.A j'.succ) / 2 - 1 / 4
  -- The two windows: each `δ` wide, retreated `(δ* - δ)/2` into its target.
  refine mem_moduliIIb_of_qgen
    (a₁ := γ - 3 * ε' - widthIIb + (widthIIb - gap212ParamsPointA.δ) / 2)
    (b₁ := γ - 3 * ε' - widthIIb + (widthIIb - gap212ParamsPointA.δ) / 2 + gap212ParamsPointA.δ)
    (a₂ := 1 / 2 - γ - 2 * W - 6 * ε' - widthIIb + (widthIIb - gap212ParamsPointA.δ) / 2)
    (b₂ := 1 / 2 - γ - 2 * W - 6 * ε' - widthIIb + (widthIIb - gap212ParamsPointA.δ) / 2
      + gap212ParamsPointA.δ)
    hx gap212Params_δ_pos hε₀ hε₀1 (gap212Params_A_add j j')
    ?_ ?_ le_rfl le_rfl (by linarith) ?_ ?_ ?_ ?_
    (gap212Params_B_le_one j m) (gap212Params_B_le_one j' m')
    (fun y hy ↦ admitsPartition₃_of_total_le
      ((total_le_pointA (gap212Params_Xi j j' hm hm' ▸ hy)).trans ?_) ?_ ?_) hq hqbig
  all_goals
    norm_num [W, omegaMax_eq_ω j j', widthIIb_eq, gap212Params_δ, cast_δ, cast_ω, cast_ϵ]
      <;> linarith

end Gap212.Routing
