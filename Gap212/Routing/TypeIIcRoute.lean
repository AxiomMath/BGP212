/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.ConditionD
public import Gap212.Routing.Dyadic
public import Gap212.Routing.Routes
public meta import Gap212.Attr

/-!
# The Type IIc route

## Its four capacities are condition (D)'s

Placing the three windows each `δ` wide inside their targets — retreating `(δ* - δ)/2` at the first
and the corresponding amount at the two `q`-scaled ones — makes the four bin capacities of
`Gap212.Extraction.four_factor` come out as

    2a₁ + b₃      = γ - 2δ - 8ω₀ - (3/2)(δ*-δ) - 58ε' + 2w
    b₂            = 1/2 - γ - 2ω₀ - (δ*-δ)/2 - 6ε' + w/2
    1/2+2ω₀-b₁-a₂ = 4ω₀ + δ + (δ*-δ) + 9ε' - w/2
    a₁-2b₁-a₃     = 8ω₀ + (δ*-δ) + 55ε' - 2w

where `w` is the dyadic block's width. Compare `Gap212.Packing.cap₁`–`cap₄`: these are exactly
condition (D)'s capacities, each shifted by an `O(ϵ)` amount. So **`Gap212.Packing.conditionD`
discharges this route's packing hypothesis**, via `AdmitsPartition₄.mono`. That is what condition
(D) was for; no other route needs it, and this one needs nothing else.

The last column of the second display is worth comparing with the transport table of
`Gap212.Transition.Transport`: the fourth capacity is `8ω₀ + (δ*-δ) + 55ε' - 2w`, and the
table's raw fourth capacity is `-4κ + 55εt`. Same shape, same `55`.

## What the widths have to satisfy

Two competing constraints, and they pin `δ* - δ` to order `ϵ`:

* the third window must fit, which needs `4w < δ* - δ` — the `4` is the `d⁻⁴` scaling, so the block
  width is squeezed four times harder here than at the second window;
* the first capacity must dominate `cap₁`, which needs `2w + ϵ ≥ (3/2)(δ* - δ) + 58ε'`.

Together these force `δ* - δ < ϵ - 58ε'`. Taking `δ* = δ + ϵ/4`, `ε' ≤ ϵ/100` and `w ≤ ϵ/32` leaves
all four capacities with slack at least `9ϵ/200`, and the estimate's own three walls have room to
spare: the binding one is `γ/4 - 1/16 - 3ω_max` at `γ = ξ₂ - ϵ`, worth `0.018`, against
`δ + ϵ/4 ≈ 0.0179`.

So the margin here is `10⁻⁴` — the thinnest of the six routes, and it is precisely the margin
`Gap212.PointA.typeII_condition_b` records as exactly `1/10000`.

## Main results

* `Gap212.Routing.widthIIc`, `widthIIc_gt_δ`.
* `Gap212.Routing.mem_moduliIIc_route`: the containment.
-/

@[expose] public section

namespace Gap212.Routing

open Gap212.PointA Gap212.Packing Gap212.Extraction

/-- The Type IIc width, `δ + ϵ/4`. The `ϵ/4` is forced from both sides — see above. -/
@[gap212 "def_delta_star_typeIIc"]
noncomputable def widthIIc : ℝ := ((δ : ℚ) : ℝ) + ((ϵ : ℚ) : ℝ) / 4

/-- The width exceeds the support's threshold, by `ϵ/4`. -/
theorem widthIIc_gt_δ : gap212ParamsPointA.δ < widthIIc := by
  rw [widthIIc, gap212Params_δ, cast_ϵ]
  norm_num

/-- `widthIIc - δ = ϵ/4`. -/
theorem widthIIc_sub_δ : widthIIc - gap212ParamsPointA.δ = ((ϵ : ℚ) : ℝ) / 4 := by
  rw [widthIIc, gap212Params_δ]
  ring

/-- **The Type IIc route.** For `γ` in the Type IIc chamber, a level `ω₀ ∈ [0, ω]`, a dyadic block
`[x^{t-w}, x^t]` at `t = 1/2 + 2ω₀` of width `w ≤ ϵ/32`, and a retreat `ε' ≤ ϵ/100`, every
generated modulus in the block lies in the Stadlmann Type IIc moduli set at width `widthIIc`.

The packing hypothesis is discharged by `Gap212.Packing.conditionD` — the only route needing it. -/
theorem mem_moduliIIc_route {x ε₀ γ ε' ω₀ t wb : ℝ} {j j' : Fin gap212ParamsPointA.n}
    {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hγlo : (2 / 5 : ℝ) - ((ϵ : ℚ) : ℝ) ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * ((ω : ℚ) : ℝ) + 7 * ((δ : ℚ) : ℝ) / 3 + 3 * ((ϵ : ℚ) : ℝ))
    (hω₀0 : 0 ≤ ω₀) (hω₀ : ω₀ ≤ ((ω : ℚ) : ℝ)) (hωt : t = 1 / 2 + 2 * ω₀)
    (hε'0 : 0 ≤ ε') (hε' : ε' ≤ ((ϵ : ℚ) : ℝ) / 100)
    (hwb0 : 0 ≤ wb) (hwb : wb ≤ ((ϵ : ℚ) : ℝ) / 32)
    (hqlo : x ^ (t - wb) ≤ (q : ℝ)) (hqhi : (q : ℝ) ≤ x ^ t)
    (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hq : q ∈ Qgen gap212ParamsPointA x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 + 2 * ω₀ - ε₀ * (1 / 2 + 2 * ω₀
      - (γ - 3 * ε' - widthIIc + (widthIIc - gap212ParamsPointA.δ) / 2 + gap212ParamsPointA.δ)
      - (1 - γ - 6 * ε' - widthIIc - (t - wb)
          + (widthIIc - gap212ParamsPointA.δ - wb) / 2))) ≤ (q : ℝ)) :
    q ∈ moduliIIcFamily x (((ω : ℚ) : ℝ)) γ widthIIc ε' := by
  have he : ((ϵ : ℚ) : ℝ) = 1 / 10 ^ 10 := cast_ϵ
  have hd : ((δ : ℚ) : ℝ) = 179 / 10000 := cast_δ
  have hw : ((ω : ℚ) : ℝ) = 13 / 2000 := cast_ω
  have hgd : gap212ParamsPointA.δ = 179 / 10000 := by rw [gap212Params_δ, hd]
  have hwid : widthIIc = 179 / 10000 + (1 / 10 ^ 10) / 4 := by rw [widthIIc, hd, he]
  have hqpos : (0 : ℝ) < (q : ℝ) := (Real.rpow_pos_of_pos (by linarith) _).trans_le hqlo
  rw [← omegaMax_eq_ω j j']
  refine mem_moduliIIc_of_qgen (ω₀ := ω₀)
    (a₁ := γ - 3 * ε' - widthIIc + (widthIIc - gap212ParamsPointA.δ) / 2)
    (b₁ := γ - 3 * ε' - widthIIc + (widthIIc - gap212ParamsPointA.δ) / 2 + gap212ParamsPointA.δ)
    (a₂ := 1 - γ - 6 * ε' - widthIIc - (t - wb) + (widthIIc - gap212ParamsPointA.δ - wb) / 2)
    (b₂ := 1 - γ - 6 * ε' - widthIIc - (t - wb) + (widthIIc - gap212ParamsPointA.δ - wb) / 2
      + gap212ParamsPointA.δ)
    (a₃ := 2 - γ - 52 * ε' - widthIIc - 4 * (t - wb)
      + (widthIIc - gap212ParamsPointA.δ - 4 * wb) / 2)
    (b₃ := 2 - γ - 52 * ε' - widthIIc - 4 * (t - wb)
      + (widthIIc - gap212ParamsPointA.δ - 4 * wb) / 2 + gap212ParamsPointA.δ)
    hx gap212Params_δ_pos hε₀ hε₀1 (gap212Params_A_add j j')
    ?_ le_rfl le_rfl le_rfl (by linarith) (by linarith)
    ?_ ?_ ?_ ?_ ?_ ?_
    (gap212Params_B_le_one j m) (gap212Params_B_le_one j' m') ?_ hq hqbig
  -- `0 < a₁`
  · rw [hwid, hgd]; norm_num
    all_goals linarith
  -- `hlo₁`, `hhi₁`
  · rw [hwid, hgd]; norm_num
  · rw [hwid, hgd]; norm_num
    all_goals linarith
  -- `hlo₂`, `hhi₂`: the second window, scaled by `q⁻¹`
  · refine div_lt_rpow hx hqlo ?_
    rw [hwid, hgd]; linarith
  · refine rpow_lt_div hx hqhi hqpos ?_
    rw [hwid, hgd]; linarith
  -- `hlo₃`, `hhi₃`: the third window, scaled by `q⁻⁴`
  · refine div_pow4_lt_rpow hx hqlo ?_
    rw [hwid, hgd]; linarith
  · refine rpow_lt_div_pow4 hx hqhi hqpos ?_
    rw [hwid, hgd]; linarith
  -- the packing condition: condition (D), weakened by `AdmitsPartition₄.mono`
  · intro y hy
    rw [gap212Params_Xi j j' hm hm'] at hy
    refine (conditionD hγlo hγhi hω₀0 hω₀ hy).mono ?_ ?_ ?_ ?_
    · rw [cap₁, hd, he, hwid, hgd, hωt]; norm_num
      all_goals linarith
    · rw [cap₂, he, hwid, hgd, hωt]; norm_num
      all_goals linarith
    · rw [cap₃, hd, he, hwid, hgd, hωt]; norm_num
      all_goals linarith
    · rw [cap₄, hwid, hgd, hωt]; norm_num
      all_goals linarith

end Gap212.Routing
