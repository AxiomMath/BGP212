/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.Basic
public import Gap212.Sieve.Certificate
public import Gap212.Windows.Bridges
public meta import Gap212.Attr

/-!
# The two numerical facts about the chosen datum

`Gap212.gap212Params` is the datum of the main theorem: `δ = 41/2500`, `ε = 1/125`, one band
(`n = 1`), `A i = i · 53/200 - 1/125`, and the ten-rung cap row `Gap212.gap212Cap`. It is the
datum written `p_⋆` throughout, and `Gap212Challenge/Basic.lean`'s support verbatim.

Two facts about it are quoted throughout the packing and routing layers, and both are arithmetic:
the level of its only band pair, and the largest pooled rough mass its cap row admits.

## Relation to Point A

The `gap212Params_*` lemmas in `Gap212.Routing.PointABridge` are proved at
`Gap212.gap212ParamsPointA`, a *different* support with `δ = 179/10000` and `ω(1,1) = 13/2000`.
Likewise `Gap212.Packing.total_le_pointA` bounds the pooled mass by `17/50`, which is Point A's
two-rung row, not this one's ten-rung row. Neither transfers, so the facts below are proved from
`gap212Params` itself.

## Main results

* `Gap212.omegaMax_gap212Params`: the only band pair of `p_⋆` has level `7/1000`.
* `Gap212.gap212Cap_le`: every rung of the cap row is at most `1081/5000`.
* `Gap212.total_le_datum`: hence the pooled rough mass of `p_⋆` never exceeds `1081/2500`.
-/

@[expose] public section

namespace Gap212

open Finset Gap212.Bridges Gap212.Packing

/-- **The level of the only band pair of `p_⋆` is `7/1000`.** With `n = 1` there is a single pair
`(1,1)`, and `A₁ = 53/200 - 1/125 = 257/1000`, so `ω(1,1) = A₁ - 1/4 = 7/1000`.

This is the level `ω(j,j')` at which every window of the routing is placed,
so it is the one numeral the whole positive-level side of the argument is calibrated to. Point A's
is `13/2000`, which is why nothing proved there transfers. -/
@[gap212 "lem_datum_omega"]
theorem omegaMax_gap212Params (j j' : Fin gap212Params.n) :
    omegaMax gap212Params j j' = 7 / 1000 := by
  have hsucc : ∀ k : Fin gap212Params.n, (k.succ).val = 1 := by
    intro k
    have hlt : k.val < 1 := k.isLt
    have hk : k.val = 0 := by omega
    simp [Fin.succ, hk]
  have hA : ∀ k : Fin gap212Params.n, gap212Params.A k.succ = 257 / 1000 := fun k ↦ by
    have : gap212Params.A k.succ = ((k.succ).val : ℝ) * (53 / 200) - 1 / 125 := rfl
    rw [this, hsucc k]; norm_num
  unfold omegaMax
  rw [hA j, hA j']
  norm_num

/-- **Every rung of the cap row is at most `1081/5000`.** The row rises through ten values and is
constant from the tenth on, so the last rung is the maximum. -/
theorem gap212Cap_le (m : ℕ) : gap212Cap m ≤ 1081 / 5000 := by
  by_cases h : 10 ≤ m
  · exact le_of_eq (gap212Cap_of_ten_le h)
  · have h' : m < 10 := by omega
    interval_cases m <;> norm_num [gap212Cap]

/-- Hence any two rungs sum to at most `1081/2500`. -/
theorem gap212Cap_add_le (m m' : ℕ) : gap212Cap m + gap212Cap m' ≤ 1081 / 2500 := by
  have h₁ := gap212Cap_le m
  have h₂ := gap212Cap_le m'
  linarith

/-- **The pooled rough mass at `p_⋆` never exceeds `1081/2500`.** The two rough sides of a tuple in
`Ξ` are capped by their own rungs, and both rungs are at most `1081/5000`.

The bound is attained only with both sides at the top rung. It *exceeds* `ξ₁ = 19/50`, so pooling
alone does not discharge Condition A at this datum: `Gap212.conditionA_at_datum` splits the mass
instead. -/
@[gap212 "lem_datum_pooled_mass"]
theorem total_le_datum {m m' : ℕ} {y : Fin (m + m') → ℝ}
    (hy : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ)) :
    ∑ i, y i ≤ 1081 / 2500 :=
  (total_le hy).trans (gap212Cap_add_le m m')

end Gap212
