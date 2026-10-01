/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.RoutePacking
public import Gap212.Routing.Retreat
public meta import Gap212.Attr

/-!
# Bridging the support record to the Point A parameter list

`Gap212.gap212ParamsPointA` is a `SupportParams` whose fields are real decimal
literals, because that is
what the sieve criterion and the integrals consume. `Gap212.PointA` holds the same numbers as exact
rationals, because that is what `norm_num` can decide. Every route needs them identified, and this
module identifies them once.

The identifications are all `norm_num`-checkable equalities of numerals, with one exception worth
naming: the level

    ω_max = (A_j + A_{j'})/2 - 1/4

that the containments run at is *equal to* `Gap212.PointA.ω`. That is not a coincidence of
notation. The support has one stratum, so `A_j = A_{j'} = A₁ = 513/2000`, and

    513/2000 - 1/4 = 13/2000 = ω.

So the `ω` appearing in every Point A inequality — the one the packing conditions are stated
against — *is* the level at which the estimates get applied. Without this the two halves of the
development cannot meet: the packing conditions would be about a different number from the
containments.

## Main results

* `Gap212.Routing.gap212Params_δ`, `gap212Params_ε`, `gap212Params_B`: the field identifications.
* `Gap212.Routing.omegaMax_eq_ω`: the level is Point A's `ω`.
* `Gap212.Routing.gap212Params_Xi`: the check set of the support is the check set of Point A.
-/

@[expose] public section

namespace Gap212.Routing

open Gap212.PointA Gap212.Packing

/-! ## The field identifications -/

/-- The support's threshold is Point A's `δ = 179/10000`. -/
theorem gap212Params_δ : gap212ParamsPointA.δ = ((δ : ℚ) : ℝ) := by
  rw [cast_δ]
  change (0.0179 : ℝ) = 179 / 10000
  norm_num

/-- The support's enlargement is Point A's `ε = 17/2000`. -/
theorem gap212Params_ε : gap212ParamsPointA.ε = ((ε : ℚ) : ℝ) := by
  rw [show ((ε : ℚ) : ℝ) = 17 / 2000 by rw [show (ε : ℚ) = 17 / 2000 from rfl]; norm_num]
  change (0.0085 : ℝ) = 17 / 2000
  norm_num

/-- The support's `B` row is Point A's `Bcap`, **for `m ≥ 1`**.

The restriction is not incidental. `SupportParams.B_zero` forces `B_{j,0} = 0`, which is what makes
the rough-mass cap vacuous when there are no large coordinates and the empty rough product in
`Qgen` equal to `1`; Point A's `Bcap` has no `m = 0` case and returns `31/200` there, which would
license rough mass with no rough factors. So the two rows genuinely differ at `0`, and every
consumer of this identification supplies `1 ≤ m`. -/
theorem gap212Params_B (j : Fin gap212ParamsPointA.n) {m : ℕ} (hm : 1 ≤ m) :
    gap212ParamsPointA.B j m = (Bcap m : ℝ) := by
  have h0 : ¬ m = 0 := by omega
  simp only [gap212ParamsPointA, if_neg h0]
  have h₁ : ((B₁ : ℚ) : ℝ) = 31 / 200 := by
    rw [show (B₁ : ℚ) = 31 / 200 from rfl]; norm_num
  have h₃ : ((B₃ : ℚ) : ℝ) = 17 / 100 := by
    rw [show (B₃ : ℚ) = 17 / 100 from rfl]; norm_num
  rw [Bcap]
  split_ifs
  · rw [h₁]; norm_num
  · rw [h₃]; norm_num

/-- Every stratum index of the Point A support is the last one, since there is only one. -/
theorem gap212Params_succ_val (j : Fin gap212ParamsPointA.n) : (j.succ).val = 1 := by
  have hn : gap212ParamsPointA.n = 1 := rfl
  have hlt := j.isLt
  have h0 : j.val = 0 := by omega
  rw [Fin.val_succ, h0]

/-- `A₁ = 513/2000`, as a real. -/
theorem gap212Params_A_succ (j : Fin gap212ParamsPointA.n) :
    gap212ParamsPointA.A j.succ = 513 / 2000 := by
  have h : gap212ParamsPointA.A j.succ = (((j.succ).val : ℝ)) * 0.265 - 0.0085 := rfl
  rw [h, gap212Params_succ_val j]
  norm_num

/-! ## The level the containments run at -/

/-- **The level is Point A's `ω`.** With one stratum, `A_j = A_{j'} = 513/2000` and
`513/2000 - 1/4 = 13/2000 = ω`. This is what lets the packing conditions, stated against `ω`, be
consumed by the containments, stated against `(A_j + A_{j'})/2 - 1/4`. -/
theorem omegaMax_eq_ω (j j' : Fin gap212ParamsPointA.n) :
    (gap212ParamsPointA.A j.succ + gap212ParamsPointA.A j'.succ) / 2 - 1 / 4 = ((ω : ℚ) : ℝ) := by
  rw [gap212Params_A_succ j, gap212Params_A_succ j', cast_ω]
  norm_num

/-- The support's check set is Point A's check set, so a packing condition proved for one applies
to the other. -/
theorem gap212Params_Xi (j j' : Fin gap212ParamsPointA.n) {m m' : ℕ}
    (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    Xi (gap212ParamsPointA.B j m) (gap212ParamsPointA.B j' m') m m' gap212ParamsPointA.δ
      = Xi (Bcap m) (Bcap m') m m' (((δ : ℚ) : ℝ)) := by
  rw [gap212Params_B j hm, gap212Params_B j' hm', gap212Params_δ]

/-! ## The consequences the containments need directly -/

/-- The threshold is positive. -/
theorem gap212Params_δ_pos : 0 < gap212ParamsPointA.δ := gap212ParamsPointA.δ_pos

/-- Each rough cap is at most `1`, which is what the hereditary bound in the extraction needs. -/
theorem gap212Params_B_le_one (j : Fin gap212ParamsPointA.n) (m : ℕ) :
    gap212ParamsPointA.B j m ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [gap212ParamsPointA.B_zero j]; norm_num
  · rw [gap212Params_B j hm]
    exact le_trans (Bcap_le (𝕜 := ℝ) m) (by norm_num)

/-- The two mixed caps add to `513/1000`, which is Point A's `ϑ` — the level of distribution the
method reaches. -/
theorem gap212Params_A_add (j j' : Fin gap212ParamsPointA.n) :
    0 ≤ gap212ParamsPointA.A j.succ + gap212ParamsPointA.A j'.succ := by
  rw [gap212Params_A_succ j, gap212Params_A_succ j']
  norm_num

/-- Named: the two mixed caps add to `ϑ = 513/1000`. -/
theorem gap212Params_A_add_eq_ϑ (j j' : Fin gap212ParamsPointA.n) :
    gap212ParamsPointA.A j.succ + gap212ParamsPointA.A j'.succ = ((ϑ : ℚ) : ℝ) := by
  rw [gap212Params_A_succ j, gap212Params_A_succ j',
    show ((ϑ : ℚ) : ℝ) = 513 / 1000 by rw [show (ϑ : ℚ) = 513 / 1000 from rfl]; norm_num]
  norm_num

end Gap212.Routing
