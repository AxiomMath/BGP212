/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Gap212.Attr
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Gap212.Sieve.Certificate

/-!
# The chosen datum's scalar facts

The exponent of a scale, with the comparison against powers of `x` that every equidistribution
estimate reads its scale bounds through, and two arithmetic facts about the datum of the main
theorems: the five scalar inequalities the Harman reduction requires of its parameters, and the wall
the first rung of the cap row has to clear. The latter two are arithmetic in explicit rationals.

## Main definitions

* `Gap212.logScale`: the exponent `γ = log N / log x` of a scale `N` at `x`.

## Main results

* `Gap212.logScale_eq_logb`: the exponent is `Real.logb x N`, so Mathlib's API for it applies.
* `Gap212.rpow_logScale`: `x ^ logScale x N = N`, the defining property, for `1 < x` and `0 < N`.
* `Gap212.logScale_le_of_le_rpow`, `Gap212.le_logScale_of_rpow_le`,
  `Gap212.lt_logScale_of_rpow_lt`: a bound on `N` by a power of `x` is a bound on the exponent.
* `Gap212.log_div_log_le_of_le_rpow`, `Gap212.le_log_div_log_of_rpow_le`,
  `Gap212.lt_log_div_log_of_rpow_lt`: the same three in the spelling the estimates state.
* `Gap212.gap212Cap_one_lt`: the first rung of the cap row clears its wall.

## Implementation notes

`logScale x N` is `Real.logb x N`, base first in both, and `logScale_eq_logb` is that identity by
`rfl`: Mathlib's `logb` API applies to the exponent verbatim, and each bound below is one step from
`Real.logb_le_iff_le_rpow` or a sibling. The five estimates state the exponent as the quotient
`log N / log x` rather than through the abbreviation, and `linarith` reads `logScale x N` and
`log N / log x` as different atoms, so each bound is stated in that spelling as well.
-/

@[expose] public section

namespace Gap212

open Real

/-- **The exponent of a scale**, `γ = log_x N = log N / log x`.

A number determined by the pair `(N, x)`, never a free parameter and never a function of `x`. Its
defining property is `x ^ logScale x N = N` for `1 < x` and `0 < N` (`rpow_logScale`), and what the
estimates use it through is its comparison with powers of `x`: for `1 < x`, `N ≤ x ^ γ` says
`logScale x N ≤ γ` and `x ^ γ ≤ N` says `γ ≤ logScale x N`. -/
@[gap212 "not_gamma"]
noncomputable def logScale (x N : ℝ) : ℝ := log N / log x

/-- The exponent of a scale is the base-`x` logarithm: `logScale x N = logb x N`, by definition.
Every `Real.logb` lemma is a lemma about `logScale` through this. -/
theorem logScale_eq_logb (x N : ℝ) : logScale x N = logb x N := rfl

/-- **The exponent recovers the scale**: `x ^ log_x N = N`, for `1 < x` and `0 < N`. -/
theorem rpow_logScale {x N : ℝ} (hx : 1 < x) (hN : 0 < N) : x ^ logScale x N = N :=
  Real.rpow_logb (by linarith) (by linarith) hN

/-- An upper bound on a scale by a power of `x` bounds its exponent: `N ≤ x ^ γ` gives
`log_x N ≤ γ`. -/
theorem logScale_le_of_le_rpow {x N γ : ℝ} (hx : 1 < x) (hN : 0 < N) (h : N ≤ x ^ γ) :
    logScale x N ≤ γ := (Real.logb_le_iff_le_rpow hx hN).2 h

/-- A lower bound on a scale by a power of `x` bounds its exponent below: `x ^ γ ≤ N` gives
`γ ≤ log_x N`. No positivity of `N` is needed: the power supplies it. -/
theorem le_logScale_of_rpow_le {x N γ : ℝ} (hx : 1 < x) (h : x ^ γ ≤ N) : γ ≤ logScale x N :=
  (Real.le_logb_iff_rpow_le hx ((Real.rpow_pos_of_pos (by linarith) γ).trans_le h)).2 h

/-- The strict form of `le_logScale_of_rpow_le`: `x ^ γ < N` gives `γ < log_x N`. -/
theorem lt_logScale_of_rpow_lt {x N γ : ℝ} (hx : 1 < x) (h : x ^ γ < N) : γ < logScale x N :=
  (Real.lt_logb_iff_rpow_lt hx ((Real.rpow_pos_of_pos (by linarith) γ).trans h)).2 h

/-- `logScale_le_of_le_rpow` in the spelling the equidistribution estimates state. -/
theorem log_div_log_le_of_le_rpow {x N γ : ℝ} (hx : 1 < x) (hN : 0 < N) (h : N ≤ x ^ γ) :
    log N / log x ≤ γ := logScale_le_of_le_rpow hx hN h

/-- `le_logScale_of_rpow_le` in the spelling the equidistribution estimates state. -/
theorem le_log_div_log_of_rpow_le {x N γ : ℝ} (hx : 1 < x) (h : x ^ γ ≤ N) :
    γ ≤ log N / log x := le_logScale_of_rpow_le hx h

/-- `lt_logScale_of_rpow_lt` in the spelling the equidistribution estimates state. -/
theorem lt_log_div_log_of_rpow_lt {x N γ : ℝ} (hx : 1 < x) (h : x ^ γ < N) :
    γ < log N / log x := lt_logScale_of_rpow_lt hx h

/-- **The first rung clears its cap wall**: `B_{1,1} = 777/5000 < 778/5000`.

The wall is what pins the first rung: a larger `B_{1,1}` would admit a rough profile whose single
large coordinate exceeds what the Type II route can extract, and the rest of the row is built
upwards from this value. The slack is exactly `1/5000`. -/
@[gap212 "lem_cap_first_rung"]
theorem gap212Cap_one_lt : gap212Cap 1 < 778 / 5000 := by
  unfold gap212Cap
  norm_num

/-- **The four scalar conditions hold at `p_⋆`**, the datum of the main theorems:
`A₁ = 257/1000`, `δ = 41/2500`, `(ξ₁, ξ₂, ξ₃) = (19/50, 2/5, 2/5)`.

The conditions are Type I, the two halves of Type II, and Type III. Their slacks at this datum,
at the loosest `ϵ` admitted here:

| condition | binding value | slack over `δ` |
|---|---|---|
| I | `ξ₁ - 4A₁ + 2/3 = 7/375` | `0.0022646` |
| II, first wall | `19/2 - 36A₁ - 13δ = 87/2500` | `0.034785` (against `0`) |
| II, cap walls | `ξ₂/4 + 11/16 - 3A₁ = 33/2000` | `0.000098` |
| III | `11/8 - (7/2)A₁ - (9/8)ξ₃ = 51/2000` | `0.009098` |

The cap walls bind, at under `10⁻⁴`, and their binding branch is the second — the same branch, and
the same order of slack, as at Point A. Type I's first branch binds and is five times thinner here
than there (`0.00226` against `0.01138`), `ξ₁ = 19/50` being below Point A's `23317/60000`.

`ϵ ≤ 10⁻⁶` is what the margins can absorb, with a factor of `49` to spare on the tightest: the
binding requirement is `2ϵ ≤ 10⁻⁴`. It is carried as a hypothesis rather than fixed at a numeral so
that the statement is about the datum and not about one choice of slack.

Stated over any linearly ordered field, as `Gap212.harman_scalar_conditions_at_datum` is: the
routing reads these in `ℝ` while the datum's arithmetic is rational.

`Gap212.Auxiliary.scalar_conditions_at_pointA` proves the same four inequalities at *Point A*
(`A₁ = 513/2000`, `δ = 179/10000`, `ξ₁ = 23317/60000`), a different datum from that of the
main theorems. -/
@[gap212 "lem_scalar_conditions_at_datum"]
theorem scalar_conditions_at_datum {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {A₁ δ ϵ ξ₁ ξ₂ ξ₃ : 𝕜}
    (hA₁ : A₁ = 257 / 1000) (hδ : δ = 41 / 2500) (hξ₁ : ξ₁ = 19 / 50) (hξ₂ : ξ₂ = 2 / 5)
    (hξ₃ : ξ₃ = 2 / 5) (hϵ : 0 < ϵ) (hϵ' : ϵ ≤ 1 / 10 ^ 6) :
    δ < min (ξ₁ - 4 * A₁ + 2 / 3) (9 / 7 - (34 / 7) * A₁) - 2 * ϵ ∧
      0 ≤ 19 / 2 - 36 * A₁ - 13 * δ - 15 * ϵ ∧
      δ ≤ min (ξ₂ / 10 - 32 * A₁ / 10 + 8 / 10) (ξ₂ / 4 + 11 / 16 - 3 * A₁) - 2 * ϵ ∧
      δ < 11 / 8 - (7 / 2) * A₁ - (9 / 8) * ξ₃ - 2 * ϵ := by
  subst hA₁ hδ hξ₁ hξ₂ hξ₃
  norm_num at hϵ' ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

end Gap212
