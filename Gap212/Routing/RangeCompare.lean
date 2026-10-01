/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.Crude
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The two cutoffs compare, and where

The four-range architecture of the routing rests on one comparison, the only genuinely analytic fact
in it. Factor extraction reaches moduli above `x^{1/2 - κ}`; bilinear Bombieri–Vinogradov reaches
moduli below `x^{1/2}(log x)^{-B}`. For the two to cover, the first cutoff must lie below the
second:

    x^{1/2 - κ} ≤ x^{1/2} / (log x)^B    ⟺    (log x)^B ≤ x^κ.

That holds for all large `x` and **fails for intermediate `x`** when `B` is large and `κ` small —
which is why the assembly needs a threshold `X₀`, and why `Gap212.Routing.exists_crude_bound`
exists to absorb `(1, X₀]`.

`Gap212.Routing.exists_threshold_ranges_compare` supplies the `X₀`. It is `(log x)^B = o(x^κ)`,
`isLittleO_log_rpow_rpow_atTop`, made into an explicit threshold.

## Why this closes the range comparison and not the whole sub-half obligation

With `X₀` in hand, the sub-half part of a generated family at scales `x ≥ X₀` sits inside bilinear
Bombieri–Vinogradov's index set, so the citation applies there; below `X₀` the crude bound applies.
So the *range* side of `Gap212.Routing.SubHalfCoverage` is settled for every shape.

What remains per shape is getting `f` into the `dconvFamily α β`-with-Siegel–Walfisz form of
bilinear Bombieri–Vinogradov. For Type II that is immediate — its members are already two-fold
convolutions with Siegel–Walfisz on both factors. For Type I and Type III it is not; the
single-scale form `Gap212.exists_hasEquidistribution_subhalf_of_harmanClass` covers the sub-half
range for every shape.

## Main results

* `Gap212.Routing.exists_threshold_log_rpow_le`: `(log x)^B ≤ x^s` beyond an explicit threshold.
* `Gap212.Routing.exists_threshold_ranges_compare`: the extraction cutoff lies below BV's.
-/

@[expose] public section

namespace Gap212.Routing

open Filter Asymptotics Real

/-! ## Logarithms lose to powers, with a threshold -/

/-- **`(log x)^B ≤ x^s` beyond an explicit threshold**, for any `B` and any `s > 0`. This is
`isLittleO_log_rpow_rpow_atTop` turned into a threshold statement. -/
theorem exists_threshold_log_rpow_le (B : ℝ) {s : ℝ} (hs : 0 < s) :
    ∃ X₀ : ℝ, 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → (log x) ^ B ≤ x ^ s := by
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (s := s) B hs).def one_pos)
  refine ⟨max X 2, by linarith [le_max_right X 2], fun x hx ↦ ?_⟩
  have hb := hX x (le_of_max_le_left hx)
  rw [one_mul, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith [le_of_max_le_right hx]) s)] at hb
  exact (le_abs_self _).trans hb

/-! ## The two cutoffs -/

/-- **The extraction's cutoff lies below bilinear Bombieri–Vinogradov's, beyond a threshold.** For
every `B` and every retreat `κ > 0` there is an `X₀` past which

    x^{1/2 - κ} ≤ x^{1/2} / (log x)^B,

so the moduli the routes do not reach are inside the range the citation covers. Below `X₀` the
comparison can fail, which is what `Gap212.Routing.exists_crude_bound` is for. -/
theorem exists_threshold_ranges_compare (B : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ X₀ : ℝ, 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
      x ^ (1 / 2 - κ) ≤ x ^ (1 / 2 : ℝ) / (log x) ^ B := by
  obtain ⟨X, hX1, hXle⟩ := exists_threshold_log_rpow_le B hκ
  refine ⟨X, hX1, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  rw [Real.rpow_sub hx0]
  exact div_le_div_of_nonneg_left (by positivity)
    (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) B) (hXle x hx)

end Gap212.Routing
