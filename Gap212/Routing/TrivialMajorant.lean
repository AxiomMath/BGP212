/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.Defs.Equidistribution
public meta import Gap212.Attr

/-!
# The trivial majorant of a bundle

A `K`-coefficient sequence is bounded termwise by `C τ(n)^k (1 + log n)^l`. Summing that bound over
the whole support of a sequence located at a scale `y` — the integers up to `c₊ y` — and doubling
it to cover the two sums a discrepancy takes gives a single quantity that majorises the discrepancy
of *any* `K`-sequence at that scale, with no cancellation used:

`Λ_K(y) = 2 C (1 + log(1 + c₊ y))^l ∑_{n ≤ c₊ y} τ(n)^k`.

It is a crude bound and that is the point: it is what the routing spends on the finitely many
scales below a threshold, where no estimate applies and the only thing available is that the sum is
finite.

## Why the logarithm is evaluated at `1 + c₊ y`

The termwise bound carries `(1 + log n)^l`, largest at the top of the range. Writing the argument
as `1 + c₊ y` rather than `c₊ y` keeps it at least `1` for every `y ≥ 0`, so `log` of it is
non-negative and the `l`-th power is monotone without a side condition on where `c₊ y` sits
relative to `1`. The alternative — `(1 + log(c₊ y))^l` — is negative for small `c₊ y` and the power
then behaves differently for even and odd `l`.

## Main definitions

* `Gap212.ConstantBundle.trivialMajorant`: the majorant `Λ_K`.

## Main results

* `Gap212.ConstantBundle.trivialMajorant_mono`: `Λ_K` is non-decreasing on `[1, ∞)` when `C ≥ 0`.
* `Gap212.ConstantBundle.trivialMajorant_nonneg`: it is non-negative when `C ≥ 0`.
-/

@[expose] public section

namespace Gap212

open Finset Real

namespace ConstantBundle

/-- **The trivial majorant of a bundle.** `Λ_K(y)` is the termwise coefficient bound of `K` summed
over the integers up to `c₊ y` and doubled, the doubling covering the two sums of a discrepancy. -/
@[gap212 "def_trivial_majorant"]
noncomputable def trivialMajorant (K : ConstantBundle) (y : ℝ) : ℝ :=
  2 * K.coeffConst * (1 + Real.log (1 + K.scaleHi * y)) ^ K.coeffSndPow *
    ∑ n ∈ Finset.Icc 1 ⌊K.scaleHi * y⌋₊, (n.divisors.card : ℝ) ^ K.coeffFstPow

/-- The divisor sum of the majorant is non-negative, each term being a power of a cardinality. -/
theorem trivialMajorant_sum_nonneg (K : ConstantBundle) (y : ℝ) :
    0 ≤ ∑ n ∈ Finset.Icc 1 ⌊K.scaleHi * y⌋₊, (n.divisors.card : ℝ) ^ K.coeffFstPow :=
  Finset.sum_nonneg fun n _ ↦ by positivity

/-- The logarithmic factor is at least `1` for `0 ≤ y`, since `1 + c₊ y ≥ 1`. -/
theorem one_le_trivialMajorant_log (K : ConstantBundle) {y : ℝ} (hy : 0 ≤ y) :
    1 ≤ (1 + Real.log (1 + K.scaleHi * y)) ^ K.coeffSndPow := by
  have h1 : (1 : ℝ) ≤ 1 + K.scaleHi * y := le_add_of_nonneg_right (by nlinarith [K.scaleHi_pos])
  exact one_le_pow₀ (by linarith [Real.log_nonneg h1])

/-- **The trivial majorant is non-negative** when the bundle's coefficient constant is. -/
theorem trivialMajorant_nonneg (K : ConstantBundle) (hC : 0 ≤ K.coeffConst) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ K.trivialMajorant y := by
  have := K.one_le_trivialMajorant_log hy
  exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (K.trivialMajorant_sum_nonneg y)

/-- **The trivial majorant is non-decreasing.** Both factors grow with `y`: the summation range
`[1, ⌊c₊ y⌋]` only widens and its terms are non-negative, and `1 + log(1 + c₊ y)` increases from a
value at least `1`, so its `l`-th power increases too. -/
@[gap212 "lem_trivial_majorant_mono"]
theorem trivialMajorant_mono (K : ConstantBundle) (hC : 0 ≤ K.coeffConst) {y y' : ℝ}
    (hy : 1 ≤ y) (hyy : y ≤ y') : K.trivialMajorant y ≤ K.trivialMajorant y' := by
  have hc := K.scaleHi_pos.le
  have h1 : (1 : ℝ) ≤ 1 + K.scaleHi * y := by nlinarith
  unfold trivialMajorant
  gcongr
  · exact mul_nonneg (by linarith)
      (by linarith [K.one_le_trivialMajorant_log (y := y') (by linarith)])
  · linarith [Real.log_nonneg h1]

end ConstantBundle

end Gap212
