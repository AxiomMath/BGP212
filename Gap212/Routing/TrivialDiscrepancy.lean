/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Consequences.Basic
public import Gap212.Routing.TrivialMajorant
public meta import Gap212.Attr

/-!
# The trivial discrepancy bound, termwise and summed

`Gap212.norm_sumError_le_and_sum_norm_sumError_le_of_located` proves two things at once and writes
the majorant out in full. The two halves — the termwise bound, and the bound summed over a
modulus family — are restated here against `Gap212.ConstantBundle.trivialMajorant`, one
declaration each.

Nothing is reproved: both are the corresponding half of that conjunction, with the inlined
expression recognised as `K.trivialMajorant y`. The point of the restatement is that consumers can
cite `Λ_K` by name instead of carrying eleven characters of arithmetic.

## Why both extra hypotheses are needed

`f` located at a scale, and `f 0 = 0`. Neither is needed for the *dyadic* discrepancy — there the
block `dyadic x ⊆ [1, 2x]` does the truncating, being finite and excluding `0`. Against the
unrestricted discrepancy the truncation has to come from the
sequence. Without location the claim is false: `f n = τ(n)^k (1 + log n)^l` is a `K`-coefficient
sequence of infinite support and no bound in terms of `K` and a scale can hold. Without `f 0 = 0`
the term at `n = 0`, which the coefficient bound never controls, sits inside the range whenever
`d ∣ a`. Both hold at every call site, the sequences there being convolutions.

## Main results

* `Gap212.norm_sumError_le_trivialMajorant`: the termwise bound `‖Δ(f;d,a)‖ ≤ Λ_K(y)`.
* `Gap212.sum_norm_sumError_le_trivialMajorant`: summed over `D ⊆ moduliRange x ω`, the bound
  `x^{1/2+2ω} Λ_K(y)`.
-/

@[expose] public section

namespace Gap212

open Finset Real

/-- The majorant of a bundle, written out, is what the trivial bound already carries. -/
theorem trivialMajorant_eq_expand (K : ConstantBundle) (y : ℝ) :
    K.trivialMajorant y = 2 * K.coeffConst * (1 + Real.log (1 + K.scaleHi * y)) ^ K.coeffSndPow *
      ∑ n ∈ Finset.Icc 1 ⌊K.scaleHi * y⌋₊, (n.divisors.card : ℝ) ^ K.coeffFstPow := rfl

/-- **The trivial discrepancy bound.** A `K`-coefficient sequence located at a scale `N ≤ y` and
vanishing at `0` has every discrepancy bounded by the bundle's trivial majorant at `y`.

No cancellation is used: the bound is the termwise coefficient bound summed over the support and
doubled, the doubling covering the two sums a discrepancy takes. -/
@[gap212 "lem_trivial_discrepancy_bound"]
theorem norm_sumError_le_trivialMajorant {K : ConstantBundle} {f : ℕ → ℂ} {N y : ℝ}
    (hf : K.IsCoefficientSequence f) (hloc : K.LocatedAtScale f N)
    (hf0 : f 0 = 0) (hN : 0 < N) (hNy : N ≤ y) (d a : ℕ) :
    ‖sumError f d a‖ ≤ K.trivialMajorant y :=
  (norm_sumError_le_and_sum_norm_sumError_le_of_located hf hloc hf0 hN hNy a).1 d

/-- **The trivial bound summed over a modulus family.** Every term is at most `Λ_K(y)` and
`moduliRange x ω` has at most `x^{1/2+2ω}` elements, so any subfamily of it contributes at most
`x^{1/2+2ω} Λ_K(y)`.

This is what the routing spends on the finitely many scales below a threshold, where no estimate
applies and the only fact available is that the family is finite. -/
@[gap212 "lem_trivial_discrepancy_sum"]
theorem sum_norm_sumError_le_trivialMajorant {K : ConstantBundle} {f : ℕ → ℂ} {N y : ℝ}
    (hf : K.IsCoefficientSequence f) (hloc : K.LocatedAtScale f N)
    (hf0 : f 0 = 0) (hN : 0 < N) (hNy : N ≤ y) (a : ℕ) {x ω : ℝ} (hx : 0 ≤ x)
    {D : Finset ℕ} (hD : D ⊆ moduliRange x ω) :
    ∑ d ∈ D, ‖sumError f d a‖ ≤ x ^ (1 / 2 + 2 * ω) * K.trivialMajorant y :=
  (norm_sumError_le_and_sum_norm_sumError_le_of_located hf hloc hf0 hN hNy a).2 x ω hx D hD

end Gap212
