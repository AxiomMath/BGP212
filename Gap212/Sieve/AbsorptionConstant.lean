/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.TrivialMajorant
public meta import Gap212.Attr

/-!
# The absorption constant

The single constant the routing pays to extend an equidistribution estimate from a threshold `x₀`
down to `x ≥ 3`. On `[3, x₀]` no estimate is available and the only thing there is to say is that
the discrepancy sum is finite; the trivial majorant of the bundle says how finite, and this
constant is that majorant rescaled so that the crude bound at every `x` in the bounded range is
below the target `C₀ x (log x)^{-A}`.

The factor `1/3` is tied to the lower endpoint `3`: the target at `x` is at least
`3 · (1/3)(log x₀)^A x₀^{1/2+2ω} Λ_K(a₊x₀) (log x)^{-A}`, and the crude bound at `x` is at most
`x₀^{1/2+2ω} Λ_K(a₊x₀)`, so the two monotonicities `(log x)^A ≤ (log x₀)^A` and
`x^{1/2+2ω} ≤ x₀^{1/2+2ω}` close the gap. `Gap212.hasEquidistribution_of_forall_ge` carries this
quantity inline with the bundle's constants unpacked; this declaration is the same number with the
bundle bundled.

## Main definitions

* `Gap212.ConstantBundle.absorptionConstant`: the constant `C₀(K, ω, A, x₀)`.
-/

@[expose] public section

namespace Gap212.ConstantBundle

/-- **The absorption constant**
`C₀(K, ω, A, x₀) = ⅓ (log x₀)^A x₀^{1/2+2ω} Λ_K(a₊ x₀)`.

The majorant is evaluated at `a₊ x₀`, the top of the range a scale commensurable with `x₀` can
reach, because the sequences the routing absorbs are located at a scale `N ≤ a₊ x` and the majorant
is non-decreasing. -/
@[gap212 "def_absorption_constant"]
noncomputable def absorptionConstant (K : ConstantBundle) (ω A x₀ : ℝ) : ℝ :=
  1 / 3 * Real.log x₀ ^ A * x₀ ^ (1 / 2 + 2 * ω) * K.trivialMajorant (K.asympHi * x₀)

end Gap212.ConstantBundle
