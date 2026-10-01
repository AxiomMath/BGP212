/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Gap212.Attr
public import Gap212.Definitions
public import Gap212.Equidistribution.Defs.FiveEstimates
public import Gap212.Routing.Defs.Equidistribution

/-!
# The five assumed equidistribution estimates

The tags of the five equidistribution estimates and of bilinear Bombieri–Vinogradov. The
propositions themselves are declared in `Gap212.Definitions`; they are hypotheses of the main
theorems, and the analytic estimates those theorems rest on.

Their shape, compared with the two-variable `...Family` forms of
`Gap212.Equidistribution.Estimates`:

* every constant lives in one `ConstantBundle`, fixed before the sequences and their scales;
* the exponent is literally `log N / log x`, not a member of a set of admissible exponents;
* the inequalities are **non-strict**, carrying a uniform slack `θ` quantified **before** `ε₀` and
  before `C`, where the `...Family` forms are strict with the slack bound existentially inside;
* `∃ C` comes before `∀ δ`, before `∀ x`, and before the sequences and scales, so one constant
  serves every width, which is what lets the width be chosen as a function of `x` at the point of
  application;
* `TypeIBakerIrving` asks `K.LocatedAtScale β N` and caps its second branch at
  `N ≤ x ^ (1/2 + 2 * ω + ε)`, both of which the `...Family` form omits;
* `TypeIIIPolymath` asks all three `K.IsCoefficientSequence ψᵢ`, takes `ω ∈ Set.Ioo 0 (1/12)` rather
  than `(0, 1/4)`, and associates its fourfold convolution to the **left**, where the `...Family`
  form associates right.
-/

@[expose] public section

namespace Gap212

attribute [gap212 "thm_ext_type_ii"] TypeIIPolymath
attribute [gap212 "thm_ext_type_iib"] TypeIbPolymath
attribute [gap212 "thm_ext_type_i"] TypeIBakerIrving
attribute [gap212 "thm_ext_type_iic"] TypeIStadlmann
attribute [gap212 "thm_ext_type_iii"] TypeIIIPolymath
attribute [gap212 "thm_ext_bilinear_bv"] BilinearBombieriVinogradov

open Real Finset

end Gap212
