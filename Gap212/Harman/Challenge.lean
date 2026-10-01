/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Gap212.Attr
public import Gap212.Definitions
public import Gap212.Routing.Defs.GeneratedModuli
public import Gap212.Main
public import Gap212.Sieve.Certificate

/-!
# The Harman class and the reduction, as the challenge states them

The three convolution classes, the equidistribution norm over a support's moduli, and the assumed
Harman reduction, as stated in `Gap212Challenge/Basic.lean`.

Each class is a predicate **at one `x` and one bundle**: the witnesses `α, β, M, N` carry no `x`
argument, and `K : ConstantBundle` fixes every constant before them. The scale bounds are
pointwise inequalities.

`HasEquidistributionOverQstar` is one explicit inequality with `x`, `ε₀`, `a`, `A`, `C` as
arguments, delegating to `HasEquidistribution` and taking its squarefree restriction from there.
The quantifiers over `ε₀`, `A`, `x` and `a` live in the statements that use it.

`HarmanReduction`'s consequent is at `primeInterval x`, not `primeIndicator`: the discrepancy
`HasEquidistribution` sums is the unrestricted one, which needs a finitely supported sequence, and
the bare prime indicator has infinite support.
-/

@[expose] public section

namespace Gap212

attribute [gap212 "def_slack"] slack
attribute [gap212 "def_type_I"] TypeI
attribute [gap212 "def_type_II"] TypeII
attribute [gap212 "def_type_III"] TypeIII
attribute [gap212 "def_harman_class"] HarmanClass
attribute [gap212 "def_equidist_over_qstar"] HasEquidistributionOverQstar
attribute [gap212 "thm_ext_harman"] HarmanReduction

open Real Finset

/-! ## The two carried inputs, and the main theorems

`SieveCriterion` and `ArithmeticCertificate` are not challenge declarations; they are stated
here in the challenge's vocabulary: at `x ≥ 3`, over
`primeInterval x`, with `C` chosen after `ε₀` and `A` and before `x` and the residue class.

`ArithmeticCertificate` is discharged by `arithmeticCertificate_of_harmanReduction` below, and
`SieveCriterion` follows from `Sieve.GPYSieve` by
`Gap212.sieveCriterion_of_gpySieve_challengeShape`. -/

/-- **The arithmetic certificate at the chosen datum.** For every `ε₀ > 0` and `A > 0` there is a
`C` such that the restricted prime indicator equidistributes over the moduli `gap212Params`
generates, at every `x ≥ 3` and every residue class coprime below `x`.

This is the conclusion of the assumed Harman reduction at the datum, which is why the sequence is
`primeInterval x` and not `primeIndicator`. -/
@[gap212 "thm_arithmetic_certificate"]
def ArithmeticCertificate : Prop :=
  ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ, ∀ x ≥ (3 : ℝ), ∀ a : ℕ, CoprimeBelow a x →
    HasEquidistributionOverQstar gap212Params x ε₀ (primeInterval x) a A C

/-- **The antecedent of the Harman reduction at the chosen parameters**: every member of the
single-scale Harman class equidistributes over the moduli `gap212Params` generates, uniformly in
the class's bundle, with `C` chosen before `x`, `f` and `a`.

This is what the five equidistribution estimates and the bilinear Bombieri–Vinogradov input are
routed into: a member of the class is a convolution of one of the three shapes, and the routing
sends each shape to the estimate that covers its modulus range. -/
def HarmanClassEquidistributes : Prop :=
  ∀ K : ConstantBundle, ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ,
    ∀ x ≥ (3 : ℝ), ∀ f : ℕ → ℂ, ∀ a : ℕ,
    HarmanClass K x (19 / 50) (2 / 5) (2 / 5) f → CoprimeBelow a x →
    HasEquidistributionOverQstar gap212Params x ε₀ f a A C

/-- **The arithmetic certificate is not an independent assumption.** It is the *consequent* of the
Harman reduction at the chosen datum, so the reduction discharges it from its antecedent by
function application — `ArithmeticCertificate` and the conclusion of
`HarmanReduction gap212Params (19/50) (2/5) (2/5)` are the same proposition, quantifier for
quantifier.

That consequent *is* this assertion, and the definition of the discrepancy admits no other
reading of it. Carrying `ArithmeticCertificate`
as a hypothesis therefore assumes strictly more than `Gap212HarmanReduction`, whose antecedent
`HarmanClassEquidistributes` is derived by `Gap212.halfLevelCoverage`. -/
theorem arithmeticCertificate_of_harmanReduction (hharman : Gap212HarmanReduction)
    (hclass : HarmanClassEquidistributes) : ArithmeticCertificate :=
  hharman hclass

/-- **The sieve criterion**, in the direct-prime form: equidistribution of the restricted prime
indicator over the moduli `p_⋆` generates, together with the strict variational inequality on
`T₄₅(p_⋆)`, gives `DHL[45,2]`.

It is the Maynard–Tao sieve over the stratified support, and it is not available from
`PrimeGapsLib`, whose sieve requires `θ < 1/2` on the `ε`-enlarged simplex, precisely the two
things this method changes. Stated at `c₁ = c₂ = 0`, which `ξ₂ = 2/5` forces.

**Stated at the datum.** The statement reads "Let
`p = p_⋆` ... If a symmetric square-integrable `F` vanishing off `T₄₅(p_⋆)` satisfies
`0 < I_T(F) < 45 J_T(F)`, then `DHL[45,2]` holds". The datum is named rather than
quantified because the cap-row bound `max_j B_{j,1} < 1` that the prime-indicator hypotheses need
is not part of `Gap212.SupportParams`, and the single band is what the retreat construction behind
`Gap212.Sieve.GPYSieve` requires. Quantifying over every `p` and every `m` would assume strictly
more; the narrow form is what lets
`Gap212.sieveCriterion_of_gpySieve_challengeShape` prove it from
`Gap212.Sieve.GPYSieve`. -/
@[gap212 "thm_sieve_criterion"]
def SieveCriterion : Prop :=
  (∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ, ∀ x ≥ (3 : ℝ), ∀ a : ℕ, CoprimeBelow a x →
    HasEquidistributionOverQstar gap212Params x ε₀ (primeInterval x) a A C) →
  Certificate gap212Params 44 0 0 → DHL 45 2

/-! ## The main theorems

The bound is `212`: the diameter of `H45`, which is the dimension `Gap212Certificate` supplies.

The forms below take `SieveCriterion` and `Gap212Certificate` as hypotheses, together with either
`ArithmeticCertificate` (the `…_of_inputs` forms) or `Gap212HarmanReduction` and
`HarmanClassEquidistributes` (the `…_of_harmanReduction` forms). `Gap212HarmanReduction` and
`Gap212Certificate` are challenge hypotheses verbatim; `HarmanClassEquidistributes` is what the
challenge's five estimates and its bilinear input are routed into. The forms with exactly the
challenge file's eight hypotheses are `Gap212.primeGapLE_212_of_challenge_hypotheses` and
`Gap212.nthPrimeGapLE_212_of_challenge_hypotheses`. -/

/-- **`DHL[45,2]`** from the sieve criterion, the arithmetic certificate and the numerical
certificate. `Gap212Certificate` is `Certificate gap212Params 44 0 0`, and `44 + 1 = 45`. -/
theorem dhl45_of_inputs (hsieve : SieveCriterion) (harith : ArithmeticCertificate)
    (hcert : Gap212Certificate) : DHL 45 2 :=
  hsieve harith hcert

/-- **`H₁ ≤ 212`**, in the `nth`-prime form: `p_{n+1} - p_n ≤ 212` for arbitrarily large `n`. -/
theorem nthPrimeGapLE_212_of_inputs (hsieve : SieveCriterion) (harith : ArithmeticCertificate)
    (hcert : Gap212Certificate) : NthPrimeGapLE 212 :=
  nthPrimeGapLE_212_of_dhl (dhl45_of_inputs hsieve harith hcert)

/-- **`H₁ ≤ 212`**, in the pair form: beyond every bound there are primes `p < q` with
`q ≤ p + 212`. -/
theorem primeGapLE_212_of_inputs (hsieve : SieveCriterion) (harith : ArithmeticCertificate)
    (hcert : Gap212Certificate) : PrimeGapLE 212 :=
  primeGapLE_of_nthPrimeGapLE (nthPrimeGapLE_212_of_inputs hsieve harith hcert)

/-- **`DHL[45,2]`** from the sieve criterion, the Harman reduction with its antecedent, and the
numerical certificate — the arithmetic certificate discharged rather than assumed. -/
@[gap212 "thm_dhl45"]
theorem dhl45_of_harmanReduction (hsieve : SieveCriterion) (hharman : Gap212HarmanReduction)
    (hclass : HarmanClassEquidistributes) (hcert : Gap212Certificate) : DHL 45 2 :=
  dhl45_of_inputs hsieve (arithmeticCertificate_of_harmanReduction hharman hclass) hcert

/-- **`H₁ ≤ 212`**, in the `nth`-prime form, on the challenge's Harman hypothesis.

Two of its four hypotheses are derivable intermediates rather than the challenge file's own
assumptions: `SieveCriterion` follows from `Sieve.GPYSieve` by
`Gap212.sieveCriterion_of_gpySieve_challengeShape`, and `HarmanClassEquidistributes` follows
from the five estimates, bilinear Bombieri–Vinogradov and
the packing certificate by `Gap212.halfLevelCoverage`. The form whose hypotheses are exactly the
challenge file's eight is `Gap212.nthPrimeGapLE_212_of_challenge_hypotheses`. -/
theorem nthPrimeGapLE_212_of_harmanReduction (hsieve : SieveCriterion)
    (hharman : Gap212HarmanReduction) (hclass : HarmanClassEquidistributes)
    (hcert : Gap212Certificate) : NthPrimeGapLE 212 :=
  nthPrimeGapLE_212_of_dhl (dhl45_of_harmanReduction hsieve hharman hclass hcert)

/-- **`H₁ ≤ 212`**, in the pair form, on the challenge's Harman hypothesis: beyond every bound
there are primes `p < q` with `q ≤ p + 212`.

The form on exactly the challenge file's eight hypotheses is
`Gap212.primeGapLE_212_of_challenge_hypotheses`, for the reason given at
`Gap212.nthPrimeGapLE_212_of_harmanReduction`. -/
theorem primeGapLE_212_of_harmanReduction (hsieve : SieveCriterion)
    (hharman : Gap212HarmanReduction) (hclass : HarmanClassEquidistributes)
    (hcert : Gap212Certificate) : PrimeGapLE 212 :=
  primeGapLE_of_nthPrimeGapLE (nthPrimeGapLE_212_of_harmanReduction hsieve hharman hclass hcert)

end Gap212
