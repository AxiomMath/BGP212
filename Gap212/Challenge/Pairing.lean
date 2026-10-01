/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Equidistribution.Estimates.Assumed
public import Gap212.Harman.Challenge
public meta import Gap212.Attr

/-!
# Pairing the challenge file with the development

`Gap212Challenge/Basic.lean` states its two objectives from eight hypotheses: the five
equidistribution estimates, the Harman reduction, bilinear Bombieri–Vinogradov, and the numerical
certificate. This module proves the two conclusions from those eight hypotheses and one named
residual, `Gap212.ChallengeResidual`.

## The residual

`Gap212.ChallengeResidual` has two fields.

* `Gap212.SieveCriterion` — the Maynard–Tao sieve over the stratified support.
  `Gap212.sieveCriterion_of_gpySieve_challengeShape` derives it from `Gap212.Sieve.GPYSieve` alone,
  and `Gap212.primeGapLE_212_of_gpySieve_packing` is the pairing stated on that instead of this
  field.

  The transfer from `Gap212.SieveCriterionFamily` is not the hard direction: both antecedents fix
  the constant before `x`, and the summands are equal on the nose by
  `Gap212.sumError_primeInterval_eq_sumErrorDyadic` with `primeIndicatorFamily n x` defeq
  `primeIndicator n`. The only real difference is `∀ x ≥ 3` against `∀ x > 1`, and that range is
  free: below `3` at most two moduli occur and `dyadic x` has at most four elements, so the sum is
  under `16`, while `c·x/(log x)^A` is at least `c/(log 3)^A` — enlarging `c` to
  `max C (16·(log 3)^A)` covers it.
* `Gap212.RoutingObligation` — the five estimates and bilinear Bombieri–Vinogradov give
  `Gap212.HarmanClassEquidistributes`. `Gap212.routingObligation_of_certificate` derives it from
  `Gap212.PackingCertificate`.

`Gap212.challengeResidual` proves `Gap212.ChallengeResidual` with no hypotheses.

`Gap212.ArithmeticCertificate` is not a field: it is the consequent of the Harman reduction,
discharged by `Gap212.arithmeticCertificate_of_harmanReduction`.

## The conclusions

`Gap212.PrimeGapLE 212` unfolds to the challenge's
`∀ n₀, ∃ p q, n₀ ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q ≤ p + 212`, and `Gap212.NthPrimeGapLE 212` to
`∀ n₀, ∃ n ≥ n₀, (n+1).nth Nat.Prime ≤ n.nth Nat.Prime + 212`.

## Main results

* `Gap212.primeGapLE_212_of_challenge_inputs`, `Gap212.nthPrimeGapLE_212_of_challenge_inputs`:
  the challenge file's eight hypotheses, plus the residual, give its two conclusions.
-/

@[expose] public section

namespace Gap212

/-! ## The residual -/

/-- **The routing obligation.** The five equidistribution estimates and bilinear
Bombieri–Vinogradov together give the antecedent of the Harman reduction at the chosen datum:
every member of the single-scale Harman class equidistributes over the moduli `gap212Params`
generates. -/
def RoutingObligation : Prop :=
  TypeIIPolymath → TypeIbPolymath → TypeIBakerIrving → TypeIStadlmann → TypeIIIPolymath →
    BilinearBombieriVinogradov → HarmanClassEquidistributes

/-- **The challenge residual.** The sieve criterion `Gap212.SieveCriterion` and the routing
obligation `Gap212.RoutingObligation`, together. -/
structure ChallengeResidual : Prop where
  /-- The Maynard–Tao sieve over the stratified support. -/
  sieve : SieveCriterion
  /-- The five estimates and bilinear Bombieri–Vinogradov give the Harman antecedent. -/
  routing : RoutingObligation

/-! ## The pairing -/

/-- **The challenge file's `thm_nth`, from the development.** The eight hypotheses are the
challenge file's, in its order; `hres` is the residual.

`NthPrimeGapLE 212` unfolds to the challenge's
`∀ n₀, ∃ n ≥ n₀, (n+1).nth Nat.Prime ≤ n.nth Nat.Prime + 212`. -/
theorem nthPrimeGapLE_212_of_challenge_inputs (hres : ChallengeResidual)
    (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath) (h₃ : TypeIBakerIrving)
    (h₄ : TypeIStadlmann) (h₅ : TypeIIIPolymath) (hharman : Gap212HarmanReduction)
    (hbv : BilinearBombieriVinogradov) (hcert : Gap212Certificate) :
    NthPrimeGapLE 212 :=
  nthPrimeGapLE_212_of_harmanReduction hres.sieve hharman
    (hres.routing h₁ h₂ h₃ h₄ h₅ hbv) hcert

/-- **The challenge file's `thm_main`, from the development.** The pair form, by
`Gap212.primeGapLE_of_nthPrimeGapLE`.

`PrimeGapLE 212` unfolds to the challenge's
`∀ n₀, ∃ p q, n₀ ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q ≤ p + 212`. -/
theorem primeGapLE_212_of_challenge_inputs (hres : ChallengeResidual)
    (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath) (h₃ : TypeIBakerIrving)
    (h₄ : TypeIStadlmann) (h₅ : TypeIIIPolymath) (hharman : Gap212HarmanReduction)
    (hbv : BilinearBombieriVinogradov) (hcert : Gap212Certificate) :
    PrimeGapLE 212 :=
  primeGapLE_of_nthPrimeGapLE
    (nthPrimeGapLE_212_of_challenge_inputs hres h₁ h₂ h₃ h₄ h₅ hharman hbv hcert)

end Gap212
