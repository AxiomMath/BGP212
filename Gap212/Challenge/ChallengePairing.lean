/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Challenge.ResidualReduction
public import Gap212.Routing.DatumAssembly
public import Gap212.Sieve.CriterionAtScale
public meta import Gap212.Attr

/-!
# The pairing, on the challenge's hypotheses and two named inputs

`Gap212.primeGapLE_212_of_challenge_inputs` takes the challenge file's eight hypotheses plus
`Gap212.ChallengeResidual`, a two-field bundle. Here the residual is derived from two named
inputs:

* `Gap212.Sieve.GPYSieve` — the Maynard–Tao sieve over the stratified support;
* `Gap212.PackingCertificate` — Condition D at the datum
  on the band `4/625 < ω₀ ≤ ω(1,1)`.

## What each replaces

`Gap212.sieveCriterion_of_gpySieve_challengeShape` discharges the `sieve` field from the first.
Both antecedents fix `C` before `x`, `Gap212.sumError_primeInterval_eq_sumErrorDyadic` identifies
the summands, and the difference between `∀ x ≥ 3` and `∀ x > 1` is absorbed by enlarging the
constant over a range where at most two moduli and four dyadic integers occur.

`Gap212.routingObligation_of_certificate` discharges the `routing` field from the second, which
supplies Condition D above `ω₀ = 4/625`.

## Main results

* `Gap212.primeGapLE_212_of_gpySieve_packing`, `nthPrimeGapLE_212_of_gpySieve_packing`: the
  challenge file's two conclusions, from its eight hypotheses and those two inputs.
-/

@[expose] public section

namespace Gap212

/-- **The challenge residual, from two named inputs.** `Gap212.ChallengeResidual` from
`Sieve.GPYSieve` and `Gap212.PackingCertificate`. -/
theorem challengeResidual_of_gpySieve_packing (hgpy : Sieve.GPYSieve)
    (hcert : PackingCertificate) : ChallengeResidual :=
  ⟨sieveCriterion_of_gpySieve_challengeShape hgpy, routingObligation_of_certificate hcert⟩

/-- **The challenge file's `thm_nth`**, from its eight hypotheses and the two named inputs.

The eight are `Gap212Challenge/Basic.lean`'s, in its order. `NthPrimeGapLE 212` unfolds to its
`∀ n₀, ∃ n ≥ n₀, (n+1).nth Nat.Prime ≤ n.nth Nat.Prime + 212`. -/
theorem nthPrimeGapLE_212_of_gpySieve_packing (hgpy : Sieve.GPYSieve)
    (hcert : PackingCertificate)
    (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath) (h₃ : TypeIBakerIrving)
    (h₄ : TypeIStadlmann) (h₅ : TypeIIIPolymath) (hharman : Gap212HarmanReduction)
    (hbv : BilinearBombieriVinogradov) (hnum : Gap212Certificate) :
    NthPrimeGapLE 212 :=
  nthPrimeGapLE_212_of_challenge_inputs
    (challengeResidual_of_gpySieve_packing hgpy hcert) h₁ h₂ h₃ h₄ h₅ hharman hbv hnum

/-- **The challenge file's `thm_main`**, from its eight hypotheses and the two named inputs.

`PrimeGapLE 212` unfolds to its
`∀ n₀, ∃ p q, n₀ ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q ≤ p + 212`. -/
theorem primeGapLE_212_of_gpySieve_packing (hgpy : Sieve.GPYSieve)
    (hcert : PackingCertificate)
    (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath) (h₃ : TypeIBakerIrving)
    (h₄ : TypeIStadlmann) (h₅ : TypeIIIPolymath) (hharman : Gap212HarmanReduction)
    (hbv : BilinearBombieriVinogradov) (hnum : Gap212Certificate) :
    PrimeGapLE 212 :=
  primeGapLE_212_of_challenge_inputs
    (challengeResidual_of_gpySieve_packing hgpy hcert) h₁ h₂ h₃ h₄ h₅ hharman hbv hnum

end Gap212
