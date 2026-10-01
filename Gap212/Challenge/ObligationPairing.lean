/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Challenge.ChallengePairing
public import Gap212.Packing.PackingCertificateProof
public import Gap212.Sieve.Polymath41CloseTotient
public import Gap212.Sieve.CriterionAssembly
public meta import Gap212.Attr

/-!
# The challenge file's conclusions, from proved inputs only

`Gap212.primeGapLE_212_of_challenge_inputs` takes the challenge file's eight hypotheses plus
`Gap212.ChallengeResidual`, an opaque two-field bundle. This module proves `ChallengeResidual`
outright (`Gap212.challengeResidual`, which takes no hypotheses), so the challenge file's
two conclusions follow from exactly its eight hypotheses.

## The chain, and where it bottoms out

The residual is discharged in two steps:

* `Gap212.routingObligation_of_certificate : PackingCertificate → RoutingObligation` — the routing
  field, from the packing certificate alone, which is Condition D on the single band
  `4/625 < ω₀ ≤ ω(1,1)`.
* `Gap212.sieveCriterion_of_gpySieve_challengeShape : Sieve.GPYSieve → SieveCriterion` — the sieve
  field, from `Gap212.Sieve.GPYSieve` alone.

`GPYSieve` is itself a theorem: `Gap212.Sieve.gpySieve_of_obligations` derives it from
`NuDenominator` and `NumeratorAsymptotic`, the tensor data coming from
`Gap212.Sieve.sieveWeights`. The three inputs the chain reaches are all theorems:

* `Sieve.NuDenominator 45` is `Gap212.Sieve.nuDenominator_45` and `Sieve.NumeratorAsymptotic 44` is
  `Gap212.Sieve.numeratorAsymptotic_44` — the two sieve obligations, at the two instances the
  assembly consumes. They are `Gap212.Sieve.nuDenominator_of_polymath41Recip` and
  `Gap212.Sieve.numeratorAsymptotic_of_polymath41Totient` at the proved
  `Gap212.Sieve.polymath41Recip` and `Gap212.Sieve.polymath41Totient`, Polymath8b's Lemma 4.1 at
  `k = 1, N = 1` in the reciprocal and totient kernels;
* `PackingCertificate` is `Gap212.packingCertificate_at_datum`. All
  91 cells of the band are certified, the transposed pairs by a proved transport rather than by
  mirroring.

`Gap212.Sieve.sieveWeights` is the composition of `Gap212.GPY.exists_retreat_gap` and
`Gap212.GPY.exists_tensorDatum_forms_gap`, so `Sieve.SieveWeights` is not a hypothesis.

## `Sieve.NuDenominatorUnrestricted` is false

`Sieve.NuDenominatorUnrestricted` quantifies over a bare family of profiles with no regularity at
all, and `Gap212.Sieve.not_nuDenominatorUnrestricted` refutes it at the indicator of `{0}`, where
every `lambdaF` is `1`, so `∑ν` counts the residue class, while every Gram entry is `0`, so the
main term is `0`.

So `Sieve.NuDenominator` is stated at a `Gap212.GPY.TensorDatum` with `ε₀ ∈ (0,1)` and a strictly
increasing tuple: `ν` is the tensor sieve weight of a tensor datum at level `ε₀`, and a tensor
datum carries smoothness and support. The refuting profile is not a tensor datum, and the clause
it fails is `Gap212.GPY.TensorDatum.smooth` (`Gap212.Sieve.tensorDatum_f_ne_spike`) — not
`compactSupport`, which it satisfies, and not the retreat clause, which it satisfies at every band.

`Gap212.Sieve.ratio_exceeds_one` and `Gap212.Sieve.dhl_of_tensorData` take the datum they are
applied to, and `Gap212.Sieve.gpySieve_of_obligations` uses the `0 < ε₀` and `ε₀ < 1` that
`Gap212.Sieve.sieveWeights` hands it.

`Sieve.NumeratorAsymptotic` is stated at the datum too, and `Gap212.Sieve.ratio_exceeds_one`
consumes both at the one datum it has in hand. The refuting profile does not touch the one-sided
numerator bound, because such profiles send `∑ᵢ𝓙ᵢ` to `0` as well
(`Gap212.Sieve.le_numerator_at_spike`, `formJMarginal_eq_zero_of_gramInnerSkip_zero`), leaving the
bound trivially true.

## The eight hypotheses

`Gap212.primeGapLE_212_of_challenge_hypotheses` and
`Gap212.nthPrimeGapLE_212_of_challenge_hypotheses` take exactly the challenge file's eight
hypotheses: `TypeIIPolymath`, `TypeIbPolymath`, `TypeIBakerIrving`, `TypeIStadlmann`,
`TypeIIIPolymath`, `Gap212HarmanReduction`, `BilinearBombieriVinogradov` and `Gap212Certificate`,
all declared in `Gap212.Definitions` under the challenge file's names.

## The statements without their hypotheses are refuted

* `Sieve.LcmGramSumLimit` is refuted by `Gap212.Sieve.not_lcmGramSumLimit`; the form stated on a
  support is `Sieve.LcmGramSumLimitOfSupport`.
* `Sieve.TotientGramSumLimit` is refuted by `Gap212.Sieve.not_totientGramSumLimit`; the form stated
  on a support is `Sieve.TotientGramSumLimitOfSupport`.
* `Sieve.SieveAsymptoticUnrestricted`, the `Prop` without its hypotheses, is refuted by
  `Gap212.Sieve.not_sieveAsymptotic_one`. The marginal-region clause the asymptotics carries is
  discharged from `𝓛`-membership by the numerator's own proof, and never from the retreat
  clause.

## Both Gram limits are stated at `C^∞`

`Sieve.LcmGramSumLimitOfSupport` and `Sieve.TotientGramSumLimitOfSupport` are stated at
`ContDiff ℝ (⊤ : ℕ∞)`: both chains end at a `Gap212.GPY.TensorDatum`, whose `smooth` field is
`ContDiff ℝ (⊤ : ℕ∞)`. This asks **more** of the profiles, so each `Prop` ranges over fewer of them
and is weaker — the same kind of narrowing as `β ≥ 1` on the two sieving errors.
`Sieve.SieveAsymptotic` is narrowed with them, being produced from the totient one.

Two things this buys. The regularity is `C^∞` where Polymath8b Lemma 4.1 — the source result both
obligations are instances of at `k = 1, N = 1` — states it, so
`Gap212.Sieve.nuDenominator_of_polymath41Recip` and
`Gap212.Sieve.numeratorAsymptotic_of_polymath41Totient` carry no regularity discrepancy against
the source at all. And the source's Fourier route is available: at `C¹` the transform of `e^tF(t)`
is merely `o(1/|ξ|)` and Mathlib's inversion theorem carries `Integrable (𝓕 f)` as a hypothesis,
while at `C^∞` it is rapidly decaying and that hypothesis is free.

There are two Gram limits, one per kernel, threaded separately. They are not interchangeable — the
reciprocal kernel weights by `μ²(e)/φ(e)` with constant `φ(W)/W` and no correction product, the
totient one by `μ²(e)/(μ*φ)(e)` with the correction `(∏_{p∤W}(1-1/(p-1)²))^{-1}` and an oddness
condition, `(μ*φ)(2) = 0`.

## Main results

* `Gap212.challengeResidual`: `Gap212.ChallengeResidual` holds.
* `Gap212.primeGapLE_212_of_challenge_hypotheses`,
  `Gap212.nthPrimeGapLE_212_of_challenge_hypotheses`: the challenge file's `thm_main` and
  `thm_nth`, from its eight hypotheses.
-/

@[expose] public section

namespace Gap212

/-- **The challenge residual holds.** `Gap212.ChallengeResidual`, with no hypotheses: its sieve
field from the theorems `Sieve.nuDenominator_45` and `Sieve.numeratorAsymptotic_44`, its routing
field from `Gap212.packingCertificate_at_datum`.

`Sieve.NuDenominator` is stated at a tensor datum; the unrestricted form,
`Sieve.NuDenominatorUnrestricted`, is refuted; see the module docstring. -/
theorem challengeResidual : ChallengeResidual :=
  challengeResidual_of_gpySieve_packing
    (Sieve.gpySieve_of_obligations Sieve.nuDenominator_45 Sieve.numeratorAsymptotic_44)
    packingCertificate_at_datum

/-- **The challenge file's `thm_nth`, from its eight hypotheses.**

`NthPrimeGapLE 212` unfolds to the challenge file's
`∀ n₀, ∃ n ≥ n₀, (n+1).nth Nat.Prime ≤ n.nth Nat.Prime + 212`.

Unlike `Gap212.nthPrimeGapLE_212_of_harmanReduction`, whose hypotheses `SieveCriterion` and
`HarmanClassEquidistributes` are derived here — the first from `Sieve.GPYSieve`, the second from
the five estimates, bilinear Bombieri–Vinogradov and the packing certificate — this takes exactly
the challenge file's eight hypotheses. -/
@[gap212 "thm_nth"]
theorem nthPrimeGapLE_212_of_challenge_hypotheses (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath)
    (h₃ : TypeIBakerIrving) (h₄ : TypeIStadlmann) (h₅ : TypeIIIPolymath)
    (hharman : Gap212HarmanReduction) (hbv : BilinearBombieriVinogradov)
    (hcert : Gap212Certificate) :
    NthPrimeGapLE 212 :=
  nthPrimeGapLE_212_of_challenge_inputs challengeResidual
    h₁ h₂ h₃ h₄ h₅ hharman hbv hcert

/-- **The challenge file's `thm_main`, from its eight hypotheses.**

`PrimeGapLE 212` unfolds to the challenge file's
`∀ n₀, ∃ p q, n₀ ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q ≤ p + 212`.

Stated on the challenge file's own hypotheses, for the reason given at
`Gap212.nthPrimeGapLE_212_of_challenge_hypotheses`. -/
@[gap212 "thm_main"]
theorem primeGapLE_212_of_challenge_hypotheses (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath)
    (h₃ : TypeIBakerIrving) (h₄ : TypeIStadlmann) (h₅ : TypeIIIPolymath)
    (hharman : Gap212HarmanReduction) (hbv : BilinearBombieriVinogradov)
    (hcert : Gap212Certificate) :
    PrimeGapLE 212 :=
  primeGapLE_212_of_challenge_inputs challengeResidual
    h₁ h₂ h₃ h₄ h₅ hharman hbv hcert

end Gap212
