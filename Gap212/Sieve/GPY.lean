/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Harman
public meta import Gap212.Attr

/-!
# The GPY sieve criterion with a gap-bound conclusion

The sieve criterion of §3 of Stadlmann's paper concludes `H₁ ≤ H(k)`, where `H(k)` is the diameter
of the shortest admissible `k`-tuple, rather than `DHL[k,2]`.

`Gap212.Sieve.GPYCriterion` states it in that form: equidistribution of the prime indicator over
the moduli a support generates, together with the strict variational inequality on that support,
gives `p_{n+1} - p_n ≤ diam H` infinitely often for every admissible tuple `H` of the right size.
Applied to `H45`, of diameter `212` (`diameter_H45`), it gives `H₁ ≤ 212` directly.

`Gap212.Sieve.gpyCriterion_of_sieveCriterion` shows that the `DHL` form
`Gap212.SieveCriterionFamily` implies `GPYCriterion`.

## Main results

* `Gap212.Sieve.GPYCriterion`: the sieve criterion with a gap-bound conclusion.
* `Gap212.Sieve.gpyCriterion_of_sieveCriterion`: `SieveCriterionFamily → GPYCriterion`.
* `Gap212.Sieve.nthPrimeGapLE_212_of_gpy`: `H₁ ≤ 212` from the criterion.
* `Gap212.Sieve.nthPrimeGapLE_212_of_parts'`: `H₁ ≤ 212` from the criterion, the Harman reduction,
  the routing conclusion and the numerical certificate.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset

/-! ## The criterion -/

/-- **The GPY sieve criterion.** Equidistribution of the prime indicator over the moduli a
support generates, plus the strict variational inequality on that support, gives
`p_{n+1} - p_n ≤ diam H` infinitely often, for any admissible `H` of size `m + 1`.

It is stated at `c₁ = c₂ = 0`, for the prime indicator. Compare `Gap212.SieveCriterionFamily`,
which concludes `DHL[m+1,2]`, and `Gap212.Sieve.GPYSieve`, which is stated for a general minorant
`ρ` admissible for `(c₁, c₂, β, T)` and whose specialization to `1_ℙ` is
`Gap212.Sieve.dhl_of_gpySieve`. -/
def GPYCriterion : Prop :=
  ∀ (p : SupportParams) (m : ℕ) (H : Finset ℕ), #H = m + 1 → H.Admissible →
    HasEquidistributionOverQstarFamily p primeIndicatorFamily → Certificate p m 0 0 →
      NthPrimeGapLE H.diameter

/-- `Gap212.SieveCriterionFamily` implies `Gap212.Sieve.GPYCriterion`: `DHL[m+1,2]` for an
admissible tuple `H` gives the gap bound `diam H` infinitely often. -/
theorem gpyCriterion_of_sieveCriterion (h : SieveCriterionFamily) : GPYCriterion := by
  intro p m H hcard hadm harith hcert
  have himg := H.image_orderEmbOfFin_univ hcard
  have hmono := (H.orderEmbOfFin hcard).strictMono
  have h' := nthPrimeGapLE_of_dhl (by lia) _ hmono.injective
    (h p m harith hcert _ hmono (by rwa [himg]))
  rwa [himg] at h'

/-! ## `H₁ ≤ 212`, from the weaker criterion -/

/-- **`H₁ ≤ 212` from the GPY criterion, the arithmetic certificate and the numerical
certificate**, by applying the criterion to `H45`, of diameter `212`. -/
theorem nthPrimeGapLE_212_of_gpy (hgpy : GPYCriterion) (harith : ArithmeticCertificateFamily)
    (hcert : Gap212Certificate) : NthPrimeGapLE 212 := by
  have h := hgpy gap212Params 44 H45 card_H45 admissible_H45 harith hcert
  rwa [diameter_H45] at h

/-- `H₁ ≤ 212` in the pair form `Gap212.PrimeGapLE 212`, from the same hypotheses as
`Gap212.Sieve.nthPrimeGapLE_212_of_gpy`. -/
theorem primeGapLE_212_of_gpy (hgpy : GPYCriterion) (harith : ArithmeticCertificateFamily)
    (hcert : Gap212Certificate) : PrimeGapLE 212 :=
  primeGapLE_of_nthPrimeGapLE (nthPrimeGapLE_212_of_gpy hgpy harith hcert)

/-- **`H₁ ≤ 212` from the GPY criterion, the Harman reduction, the routing conclusion and the
numerical certificate.** This is `Gap212.Harman.nthPrimeGapLE_212_of_parts` with
`Gap212.SieveCriterionFamily` replaced by the weaker `Gap212.Sieve.GPYCriterion`. -/
theorem nthPrimeGapLE_212_of_parts' {ξ₁ ξ₂ ξ₃ : ℝ}
    (hgpy : GPYCriterion)
    (hharman : Harman.HarmanReductionFamily gap212Params ξ₁ ξ₂ ξ₃)
    (hroute : Harman.RoutingConclusionFamily gap212Params ξ₁ ξ₂ ξ₃)
    (hcert : Gap212Certificate) :
    NthPrimeGapLE 212 :=
  nthPrimeGapLE_212_of_gpy hgpy (Harman.arithmeticCertificate_of_routingFamily hharman hroute) hcert

end Gap212.Sieve
