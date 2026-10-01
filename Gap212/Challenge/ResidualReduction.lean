/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Challenge.Pairing
public import Gap212.Packing.PackingCertificate
public import Gap212.Routing.HalfLevelAtScale
public meta import Gap212.Attr

/-!
# The challenge residual from Condition D at the datum

`Gap212.ChallengeResidual` has two fields, `sieve : SieveCriterion` and
`routing : RoutingObligation`. This module derives the routing field from Condition D at the datum
on the full chamber `0 ≤ ω₀ ≤ ω(1,1)`, and the whole residual from that and the sieve criterion.

## The routing field

`Gap212.routingObligation_of_conditionD` proves `RoutingObligation` from Condition D at the datum
on the full chamber, and nothing else: the five estimates and bilinear Bombieri–Vinogradov give
`Gap212.HarmanClassEquidistributes` through the routing at one `x`. Condition D on the full chamber
follows from `Gap212.PackingCertificate` by `Gap212.conditionD_at_datum`, which proves `[0, 4/625]`
from seven bands and takes only `4/625 < ω₀ ≤ ω(1,1)` from the certificate.

The A, A′, B, C and E conditions do not arise on this route.

## Main results

* `Gap212.routingObligation_of_packingCertificate`: the routing field, from Condition D at the
  datum on the full chamber.
* `Gap212.challengeResidual_of_sieve_and_certificate`: the whole residual, from the sieve criterion
  and Condition D at the datum on the full chamber.
-/

@[expose] public section

namespace Gap212

open Gap212.Bridges Gap212.Defs Gap212.Packing

/-- **The routing obligation, from Condition D at the datum on the full chamber.** Condition D
for every pair of bands `j, j'` and every pair of indices `m, m'`, with the chamber at
`omegaMax gap212Params j j'`, gives `Gap212.RoutingObligation`. -/
theorem routingObligation_of_packingCertificate
    (hcert : ∀ (j j' : Fin gap212Params.n) (m m' : ℕ),
      Defs.ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
        capD (chamberD (omegaMax gap212Params j j') (omegaMax gap212Params j j'))) :
    RoutingObligation := by
  refine routingObligation_of_conditionD fun j j' m m' ↦ ?_
  have hcap : capCondD gap212Params = capD := capCondD_gap212Params
  have hch : chamberCondD gap212Params (2 / 5) (omegaMax gap212Params j j')
      (omegaMax gap212Params j j') = chamberD (omegaMax gap212Params j j')
        (omegaMax gap212Params j j') := chamberCondD_gap212Params _ _
  rw [hcap, hch]
  exact hcert j j' m m'

/-- **The whole residual, from the sieve criterion and Condition D at the datum.** The routing
field is `Gap212.routingObligation_of_packingCertificate`. -/
theorem challengeResidual_of_sieve_and_certificate (hsieve : SieveCriterion)
    (hcert : ∀ (j j' : Fin gap212Params.n) (m m' : ℕ),
      Defs.ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
        capD (chamberD (omegaMax gap212Params j j') (omegaMax gap212Params j j'))) :
    ChallengeResidual :=
  ⟨hsieve, routingObligation_of_packingCertificate hcert⟩

end Gap212
