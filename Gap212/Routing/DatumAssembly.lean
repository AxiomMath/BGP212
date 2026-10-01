/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.ContinuumPacking
public import Gap212.Routing.HalfLevelAtScale
public meta import Gap212.Attr

/-!
# The routing results at the datum

`Gap212.harmanAntecedent_of_conditionD` and
`Gap212.halfLevelCoverage_of_conditionD` carry Condition D
at `p_⋆` as a hypothesis. Condition D at the datum is exactly what the continuum packing
condition supplies, and `Gap212.conditionD_at_datum_all` derives it from the packing certificate.

The two results are therefore restated here with the certificate in place of Condition D. Nothing
new is proved; this is the composition.

## Main results

* `Gap212.harmanAntecedent`: the Harman antecedent at `p_⋆`.
* `Gap212.halfLevelCoverage`: coverage at the half level, whose conclusion is
  `Gap212.HarmanClassEquidistributes`.
-/

@[expose] public section

namespace Gap212

open Gap212.Bridges Gap212.Defs Gap212.Packing

open Classical in
/-- **The Harman antecedent above the half level** at `p_⋆` and `(ξ₁,ξ₂,ξ₃) = (19/50, 2/5, 2/5)`,
from the five estimates and the packing certificate.

The certificate stands where the continuum packing condition is needed; every other
hypothesis is a theorem proved at this datum. -/
@[gap212 "thm_harman_antecedent"]
theorem harmanAntecedent (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath) (h₃ : TypeIBakerIrving)
    (h₄ : TypeIStadlmann) (h₅ : TypeIIIPolymath) (hcert : PackingCertificate)
    (K : ConstantBundle) :
    ∀ ε₀ > (0 : ℝ), ∃ ε₁ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ,
      ∀ x ≥ (3 : ℝ), ∀ f : ℕ → ℂ, ∀ a : ℕ,
        HarmanClass K x (19 / 50) (2 / 5) (2 / 5) f → CoprimeBelow a x →
        HasEquidistribution x
          {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar gap212Params x ε₀ ∧ x ^ (1 / 2 - ε₁) < (q : ℝ)}
          f a A C :=
  harmanAntecedent_of_conditionD h₁ h₂ h₃ h₄ h₅
    (fun j j' m m' ↦ by
      have h := conditionD_at_datum_all hcert j j' m m'
      rwa [capCondD_gap212Params, chamberCondD_gap212Params] at *) K

/-- **Coverage at the half level**: the five estimates, bilinear Bombieri–Vinogradov and the
packing certificate give `Gap212.HarmanClassEquidistributes`.

This is what the challenge residual's routing field turns on: its conclusion is exactly the
antecedent of `Gap212.Gap212HarmanReduction`, so with it the reduction discharges
`Gap212.ArithmeticCertificate`. -/
@[gap212 "thm_half_level_coverage"]
theorem halfLevelCoverage (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath) (h₃ : TypeIBakerIrving)
    (h₄ : TypeIStadlmann) (h₅ : TypeIIIPolymath) (hbv : BilinearBombieriVinogradov)
    (hcert : PackingCertificate) : HarmanClassEquidistributes :=
  halfLevelCoverage_of_conditionD h₁ h₂ h₃ h₄ h₅ hbv
    (fun j j' m m' ↦ conditionD_at_datum_all hcert j j' m m')

/-- **The routing obligation from the certificate alone.** -/
theorem routingObligation_of_certificate (hcert : PackingCertificate) : RoutingObligation :=
  fun h₁ h₂ h₃ h₄ h₅ hbv ↦ halfLevelCoverage h₁ h₂ h₃ h₄ h₅ hbv hcert

end Gap212
