/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.DatumConditionD
public import Gap212.Packing.DatumConditionE
public import Gap212.Packing.DatumConditions
public meta import Gap212.Attr

/-!
# The packing certificates at the chosen datum

On a single cell of the subdivision, `Gap212.Packing.forall_affine_nonneg_iff_exists_dual_or_farkas`
shows that a bin inequality holds exactly when a rational dual vector, or a Farkas vector proving
the cell empty, exists. So "every cell admits certifying data" and "the condition holds on every
cell" are the same assertion, and the packing certificate is stated as the condition itself at
`p_⋆`.

## What this definition contains

This definition is Condition D on one band: a single `Gap212.Defs.ConditionD` over
`Gap212.chamberDBand` at `4/625 < ω₀ ≤ ω(1,1)`. Conditions A, A′, B, C and E are not part of it,
because they are theorems: `Gap212.conditionA_at_datum`,
`conditionA_high_at_datum`, `conditionB_at_datum`, `conditionC_at_datum` and `conditionE_at_datum`,
proved by uniform arguments in the larger rough count with no subdivision at all, and bundled as
`Gap212.uniformConditions_at_datum`. `Gap212.packingCertificate_of_conditions`, in
`Gap212.Packing.ContinuumPacking` — it needs `Gap212.conditionD_at_datum`, which is downstream
of this file — puts the six back together with only this band taken from the certificate.

Condition D at this datum is proved separately, for every cell and every `γ`, on `0 ≤ ω₀ ≤ 4/625` —
`Gap212.conditionD_at_datum_low_level` on `[0, 7/10000]`, `Gap212.conditionD_at_datum_mid_band` on
`(7/10000, 1/400]`, `Gap212.conditionD_at_datum_band_2` on `(1/400, 1/250]`,
`Gap212.conditionD_at_datum_band_3` on `(1/250, 43/10000]`, `Gap212.conditionD_at_datum_band_4` on
`(43/10000, 13/2500]`, `Gap212.conditionD_at_datum_band_5` on `(13/2500, 541/100000]` and
`Gap212.conditionD_at_datum_band_6` on `(541/100000, 4/625]` — which is `32/35` of the chamber
`[0, 7/1000]`. `Gap212.packingCertificate_at_datum` proves the rest, cell by cell.

What defeats the argument above `4/625` is the size of the reserve. The three-block capacity is
`c₁ + c₂ + c₃ = 1/2 - δ - 6ω₀ - 3ϵ`, which at `ω₀ = ω(1,1) = 7/1000` is `0.4416`: only `0.0092`
above the pooled mass `1081/2500 = 0.4324`, and that is less than the floor `δ = 0.0164` on a
single coordinate. So no argument that parks one coordinate in the third block and fills the second
by subset sum can reach the top of the chamber; the fourth block must carry mass too, and
`c₄ = 8ω₀` is below the largest coordinate a rough side can hold (`B_{1,10} - 9δ = 0.0686`), so
which coordinates fit in it depends on the profile and not only on the cell. That is exactly the
cell-and-profile subdivision the certificates encode.

## Main definitions

* `Gap212.PackingCertificate`: Condition D at `p_⋆` on the band `4/625 < ω₀ ≤ ω(1,1)`.

## Main results

* `Gap212.uniformConditions_at_datum`: Conditions A, A′, B, C and E, all theorems at the datum.
-/

@[expose] public section

namespace Gap212

open Gap212.Bridges Gap212.Defs Gap212.Packing

/-- **The Type IIc packing above the level `4/625` at `p_⋆`.** Condition D on the band
`4/625 < ω₀ ≤ ω(1,1)`, at the datum's own `B` row and `δ` and at the level of its only band pair.

Conditions A, A′, B, C and E, and Condition D on `[0, 4/625]`, are proved separately at the datum;
`Gap212.packingCertificate_at_datum` proves this band cell by cell. -/
@[gap212 "thm_ext_packing_certificate"]
def PackingCertificate : Prop :=
  ∀ (j j' : Fin gap212Params.n) (m m' : ℕ),
    m ≤ ⌊1 / gap212Params.δ⌋₊ → m' ≤ ⌊1 / gap212Params.δ⌋₊ →
    Gap212.Defs.ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      capD (chamberDBand (omegaMax gap212Params j j') (4 / 625)
        (omegaMax gap212Params j j'))

/-- **The five uniform conditions at `p_⋆`, as one bundle.** Conditions A, A′, B, C and E, each at
the datum's capacities. Every component is a theorem proved at the datum. -/
theorem uniformConditions_at_datum (j j' : Fin gap212Params.n) {m m' : ℕ}
    (hm : m ≤ ⌊1 / gap212Params.δ⌋₊) (hm' : m' ≤ ⌊1 / gap212Params.δ⌋₊) :
    Gap212.Defs.ConditionA (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
        (19 / 50 - 2 * slack) (1 / 6 - 4 * omegaMax gap212Params j j' - 2 * slack) ∧
    Gap212.Defs.ConditionAHigh
        (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
        (1 / 2 - 2 * omegaMax gap212Params j j' - 2 * slack)
        (1 / 14 - 68 * omegaMax gap212Params j j' / 14 - 2 * slack) ∧
    Gap212.Defs.ConditionB (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
        (2 / 5 + 24 * omegaMax gap212Params j j' / 5 + 7 * gap212Params.δ / 5 - 2 * slack)
        (1 / 14 - 24 * omegaMax gap212Params j j' / 7 - 2 * slack) ∧
    Gap212.Defs.ConditionC (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
        (1 / 3 + 8 * omegaMax gap212Params j j' + 7 * gap212Params.δ / 3 - 4 * slack)
        (1 / 10 - 34 * omegaMax gap212Params j j' / 5 - 7 * gap212Params.δ / 5 - 4 * slack)
        (2 * omegaMax gap212Params j j' + gap212Params.δ - 4 * slack) ∧
    Gap212.Defs.ConditionE (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
        (1 - 6 * omegaMax gap212Params j j' - 3 * (2 / 5 : ℝ) / 2 - 8 * slack / 3)
        (5 * omegaMax gap212Params j j' / 2 + 3 * (2 / 5 : ℝ) / 8 - 2 * slack) :=
  ⟨conditionA_at_datum rfl rfl j j' m m', conditionA_high_at_datum rfl j j' m m',
    conditionB_at_datum rfl j j' m m', conditionC_at_datum rfl j j' m m',
    conditionE_at_datum j j' rfl hm hm'⟩

end Gap212
