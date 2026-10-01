/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Consequences.CheckSetEmptyAboveThirteen
public import Gap212.Packing.DatumConditionDPairs
public import Gap212.Packing.PackingCertificate
public meta import Gap212.Attr

/-!
# Condition D at the datum

Condition D at `p_⋆` holds on the whole chamber `0 ≤ ω₀ ≤ ω(1,1)`: seven bands below
`ω₀ = 4/625` are proved by arguments uniform in the cell, and the band above is
`Gap212.PackingCertificate`. The theorems here take the certificate as a hypothesis and assemble
the chamber.

## The bands

`Gap212.PackingCertificate` is Condition D on the band `4/625 < ω₀ ≤ ω(1,1)` and nothing else, and
`Gap212.packingCertificate_at_datum` proves it. Conditions A, A′, B, C and E are
`Gap212.uniformConditions_at_datum`, and `Gap212.packingCertificate_of_conditions` below puts the
six together with only the band taken from the certificate. Condition D on `0 ≤ ω₀ ≤ 4/625` is
proved without it:
`Gap212.conditionD_at_datum_low_level` on `[0, 7/10000]`,
`Gap212.conditionD_at_datum_mid_band` on `(7/10000, 1/400]`,
`Gap212.conditionD_at_datum_band_2` on `(1/400, 1/250]`,
`Gap212.conditionD_at_datum_band_3` on `(1/250, 43/10000]`,
`Gap212.conditionD_at_datum_band_4` on `(43/10000, 13/2500]`,
`Gap212.conditionD_at_datum_band_5` on `(13/2500, 541/100000]` and
`Gap212.conditionD_at_datum_band_6` on `(541/100000, 4/625]` — the first three uniform in the cell,
the next two reading each branch's floor one side at a time, the sixth reading the level as the
integer it is, the last running its dichotomy on pairs rather than singletons. What the certificate
supplies is the remaining `4/625 < ω₀ ≤ 7/1000`.

## Main results

* `Gap212.conditionD_at_datum`: Condition D at `p_⋆` on the full chamber, from the certificate.
* `Gap212.conditionD_at_datum_all`: the same at every `m, m'`, the check set being empty above 13.
* `Gap212.packingCertificate_of_conditions`: the six conditions at `p_⋆`, with only Condition D
  on `(4/625, ω(1,1)]` taken from the certificate.
-/

@[expose] public section

namespace Gap212

open Gap212.Bridges Gap212.Defs Gap212.Packing

/-- **Condition D at the datum**, on the whole chamber `0 ≤ ω₀ ≤ ω(1,1)`, from the packing
certificate on the band above `ω₀ = 4/625` together with the seven bands proved below it.

`Gap212.PackingCertificate` is exactly the band `4/625 < ω₀ ≤ ω(1,1)`, so this composition is where
the eight pieces of the chamber meet: `Gap212.conditionD_at_datum_low_level` supplies
`[0, 7/10000]`, `Gap212.conditionD_at_datum_mid_band` supplies `(7/10000, 1/400]`,
`Gap212.conditionD_at_datum_band_2` supplies `(1/400, 1/250]`, `Gap212.conditionD_at_datum_band_3`
supplies `(1/250, 43/10000]`, `Gap212.conditionD_at_datum_band_4` supplies `(43/10000, 13/2500]`,
`Gap212.conditionD_at_datum_band_5` supplies `(13/2500, 541/100000]`,
`Gap212.conditionD_at_datum_band_6` supplies `(541/100000, 4/625]`,
`Gap212.conditionD_of_band_split` glues those to the certificate's band, and
`Gap212.conditionD_of_band` splits a chamber point between the low range and the rest. -/
@[gap212 "lem_continuum_packing"]
theorem conditionD_at_datum (hcert : PackingCertificate) (j j' : Fin gap212Params.n) {m m' : ℕ}
    (hm : m ≤ ⌊1 / gap212Params.δ⌋₊) (hm' : m' ≤ ⌊1 / gap212Params.δ⌋₊) :
    Defs.ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      capD (chamberD (omegaMax gap212Params j j') (omegaMax gap212Params j j')) :=
  conditionD_of_band (conditionD_at_datum_low_level j j')
    (conditionD_of_band_split (conditionD_at_datum_mid_band j j')
      (conditionD_of_band_split (conditionD_at_datum_band_2 j j')
        (conditionD_of_band_split (conditionD_at_datum_band_3 j j')
          (conditionD_of_band_split (conditionD_at_datum_band_4 j j')
            (conditionD_of_band_split (conditionD_at_datum_band_5 j j')
              (conditionD_of_band_split (conditionD_at_datum_band_6 j j')
                (hcert j j' m m' hm hm')))))))

/-- **The five uniform conditions and Condition D at `p_⋆`, from the packing certificate.**

Conditions A, A′, B, C and E come from `Gap212.uniformConditions_at_datum`: each is proved by an
argument uniform in `m` and `m'` with no cell enumeration and no certificate. Condition D comes
from `Gap212.conditionD_at_datum`, which takes from the certificate only the band
`4/625 < ω₀ ≤ ω(1,1)` and proves `[0, 4/625]` from the seven bands below it. -/
theorem packingCertificate_of_conditions (hcert : PackingCertificate)
    (j j' : Fin gap212Params.n) {m m' : ℕ}
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
        (5 * omegaMax gap212Params j j' / 2 + 3 * (2 / 5 : ℝ) / 8 - 2 * slack) ∧
    Defs.ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      capD (chamberD (omegaMax gap212Params j j') (omegaMax gap212Params j j')) := by
  obtain ⟨hA, hA', hB, hC, hE⟩ := uniformConditions_at_datum j j' hm hm'
  exact ⟨hA, hA', hB, hC, hE, conditionD_at_datum hcert j j' hm hm'⟩

/-- **The rungs of the cap row dominate `k δ` up to the thirteenth**, which is what
`Gap212.Xi_nonempty_iff_le_thirteen` asks of the row. -/
theorem gap212Cap_rung_lower (k : ℕ) (hk : k ≤ 13) : (k : ℝ) * (41 / 2500) ≤ gap212Cap k := by
  interval_cases k <;> norm_num [gap212Cap]

/-- **Condition D at the datum, at every `m` and `m'`.** Above the thirteenth rung the check set is
empty by `Gap212.Xi_nonempty_iff_le_thirteen`, and `Gap212.Defs.ConditionD` quantifies over its
members, so the condition holds vacuously there. Below it the bound `13 ≤ ⌊1/δ⌋ = 60` puts the
index inside the certificate's range.

This is the form the routing consumes: `Gap212.harmanAntecedent_of_conditionD` and
`halfLevelCoverage_of_conditionD` ask for Condition D at unrestricted `m, m'`, and the emptiness is
what supplies it without widening the certificate. -/
theorem conditionD_at_datum_all (hcert : PackingCertificate) (j j' : Fin gap212Params.n)
    (m m' : ℕ) :
    Defs.ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      capD (chamberD (omegaMax gap212Params j j') (omegaMax gap212Params j j')) := by
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  by_cases h13 : m ≤ 13 ∧ m' ≤ 13
  · have hfl : (13 : ℕ) ≤ ⌊1 / gap212Params.δ⌋₊ := by
      rw [hδ]; norm_num [Nat.le_floor]
    exact conditionD_at_datum hcert j j' (h13.1.trans hfl) (h13.2.trans hfl)
  · -- the check set is empty, so the condition quantifies over nothing
    intro _ _ y hy
    exact absurd ((Xi_nonempty_iff_le_thirteen (B := gap212Cap) gap212Cap_le
      gap212Cap_rung_lower m m').1 ⟨y, by rw [hδ] at hy; exact hy⟩) h13

end Gap212
