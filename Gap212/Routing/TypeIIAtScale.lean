/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.AssemblyAtScale
public import Gap212.Routing.ContainmentIIc
public import Gap212.Routing.SwapAtScale
public meta import Gap212.Attr

/-!
# The Type II route at one `x`, general in the support

Type II is the expensive one. Its exponent range is `[ξ₂ - ϵ, 1 - ξ₂ + ϵ]`, the reflection folds it
onto `[ξ₂ - ϵ, 1/2]`, and that interval is covered by **three** estimates with three different
modulus families, so the route splits three ways where Type I and Type III do not split at all.

## Where the three ranges are cut

A cover that uses the endpoints the width lemmas need leaves a little room. This
module cuts at

* `γ ≤ γ_c = 1/3 + 8ω + (7/3)δ + 3ϵ` — Type IIc, the only branch the interval `[2/5, 0.4276]`
  has;
* `γ_c < γ < γ_a = 2/5 + (24/5)ω + (7/5)δ + (7/5)ϵ` — Type IIb;
* `γ_a ≤ γ ≤ 1/2` — Type IIa.

`γ_a` is exactly where `δ*_IIa(γ) ≥ δ` begins, and it is `(3/5)ϵ` *below* the nominal
right endpoint of the IIb range. That shift is load-bearing: the IIb window's lower end
`a₂ = 1/2 - γ - 2ω - 6ε' - δ*_IIb(γ)` decreases in `γ`, and at the nominal endpoint the
hypothesis `19ω + 7δ ≤ 1/4 - (13/2)ϵ` leaves only `a₂ ≥ -6ε'`, which is not positive. Cutting
`(3/5)ϵ` earlier leaves `a₂ ≥ (6/7)ϵ - 6ε' > 0`, and `three_factor_strict` needs `a₂ > 0`.

## The two nested routes are served by the strict extractions

`Gap212.Extraction.three_factor_strict` gives the IIb route its two open windows at the **bare**
capacities, so Condition C is quoted as stated and no inset is charged to it. Type IIc still uses
the non-strict `four_factor` through `Gap212.Routing.mem_moduliIIc_of_qgen`, and pays for its three
open windows with an inset of `ϵ/8` — affordable only because its width is `δ + ϵ/4` rather than
`δ`, and absorbed by Condition D's margins `ϵ - 58ε'`, `ϵ - 6ε'`, `ϵ + 9ε'` and `55ε'`.

## Type IIc reads the modulus's own level

Alone among the six routes, `Gap212.moduliIIc` pins two of its three windows to the modulus `d`
itself, so the route is run at `ω₀ = (log_x q - 1/2)/2` — the level of the modulus at hand, for
which `q = x^{1/2 + 2ω₀}` exactly. That level is negative for the moduli just below `x^{1/2}`,
where Condition D is unsatisfiable; the four capacities are then compared with Condition D's at
`ω₀ = 0` instead, which they dominate as long as `ε₁ ≤ ϵ/16`. That bound on the threshold is what
fixes how far below the half-level the four-factor extraction reaches.

## Main results

* `Gap212.mem_moduliIIb_of_conditionC`: `Q ⊆ D_IIb` from Condition C, at the bare capacities.
* `Gap212.capCondD`, `Gap212.chamberCondD`: Condition D's capacity row and chamber at an arbitrary
  support, in the shape `Gap212.Defs.ConditionD` consumes.
* `Gap212.mem_moduliIIc_of_conditionD`: `Q ⊆ D_IIc` from Condition D, at the modulus's own level.
* `Gap212.typeII_equidistribution`: Type II equidistribution over the squarefree generated moduli
  above `x^{1/2-ε₁}`.
-/

@[expose] public section

namespace Gap212

open Finset Real Gap212.Bridges Gap212.Packing

/-! ## Type IIb -/

/-- **`Q ⊆ D_IIb`, from Condition C** (at an arbitrary support). Two nested divisors, both windows
open and both at the **bare** capacities, through `Gap212.Extraction.three_factor_strict`.

The right endpoint of the range is `2/5 + (24/5)ω + (7/5)δ + (7/5)ϵ`, three fifths of an `ϵ` below
the nominal one; see the module docstring for why that shift is what makes the second
window's lower end positive. -/
@[gap212 "lem_typeIIb_containment"]
theorem mem_moduliIIb_of_conditionC {p : SupportParams} {x ε₀ ε₁ ε' γ ω : ℝ}
    {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₁ : ε₁ ≤ ε₀ * p.δ / 2)
    (hε'0 : 0 ≤ ε') (hε' : 58 * ε' ≤ slack)
    (hωeq : ω = omegaMax p j j') (hω : 0 < ω)
    (hnew : 19 * ω + 7 * p.δ ≤ 1 / 4 - 13 * slack / 2)
    (hCcond : Defs.ConditionC (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (1 / 3 + 8 * ω + 7 * p.δ / 3 - 4 * slack)
      (1 / 10 - 34 * ω / 5 - 7 * p.δ / 5 - 4 * slack)
      (2 * ω + p.δ - 4 * slack))
    (hγlo : 1 / 3 + 8 * ω + 7 * p.δ / 3 + 3 * slack < γ)
    (hγhi : γ < 2 / 5 + 24 * ω / 5 + 7 * p.δ / 5 + 7 * slack / 5)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hq : q ∈ Qgen p x j j' m m' ε₀) (hqbig : x ^ (1 / 2 - ε₁) ≤ (q : ℝ)) :
    q ∈ moduliIIbFamily x ω γ (Routing.deltaStarIIb γ ω slack) ε' := by
  classical
  have hs0 : (0 : ℝ) < slack := by norm_num [slack]
  have hδpos := p.δ_pos
  have hωA : (p.A j.succ + p.A j'.succ) / 2 - 1 / 4 = ω := by rw [hωeq, omegaMax]
  have hApos : 0 ≤ p.A j.succ + p.A j'.succ := by rw [hωeq, omegaMax] at hω; linarith
  have hD : Routing.deltaStarIIb γ ω slack = 3 * γ / 7 - 1 / 7 - 24 * ω / 7 - slack := by
    rw [Routing.deltaStarIIb]
  obtain ⟨-, -, -, -, -, hq1, -⟩ := id hq
  -- the two windows, at the bare capacities
  have ha₁ : 0 < γ - 3 * ε' - Routing.deltaStarIIb γ ω slack := by rw [hD]; linarith
  have ha₂ : 0 < 1 / 2 - γ - 2 * ω - 6 * ε' - Routing.deltaStarIIb γ ω slack := by
    rw [hD]; linarith
  have hthr : ε₁ < ε₀ * (1 / 2 - (γ - 3 * ε')
      - (1 / 2 - γ - 2 * ω - 6 * ε' - Routing.deltaStarIIb γ ω slack)) := by
    have h : p.δ ≤ 1 / 2 - (γ - 3 * ε')
        - (1 / 2 - γ - 2 * ω - 6 * ε' - Routing.deltaStarIIb γ ω slack) := by
      rw [hD]; linarith
    nlinarith
  have hpack : ∀ y ∈ Xi (p.B j m) (p.B j' m') m m' p.δ,
      AdmitsPartition₃ y (γ - 3 * ε')
        (1 / 2 - γ - 2 * ω - 6 * ε')
        (1 / 2 - (γ - 3 * ε')
          - (1 / 2 - γ - 2 * ω - 6 * ε' - Routing.deltaStarIIb γ ω slack)) := fun y hy ↦
    (hCcond y hy).mono (by linarith) (by linarith) (by rw [hD]; linarith)
  obtain ⟨u, r, hur, hu1, hu2, hr1, hr2⟩ :=
    Extraction.three_factor_strict hx hδpos hε₀ hε₀1 ha₁ ha₂ (by rw [hD]; linarith)
      (by rw [hD]; linarith) (by ring_nf; linarith) hthr hB hB' hpack hq hqbig
  have hrq : r ∣ q := dvd_trans (Dvd.intro_left u rfl) hur
  have hr0 : 0 < r := by exact_mod_cast (Real.rpow_pos_of_pos (by linarith) _).trans hr1
  rw [moduliIIbFamily, Finset.mem_filter]
  exact ⟨hωA ▸ Routing.mem_moduliRange_of_qgen hx hε₀ hApos hq, r,
    Nat.mem_divisors.mpr ⟨hrq, by omega⟩, hr1, hr2, u,
    Nat.mem_divisors.mpr ⟨(Nat.dvd_div_iff_mul_dvd hrq).mpr (by rwa [mul_comm] at hur),
      (Nat.div_pos (Nat.le_of_dvd (by omega) hrq) hr0).ne'⟩, hu1, hu2⟩

/-! ## Condition D's capacity row and chamber, at an arbitrary support

`Gap212.Defs.ConditionD` takes the four capacities as one function of `(γ, ω₀)` and the chamber as
a set of pairs, so the quantifier over the chamber belongs to the condition. Both are written here
at a general `p`; at `p = gap212Params` they are the row and chamber the datum's Condition D is
verified against. -/

/-- **Condition D's capacity row**: `c₁ = γ - 2δ - 8ω₀ - ϵ`, `c₂ = 1/2 - γ - 2ω₀ - ϵ`,
`c₃ = 4ω₀ + δ - ϵ`, `c₄ = 8ω₀`, indexed by `Fin 4`. -/
noncomputable def capCondD (p : SupportParams) (γ ω₀ : ℝ) : Fin 4 → ℝ := fun i ↦
  if i = 0 then γ - 2 * p.δ - 8 * ω₀ - slack
  else if i = 1 then 1 / 2 - γ - 2 * ω₀ - slack
  else if i = 2 then 4 * ω₀ + p.δ - slack
  else 8 * ω₀

/-- **The Type IIc chamber**: `γ ∈ [ξ₂ - ϵ, 1/3 + 8ω + (7/3)δ + 3ϵ]` and `ω₀ ∈ [0, ω₀ᵘᵖ]`. The
level ceiling is a parameter because a verification may reach only part of `[0, ω(j,j')]`. -/
def chamberCondD (p : SupportParams) (ξ₂ ω ω₀up : ℝ) : Set (ℝ × ℝ) :=
  {r | ξ₂ - slack ≤ r.1 ∧ r.1 ≤ 1 / 3 + 8 * ω + 7 * p.δ / 3 + 3 * slack ∧
    0 ≤ r.2 ∧ r.2 ≤ ω₀up}

/-- The first entry of `capCondD p γ ω₀` is `γ - 2δ - 8ω₀ - ϵ`. -/
theorem capCondD_zero (p : SupportParams) (γ ω₀ : ℝ) :
    capCondD p γ ω₀ 0 = γ - 2 * p.δ - 8 * ω₀ - slack := by
  rw [capCondD, if_pos (rfl : (0 : Fin 4) = 0)]

/-- The second entry of `capCondD p γ ω₀` is `1/2 - γ - 2ω₀ - ϵ`. -/
theorem capCondD_one (p : SupportParams) (γ ω₀ : ℝ) :
    capCondD p γ ω₀ 1 = 1 / 2 - γ - 2 * ω₀ - slack := by
  rw [capCondD, if_neg (by decide : ¬ ((1 : Fin 4) = 0)), if_pos (rfl : (1 : Fin 4) = 1)]

/-- The third entry of `capCondD p γ ω₀` is `4ω₀ + δ - ϵ`. -/
theorem capCondD_two (p : SupportParams) (γ ω₀ : ℝ) :
    capCondD p γ ω₀ 2 = 4 * ω₀ + p.δ - slack := by
  rw [capCondD, if_neg (by decide : ¬ ((2 : Fin 4) = 0)),
    if_neg (by decide : ¬ ((2 : Fin 4) = 1)), if_pos (rfl : (2 : Fin 4) = 2)]

/-- The fourth entry of `capCondD p γ ω₀` is `8ω₀`. -/
theorem capCondD_three (p : SupportParams) (γ ω₀ : ℝ) : capCondD p γ ω₀ 3 = 8 * ω₀ := by
  rw [capCondD, if_neg (by decide : ¬ ((3 : Fin 4) = 0)),
    if_neg (by decide : ¬ ((3 : Fin 4) = 1)), if_neg (by decide : ¬ ((3 : Fin 4) = 2))]

/-! ## Type IIc

The width is `δ + ϵ/4`, not `δ`: the three windows must sit strictly inside their targets and
`Gap212.Extraction.four_factor` has no strict form, so an inset of `ϵ/8` has to be bought, and a
window of width exactly `δ` has nothing to buy it with. The `ϵ/4` is affordable at both ends — the
estimate's three walls have room after it, and Condition D's four margins `ϵ - 58ε'`, `ϵ - 6ε'`,
`ϵ + 9ε'` and `55ε'` absorb the `(3/2)(ϵ/4)`, `ϵ/8`, `ϵ/4` and `ϵ/4` the inset costs them. -/

/-- **`Q ⊆ D_IIc`, from Condition D** (at an arbitrary support), run at the modulus's **own** level
`ω₀`, for which `q = x^{1/2+2ω₀}` exactly.

Condition D is consumed at `max ω₀ 0`, which is what lets the moduli just below `x^{1/2}` be
reached: there `ω₀ < 0`, Condition D is unsatisfiable (its fourth capacity `8ω₀` is negative), and
the four raw capacities are compared with its bounds at `ω₀ = 0` instead. The comparison costs
`ω₀ ≥ -ϵ/32`, which is the third and fourth capacities' whole slack; the first two hold at every
`ω₀`. -/
@[gap212 "lem_typeIIc_containment"]
theorem mem_moduliIIc_of_conditionD {p : SupportParams} {x ε₀ ε' γ ω ω₀ ξ₂ : ℝ}
    {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hε'0 : 0 ≤ ε') (hε' : 200 * ε' ≤ slack)
    (hωeq : ω = omegaMax p j j') (hω : 0 < ω)
    (hcaps : p.δ ≤ γ / 10 - 32 * ω / 10 - slack)
    (hD : Defs.ConditionD (Xi (p.B j m) (p.B j' m') m m' p.δ) (capCondD p)
      (chamberCondD p ξ₂ ω ω))
    (hγlo : ξ₂ - slack ≤ γ) (hγhi : γ ≤ 1 / 3 + 8 * ω + 7 * p.δ / 3 + 3 * slack)
    (hω₀lo : -(slack / 32) ≤ ω₀) (hω₀hi : ω₀ ≤ ω)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hq : q ∈ Qgen p x j j' m m' ε₀) (hqeq : (q : ℝ) = x ^ (1 / 2 + 2 * ω₀)) :
    q ∈ moduliIIcFamily x ω γ (p.δ + slack / 4) ε' := by
  classical
  have hs0 : (0 : ℝ) < slack := by norm_num [slack]
  have hδpos := p.δ_pos
  have hωA : (p.A j.succ + p.A j'.succ) / 2 - 1 / 4 = ω := by rw [hωeq, omegaMax]
  have hApos : 0 ≤ p.A j.succ + p.A j'.succ := by rw [hωeq, omegaMax] at hω; linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := hqeq ▸ Real.rpow_pos_of_pos (by linarith) _
  -- `γ ≥ 10δ + 32ω + 10ϵ`, which is what makes the first window's lower end positive
  have hγbig : 10 * p.δ + 32 * ω + 10 * slack ≤ γ := by linarith
  have hmx1 : ω₀ ≤ max ω₀ 0 := le_max_left _ _
  have hmx2 : max ω₀ 0 ≤ ω₀ + slack / 32 := max_le (by linarith) (by linarith)
  have hmemD : ((γ, max ω₀ 0) : ℝ × ℝ) ∈ chamberCondD p ξ₂ ω ω :=
    ⟨hγlo, hγhi, le_max_right _ _, max_le hω₀hi hω.le⟩
  rw [← hωA]
  refine Routing.mem_moduliIIc_of_qgen (ω₀ := ω₀)
    (a₁ := γ - 3 * ε' - p.δ - slack / 8)
    (b₁ := γ - 3 * ε' - slack / 8)
    (a₂ := 1 - γ - 6 * ε' - p.δ - slack / 8 - (1 / 2 + 2 * ω₀))
    (b₂ := 1 - γ - 6 * ε' - slack / 8 - (1 / 2 + 2 * ω₀))
    (a₃ := 2 - γ - 52 * ε' - p.δ - slack / 8 - 4 * (1 / 2 + 2 * ω₀))
    (b₃ := 2 - γ - 52 * ε' - slack / 8 - 4 * (1 / 2 + 2 * ω₀))
    hx hδpos hε₀ hε₀1 hApos (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (Routing.div_lt_rpow hx hqeq.ge (by linarith))
    (Routing.rpow_lt_div hx hqeq.le hqpos (by linarith))
    (Routing.div_pow4_lt_rpow hx hqeq.ge (by linarith))
    (Routing.rpow_lt_div_pow4 hx hqeq.le hqpos (by linarith))
    hB hB' ?_ hq ?_
  · -- the packing condition: Condition D at `max ω₀ 0`, weakened to the raw capacities
    intro y hy
    refine (hD (γ, max ω₀ 0) hmemD y hy).mono ?_ ?_ ?_ ?_
    · rw [capCondD_zero]; linarith
    · rw [capCondD_one]; linarith
    · rw [capCondD_two]; linarith
    · rw [capCondD_three]; linarith
  · -- the threshold: `q` is at its own level exactly, and the third capacity is positive
    refine le_trans ((Real.rpow_le_rpow_left_iff hx).mpr ?_) hqeq.ge
    nlinarith [mul_nonneg hε₀.le (by linarith : (0 : ℝ) ≤ 4 * ω₀ + p.δ + slack / 4 + 9 * ε')]

/-- **`Q ⊆ D_IIc` above the threshold.** `Gap212.mem_moduliIIc_of_conditionD` at the modulus's
own level `ω₀ = (log_x q - 1/2)/2`, which lies in `[-ϵ/32, ω]` for every generated modulus above
`x^{1/2-ε₁}` once `ε₁ ≤ ϵ/16`. -/
theorem mem_moduliIIc_of_conditionD_of_threshold {p : SupportParams} {x ε₀ ε₁ ε' γ ξ₂ : ℝ}
    {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₁ : ε₁ ≤ slack / 16)
    (hε'0 : 0 ≤ ε') (hε' : 200 * ε' ≤ slack) (hω : 0 < omegaMax p j j')
    (hcaps : p.δ ≤ γ / 10 - 32 * omegaMax p j j' / 10 - slack)
    (hD : Defs.ConditionD (Xi (p.B j m) (p.B j' m') m m' p.δ) (capCondD p)
      (chamberCondD p ξ₂ (omegaMax p j j') (omegaMax p j j')))
    (hγlo : ξ₂ - slack ≤ γ) (hγhi : γ ≤ 1 / 3 + 8 * omegaMax p j j' + 7 * p.δ / 3 + 3 * slack)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hq : q ∈ Qgen p x j j' m m' ε₀) (hqbig : x ^ (1 / 2 - ε₁) ≤ (q : ℝ)) :
    q ∈ moduliIIcFamily x (omegaMax p j j') γ (p.δ + slack / 4) ε' := by
  have hApos : 0 ≤ p.A j.succ + p.A j'.succ := by rw [omegaMax] at hω; linarith
  obtain ⟨-, -, -, -, -, hq1, -⟩ := id hq
  have hlogq : 1 / 2 - ε₁ ≤ logb x (q : ℝ) := le_logb_of_rpow_le hx hq1 hqbig
  have hqle : (q : ℝ) ≤ x ^ (1 / 2 + 2 * omegaMax p j j') := by
    refine (Extraction.qgen_le hx hq).trans ((Real.rpow_le_rpow_left_iff hx).mpr ?_)
    rw [omegaMax]
    nlinarith [mul_nonneg hε₀.le hApos]
  have hlogq' : logb x (q : ℝ) ≤ 1 / 2 + 2 * omegaMax p j j' := logb_le_of_le_rpow hx hq1 hqle
  refine mem_moduliIIc_of_conditionD (ω₀ := (logb x (q : ℝ) - 1 / 2) / 2) hx hε₀ hε₀1 hε'0 hε'
    rfl hω hcaps hD hγlo hγhi (by linarith) (by linarith) hB hB' hq ?_
  rw [show 1 / 2 + 2 * ((logb x (q : ℝ) - 1 / 2) / 2) = logb x (q : ℝ) by ring,
    Real.rpow_logb (by linarith) hx.ne' (Nat.cast_pos.mpr hq1)]

/-! ## The three ranges, composed at one bundle

A Type II member is presented twice — once as it stands and once reflected — and the estimates are
applied at both bundles, so the composition is factored out here and quantified over
the bundle. Nothing below is normalized: `Gap212.TypeIIPolymath`, `TypeIbPolymath` and
`TypeIStadlmann` take their bundle as given, so unlike Type I and Type III no `flat` is spent. -/

/-- Raising the constant of an equidistribution bound. The three ranges return three constants and
the band takes their sum. -/
theorem hasEquidistribution_of_le {x : ℝ} {D : Finset ℕ} {f : ℕ → ℂ} {a : ℕ} {A C C' : ℝ}
    (hx : 3 ≤ x) (hCC : C ≤ C') (h : HasEquidistribution x D f a A C) :
    HasEquidistribution x D f a A C' :=
  h.trans <| div_le_div_of_nonneg_right (by gcongr)
    (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) A).le

open Classical in
/-- **The Type II band bound, at one bundle and one presentation.** For a convolution `α ⋆ β` whose
second scale has exponent `γ ∈ [ξ₂ - ϵ, 1/2]`, the squarefree generated moduli above `x^{1/2-ε₁}`
carry `O_A(x (log x)^{-A})`.

This is the whole three-range argument: the exponent lands in exactly one of the IIc, IIb and IIa
ranges, each range has its own width, its own estimate and its own Condition, and the three
constants are summed. `ε₁ = min(min(ε₀,1/2)·δ/2, ϵ/16)` — the second entry is the Type IIc level
bound, and it is why the threshold is not simply `ε₀δ/2` as it is for Type I and Type III. -/
theorem typeII_band_bound (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath) (h₄ : TypeIStadlmann)
    {p : SupportParams} {ξ₂ : ℝ} {j j' : Fin p.n} {m m' : ℕ}
    (_hscalar₁ : 0 ≤ 19 / 2 - 36 * p.A (Fin.last p.n) - 13 * p.δ - 15 * slack)
    (hscalar₂ : p.δ ≤ min (ξ₂ / 10 - 32 / 10 * p.A (Fin.last p.n) + 8 / 10)
      (ξ₂ / 4 + 11 / 16 - 3 * p.A (Fin.last p.n)) - 2 * slack)
    (hBcond : Defs.ConditionB (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (2 / 5 + 24 * omegaMax p j j' / 5 + 7 * p.δ / 5 - 2 * slack)
      (1 / 14 - 24 * omegaMax p j j' / 7 - 2 * slack))
    (hCcond : Defs.ConditionC (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (1 / 3 + 8 * omegaMax p j j' + 7 * p.δ / 3 - 4 * slack)
      (1 / 10 - 34 * omegaMax p j j' / 5 - 7 * p.δ / 5 - 4 * slack)
      (2 * omegaMax p j j' + p.δ - 4 * slack))
    (hDcond : Defs.ConditionD (Xi (p.B j m) (p.B j' m') m m' p.δ) (capCondD p)
      (chamberCondD p ξ₂ (omegaMax p j j') (omegaMax p j j')))
    (hω : omegaMax p j j' ∈ Set.Ioo (0 : ℝ) (1 / 4))
    (hnew : 19 * omegaMax p j j' + 7 * p.δ ≤ 1 / 4 - 13 * slack / 2)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1) (KK : ConstantBundle) :
    ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ,
      ∀ x ≥ (3 : ℝ), ∀ α β : ℕ → ℂ, ∀ M ≥ (1 : ℝ), ∀ N ≥ (1 : ℝ), ∀ a : ℕ,
        KK.IsCoefficientSequence α → KK.IsCoefficientSequence β →
        KK.LocatedAtScale α M → KK.LocatedAtScale β N →
        KK.asympEq (M * N) x → KK.HasSiegelWalfisz β N →
        x ^ (ξ₂ - slack) ≤ N → Real.log N / Real.log x ≤ 1 / 2 → CoprimeBelow a x →
        HasEquidistribution x
          {q ∈ Finset.Icc 1 ⌊x⌋₊ |
            q ∈ Qgen p x j j' m m' ε₀ ∧ x ^ (1 / 2 - extractionThreshold p ε₀) < (q : ℝ)}
          (dconv α β) a A C := by
  classical
  have hs0 : (0 : ℝ) < slack := by norm_num [slack]
  have hδpos := p.δ_pos
  have hlast := omegaMax_le_last p j j'
  have hω0 := hω.1
  have hAn : 1 / 4 < p.A (Fin.last p.n) := by linarith
  obtain ⟨hsc₂a, hsc₂b⟩ := le_min_iff.mp (le_sub_iff_add_le.mp hscalar₂)
  have hξ₂pos : 20 * slack < ξ₂ := by linarith
  obtain ⟨hAj, hAj'⟩ := pos_sub_eps_of_omegaMax_pos hω0
  have hApos : 0 ≤ p.A j.succ + p.A j'.succ := by rw [omegaMax] at hω0; linarith
  intro ε₀ hε₀
  set e : ℝ := min ε₀ (1 / 2) with he_def
  have he0 : 0 < e := lt_min hε₀ (by norm_num)
  have he1 : e < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hee : e ≤ ε₀ := min_le_left _ _
  have hε₁a : extractionThreshold p ε₀ ≤ e * p.δ / 2 := extractionThreshold_le_retreat p ε₀
  have hε₁b : extractionThreshold p ε₀ ≤ slack / 16 := extractionThreshold_le_slack p ε₀
  intro A hAsav
  -- the three estimates, at the level, the slack `θ = 3ϵ` and the window `[γ₁, 1/2]`
  have hγ₁pos : 0 < min (ξ₂ - slack) (1 / 4) := lt_min (by linarith) (by norm_num)
  have hγ₁le : min (ξ₂ - slack) (1 / 4) ≤ 1 / 2 :=
    le_trans (min_le_right _ _) (by norm_num)
  obtain ⟨eps₁, heps₁, hm₁⟩ := h₁ KK (omegaMax p j j') hω (3 * slack) (by linarith)
    (min (ξ₂ - slack) (1 / 4)) (1 / 2) hγ₁pos hγ₁le le_rfl
  obtain ⟨eps₂, heps₂, hm₂⟩ := h₂ KK (omegaMax p j j') hω (3 * slack) (by linarith)
    (min (ξ₂ - slack) (1 / 4)) (1 / 2) hγ₁pos hγ₁le le_rfl
  obtain ⟨eps₄, heps₄, hm₄⟩ := h₄ KK (omegaMax p j j') hω (3 * slack) (by linarith)
    (min (ξ₂ - slack) (1 / 4)) (1 / 2) hγ₁pos hγ₁le le_rfl
  set mn : ℝ := min (min eps₁ eps₂) (min eps₄ (slack / 100)) with hmn_def
  have hmn0 : 0 < mn :=
    lt_min (lt_min heps₁ heps₂) (lt_min heps₄ (by positivity))
  have hmn1 : mn ≤ eps₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hmn2 : mn ≤ eps₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hmn4 : mn ≤ eps₄ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hmns : mn ≤ slack / 100 := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨C₁, hC₁⟩ := hm₁ (mn / 2) ⟨by linarith, by linarith⟩ A hAsav
  obtain ⟨C₂, hC₂⟩ := hm₂ (mn / 2) ⟨by linarith, by linarith⟩ A hAsav
  obtain ⟨C₄, hC₄⟩ := hm₄ (mn / 2) ⟨by linarith, by linarith⟩ A hAsav
  refine ⟨max C₁ (max C₂ C₄), ?_⟩
  intro x hx α β M hM N hN a hα hβ hαM hβN hasymp hSW hNlo hγhalf hcop
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  obtain ⟨γ, hγL⟩ : ∃ γ : ℝ, Real.log N / Real.log x = γ := ⟨_, rfl⟩
  rw [hγL] at hγhalf
  have hNx : N = x ^ γ := by rw [← hγL]; exact (rpow_logScale hx1 hN0).symm
  have hγlo : ξ₂ - slack ≤ γ := by rw [← hγL]; exact le_logScale_of_rpow_le hx1 hNlo
  have hNlb : x ^ min (ξ₂ - slack) (1 / 4) ≤ N :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hx1.le (min_le_left _ _)) hNlo
  have hNub : N ≤ x ^ (1 / 2 : ℝ) := by
    rw [hNx]; exact Real.rpow_le_rpow_of_exponent_le hx1.le hγhalf
  have hε' : 200 * (mn / 2) ≤ slack := by linarith
  have hε'0 : (0 : ℝ) ≤ mn / 2 := by linarith
  have hanti : Qgen p x j j' m m' ε₀ ⊆ Qgen p x j j' m m' e :=
    Routing.qgen_antitone hx1 hee (brow_nonneg p j m) (brow_nonneg p j' m') hAj hAj'
  rcases le_or_gt γ (1 / 3 + 8 * omegaMax p j j' + 7 * p.δ / 3 + 3 * slack) with hγc | hγc
  · -- **Type IIc.** The width is `δ + ϵ/4` and each modulus is routed at its own level.
    have hcaps₁ : p.δ ≤ γ / 10 - 32 * omegaMax p j j' / 10 - slack := by linarith
    have hcaps₂ : p.δ ≤ γ / 4 - 1 / 16 - 3 * omegaMax p j j' - slack := by linarith
    have hfirst : p.δ ≤ 1 / 4 - 2 * omegaMax p j j' - γ / 2 - slack := by linarith
    have hEq := hC₄ (p.δ + slack / 4) (by linarith) x hx α β M hM N hN a hα hβ hαM hβN
      hasymp hSW hNlb hNub (by linarith) (by linarith) (by linarith) hcop
    rw [hNx, ← Routing.moduliIIcFamily_eq_moduliIIc hx0] at hEq
    refine hasEquidistribution_of_le hx (le_trans (le_max_right _ _) (le_max_right _ _))
      (hasEquidistribution_of_subset ?_ hEq)
    intro q hq
    obtain ⟨-, hqQ, hqbig⟩ := Finset.mem_filter.mp hq
    exact mem_moduliIIc_of_conditionD_of_threshold hx1 he0 he1 hε₁b hε'0 hε' hω0 hcaps₁ hDcond
      hγlo hγc hB hB' (hanti hqQ) hqbig.le
  · rcases lt_or_ge γ (2 / 5 + 24 * omegaMax p j j' / 5 + 7 * p.δ / 5 + 7 * slack / 5)
      with hγa | hγa
    · -- **Type IIb.** Two nested divisors at the width `δ*_IIb(γ)`.
      have hEq := hC₂ (Routing.deltaStarIIb γ (omegaMax p j j') slack)
        (by rw [Routing.deltaStarIIb]; linarith) x hx α β
        M hM N hN a hα hβ hαM hβN hasymp hSW hNlb hNub
        (by rw [hγL, Routing.deltaStarIIb]; linarith)
        (by rw [hγL, Routing.deltaStarIIb]; linarith) hcop
      rw [hNx, ← Routing.moduliIIbFamily_eq_moduliIIb hx0] at hEq
      refine hasEquidistribution_of_le hx (le_trans (le_max_left _ _) (le_max_right _ _))
        (hasEquidistribution_of_subset ?_ hEq)
      intro q hq
      obtain ⟨-, hqQ, hqbig⟩ := Finset.mem_filter.mp hq
      exact mem_moduliIIb_of_conditionC hx1 he0 he1 hε₁a hε'0 (by linarith) rfl hω0 hnew hCcond
        hγc hγa hB hB' (hanti hqQ) hqbig.le
    · -- **Type IIa.** One divisor at the width `δ*_IIa(γ)`.
      have hEq := hC₁ (Routing.deltaStarIIa γ (omegaMax p j j') slack)
        (by rw [Routing.deltaStarIIa]; linarith) x hx α β
        M hM N hN a hα hβ hαM hβN hasymp hSW hNlb hNub
        (by rw [hγL, Routing.deltaStarIIa]; linarith)
        (by rw [hγL, Routing.deltaStarIIa]; linarith) hcop
      rw [hNx, ← Routing.moduliIIaFamily_eq_moduliIIa hx0] at hEq
      refine hasEquidistribution_of_le hx (le_max_left _ _)
        (hasEquidistribution_of_subset ?_ hEq)
      intro q hq
      obtain ⟨-, hqQ, hqbig⟩ := Finset.mem_filter.mp hq
      exact mem_moduliIIa_of_conditionB hx1 he0 he1 hε₁a hε'0 (by linarith) rfl hω0 hBcond
        hγa hγhalf hB hB' (hanti hqQ) hqbig.le

/-! ## The two presentations

The reflection is where the two presentations come from.
`Gap212.exists_bundle_typeII_swap_witnesses` supplies a bundle `K'`, depending on `K` alone, at
which a Type II member's factors may be exchanged and its second scale replaced by `x / N` exactly;
the exponent of that scale is `1 - γ` on the nose, so a member with `γ > 1/2` is re-presented with
exponent below `1/2`.

What it does **not** supply is a transfer of `K`-data to `K'`, so the two presentations are handled
at two different bundles and the band bound is invoked twice — once at `K`, once at `K'` — with the
threshold the smaller of the two and the constant the larger. Both estimates take their bundle as
given, so no normalization is spent anywhere in Type II. -/

open Classical in
/-- **The Type II band bound, both presentations.** The explicit-threshold form: for
every `ε₀ > 0` and every saving `A` there is one constant covering every member of the class, at
the threshold `Gap212.extractionThreshold p ε₀`. -/
theorem typeII_bound (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath) (h₄ : TypeIStadlmann)
    {p : SupportParams} {ξ₂ : ℝ} {j j' : Fin p.n} {m m' : ℕ}
    (hscalar₁ : 0 ≤ 19 / 2 - 36 * p.A (Fin.last p.n) - 13 * p.δ - 15 * slack)
    (hscalar₂ : p.δ ≤ min (ξ₂ / 10 - 32 / 10 * p.A (Fin.last p.n) + 8 / 10)
      (ξ₂ / 4 + 11 / 16 - 3 * p.A (Fin.last p.n)) - 2 * slack)
    (hBcond : Defs.ConditionB (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (2 / 5 + 24 * omegaMax p j j' / 5 + 7 * p.δ / 5 - 2 * slack)
      (1 / 14 - 24 * omegaMax p j j' / 7 - 2 * slack))
    (hCcond : Defs.ConditionC (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (1 / 3 + 8 * omegaMax p j j' + 7 * p.δ / 3 - 4 * slack)
      (1 / 10 - 34 * omegaMax p j j' / 5 - 7 * p.δ / 5 - 4 * slack)
      (2 * omegaMax p j j' + p.δ - 4 * slack))
    (hDcond : Defs.ConditionD (Xi (p.B j m) (p.B j' m') m m' p.δ) (capCondD p)
      (chamberCondD p ξ₂ (omegaMax p j j') (omegaMax p j j')))
    (hω : omegaMax p j j' ∈ Set.Ioo (0 : ℝ) (1 / 4))
    (hnew : 19 * omegaMax p j j' + 7 * p.δ ≤ 1 / 4 - 13 * slack / 2)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1) (K : ConstantBundle) :
    ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ,
      ∀ x ≥ (3 : ℝ), ∀ f : ℕ → ℂ, ∀ a : ℕ, TypeII K x ξ₂ f → CoprimeBelow a x →
        HasEquidistribution x
          {q ∈ Finset.Icc 1 ⌊x⌋₊ |
            q ∈ Qgen p x j j' m m' ε₀ ∧ x ^ (1 / 2 - extractionThreshold p ε₀) < (q : ℝ)}
          f a A C := by
  classical
  have hs0 : (0 : ℝ) < slack := by norm_num [slack]
  have hδpos := p.δ_pos
  have hlast := omegaMax_le_last p j j'
  have hAn : 1 / 4 < p.A (Fin.last p.n) := by linarith [hω.1]
  have hsc₂a : p.δ + 2 * slack ≤ ξ₂ / 10 - 32 / 10 * p.A (Fin.last p.n) + 8 / 10 :=
    (le_min_iff.mp (le_sub_iff_add_le.mp hscalar₂)).1
  have hξ₂ : slack ≤ ξ₂ := by linarith
  obtain ⟨K', hK'⟩ := exists_bundle_typeII_swap_witnesses K
  intro ε₀ hε₀ A hAsav
  obtain ⟨Ca, hCa⟩ := typeII_band_bound h₁ h₂ h₄ hscalar₁ hscalar₂ hBcond hCcond hDcond
    hω hnew hB hB' K ε₀ hε₀ A hAsav
  obtain ⟨Cb, hCb⟩ := typeII_band_bound h₁ h₂ h₄ hscalar₁ hscalar₂ hBcond hCcond hDcond
    hω hnew hB hB' K' ε₀ hε₀ A hAsav
  refine ⟨max Ca Cb, ?_⟩
  intro x hx f a hf hcop
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  obtain ⟨α, β, M, hM, N, hN, hfeq, hα, hβ, hαM, hβN, hasymp, hSWα, hSWβ, hNlo, hNhi⟩ := hf
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  by_cases hγ : Real.log N / Real.log x ≤ 1 / 2
  · -- the member is already presented below the half-power
    have hEq := hCa x hx α β M hM N hN a hα hβ hαM hβN hasymp hSWβ hNlo hγ hcop
    rw [← hfeq] at hEq
    exact hasEquidistribution_of_le hx (le_max_left _ _) hEq
  · -- reflect: the factors are exchanged and the second scale becomes `x / N`
    obtain ⟨-, hxN1, hxNeq, hfeq', hβ', hα', hβN', hαN', hasymp', hSWβ', hSWα', hNlo', -⟩ :=
      hK' ξ₂ x f α β M N hξ₂ hx1 hM hN hfeq hα hβ hαM hβN hasymp hSWα hSWβ hNlo hNhi
    have hxNpos : (0 : ℝ) < x / N := lt_of_lt_of_le zero_lt_one hxN1
    have hγ' : Real.log (x / N) / Real.log x ≤ 1 / 2 := by
      refine logScale_le_of_le_rpow hx1 hxNpos ?_
      rw [hxNeq, not_le] at *
      exact Real.rpow_le_rpow_of_exponent_le hx1.le (by rw [Real.logb]; linarith)
    have hEq := hCb x hx β α N hN (x / N) hxN1 a hβ' hα' hβN' hαN' hasymp' hSWα' hNlo' hγ' hcop
    rw [← hfeq'] at hEq
    exact hasEquidistribution_of_le hx (le_max_right _ _) hEq

open Classical in
/-- **Type II equidistribution over the generated moduli.** Assume the two scalar Type II
conditions, Conditions B, C and D at the band, and suppose `ω(j,j') ∈ (0,1/4)`,
`2/5 + (34/5)ω + (7/5)δ + 2ϵ ≤ 1/2`, `19ω + 7δ ≤ 1/4 - (13/2)ϵ` and `B_{j,m}, B_{j',m'} ≤ 1`. Then
for every bundle `K` and every `ε₀ > 0` there is an `ε₁ > 0` such that for every `A > 0` there is a
`C` with: for every `x ≥ 3`, every `f` of Type II at `(K,x)` for `ξ₂` and every `a` coprime below
`x`, the squarefree generated moduli above `x^{1/2-ε₁}` carry `∑ |Δ(f;q,a)| ≤ C x (log x)^{-A}`.

`19ω + 7δ ≤ 1/4 - (13/2)ϵ` is the hypothesis the lemma is false without: it is exactly what makes
the Type IIb window's lower end positive at the top of that range, and the other hypotheses do not
imply it. -/
@[gap212 "lem_typeII_equidistribution"]
theorem typeII_equidistribution (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath) (h₄ : TypeIStadlmann)
    {p : SupportParams} {ξ₂ : ℝ} {j j' : Fin p.n} {m m' : ℕ}
    (hscalar₁ : 0 ≤ 19 / 2 - 36 * p.A (Fin.last p.n) - 13 * p.δ - 15 * slack)
    (hscalar₂ : p.δ ≤ min (ξ₂ / 10 - 32 / 10 * p.A (Fin.last p.n) + 8 / 10)
      (ξ₂ / 4 + 11 / 16 - 3 * p.A (Fin.last p.n)) - 2 * slack)
    (hBcond : Defs.ConditionB (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (2 / 5 + 24 * omegaMax p j j' / 5 + 7 * p.δ / 5 - 2 * slack)
      (1 / 14 - 24 * omegaMax p j j' / 7 - 2 * slack))
    (hCcond : Defs.ConditionC (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (1 / 3 + 8 * omegaMax p j j' + 7 * p.δ / 3 - 4 * slack)
      (1 / 10 - 34 * omegaMax p j j' / 5 - 7 * p.δ / 5 - 4 * slack)
      (2 * omegaMax p j j' + p.δ - 4 * slack))
    (hDcond : Defs.ConditionD (Xi (p.B j m) (p.B j' m') m m' p.δ) (capCondD p)
      (chamberCondD p ξ₂ (omegaMax p j j') (omegaMax p j j')))
    (hω : omegaMax p j j' ∈ Set.Ioo (0 : ℝ) (1 / 4))
    (_hhalf : 2 / 5 + 34 * omegaMax p j j' / 5 + 7 * p.δ / 5 + 2 * slack ≤ 1 / 2)
    (hnew : 19 * omegaMax p j j' + 7 * p.δ ≤ 1 / 4 - 13 * slack / 2)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1) (K : ConstantBundle) :
    ∀ ε₀ > (0 : ℝ), ∃ ε₁ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ,
      ∀ x ≥ (3 : ℝ), ∀ f : ℕ → ℂ, ∀ a : ℕ, TypeII K x ξ₂ f → CoprimeBelow a x →
        HasEquidistribution x
          {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qgen p x j j' m m' ε₀ ∧ x ^ (1 / 2 - ε₁) < (q : ℝ)}
          f a A C :=
  fun ε₀ hε₀ ↦ ⟨extractionThreshold p ε₀, extractionThreshold_pos hε₀,
    typeII_bound h₁ h₂ h₄ hscalar₁ hscalar₂ hBcond hCcond hDcond hω hnew hB hB' K ε₀ hε₀⟩

end Gap212
