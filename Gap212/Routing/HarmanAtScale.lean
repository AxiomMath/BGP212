/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.DatumConditionD
public import Gap212.Packing.DatumConditionE
public import Gap212.Packing.DatumConditions
public import Gap212.Packing.DatumFacts
public import Gap212.Routing.TypeIIAtScale
public meta import Gap212.Attr

/-!
# From the three types to the whole Harman class, and to `Q⋆`

`Gap212.typeI_equidistribution`, `typeII_equidistribution` and `typeIII_equidistribution` each
bound one band `Q_gen(p,x,j,j',m,m')` for one shape of member. This module puts the three together
over the disjunction that is the Harman class, and the bands together over the union that is `Q⋆`.

## Why the threshold had to be named

`Gap212.qstarAboveSum_le_of_forall_qgen` needs **one** threshold for every band at once, and the
per-band statements deliver an existential one. `Gap212.extractionThreshold` is that common value —
`min(min(ε₀,1/2)·δ/2, ϵ/16)`, the same for all three routes and independent of the band — so the
pooling costs nothing but the band count. The constants do vary with the band, and are taken to
their maximum over the finitely many `(j,j',m,m')`; indexing that maximum by
`Fin n × Fin n × Fin(⌊1/δ⌋+1) × Fin(⌊1/δ⌋+1)`, a nonempty `Fintype`, is what makes `Finset.sup'`
available.

## Why the hypothesis list takes the shape it does

Two features of it are forced rather than chosen:

* `19ω(j,j') + 7δ ≤ 1/4 - (13/2)ϵ` and `B_{j,m}, B_{j',m'} ≤ 1` are what the Type II and Type I
  equidistribution statements carry, and this is where they are supplied.
* The six Conditions are asked at **every** `m, m' ≤ ⌊1/δ⌋`, `m = m' = 0` included. Asking them
  only for `m + m' > 0` and recovering the smooth-only band separately needs, as a hypothesis of
  its own, that each of the eleven capacities is nonnegative, and that does not follow from
  the rest of the list (Condition C's second capacity
`1/10 - (34/5)ω - (7/5)δ - 4ϵ` is only `≥ -2ϵ` under `2/5 + (34/5)ω + (7/5)δ + 2ϵ ≤ 1/2`). Asking
the Conditions at `m = m' = 0` too is how that band is covered here, and it costs nothing at `p_⋆`,
where all five are proved at every `m, m'` — and nothing at all in general, the check set at
`m = m' = 0` having an empty index set.

## Main results

* `Gap212.harmanClass_qstarAbove_bound`: the packing conditions give equidistribution above the
  half-level, general in the support `p` and in `ξ₁, ξ₂, ξ₃`.
-/

@[expose] public section

namespace Gap212

open Finset Real Gap212.Bridges Gap212.Packing

open Classical in
/-- **The packing conditions give equidistribution above the half-level.** For every bundle `K` and
every `ε₀ > 0` there is an `ε₁ > 0` such that for every `A > 0` there is a `C` with: for every
`x ≥ 3`, every member of the Harman class at `(K,x)` and every `a` coprime below `x`, the
squarefree moduli of `Q⋆(p,x,ε₀)` above `x^{1/2-ε₁}` carry `∑ |Δ(f;q,a)| ≤ C x (log x)^{-A}`. -/
@[gap212 "prop_tupleconditions"]
theorem harmanClass_qstarAbove_bound (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath)
    (h₃ : TypeIBakerIrving) (h₄ : TypeIStadlmann) (h₅ : TypeIIIPolymath)
    {p : SupportParams} {ξ₁ ξ₂ ξ₃ : ℝ}
    (hscalarI : p.δ < min (ξ₁ - 4 * p.A (Fin.last p.n) + 2 / 3)
      (9 / 7 - 34 / 7 * p.A (Fin.last p.n)) - 2 * slack)
    (hscalarII₁ : 0 ≤ 19 / 2 - 36 * p.A (Fin.last p.n) - 13 * p.δ - 15 * slack)
    (hscalarII₂ : p.δ ≤ min (ξ₂ / 10 - 32 / 10 * p.A (Fin.last p.n) + 8 / 10)
      (ξ₂ / 4 + 11 / 16 - 3 * p.A (Fin.last p.n)) - 2 * slack)
    (hscalarIII : p.δ < 11 / 8 - 7 / 2 * p.A (Fin.last p.n) - 9 / 8 * ξ₃ - 2 * slack)
    (hcondA : ∀ (j j' : Fin p.n) (m m' : ℕ), m ≤ ⌊1 / p.δ⌋₊ → m' ≤ ⌊1 / p.δ⌋₊ →
      Defs.ConditionA (Xi (p.B j m) (p.B j' m') m m' p.δ)
        (ξ₁ - 2 * slack) (1 / 6 - 4 * omegaMax p j j' - 2 * slack))
    (hcondA' : ∀ (j j' : Fin p.n) (m m' : ℕ), m ≤ ⌊1 / p.δ⌋₊ → m' ≤ ⌊1 / p.δ⌋₊ →
      Defs.ConditionAHigh (Xi (p.B j m) (p.B j' m') m m' p.δ)
        (1 / 2 - 2 * omegaMax p j j' - 2 * slack)
        (1 / 14 - 68 * omegaMax p j j' / 14 - 2 * slack))
    (hcondB : ∀ (j j' : Fin p.n) (m m' : ℕ), m ≤ ⌊1 / p.δ⌋₊ → m' ≤ ⌊1 / p.δ⌋₊ →
      Defs.ConditionB (Xi (p.B j m) (p.B j' m') m m' p.δ)
        (2 / 5 + 24 * omegaMax p j j' / 5 + 7 * p.δ / 5 - 2 * slack)
        (1 / 14 - 24 * omegaMax p j j' / 7 - 2 * slack))
    (hcondC : ∀ (j j' : Fin p.n) (m m' : ℕ), m ≤ ⌊1 / p.δ⌋₊ → m' ≤ ⌊1 / p.δ⌋₊ →
      Defs.ConditionC (Xi (p.B j m) (p.B j' m') m m' p.δ)
        (1 / 3 + 8 * omegaMax p j j' + 7 * p.δ / 3 - 4 * slack)
        (1 / 10 - 34 * omegaMax p j j' / 5 - 7 * p.δ / 5 - 4 * slack)
        (2 * omegaMax p j j' + p.δ - 4 * slack))
    (hcondD : ∀ (j j' : Fin p.n) (m m' : ℕ), m ≤ ⌊1 / p.δ⌋₊ → m' ≤ ⌊1 / p.δ⌋₊ →
      Defs.ConditionD (Xi (p.B j m) (p.B j' m') m m' p.δ) (capCondD p)
        (chamberCondD p ξ₂ (omegaMax p j j') (omegaMax p j j')))
    (hcondE : ∀ (j j' : Fin p.n) (m m' : ℕ), m ≤ ⌊1 / p.δ⌋₊ → m' ≤ ⌊1 / p.δ⌋₊ →
      Defs.ConditionE (Xi (p.B j m) (p.B j' m') m m' p.δ)
        (1 - 6 * omegaMax p j j' - 3 / 2 * ξ₃ - 8 / 3 * slack)
        (5 / 2 * omegaMax p j j' + 3 / 8 * ξ₃ - 2 * slack))
    (hω : ∀ j j' : Fin p.n, omegaMax p j j' ∈ Set.Ioo (0 : ℝ) (1 / 12))
    (_hhalf : ∀ j j' : Fin p.n,
      2 / 5 + 34 * omegaMax p j j' / 5 + 7 * p.δ / 5 + 2 * slack ≤ 1 / 2)
    (hnew : ∀ j j' : Fin p.n, 19 * omegaMax p j j' + 7 * p.δ ≤ 1 / 4 - 13 * slack / 2)
    (hξ₁ : ξ₁ ≤ 1 / 2) (hξ₃ : 0 < ξ₃) (hκ : ξ₃ + slack < 1 / 2)
    (hδstar : ∀ j j' : Fin p.n, 0 < Routing.deltaStarIII' (omegaMax p j j') ξ₃ slack)
    (hδstarhi : ∀ j j' : Fin p.n,
      Routing.deltaStarIII' (omegaMax p j j') ξ₃ slack < 1 / 4 + omegaMax p j j')
    (hwin₂ : ∀ j j' : Fin p.n,
      p.δ ≤ 5 / 2 * omegaMax p j j' + 3 / 8 * ξ₃ + 2 / 3 * slack)
    (hB : ∀ (j : Fin p.n) (m : ℕ), p.B j m ≤ 1) (K : ConstantBundle) :
    ∀ ε₀ > (0 : ℝ), ∃ ε₁ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ,
      ∀ x ≥ (3 : ℝ), ∀ f : ℕ → ℂ, ∀ a : ℕ, HarmanClass K x ξ₁ ξ₂ ξ₃ f → CoprimeBelow a x →
        HasEquidistribution x
          {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ x ^ (1 / 2 - ε₁) < (q : ℝ)} f a A C := by
  classical
  have hωI : ∀ j j' : Fin p.n, omegaMax p j j' ∈ Set.Ioo (0 : ℝ) (1 / 4) := fun j j' ↦
    ⟨(hω j j').1, lt_trans (hω j j').2 (by norm_num)⟩
  haveI : Nonempty (Fin p.n) := Fin.pos_iff_nonempty.mp p.n_pos
  intro ε₀ hε₀
  refine ⟨extractionThreshold p ε₀, extractionThreshold_pos hε₀, ?_⟩
  intro A hAsav
  -- one constant per band and per shape, indexed by a nonempty `Fintype`
  set ι : Type := Fin p.n × Fin p.n × Fin (⌊1 / p.δ⌋₊ + 1) × Fin (⌊1 / p.δ⌋₊ + 1) with hι
  choose CI hCI using fun t : ι ↦
    typeI_bound h₃ hscalarI
      (hcondA t.1 t.2.1 t.2.2.1 t.2.2.2 (Nat.lt_succ_iff.mp t.2.2.1.isLt)
        (Nat.lt_succ_iff.mp t.2.2.2.isLt))
      (hcondA' t.1 t.2.1 t.2.2.1 t.2.2.2 (Nat.lt_succ_iff.mp t.2.2.1.isLt)
        (Nat.lt_succ_iff.mp t.2.2.2.isLt))
      (hωI t.1 t.2.1) hξ₁ (hB t.1 t.2.2.1) (hB t.2.1 t.2.2.2) K ε₀ hε₀ A hAsav
  choose CII hCII using fun t : ι ↦
    typeII_bound h₁ h₂ h₄ hscalarII₁ hscalarII₂
      (hcondB t.1 t.2.1 t.2.2.1 t.2.2.2 (Nat.lt_succ_iff.mp t.2.2.1.isLt)
        (Nat.lt_succ_iff.mp t.2.2.2.isLt))
      (hcondC t.1 t.2.1 t.2.2.1 t.2.2.2 (Nat.lt_succ_iff.mp t.2.2.1.isLt)
        (Nat.lt_succ_iff.mp t.2.2.2.isLt))
      (hcondD t.1 t.2.1 t.2.2.1 t.2.2.2 (Nat.lt_succ_iff.mp t.2.2.1.isLt)
        (Nat.lt_succ_iff.mp t.2.2.2.isLt))
      (hωI t.1 t.2.1) (hnew t.1 t.2.1) (hB t.1 t.2.2.1) (hB t.2.1 t.2.2.2) K ε₀ hε₀ A hAsav
  choose CIII hCIII using fun t : ι ↦
    typeIII_bound h₅ hscalarIII
      (hcondE t.1 t.2.1 t.2.2.1 t.2.2.2 (Nat.lt_succ_iff.mp t.2.2.1.isLt)
        (Nat.lt_succ_iff.mp t.2.2.2.isLt))
      (hω t.1 t.2.1) hξ₃ hκ (hδstar t.1 t.2.1) (hδstarhi t.1 t.2.1) (hwin₂ t.1 t.2.1)
      (hB t.1 t.2.2.1) (hB t.2.1 t.2.2.2) K ε₀ hε₀ A hAsav
  set Cmax : ℝ := (univ : Finset ι).sup' univ_nonempty
    (fun t ↦ max (CI t) (max (CII t) (CIII t))) with hCmax
  refine ⟨(bandCount p : ℝ) * Cmax, ?_⟩
  intro x hx f a hf hcop
  rw [HasEquidistribution, Finset.filter_filter]
  refine le_trans (qstarAboveSum_le_of_forall_qgen (c := Cmax * x / (Real.log x) ^ A) ?_)
    (le_of_eq (by ring))
  intro j j' m m' hm hm'
  set t : ι := (j, j', ⟨m, Nat.lt_succ_of_le hm⟩, ⟨m', Nat.lt_succ_of_le hm'⟩) with ht
  have hle : ∀ c : ℝ, c ≤ max (CI t) (max (CII t) (CIII t)) → c ≤ Cmax := fun c hc ↦
    le_trans hc (le_sup' (fun t ↦ max (CI t) (max (CII t) (CIII t))) (mem_univ t))
  have hband : HasEquidistribution x
      {q ∈ Finset.Icc 1 ⌊x⌋₊ |
        q ∈ Qgen p x j j' m m' ε₀ ∧ x ^ (1 / 2 - extractionThreshold p ε₀) < (q : ℝ)}
      f a A Cmax := by
    rcases hf with hI | hII | hIII
    · exact hasEquidistribution_of_le hx (hle _ (le_max_left _ _)) (hCI t x hx f a hI hcop)
    · exact hasEquidistribution_of_le hx
        (hle _ (le_trans (le_max_left _ _) (le_max_right _ _))) (hCII t x hx f a hII hcop)
    · exact hasEquidistribution_of_le hx
        (hle _ (le_trans (le_max_right _ _) (le_max_right _ _))) (hCIII t x hx f a hIII hcop)
  rwa [HasEquidistribution, Finset.filter_filter] at hband

/-! ## At the chosen datum

Every hypothesis of the previous theorem is discharged at `p_⋆` except Condition D: Conditions A,
A′, B, C and E are proved at the datum in `Gap212.Packing.DatumConditions` and
`DatumConditionE`, and the rest is exact rational arithmetic in `δ = 41/2500`, `A₁ = 257/1000`,
`ω(1,1) = 7/1000` and `(ξ₁,ξ₂,ξ₃) = (19/50, 2/5, 2/5)`.

Condition D at the datum — the continuum packing condition — is a hypothesis here; it holds on the
whole level range by `Gap212.conditionD_at_datum_all`, from `Gap212.PackingCertificate`, which is
`Gap212.packingCertificate_at_datum`. The route needs all of `[0, ω(1,1)] = [0, 7/1000]`, because
`Gap212.mem_moduliIIc_of_conditionD` runs each modulus at its own level `ω₀ = (log_x q - 1/2)/2` and
`Gap212.Extraction.qgen_le` places the generated moduli exactly up to `x^{1/2 + 2ω(1,1)}`. -/



/-- `A₁ = 257/1000` at the datum, read off the affine node row at the top index. -/
theorem gap212Params_A_last : gap212Params.A (Fin.last gap212Params.n) = 257 / 1000 := by
  have h : gap212Params.A (Fin.last gap212Params.n)
      = ((Fin.last gap212Params.n).val : ℝ) * (53 / 200) - 1 / 125 := rfl
  rw [h, Fin.val_last, show gap212Params.n = 1 from rfl]
  norm_num

/-- Every rung of the datum's cap row is at most `1`; it is at most `1081/5000`. -/
theorem gap212Params_B_le_one (j : Fin gap212Params.n) (m : ℕ) : gap212Params.B j m ≤ 1 :=
  le_trans (gap212Cap_le m) (by norm_num)

/-! ### The datum's own capacity row

`Gap212.Packing.DatumConditionD` states Condition D at `p_⋆` against its own `Gap212.capD` and
`Gap212.chamberD`. Those are `Gap212.capCondD` and `Gap212.chamberCondD` at `p = gap212Params` and
`ξ₂ = 2/5`, so the datum's Condition D plugs straight into the route once it covers the whole level
range. -/

/-- At the datum, the capacity row `capCondD gap212Params` is `capD`. -/
theorem capCondD_gap212Params : capCondD gap212Params = capD := by
  funext γ ω₀ i
  rw [capCondD, capD]

/-- At the datum and `ξ₂ = 2/5`, the chamber `chamberCondD gap212Params (2/5) ω ω₀up` is
`chamberD ω ω₀up`. -/
theorem chamberCondD_gap212Params (ω ω₀up : ℝ) :
    chamberCondD gap212Params (2 / 5) ω ω₀up = chamberD ω ω₀up := rfl

open Classical in
/-- **The Harman antecedent above the half-level**, from
Condition D at the datum. At `p_⋆` and `(ξ₁,ξ₂,ξ₃) = (19/50, 2/5, 2/5)`: for every bundle `K` and
every `ε₀ > 0` there is an `ε₁ > 0` such that for every `A > 0` there is a `C` bounding the
squarefree moduli of `Q⋆(p_⋆,x,ε₀)` above `x^{1/2-ε₁}`, at every `x ≥ 3`, every member of the class
and every `a` coprime below `x`.

The tightest of the numerical checks is the second cap wall of the scalar Type II condition,
`ξ₂/4 + 11/16 - 3A₁ - 2ϵ = 33/2000` against `δ = 41/2500`: a margin of `1/10000`. -/
theorem harmanAntecedent_of_conditionD (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath)
    (h₃ : TypeIBakerIrving) (h₄ : TypeIStadlmann) (h₅ : TypeIIIPolymath)
    (hcondD : ∀ (j j' : Fin gap212Params.n) (m m' : ℕ),
      Defs.ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
        (capCondD gap212Params)
        (chamberCondD gap212Params (2 / 5) (omegaMax gap212Params j j')
          (omegaMax gap212Params j j')))
    (K : ConstantBundle) :
    ∀ ε₀ > (0 : ℝ), ∃ ε₁ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ,
      ∀ x ≥ (3 : ℝ), ∀ f : ℕ → ℂ, ∀ a : ℕ,
        HarmanClass K x (19 / 50) (2 / 5) (2 / 5) f → CoprimeBelow a x →
        HasEquidistribution x
          {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar gap212Params x ε₀ ∧ x ^ (1 / 2 - ε₁) < (q : ℝ)}
          f a A C := by
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  have hs : slack = 1 / 10 ^ 10 := rfl
  have hA := gap212Params_A_last
  have hom := omegaMax_gap212Params
  refine harmanClass_qstarAbove_bound h₁ h₂ h₃ h₄ h₅ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun j j' m m' _ _ ↦ hcondD j j' m m') ?_ ?_ ?_ ?_ (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
    gap212Params_B_le_one K
  · rw [hδ, hA, hs, lt_sub_iff_add_lt, lt_min_iff]; norm_num
  · rw [hδ, hA, hs]; norm_num
  · rw [hδ, hA, hs, le_sub_iff_add_le, le_min_iff]; norm_num
  · rw [hδ, hA, hs]; norm_num
  · exact fun j j' m m' _ _ ↦ conditionA_at_datum rfl rfl j j' m m'
  · exact fun j j' m m' _ _ ↦ conditionA_high_at_datum rfl j j' m m'
  · exact fun j j' m m' _ _ ↦ conditionB_at_datum rfl j j' m m'
  · exact fun j j' m m' _ _ ↦ conditionC_at_datum rfl j j' m m'
  · intro j j' m m' hm hm' y hy
    exact ((conditionE_at_datum j j' rfl hm hm') y hy).mono (le_of_eq (by ring))
      (le_of_eq (by ring))
  · intro j j'
    rw [hom j j']
    constructor <;> norm_num
  · intro j j'
    rw [hom j j', hδ, hs]; norm_num
  · intro j j'
    rw [hom j j', hδ, hs]; norm_num
  · rw [hs]; norm_num
  · intro j j'
    rw [hom j j', Routing.deltaStarIII', hs]; norm_num
  · intro j j'
    rw [hom j j', Routing.deltaStarIII', hs]; norm_num
  · intro j j'
    rw [hom j j', hδ, hs]; norm_num

end Gap212
