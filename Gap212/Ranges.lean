/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Defs
public import Gap212.Inputs.BilinearBV
public import Gap212.Routing.Assembly
public meta import Gap212.Attr

/-!
# Assembling the three types, and the four modulus ranges

The equidistribution layer is a tower of compositions: each of the three shapes in
the Harman class is routed to its estimate, the three are combined by the class being a
disjunction, and the resulting bound is then read off on each of the four modulus ranges the
argument separates.

Everything here is that composition. The analysis sits in the five assumed estimates, in the route
containments of `Gap212.Routing.Routes`, and in bilinear Bombieri–Vinogradov; what this module
supplies is the wiring, plus the one structural fact the wholly smooth band needs.

## The half-level restriction, and why it is in the statements

Stating the three type lemmas over the whole generated family, and dismissing the moduli below
`x^{1/2 - ε₁}` as "at most `x^{1/2}` terms each trivially `O(x^{1/2 + ε₁})`", is false in the
direction it is used: for a modulus *below* the half-level the count in a residue class is
`x/q ≥ x^{1/2 + ε₁}`, so the trivial bound is larger there, not smaller, and the total is
`x^{1 + ε₁}` rather than `o(x)`. The sub-half range genuinely needs bilinear
Bombieri–Vinogradov — which is assumed anyway, as
`Gap212.Inputs.BilinearBombieriVinogradovFamily`, and applied on exactly that range by
`Gap212.Inputs.subhalfSum_le_of_bv`.

So the type lemmas, their assembly, and the Harman antecedent are all stated *above* the
half-level. That is what `Gap212.Routing.PositiveLevelCoverage p f t` already says, at threshold
`t`, and it is what the route containments — every one of which carries a hypothesis `x^{…} ≤ q` —
can actually deliver.

## Main definitions

* `Gap212.Ranges.RangeBound`: the discrepancy bound over the generated moduli lying in a given
  range, which is the shape the four range lemmas take.

## Main results

* `Gap212.Ranges.mem_Qgen_zero_smooth`: at `m = m' = 0` a generated modulus is `x^δ`-smooth and
  bounded by the two nodes together — the wholly smooth band, structurally.
* `Gap212.Ranges.positiveLevelCoverage_of_cases`: the three shapes suffice for the whole class.
* `Gap212.Ranges.harmanAntecedent_positiveLevel`: the same at the support `gap212Params` and the
  Point A Harman parameters.
* `Gap212.Ranges.typeI_positiveLevelCoverage`, `typeIII_positiveLevelCoverage`,
  `typeII_positiveLevelCoverage`: each shape's route composed with its estimate.
* `Gap212.Ranges.rangeBound_endpointRange`, `rangeBound_transitionModuli`,
  `rangeBound_positiveLevelModuli`: the bound read off on each of the three ranges at or above the
  half-level.
-/

@[expose] public section

namespace Gap212.Ranges

open Finset Real Gap212.Routing Gap212.Inputs Gap212.PointA Gap212.Defs

/-! ## The wholly smooth band -/

/-- **At `m = m' = 0` a generated modulus is wholly `x^δ`-smooth**, and bounded by the two nodes
together.

With no rough factors the two rough caps are vacuous and the factorization collapses to `q = e e'`,
whose every prime factor is strictly below `x^δ` by definition of the smooth part; the conclusion
records that non-strictly, the form the reservoir lemmas consume. This is the structural
half of the wholly-smooth-band argument: it is what lets a target window of width at
least `δ` be hit using the prime factors of `q` alone, so that the band lies inside *every* one of
the five modulus sets and whichever type `f` has applies to it. -/
@[gap212 "lem_smooth_only_band"]
theorem mem_Qgen_zero_smooth {p : SupportParams} {x ε₀ : ℝ} {j j' : Fin p.n} {q : ℕ}
    (hx : 1 < x) (hq : q ∈ Qgen p x j j' 0 0 ε₀) :
    (∀ r : ℕ, r.Prime → r ∣ q → (r : ℝ) ≤ x ^ p.δ) ∧
      (q : ℝ) ≤ x ^ ((1 - ε₀) * (p.A j.succ - p.ε) + (1 - ε₀) * (p.A j'.succ + p.ε)) := by
  obtain ⟨e, e', f, f', hqeq, -, -, -, -, hecap, he'cap, hsmooth, -, -⟩ := hq
  have hprod : q = e * e' := by simpa using hqeq
  have hxpos : (0 : ℝ) < x := lt_trans zero_lt_one hx
  refine ⟨fun r hr hrq ↦ (hsmooth r hr (by rwa [hprod] at hrq)).le, ?_⟩
  have hecap' : ((e : ℕ) : ℝ) ≤ x ^ ((1 - ε₀) * (p.A j.succ - p.ε)) := by
    simpa using hecap
  have he'cap' : ((e' : ℕ) : ℝ) ≤ x ^ ((1 - ε₀) * (p.A j'.succ + p.ε)) := by
    simpa using he'cap
  calc (q : ℝ) = (e : ℝ) * (e' : ℝ) := by rw [hprod]; push_cast; ring
    _ ≤ x ^ ((1 - ε₀) * (p.A j.succ - p.ε)) * x ^ ((1 - ε₀) * (p.A j'.succ + p.ε)) :=
        mul_le_mul hecap' he'cap' (Nat.cast_nonneg _)
          (Real.rpow_nonneg hxpos.le _)
    _ = x ^ ((1 - ε₀) * (p.A j.succ - p.ε) + (1 - ε₀) * (p.A j'.succ + p.ε)) :=
        (Real.rpow_add hxpos _ _).symm

/-! ## Each shape, routed to its estimate -/

/-- **Type I equidistribution above the half-level.** The Baker–Irving estimate applies to every
Type I member of the class (`Gap212.Routing.typeI_estimate_applies`), and the route containment
puts the generated moduli above the threshold inside `moduliIFamily`; composing the two
is the positive-level
obligation.

The estimate is invoked at the chamber point `(ω, γ, widthI₁)`, which is where the two `γ`-branches
are reconciled by a single width. -/
theorem typeI_positiveLevelCoverage (h₃ : TypeIBakerIrvingFamily) {p : SupportParams}
    {f : ℕ → ℝ → ℂ}
    {t : ℝ → ℝ} {γ eb : ℝ} (hf : Harman.TypeIFamily (((ξ₁ : ℚ) : ℝ)) f) (heb : 0 < eb)
    (hmem : (((ω : ℚ) : ℝ), γ, widthI₁) ∈
      triples (((ω : ℚ) : ℝ)) widthI₁ (Set.Ici gammaLoI))
    (hcont : ∀ ε : ℝ, 0 < ε → ε ≤ eb → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ x : ℝ, 1 < x → ∀ q : ℕ,
      q ∈ Finset.Icc 1 ⌊x⌋₊ → q ∈ Qstar p x ε₀ → Squarefree q → ¬ ((q : ℝ) < t x) →
      q ∈ moduliIFamily x (((ω : ℚ) : ℝ)) γ widthI₁ ε) :
    PositiveLevelCoverage p f t :=
  positiveLevelCoverage_of_containment heb hmem (typeI_estimate_applies h₃ hf) hcont

/-- **Type III equidistribution above the half-level**, the same composition with the Polymath Type
III estimate and the width `widthIII`.

Type III needs no localization: its exponent set is the singleton `{ξ₃ + ϵ}`, so a single width
serves and no cover of scales is needed. -/
theorem typeIII_positiveLevelCoverage (h₅ : TypeIIIPolymathFamily) {p : SupportParams}
    {f : ℕ → ℝ → ℂ}
    {t : ℝ → ℝ} {eb : ℝ} (hf : Harman.TypeIIIFamily (((ξ₃ : ℚ) : ℝ)) f) (heb : 0 < eb)
    (hmem : (((ω : ℚ) : ℝ), ((ξ₃ : ℚ) : ℝ) + Harman.slack, widthIII) ∈
      triples (((ω : ℚ) : ℝ)) widthIII {((ξ₃ : ℚ) : ℝ) + Harman.slack})
    (hcont : ∀ ε : ℝ, 0 < ε → ε ≤ eb → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ x : ℝ, 1 < x → ∀ q : ℕ,
      q ∈ Finset.Icc 1 ⌊x⌋₊ → q ∈ Qstar p x ε₀ → Squarefree q → ¬ ((q : ℝ) < t x) →
      q ∈ moduliIIIFamily x (((ω : ℚ) : ℝ)) (((ξ₃ : ℚ) : ℝ) + Harman.slack) widthIII ε) :
    PositiveLevelCoverage p f t :=
  positiveLevelCoverage_of_containment heb hmem (typeIII_estimate_applies h₅ hf) hcont

/-- **Type II equidistribution above the half-level.** Type II is the shape that cannot be handled
at one width: `Gap212.Routing.typeIIa_wall_unsatisfiable` shows the first Type IIa wall is
unsatisfiable at the bottom of the `γ`-range, so the three sub-ranges must be treated separately.

The recombination is by scale, not by exponent set: each sub-range gets a localized copy of `f`,
and `Gap212.Routing.positiveLevelCoverage_of_cover` puts the finitely many bounds back together by
taking the maximum of their constants. The shape hypothesis is carried because it is what makes
each localized copy still a Type II member — `Gap212.Routing.dconv_restrict` — and hence what makes
the three per-range obligations the ones the estimates can discharge. -/
theorem typeII_positiveLevelCoverage {p : SupportParams} {f : ℕ → ℝ → ℂ} {t : ℝ → ℝ} {ξ₂ : ℝ}
    {ι : Type*} [Finite ι] [Nonempty ι] {S : ι → Set ℝ}
    (_hf : Harman.TypeIIFamily ξ₂ f) (hcover : ∀ x : ℝ, 1 < x → ∃ i, x ∈ S i)
    (hroute : ∀ i, PositiveLevelCoverage p (restrict (S i) f) t) :
    PositiveLevelCoverage p f t :=
  positiveLevelCoverage_of_cover hcover hroute

/-! ## The three shapes assembled -/

/-- **The packing conditions give equidistribution above the half-level.** `HarmanClassFamily` is a
disjunction, so a positive-level bound for each of the three shapes is a positive-level bound for
every member of the class.

The scalar and packing conditions enter through the three shape hypotheses: each is what makes its
route's containment and its estimate's parameter inequalities hold. -/
theorem positiveLevelCoverage_of_cases {p : SupportParams} {ξ₁ ξ₂ ξ₃ : ℝ} {f : ℕ → ℝ → ℂ}
    {t : ℝ → ℝ}
    (hI : ∀ g : ℕ → ℝ → ℂ, Harman.TypeIFamily ξ₁ g → PositiveLevelCoverage p g t)
    (hII : ∀ g : ℕ → ℝ → ℂ, Harman.TypeIIFamily ξ₂ g → PositiveLevelCoverage p g t)
    (hIII : ∀ g : ℕ → ℝ → ℂ, Harman.TypeIIIFamily ξ₃ g → PositiveLevelCoverage p g t)
    (hf : Harman.HarmanClassFamily ξ₁ ξ₂ ξ₃ f) :
    PositiveLevelCoverage p f t := by
  rcases hf with h | h | h
  · exact hI f h
  · exact hII f h
  · exact hIII f h

/-- **The Harman antecedent above the half-level**, at the support `gap212Params` and the Point A
Harman parameters `(ξ₁, ξ₂, ξ₃) = (23317/60000, 2/5, 2/5)`.

This is `Gap212.Ranges.positiveLevelCoverage_of_cases` instantiated there; the three shape
hypotheses have the form of the three route compositions above. -/
theorem harmanAntecedent_positiveLevel {f : ℕ → ℝ → ℂ} {t : ℝ → ℝ}
    (hI : ∀ g : ℕ → ℝ → ℂ, Harman.TypeIFamily (((ξ₁ : ℚ) : ℝ)) g →
      PositiveLevelCoverage gap212Params g t)
    (hII : ∀ g : ℕ → ℝ → ℂ, Harman.TypeIIFamily (((ξ₂ : ℚ) : ℝ)) g →
      PositiveLevelCoverage gap212Params g t)
    (hIII : ∀ g : ℕ → ℝ → ℂ, Harman.TypeIIIFamily (((ξ₃ : ℚ) : ℝ)) g →
      PositiveLevelCoverage gap212Params g t)
    (hf : Harman.HarmanClassFamily (((ξ₁ : ℚ) : ℝ)) (((ξ₂ : ℚ) : ℝ)) (((ξ₃ : ℚ) : ℝ)) f) :
    PositiveLevelCoverage gap212Params f t :=
  positiveLevelCoverage_of_cases hI hII hIII hf

/-! ## The four modulus ranges

The generated moduli split into four classes, each bounded in turn. Three of them — the endpoint
block, the transition, and the positive level — lie at or above the half-level, so each is a
restriction of the positive-level bound. The fourth is the sub-half range, which is
`Gap212.Inputs.subhalfSum_le_of_bv`'s business.
-/

open Classical in
/-- **The discrepancy bound on a range.** `R x` selects the moduli of interest at scale `x`; the
sum runs over the squarefree generated moduli inside it.

This is the shape each of the four range lemmas takes, and `Gap212.Routing.discrepancy` being a
norm is what makes the four of them add up to a bound over the whole family. -/
def RangeBound (p : SupportParams) (f : ℕ → ℝ → ℂ) (R : ℝ → Set ℕ) : Prop :=
  ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ c > (0 : ℝ), ∀ x : ℝ, 1 < x → ∀ a : ℕ, CoprimeBelow a x →
    ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ Squarefree q}.filter (fun q ↦ q ∈ R x),
      discrepancy f x a q ≤ c * x / (log x) ^ A

open Classical in
/-- **A range above the threshold inherits the positive-level bound.** If every modulus of the
range is at or above `t x`, the positive-level bound restricts to it — the summand being a norm,
shrinking the index set shrinks the sum. -/
theorem rangeBound_of_positiveLevelCoverage {p : SupportParams} {f : ℕ → ℝ → ℂ} {t : ℝ → ℝ}
    {R : ℝ → Set ℕ} (hR : ∀ x : ℝ, 1 < x → ∀ q : ℕ, q ∈ R x → ¬ ((q : ℝ) < t x))
    (h : PositiveLevelCoverage p f t) :
    RangeBound p f R := by
  classical
  intro ε₀ hε₀ A hA
  obtain ⟨c, hc, hbd⟩ := h ε₀ hε₀ A hA
  refine ⟨c, hc, fun x hx a ha ↦ le_trans (discrepancySum_le_of_subset ?_) (hbd x hx a ha)⟩
  intro q hq
  rw [Finset.mem_filter] at hq ⊢
  exact ⟨hq.1, hR x hx q hq.2⟩

open Classical in
/-- **The endpoint range.** The block at level exactly `1/2` consists of moduli at least `x^{1/2}`,
so the positive-level bound at threshold `x ↦ x^{1/2}` covers it.

The endpoint is where the extraction leaves are constructed, and the transition transports them
outwards from here; `Gap212.Packing.conditionD` supplies Condition D at this level. -/
theorem rangeBound_endpointRange {p : SupportParams} {f : ℕ → ℝ → ℂ}
    (h : PositiveLevelCoverage p f (fun x ↦ x ^ (1 / 2 : ℝ))) :
    RangeBound p f endpointRange := by
  refine rangeBound_of_positiveLevelCoverage (fun x hx q hq ↦ ?_) h
  have hle : x ^ (1 / 2 + 2 * (0 : ℝ)) ≤ (q : ℝ) := hq.1
  rw [not_lt]
  simpa using hle

open Classical in
/-- **The transition range.** Every modulus here exceeds `x^{1/2}(log x)^{-C}`, so the
positive-level bound at that threshold covers it.

This is the logarithmically thin band just below the half-level: the four raw capacities stay above
their endpoint values there by `Gap212.Transition.IIc.endpoint_le_cap₁`–`endpoint_le_cap₄`, and one
window serves every leaf by `Gap212.Transition.transitionRadius_pos`. -/
theorem rangeBound_transitionModuli {p : SupportParams} {f : ℕ → ℝ → ℂ} (C : ℝ)
    (h : PositiveLevelCoverage p f (fun x ↦ x ^ (1 / 2 : ℝ) / (log x) ^ C)) :
    RangeBound p f (fun x ↦ transitionModuli x C) :=
  rangeBound_of_positiveLevelCoverage (fun _ _ _ hq ↦ not_lt.mpr hq.1.le) h

open Classical in
/-- **The positive-level range.** Every modulus here exceeds `x^{1/2}`, so the positive-level bound
at that threshold covers it.

This is the range the five Type estimates were built for; the parameter points lie in finitely many
compact chambers, on each of which `Gap212.Auxiliary.uniform_margin_on_compact` turns the strict
parameter inequalities into a uniform margin. -/
theorem rangeBound_positiveLevelModuli {p : SupportParams} {f : ℕ → ℝ → ℂ}
    (h : PositiveLevelCoverage p f (fun x ↦ x ^ (1 / 2 : ℝ))) :
    RangeBound p f positiveLevelModuli :=
  rangeBound_of_positiveLevelCoverage (fun _ _ _ hq ↦ not_lt.mpr (le_of_lt hq)) h

end Gap212.Ranges
