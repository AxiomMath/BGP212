/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.TypeIIIAssembly
public meta import Gap212.Attr

/-!
# What `RoutingConclusionFamily` decomposes into

`Gap212.Harman.RoutingConclusionFamily` is the two-variable routing conclusion. This module
decomposes it into a named finite list of obligations.

## Two orthogonal splits

**By type.** `HarmanClassFamily` is a three-way disjunction, so
`Gap212.Routing.routingConclusion_of_cases` reduces the goal to three independent statements, one
per shape.

**By modulus size.** Each of those splits again. The containments of
`Gap212.Routing.Containment` all carry a hypothesis `x^{…} ≤ q`: factor extraction only
reaches moduli above the retreated half-level. So for each type there are two obligations —
`Gap212.Routing.PositiveLevelCoverage` above the threshold and `Gap212.Routing.SubHalfCoverage`
below it — and `Gap212.Routing.hasEquidistributionOverQstar_of_halves` shows the two suffice.

So `RoutingConclusionFamily` is exactly six obligations: three types × two modulus ranges.

## The two columns

The positive-level column is the routes: each route containment composed with its estimate, as
`Gap212.Routing.typeIII_estimate_applies` does for Type III. Type II additionally needs
localization by scale, no single width covering its `γ`-range.

The sub-half column is bilinear Bombieri–Vinogradov, whose shape is `dconvFamily α β` with
Siegel–Walfisz on `β` and both scales at least `x^η`. A Harman-class member is not in that shape —
Type III is a *four-fold* convolution, Type I has a smooth factor with no Siegel–Walfisz hypothesis
at all. In this two-variable form `SubHalfCoverage` is a hypothesis; the single-scale chain covers
the sub-half range by `Gap212.exists_hasEquidistribution_subhalf_of_harmanClass`, and the whole
class by `Gap212.halfLevelCoverage`.

## Main results

* `Gap212.Routing.routingConclusion_of_cases`: three per-type obligations suffice.
* `Gap212.Routing.SubHalfCoverage`, `PositiveLevelCoverage`: the two modulus ranges, named.
* `Gap212.Routing.hasEquidistributionOverQstar_of_halves`: the two ranges together suffice.
* `Gap212.Routing.positiveLevelCoverage_of_cover`, `subHalfCoverage_of_cover`: each half combines
  across a finite cover of scales, which is what localization by scale needs.
* `Gap212.Routing.positiveLevelCoverage_of_containment`: an estimate plus a containment gives the
  positive-level obligation — the step every route needs.
-/

@[expose] public section

namespace Gap212.Routing

open Finset Real

/-! ## Splitting by type -/

/-- **Three per-type obligations suffice.** `HarmanClassFamily` is a disjunction, so
`RoutingConclusionFamily`
needs nothing beyond one statement per shape. -/
theorem routingConclusion_of_cases {p : SupportParams} {ξ₁ ξ₂ ξ₃ : ℝ}
    (hI : ∀ f : ℕ → ℝ → ℂ, Harman.TypeIFamily ξ₁ f → HasEquidistributionOverQstarFamily p f)
    (hII : ∀ f : ℕ → ℝ → ℂ, Harman.TypeIIFamily ξ₂ f → HasEquidistributionOverQstarFamily p f)
    (hIII : ∀ f : ℕ → ℝ → ℂ, Harman.TypeIIIFamily ξ₃ f → HasEquidistributionOverQstarFamily p f) :
    Harman.RoutingConclusionFamily p ξ₁ ξ₂ ξ₃ := by
  rintro f (h | h | h)
  exacts [hI f h, hII f h, hIII f h]

/-! ## Splitting by modulus size -/

open Classical in
/-- **The sub-half obligation**, at a size threshold `t`: the generated moduli below `t x`
contribute `O_A(x/log(x)^A)`.

This is the range of bilinear Bombieri–Vinogradov, reached through the Heath–Brown identity and
smooth dyadic partitions; see the module docstring. -/
def SubHalfCoverage (p : SupportParams) (f : ℕ → ℝ → ℂ) (t : ℝ → ℝ) : Prop :=
  ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ c > (0 : ℝ), ∀ x : ℝ, 1 < x → ∀ a : ℕ, CoprimeBelow a x →
    ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ Squarefree q}.filter
      (fun n : ℕ ↦ (n : ℝ) < t x), discrepancy f x a q ≤ c * x / (log x) ^ A

open Classical in
/-- **The positive-level obligation**, at threshold `t`: the moduli at or above `t x` contribute
`O_A(x/log(x)^A)`.

This is the range of the routes: each containment composed with its estimate, as
`Gap212.Routing.typeIII_estimate_applies` does for Type III. -/
def PositiveLevelCoverage (p : SupportParams) (f : ℕ → ℝ → ℂ) (t : ℝ → ℝ) : Prop :=
  ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ c > (0 : ℝ), ∀ x : ℝ, 1 < x → ∀ a : ℕ, CoprimeBelow a x →
    ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ Squarefree q}.filter
      (fun n : ℕ ↦ ¬ ((n : ℝ) < t x)), discrepancy f x a q ≤ c * x / (log x) ^ A

open Classical in
/-- **The two ranges together suffice.** At any threshold, a bound below and a bound above give
equidistribution over the whole generated family; the constants add. -/
theorem hasEquidistributionOverQstar_of_halves {p : SupportParams} {f : ℕ → ℝ → ℂ} {t : ℝ → ℝ}
    (hsub : SubHalfCoverage p f t) (hpos : PositiveLevelCoverage p f t) :
    HasEquidistributionOverQstarFamily p f := by
  intro ε₀ hε₀ A hA
  obtain ⟨c₁, hc₁, h₁⟩ := hsub ε₀ hε₀ A hA
  obtain ⟨c₂, hc₂, h₂⟩ := hpos ε₀ hε₀ A hA
  refine ⟨c₁ + c₂, by linarith, fun x hx a ha ↦ ?_⟩
  exact (sum_le_of_split (h₁ x hx a ha) (h₂ x hx a ha)).trans_eq (by ring)

/-! ## The Type III obligation

Type III's route composition is `Gap212.Routing.typeIII_estimate_applies`, so its positive level
is supplied by the route and the sub-half range is the remaining input. -/

/-- **Type III from the two halves.** Given both halves, a Type III member of the Harman class
equidistributes over the generated moduli; its positive level is what the route delivers once
composed. -/
theorem typeIII_of_halves {f : ℕ → ℝ → ℂ} {t : ℝ → ℝ}
    (hsub : SubHalfCoverage gap212Params f t)
    (hpos : PositiveLevelCoverage gap212Params f t) :
    HasEquidistributionOverQstarFamily gap212Params f :=
  hasEquidistributionOverQstar_of_halves hsub hpos

/-! ## Combining the halves across a cover of scales

Localization splits a Harman shape by scale, so each half-obligation has to be combinable across
that split. Both are, by the same argument as
`Gap212.Routing.hasEquidistributionOverQstar_of_cover`: at a scale in `S i` the discrepancy of the
localized copy equals that of `f`, and finitely many constants have a maximum.

These are what let Type II's three `γ`-ranges be handled separately and then put back together. -/

open Classical in
/-- The common core of `positiveLevelCoverage_of_cover` and `subHalfCoverage_of_cover`: a
per-piece bound over any filter of the generated moduli combines across a finite cover of
scales. -/
private theorem coverage_of_cover_aux {p : SupportParams} {f : ℕ → ℝ → ℂ} {P : ℝ → ℕ → Prop}
    [∀ x, DecidablePred (P x)] {ι : Type*} [Finite ι] [Nonempty ι] {S : ι → Set ℝ}
    (hcover : ∀ x : ℝ, 1 < x → ∃ i, x ∈ S i)
    (h : ∀ i, ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ c > (0 : ℝ), ∀ x : ℝ, 1 < x → ∀ a : ℕ,
      CoprimeBelow a x → ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ Squarefree q}.filter
        (P x), discrepancy (restrict (S i) f) x a q ≤ c * x / (log x) ^ A) :
    ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ c > (0 : ℝ), ∀ x : ℝ, 1 < x → ∀ a : ℕ,
      CoprimeBelow a x → ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ Squarefree q}.filter
        (P x), discrepancy f x a q ≤ c * x / (log x) ^ A := by
  have _inst : Fintype ι := Fintype.ofFinite ι
  intro ε₀ hε₀ A hA
  choose c hc hbd using fun i ↦ h i ε₀ hε₀ A hA
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨univ.sup' univ_nonempty c, (hc i₀).trans_le (le_sup' c (mem_univ i₀)),
    fun x hx a ha ↦ ?_⟩
  obtain ⟨i, hi⟩ := hcover x hx
  rw [sum_congr rfl fun q _ ↦ (discrepancy_restrict_of_mem hi).symm]
  refine (hbd i x hx a ha).trans ?_
  have := Real.rpow_pos_of_pos (Real.log_pos hx) A
  gcongr
  exact le_sup' c (mem_univ i)

open Classical in
/-- **The positive-level obligation combines across a finite cover of scales.** -/
theorem positiveLevelCoverage_of_cover {p : SupportParams} {f : ℕ → ℝ → ℂ} {t : ℝ → ℝ}
    {ι : Type*} [Finite ι] [Nonempty ι] {S : ι → Set ℝ}
    (hcover : ∀ x : ℝ, 1 < x → ∃ i, x ∈ S i)
    (h : ∀ i, PositiveLevelCoverage p (restrict (S i) f) t) :
    PositiveLevelCoverage p f t :=
  coverage_of_cover_aux hcover h

open Classical in
/-- **The sub-half obligation combines across a finite cover of scales**, by the same argument. -/
theorem subHalfCoverage_of_cover {p : SupportParams} {f : ℕ → ℝ → ℂ} {t : ℝ → ℝ}
    {ι : Type*} [Finite ι] [Nonempty ι] {S : ι → Set ℝ}
    (hcover : ∀ x : ℝ, 1 < x → ∃ i, x ∈ S i)
    (h : ∀ i, SubHalfCoverage p (restrict (S i) f) t) :
    SubHalfCoverage p f t :=
  coverage_of_cover_aux hcover h

/-! ## From an estimate and a containment to the positive-level obligation

The step every route needs, and the reason the per-range statements are not immediate. An estimate
gives a bound over its own moduli set `D x ω γ δ ε`; the obligation wants one over the generated
family's positive-level part. The containment closes the gap, and one observation makes it cheap.

**The target set does not depend on the stratum indices.** `moduliIIaFamily x ω γ δ
ε` and its companions
are functions of the chamber alone, so the union over `(j, j', m, m')` implicit in `Qstar` needs no
union bound — each modulus is routed by whichever tuple witnesses its membership, and they all land
in the same set.

What does need care is `ε`. `HasEquidistributionFamily` opens with `∃ ε₀, ∀ ε ∈ Ioo 0 ε₀`, so `ε`
is chosen inside, while the containments need it below their own bound. Taking `ε = min (ε₀/2) eb`
satisfies both. -/

open Classical in
/-- **An estimate plus a containment gives the positive-level obligation.** `eb` is the caller's
bound on the retreat — the containments need `ε'` small — and `(ω, γ, δs)` is the chamber point the
estimate is applied at. -/
theorem positiveLevelCoverage_of_containment {p : SupportParams} {f : ℕ → ℝ → ℂ} {t : ℝ → ℝ}
    {D : ℝ → ℝ → ℝ → ℝ → ℝ → Finset ℕ} {S : Set (ℝ × ℝ × ℝ)} {ω γ δs eb : ℝ}
    (heb : 0 < eb) (hmem : (ω, γ, δs) ∈ S) (h : HasEquidistributionFamily f D S)
    (hcont : ∀ ε : ℝ, 0 < ε → ε ≤ eb → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ x : ℝ, 1 < x → ∀ q : ℕ,
      q ∈ Finset.Icc 1 ⌊x⌋₊ → q ∈ Qstar p x ε₀ → Squarefree q → ¬ ((q : ℝ) < t x) →
      q ∈ D x ω γ δs ε) :
    PositiveLevelCoverage p f t := by
  obtain ⟨e₀, he₀, hmain⟩ := h
  intro ε₀ hε₀ A hA
  obtain ⟨c, hc, hbd⟩ := hmain (min (e₀ / 2) eb)
    ⟨lt_min (by linarith) heb, lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩ A hA
  refine ⟨c, hc, fun x hx a ha ↦ ?_⟩
  refine (discrepancySum_le_of_subset fun q hq ↦ ?_).trans (hbd (ω, γ, δs) hmem x hx a ha)
  simp only [Finset.mem_filter] at hq ⊢
  obtain ⟨⟨hqIcc, hqQ, hqsf⟩, hqlarge⟩ := hq
  exact ⟨hcont _ (lt_min (by linarith) heb) (min_le_right _ _) ε₀ hε₀ x hx q hqIcc hqQ hqsf
    hqlarge, hqsf⟩

end Gap212.Routing
