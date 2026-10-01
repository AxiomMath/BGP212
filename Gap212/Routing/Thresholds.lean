/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.TypeIISubHalf
public meta import Gap212.Attr

/-!
# The threshold cannot be fixed before the retreat

`Gap212.Routing.hasEquidistributionOverQstar_of_halves` splits the generated moduli at a single
threshold `t` and shows that a bound below and a bound above suffice. That theorem is true. It is
also not instantiable, and the reason is where `t` is bound rather than anything about what the
inputs can reach.

## The two demands

* **Below.** Bilinear Bombieri–Vinogradov covers `q ≤ x^{1/2}(log x)^{-B}` and nothing above it, so
  `Gap212.Routing.SubHalfCoverage p f t` is reachable only where `t x ≤ x^{1/2}(log x)^{-B}`.
* **Above.** Every route's size hypothesis is of the form `x^{1/2 - ε₀ · cap} ≤ q`. So the
  containment can be applied at any threshold at or above that — but `t` in
  `Gap212.Routing.PositiveLevelCoverage` is fixed *before* `ε₀`, and demanding
  `t x ≥ x^{1/2 - ε₀ · cap}` for *every* `ε₀ > 0` forces `t x ≥ x^{1/2}` in the limit.

Since `(log x)^B > 1` wherever `log x > 1`, the two demands contradict each other. That is
`Gap212.Routing.no_single_threshold`, and it is why the `ε₀`-independent thresholds
`Gap212.Ranges.rangeBound_transitionModuli` is stated at are the wrong shape: at
`x^{1/2}(log x)^{-C}` the positive-level hypothesis cannot be met, and at `x^{1/2}` the sub-half
one cannot.

## A retreat-dependent threshold

Let the threshold depend on the retreat. `Gap212.Routing.SubHalfCoverageAt` and
`PositiveLevelCoverageAt` take `t : ℝ → ℝ → ℝ`, the retreat first, and
`Gap212.Routing.hasEquidistributionOverQstar_of_pointwise_halves` assembles them exactly as before
— the proof is unchanged, because nothing in it ever needed `t` to be uniform in `ε₀`. What changes
is that both sides are now satisfiable: below, `t ε₀ x = x^{1/2 - ε₀/100}` sits under BV's range
for large `x`; above, it sits over every route's `hqbig`.

## Main results

* `Gap212.Routing.no_single_threshold`: no threshold fixed before the retreat serves both halves.
* `Gap212.Routing.hasEquidistributionOverQstar_of_pointwise_halves`: the split with the threshold
  chosen per retreat — the form the routing can actually consume.
-/

@[expose] public section

namespace Gap212.Routing

open Finset Real

/-! ## The obstruction -/

/-- **No threshold fixed before the retreat serves both halves.** A `t` below bilinear
Bombieri–Vinogradov's range at every scale cannot also sit above `x^{1/2 - ε₀}` for every `ε₀ > 0`.

Witnessed at `x = e²`, where `log x = 2`: the first demand gives `t x ≤ x^{1/2} / 2^B` and the
second, applied at any `ε₀ < B log 2 / 2`, gives `t x > x^{1/2} / 2^B`.

The quantifier order is the whole content. Each demand alone is satisfiable; it is fixing `t`
before `ε₀` that makes them incompatible, and letting `t` depend on `ε₀` dissolves the conflict
without weakening either. -/
theorem no_single_threshold {B : ℝ} (hB : 0 < B) (t : ℝ → ℝ) :
    ¬ ((∀ x : ℝ, 1 < x → t x ≤ x ^ ((1 : ℝ) / 2) / (log x) ^ B) ∧
      (∀ ε₀ : ℝ, 0 < ε₀ → ∀ x : ℝ, 1 < x → x ^ ((1 : ℝ) / 2 - ε₀) ≤ t x)) := by
  rintro ⟨hlow, hhigh⟩
  set x : ℝ := exp 2 with hxdef
  have hx1 : 1 < x := by
    rw [hxdef]
    calc (1 : ℝ) = exp 0 := (Real.exp_zero).symm
      _ < exp 2 := Real.exp_lt_exp.mpr (by norm_num)
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hlog : log x = 2 := by rw [hxdef, Real.log_exp]
  -- The upper demand, made explicit at `x = e²`.
  have hup : t x ≤ x ^ ((1 : ℝ) / 2) / (2 : ℝ) ^ B := by
    have := hlow x hx1
    rwa [hlog] at this
  -- Pick a retreat small enough that the lower demand overshoots it.
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨ε₀, hε₀0, hε₀⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ * 2 < B * Real.log 2 :=
    ⟨B * Real.log 2 / 4, by positivity, by nlinarith⟩
  have hdown : x ^ ((1 : ℝ) / 2 - ε₀) ≤ t x := hhigh ε₀ hε₀0 x hx1
  -- `x^{1/2 - ε₀} > x^{1/2} / 2^B`, because `ε₀ log x < B log 2`.
  have hkey : x ^ ((1 : ℝ) / 2) / (2 : ℝ) ^ B < x ^ ((1 : ℝ) / 2 - ε₀) := by
    have hsplit : x ^ ((1 : ℝ) / 2 - ε₀) = x ^ ((1 : ℝ) / 2) / x ^ ε₀ := by
      rw [Real.rpow_sub hx0]
    rw [hsplit]
    have hxpow : x ^ ε₀ < (2 : ℝ) ^ B := by
      rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_lt_exp.mpr (by rw [hlog]; nlinarith)
    have hnum : (0 : ℝ) < x ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
    have hden : (0 : ℝ) < x ^ ε₀ := Real.rpow_pos_of_pos hx0 _
    exact div_lt_div_of_pos_left hnum hden hxpow
  linarith

/-! ## The retreat-dependent split -/

open Classical in
/-- **The sub-half obligation, at a retreat-dependent threshold.** Identical to
`Gap212.Routing.SubHalfCoverage` except that the threshold is handed the retreat first, which is
what lets it sit under bilinear Bombieri–Vinogradov's range. -/
def SubHalfCoverageAt (p : SupportParams) (f : ℕ → ℝ → ℂ) (t : ℝ → ℝ → ℝ) : Prop :=
  ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ c > (0 : ℝ), ∀ x : ℝ, 1 < x → ∀ a : ℕ, CoprimeBelow a x →
    ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ Squarefree q}.filter
      (fun n : ℕ ↦ (n : ℝ) < t ε₀ x), discrepancy f x a q ≤ c * x / (log x) ^ A

open Classical in
/-- **The positive-level obligation, at a retreat-dependent threshold.** Identical to
`Gap212.Routing.PositiveLevelCoverage` except for where the threshold is bound, which is what lets
it sit above every route's `hqbig`. -/
def PositiveLevelCoverageAt (p : SupportParams) (f : ℕ → ℝ → ℂ) (t : ℝ → ℝ → ℝ) : Prop :=
  ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ c > (0 : ℝ), ∀ x : ℝ, 1 < x → ∀ a : ℕ, CoprimeBelow a x →
    ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ Squarefree q}.filter
      (fun n : ℕ ↦ ¬ ((n : ℝ) < t ε₀ x)), discrepancy f x a q ≤ c * x / (log x) ^ A

open Classical in
/-- **The two halves together suffice, at a retreat-dependent threshold.** The same proof as
`Gap212.Routing.hasEquidistributionOverQstar_of_halves`: the two filters partition the sum and the
constants add. Nothing in it ever needed the threshold to be uniform in the retreat, which is
exactly why moving the binder costs nothing and buys satisfiability. -/
theorem hasEquidistributionOverQstar_of_pointwise_halves {p : SupportParams} {f : ℕ → ℝ → ℂ}
    {t : ℝ → ℝ → ℝ} (hsub : SubHalfCoverageAt p f t) (hpos : PositiveLevelCoverageAt p f t) :
    HasEquidistributionOverQstarFamily p f := by
  classical
  intro ε₀ hε₀ A hA
  obtain ⟨c₁, hc₁, h₁⟩ := hsub ε₀ hε₀ A hA
  obtain ⟨c₂, hc₂, h₂⟩ := hpos ε₀ hε₀ A hA
  refine ⟨c₁ + c₂, by linarith, fun x hx a ha ↦ ?_⟩
  have hring : c₁ * x / (log x) ^ A + c₂ * x / (log x) ^ A = (c₁ + c₂) * x / (log x) ^ A := by ring
  exact le_trans (sum_le_of_split (h₁ x hx a ha) (h₂ x hx a ha)) (le_of_eq hring)

/-! ## Reaching the retreat-dependent form from the per-threshold theorems

The half-obligations are proved at one threshold at a time —
`Gap212.Routing.typeII_subHalfCoverage`, for instance, gives
`SubHalfCoverage p f (fun x ↦ x^{1/2-κ})` for *every* `κ > 0`, from bilinear Bombieri–Vinogradov
alone. Those are exactly the ingredients the retreat-dependent form wants: instantiate `κ` at the
retreat.

Both bridges are one line, because `SubHalfCoverageAt p f t` and `SubHalfCoverage p f (t ε₀)` open
with the *same* `∀ ε₀ > 0`. Feeding the retreat to the threshold and to the obligation at once is
all that happens. That they are this cheap is the point: the obstruction was never about strength,
only about where the binder sat. -/

/-- **The sub-half half, at a retreat-dependent threshold, from the per-threshold family.** -/
theorem subHalfCoverageAt_of_pointwise {p : SupportParams} {f : ℕ → ℝ → ℂ} {t : ℝ → ℝ → ℝ}
    (h : ∀ ε₀ : ℝ, 0 < ε₀ → SubHalfCoverage p f (t ε₀)) :
    SubHalfCoverageAt p f t :=
  fun ε₀ hε₀ A hA ↦ h ε₀ hε₀ ε₀ hε₀ A hA

/-- **The positive-level half, likewise.** -/
theorem positiveLevelCoverageAt_of_pointwise {p : SupportParams} {f : ℕ → ℝ → ℂ}
    {t : ℝ → ℝ → ℝ} (h : ∀ ε₀ : ℝ, 0 < ε₀ → PositiveLevelCoverage p f (t ε₀)) :
    PositiveLevelCoverageAt p f t :=
  fun ε₀ hε₀ A hA ↦ h ε₀ hε₀ ε₀ hε₀ A hA

/-- **Equidistribution from the two per-retreat families.** The form the routing consumes: a
sub-half bound and a positive-level bound at each retreat, at a threshold that may depend on it.

For Type II the first family is `Gap212.Routing.typeII_subHalfCoverage` applied at `κ = ε₀ · cap`,
which needs nothing but bilinear Bombieri–Vinogradov; the second is what the six route containments
deliver, now that they are asked at a threshold their `hqbig` can actually reach. -/
theorem hasEquidistributionOverQstar_of_pointwise_families {p : SupportParams} {f : ℕ → ℝ → ℂ}
    {t : ℝ → ℝ → ℝ}
    (hsub : ∀ ε₀ : ℝ, 0 < ε₀ → SubHalfCoverage p f (t ε₀))
    (hpos : ∀ ε₀ : ℝ, 0 < ε₀ → PositiveLevelCoverage p f (t ε₀)) :
    HasEquidistributionOverQstarFamily p f :=
  hasEquidistributionOverQstar_of_pointwise_halves
    (subHalfCoverageAt_of_pointwise hsub) (positiveLevelCoverageAt_of_pointwise hpos)

/-- **Type II's sub-half family, from bilinear Bombieri–Vinogradov alone.** The retreat-scaled
threshold `x^{1/2 - ε₀ · cap}` is admissible for every positive `cap`, so this is
`Gap212.Routing.typeII_subHalfCoverage` with `κ` instantiated at the retreat.

This is one of the two families `Gap212.Routing.hasEquidistributionOverQstar_of_pointwise_families`
needs, and it is the half that was unreachable at any fixed threshold. -/
theorem typeII_subHalfCoverage_family {ξ₂ cap : ℝ} {f : ℕ → ℝ → ℂ} {p : SupportParams}
    (hbv : Inputs.BilinearBombieriVinogradovFamily) (hξ : 0 < ξ₂ - Harman.slack) (hcap : 0 < cap)
    (hf : Harman.TypeIIFamily ξ₂ f) :
    ∀ ε₀ : ℝ, 0 < ε₀ → SubHalfCoverage p f (fun x ↦ x ^ (1 / 2 - ε₀ * cap)) :=
  fun _ hε₀ ↦ typeII_subHalfCoverage hbv hξ (mul_pos hε₀ hcap) hf

/-- **A uniform threshold is a special case.** Reading a `t : ℝ → ℝ` as ignoring the retreat
recovers the original two-way split, so nothing is lost by the retreat-dependent form. -/
theorem subHalfCoverageAt_const {p : SupportParams} {f : ℕ → ℝ → ℂ} {t : ℝ → ℝ}
    (h : SubHalfCoverage p f t) : SubHalfCoverageAt p f (fun _ ↦ t) := h

/-- The same for the positive-level half. -/
theorem positiveLevelCoverageAt_const {p : SupportParams} {f : ℕ → ℝ → ℂ} {t : ℝ → ℝ}
    (h : PositiveLevelCoverage p f t) : PositiveLevelCoverageAt p f (fun _ ↦ t) := h

end Gap212.Routing
