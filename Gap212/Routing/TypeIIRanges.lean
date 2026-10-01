/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.Assembly
public import Gap212.Routing.Swap

/-!
# Type II's three scale-sets, and the reduction of its positive level to them

Type II is the only Harman shape that needs localization: no single width covers its `γ`-range, so
the three estimates have to be applied on three different sets of *scales*. This module names those
sets and reduces the positive-level obligation to one statement per set.

## The exponent as a function of the scale

`Harman.TypeIIFamily` gives `∀ x > 1, ∃ g, … ∧ N x = x^g`, an existential. But
for `x > 1` the `g` is
determined — `g = log_x (N x)` — so `Gap212.Routing.gammaOf` names it, and
`Gap212.Routing.gammaOf_eq` recovers it from the existential. Without a *function* there are no
scale-sets to localize over.

## The three sets

Cut by the same two thresholds the routes use:

    S_a = {x | γ_loIIa ≤ γ(x)}                        Type IIa
    S_b = {x | γ_loIIb ≤ γ(x) < γ_loIIa}              Type IIb
    S_c = {x | γ(x) < γ_loIIb}                        Type IIc

They cover every scale by trichotomy, which is `Gap212.Routing.scaleII_cover`, and
`Gap212.Routing.typeII_positiveLevel_of_ranges` combines them through
`Gap212.Routing.positiveLevelCoverage_of_cover`.

What is left after this is one per-range statement — the estimate applied to the localized and
patched copy, through that range's containment. The `γ > 1/2` half of Type II's range is handled
inside `S_a` by the swap of `Gap212.Routing.Swap`, `1 - γ ≤ 1/2` landing there.

## Main results

* `Gap212.Routing.gammaOf`, `gammaOf_eq`: the exponent as a function of the scale.
* `Gap212.Routing.scaleIIa`, `scaleIIb`, `scaleIIc`, `scaleII_cover`.
* `Gap212.Routing.typeII_positiveLevel_of_ranges`: the reduction.
-/

@[expose] public section

namespace Gap212.Routing

open Finset Real

/-! ## The exponent as a function of the scale -/

/-- The exponent of a scale function at `x`: the `g` with `N x = x^g`, named. -/
noncomputable def gammaOf (N : ℝ → ℝ) (x : ℝ) : ℝ := logb x (N x)

/-- **`gammaOf` recovers the exponent from the existential.** For `x > 1` the `g` in `N x = x^g` is
unique, so `Harman.TypeIIFamily`'s existential determines a function. -/
theorem gammaOf_eq {N : ℝ → ℝ} {x g : ℝ} (hx : 1 < x) (h : N x = x ^ g) : gammaOf N x = g := by
  rw [gammaOf, h, Real.logb_rpow (b := x) (by linarith) (by linarith)]

/-! ## The three scale-sets -/

/-- The scales where the Type IIa route applies. -/
def scaleIIa (N : ℝ → ℝ) : Set ℝ := {x | gammaLoIIa ≤ gammaOf N x}

/-- The scales where the Type IIb route applies. -/
def scaleIIb (N : ℝ → ℝ) : Set ℝ :=
  {x | gammaLoIIb ≤ gammaOf N x ∧ gammaOf N x < gammaLoIIa}

/-- The scales where the Type IIc route applies. -/
def scaleIIc (N : ℝ → ℝ) : Set ℝ := {x | gammaOf N x < gammaLoIIb}

/-- **The three scale-sets cover**, by trichotomy against the two thresholds. -/
theorem scaleII_cover (N : ℝ → ℝ) (x : ℝ) :
    x ∈ scaleIIa N ∨ x ∈ scaleIIb N ∨ x ∈ scaleIIc N := by
  by_cases ha : gammaLoIIa ≤ gammaOf N x
  · exact Or.inl ha
  · by_cases hb : gammaLoIIb ≤ gammaOf N x
    · exact Or.inr (Or.inl ⟨hb, not_le.mp ha⟩)
    · exact Or.inr (Or.inr (not_le.mp hb))

/-! ## The reduction -/

/-- **Type II's positive level reduces to one statement per scale-set.** Each route applies on the
scales where its `γ`-range holds, and `positiveLevelCoverage_of_cover` puts the three together.

This is the shape localization forces: the three ranges cannot share a width, so they cannot share a
single application of a single estimate either. -/
theorem typeII_positiveLevel_of_ranges {p : SupportParams} {f : ℕ → ℝ → ℂ} {N : ℝ → ℝ} {t : ℝ → ℝ}
    (ha : PositiveLevelCoverage p (restrict (scaleIIa N) f) t)
    (hb : PositiveLevelCoverage p (restrict (scaleIIb N) f) t)
    (hc : PositiveLevelCoverage p (restrict (scaleIIc N) f) t) :
    PositiveLevelCoverage p f t := by
  classical
  refine positiveLevelCoverage_of_cover (ι := Fin 3)
    (S := fun i ↦ if i = 0 then scaleIIa N else if i = 1 then scaleIIb N else scaleIIc N)
    (fun x _ ↦ ?_) (fun i ↦ ?_)
  · rcases scaleII_cover N x with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, by simpa using h⟩
  · fin_cases i
    · simpa using ha
    · simpa using hb
    · simpa using hc

/-- The same reduction for the sub-half half, which the Type II routing also splits. -/
theorem typeII_subHalf_of_ranges {p : SupportParams} {f : ℕ → ℝ → ℂ} {N : ℝ → ℝ} {t : ℝ → ℝ}
    (ha : SubHalfCoverage p (restrict (scaleIIa N) f) t)
    (hb : SubHalfCoverage p (restrict (scaleIIb N) f) t)
    (hc : SubHalfCoverage p (restrict (scaleIIc N) f) t) :
    SubHalfCoverage p f t := by
  classical
  refine subHalfCoverage_of_cover (ι := Fin 3)
    (S := fun i ↦ if i = 0 then scaleIIa N else if i = 1 then scaleIIb N else scaleIIc N)
    (fun x _ ↦ ?_) (fun i ↦ ?_)
  · rcases scaleII_cover N x with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, by simpa using h⟩
  · fin_cases i
    · simpa using ha
    · simpa using hb
    · simpa using hc

end Gap212.Routing
