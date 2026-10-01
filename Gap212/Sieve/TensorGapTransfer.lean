/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.TensorFacts
public import Gap212.Sieve.UStrip
public meta import Gap212.Attr

/-!
# A tail that is compactly supported on `ℝ` carries no mass

For `g` vanishing on `(-∞, 0]`, the tail `(𝒯g)(t) = ∫_t^∞ g` equals the total mass `∫ g` at
every `t ≤ 0`. A tail with compact support on `ℝ` therefore has `(𝒯g)(0) = ∫_0^∞ g = 0`. This is
why the support conditions of `Gap212.GPY.TensorDatum` are stated on the nonnegative orthant rather
than on `ℝ`: on `ℝ` they would force every boundary value `f_{l,i}(0)` entering
`Gap212.Defs.formJMarginal` to vanish, and with it every form `𝓙ᵢ`.

## Main results

* `Gap212.GPY.tailTransform_eq_zero_of_hasCompactSupport`: a tail with compact support on `ℝ` has
  `(𝒯g)(0) = 0`.
-/

@[expose] public section

namespace Gap212.GPY

open MeasureTheory

/-! ### A compactly supported tail carries no mass -/

/-- **A tail that is compactly supported on `ℝ` has no mass.** If `g` vanishes on `(-∞,0]` and
`𝒯g` has compact support then `(𝒯g)(0) = ∫_0^∞ g = 0`.

Far below the support of `𝒯g` the tail is `0`, and there it already integrates all of `g`; since
`g` vanishes on the negatives that integral is `∫_0^∞ g`. -/
theorem tailTransform_eq_zero_of_hasCompactSupport {g : ℝ → ℝ}
    (hsupp : ∀ t : ℝ, t ≤ 0 → g t = 0) (hc : HasCompactSupport (tailTransform g)) :
    tailTransform g 0 = 0 := by
  -- The tail vanishes outside a ball, so it vanishes at some negative `t`.
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hrt : tailTransform g (-(|r| + 1)) = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun hmem ↦ ?_
    have := hr hmem
    rw [Real.closedBall_eq_Icc] at this
    have h1 : -(|r| + 1) ∈ Set.Icc (0 - r) (0 + r) := this
    have h2 : |r| + 1 ≤ r := by simpa using h1.1
    have := abs_nonneg r
    have := le_abs_self r
    linarith
  -- Both half-lines integrate all of `g`.
  have hall : ∀ b : ℝ, b ≤ 0 → (∫ t in Set.Ioi b, g t) = ∫ t, g t := by
    intro b hb
    rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
      (Set.subset_univ (Set.Ioi b)) ?_, setIntegral_univ]
    intro x hx
    exact hsupp x ((by simpa using hx.2 : x ≤ b).trans hb)
  have h0 := hall 0 le_rfl
  have hneg := hall (-(|r| + 1)) (by have := abs_nonneg r; linarith)
  simp only [tailTransform] at hrt ⊢
  rw [h0, ← hneg, hrt]

end Gap212.GPY
