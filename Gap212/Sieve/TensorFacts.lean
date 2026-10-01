/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.EndgameDefs
public import Gap212.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Pi
public meta import Gap212.Attr

/-!
# The tail transform, and the discrete forms as integrals

The tensor construction runs the sieve backwards: the sieve weight built from profiles `f`
evaluates to a quadratic form in the numbers `∫₀^∞ f'_{l,s}f'_{l',s}` and `f_{l,i}(0)`, and the
variational problem is about integrals of `F` itself. What joins the two is the tail transform
`(𝒯g)(t) = ∫_t^∞ g`, whose derivative is `-g` and whose value at `0` is the total mass of `g`; so
the divisor profiles are taken to be tails, and the two discrete forms become honest integrals of
the tensor sum and of its marginals.

## What each result does

* `Gap212.GPY.hasDerivAt_tailTransform` and `Gap212.GPY.contDiff_tailTransform`: `𝒯g` is smooth and
  differentiates back to `-g`. This is what makes the *derivative* pairings in the discrete energy
  computable, and — with `tailTransform g 0 = ∫₀^∞ g`, which holds by definition — what makes the
  boundary factors in the discrete marginal form the total masses.
* `Gap212.GPY.prod_tailTransform_eq_zero`: a product of tails is supported on a *downward* box.
  This is the shape the support region can contain, and it is why the construction uses tails at
  all.
* `Gap212.GPY.formI_of_tensor`, `Gap212.GPY.formJ_of_tensor`: the two discrete forms
  `Gap212.Defs.formI` and `Gap212.Defs.formJMarginal` as integrals over the orthant, of the tensor
  sum and of its `i`-th marginal.

## Smoothness, and the exponent `⊤`

`ContDiff ℝ ⊤` with `⊤ : WithTop ℕ∞` is *analyticity*, not `C^∞`; the smoothness statements here
are therefore at `(⊤ : ℕ∞)`, the genuine `C^∞`. A non-zero compactly supported function on `ℝ` is
never analytic, so no statement about compactly supported bump factors can be made at the larger
exponent.

## Where the orthant sits

The forms are integrals over `[0,∞)^k`, written `Set.univ.pi fun _ ↦ Set.Ici 0`. Internally every
fibre integral is over `Set.Ioi 0`: the two restrictions of Lebesgue measure on `ℝ` agree, since
they differ on a point, and that identification (`Gap212.GPY.volume_restrict_orthant`) is what lets
Mathlib's product Fubini act on the orthant at all.
-/

@[expose] public section

namespace Gap212.GPY

open Finset MeasureTheory Set

/-! ### The tail transform -/

/-- **The tail transform differentiates back.** For continuous compactly supported `g`,
`(𝒯g)'(t) = -g(t)` at every `t`.

The tail is a constant minus a primitive: `∫_t^∞ g = ∫_a^∞ g - ∫_a^t g` for any `a ≤ t`, and the
fundamental theorem of calculus differentiates the second term. -/
theorem hasDerivAt_tailTransform {g : ℝ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g)
    (t : ℝ) : HasDerivAt (tailTransform g) (-g t) t := by
  have hint : Integrable g := hg.integrable_of_hasCompactSupport hc
  have hderiv :
      HasDerivAt (fun u ↦ tailTransform g (t - 1) - ∫ x in (t - 1)..u, g x) (-g t) t := by
    have h1 : HasDerivAt (fun u ↦ ∫ x in (t - 1)..u, g x) (g t) t :=
      intervalIntegral.integral_hasDerivAt_right hint.intervalIntegrable
        (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
    simpa using h1.const_sub (tailTransform g (t - 1))
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds (show t - 1 < t by linarith)] with u hu
  have := intervalIntegral.integral_Ioi_sub_Ioi hint.integrableOn hu.le
  simp only [tailTransform] at *
  linarith

/-- The derivative of a tail, as a function: `(𝒯g)' = -g`. -/
theorem deriv_tailTransform {g : ℝ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    deriv (tailTransform g) = -g :=
  funext fun t ↦ (hasDerivAt_tailTransform hg hc t).deriv

/-- **The tail transform differentiates back**: for smooth
compactly supported `g`, the tail `𝒯g` is smooth and `(𝒯g)' = -g`.

Smoothness is `C^∞`, i.e. `ContDiff ℝ (⊤ : ℕ∞)`: it follows from `(𝒯g)' = -g` by
`contDiff_infty_iff_deriv`, the tail being differentiable everywhere. -/
@[gap212 "lem_tail_derivative"]
theorem contDiff_tailTransform {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) :
    ContDiff ℝ (⊤ : ℕ∞) (tailTransform g) ∧ deriv (tailTransform g) = -g := by
  have hcont : Continuous g := hg.continuous
  have hd : ∀ t, HasDerivAt (tailTransform g) (-g t) t := hasDerivAt_tailTransform hcont hc
  have hderiv : deriv (tailTransform g) = -g := deriv_tailTransform hcont hc
  refine ⟨contDiff_infty_iff_deriv.2 ⟨fun t ↦ (hd t).differentiableAt, ?_⟩, hderiv⟩
  rw [hderiv]
  exact hg.neg

/-- **A product of tails is supported on a downward box.** If each `gᵢ` vanishes above `βᵢ`, then
`∏ᵢ (𝒯gᵢ)(tᵢ)` vanishes as soon as one coordinate exceeds its `βᵢ`.

Only the support hypothesis is used; continuity and compact support play no part, the offending
factor being an integral of the zero function. -/
@[gap212 "lem_tail_box_support"]
theorem prod_tailTransform_eq_zero {k : ℕ} {g : Fin k → ℝ → ℝ} {β : Fin k → ℝ}
    (hsupp : ∀ i, Function.support (g i) ⊆ Set.Iic (β i)) {t : Fin k → ℝ} {i : Fin k}
    (hi : β i < t i) : ∏ s : Fin k, tailTransform (g s) (t s) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  have hz : ∀ x ∈ Set.Ioi (t i), g i x = 0 := by
    intro x hx
    by_contra h
    exact absurd (hsupp i h) (by simp only [Set.mem_Iic, not_le]; exact hi.trans hx)
  simpa [tailTransform] using setIntegral_eq_zero_of_forall_eq_zero hz

/-! ### Fubini on the orthant -/

/-- Lebesgue measure on `ℝ^k` restricted to the closed orthant `[0,∞)^k` is the product of the
restrictions to the open half-line `(0,∞)`.

Going to the *open* half-line is what matches Mathlib's one-dimensional integrals over `Set.Ioi`,
and it costs nothing: the two restrictions of Lebesgue measure on `ℝ` are equal, differing on a
single point. -/
theorem volume_restrict_orthant (k : ℕ) :
    (volume : Measure (Fin k → ℝ)).restrict (Set.univ.pi fun _ ↦ Set.Ici (0 : ℝ))
      = Measure.pi (fun _ : Fin k ↦ volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hIci : (volume.restrict (Set.Ici (0 : ℝ))) = volume.restrict (Set.Ioi 0) :=
    (Measure.restrict_congr_set Ioi_ae_eq_Ici).symm
  rw [volume_pi, Measure.restrict_pi_pi]
  simp only [hIci]

/-- **The product of one-dimensional integrals is the integral of the product over the orthant.**
No integrability hypothesis: Mathlib's `integral_fintype_prod_eq_prod` holds unconditionally. -/
theorem integral_orthant_prod {k : ℕ} (F : Fin k → ℝ → ℝ) :
    (∫ t in Set.univ.pi fun _ : Fin k ↦ Set.Ici (0 : ℝ), ∏ s, F s (t s))
      = ∏ s, ∫ x in Set.Ioi (0 : ℝ), F s x := by
  rw [volume_restrict_orthant]
  exact integral_fintype_prod_eq_prod fun s ↦ F s

/-- A product of pairwise products of continuous functions, one of each pair compactly supported,
is integrable on the orthant. This is the hypothesis every exchange of the finite tensor sums with
the integral below needs. -/
theorem integrableOn_orthant_prod_mul {k : ℕ} (u v : Fin k → ℝ → ℝ) (hu : ∀ s, Continuous (u s))
    (hv : ∀ s, Continuous (v s)) (hcu : ∀ s, HasCompactSupport (u s)) :
    IntegrableOn (fun t : Fin k → ℝ ↦ ∏ s, (u s (t s) * v s (t s)))
      (Set.univ.pi fun _ ↦ Set.Ici (0 : ℝ)) := by
  rw [IntegrableOn, volume_restrict_orthant]
  refine MeasureTheory.Integrable.fin_nat_prod
    (μ := fun _ : Fin k ↦ volume.restrict (Set.Ioi (0 : ℝ)))
    (f := fun s x ↦ u s x * v s x) fun s ↦ ?_
  exact (((hu s).mul (hv s)).integrable_of_hasCompactSupport (hcu s).mul_right).restrict

/-! ### The discrete energy -/

/-- **The discrete energy is the square of the tensor sum.** When the divisor profiles are tails
`f_{l,s} = 𝒯g_{l,s}` of continuous compactly supported `g_{l,s}`, the form `𝓘` assembled from the
derivative pairings `∫₀^∞ f'_{l,s}f'_{l',s}` is exactly `∫_{[0,∞)^k} (∑ₗ cₗ ∏ₛ g_{l,s})²`.

Two signs cancel — `f' = -g` in both factors — so the derivative pairing is the pairing of the
`g`'s themselves; the rest is Fubini on the orthant and the expansion of a square of a finite sum.
No support hypothesis on the `g`'s is needed: the identity is between the same two integrals
however they sit relative to the orthant. -/
@[gap212 "lem_calI_of_tensor"]
theorem formI_of_tensor {L k : ℕ} (c : Fin L → ℝ) (g : Fin L → Fin k → ℝ → ℝ)
    (hg : ∀ l s, Continuous (g l s)) (hgc : ∀ l s, HasCompactSupport (g l s)) :
    Gap212.Defs.formI c (fun l l' s ↦ ∫ t in Set.Ioi (0 : ℝ),
        deriv (tailTransform (g l s)) t * deriv (tailTransform (g l' s)) t)
      = ∫ t in Set.univ.pi fun _ : Fin k ↦ Set.Ici (0 : ℝ),
          (∑ l, c l * ∏ s, g l s (t s)) ^ 2 := by
  classical
  have hd : ∀ l s, deriv (tailTransform (g l s)) = -(g l s) := fun l s ↦
    deriv_tailTransform (hg l s) (hgc l s)
  have hint : ∀ l l' : Fin L, IntegrableOn
      (fun t : Fin k → ℝ ↦ c l * c l' * ∏ s, (g l s (t s) * g l' s (t s)))
      (Set.univ.pi fun _ ↦ Set.Ici (0 : ℝ)) := fun l l' ↦
    (integrableOn_orthant_prod_mul _ _ (hg l) (hg l') (hgc l)).const_mul _
  have hsq : ∀ t : Fin k → ℝ, (∑ l, c l * ∏ s, g l s (t s)) ^ 2
      = ∑ l : Fin L, ∑ l' : Fin L, c l * c l' * ∏ s, (g l s (t s) * g l' s (t s)) := by
    intro t
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun l' _ ↦ ?_
    rw [Finset.prod_mul_distrib]
    ring
  simp only [hsq]
  rw [integral_finsetSum _ fun l _ ↦ integrable_finsetSum _ fun l' _ ↦ hint l l']
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [integral_finsetSum _ fun l' _ ↦ hint l l']
  refine Finset.sum_congr rfl fun l' _ ↦ ?_
  rw [integral_const_mul, integral_orthant_prod fun s x ↦ g l s x * g l' s x]
  simp only [hd, Pi.neg_apply, neg_mul_neg]

/-! ### The discrete marginal form -/

/-- **The discrete marginal form as a marginal integral.** With the same tail profiles, `𝓙ᵢ` is
`∫_{[0,∞)^{k-1}} (Γᵢ² - Γ_{i,𝓤}²)`, the two functions being the `i`-th tensor marginal and its high
part.

The left-hand side is `Gap212.Defs.formJMarginal`, which *is* `𝓙ᵢ`: nothing is
written out beside it. It is not `Gap212.Defs.formJLowLow`, the low–low group alone, which
differs from it by a cross term.

Pointwise `Γᵢ = Γ_{i,𝓛} + Γ_{i,𝓤}`, so
`Γ_{i,𝓛}² + 2Γ_{i,𝓛}Γ_{i,𝓤} = Γᵢ² - Γ_{i,𝓤}²`, and it is the sum of the low–low group and twice
the high–low one that telescopes. The rest is the same Fubini as the energy, plus
`f_{l,i}(0) = ∫₀^∞ g_{l,i}`, which holds by definition of the tail. -/
@[gap212 "lem_calJ_of_tensor"]
theorem formJ_of_tensor {L m : ℕ} (c : Fin L → ℝ) (g : Fin L → Fin (m + 1) → ℝ → ℝ)
    (i : Fin (m + 1)) (inMarg : Fin L → Prop) [DecidablePred inMarg]
    (hg : ∀ l s, Continuous (g l s)) (hgc : ∀ l s, HasCompactSupport (g l s)) :
    Gap212.Defs.formJMarginal c (fun l ↦ tailTransform (g l i) 0)
        (fun l l' s ↦ ∫ t in Set.Ioi (0 : ℝ),
          deriv (tailTransform (g l (i.succAbove s))) t *
            deriv (tailTransform (g l' (i.succAbove s))) t)
        (Gap212.Defs.LSet inMarg) (Gap212.Defs.USet inMarg)
      = ∫ u in Set.univ.pi fun _ : Fin m ↦ Set.Ici (0 : ℝ),
          (tensorMarginal c g i u ^ 2
            - tensorMarginalHigh c g (Gap212.Defs.USet inMarg) i u ^ 2) := by
  classical
  set 𝓛 := Gap212.Defs.LSet inMarg with h𝓛
  set 𝓤 := Gap212.Defs.USet inMarg with h𝓤
  set a : Fin L → ℝ := fun l ↦ c l * tailTransform (g l i) 0 with ha
  set P : Fin L → (Fin m → ℝ) → ℝ := fun l u ↦ ∏ s : Fin m, g l (i.succAbove s) (u s) with hP
  set S : Set (Fin m → ℝ) := Set.univ.pi fun _ : Fin m ↦ Set.Ici (0 : ℝ) with hS
  -- The derivative pairing is the pairing of the `g`'s.
  have hd : ∀ l s, deriv (tailTransform (g l s)) = -(g l s) := fun l s ↦
    deriv_tailTransform (hg l s) (hgc l s)
  have hinner : ∀ (l l' : Fin L) (s : Fin m), (∫ t in Set.Ioi (0 : ℝ),
      deriv (tailTransform (g l (i.succAbove s))) t *
        deriv (tailTransform (g l' (i.succAbove s))) t)
      = ∫ t in Set.Ioi (0 : ℝ), g l (i.succAbove s) t * g l' (i.succAbove s) t := by
    intro l l' s
    simp only [hd, Pi.neg_apply, neg_mul_neg]
  -- Each pair of marginal products integrates to the product of its fibre pairings.
  have hfub : ∀ l l' : Fin L, (∫ u in S, P l u * P l' u)
      = ∏ s : Fin m, ∫ t in Set.Ioi (0 : ℝ), g l (i.succAbove s) t * g l' (i.succAbove s) t := by
    intro l l'
    have hprod : ∀ u : Fin m → ℝ, P l u * P l' u
        = ∏ s : Fin m, (g l (i.succAbove s) (u s) * g l' (i.succAbove s) (u s)) := fun u ↦ by
      rw [hP]; exact (Finset.prod_mul_distrib).symm
    simp only [hS, hprod]
    exact integral_orthant_prod fun s x ↦ g l (i.succAbove s) x * g l' (i.succAbove s) x
  have hint : ∀ l l' : Fin L, IntegrableOn (fun u ↦ a l * a l' * (P l u * P l' u)) S := by
    intro l l'
    have hprod : (fun u : Fin m → ℝ ↦ a l * a l' * (P l u * P l' u))
        = fun u ↦ a l * a l' *
          ∏ s : Fin m, (g l (i.succAbove s) (u s) * g l' (i.succAbove s) (u s)) := by
      funext u
      simp only [hP]
      rw [← Finset.prod_mul_distrib]
    rw [hprod, hS]
    exact (integrableOn_orthant_prod_mul _ _ (fun s ↦ hg l (i.succAbove s))
      (fun s ↦ hg l' (i.succAbove s)) fun s ↦ hgc l (i.succAbove s)).const_mul _
  -- The pointwise telescoping of the two squares.
  have hpt : ∀ u : Fin m → ℝ,
      tensorMarginal c g i u ^ 2 - tensorMarginalHigh c g 𝓤 i u ^ 2
        = (∑ l ∈ 𝓛, ∑ l' ∈ 𝓛, a l * a l' * (P l u * P l' u))
          + 2 * ∑ l ∈ 𝓤, ∑ l' ∈ 𝓛, a l * a l' * (P l u * P l' u) := by
    intro u
    have hΓ : tensorMarginal c g i u = ∑ l : Fin L, a l * P l u :=
      Finset.sum_congr rfl fun l _ ↦ by simp only [ha, hP, tailTransform, mul_assoc]
    have hU : tensorMarginalHigh c g 𝓤 i u = ∑ l ∈ 𝓤, a l * P l u :=
      Finset.sum_congr rfl fun l _ ↦ by simp only [ha, hP, tailTransform, mul_assoc]
    have hsplit : ∑ l : Fin L, a l * P l u
        = (∑ l ∈ 𝓛, a l * P l u) + ∑ l ∈ 𝓤, a l * P l u := by
      rw [h𝓛, h𝓤, Gap212.Defs.LSet, Gap212.Defs.USet]
      exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hpair : ∀ s t : Finset (Fin L), (∑ l ∈ s, ∑ l' ∈ t, a l * a l' * (P l u * P l' u))
        = (∑ l ∈ s, a l * P l u) * ∑ l' ∈ t, a l' * P l' u := by
      intro s t
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun l' _ ↦ by ring
    rw [hΓ, hU, hsplit, hpair 𝓛 𝓛, hpair 𝓤 𝓛]
    ring
  have hIA : IntegrableOn (fun u ↦ ∑ l ∈ 𝓛, ∑ l' ∈ 𝓛, a l * a l' * (P l u * P l' u)) S :=
    integrable_finsetSum _ fun l _ ↦ integrable_finsetSum _ fun l' _ ↦ hint l l'
  have hIB : IntegrableOn (fun u ↦ ∑ l ∈ 𝓤, ∑ l' ∈ 𝓛, a l * a l' * (P l u * P l' u)) S :=
    integrable_finsetSum _ fun l _ ↦ integrable_finsetSum _ fun l' _ ↦ hint l l'
  -- Each group is the integral of its own double sum.
  have hgroup : ∀ s t : Finset (Fin L),
      (∫ u in S, ∑ l ∈ s, ∑ l' ∈ t, a l * a l' * (P l u * P l' u))
      = ∑ l ∈ s, ∑ l' ∈ t, c l * c l' * tailTransform (g l i) 0 * tailTransform (g l' i) 0 *
          ∏ σ : Fin m, ∫ x in Set.Ioi (0 : ℝ),
            deriv (tailTransform (g l (i.succAbove σ))) x *
              deriv (tailTransform (g l' (i.succAbove σ))) x := by
    intro s t
    rw [integral_finsetSum _ fun l _ ↦ integrable_finsetSum _ fun l' _ ↦ hint l l']
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [integral_finsetSum _ fun l' _ ↦ hint l l']
    refine Finset.sum_congr rfl fun l' _ ↦ ?_
    rw [integral_const_mul, hfub l l']
    simp only [hinner, ha]
    ring
  simp only [hpt, Gap212.Defs.formJMarginal, Gap212.Defs.formJLowLow]
  rw [integral_add hIA (hIB.const_mul 2), integral_const_mul, hgroup 𝓛 𝓛, hgroup 𝓤 𝓛]

end Gap212.GPY
