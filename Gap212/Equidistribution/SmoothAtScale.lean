/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Gap212.Equidistribution.CoefficientSequence
public meta import Gap212.Attr

/-!
# Smoothness at a scale, with the derivative bounds quantified correctly

[2, Definition 6 (iii)] asks that `α(n;x) = ψ(n/N(x))` for a smooth `ψ` supported on an
absolute interval whose derivatives satisfy `|ψ^{(j)}(t)| ≪_j log(x)^{O_j(1)}`.

## Why this definition exists alongside `Gap212.IsSmoothAtScaleFamily`

`Gap212.IsSmoothAtScaleFamily` binds the derivative bound `b` and exponent `m` *inside* `∀ x`:

    ∃ c C, 0 < c ∧ c ≤ C ∧
      ∀ x, 1 < x → ∃ ψ, … ∧ (∀ j, ∃ b m, 0 < b ∧ ∀ t, ‖iteratedDeriv j ψ t‖ ≤ b * (log x) ^ m) ∧ …

That is not what `≪_j` and `O_j(1)` say, and it is much weaker than intended: the constant and
the exponent may be re-chosen for each `x`, so a family whose derivatives grow arbitrarily fast
in `x` satisfies it. Since the bound is then permitted to absorb any `x`-dependence, the
condition carries almost no information about the family.

The definition below binds `b` and `m` as functions of `j` alone, *before* `x`, which is the
reading the subscripted `≪_j` and `O_j(1)` intend and the one the challenge file states. It is
therefore strictly stronger, so any consumer of that definition is still satisfied by
a family meeting this one.

## Main definitions

* `Gap212.Corrected.IsSmoothAtScaleFamily`: [2, Definition 6 (iii)] with uniform derivative bounds.
-/

@[expose] public section

namespace Gap212.Corrected

open Real

/-- `α` is **smooth at scale** `N` ([2, Definition 6 (iii)]): for absolute `0 < c ≤ C` and sequences
`b : ℕ → ℝ`, `m : ℕ → ℕ` chosen once and for all, every `x > 1` admits a smooth `ψ` vanishing
off `[c, C]` with `α(n;x) = ψ(n/N(x))` and `|ψ^{(j)}(t)| ≤ b j * (log x) ^ m j` for all `j, t`.

`b` and `m` are bound before `x` and depend on `j` alone. See the module docstring: binding them
inside `∀ x`, as `Gap212.IsSmoothAtScaleFamily` does, lets the bound be re-chosen per `x` and
drains the condition of content.

`Gap212.IsSmoothAtScale` takes `b` and `m` as explicit arguments, which builds the same
uniformity into the single-scale form. -/
def IsSmoothAtScaleFamily (α : ℕ → ℝ → ℂ) (N : ℝ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∃ (b : ℕ → ℝ) (m : ℕ → ℕ), (∀ j, 0 < b j) ∧
    ∀ (x : ℝ), 1 < x → ∃ ψ : ℝ → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      (∀ t : ℝ, ψ t ≠ 0 → t ∈ Set.Icc c C) ∧
      (∀ (j : ℕ) (t : ℝ), ‖iteratedDeriv j ψ t‖ ≤ b j * (log x) ^ m j) ∧
      ∀ n : ℕ, α n x = ψ ((n : ℝ) / N x)

/-- The corrected notion implies `Gap212.IsSmoothAtScaleFamily`, so nothing that consumes
that definition is weakened by supplying this instead. Given `b` and `m` uniform in
`x`, the witnesses required inside `∀ x` are those same values. -/
theorem isSmoothAtScale_le {α : ℕ → ℝ → ℂ} {N : ℝ → ℝ} (h : IsSmoothAtScaleFamily α N) :
    Gap212.IsSmoothAtScaleFamily α N := by
  obtain ⟨c, C, hc, hcC, b, m, hb, hx⟩ := h
  refine ⟨c, C, hc, hcC, ?_⟩
  intro x hx1
  obtain ⟨ψ, hψsmooth, hψsupp, hψderiv, hψeq⟩ := hx x hx1
  exact ⟨ψ, hψsmooth, hψsupp, fun j ↦ ⟨b j, m j, hb j, fun t ↦ hψderiv j t⟩, hψeq⟩

end Gap212.Corrected
