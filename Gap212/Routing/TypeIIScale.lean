/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Harman
public import Gap212.Routing.RangeCompare
public import Gap212.Inputs.BilinearBV

/-!
# Type II members satisfy bilinear Bombieri–Vinogradov's scale condition

The scale condition of bilinear Bombieri–Vinogradov, supplied for a Type II member.

## `∀ x > 1` and "eventually" are not interchangeable for hypotheses

[1, Theorem 2.9] states the scale condition as `min(M,N) ≥ x^η` with no quantifier on `x`, every
statement there being asymptotic. Read literally as `∀ x > 1` the citation is **unusable**, and
not for a technical reason:

A Type II member gives `N x = x^g` with `ξ₂ - ϵ ≤ g ≤ 1 - ξ₂ + ϵ`, so `N x ≥ x^{ξ₂-ϵ}` pointwise —
fine. But `M` is pinned only by `M x · N x ≍ x`, i.e. `c x ≤ M x N x` **with a constant**, giving
`M x ≥ c x^{1-g}`. If `c < 1` then as `x → 1⁺` the left side tends to `c` while `x^η → 1`, and the
pointwise inequality fails however small `η` is taken.

So the eventual reading is the faithful one, and
`Gap212.Inputs.BilinearBombieriVinogradovFamily` states
it that way. Note where the `∀ x > 1` convention had to break: for *conclusions* it is free, since
near `x = 1` the bound `c x/(log x)^A` blows up; for *hypotheses* it is not.

## What the condition costs

`Gap212.Routing.typeII_scale_eventually` supplies it at `η = (ξ₂ - ϵ)/2`. Half the exponent is
given away, and that is what buys the threshold: `x^η ≤ c x^{2η}` holds once `x^η ≥ 1/c`, which
`tendsto_rpow_atTop` makes eventual. The `N` half needs no threshold at all.

With this, every BV hypothesis is available for a Type II member — it is already a two-fold
convolution with Siegel–Walfisz on both factors — so the Type II sub-half obligation reduces to the
range comparison of `Gap212.Routing.RangeCompare`.

## Main results

* `Gap212.Routing.typeII_scale_eventually`: every BV hypothesis, for a Type II member of the Harman
  class, at `η = (ξ₂ - ϵ)/2`.
-/

@[expose] public section

namespace Gap212.Routing

open Filter Real

/-- **Every bilinear Bombieri–Vinogradov hypothesis holds for a Type II member**, at
`η = (ξ₂ - ϵ)/2`.

`N` needs no threshold: `N x = x^g ≥ x^{ξ₂-ϵ} ≥ x^η` for every `x > 1`. `M` does, being pinned only
up to the constant of `M N ≍ x`; `x^η ≤ c x^{2η}` requires `x^η ≥ 1/c`. -/
theorem typeII_scale_eventually {ξ₂ : ℝ} {f : ℕ → ℝ → ℂ}
    (hξ : 0 < ξ₂ - Harman.slack) (hf : Harman.TypeIIFamily ξ₂ f) :
    ∃ (α β : ℕ → ℝ → ℂ) (M N : ℝ → ℝ) (η : ℝ), 0 < η ∧
      f = dconvFamily α β ∧
      IsCoefficientSequenceFamily α ∧ LocatedAtScaleFamily α M ∧
      IsCoefficientSequenceFamily β ∧ LocatedAtScaleFamily β N ∧ HasSiegelWalfiszFamily β N ∧
      AsympEq (fun x ↦ M x * N x) id ∧
      (∃ X : ℝ, ∀ x : ℝ, X ≤ x → x ^ η ≤ M x ∧ x ^ η ≤ N x) := by
  obtain ⟨α, β, M, N, hfeq, hα, hαM, -, hβ, hβN, hβSW, hprod, hexp⟩ := hf
  refine ⟨α, β, M, N, (ξ₂ - Harman.slack) / 2, by linarith, hfeq, hα, hαM, hβ, hβN, hβSW,
    hprod, ?_⟩
  obtain ⟨c, C, hc, -, hbd⟩ := hprod
  -- The `M` half needs `x^η ≥ 1/c`, which holds eventually.
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (y := (ξ₂ - Harman.slack) / 2) (by linarith)).eventually_ge_atTop (1 / c))
  refine ⟨max X₁ 2, fun x hx ↦ ?_⟩
  have hx1 : (1 : ℝ) < x := by linarith [le_max_right X₁ 2]
  have hx0 : (0 : ℝ) < x := by linarith
  have hcx : 1 / c ≤ x ^ ((ξ₂ - Harman.slack) / 2) := hX₁ x (le_of_max_le_left hx)
  obtain ⟨g, hglo, hghi, hNx⟩ := hexp x hx1
  have hlow : c * x ≤ M x * x ^ g := by simpa [id, hNx] using (hbd x hx1).1
  -- `N`: the exponent only has to be shrunk.
  refine ⟨?_, by rw [hNx]; exact Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)⟩
  -- `M`: divide `c x ≤ M x · N x` by `N x = x^g`.
  calc x ^ ((ξ₂ - Harman.slack) / 2)
      = c * (1 / c * x ^ ((ξ₂ - Harman.slack) / 2)) := by field_simp
    _ ≤ c * (x ^ ((ξ₂ - Harman.slack) / 2) * x ^ ((ξ₂ - Harman.slack) / 2)) := by
        gcongr
    _ = c * x ^ (2 * ((ξ₂ - Harman.slack) / 2)) := by rw [two_mul, Real.rpow_add hx0]
    _ ≤ c * x ^ (1 - g) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)) hc.le
    _ = c * x / x ^ g := by rw [Real.rpow_sub hx0, Real.rpow_one]; ring
    _ ≤ M x := by rwa [div_le_iff₀ (by positivity)]

end Gap212.Routing
