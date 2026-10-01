/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.Convolution
public import Gap212.Routing.Assembly
public import Gap212.Routing.TypeIIScale

/-!
# Type II's sub-half obligation, discharged

A `Gap212.Routing.SubHalfCoverage` instance, for the one shape that needs no Heath–Brown
decomposition: a Type II member is already `dconvFamily α β` with Siegel–Walfisz on both factors —
exactly BV's shape.

## The three pieces, and how they meet

* **shape** — `Gap212.Routing.typeII_scale_eventually` supplies every BV hypothesis,
  including the scale condition in its eventual form;
* **range** — `Gap212.Routing.exists_threshold_ranges_compare` (the `X₀` past which
  `x^{1/2-κ} ≤ x^{1/2}(log x)^{-B}`) puts the sub-half moduli inside BV's index set;
* **small scales** — `Gap212.Routing.exists_crude_bound` and `absorb_compact_range` cover
  `(1, X₀]`, where the range comparison can fail.

The constants add: `c = c_BV + c_crude`. Each half is `O_A(x/(log x)^A)` separately, so nothing is
lost by splitting at `X₀`.

The crude bound needs `IsCoefficientSequenceFamily f`, which for a convolution is
`Gap212.Routing.isCoefficientSequence_dconv`.

## Main results

* `Gap212.Routing.typeII_subHalfCoverage`: the obligation, from bilinear BV alone.
-/

@[expose] public section

namespace Gap212.Routing

open Finset Real Filter

open Classical in
/-- **Type II's sub-half obligation, from bilinear Bombieri–Vinogradov alone.** For a Type II
member of the Harman class and any retreat `κ > 0`, the generated moduli below `x^{1/2-κ}`
contribute `O_A(x/(log x)^A)`.

No Heath–Brown decomposition is used: the member is already in BV's shape. -/
theorem typeII_subHalfCoverage {ξ₂ κ : ℝ} {f : ℕ → ℝ → ℂ} {p : SupportParams}
    (hbv : Inputs.BilinearBombieriVinogradovFamily)
    (hξ : 0 < ξ₂ - Harman.slack) (hκ : 0 < κ)
    (hf : Harman.TypeIIFamily ξ₂ f) :
    SubHalfCoverage p f (fun x ↦ x ^ (1 / 2 - κ)) := by
  obtain ⟨α, β, M, N, η, hη, hfeq, hα, hαM, hβ, hβN, hβSW, hprod, hscale⟩ :=
    typeII_scale_eventually hξ hf
  subst hfeq
  have hcoef : IsCoefficientSequenceFamily (dconvFamily α β) := isCoefficientSequence_dconv hα hβ
  intro ε₀ hε₀ A hA
  -- Bilinear Bombieri–Vinogradov, at saving `A`.
  obtain ⟨B, hB, cBV, hcBV, hBV⟩ :=
    Inputs.subhalfSum_le_of_bv hbv hη hα hαM hβ hβN (Or.inr hβSW) hprod hscale hA
  -- The threshold past which the sub-half moduli sit inside BV's index set.
  obtain ⟨X₀, hX₀1, hX₀⟩ := exists_threshold_ranges_compare B hκ
  -- The crude bound below it.
  obtain ⟨Mc, hMc, hcrude⟩ := exists_crude_bound hcoef hX₀1
  obtain ⟨cC, hcC, habs⟩ := absorb_compact_range hMc hA hX₀1
  refine ⟨cBV + cC, by linarith, fun x hx a ha ↦ ?_⟩
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hL : 0 ≤ (log x) ^ A := Real.rpow_nonneg (Real.log_nonneg hx.le) A
  set S : Finset ℕ :=
    {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ Squarefree q}.filter
      (fun n : ℕ ↦ (n : ℝ) < x ^ (1 / 2 - κ)) with hSdef
  rcases le_or_gt X₀ x with hbig | hbig
  · -- Above the threshold: the citation applies.
    have hsub : S ⊆ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / (log x) ^ B⌋₊ := by
      intro q hq
      simp only [hSdef, Finset.mem_filter, Finset.mem_Icc] at hq ⊢
      exact ⟨hq.1.1.1, Nat.le_floor (hq.2.le.trans (hX₀ x hbig))⟩
    refine (hBV x hx a ha S hsub).trans ?_
    gcongr
    linarith
  · -- Below it: the crude bound, absorbed.
    refine ((hcrude x hx hbig.le a S ((Finset.filter_subset _ _).trans
      (Finset.filter_subset _ _))).trans (habs x hx hbig.le)).trans ?_
    gcongr
    linarith

end Gap212.Routing
