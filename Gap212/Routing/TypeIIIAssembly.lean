/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Harman
public import Gap212.Routing.Localize
public import Gap212.Routing.Routes

/-!
# The Type III route, composed end to end

A route taken all the way from a member of the Harman class to a bound on a generated-modulus
discrepancy sum. It is the easiest of the six, for the following reason.

## Type III needs no localization

`Gap212.Routing.Localize` shows a route cannot in general be applied to a Harman-class member
directly, because `Gap212.HasEquidistributionFamily`'s exponent set `G` must cover every scale while
the routes need `γ`-restricted applications. Type III escapes this: its size conditions are stated
against the *fixed* `ξ₃`, so `G` can be the **singleton** `{ξ₃ + ϵ}` and every hypothesis holds on
it at once.

The value `ξ₃ + ϵ` rather than `ξ₃` is forced, and this is the subtle point. The Type III class
`Gap212.Harman.TypeIIIFamily` gives `x^{1-ξ₃-ϵ} ≤ N₁N₂`, which is *not* `DomGE (N₁N₂) (x^{1-ξ₃})` —
that would need `c x^{1-ξ₃} ≤ x^{1-ξ₃-ϵ}`, i.e. `c ≤ x^{-ϵ}`, and no fixed `c` survives `x → ∞`. At
`g = ξ₃ + ϵ` the target is `x^{1-ξ₃-ϵ}` exactly and all four size conditions hold with constant `1`.

That also fixes the wall's margin: `28ω + 9g + 8δ*` at `g = ξ₃ + ϵ` is `4 + 9ϵ - 16ϵ = 4 - 7ϵ`,
using the width `Gap212.Routing.widthIII`, which carries `-2ϵ`. With the width displayed in [2],
which carries `-ϵ`, it would be `4 + ϵ` (`Gap212.Routing.typeIII_wall_fails_as_printed`).

## What composing gives, and what it does not

`Gap212.Routing.typeIII_estimate_applies` produces the estimate's conclusion for `f`. Combined
with `Gap212.Routing.mem_moduliIII_route` and monotonicity it bounds the **positive-level** part of
a `Qgen` sum — the moduli above the retreated half-level, which is all the containments reach.

The sub-half part is covered by no route: it is bilinear Bombieri–Vinogradov's, and reaching it
needs a two-factor presentation of `f` with Siegel–Walfisz on one side. In the single-scale form
that is `Gap212.exists_hasEquidistribution_subhalf_of_harmanClass`.

## Main results

* `Gap212.Routing.typeIII_estimate_applies`: the Type III estimate applies to every Type III member
  of the Harman class, at Point A's level and the width `widthIII`.
* `Gap212.Routing.typeI_estimate_applies`: the same for Type I, both `γ`-branches at one width.
* `Gap212.Routing.slack_eq_ϵ`: `Harman.slack` and `PointA.ϵ` are the same real.
-/

@[expose] public section

namespace Gap212.Routing

open Finset Real Gap212.PointA Gap212.Packing

/-! ## The estimate applies -/

/-- **The Type III estimate applies to every Type III member of the Harman class**, with exponent
set the singleton `{ξ₃ + ϵ}`, level `ω`, and the width `widthIII`.

The singleton is why Type III needs no localization; `ξ₃ + ϵ` rather than `ξ₃` is what makes
the four size conditions hold with constant `1`. -/
theorem typeIII_estimate_applies (h₅ : TypeIIIPolymathFamily) {f : ℕ → ℝ → ℂ}
    (hf : Harman.TypeIIIFamily (((ξ₃ : ℚ) : ℝ)) f) :
    HasEquidistributionFamily f moduliIIIFamily
      (triples (((ω : ℚ) : ℝ)) widthIII {((ξ₃ : ℚ) : ℝ) + Harman.slack}) := by
  obtain ⟨α, ψ₁, ψ₂, ψ₃, M, N₁, N₂, N₃, hfeq, hα, hαM, hs₁, hs₂, hs₃, hprod, hsize⟩ := hf
  have hslack : (0 : ℝ) < Harman.slack := by
    rw [Harman.slack]; norm_num
  -- Every size condition holds at `g = ξ₃ + ϵ`, with constant `1`.
  have hsizeG : ∀ g ∈ ({((ξ₃ : ℚ) : ℝ) + Harman.slack} : Set ℝ),
      DomGE (fun x ↦ N₁ x * N₂ x) (fun x ↦ x ^ (1 - g)) ∧
      DomGE (fun x ↦ N₁ x * N₃ x) (fun x ↦ x ^ (1 - g)) ∧
      DomGE (fun x ↦ N₂ x * N₃ x) (fun x ↦ x ^ (1 - g)) ∧
      DomGE N₁ (fun x ↦ x ^ (1 - 2 * g)) ∧ DomLE N₁ (fun x ↦ x ^ g) ∧
      DomGE N₂ (fun x ↦ x ^ (1 - 2 * g)) ∧ DomLE N₂ (fun x ↦ x ^ g) ∧
      DomGE N₃ (fun x ↦ x ^ (1 - 2 * g)) ∧ DomLE N₃ (fun x ↦ x ^ g) := by
    rintro _ rfl
    refine ⟨⟨1, one_pos, fun x hx ↦ ?_⟩, ⟨1, one_pos, fun x hx ↦ ?_⟩, ⟨1, one_pos, fun x hx ↦ ?_⟩,
      ⟨1, one_pos, fun x hx ↦ ?_⟩, ⟨1, one_pos, fun x hx ↦ ?_⟩,
      ⟨1, one_pos, fun x hx ↦ ?_⟩, ⟨1, one_pos, fun x hx ↦ ?_⟩,
      ⟨1, one_pos, fun x hx ↦ ?_⟩, ⟨1, one_pos, fun x hx ↦ ?_⟩⟩ <;> rw [one_mul]
    · simpa [sub_add_eq_sub_sub] using (hsize x hx).2.2.2.1
    · simpa [sub_add_eq_sub_sub] using (hsize x hx).2.2.2.2.1
    · simpa [sub_add_eq_sub_sub] using (hsize x hx).2.2.2.2.2
    -- `x^{1-2ξ₃-2ϵ} ≤ x^{1-2ξ₃-ϵ}` for `x > 1`: the smaller exponent is the weaker demand.
    · exact (rpow_le_rpow_of_exponent_le hx.le (by linarith)).trans (hsize x hx).1.1
    · exact (hsize x hx).1.2
    · exact (rpow_le_rpow_of_exponent_le hx.le (by linarith)).trans (hsize x hx).2.1.1
    · exact (hsize x hx).2.1.2
    · exact (rpow_le_rpow_of_exponent_le hx.le (by linarith)).trans (hsize x hx).2.2.1.1
    · exact (hsize x hx).2.2.1.2
  -- The wall, at the width `widthIII`: `4 - 7ϵ < 4`.
  have hwall : ∃ ε₁ > (0 : ℝ), ∀ g ∈ ({((ξ₃ : ℚ) : ℝ) + Harman.slack} : Set ℝ),
      28 * (((ω : ℚ) : ℝ)) + 9 * g + 8 * widthIII + ε₁ < 4 := by
    refine ⟨Harman.slack, hslack, ?_⟩
    rintro _ rfl
    unfold widthIII deltaStarIII'
    rw [cast_ω, cast_ξ₃, cast_ϵ, Harman.slack]
    norm_num
  rw [hfeq]
  exact h₅ α ψ₁ ψ₂ ψ₃ M N₁ N₂ N₃ _ _ _ hα hαM (Gap212.Corrected.isSmoothAtScale_le hs₁)
    (Gap212.Corrected.isSmoothAtScale_le hs₂) (Gap212.Corrected.isSmoothAtScale_le hs₃)
    hprod hsizeG hwall

/-! ## Type I, and it needs no localization either

Type I's two `γ`-branches are cut at `γ = 1/2` inside `Gap212.moduliIFamily`, and the wall of [2,
Lemma 5] differs across them — `3γ - 12ω - 3δ > 1` below, `68ω + 14δ < 1` above. So one might expect
the same obstruction as Type II, needing two widths. It does not arise, for an asymmetric reason:

* below `1/2` the wall *improves* with `γ`, so the width at the bottom of the range works
  throughout, and `Gap212.Packing.typeI_analytic₁` makes it exactly saturating there;
* above `1/2` the wall does not involve `γ` at all, and at that same width it reads
  `0.85197 < 1` — margin `0.148`, the most comfortable inequality anywhere in the routing.

So `G` can be all of `Ici (ξ₁ - ϵ)` at the single width `widthI₁`, the exponent condition holding
because `Harman.TypeIFamily` bounds `γ` from below and not above. -/

/-- `Harman.slack` and `Gap212.PointA.ϵ` are the same real number, `10⁻¹⁰`, reached by two
different definitions. -/
theorem slack_eq_ϵ : Harman.slack = ((ϵ : ℚ) : ℝ) := by
  rw [Harman.slack, cast_ϵ]

/-- **The Type I estimate applies to every Type I member of the Harman class**, with exponent set
`Ici (ξ₁ - ϵ)`, level `ω`, and the single width `widthI₁` — both `γ`-branches at once. -/
theorem typeI_estimate_applies (h₃ : TypeIBakerIrvingFamily) {f : ℕ → ℝ → ℂ}
    (hf : Harman.TypeIFamily (((ξ₁ : ℚ) : ℝ)) f) :
    HasEquidistributionFamily f moduliIFamily
      (triples (((ω : ℚ) : ℝ)) widthI₁ (Set.Ici gammaLoI)) := by
  obtain ⟨α, β, M, N, hfeq, hα, hαM, hβ, hsβ, hprod, hexp⟩ := hf
  -- The exponent condition: `Harman.TypeIFamily` bounds `γ` below, which is all `Ici` needs.
  have hG : ∀ x : ℝ, 1 < x → ∃ g ∈ Set.Ici gammaLoI, N x = x ^ g := fun x hx ↦ by
    obtain ⟨g, hg, hNx⟩ := hexp x hx
    exact ⟨g, by rwa [Set.mem_Ici, gammaLoI, ← slack_eq_ϵ], hNx⟩
  -- Both walls, at the single width.
  have hwall : ∃ ε₁ > (0 : ℝ), ∀ g ∈ Set.Ici gammaLoI,
      (g ≤ 1 / 2 → 1 + ε₁ < 3 * g - 12 * (((ω : ℚ) : ℝ)) - 3 * widthI₁) ∧
      (1 / 2 < g → 68 * (((ω : ℚ) : ℝ)) + 14 * widthI₁ + ε₁ < 1) := by
    refine ⟨2 / 10 ^ 10, by norm_num, fun g hg ↦ ?_⟩
    rw [Set.mem_Ici, gammaLoI, cast_ξ₁, cast_ϵ] at hg
    unfold widthI₁ gammaLoI deltaStarI₁
    rw [cast_ξ₁, cast_ω, cast_ϵ]
    -- below `1/2`: the identity at the bottom, then monotonicity in `g`; above: no `γ` at all
    exact ⟨fun _ ↦ by norm_num; linarith, fun _ ↦ by norm_num⟩
  rw [hfeq]
  exact h₃ α β M N _ _ _ hα hαM hβ (Gap212.Corrected.isSmoothAtScale_le hsβ) hprod hG hwall

end Gap212.Routing
