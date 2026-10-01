/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Harman
public import Gap212.Routing.Localize

/-!
# Patching the scale function off a set of scales

`Gap212.Routing.Localize` zeroes a sequence outside a set `S` of scales. The localized copy also
needs its scale function patched off `S` so the exponent condition still holds there, which is
harmless because the sequence is `0` there.

This module supplies that patch. It is the only construction in the routing the source does not
mention at all, and it is needed because `Gap212.HasEquidistributionFamily`'s exponent condition
`∀ x > 1, ∃ g ∈ G, N x = x^g` constrains `N`, not the sequence — so zeroing the sequence off `S`
does *not* by itself let `G` be restricted.

## What has to survive the patch

Setting `patchScale S N g₀ x = N x` on `S` and `x^{g₀}` off it, every hypothesis the estimates take
about a scale survives:

* `LocatedAtScaleFamily` — off `S` the localized sequence vanishes, so the condition is vacuous;
* `HasSiegelWalfiszFamily` — off `S` both sums are `0`, so the discrepancy is `0`
  and any nonnegative
  bound holds;
* `AsympEq (M N) id` — this is the one that constrains the patch: off `S` the product is
  `x^{g₁} x^{g₀}`, so **`g₀ + g₁ = 1`** is forced. The constants also have to be widened to
  `min c 1` and `max C 1`, since off `S` the product is exactly `x`;
* the exponent condition — holds off `S` by construction, provided `g₀ ∈ G`.

So a patched pair is a legitimate input to any of the five estimates, with `G` free to be as small
as the route needs.

## Main results

* `Gap212.Routing.patchScale`, with `patchScale_of_mem` / `patchScale_of_notMem`.
* `Gap212.Routing.locatedAtScale_patch`, `hasSiegelWalfisz_patch`, `asympEq_patch`,
  `exponent_patch`.
-/

@[expose] public section

namespace Gap212.Routing

open Finset Real

open Classical in
/-- `patchScale S N g₀` agrees with `N` at scales in `S` and is `x^{g₀}` elsewhere. -/
noncomputable def patchScale (S : Set ℝ) (N : ℝ → ℝ) (g₀ : ℝ) : ℝ → ℝ :=
  fun x ↦ if x ∈ S then N x else x ^ g₀

/-- At a scale `x ∈ S`, `patchScale S N g₀ x = N x`. -/
theorem patchScale_of_mem {S : Set ℝ} {N : ℝ → ℝ} {g₀ x : ℝ} (hx : x ∈ S) :
    patchScale S N g₀ x = N x := by
  classical
  rw [patchScale]; simp [hx]

/-- At a scale `x ∉ S`, `patchScale S N g₀ x = x ^ g₀`. -/
theorem patchScale_of_notMem {S : Set ℝ} {N : ℝ → ℝ} {g₀ x : ℝ} (hx : x ∉ S) :
    patchScale S N g₀ x = x ^ g₀ := by
  classical
  rw [patchScale]; simp [hx]

/-- **`LocatedAtScaleFamily` survives the patch.** Off `S` the localized sequence
vanishes, so there is
nothing to locate. -/
theorem locatedAtScale_patch {S : Set ℝ} {α : ℕ → ℝ → ℂ} {N : ℝ → ℝ} {g₀ : ℝ}
    (h : LocatedAtScaleFamily α N) : LocatedAtScaleFamily (restrict S α) (patchScale S N g₀) := by
  obtain ⟨c, C, hc, hcC, hbd⟩ := h
  refine ⟨c, C, hc, hcC, fun x hx n hne ↦ ?_⟩
  by_cases hm : x ∈ S
  · rw [restrict_of_mem hm] at hne
    rw [patchScale_of_mem hm]
    exact hbd x hx n hne
  · rw [restrict_of_notMem hm] at hne
    exact absurd rfl hne

/-- **`HasSiegelWalfiszFamily` survives the patch.** Off `S` both sums are `0`, so
the discrepancy is `0`
and any nonnegative bound holds — which is why the patch's value `x^{g₀}` must be nonnegative, as
it is. -/
theorem hasSiegelWalfisz_patch {S : Set ℝ} {β : ℕ → ℝ → ℂ} {N : ℝ → ℝ} {g₀ : ℝ}
    (h : HasSiegelWalfiszFamily β N) :
    HasSiegelWalfiszFamily (restrict S β) (patchScale S N g₀) := by
  classical
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun A hA ↦ ?_⟩
  obtain ⟨c, hc, hbd⟩ := hk A hA
  refine ⟨c, hc, fun x hx q r hq hr a hcop ↦ ?_⟩
  by_cases hm : x ∈ S
  · simp only [restrict_of_mem hm, patchScale_of_mem hm]
    exact hbd x hx q r hq hr a hcop
  · have hzero : ∀ n : ℕ, restrict S β n x = 0 := fun n ↦ restrict_of_notMem hm
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hlog : (0 : ℝ) < (log x) ^ A := Real.rpow_pos_of_pos (Real.log_pos hx) A
    simp only [hzero, patchScale_of_notMem hm]
    rw [finsum_mem_zero, finsum_mem_zero]
    simp only [mul_zero, sub_zero, norm_zero]
    have hxg : (0 : ℝ) ≤ x ^ g₀ := Real.rpow_nonneg hx0.le g₀
    positivity

/-- **`AsympEq (M N) id` survives the patch, and forces `g₀ + g₁ = 1`.** Off `S` the product is
`x^{g₁} x^{g₀} = x^{g₀+g₁}`, which has to be `x`. The constants widen to `min c 1` and `max C 1`,
since off `S` the product is exactly `x`. -/
theorem asympEq_patch {S : Set ℝ} {M N : ℝ → ℝ} {g₀ g₁ : ℝ}
    (h : AsympEq (fun x ↦ M x * N x) id) (hsum : g₁ + g₀ = 1) :
    AsympEq (fun x ↦ patchScale S M g₁ x * patchScale S N g₀ x) id := by
  classical
  obtain ⟨c, C, hc, hcC, hbd⟩ := h
  refine ⟨min c 1, max C 1, lt_min hc one_pos, le_trans (min_le_left _ _)
    (le_trans hcC (le_max_left _ _)), fun x hx ↦ ?_⟩
  dsimp only [id_eq]
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  by_cases hm : x ∈ S
  · rw [patchScale_of_mem hm, patchScale_of_mem hm]
    obtain ⟨hlo, hhi⟩ := hbd x hx
    refine ⟨le_trans ?_ hlo, le_trans hhi ?_⟩
    · exact mul_le_mul_of_nonneg_right (min_le_left _ _) (le_of_lt hx0)
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hx0)
  · rw [patchScale_of_notMem hm, patchScale_of_notMem hm]
    have hprod : x ^ g₁ * x ^ g₀ = x := by
      rw [← Real.rpow_add hx0, hsum, Real.rpow_one]
    rw [hprod]
    refine ⟨?_, ?_⟩
    · simpa using mul_le_mul_of_nonneg_right (min_le_right c 1) (le_of_lt hx0)
    · simpa using mul_le_mul_of_nonneg_right (le_max_right C 1) (le_of_lt hx0)

/-- **The exponent condition survives the patch**, provided the off-`S` exponent is in `G`. This is
the point of the patch: `G` may now be as small as the route needs, since off `S` the scale is
`x^{g₀}` by fiat. -/
theorem exponent_patch {S : Set ℝ} {N : ℝ → ℝ} {g₀ : ℝ} {G : Set ℝ} (hg₀ : g₀ ∈ G)
    (h : ∀ x : ℝ, 1 < x → x ∈ S → ∃ g ∈ G, N x = x ^ g) :
    ∀ x : ℝ, 1 < x → ∃ g ∈ G, patchScale S N g₀ x = x ^ g := by
  classical
  intro x hx
  by_cases hm : x ∈ S
  · obtain ⟨g, hgG, hNx⟩ := h x hx hm
    exact ⟨g, hgG, by rw [patchScale_of_mem hm]; exact hNx⟩
  · exact ⟨g₀, hg₀, patchScale_of_notMem hm⟩

end Gap212.Routing
