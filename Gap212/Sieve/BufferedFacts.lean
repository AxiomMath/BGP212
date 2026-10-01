/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.EndgameDefs
public import Gap212.Support.Hereditary
public meta import Gap212.Attr

/-!
# A neighbourhood of the buffered region lies in the retreat region

The buffered region `R⁺⁺_k(j, ε₀, ζ₁, κ)` carries two buffers, and this file proves the one
statement they exist for: every point within `η` of the buffered region still lies in the retreat
region `R⁺_k(j, ε₀)`, provided `η ≤ ζ₁` and `κ ≥ k(ζ₁ + η)`.

## Why two buffers

`κ` is slack in the two *inequalities* — the total mass and the rough cap — and a perturbation of
size `η` moves each by at most `kη`, so `κ ≥ kη` alone would look sufficient. It is not. The rough
set is defined by a *threshold*, and a coordinate sitting just below `δ` can be pushed above it by
the perturbation, joining the rough set of `v` and bringing its mass into a cap that the buffered
region's own cap clause never looked at. `ζ₁` is the slack at the threshold: the buffered region's
cap is asked at the *lower* threshold `δ - ζ₁`, so the rough set of `v` is contained in the set the
cap clause already controls.

Paying for `ζ₁` is what costs the extra `kζ₁` in `κ ≥ k(ζ₁ + η)`: passing from the cap at
`#I = #{i : δ - ζ₁ ≤ tᵢ}` down to the cap at `#Iᵥ = #{i : δ ≤ vᵢ}` drops `#I - #Iᵥ` coordinates,
each of which loses at least `δ - ζ₁` from the mass while the cap row, by
`Gap212.SupportParams.B_step_iterate`, loses at most `δ` from the bound — a shortfall of `ζ₁` per
dropped coordinate, hence at most `kζ₁` in all.

## Main results

* `Gap212.GPY.mem_retreatRegion_of_mem_bufferedRegion`: the neighbourhood statement.
-/

@[expose] public section

namespace Gap212.GPY

open Finset

variable {p : SupportParams}

/-- Membership in `Gap212.GPY.roughAt` is the threshold inequality. -/
theorem mem_roughAt_iff {k : ℕ} {θ : ℝ} {t : Fin k → ℝ} {i : Fin k} :
    i ∈ roughAt θ t ↔ θ ≤ t i := by
  classical
  simp [roughAt]

/-- **A neighbourhood of the buffered region lies in the retreat region.** If `t` lies in
`R⁺⁺_k(j, ε₀, ζ₁, κ)` and `v` is within `η` of `t` in every coordinate, with `η ≤ ζ₁` and
`κ ≥ k(ζ₁ + η)`, then `v` lies in `R⁺_k(j, ε₀)`.

This is the uniform buffer the tensor construction needs: a corner of a downward box that merely
lies *near* the support of the retreated function is still inside the retreat region, so the moduli
the corresponding sieve weight generates are still in `Q⋆`. Appealing to the measure-zero
threshold hyperplane would not do, since the corner is a single point. -/
@[gap212 "lem_buffered_neighbourhood"]
theorem mem_retreatRegion_of_mem_bufferedRegion {k : ℕ} {j : Fin p.n} {ε₀ ζ₁ κ η : ℝ}
    (hε₀ : 0 < ε₀) (hε₀' : ε₀ ≤ 1) (hζ₁ : 0 < ζ₁) (hκ : 0 < κ) (hηζ : η ≤ ζ₁)
    (hκk : (k : ℝ) * (ζ₁ + η) ≤ κ) {t v : Fin k → ℝ}
    (ht : t ∈ bufferedRegion p k j ε₀ ζ₁ κ) (hv : ∀ i, |v i - t i| ≤ η) :
    v ∈ retreatRegion p k j ε₀ := by
  classical
  obtain ⟨hcoord, htotal, hcap⟩ := ht
  -- The two-sided form of the perturbation bound.
  have hlo : ∀ i, t i - η ≤ v i := fun i ↦ by linarith [(abs_le.mp (hv i)).1]
  have hhi : ∀ i, v i ≤ t i + η := fun i ↦ by linarith [(abs_le.mp (hv i)).2]
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- No coordinates at all: both inequalities are about the empty sum.
    subst hk0
    refine ⟨fun i ↦ i.elim0, ?_, by simp [SupportParams.roughIdx, p.B_zero]⟩
    simp only [univ_eq_empty, sum_empty] at htotal ⊢
    linarith
  -- With a coordinate available, the perturbation bound forces `0 ≤ η`.
  have hη0 : 0 ≤ η := le_trans (abs_nonneg _) (hv ⟨0, hkpos⟩)
  have h1k : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
  have hηκ : ∀ r : ℕ, r ≤ k → (r : ℝ) * η ≤ κ - (k : ℝ) * ζ₁ := by
    intro r hr
    linarith [mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ).mpr hr) hη0]
  refine ⟨fun i ↦ ⟨?_, ?_⟩, ?_, ?_⟩
  · -- `0 ≤ vᵢ`: the coordinate starts at `ζ₁` and moves by at most `η ≤ ζ₁`.
    linarith [(hcoord i).1, hlo i]
  · -- `vᵢ ≤ 1`: the coordinate stops at `1 - κ` and `η ≤ κ - kζ₁ ≤ κ`.
    nlinarith [(hcoord i).2, hhi i, hζ₁.le]
  · -- The total mass: the perturbation costs at most `kη`, and `kη < κ`.
    have hsum : ∑ i, v i ≤ ∑ i, t i + (k : ℝ) * η :=
      (sum_le_sum fun i _ ↦ hhi i).trans_eq (by simp [sum_add_distrib, mul_comm])
    nlinarith [hηκ k le_rfl]
  · -- The cap, the only clause where the threshold buffer does work.
    set Iv := p.roughIdx k v with hIv
    set I := roughAt (p.δ - ζ₁) t with hI
    rcases Iv.eq_empty_or_nonempty with hIvE | hIvN
    · simp [hIvE, p.B_zero]
    -- Every rough coordinate of `v` sits above `δ - ζ₁` in `t`.
    have hsub : Iv ⊆ I := by
      intro i hi
      have hδ : p.δ ≤ v i := by
        simpa [hIv, SupportParams.roughIdx] using hi
      have := hhi i
      exact mem_roughAt_iff.mpr (by linarith)
    have hcapI := hcap (hIvN.mono hsub)
    set m := I.card with hm
    set r := Iv.card with hr
    have hr1 : 1 ≤ r := Finset.card_pos.mpr hIvN
    have hrk : r ≤ k := by simpa using Finset.card_le_univ Iv
    have hmk : m ≤ k := by simpa using Finset.card_le_univ I
    -- Cardinalities, phrased additively to avoid truncated subtraction.
    set d := (I \ Iv).card with hd
    have hcard : d + r = m := by
      have h1 := Finset.sum_sdiff (f := fun _ : Fin k ↦ (1 : ℕ)) hsub
      simpa [hd, hr, hm] using h1
    -- The dropped coordinates each carry at least `δ - ζ₁`.
    have hdrop : (d : ℝ) * (p.δ - ζ₁) ≤ ∑ i ∈ I \ Iv, t i := by
      simpa using card_nsmul_le_sum _ _ _ fun i hi ↦ mem_roughAt_iff.mp (mem_sdiff.mp hi).1
    have hsplit : ∑ i ∈ I \ Iv, t i + ∑ i ∈ Iv, t i = ∑ i ∈ I, t i := Finset.sum_sdiff hsub
    -- The cap row degrades by at most `d·δ` when the index drops from `m` to `r`.
    have hchain : p.B j m ≤ p.B j r + (d : ℝ) * p.δ := by
      have : p.B j (r + d) ≤ p.B j r + (d : ℝ) * p.δ := p.B_step_iterate j hr1 d
      rwa [show r + d = m by omega] at this
    -- And the perturbation costs at most `rη`, absorbed by the buffer.
    have hpert : ∑ i ∈ Iv, v i ≤ ∑ i ∈ Iv, t i + (r : ℝ) * η :=
      (sum_le_sum fun i _ ↦ hhi i).trans_eq (by simp [sum_add_distrib, hr, mul_comm])
    have hdk : (d : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : d ≤ k)
    have hηr := hηκ r hrk
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith [hcapI, hchain, hdrop, hsplit, hpert, mul_nonneg hd0 hε₀.le, p.δ_pos.le]

end Gap212.GPY
