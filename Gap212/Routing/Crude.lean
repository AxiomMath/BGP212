/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.Union
public meta import Gap212.Attr

/-!
# The compact range, absorbed into the constant

`Gap212.HasEquidistributionOverQstarFamily` is `∀ x > 1` with `∃ c` chosen first,
while every analytic
input it is assembled from is only usable once `x` is large: bilinear Bombieri–Vinogradov puts its
moduli in `[1, x^{1/2}(log x)^{-B}]`, and the small part of a generated family sits there only when
`(log x)^B ≤ x^{ε₁}` — true near `x = 1` and for large `x`, false in between.

So the assembly needs the range `x ∈ (1, X₀]` handled separately and folded into `c`. This module
does that, and the point worth recording is that **no compactness argument is needed**: on
`(1, X₀]` every quantity involved is monotone, so an explicit constant does it.

## The crude bound

For a coefficient sequence `‖f(n;x)‖ ≤ C τ(n)^k (log x)^l`, and on the dyadic block
`τ(n) ≤ n ≤ 2x`. The discrepancy at one modulus is at most twice the block's total mass — both its
terms are, the second because `1/φ(q) ≤ 1` for `q ≥ 1`. Summing over at most `⌊x⌋` moduli:

    ∑_q discrepancy ≤ 2 ⌊x⌋ (⌊2x⌋ + 1) C (⌊2x⌋)^k (log x)^l,

every factor of which is increasing in `x`. Evaluating at `X₀` gives a constant.

## The absorption

`c x / (log x)^A ≥ M` on `(1, X₀]` needs `c ≥ M (log x)^A / x`, and there `(log x)^A ≤ (log X₀)^A`
while `x > 1`. So `c = M (log X₀)^A + M` works — again only monotonicity of `log` and of `t ↦ t^A`.

This is analysis of the cheapest kind: the bound may be catastrophically lossy, being used only on
a bounded range.

## Main results

* `Gap212.Routing.discrepancy_le_block_mass`: one modulus, twice the block mass.
* `Gap212.Routing.exists_crude_bound`: the sum is bounded on `(1, X₀]`.
* `Gap212.Routing.absorb_compact_range`: a bounded sum is `≤ c x (log x)^{-A}` there.
-/

@[expose] public section

namespace Gap212.Routing

open Finset Real

/-! ## One modulus -/

open Classical in
/-- **The discrepancy at one modulus is at most twice the dyadic block's mass.** Both terms of the
difference are bounded by the mass: the first because it sums a subset, the second because
`1/φ(q) ≤ 1` once `q ≥ 1`. -/
theorem discrepancy_le_block_mass {f : ℕ → ℝ → ℂ} {x : ℝ} {a q : ℕ} (hq : 1 ≤ q) :
    discrepancy f x a q ≤ 2 * ∑ n ∈ dyadic x, ‖f n x‖ := by
  classical
  have hmass : ∀ s ⊆ dyadic x, ‖∑ n ∈ s, f n x‖ ≤ ∑ n ∈ dyadic x, ‖f n x‖ := fun s hs ↦
    (norm_sum_le _ _).trans (sum_le_sum_of_subset_of_nonneg hs fun _ _ _ ↦ norm_nonneg _)
  have hcoef : ‖(1 / (Nat.totient q : ℂ))‖ ≤ 1 := by
    rw [norm_div, norm_one, Complex.norm_natCast]
    exact div_le_one_of_le₀ (by exact_mod_cast Nat.totient_pos.mpr hq) (Nat.cast_nonneg _)
  have h2 := mul_le_mul hcoef (hmass _ (filter_subset (Nat.Coprime · q) _)) (norm_nonneg _)
    zero_le_one
  rw [one_mul, ← norm_mul] at h2
  unfold discrepancy
  linarith [norm_sub_le (∑ n ∈ dyadic x with n ≡ a [MOD q], f n x)
    ((1 / (Nat.totient q : ℂ)) * ∑ n ∈ dyadic x with Nat.Coprime n q, f n x),
    hmass _ (filter_subset (· ≡ a [MOD q]) (dyadic x))]

/-! ## The block's mass, crudely -/

/-- Every member of the dyadic block is at most `⌊2x⌋`. -/
theorem le_of_mem_dyadic {x : ℝ} {n : ℕ} (hn : n ∈ dyadic x) : n ≤ ⌊2 * x⌋₊ :=
  (mem_Icc.mp hn).2

/-- The block has at most `⌊2x⌋ + 1` members. -/
theorem card_dyadic_le {x : ℝ} : (dyadic x).card ≤ ⌊2 * x⌋₊ + 1 := by
  rw [dyadic, Nat.card_Icc]
  omega

/-! ## The crude bound, and its absorption -/

open Classical in
/-- **The discrepancy sum is bounded on `(1, X₀]`.** Catastrophically lossy — every `τ(n)` is
replaced by `2x` — which is fine, because the bound is only used on a bounded range. -/
theorem exists_crude_bound {f : ℕ → ℝ → ℂ} (hf : IsCoefficientSequenceFamily f) {X₀ : ℝ}
    (hX₀ : 1 < X₀) :
    ∃ M > (0 : ℝ), ∀ x : ℝ, 1 < x → x ≤ X₀ → ∀ a : ℕ, ∀ D : Finset ℕ,
      D ⊆ Finset.Icc 1 ⌊x⌋₊ → ∑ q ∈ D, discrepancy f x a q ≤ M := by
  classical
  obtain ⟨C, k, l, hC, hbd⟩ := hf
  have hL : 0 < log X₀ := Real.log_pos hX₀
  set B : ℝ := C * (⌊2 * X₀⌋₊ : ℝ) ^ k * (log X₀) ^ l with hBdef
  have hB : 0 ≤ B := by positivity
  set N₂ : ℝ := (⌊2 * X₀⌋₊ : ℝ) + 1 with hN₂
  set N₁ : ℝ := (⌊X₀⌋₊ : ℝ) + 1 with hN₁
  have hN₂B : 0 ≤ N₂ * B := by positivity
  refine ⟨2 * N₁ * (N₂ * B) + 1, by positivity, fun x hx hxX a D hD ↦ ?_⟩
  have hlog0 : 0 < log x := Real.log_pos hx
  -- Each entry of the block is bounded by `B`.
  have hentry : ∀ n ∈ dyadic x, ‖f n x‖ ≤ B := fun n hn ↦ (hbd n x hx).trans <| by
    have hτ : (n.divisors.card : ℝ) ≤ ⌊2 * X₀⌋₊ := by
      exact_mod_cast (Nat.card_divisors_le_self n).trans
        ((le_of_mem_dyadic hn).trans (Nat.floor_le_floor (by linarith)))
    rw [hBdef]
    gcongr
  -- The block's mass is at most `N₂ * B`, and there are at most `N₁` moduli.
  have hcard : ((dyadic x).card : ℝ) ≤ N₂ := by
    have := Nat.floor_le_floor (show 2 * x ≤ 2 * X₀ by linarith)
    rw [hN₂]
    exact_mod_cast card_dyadic_le.trans (by omega)
  have hDcard : (D.card : ℝ) ≤ N₁ := by
    have := Nat.floor_le_floor hxX
    have := card_le_card hD
    rw [Nat.card_Icc] at this
    rw [hN₁]
    exact_mod_cast (by omega : D.card ≤ ⌊X₀⌋₊ + 1)
  have hmass := sum_le_card_nsmul _ _ _ hentry
  have hterm : ∀ q ∈ D, discrepancy f x a q ≤ 2 * (N₂ * B) := fun q hq ↦
    (discrepancy_le_block_mass (mem_Icc.mp (hD hq)).1).trans <| by
      rw [nsmul_eq_mul] at hmass; nlinarith [mul_le_mul_of_nonneg_right hcard hB]
  have hsum := sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hsum
  nlinarith [mul_le_mul_of_nonneg_right hDcard hN₂B]

/-- **A bounded sum is `≤ c x (log x)^{-A}` on `(1, X₀]`.** Only monotonicity of `log` and of
`t ↦ t^A` is used — the compact range needs no compactness. -/
theorem absorb_compact_range {M A X₀ : ℝ} (hM : 0 < M) (hA : 0 < A) (hX₀ : 1 < X₀) :
    ∃ c > (0 : ℝ), ∀ x : ℝ, 1 < x → x ≤ X₀ → M ≤ c * x / (log x) ^ A := by
  have hL : 0 < log X₀ := Real.log_pos hX₀
  refine ⟨M * (log X₀) ^ A + M, by positivity, fun x hx hxX ↦ ?_⟩
  have hlog0 : 0 < log x := Real.log_pos hx
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hlog0 A)]
  calc M * (log x) ^ A ≤ M * (log X₀) ^ A := by gcongr
    _ ≤ (M * (log X₀) ^ A + M) * x :=
        (le_add_of_nonneg_right hM.le).trans (le_mul_of_one_le_right (by positivity) hx.le)

end Gap212.Routing
