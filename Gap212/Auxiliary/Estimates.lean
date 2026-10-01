/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Linarith
public meta import Gap212.Attr

/-!
# Self-contained auxiliary facts

A handful of small lemmas, each stated with its dependencies inlined, so nothing here depends on
the rest of the development.

## Main results

* `Gap212.Auxiliary.affine_perturbation`: an affine capacity moves by at most `L |θ - 1/2|`.
* `Gap212.Auxiliary.omega_max_le_top`: the level of a band pair is bounded by the top node.
* `Gap212.Auxiliary.total_piece_count`: four polylogarithmic counts multiply to a polylogarithmic
  one.
* `Gap212.Auxiliary.typeIII_parameter_match`: the Type III scale conditions transfer to
  `γ = ξ₃ + ϵ`.
* `Gap212.Auxiliary.typeII_range_cover`: the three Type II ranges are exhaustive.
-/

@[expose] public section

namespace Gap212.Auxiliary

open Real MeasureTheory

/-- **Affine perturbation.** An affine capacity with slope bounded by `L` moves by at most
`L |θ - 1/2|` away from the half-level. This is what converts a reserve into a transport radius. -/
theorem affine_perturbation (c₀ s θ L : ℝ) (hs : |s| ≤ L) :
    |(c₀ + s * (θ - 1 / 2)) - c₀| ≤ L * |θ - 1 / 2| := by
  rw [add_sub_cancel_left, abs_mul]
  exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)

/-- **The level of a band pair is bounded by the top node.** The average of two nodes each at most
`Atop` is at most `Atop`. -/
@[gap212 "lem_omega_max_le_An"]
theorem omega_max_le_top {n : ℕ} (A : Fin n → ℝ) (Atop : ℝ)
    (hA : ∀ i, A i ≤ Atop) (j j' : Fin n) :
    (A j + A j') / 2 - 1 / 4 ≤ Atop - 1 / 4 := by
  linarith [hA j, hA j']

/-- **The decomposition pieces are polylogarithmically many.** Four polylogarithmic counts multiply
to a polylogarithmic one, with the exponent the sum. -/
theorem total_piece_count {x C₁ C₂ C₃ C₄ c₁ c₂ c₃ c₄ n₁ n₂ n₃ n₄ : ℝ}
    (_hx : 1 < x) (hlog : 1 ≤ Real.log x)
    (hC : 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 0 < C₄)
    (h₁ : n₁ ≤ C₁ * Real.log x ^ c₁) (h₂ : n₂ ≤ C₂ * Real.log x ^ c₂)
    (h₃ : n₃ ≤ C₃ * Real.log x ^ c₃) (h₄ : n₄ ≤ C₄ * Real.log x ^ c₄)
    (hn : 0 ≤ n₁ ∧ 0 ≤ n₂ ∧ 0 ≤ n₃ ∧ 0 ≤ n₄) :
    n₁ * n₂ * n₃ * n₄ ≤ (C₁ * C₂ * C₃ * C₄) * Real.log x ^ (c₁ + c₂ + c₃ + c₄) := by
  obtain ⟨hC₁, hC₂, hC₃, hC₄⟩ := hC
  obtain ⟨hn₁, hn₂, hn₃, hn₄⟩ := hn
  have hL0 : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlog
  -- RHS = (C₁C₂C₃C₄) * L^(c₁+c₂+c₃+c₄) = ∏ (Cᵢ * L^cᵢ) by rpow_add + ring
  have hrhs : (C₁ * C₂ * C₃ * C₄) * Real.log x ^ (c₁ + c₂ + c₃ + c₄)
      = (C₁ * Real.log x ^ c₁) * (C₂ * Real.log x ^ c₂) * (C₃ * Real.log x ^ c₃)
          * (C₄ * Real.log x ^ c₄) := by
    rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0]
    ring
  rw [hrhs]
  gcongr

/-- **The Type III parameter match.** The class's scale conditions at `ξ₃` transfer to the
estimate's conditions at `γ = ξ₃ + ϵ`; the content is that `1 - 2ξ₃ - ϵ ≥ 1 - 2γ`. -/
@[gap212 "lem_typeIII_parameter_match"]
theorem typeIII_parameter_match {ξ₃ ϵ N₁ _N₂ _N₃ x : ℝ} (hϵ : 0 < ϵ) (hx : 1 < x)
    (h₁ : x ^ (1 - 2 * ξ₃ - ϵ) ≤ N₁) (h₂ : N₁ ≤ x ^ (ξ₃ + ϵ)) :
    x ^ (1 - 2 * (ξ₃ + ϵ)) ≤ N₁ ∧ N₁ ≤ x ^ ((ξ₃ + ϵ)) := by
  refine ⟨le_trans ?_ h₁, h₂⟩
  apply Real.rpow_le_rpow_of_exponent_le hx.le
  linarith

/-- **The three Type II ranges are exhaustive.** Trichotomy on `γ` against the two thresholds.
The content of the Type II decomposition is that each range carries an estimate, not that they
cover. -/
@[gap212 "lem_typeII_range_cover"]
theorem typeII_range_cover (ϵ ω δ γ : ℝ) :
    γ ≤ 1/3 + 8 * ω + 7 * δ / 3 + 3 * ϵ ∨
      (1/3 + 8 * ω + 7 * δ / 3 + 3 * ϵ < γ ∧ γ < 2/5 + 24 * ω / 5 + 7 * δ / 5 + 2 * ϵ) ∨
      2/5 + 24 * ω / 5 + 7 * δ / 5 + 2 * ϵ ≤ γ := by
  grind

/-- **Positive energy forces a nonzero function.** If `F` vanished on all of `T` its energy would
be zero, contradicting positivity. Uses `setIntegral_eq_zero_of_forall_eq_zero`, which needs no
measurability of `T`. -/
theorem certificate_nonzero {k : ℕ} {T : Set (Fin k → ℝ)} {F : (Fin k → ℝ) → ℝ}
    (hI : 0 < ∫ t in T, F t ^ 2) : ¬ (∀ t ∈ T, F t = 0) :=
  fun h ↦ hI.ne' (setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ by simp [h t ht])

/-- **The deficiency is small on the transition range.** For a modulus strictly between
`x^{1/2}(log x)^{-C}` and `x^{1/2}`, the deficiency `κ = 1/2 - log_x q` is positive and below
`C log log x / log x`. Taking logarithms of both bounds; the hypothesis `x > e` is what makes
`log x > 1` and the divisions safe. -/
theorem kappa_range_on_tr {x q C : ℝ} (hx : exp 1 < x) (hq : 0 < q)
    (hlo : x ^ ((1 : ℝ) / 2) / (log x) ^ C < q) (hhi : q < x ^ ((1 : ℝ) / 2)) :
    0 < 1 / 2 - log q / log x ∧ 1 / 2 - log q / log x < C * log (log x) / log x := by
  have hx0 : (0:ℝ) < x := (Real.exp_pos 1).trans hx
  have hL0 : 0 < log x := one_pos.trans ((Real.lt_log_iff_exp_lt hx0).2 hx)
  have h₁ := Real.log_lt_log hq hhi
  have h₂ := Real.log_lt_log (by positivity) hlo
  rw [Real.log_rpow hx0] at h₁
  rw [Real.log_div (by positivity) (by positivity), Real.log_rpow hx0, Real.log_rpow hL0] at h₂
  refine ⟨?_, ?_⟩
  · rw [sub_pos, div_lt_iff₀ hL0]; linarith
  · rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hL0]; linarith

/-- **At most one factor precedes the last transferred one.** An index set whose entries each carry
at least `δ` and whose total is below `2δ` has at most one element: `card * δ ≤ ∑ y < 2δ` with
`δ > 0`. -/
theorem at_most_one_precedes {ℓ : ℕ} (y : Fin ℓ → ℝ) (I : Finset (Fin ℓ)) (δ : ℝ)
    (hδ : 0 < δ) (hy : ∀ i ∈ I, δ ≤ y i) (htot : ∑ i ∈ I, y i < 2 * δ) :
    I.card ≤ 1 := by
  have h : (I.card : ℝ) < 2 := lt_of_mul_lt_mul_right
    (by simpa using (Finset.card_nsmul_le_sum I y δ hy).trans_lt htot) hδ.le
  exact Nat.le_of_lt_succ (by exact_mod_cast h)

end Gap212.Auxiliary
