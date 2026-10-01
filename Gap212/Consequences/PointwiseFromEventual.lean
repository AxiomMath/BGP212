/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Gap212.Attr
public import Gap212.Routing.Defs.Equidistribution
public import Gap212.Equidistribution.Moduli
public import Gap212.Consequences.Basic

/-!
# From a threshold to `x ≥ 3`

An equidistribution hypothesis holding for every `x ≥ x₀` holds for every `x ≥ 3`, at an enlarged
constant: above the threshold the hypothesis applies directly, and on the bounded range
`3 ≤ x ≤ x₀` the trivial discrepancy bound is absorbed into the constant.

## Main results

* `Gap212.hasEquidistribution_of_forall_ge`: the threshold is lowered to `3`.
-/

@[expose] public section

namespace Gap212


open Gap212 Real

/-- The constant of a coefficient bound is nonnegative: at `n = 1` the divisor factor is
`τ(1) ^ k = 1` and the logarithmic factor is `(1 + log 1) ^ l = 1`, so the bound reads
`‖f 1‖ ≤ C`. -/
private theorem nonneg_of_isCoefficientSequence {C : ℝ} {k l : ℕ} {f : ℕ → ℂ}
    (hf : IsCoefficientSequence C k l f) : 0 ≤ C := by
  simpa using (norm_nonneg (f 1)).trans (hf 1 le_rfl)

/-- The trivial discrepancy bound `Λ(y) = 2 C (1 + log (1 + c₁ y))^l ∑_{1 ≤ n ≤ c₁ y} τ(n)^k` is
non-negative as soon as `0 ≤ C`, at every `c₁` and `y`. Where the majorising sum is nonempty the
logarithm is taken at a point `≥ 2`, and where it is empty the bound is `0`. -/
private theorem trivialDiscrepancyBound_nonneg {C : ℝ} {k l : ℕ} {c₁ y : ℝ} (hC : 0 ≤ C) :
    0 ≤ 2 * C * (1 + Real.log (1 + c₁ * y)) ^ l *
      ∑ n ∈ Finset.Icc 1 ⌊c₁ * y⌋₊, (n.divisors.card : ℝ) ^ k := by
  rcases Nat.eq_zero_or_pos ⌊c₁ * y⌋₊ with h | h
  · simp [h]
  · have h1 : (1 : ℝ) ≤ c₁ * y := Nat.floor_pos.mp h
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + c₁ * y)
    exact mul_nonneg (mul_nonneg (by linarith) (pow_nonneg (by linarith) l))
      (Finset.sum_nonneg fun n _ ↦ by positivity)

/-- **The bounded range is absorbed.** For `3 ≤ x ≤ x₀`, a saving `A ≥ 0`, an exponent
`1/2 + 2ω ≥ 0`, a non-negative `C₁` and a non-negative `Λ`,

`x^{1/2+2ω} Λ ≤ (C₁ + (1/3) (log x₀)^A x₀^{1/2+2ω} Λ) x (log x)^{-A}`.

The left-hand side is at most `x₀^{1/2+2ω} Λ (log x)^A (log x)^{-A}` and the right-hand side is at
least `3 · (1/3) (log x₀)^A x₀^{1/2+2ω} Λ (log x)^{-A}`, so the two comparisons
`(log x)^A ≤ (log x₀)^A` and `x^{1/2+2ω} ≤ x₀^{1/2+2ω}` suffice. This is the inequality that ties
the factor `1/3` to the lower endpoint `3`. -/
private theorem absorb_trivial_bound_of_le_threshold {A ω x x₀ C₁ Λ : ℝ} (hω : 0 ≤ 1 / 2 + 2 * ω)
    (hA : 0 ≤ A) (hx : 3 ≤ x) (hxx₀ : x ≤ x₀) (hC₁ : 0 ≤ C₁) (hΛ : 0 ≤ Λ) :
    x ^ (1 / 2 + 2 * ω) * Λ ≤
      (C₁ + 1 / 3 * Real.log x₀ ^ A * x₀ ^ (1 / 2 + 2 * ω) * Λ) * x / Real.log x ^ A := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hL : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlx A
  have hlog : Real.log x ≤ Real.log x₀ := Real.log_le_log hx0 hxx₀
  have k1 : (0 : ℝ) ≤ x₀ ^ (1 / 2 + 2 * ω) * Λ := mul_nonneg (Real.rpow_nonneg (by linarith) _) hΛ
  have k2 : x ^ (1 / 2 + 2 * ω) * Λ * Real.log x ^ A ≤
      x₀ ^ (1 / 2 + 2 * ω) * Λ * Real.log x₀ ^ A := by
    gcongr
  rw [le_div_iff₀ hL]
  nlinarith [mul_nonneg hC₁ hx0.le, mul_nonneg (Real.rpow_nonneg (hlx.le.trans hlog) A) k1]

/-- **From a threshold to `x ≥ 3`** (`Gap212.hasEquidistribution_of_forall_ge`). -/
@[gap212 "lem_pointwise_from_eventual"]
theorem hasEquidistribution_of_forall_ge {C : ℝ} {k l : ℕ} {c₀ c₁ b ω A x₀ C₁ : ℝ}
    {P : ℝ → Finset ℕ → (ℕ → ℂ) → ℕ → Prop}
    (hω : 0 ≤ 1 / 2 + 2 * ω) (hA : 0 ≤ A) (hx₀ : 3 ≤ x₀) (hC₁ : 0 ≤ C₁)
    (h : ∀ x ≥ x₀, ∀ D ⊆ moduliRange x ω, ∀ f : ℕ → ℂ, ∀ a : ℕ, P x D f a →
      ∀ N : ℝ, 1 ≤ N → N ≤ b * x → IsCoefficientSequence C k l f →
        LocatedAtScale c₀ c₁ f N → f 0 = 0 → HasEquidistribution x D f a A C₁) :
    ∀ x ≥ (3 : ℝ), ∀ D ⊆ moduliRange x ω, ∀ f : ℕ → ℂ, ∀ a : ℕ, P x D f a →
      ∀ N : ℝ, 1 ≤ N → N ≤ b * x → IsCoefficientSequence C k l f →
        LocatedAtScale c₀ c₁ f N → f 0 = 0 →
          HasEquidistribution x D f a A
            (C₁ + 1 / 3 * Real.log x₀ ^ A * x₀ ^ (1 / 2 + 2 * ω) *
              (2 * C * (1 + Real.log (1 + c₁ * (b * x₀))) ^ l *
                ∑ n ∈ Finset.Icc 1 ⌊c₁ * (b * x₀)⌋₊, (n.divisors.card : ℝ) ^ k)) := by
  intro x hx D hD f a hP N hN hNx hf hloc hf0
  have hΛ : (0 : ℝ) ≤ 2 * C * (1 + Real.log (1 + c₁ * (b * x₀))) ^ l *
      ∑ n ∈ Finset.Icc 1 ⌊c₁ * (b * x₀)⌋₊, (n.divisors.card : ℝ) ^ k :=
    trivialDiscrepancyBound_nonneg (nonneg_of_isCoefficientSequence hf)
  rcases le_or_gt x₀ x with hxx₀ | hxx₀
  · -- Above the threshold the hypothesis applies, and the constant has only grown.
    have hp : 0 < Real.log x ^ A := Real.rpow_pos_of_pos (Real.log_pos (by linarith)) A
    have hC₀ : (0 : ℝ) ≤ 1 / 3 * Real.log x₀ ^ A * x₀ ^ (1 / 2 + 2 * ω) *
        (2 * C * (1 + Real.log (1 + c₁ * (b * x₀))) ^ l *
          ∑ n ∈ Finset.Icc 1 ⌊c₁ * (b * x₀)⌋₊, (n.divisors.card : ℝ) ^ k) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) A).le)
        (Real.rpow_nonneg (by linarith) _)) hΛ
    exact (h x hxx₀ D hD f a hP N hN hNx hf hloc hf0).trans (by gcongr; linarith)
  · -- On the bounded range `3 ≤ x ≤ x₀` the trivial discrepancy bound suffices.
    have hbpos : 0 < b := by nlinarith [hN.trans hNx]
    have htriv := (norm_sumError_le_and_sum_norm_sumError_le_of_located hf hloc hf0
      (by linarith : (0 : ℝ) < N) (hNx.trans (by nlinarith : b * x ≤ b * x₀)) a).2
      x ω (by linarith) D hD
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun d _ _ ↦ norm_nonneg _).trans
        (htriv.trans (absorb_trivial_bound_of_le_threshold hω hA hx hxx₀.le hC₁ hΛ))


end Gap212
