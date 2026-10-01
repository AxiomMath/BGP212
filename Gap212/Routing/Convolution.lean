/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.Crude

/-!
# A convolution of coefficient sequences is a coefficient sequence

Needed because `Gap212.Routing.exists_crude_bound` asks for
`IsCoefficientSequenceFamily f`, and every
Harman-class member is a convolution. Divisor-boundedness closing under Dirichlet convolution is
folklore.

## The exponent grows by one

`|α ⋆ β (n;x)| ≤ ∑_{d ∣ n} |α(d;x)| |β(n/d;x)| ≤ τ(n) · C₁τ(n)^{k₁}L^{l₁} · C₂τ(n)^{k₂}L^{l₂}`,

using `τ(d) ≤ τ(n)` and `τ(n/d) ≤ τ(n)` for `d ∣ n` — both from `Nat.divisors_subset_of_dvd`. So
the divisor exponent is `k₁ + k₂ + 1`, the extra `1` paying for the number of terms. That growth is
harmless here: the crude bound replaces `τ(n)` by `2x` anyway, and the estimates never inspect the
exponent.

## `n = 0`

`Nat.divisors 0 = ∅`, so the convolution vanishes there and the bound is the trivial one — but it
does need `log x ≥ 0`, which is where `1 < x` is used.

## Main results

* `Gap212.Routing.isCoefficientSequence_dconv`.
-/

@[expose] public section

namespace Gap212.Routing

open Finset Real

/-- **A Dirichlet convolution of coefficient sequences is a coefficient sequence**, with divisor
exponent `k₁ + k₂ + 1`. -/
theorem isCoefficientSequence_dconv {α β : ℕ → ℝ → ℂ}
    (hα : IsCoefficientSequenceFamily α) (hβ : IsCoefficientSequenceFamily β) :
    IsCoefficientSequenceFamily (dconvFamily α β) := by
  obtain ⟨C₁, k₁, l₁, hC₁, h₁⟩ := hα
  obtain ⟨C₂, k₂, l₂, hC₂, h₂⟩ := hβ
  refine ⟨C₁ * C₂, k₁ + k₂ + 1, l₁ + l₂, by positivity, fun n x hx ↦ ?_⟩
  have hL : (0 : ℝ) ≤ log x := (Real.log_pos hx).le
  rcases eq_or_ne n 0 with rfl | hn0
  · -- `divisors 0 = ∅`, so the convolution vanishes.
    simp only [dconvFamily, Nat.divisors_zero, Finset.sum_empty, norm_zero]
    positivity
  · -- Each term is bounded by the same quantity.
    have hterm : ∀ d ∈ n.divisors,
        ‖α d x * β (n / d) x‖
          ≤ C₁ * C₂ * (n.divisors.card : ℝ) ^ (k₁ + k₂) * (log x) ^ (l₁ + l₂) := by
      intro d hd
      have hdvd := Nat.dvd_of_mem_divisors hd
      have hτd : (d.divisors.card : ℝ) ≤ n.divisors.card := by
        exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hn0 hdvd)
      have hτq : ((n / d).divisors.card : ℝ) ≤ n.divisors.card := by
        exact_mod_cast Finset.card_le_card
          (Nat.divisors_subset_of_dvd hn0 (Nat.div_dvd_of_dvd hdvd))
      rw [norm_mul]
      calc ‖α d x‖ * ‖β (n / d) x‖
          ≤ (C₁ * (n.divisors.card : ℝ) ^ k₁ * (log x) ^ l₁)
            * (C₂ * (n.divisors.card : ℝ) ^ k₂ * (log x) ^ l₂) := by
            gcongr
            · exact (h₁ d x hx).trans (by gcongr)
            · exact (h₂ (n / d) x hx).trans (by gcongr)
        _ = C₁ * C₂ * (n.divisors.card : ℝ) ^ (k₁ + k₂) * (log x) ^ (l₁ + l₂) := by ring
    -- Sum the bound over the `τ(n)` terms.
    calc ‖dconvFamily α β n x‖ ≤ ∑ d ∈ n.divisors, ‖α d x * β (n / d) x‖ := norm_sum_le _ _
      _ ≤ n.divisors.card •
            (C₁ * C₂ * (n.divisors.card : ℝ) ^ (k₁ + k₂) * (log x) ^ (l₁ + l₂)) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = C₁ * C₂ * (n.divisors.card : ℝ) ^ (k₁ + k₂ + 1) * (log x) ^ (l₁ + l₂) := by
          rw [nsmul_eq_mul]; ring

end Gap212.Routing
