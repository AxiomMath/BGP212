/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public meta import Gap212.Attr

/-!
# The window arithmetic behind the factor-extraction lemmas

The two-, three- and four-factor extraction lemmas each reduce, after the
combinatorial step, to a handful of affine inequalities between window endpoints. Those
inequalities are collected here so the extraction proofs cite them by name instead of
re-deriving them inline, and so the arithmetic is checked independently of the
combinatorics.

Everything is stated over an arbitrary linearly ordered field: the entries are logarithmic
sizes `yᵢ = log_x(fᵢ)` and the window endpoints are exponents, so nothing here needs `ℝ`
specifically, and the results are used at `ℝ`.

## Main results

* `Gap212.Windows.epsilon_two_factor`: the slack condition for the two-factor extraction.
* `Gap212.Windows.epsilon_three_factor`: the same for the three-factor extraction.
* `Gap212.Windows.three_factor_first_window`: the first window of the three-factor
  extraction is reachable.
* `Gap212.Windows.four_factor_second_bin`: the second bin of the four-factor extraction is
  reachable.
* `Gap212.Windows.four_factor_first_bin`: the first bin of the four-factor extraction has
  the capacity it needs.
* `Gap212.Windows.four_factor_r_window`: the `r`-window of the four-factor extraction is
  reachable.
-/

@[expose] public section

namespace Gap212.Windows

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **Slack for the two-factor extraction.** With `ε₁ ≤ ε₀(1/2 - a)` the mass left after
removing the second block still reaches the window's lower endpoint `a`.

The computation is `1/2 - ε₁ - (1-ε₀)(1/2 - a) = a - ε₁ + ε₀(1/2 - a)`, so the claim is
exactly `ε₁ ≤ ε₀(1/2 - a)`. -/
@[gap212 "lem_epsilon1_two_factor"]
theorem epsilon_two_factor {a ε₀ ε₁ : 𝕜} (h : ε₁ ≤ ε₀ * (1 / 2 - a)) :
    a ≤ 1 / 2 - ε₁ - (1 - ε₀) * (1 / 2 - a) := by
  nlinarith [h]

/-- **Slack for the three-factor extraction.** With `ε₁ ≤ ε₀(1/2 - b₁ - a₂)` the mass left
after removing the first block and the third still reaches `a₂`. -/
@[gap212 "lem_epsilon1_three_factor"]
theorem epsilon_three_factor {a₂ b₁ ε₀ ε₁ : 𝕜} (h : ε₁ ≤ ε₀ * (1 / 2 - b₁ - a₂)) :
    a₂ ≤ 1 / 2 - ε₁ - b₁ - (1 - ε₀) * (1 / 2 - b₁ - a₂) := by
  nlinarith [h]

/-- **The first window of the three-factor extraction is reachable.** Under
`b₁ - b₂ ≥ a₁ - a₂` the mass available after removing the second block and the third
reaches `a₁`, not merely `a₂`.

The previous lemma applied with `b₂` in place of `b₁` gives `b₁ - b₂ + a₂` as a lower
bound, and `b₁ - b₂ ≥ a₁ - a₂` turns that into `a₁`. -/
@[gap212 "lem_three_factor_first_window"]
theorem three_factor_first_window {a₁ a₂ b₁ b₂ ε₀ ε₁ : 𝕜}
    (hwidth : a₁ - a₂ ≤ b₁ - b₂) (h : ε₁ ≤ ε₀ * (1 / 2 - b₁ - a₂)) :
    a₁ ≤ 1 / 2 - ε₁ - b₂ - (1 - ε₀) * (1 / 2 - b₁ - a₂) := by
  nlinarith [h, hwidth]

/-- **The second bin of the four-factor extraction is reachable.** With
`3(b₁ - a₁) + (a₃ - b₃) ≥ 0`, subtracting the first, third and fourth capacities from the
total `1/2 + 2ω₀` leaves at least `a₂`.

The two occurrences of `1/2 + 2ω₀` cancel, leaving `a₂ + (3b₁ - 3a₁ + a₃ - b₃)`. -/
@[gap212 "lem_four_factor_second_bin"]
theorem four_factor_second_bin {a₁ a₂ a₃ b₁ b₃ ω₀ : 𝕜}
    (h : 0 ≤ 3 * (b₁ - a₁) + (a₃ - b₃)) :
    a₂ ≤ (1 / 2 + 2 * ω₀) - (2 * a₁ + b₃) - (1 / 2 + 2 * ω₀ - b₁ - a₂)
          - (a₁ - 2 * b₁ - a₃) := by
  nlinarith [h]

/-- **The first bin of the four-factor extraction has capacity.** Under the same hypothesis
the first and fourth capacities together do not exceed `b₁`, since their sum is
`b₁ - (3(b₁ - a₁) + (a₃ - b₃))`. -/
@[gap212 "lem_four_factor_first_bin"]
theorem four_factor_first_bin {a₁ a₃ b₁ b₃ : 𝕜}
    (h : 0 ≤ 3 * (b₁ - a₁) + (a₃ - b₃)) :
    (2 * a₁ + b₃) + (a₁ - 2 * b₁ - a₃) ≤ b₁ := by
  nlinarith [h]

/-- **The `r`-window of the four-factor extraction is reachable.** Under
`b₁ - b₂ ≥ a₁ - a₂` the mass left after the second and third capacities is at least `a₁`,
the difference being exactly `b₁ - b₂ + a₂`. -/
@[gap212 "lem_four_factor_r_window"]
theorem four_factor_r_window {a₁ a₂ b₁ b₂ ω₀ : 𝕜} (hwidth : a₁ - a₂ ≤ b₁ - b₂) :
    a₁ ≤ (1 / 2 + 2 * ω₀) - b₂ - (1 / 2 + 2 * ω₀ - b₁ - a₂) := by
  nlinarith [hwidth]

/-- **The nested window of the four-factor extraction.** For any `c` in the outer window
`[a₁, b₁]`, the reservoir `J₁` of small elements can hit the nested window `[2c + a₃, 2c + b₃]`
exactly.

The subset-sum mechanism is taken as the hypothesis `hsubset` — it is
`Gap212.Packing.exists_subset_sum_mem_Icc` at `ℝ`, and passing it in keeps this lemma independent
of which field the reservoir lives over.

Two cases, and the second is easy to miss: `hsubset` needs a nonnegative target, so it only
applies when `t ≤ 2c + a₃`. When `t` already exceeds `2c + a₃` the empty subset works, because
`c ≥ a₁` gives `t ≤ 2a₁ + b₃ ≤ 2c + b₃`. -/
@[gap212 "lem_four_factor_nested_window"]
theorem four_factor_nested_window
    {ℓ : ℕ} (z : Fin ℓ → ℝ) (J₁ : Finset (Fin ℓ))
    (δ a₁ a₃ b₁ b₃ c t : ℝ)
    (hsubset : ∀ w D : ℝ, (∀ i ∈ J₁, z i ≤ w) → 0 ≤ w → 0 ≤ D → D ≤ ∑ i ∈ J₁, z i →
      ∃ I ⊆ J₁, D ≤ ∑ i ∈ I, z i ∧ ∑ i ∈ I, z i ≤ D + w)
    (hz : ∀ i ∈ J₁, z i ≤ δ) (hδ : 0 < δ)
    (hc : a₁ ≤ c) (hcb : c ≤ b₁)
    (ht : t ≤ 2 * a₁ + b₃)
    (hreach : 2 * b₁ + a₃ ≤ t + ∑ i ∈ J₁, z i)
    (hwidth : δ ≤ b₃ - a₃) :
    ∃ J' ⊆ J₁, 2 * c + a₃ ≤ t + ∑ i ∈ J', z i ∧ t + ∑ i ∈ J', z i ≤ 2 * c + b₃ := by
  by_cases hD : t ≤ 2 * c + a₃
  · obtain ⟨I, hIsub, hlo, hhi⟩ :=
      hsubset δ (2 * c + a₃ - t) hz (le_of_lt hδ) (by linarith) (by linarith)
    exact ⟨I, hIsub, by linarith, by linarith⟩
  · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩ <;>
      simp only [Finset.sum_empty, add_zero] <;> linarith

end Gap212.Windows
