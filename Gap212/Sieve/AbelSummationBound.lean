/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic

/-!
# Summation by parts over `Finset.Ioc`, and the Abel bound it gives

Two purely algebraic facts about finite sums of reals over a half-open integer interval
`Finset.Ioc a b`. There is no arithmetic here: `S`, `g` and `u` are arbitrary functions `ℕ → ℝ`.

`Gap212.Sieve.sum_Ioc_by_parts` is the discrete integration-by-parts identity: if `S` is thought
of as a partial-sum function, so that `u n = S n - S (n - 1)` is its increment, then

  `∑_{a < n ≤ b} u n · g n = S b · g b - S a · g (a+1) + ∑_{a < n < b} S n · (g n - g (n+1))`.

It is an identity, with no hypothesis beyond `a < b`, and is proved by induction on `b` from the
base `b = a + 1` using `Nat.le_induction`.

`Gap212.Sieve.abs_sum_Ioc_mul_le` is the estimate that identity exists for. Given a bound `D` on
the partial sums `|S n|` over the range, a normalisation `S a = 0`, and a bound `V` on the total
variation `∑_{a < n < b} |g n - g (n+1)|` of the weight, it concludes

  `|∑_{a < n ≤ b} u n · g n| ≤ D · (|g b| + V)`.

This is the shape in which Abel summation is actually applied: the oscillation of `u` is used only
through the single number `D`, and the weight `g` only through `|g b|` and its variation. The
degenerate case `a = b` is allowed — both sides are then trivial, the left being an empty sum.

## Main results

* `Gap212.Sieve.sum_Ioc_by_parts`: summation by parts over `Finset.Ioc`.
* `Gap212.Sieve.abs_sum_Ioc_mul_le`: the Abel-summation bound `D · (|g b| + V)`.
-/

@[expose] public section

open Finset

namespace Gap212.Sieve

/-- **Summation by parts.** For `S g : ℕ → ℝ` and `a < b`, summing the increments
`S n - S (n - 1)` of `S` against the weight `g` over `Finset.Ioc a b` equals the boundary terms
`S b * g b - S a * g (a + 1)` plus the sum of `S` against the *backward differences* of `g` over
the open interval `Finset.Ioo a b`.

The subtraction `n - 1` is truncated subtraction in `ℕ`; every `n ∈ Finset.Ioc a b` satisfies
`n ≥ a + 1 ≥ 1`, so no truncation occurs in the terms that appear. -/
theorem sum_Ioc_by_parts {a b : ℕ} (hab : a < b) (S g : ℕ → ℝ) :
    ∑ n ∈ Finset.Ioc a b, (S n - S (n - 1)) * g n
      = S b * g b - S a * g (a + 1)
        + ∑ n ∈ Finset.Ioo a b, S n * (g n - g (n + 1)) := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp only [Nat.succ_eq_add_one]
    rw [Nat.Ioc_succ_singleton, Finset.Ioo_add_one_right_eq_Ioc, Finset.Ioc_self,
      Finset.sum_singleton, Finset.sum_empty, Nat.add_sub_cancel]
    ring
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top (le_of_lt hab), ih,
      Finset.Ioo_add_one_right_eq_Ioc, ← Finset.Ioo_insert_right hab,
      Finset.sum_insert (by simp)]
    have h1 : b + 1 - 1 = b := by omega
    rw [h1]
    ring

/-- **The Abel-summation bound.** Let `u` be the increment sequence of `S` on `Finset.Ioc a b`
(hypothesis `hu`), normalised by `S a = 0`. If every partial sum satisfies `|S n| ≤ D` on
`a ≤ n ≤ b`, and the weight `g` has total variation at most `V` across `Finset.Ioo a b`, then

  `|∑_{n ∈ Ioc a b} u n * g n| ≤ D * (|g b| + V)`.

Both `0 ≤ D` and `0 ≤ V` are consequences of the hypotheses, not extra assumptions: `D` bounds
`|S a| = 0`, and `V` bounds a sum of absolute values. The case `a = b` is degenerate and allowed:
the sum is empty and the right-hand side is nonnegative. -/
theorem abs_sum_Ioc_mul_le {a b : ℕ} (hab : a ≤ b) {u S g : ℕ → ℝ}
    (hu : ∀ n, a < n → n ≤ b → u n = S n - S (n - 1)) (hSa : S a = 0)
    {D : ℝ} (hS : ∀ n, a ≤ n → n ≤ b → |S n| ≤ D)
    {V : ℝ} (hV : ∑ n ∈ Finset.Ioo a b, |g n - g (n + 1)| ≤ V) :
    |∑ n ∈ Finset.Ioc a b, u n * g n| ≤ D * (|g b| + V) := by
  have hD : 0 ≤ D := by
    have h := hS a le_rfl hab
    rwa [hSa, abs_zero] at h
  have hV0 : 0 ≤ V := le_trans (Finset.sum_nonneg fun n _ => abs_nonneg _) hV
  rcases eq_or_lt_of_le hab with rfl | hlt
  · rw [Finset.Ioc_self, Finset.sum_empty, abs_zero]
    exact mul_nonneg hD (add_nonneg (abs_nonneg _) hV0)
  · have hrw : ∑ n ∈ Finset.Ioc a b, u n * g n
        = ∑ n ∈ Finset.Ioc a b, (S n - S (n - 1)) * g n :=
      Finset.sum_congr rfl fun n hn => by
        rw [hu n (Finset.mem_Ioc.mp hn).1 (Finset.mem_Ioc.mp hn).2]
    rw [hrw, sum_Ioc_by_parts hlt, hSa, zero_mul, sub_zero]
    calc |S b * g b + ∑ n ∈ Finset.Ioo a b, S n * (g n - g (n + 1))|
        ≤ |S b * g b| + |∑ n ∈ Finset.Ioo a b, S n * (g n - g (n + 1))| := abs_add_le _ _
      _ = |S b| * |g b| + |∑ n ∈ Finset.Ioo a b, S n * (g n - g (n + 1))| := by rw [abs_mul]
      _ ≤ |S b| * |g b| + ∑ n ∈ Finset.Ioo a b, |S n| * |g n - g (n + 1)| :=
          add_le_add le_rfl ((abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun n _ => (abs_mul _ _).le))
      _ ≤ D * |g b| + ∑ n ∈ Finset.Ioo a b, D * |g n - g (n + 1)| :=
          add_le_add (mul_le_mul_of_nonneg_right (hS b (le_of_lt hlt) le_rfl) (abs_nonneg _))
            (Finset.sum_le_sum fun n hn =>
              mul_le_mul_of_nonneg_right
                (hS n (le_of_lt (Finset.mem_Ioo.mp hn).1) (le_of_lt (Finset.mem_Ioo.mp hn).2))
                (abs_nonneg _))
      _ = D * |g b| + D * ∑ n ∈ Finset.Ioo a b, |g n - g (n + 1)| := by rw [Finset.mul_sum]
      _ ≤ D * |g b| + D * V := add_le_add le_rfl (mul_le_mul_of_nonneg_left hV hD)
      _ = D * (|g b| + V) := by ring

end Gap212.Sieve
