/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# The renewal identity for a Dirichlet-invertible weight

Let `b` be an arithmetic function and let `β` be *minus its Dirichlet logarithm*, i.e. the unique
arithmetic function with

  `b * β = -(b ⬝ log)`      (`Gap212.Sieve.summatory_mul_log`'s hypothesis)

where `*` is Dirichlet convolution and `⬝` pointwise multiplication. Writing
`S(t) = ∑_{n ≤ t} b n` and `V(t) = ∑_{n ≤ t} β n` for the two summatory functions, the two ways of
summing `∑_{mn ≤ t} b m β n` give the **renewal identity**

  `S(t) · log t = -∑_{n ≤ t} b n · (V(t/n) - log (t/n))`.

It is exact: no error term, no hypothesis beyond the convolution relation and `t > 0`.

It is used in `Gap212.Sieve.MoebiusDecay`: the whole left-hand side is expressed through the
deviation `V(y) - log y`, which for the weights of interest is Mertens' first theorem and tends to
a constant. At `b = μ/id`, `β = Λ/id` and the identity reads

  `(∑_{n ≤ t} μ(n)/n) · log t = -∑_{n ≤ t} (μ(n)/n) · (∑_{k ≤ t/n} Λ(k)/k - log (t/n))`.

## Main definitions

* `Gap212.Sieve.summatory`: `∑_{n ≤ t} b n`, for an arithmetic function `b` and a real `t`.

## Main results

* `Gap212.Sieve.summatory_hyperbola`: the Dirichlet hyperbola identity in the form
  `∑_{k ≤ t} (b * β) k = ∑_{n ≤ t} b n · V(t/n)`, for a real cutoff.
* `Gap212.Sieve.moebius_mul_vonMangoldt`: `μ * Λ = -(μ ⬝ log)`, the convolution relation at the
  Möbius weight, deduced from Mathlib's `ArithmeticFunction.sum_moebius_mul_log_eq` by Möbius
  inversion.
* `Gap212.Sieve.summatory_mul_log`: the renewal identity.
-/

@[expose] public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Gap212.Sieve

/-- The summatory function `∑_{n ≤ t} b n` of an arithmetic function, at a real cutoff. It depends
on `t` only through `⌊t⌋₊`. -/
noncomputable def summatory (b : ArithmeticFunction ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, b n

/-- `summatory b` takes the same value at `t` and `s` when `⌊t⌋₊ = ⌊s⌋₊`. -/
theorem summatory_eq_of_floor_eq {b : ArithmeticFunction ℝ} {t s : ℝ} (h : ⌊t⌋₊ = ⌊s⌋₊) :
    summatory b t = summatory b s := by
  rw [summatory, summatory, h]

@[simp] theorem summatory_natCast (b : ArithmeticFunction ℝ) (n : ℕ) :
    summatory b (n : ℝ) = ∑ k ∈ Finset.Ioc 0 n, b k := by
  rw [summatory, Nat.floor_natCast]

/-- `∑_{n ≤ t} b n` is nondecreasing when `b` is nonnegative. -/
theorem monotone_summatory {b : ArithmeticFunction ℝ} (hb : ∀ n, 0 ≤ b n) :
    Monotone (summatory b) := fun _ _ hts ↦
  sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right (Nat.floor_le_floor hts))
    fun n _ _ ↦ hb n

/-- `∑_{n ≤ t} b n` is nonnegative when `b` is nonnegative. -/
theorem summatory_nonneg {b : ArithmeticFunction ℝ} (hb : ∀ n, 0 ≤ b n) (t : ℝ) :
    0 ≤ summatory b t :=
  Finset.sum_nonneg fun n _ => hb n

/-- **The Dirichlet hyperbola identity**, at a real cutoff: summing `b m β n` over `mn ≤ t` by the
product and by the first factor. -/
theorem summatory_hyperbola (b β : ArithmeticFunction ℝ) (t : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, (b * β) n
      = ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, b n * summatory β (t / n) := by
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [summatory, Nat.floor_div_natCast]

/-- `μ * Λ = -(μ ⬝ log)`: the Möbius function's Dirichlet logarithm is `-Λ`. Mathlib's
`ArithmeticFunction.sum_moebius_mul_log_eq` is `(μ ⬝ log) * ζ = -Λ`; convolving with `μ` and using
`ζ * μ = 1` turns it into this. -/
theorem moebius_mul_vonMangoldt :
    ((μ : ArithmeticFunction ℝ) * vonMangoldt) = -((μ : ArithmeticFunction ℝ).pmul log) := by
  have h1 : ((μ : ArithmeticFunction ℝ).pmul log) * ζ = -vonMangoldt := by
    ext n
    rw [coe_mul_zeta_apply]
    simpa using sum_moebius_mul_log_eq (n := n)
  rw [← mul_one ((μ : ArithmeticFunction ℝ).pmul log), ← coe_zeta_mul_coe_moebius, ← mul_assoc,
    h1]
  ring

/-- **The renewal identity.** If `β` is minus the Dirichlet logarithm of `b`, then for every
`t > 0`

  `S(t) · log t = -∑_{n ≤ t} b n · (V(t/n) - log (t/n))`

with `S = summatory b` and `V = summatory β`. Exact, with no error term: the two sides are the two
ways of summing `b m β n` over the hyperbola `mn ≤ t`, after `log (t/n) = log t - log n`. -/
theorem summatory_mul_log {b β : ArithmeticFunction ℝ}
    (hbβ : b * β = -(b.pmul ArithmeticFunction.log)) {t : ℝ} (ht : 0 < t) :
    summatory b t * Real.log t
      = -∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, b n * (summatory β (t / n) - Real.log (t / n)) := by
  have hsplit : ∀ n ∈ Finset.Ioc 0 ⌊t⌋₊,
      b n * (summatory β (t / n) - Real.log (t / n))
        = b n * summatory β (t / n) - (b n * Real.log t - b n * Real.log n) := by
    intro n hn
    rw [Real.log_div ht.ne' (Nat.cast_ne_zero.mpr (mem_Ioc.mp hn).1.ne')]
    ring
  have hconv : ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, b n * summatory β (t / n)
      = -∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, b n * Real.log n := by
    rw [← summatory_hyperbola, hbβ]
    simp [Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, hconv, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← summatory]
  ring

end Gap212.Sieve
