/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.SmoothNumbers
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The prime tail product tends to one

For the totient kernel, at **fixed** `W` the normalized Gram sum tends not to `∫F'G'` but to
`(∏_{p ∤ W}(1 - 1/(p-1)²)) · ∫F'G'`: the identity `φ(W∏ᵢ[dᵢ,d'ᵢ]) = φ(W)∏ᵢφ([dᵢ,d'ᵢ])` holds
only when the lcms are pairwise coprime, and correcting for this leaves the factor behind. (The
reciprocal kernel `1/∏ᵢ[dᵢ,d'ᵢ]` is already a product and has no such factor.) Since `W(x)` is a
primorial tending to infinity, the factor tends to `1`, and this file proves that.

The argument is elementary, using nothing about the distribution of primes beyond `2 ≤ p`. Since
`W(x)` is the primorial of `z`, a prime fails to divide `W(x)` exactly when it exceeds `z`, so the
product is a tail `∏_{p > z}(1 - 1/(p-1)²)`; and `∑_p 1/(p-1)²` converges by comparison with
`∑ 4/p²`, so the tail vanishes and the product tends to `1`.

## Main results

* `Gap212.Sieve.one_div_sub_one_sq_le`: `1/(p-1)² ≤ 4/p²` for `2 ≤ p` — the comparison. Sharp at
  `p = 2`, where both sides are `1`.
* `Gap212.Sieve.summable_primeTailWeight`: `∑_p 1/(p-1)²` converges.
* `Gap212.Sieve.one_sub_sum_le_prod_one_sub`: `1 - ∑ a ≤ ∏ (1 - a)` for `a` valued in `[0,1]`.
* `Gap212.Sieve.exists_threshold_prod_one_sub_ge`: for every `ε > 0` there is a `z`
  such that **every**
  finite product of `1 - 1/(p-1)²` over primes exceeding `z` lies in `[1 - ε, 1]`.

## Why the last statement has that shape

The products of interest run over the primes dividing a modulus, a set that varies with `x` and
is not the whole tail, so the bound is uniform in the finite set: the `z` depends only on `ε`.

`1 - 1/(p-1)² ∈ [0,1]` needs `p > 2`, since at `p = 2` the factor is `0`; the threshold `z ≥ 2` in
`exists_threshold_prod_one_sub_ge` supplies it. This is the same `p = 2` degeneracy that makes
`Gap212.Sieve.innerSumTotientConst e` vanish for odd `e`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset

/-- **The comparison behind the convergence**: `1/(p-1)² ≤ 4/p²` for `p ≥ 2`.
Sharp at `p = 2`, where
both sides are `1`; the slack is `(3p-2)(p-2)/(p²(p-1)²)`. -/
theorem one_div_sub_one_sq_le {p : ℕ} (hp : 2 ≤ p) :
    (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 4 / (p : ℝ) ^ 2 := by
  have h1 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hA : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
  have hB : (0 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hA hB]
  nlinarith

/-- The weight whose tail controls the correction factor, `1/(p-1)²` at a prime. -/
noncomputable def primeTailWeight (p : Nat.Primes) : ℝ :=
  (1 : ℝ) / ((((p : ℕ)) : ℝ) - 1) ^ 2

/-- `primeTailWeight p` is nonnegative. -/
theorem primeTailWeight_nonneg (p : Nat.Primes) : 0 ≤ primeTailWeight p := by
  have h1 : (2 : ℝ) ≤ (((p : ℕ)) : ℝ) := by exact_mod_cast p.2.two_le
  unfold primeTailWeight
  positivity

/-- **`∑_p 1/(p-1)²` converges**, by comparison with `∑ 4/p²`. Elementary: no distribution of
primes is used, only that every prime is at least `2`. -/
theorem summable_primeTailWeight : Summable primeTailWeight := by
  have hmaj : Summable (fun p : Nat.Primes => (4 : ℝ) / ((((p : ℕ)) : ℝ)) ^ 2) := by
    have h : Summable (fun n : ℕ => (4 : ℝ) / (n : ℝ) ^ 2) := by
      simpa [div_eq_mul_inv, mul_comm] using
        (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (4 : ℝ)
    exact h.subtype _
  exact hmaj.of_nonneg_of_le primeTailWeight_nonneg fun p ↦ one_div_sub_one_sq_le p.2.two_le

/-- **The elementary product bound**: for `a` valued in `[0,1]` on `s`, `1 - ∑ a ≤ ∏ (1 - a)`.

By induction on `s`: adjoining `i` multiplies the product by `1 - a i ≥ 0`, and
`(1 - a i)(1 - σ) = 1 - a i - σ + a i σ ≥ 1 - a i - σ`, the discarded `a i σ` being
non-negative. -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} {s : Finset ι} {a : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i t hit ih =>
    have h0' : ∀ j ∈ t, 0 ≤ a j := fun j hj ↦ h0 j (mem_cons_of_mem hj)
    have hai1 := h1 i (mem_cons_self i t)
    rw [prod_cons, sum_cons]
    nlinarith [mul_le_mul_of_nonneg_left (ih h0' fun j hj ↦ h1 j (mem_cons_of_mem hj))
      (sub_nonneg.2 hai1), mul_nonneg (h0 i (mem_cons_self i t)) (sum_nonneg h0')]

/-- At a prime above `2` the factor `1 - 1/(p-1)²` lies in `[0,1]`; at `p = 2` it
is `0`, which is why
the threshold is needed. -/
theorem primeTailWeight_le_one {p : Nat.Primes} (hp : 2 < (p : ℕ)) : primeTailWeight p ≤ 1 := by
  have h3 : (2 : ℝ) < (((p : ℕ)) : ℝ) := by exact_mod_cast hp
  unfold primeTailWeight
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- **The prime tail product tends to one, uniformly.** For every `ε > 0` there is a threshold
`z` such that *every* finite product of `1 - 1/(p-1)²` over primes exceeding `z` lies in
`[1 - ε, 1]`.

Consequently `(∏_{p ∤ W(x)}(1 - 1/(p-1)²)) → 1` as `W(x)` runs through the primorials, since
`p ∤ W(x)` is `p > z(x)` and `z(x) → ∞`. -/
theorem exists_threshold_prod_one_sub_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℕ, 2 ≤ z ∧ ∀ s : Finset Nat.Primes, (∀ p ∈ s, z < (p : ℕ)) →
      1 - ε ≤ ∏ p ∈ s, (1 - primeTailWeight p) ∧ ∏ p ∈ s, (1 - primeTailWeight p) ≤ 1 := by
  classical
  obtain ⟨F, hF⟩ := summable_primeTailWeight.vanishing (gt_mem_nhds hε)
  refine ⟨max 2 (F.sup (fun p => (p : ℕ))), le_max_left _ _, fun s hs => ?_⟩
  have hdisj : Disjoint s F := by
    refine disjoint_left.mpr fun p hps hpF ↦ ?_
    have := hs p hps
    have := le_sup (f := fun q : Nat.Primes ↦ (q : ℕ)) hpF
    lia
  have hsum : ∑ p ∈ s, primeTailWeight p < ε := hF s hdisj
  have hbnd : ∀ p ∈ s, 0 ≤ primeTailWeight p ∧ primeTailWeight p ≤ 1 := fun p hp ↦
    ⟨primeTailWeight_nonneg p, primeTailWeight_le_one ((le_max_left 2 _).trans_lt (hs p hp))⟩
  exact ⟨le_trans (by linarith) (one_sub_sum_le_prod_one_sub (fun p hp ↦ (hbnd p hp).1)
      fun p hp ↦ (hbnd p hp).2),
    prod_le_one (fun p hp ↦ by linarith [(hbnd p hp).2]) fun p hp ↦ by linarith [(hbnd p hp).1]⟩

end Gap212.Sieve
