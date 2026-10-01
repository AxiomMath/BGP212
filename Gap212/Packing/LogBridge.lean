/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

/-!
# Products of divisors against sums of logarithms

The packing conditions of Proposition 3 are inequalities on **sums** — `∑_{i ∈ I₁} yᵢ ≤ b`, where
`yᵢ = log_x(fᵢ)`. The moduli they are applied to are **products** — `q = e e' ∏ fᵢ ∏ f'ᵢ`, and what
the factor-extraction lemmas must produce is a divisor in a multiplicative window `[x^a, x^b]`.

This module is the dictionary between the two. The single fact that does the work is

    ∏_{i ∈ s} fᵢ = x ^ (∑_{i ∈ s} log_x fᵢ),

after which a bound on the sum of logarithms transfers to a bound on the product by monotonicity of
`x ^ ·`. That is what lets a partition supplied by `Ξ` be turned into a divisor of the right size:
the partition controls the sum, the identity converts it to the product, and
`Gap212.Packing.exists_divisor_window` finishes.

Everything is stated for tuples of *positive naturals*, since the rough factors `fᵢ` and the smooth
primes are natural numbers, and for base `x > 1`.

## Main results

* `Gap212.Packing.logb_prod_nat`: `log_x (∏ fᵢ) = ∑ log_x fᵢ`, for any base.
* `Gap212.Packing.prod_eq_rpow_sum_logb`: `∏ fᵢ = x ^ (∑ log_x fᵢ)`.
* `Gap212.Packing.prod_le_rpow_of_sum_le`: a bound on the sum of logarithms bounds the product.
* `Gap212.Packing.prod_lt_rpow_of_sum_lt`, `Gap212.Packing.rpow_lt_of_lt_logb`: the two strict
  forms, which are what produce an **open** window `(x^a, x^b)` from the retreat `1 - ε₀`.
* `Gap212.Packing.le_logb_of_rpow_le`: `x^δ ≤ f` gives `δ ≤ log_x f`, the form in which the
  roughness hypothesis `log_x fᵢ ≥ δ` is used.
* `Gap212.Packing.logb_le_of_le_rpow`: the converse direction, for the cap hypotheses.
* `Gap212.Packing.rpow_le_of_le_logb`: turning a logarithmic lower bound back into a size bound.
* `Gap212.Packing.logb_mul_nat`: the logarithm of a product of two positive naturals splits.
-/

@[expose] public section

namespace Gap212.Packing

open Finset Real

variable {ι : Type*} {x : ℝ}

/-- The base-`x` logarithm of a product of positive naturals is the sum of their logarithms. No
hypothesis on the base is needed: `logb` is `log / log x`, and the identity is `Real.log_prod`
divided through. -/
theorem logb_prod_nat (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, 1 ≤ f i) :
    logb x ((∏ i ∈ s, f i : ℕ) : ℝ) = ∑ i ∈ s, logb x (f i) := by
  have hne : ∀ i ∈ s, ((f i : ℝ)) ≠ 0 := by
    intro i hi
    have := hf i hi
    positivity
  unfold Real.logb
  rw [Nat.cast_prod, Real.log_prod hne, Finset.sum_div]

/-- **The bridge.** A product of positive naturals is `x` to the power of the sum of their base-`x`
logarithms.

This is the identity that converts the additive packing conditions into multiplicative statements
about divisors. -/
theorem prod_eq_rpow_sum_logb (hx : 1 < x) (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, 1 ≤ f i) :
    ((∏ i ∈ s, f i : ℕ) : ℝ) = x ^ (∑ i ∈ s, logb x (f i)) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hx1 : x ≠ 1 := ne_of_gt hx
  have hpos : (0 : ℝ) < ((∏ i ∈ s, f i : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    refine Finset.prod_pos fun i hi ↦ ?_
    have := hf i hi
    positivity
  rw [← logb_prod_nat s f hf, Real.rpow_logb hx0 hx1 hpos]

/-- A bound on the sum of logarithms bounds the product. This is the direction the packing
conditions are used in: `∑_{i ∈ I₁} log_x fᵢ ≤ b` gives `∏_{i ∈ I₁} fᵢ ≤ x^b`. -/
theorem prod_le_rpow_of_sum_le (hx : 1 < x) (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, 1 ≤ f i)
    {c : ℝ} (hc : ∑ i ∈ s, logb x (f i) ≤ c) :
    ((∏ i ∈ s, f i : ℕ) : ℝ) ≤ x ^ c := by
  rw [prod_eq_rpow_sum_logb hx s f hf]
  exact (Real.rpow_le_rpow_left_iff hx).mpr hc

/-- **The strict form.** A *strict* bound on the sum of logarithms bounds the product strictly:
`∑_{i ∈ I₁} log_x fᵢ < b` gives `∏_{i ∈ I₁} fᵢ < x^b`.

This is one of the two places the open window of a modulus family is produced. The rescaled profile
satisfies `log_x fᵢ = (1 - ε₀) yᵢ`, so a packing condition `∑_{I₁} yᵢ ≤ b` at the *bare* capacity
already gives `∑_{I₁} log_x fᵢ ≤ (1 - ε₀) b < b` whenever `ε₀ > 0` and `b > 0`. No inward inset on
the capacity is needed to reach the strict inequality — the retreat supplies it. -/
theorem prod_lt_rpow_of_sum_lt (hx : 1 < x) (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, 1 ≤ f i)
    {c : ℝ} (hc : ∑ i ∈ s, logb x (f i) < c) :
    ((∏ i ∈ s, f i : ℕ) : ℝ) < x ^ c := by
  rw [prod_eq_rpow_sum_logb hx s f hf]
  exact (Real.rpow_lt_rpow_left_iff hx).mpr hc

/-- Conversely, a bound on the product bounds the sum of logarithms. This is how the `Q`-membership
caps — `∏ fᵢ ≤ x^{(1-ε₀)B_{j,m}}` — become the hypotheses of `Ξ`. -/
theorem sum_logb_le_of_prod_le (hx : 1 < x) (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, 1 ≤ f i)
    {c : ℝ} (hc : ((∏ i ∈ s, f i : ℕ) : ℝ) ≤ x ^ c) :
    ∑ i ∈ s, logb x (f i) ≤ c := by
  rw [prod_eq_rpow_sum_logb hx s f hf] at hc
  exact (Real.rpow_le_rpow_left_iff hx).mp hc

/-- `x^δ ≤ f` gives `δ ≤ log_x f`. The roughness hypothesis of the generated moduli — each rough
factor is at least `x^δ` — enters `Ξ` in this form. -/
theorem le_logb_of_rpow_le (hx : 1 < x) {n : ℕ} {δ : ℝ} (hn : 1 ≤ n) (h : x ^ δ ≤ (n : ℝ)) :
    δ ≤ logb x (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hstep : x ^ δ ≤ x ^ (logb x (n : ℝ)) := by
    rwa [Real.rpow_logb (lt_trans zero_lt_one hx) (ne_of_gt hx) hnpos]
  exact (Real.rpow_le_rpow_left_iff hx).mp hstep

/-- `f ≤ x^c` gives `log_x f ≤ c`. Used for the upper caps on individual factors. -/
theorem logb_le_of_le_rpow (hx : 1 < x) {n : ℕ} {c : ℝ} (hn : 1 ≤ n) (h : (n : ℝ) ≤ x ^ c) :
    logb x (n : ℝ) ≤ c := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hstep : x ^ (logb x (n : ℝ)) ≤ x ^ c := by
    rwa [Real.rpow_logb (lt_trans zero_lt_one hx) (ne_of_gt hx) hnpos]
  exact (Real.rpow_le_rpow_left_iff hx).mp hstep

/-- A sub-product of a product of positive naturals divides it. Trivial, but it is what turns the
chosen block `I₁` of a partition into an actual divisor of the modulus. -/
theorem prod_subset_dvd_prod {s t : Finset ι} (hst : t ⊆ s) (f : ι → ℕ) :
    (∏ i ∈ t, f i) ∣ (∏ i ∈ s, f i) :=
  Finset.prod_dvd_prod_of_subset _ _ _ hst

/-- Splitting a product along a subset and its complement. Together with
`Gap212.Packing.exists_divisor_window` this is how the modulus is presented as `R · S` with `R` the
selected rough part. -/
theorem prod_sdiff_mul_prod [DecidableEq ι] {s t : Finset ι} (hst : t ⊆ s) (f : ι → ℕ) :
    (∏ i ∈ t, f i) * (∏ i ∈ s \ t, f i) = ∏ i ∈ s, f i := by
  rw [mul_comm]
  exact Finset.prod_sdiff hst

/-- `c ≤ log_x n` gives `x^c ≤ n`, the converse of `logb_le_of_le_rpow`. Needed to turn the
logarithmic lower bound on the selected part back into the size hypothesis of
`Gap212.Packing.exists_divisor_window`. -/
theorem rpow_le_of_le_logb (hx : 1 < x) {n : ℕ} {c : ℝ} (hn : 1 ≤ n) (h : c ≤ logb x (n : ℝ)) :
    x ^ c ≤ (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hstep : x ^ c ≤ x ^ (logb x (n : ℝ)) := (Real.rpow_le_rpow_left_iff hx).mpr h
  rwa [Real.rpow_logb (lt_trans zero_lt_one hx) (ne_of_gt hx) hnpos] at hstep

/-- **The strict form of `rpow_le_of_le_logb`**: `c < log_x n` gives `x^c < n`.

The other half of the open window. The selected part together with the reservoir has logarithm
strictly above `a` as soon as the modulus threshold `ε₁` is chosen strictly below `ε₀(1/2 - a)`,
and that strictness is what the open lower end of a modulus family asks for. -/
theorem rpow_lt_of_lt_logb (hx : 1 < x) {n : ℕ} {c : ℝ} (hn : 1 ≤ n) (h : c < logb x (n : ℝ)) :
    x ^ c < (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hstep : x ^ c < x ^ (logb x (n : ℝ)) := (Real.rpow_lt_rpow_left_iff hx).mpr h
  rwa [Real.rpow_logb (lt_trans zero_lt_one hx) (ne_of_gt hx) hnpos] at hstep

/-- The logarithm of a product of two positive naturals splits. -/
theorem logb_mul_nat {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    logb x ((a * b : ℕ) : ℝ) = logb x (a : ℝ) + logb x (b : ℝ) := by
  have ha0 : ((a : ℝ)) ≠ 0 := by positivity
  have hb0 : ((b : ℝ)) ≠ 0 := by positivity
  push_cast
  exact Real.logb_mul ha0 hb0

end Gap212.Packing
