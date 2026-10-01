/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Harmonic.Bounds
public import PrimeGapsTheory.Arithmetic.Mertens.CoprimeHarmonic
public import Gap212.Sieve.PrimeTailProduct
public meta import Gap212.Attr

/-!
# The Mertens asymptotic for the weight `μ²/φ` over a coprimality class

For `W ≥ 1` squarefree and `N ≥ 1`,

  `∑_{e ≤ N, (W,e)=1} μ²(e)/φ(e) = (φ(W)/W)·(log N + γ + ℓ_W) + O(1 + τ(W)/N)`,

with an **absolute** `O`-constant (`Gap212.Sieve.sum_moebiusSq_div_totient_coprime`). Here
`ℓ_W = ∑_{p ∣ W} log p/(p-1)` is the constant of the coprime harmonic sum
(`PrimeGaps.ellV`). The prefactor is exactly `φ(W)/W` with **no** correction factor, and that is
the whole point: the local factor of the weight at `p ∤ W` is `(1 + 1/(p-1))(1 - 1/p) = 1`, so
nothing survives. This is what distinguishes the reciprocal kernel from the totient kernel, whose
analogue does carry a correction.

## Why the proof is elementary, and what carries it

For squarefree `n` the weight is a product of geometric series,

  `μ²(n)/φ(n) = (1/n)∏_{p ∣ n}(1 - 1/p)^{-1} = ∑_{m : rad(m) = n} 1/m`,

`rad` being the radical (`Gap212.Sieve.rad`). Summing over `n ≤ N` therefore turns the weighted sum
into a *reciprocal* sum over the integers of radical at most `N`, and every `k ≤ N` occurs, with
`n = rad k`. The main term is thus the coprime harmonic sum, which the dependency already supplies
with the right constant and an explicit rate
(`PrimeGaps.coprime_reciprocal_sum_asymptotic`), and the whole difficulty is the excess — the `k`
with `rad k ≤ N < k`.

The excess is `O(1)`, absolutely, and the bound needs nothing analytic. Write `k = a·b²` with `a`
squarefree (`Nat.sq_mul_squarefree`). Then `a` is a squarefree divisor of `k`, hence divides
`rad k ≤ N`; and `k > N` forces `a > N/b²`, so `a` is confined to `(N/b², N]`, a range of
logarithmic length `2 log b`. Also `b ≥ 2`, since `b = 1` would make `k = a` squarefree and so
equal to its own radical. Hence

  `∑_{rad k ≤ N < k} 1/k ≤ ∑_{b ≥ 2}(1/b²)(1 + 2 log b) ≤ 9`

(`Gap212.Sieve.sum_filter_gt_reach_le` via `Gap212.Sieve.sum_excess_pairs_le`), the two series
being summed by telescoping (`Gap212.Sieve.sum_inv_sq_le`, `Gap212.Sieve.sum_inv_mul_sqrt_le`)
after `log b ≤ 2√b`.

Everything is kept finite: instead of the infinite sum `∑_{rad m ∣ n} 1/m` the proof uses the
divisors of `n^J` for a single `J` depending only on `N` (`Gap212.Sieve.expo`), and the defect
between the truncated Euler product and `n/φ(n)` is `≤ 1/2` in total
(`Gap212.Sieve.sum_defect_le`). So no `tsum`, no summability of a multiplicative function, and no
Euler product over all primes enters.

## The `W`-dependence

`Gap212.Sieve.MertensWeightedGramLimit` needs
`∑_{e≤y,(e,W)=1}μ²(e)/φ(e) = (φ(W)/W)(log y + o(log y))` with `W = W(x)` the primorial of
`⌊log log log x⌋` and `y` of size `x^β`. The error here is `O(1 + τ(W)/N)`; dividing by the
prefactor costs `W/φ(W) ≪ log log W`, and `τ(W(x)) = 2^{⌊log log log x⌋} = (log log x)^{log 2}`, so
the whole error is `O((log log x)^{1+log 2})`, against `log y ≍ β log x`. The `W`-dependence is
therefore explicit and harmless.

## Main definitions

* `Gap212.Sieve.rad`: the radical, `∏_{p ∣ n} p`.
* `Gap212.Sieve.geomDefect`: the truncated geometric factor `∏_{p ∣ n}(1 - p^{-(J+1)})`.
* `Gap212.Sieve.expo`: the truncation exponent `2·⌊log₂ N⌋ + 2`.
* `Gap212.Sieve.sqSplit`: a choice of `(a, b)` with `k = b²a` and `a` squarefree.
* `Gap212.Sieve.sqfreeBase`, `Gap212.Sieve.reach`: the pair sum's base points and the integers it
  reaches.

## Main results

* `Gap212.Sieve.sum_inv_divisors_pow`: the truncated Euler product
  `∑_{d ∣ n^J} 1/d = Q(n,J)·(n/φ(n))` for squarefree `n`.
* `Gap212.Sieve.sum_moebiusSq_div_totient_sub_coprimeReciprocal`: the sandwich
  `0 ≤ A_W(N) - ∑_{k≤N,(k,W)=1}1/k ≤ 10`, with an absolute constant.
* `Gap212.Sieve.sum_moebiusSq_div_totient_coprime`: **the asymptotic**, with main term
  `(φ(W)/W)(log N + γ + ℓ_W)` and error `≤ C·(1 + τ(W)/N)` for an absolute `C` (the dependency's
  coprime-harmonic constant plus `10`).
* `Gap212.Sieve.sum_moebiusSq_div_totient_coprime_log`: the same in the form
  `(φ(W)/W)·(log N + O_W(1))`, with the `O_W(1)` named.
-/

@[expose] public section

open Finset

namespace Gap212.Sieve

open scoped ArithmeticFunction.Moebius

/-! ## The radical -/

/-- **The radical** `rad n = ∏_{p ∣ n} p`, the product of the distinct primes dividing `n`. It is
the squarefree number with the same prime factors as `n`, and `rad 0 = rad 1 = 1`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- `rad n` divides `n`. -/
theorem rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

/-- `rad n` has the same prime factors as `n`. -/
theorem primeFactors_rad (n : ℕ) : (rad n).primeFactors = n.primeFactors :=
  Nat.primeFactors_prod_primeFactors n

/-- `rad n` is positive. -/
theorem rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

/-- `rad n` is squarefree. -/
theorem squarefree_rad (n : ℕ) : Squarefree (rad n) :=
  squarefree_prod_of_pairwise_isCoprime (fun _ hp _ hq hpq => Nat.coprime_iff_isRelPrime.mp
    ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq))
    (fun _ hp => (Nat.prime_of_mem_primeFactors hp).squarefree)

/-- The radical of a squarefree number is the number itself. -/
theorem rad_eq_self {n : ℕ} (hn : Squarefree n) : rad n = n :=
  Nat.prod_primeFactors_of_squarefree hn

/-- For `n ≠ 0`, `rad n ≤ n`. -/
theorem rad_le {n : ℕ} (hn : n ≠ 0) : rad n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (rad_dvd n)

/-- A squarefree divisor of `n` divides `rad n`: its prime factors are among `n`'s, and both sides
are products over their prime factors. -/
theorem dvd_rad_of_squarefree {a n : ℕ} (ha : Squarefree a) (hdvd : a ∣ n) (hn : n ≠ 0) :
    a ∣ rad n := by
  rw [← rad_eq_self ha, rad, rad]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono hdvd hn)

/-- **Every `k` divides a fixed power of its radical**, once the exponent beats `log₂ k`: the
`p`-adic valuation of `k` is at most `log₂ k`, and `rad k` carries each prime exactly once. -/
theorem dvd_rad_pow {k J : ℕ} (hk : k ≠ 0) (hJ : Nat.log 2 k ≤ J) : k ∣ rad k ^ J := by
  have hr0 : rad k ≠ 0 := (rad_pos k).ne'
  rw [← Nat.factorization_le_iff_dvd hk (pow_ne_zero _ hr0), Finsupp.le_def]
  intro p
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  by_cases hp : p ∈ k.primeFactors
  · have hpp := Nat.prime_of_mem_primeFactors hp
    rw [Nat.factorization_eq_one_of_squarefree (squarefree_rad k) hpp
      (Nat.dvd_of_mem_primeFactors (primeFactors_rad k ▸ hp)), mul_one]
    exact (Nat.le_log_of_pow_le one_lt_two ((Nat.pow_le_pow_left hpp.two_le _).trans
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (Nat.ordProj_dvd k p)))).trans hJ
  · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
    simp [hp]

private lemma primeFactors_subset_of_dvd_pow {n m J : ℕ} (hn : n ≠ 0) (hJ : J ≠ 0)
    (hmd : m ∣ n ^ J) : m.primeFactors ⊆ n.primeFactors :=
  Nat.primeFactors_pow n hJ ▸ Nat.primeFactors_mono hmd (pow_ne_zero _ hn)

/-- **The radical of `n·m` is `n`** when `n` is squarefree and `m` divides a power of `n`: the two
have the same prime factors. This is what makes the pair `(n, m)` recoverable from the product,
hence the reindexing below a bijection. -/
theorem rad_mul_of_dvd_pow {n m J : ℕ} (hn : Squarefree n) (hJ : J ≠ 0) (hm : m ≠ 0)
    (hmd : m ∣ n ^ J) : rad (n * m) = n := by
  rw [rad, Nat.primeFactors_mul hn.ne_zero hm,
    Finset.union_eq_left.mpr (primeFactors_subset_of_dvd_pow hn.ne_zero hJ hmd),
    Nat.prod_primeFactors_of_squarefree hn]

/-- Coprimality to `W` only sees the prime factors, so it transfers between `n` and `n·m` whenever
`m` divides a power of `n`. -/
theorem coprime_mul_of_dvd_pow {W n m J : ℕ} (hmd : m ∣ n ^ J) (h : Nat.Coprime W n) :
    Nat.Coprime W (n * m) :=
  h.mul_right ((h.pow_right J).coprime_dvd_right hmd)

/-! ## The truncated Euler product for the reciprocal-divisor sum -/

/-- `∑_{d ∣ N} 1/d = (∑_{d ∣ N} d)/N`, by pairing `d` with `N/d`. -/
theorem sum_inv_divisors {N : ℕ} (hN : N ≠ 0) :
    ∑ d ∈ N.divisors, (1 : ℝ) / d = (∑ d ∈ N.divisors, (d : ℝ)) / N := by
  rw [← Nat.sum_div_divisors N (fun d => (1 : ℝ) / d), Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd)
    (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne')]
  field_simp

/-- The truncated geometric factor `∏_{p ∣ n}(1 - p^{-(J+1)})`, the only thing separating the
divisor sum of `n^J` from the full Euler product `n/φ(n)`. -/
noncomputable def geomDefect (n J : ℕ) : ℝ := ∏ p ∈ n.primeFactors, (1 - ((p : ℝ)⁻¹) ^ (J + 1))

private lemma two_le_of_mem_primeFactors {n p : ℕ} (hp : p ∈ n.primeFactors) : (2 : ℝ) ≤ p := by
  exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le

private lemma inv_pow_le_one_of_mem {n p : ℕ} (J : ℕ) (hp : p ∈ n.primeFactors) :
    ((p : ℝ)⁻¹) ^ (J + 1) ≤ 1 :=
  pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith [two_le_of_mem_primeFactors hp]))

/-- `geomDefect n J` is nonnegative. -/
theorem geomDefect_nonneg (n J : ℕ) : 0 ≤ geomDefect n J :=
  Finset.prod_nonneg fun _ hp => sub_nonneg.mpr (inv_pow_le_one_of_mem J hp)

/-- `geomDefect n J` is at most `1`. -/
theorem geomDefect_le_one (n J : ℕ) : geomDefect n J ≤ 1 :=
  Finset.prod_le_one (fun _ hp => sub_nonneg.mpr (inv_pow_le_one_of_mem J hp))
    (fun _ _ => sub_le_self _ (by positivity))

/-- The defect from `1` is at most `ω(n)·2^{-(J+1)}`: each omitted factor is `p^{-(J+1)} ≤
2^{-(J+1)}`, and `1 - ∏(1 - x_p) ≤ ∑ x_p`. -/
theorem one_sub_geomDefect_le (n J : ℕ) :
    1 - geomDefect n J ≤ (#n.primeFactors : ℝ) * (2 : ℝ)⁻¹ ^ (J + 1) := by
  have hb := one_sub_sum_le_prod_one_sub (s := n.primeFactors) (fun _ _ => by positivity)
    (fun _ => inv_pow_le_one_of_mem J)
  have hsum := Finset.sum_le_card_nsmul n.primeFactors (fun p : ℕ => ((p : ℝ)⁻¹) ^ (J + 1)) _
    fun p hp => pow_le_pow_left₀ (by positivity)
      (inv_anti₀ two_pos (two_le_of_mem_primeFactors hp)) _
  rw [nsmul_eq_mul] at hsum
  rw [geomDefect]
  linarith

/-- **The truncated Euler product.** For squarefree `n` and `J ≥ 1`,
`∑_{d ∣ n^J} 1/d = Q(n,J)·(n/φ(n))` with `Q(n,J) = ∏_{p ∣ n}(1 - p^{-(J+1)})`. Both sides are
products over `n.primeFactors` of the truncated geometric series `∑_{j ≤ J} p^{-j}`. -/
theorem sum_inv_divisors_pow {n J : ℕ} (hn : Squarefree n) (hJ : J ≠ 0) :
    ∑ d ∈ (n ^ J).divisors, (1 : ℝ) / d
      = geomDefect n J * ((n : ℝ) / (n.totient : ℝ)) := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hnJ : n ^ J ≠ 0 := pow_ne_zero _ hn0
  -- the divisor sum of `n^J`, as a product of truncated geometric series in `p`
  have hcast : (∑ d ∈ (n ^ J).divisors, (d : ℝ))
      = ∏ p ∈ n.primeFactors, ∑ k ∈ range (J + 1), (p : ℝ) ^ k := by
    rw [← Nat.cast_sum, Nat.sum_divisors hnJ, Nat.primeFactors_pow n hJ]
    push_cast
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_one_of_squarefree hn (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp), mul_one]
  -- `n ^ J = ∏ p ^ J`
  have hnpow : (n : ℝ) ^ J = ∏ p ∈ n.primeFactors, (p : ℝ) ^ J := by
    rw [Finset.prod_pow, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
  -- the untruncated factor is `n / φ n`
  have hphi : (n : ℝ) / n.totient = (∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ := by
    have hq := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    push_cast at hq
    rw [hq]
    field_simp
  rw [sum_inv_divisors hnJ, hcast, Nat.cast_pow, hnpow, ← Finset.prod_div_distrib, hphi,
    geomDefect, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp2 := two_le_of_mem_primeFactors hp
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [geom_sum_eq (by linarith), inv_pow, pow_succ]
  field_simp

/-! ## Two telescoping series, and the harmonic length of a short range -/

private lemma inv_sq_le_telescope (i : ℕ) :
    (1 : ℝ) / ((i : ℝ) + 2) ^ 2 ≤ (1 : ℝ) / ((i : ℝ) + 1) - (1 : ℝ) / ((i : ℝ) + 2) := by
  rw [div_sub_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) i]

private lemma sum_Icc_two_le_of_telescope {g f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i)
    (h : ∀ i, g (i + 2) ≤ f i - f (i + 1)) (B : ℕ) : ∑ b ∈ Finset.Icc 2 B, g b ≤ f 0 := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  calc ∑ i ∈ range (B + 1 - 2), g (2 + i) ≤ ∑ i ∈ range (B + 1 - 2), (f i - f (i + 1)) :=
        Finset.sum_le_sum fun i _ => add_comm i 2 ▸ h i
    _ = f 0 - f (B + 1 - 2) := Finset.sum_range_sub' f _
    _ ≤ f 0 := sub_le_self _ (hf _)

/-- `∑_{b=2}^{B} 1/b² ≤ 1`, by telescoping `1/b² ≤ 1/(b-1) - 1/b`. -/
theorem sum_inv_sq_le (B : ℕ) : ∑ b ∈ Finset.Icc 2 B, (1 : ℝ) / (b : ℝ) ^ 2 ≤ 1 :=
  (sum_Icc_two_le_of_telescope (f := fun j => 1 / ((j : ℝ) + 1)) (fun _ => by positivity)
    (fun i => by convert inv_sq_le_telescope i using 3 <;> push_cast <;> ring) B).trans
    (by norm_num)

private lemma inv_mul_sqrt_le_telescope (i : ℕ) :
    (1 : ℝ) / (((i : ℝ) + 2) * Real.sqrt ((i : ℝ) + 2))
      ≤ 2 / Real.sqrt ((i : ℝ) + 1) - 2 / Real.sqrt ((i : ℝ) + 2) := by
  set u := Real.sqrt ((i : ℝ) + 1)
  set v := Real.sqrt ((i : ℝ) + 2)
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hu0 : 0 < u := Real.sqrt_pos.mpr (by linarith)
  have hv0 : 0 < v := Real.sqrt_pos.mpr (by linarith)
  have hu2 : u ^ 2 = (i : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have hv2 : v ^ 2 = (i : ℝ) + 2 := Real.sq_sqrt (by linarith)
  rw [← hv2, div_sub_div _ _ hu0.ne' hv0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  -- `(v - u)(v + u) = 1`, and the difference of the two sides is `(v - u)² v (2v + u) ≥ 0`
  have hdiff : (v - u) * (v + u) = 1 := by linear_combination hv2 - hu2
  linarith [mul_nonneg (mul_nonneg (sq_nonneg (v - u)) hv0.le) (by positivity : 0 ≤ 2 * v + u),
    congrArg (· * (u * v)) hdiff]

/-- `∑_{b=2}^{B} 1/(b√b) ≤ 2`, by telescoping against `2/√(b-1) - 2/√b`. -/
theorem sum_inv_mul_sqrt_le (B : ℕ) :
    ∑ b ∈ Finset.Icc 2 B, (1 : ℝ) / ((b : ℝ) * Real.sqrt b) ≤ 2 :=
  (sum_Icc_two_le_of_telescope (f := fun j => 2 / Real.sqrt ((j : ℝ) + 1))
    (fun _ => by positivity)
    (fun i => by convert inv_mul_sqrt_le_telescope i using 3 <;> push_cast <;> ring_nf) B).trans
    (by norm_num)

/-- `log t ≤ 2√t`: apply `log s ≤ s - 1` at `s = √t`. -/
theorem log_le_two_mul_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ht)
  rw [Real.log_sqrt ht.le] at h
  linarith [Real.sqrt_nonneg t]

/-- `∑_{b=2}^{B} log b / b² ≤ 4`, from `log b ≤ 2√b` and the previous telescoping bound. -/
theorem sum_log_div_sq_le (B : ℕ) :
    ∑ b ∈ Finset.Icc 2 B, Real.log b / (b : ℝ) ^ 2 ≤ 4 := by
  have hterm : ∀ b ∈ Finset.Icc 2 B,
      Real.log b / (b : ℝ) ^ 2 ≤ 2 * ((1 : ℝ) / ((b : ℝ) * Real.sqrt b)) := by
    intro b hb
    have hb0 : (0 : ℝ) < b := Nat.cast_pos.mpr (two_pos.trans_le (Finset.mem_Icc.mp hb).1)
    calc Real.log b / (b : ℝ) ^ 2 ≤ 2 * Real.sqrt b / (b : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right (log_le_two_mul_sqrt hb0) (by positivity)
      _ = 2 * ((1 : ℝ) / ((b : ℝ) * Real.sqrt b)) := by
          field_simp
          exact Real.sq_sqrt hb0.le
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  linarith [sum_inv_mul_sqrt_le B]

/-- **The harmonic length of the excess range.** For `b ≥ 2` the integers `a ≤ N` with `a b² > N`
are exactly those in `(N/b², N]`, and the reciprocal sum over that range is at most
`1 + 2 log b` — no dependence on `N`. -/
theorem sum_inv_filter_mul_sq_le {N b : ℕ} (hN : 1 ≤ N) (hb : 2 ≤ b) :
    ∑ a ∈ Finset.Icc 1 N with N < a * b ^ 2, (1 : ℝ) / a ≤ 1 + 2 * Real.log b := by
  obtain ⟨m, hmN, hmiff⟩ : ∃ m : ℕ, m ≤ N ∧ ∀ a : ℕ, (m < a ↔ N < a * b ^ 2) :=
    ⟨N / b ^ 2, Nat.div_le_self _ _, fun a => Nat.div_lt_iff_lt_mul (by positivity)⟩
  have hset : (Finset.Icc 1 N).filter (fun a => N < a * b ^ 2)
      = Finset.Ico (m + 1) (N + 1) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, ← hmiff]
    omega
  rw [hset]
  -- split the harmonic sum
  have hsplit := Finset.sum_Ico_consecutive (fun a : ℕ => (1 : ℝ) / a)
    (by omega : 1 ≤ m + 1) (by omega : m + 1 ≤ N + 1)
  have hIco : ∀ k : ℕ, (∑ a ∈ Finset.Ico 1 (k + 1), (1 : ℝ) / a) = (harmonic k : ℝ) := fun k => by
    rw [PrimeGaps.harmonic_cast_eq_sum, Finset.Ico_add_one_right_eq_Icc]
  rw [hIco, hIco] at hsplit
  -- `N < (m+1) b²`, so `log N ≤ log (m+1) + 2 log b`
  have hb0 : (0 : ℝ) < b := Nat.cast_pos.mpr (by omega)
  have hlog : Real.log N ≤ Real.log (↑(m + 1) * (b : ℝ) ^ 2) :=
    Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast ((hmiff _).mp m.lt_succ_self).le)
  rw [Real.log_mul (by positivity) (pow_ne_zero _ hb0.ne'), Real.log_pow, Nat.cast_ofNat] at hlog
  linarith [log_add_one_le_harmonic m, harmonic_le_one_add_log N]

/-- **The `(b, a)` sum that dominates the excess** is bounded absolutely: `1 + 2·4 = 9`. -/
theorem sum_excess_pairs_le {N B : ℕ} (hN : 1 ≤ N) :
    ∑ q ∈ (Finset.Icc 2 B) ×ˢ (Finset.Icc 1 N) with N < q.2 * q.1 ^ 2,
        (1 : ℝ) / ((q.2 : ℝ) * (q.1 : ℝ) ^ 2) ≤ 9 := by
  rw [Finset.sum_filter, Finset.sum_product]
  have hb : ∀ b ∈ Finset.Icc 2 B,
      (∑ a ∈ Finset.Icc 1 N, if N < a * b ^ 2 then (1 : ℝ) / ((a : ℝ) * (b : ℝ) ^ 2) else 0)
        ≤ (1 : ℝ) / (b : ℝ) ^ 2 + 2 * (Real.log b / (b : ℝ) ^ 2) := by
    intro b hb
    calc _ = (1 / (b : ℝ) ^ 2) * ∑ a ∈ Finset.Icc 1 N with N < a * b ^ 2, (1 : ℝ) / a := by
          rw [Finset.mul_sum, Finset.sum_filter]
          exact Finset.sum_congr rfl fun a _ => by split_ifs <;> ring
      _ ≤ (1 / (b : ℝ) ^ 2) * (1 + 2 * Real.log b) :=
          mul_le_mul_of_nonneg_left (sum_inv_filter_mul_sq_le hN (Finset.mem_Icc.mp hb).1)
            (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum hb).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith [sum_inv_sq_le B, sum_log_div_sq_le B]

/-! ## The reindexing: from the `μ²/φ` sum to a reciprocal sum over integers of small radical -/

/-- The truncation exponent: `2·⌊log₂ N⌋ + 2`. It is large enough that every `k ≤ N` divides
`(rad k)^{expo N}`, and that the truncated Euler product's defect summed over the whole range is at
most `1/2`. -/
def expo (N : ℕ) : ℕ := 2 * Nat.log 2 N + 2

/-- The truncation exponent `expo N` is nonzero. -/
theorem expo_ne_zero (N : ℕ) : expo N ≠ 0 := by simp [expo]

/-- **The squarefree-part splitting** `k = b²·a` with `a` squarefree, as a function of `k`. Only
its defining property `Gap212.Sieve.sqSplit_spec` is used. -/
noncomputable def sqSplit (k : ℕ) : ℕ × ℕ :=
  ((Nat.sq_mul_squarefree k).choose, (Nat.sq_mul_squarefree k).choose_spec.choose)

/-- `sqSplit k = (a, b)` satisfies `b² · a = k` with `a` squarefree. -/
theorem sqSplit_spec (k : ℕ) :
    (sqSplit k).2 ^ 2 * (sqSplit k).1 = k ∧ Squarefree (sqSplit k).1 :=
  (Nat.sq_mul_squarefree k).choose_spec.choose_spec

/-- The squarefree integers `1 ≤ n ≤ N` coprime to `W`: the base points of the pair sum. -/
def sqfreeBase (W N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => Nat.Coprime W n ∧ Squarefree n)

/-- The integers reached by the pair sum: the products `n·m` with `n ∈ sqfreeBase W N` and
`m ∣ n^{expo N}`. Every `k ≤ N` coprime to `W` is reached, with `n = rad k`
(`Gap212.Sieve.filter_le_reach_eq`), and every element has radical at most `N`. -/
def reach (W N : ℕ) : Finset ℕ :=
  ((sqfreeBase W N).sigma fun n => (n ^ expo N).divisors).image fun x => x.1 * x.2

/-- Membership in `sqfreeBase W N`: `1 ≤ n ≤ N`, `n` coprime to `W`, and `n` squarefree. -/
theorem mem_sqfreeBase {W N n : ℕ} :
    n ∈ sqfreeBase W N ↔ (1 ≤ n ∧ n ≤ N) ∧ Nat.Coprime W n ∧ Squarefree n := by
  simp only [sqfreeBase, Finset.mem_filter, Finset.mem_Icc]

/-- **The product map is injective on the pair set**, because `n` is recovered as the radical of
the product (`Gap212.Sieve.rad_mul_of_dvd_pow`) and then `m` by cancellation. -/
theorem injOn_reach (W N : ℕ) :
    Set.InjOn (fun x : (_ : ℕ) × ℕ => x.1 * x.2)
      ((sqfreeBase W N).sigma fun n => (n ^ expo N).divisors) := by
  rintro ⟨n, m⟩ hx ⟨n', m'⟩ hy (hxy : n * m = n' * m')
  simp only [Finset.mem_coe, Finset.mem_sigma, mem_sqfreeBase, Nat.mem_divisors] at hx hy
  obtain ⟨⟨-, -, hn⟩, hmd, hJ⟩ := hx
  obtain ⟨⟨-, -, hn'⟩, hmd', hJ'⟩ := hy
  obtain rfl : n = n' := by
    rw [← rad_mul_of_dvd_pow hn (expo_ne_zero N) (ne_zero_of_dvd_ne_zero hJ hmd) hmd,
      ← rad_mul_of_dvd_pow hn' (expo_ne_zero N) (ne_zero_of_dvd_ne_zero hJ' hmd') hmd', hxy]
  rw [Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn.ne_zero) hxy]

/-- **The pair sum is a reciprocal sum over `reach W N`.** -/
theorem sum_pairs_eq_sum_reach (W N : ℕ) :
    (∑ n ∈ sqfreeBase W N, ∑ m ∈ (n ^ expo N).divisors, (1 : ℝ) / ((n : ℝ) * (m : ℝ)))
      = ∑ k ∈ reach W N, (1 : ℝ) / k := by
  rw [Finset.sum_sigma', reach,
    Finset.sum_image (f := fun k : ℕ => (1 : ℝ) / k) (injOn_reach W N)]
  exact Finset.sum_congr rfl fun _ _ => by push_cast; ring

/-- Structure of the reached integers: each is positive, has radical at most `N`, is coprime to
`W`, and is at most `N^{expo N + 1}`. -/
theorem reach_props {W N k : ℕ} (hk : k ∈ reach W N) :
    1 ≤ k ∧ rad k ≤ N ∧ Nat.Coprime W k ∧ k ≤ N ^ (expo N + 1) := by
  simp only [reach, Finset.mem_image, Finset.mem_sigma, mem_sqfreeBase, Nat.mem_divisors] at hk
  obtain ⟨⟨n, m⟩, ⟨⟨⟨hn1, hnN⟩, hnW, hnsf⟩, hmd, hJ⟩, rfl⟩ := hk
  have hm0 := ne_zero_of_dvd_ne_zero hJ hmd
  refine ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), ?_,
    coprime_mul_of_dvd_pow hmd hnW, ?_⟩
  · rw [rad_mul_of_dvd_pow hnsf (expo_ne_zero N) hm0 hmd]
    exact hnN
  · rw [pow_succ']
    exact Nat.mul_le_mul hnN
      ((Nat.le_of_dvd (by positivity) hmd).trans (Nat.pow_le_pow_left hnN _))

/-- **The part of `reach W N` below `N` is exactly the coprime range.** One inclusion is
`Gap212.Sieve.reach_props`; the other sends `k` to the pair `(rad k, k / rad k)`, legitimate
because `k ∣ (rad k)^{expo N}` for `k ≤ N` (`Gap212.Sieve.dvd_rad_pow`). -/
theorem filter_le_reach_eq {W N : ℕ} :
    (reach W N).filter (fun k => k ≤ N) = (Finset.Icc 1 N).filter fun k => Nat.Coprime W k := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun ⟨hk, hkN⟩ => ⟨⟨(reach_props hk).1, hkN⟩, (reach_props hk).2.2.1⟩
  rintro ⟨⟨hk1, hkN⟩, hcop⟩
  have hk0 : k ≠ 0 := by omega
  have hrd := rad_dvd k
  have hkdvd : k ∣ rad k ^ expo N :=
    dvd_rad_pow hk0 ((Nat.log_mono_right hkN).trans (by rw [expo]; omega))
  refine ⟨Finset.mem_image.mpr ⟨⟨rad k, k / rad k⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩,
    Nat.mul_div_cancel' hrd⟩, hkN⟩
  · exact mem_sqfreeBase.mpr ⟨⟨rad_pos k, (rad_le hk0).trans hkN⟩, hcop.coprime_dvd_right hrd,
      squarefree_rad k⟩
  · exact Nat.mem_divisors.mpr ⟨(Nat.div_dvd_of_dvd hrd).trans hkdvd, pow_ne_zero _ (rad_pos k).ne'⟩

/-- **The excess is at most `9`, absolutely.** Each reached `k > N` is `b²a` with `a` squarefree,
so `a ∣ rad k ≤ N` and `b ≥ 2`, and `k > N` confines `a` to `(N/b², N]`. -/
theorem sum_filter_gt_reach_le {W N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ (reach W N).filter (fun k => N < k), (1 : ℝ) / k ≤ 9 := by
  set B := N ^ (expo N + 1)
  set g : ℕ → ℕ × ℕ := fun k => ((sqSplit k).2, (sqSplit k).1) with hg
  have hmem : ∀ k ∈ (reach W N).filter (fun k => N < k),
      g k ∈ ((Finset.Icc 2 B) ×ˢ (Finset.Icc 1 N)).filter
        (fun q => N < q.2 * q.1 ^ 2) := by
    intro k hk
    obtain ⟨hkr, hkN⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1, hrad, -, hkB⟩ := reach_props hkr
    obtain ⟨hsplit, hsf⟩ := sqSplit_spec k
    set a := (sqSplit k).1
    set b := (sqSplit k).2
    have hk0 : k ≠ 0 := by omega
    have ha0 : a ≠ 0 := by
      intro h; rw [h, mul_zero] at hsplit; omega
    have hb0 : b ≠ 0 := by
      intro h; simp [h] at hsplit; omega
    -- `a ∣ rad k`, hence `a ≤ N`
    have haN : a ≤ N := (Nat.le_of_dvd (rad_pos k)
      (dvd_rad_of_squarefree hsf (Dvd.intro_left _ hsplit) hk0)).trans hrad
    -- `b ≥ 2`, else `k` would be squarefree and equal to its radical
    have hb2 : 2 ≤ b := by
      by_contra h
      rw [show b = 1 by omega, one_pow, one_mul] at hsplit
      have := rad_eq_self (hsplit ▸ hsf)
      omega
    have hbB : b ≤ B := (Nat.le_self_pow two_ne_zero b).trans
      ((Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero ha0)).trans (hsplit.trans_le hkB))
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, hg]
    exact ⟨⟨⟨hb2, hbB⟩, Nat.one_le_iff_ne_zero.mpr ha0, haN⟩, by rw [mul_comm, hsplit]; exact hkN⟩
  have hinj : Set.InjOn g ↑((reach W N).filter (fun k => N < k)) := by
    intro k _ k' _ h
    simp only [hg, Prod.mk.injEq] at h
    rw [← (sqSplit_spec k).1, ← (sqSplit_spec k').1, h.1, h.2]
  calc ∑ k ∈ (reach W N).filter (fun k => N < k), (1 : ℝ) / k
      = ∑ q ∈ ((reach W N).filter (fun k => N < k)).image g,
          (1 : ℝ) / ((q.2 : ℝ) * (q.1 : ℝ) ^ 2) := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hs : (((sqSplit k).2 ^ 2 * (sqSplit k).1 : ℕ) : ℝ) = k :=
          mod_cast (sqSplit_spec k).1
        push_cast at hs
        rw [← hs, mul_comm]
    _ ≤ ∑ q ∈ (Finset.Icc 2 B) ×ˢ (Finset.Icc 1 N) with N < q.2 * q.1 ^ 2,
          (1 : ℝ) / ((q.2 : ℝ) * (q.1 : ℝ) ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmem)
          (fun q _ _ => by positivity)
    _ ≤ 9 := sum_excess_pairs_le hN

/-! ## The truncation defect, and the sandwich -/

/-- For `n ≠ 0`, `n` has at most `n` distinct prime factors. -/
theorem card_primeFactors_le {n : ℕ} (hn : n ≠ 0) : #n.primeFactors ≤ n := by
  simpa using Finset.card_le_card (t := Finset.Icc 1 n) fun p hp => Finset.mem_Icc.mpr
    ⟨(Nat.prime_of_mem_primeFactors hp).pos,
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_primeFactors hp)⟩

/-- **The total truncation defect is at most `1/2`.** Each term is at most
`ω(n)·2^{-(J+1)} ≤ N·2^{-(J+1)}` and there are at most `N` of them, and `J + 1 = 2⌊log₂N⌋ + 3`
makes `N²·2^{-(J+1)} ≤ 1/2` because `N < 2^{⌊log₂N⌋+1}`. -/
theorem sum_defect_le {W N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ sqfreeBase W N, (1 - geomDefect n (expo N)) * (1 / (n.totient : ℝ)) ≤ 1 / 2 := by
  have hterm : ∀ n ∈ sqfreeBase W N,
      (1 - geomDefect n (expo N)) * (1 / (n.totient : ℝ))
        ≤ (N : ℝ) * (2 : ℝ)⁻¹ ^ (expo N + 1) := by
    intro n hn
    obtain ⟨⟨hn1, hnN⟩, -, -⟩ := mem_sqfreeBase.mp hn
    have hphi : (1 : ℝ) ≤ n.totient := Nat.one_le_cast.mpr (Nat.totient_pos.mpr (by omega))
    have hcard : (#n.primeFactors : ℝ) ≤ N :=
      mod_cast (card_primeFactors_le (by omega)).trans hnN
    calc (1 - geomDefect n (expo N)) * (1 / (n.totient : ℝ))
        ≤ 1 - geomDefect n (expo N) :=
          mul_le_of_le_one_right (by linarith [geomDefect_le_one n (expo N)])
            (div_le_one_of_le₀ hphi (by positivity))
      _ ≤ (#n.primeFactors : ℝ) * (2 : ℝ)⁻¹ ^ (expo N + 1) := one_sub_geomDefect_le n (expo N)
      _ ≤ (N : ℝ) * (2 : ℝ)⁻¹ ^ (expo N + 1) := by gcongr
  have hcard : (#(sqfreeBase W N) : ℝ) ≤ N :=
    mod_cast (Finset.card_filter_le _ _).trans (by simp)
  -- `2^{-(expo N + 1)} = (2^{-(L+1)})² / 2` and `N < 2^{L+1}`, with `L = ⌊log₂ N⌋`
  have he : (2 : ℝ)⁻¹ ^ (expo N + 1) = ((2 : ℝ)⁻¹ ^ (Nat.log 2 N + 1)) ^ 2 * 2⁻¹ := by
    rw [← pow_mul, ← pow_succ, expo]
    ring_nf
  have hNY : (N : ℝ) * (2 : ℝ)⁻¹ ^ (Nat.log 2 N + 1) ≤ 1 := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact_mod_cast (Nat.lt_pow_succ_log_self one_lt_two N).le
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_right hcard (by positivity)).trans ?_
  rw [he]
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N)
    (by positivity : (0 : ℝ) ≤ 2⁻¹ ^ (Nat.log 2 N + 1))]

/-- The weight is supported on squarefree integers, where it is `1/φ`. -/
theorem sum_moebiusSq_eq_sum_sqfreeBase (W N : ℕ) :
    (∑ e ∈ Finset.Icc 1 N with Nat.Coprime W e, ((μ e : ℝ) ^ 2 / (e.totient : ℝ)))
      = ∑ n ∈ sqfreeBase W N, (1 : ℝ) / (n.totient : ℝ) := by
  rw [sqfreeBase, ← Finset.filter_filter, Finset.sum_filter (p := Squarefree)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
  split_ifs <;> simp

/-- The dependency's coprime reciprocal sum at an integer cutoff, with the coprimality written as
`(W, e) = 1`. -/
theorem coprimeReciprocalSum_eq (W N : ℕ) :
    PrimeGaps.coprimeReciprocalSum W (N : ℝ)
      = ∑ k ∈ Finset.Icc 1 N with Nat.Coprime W k, (1 : ℝ) / k := by
  rw [PrimeGaps.coprimeReciprocalSum, Nat.floor_natCast]
  refine Finset.sum_congr (Finset.filter_congr fun k _ => ?_) fun _ _ => rfl
  exact ⟨Nat.Coprime.symm, Nat.Coprime.symm⟩

/-- **The sandwich.** The `μ²/φ`-weighted sum over `e ≤ N` coprime to `W` exceeds the coprime
harmonic sum over the same range, by at most the absolute constant `10`. The lower bound is that
every `k ≤ N` coprime to `W` is reached by the pair sum; the upper bound is the excess bound plus
the truncation defect. -/
theorem sum_moebiusSq_div_totient_sub_coprimeReciprocal {W N : ℕ} (hN : 1 ≤ N) :
    (∑ k ∈ Finset.Icc 1 N with Nat.Coprime W k, (1 : ℝ) / k)
        ≤ ∑ e ∈ Finset.Icc 1 N with Nat.Coprime W e, ((μ e : ℝ) ^ 2 / (e.totient : ℝ))
      ∧ (∑ e ∈ Finset.Icc 1 N with Nat.Coprime W e, ((μ e : ℝ) ^ 2 / (e.totient : ℝ)))
        ≤ (∑ k ∈ Finset.Icc 1 N with Nat.Coprime W k, (1 : ℝ) / k) + 10 := by
  -- the weighted sum minus the pair sum is the truncation defect
  have hAP : ∑ e ∈ Finset.Icc 1 N with Nat.Coprime W e, ((μ e : ℝ) ^ 2 / (e.totient : ℝ))
        - ∑ k ∈ reach W N, (1 : ℝ) / k
      = ∑ n ∈ sqfreeBase W N, (1 - geomDefect n (expo N)) * (1 / (n.totient : ℝ)) := by
    rw [sum_moebiusSq_eq_sum_sqfreeBase, ← sum_pairs_eq_sum_reach, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨⟨hn1, -⟩, -, hsf⟩ := mem_sqfreeBase.mp hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hphi0 : (n.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hn1).ne'
    simp only [← one_div_mul_one_div, ← Finset.mul_sum, sum_inv_divisors_pow hsf (expo_ne_zero N)]
    field_simp
  have hdef_lo : 0 ≤ ∑ n ∈ sqfreeBase W N, (1 - geomDefect n (expo N)) * (1 / (n.totient : ℝ)) :=
    Finset.sum_nonneg fun n _ =>
      mul_nonneg (sub_nonneg.mpr (geomDefect_le_one n (expo N))) (by positivity)
  -- the pair sum is a reciprocal sum over `reach`, split at `N`
  have hsplit := Finset.sum_filter_add_sum_filter_not (reach W N) (· ≤ N) fun k => (1 : ℝ) / k
  simp only [not_le] at hsplit
  rw [filter_le_reach_eq] at hsplit
  have hEpos : 0 ≤ ∑ k ∈ (reach W N).filter (fun k => N < k), (1 : ℝ) / k :=
    Finset.sum_nonneg fun k _ => by positivity
  constructor <;> linarith [sum_filter_gt_reach_le (W := W) hN, sum_defect_le (W := W) hN]

/-! ## The asymptotic -/

/-- **The Mertens asymptotic for the weight `μ²/φ` over a coprimality class.** For every squarefree
`W ≥ 1` and every `N ≥ 1`,

  `∑_{e ≤ N, (W,e)=1} μ²(e)/φ(e) = (φ(W)/W)(log N + γ + ℓ_W) + O(1 + τ(W)/N)`,

with `ℓ_W = PrimeGaps.ellV W = ∑_{p ∣ W} log p/(p-1)` and an **absolute** constant. The prefactor
is exactly `φ(W)/W`: no correction factor, because the local factor of the weight at `p ∤ W` is
`(1 + 1/(p-1))(1 - 1/p) = 1`.

The hypotheses are `1 ≤ W`, `Squarefree W` and `1 ≤ N`; in the application `W = W(x)` is a
primorial and `N = B(x) ≥ x^β`. The error term is needed: at `W` the primorial of `⌊N⌋` the left
side is exactly `1` while `(φ(W)/W) log N ≈ e^{-γ}`. -/
@[gap212 "lem_moebius_sq_totient_asymptotic"]
theorem sum_moebiusSq_div_totient_coprime :
    ∃ C : ℝ, 0 < C ∧ ∀ W : ℕ, 1 ≤ W → Squarefree W → ∀ N : ℕ, 1 ≤ N →
      |(∑ e ∈ Finset.Icc 1 N with Nat.Coprime W e, ((μ e : ℝ) ^ 2 / (e.totient : ℝ)))
          - (W.totient : ℝ) / (W : ℝ)
            * (Real.log N + Real.eulerMascheroniConstant + PrimeGaps.ellV W)|
        ≤ C * (1 + (#W.divisors : ℝ) / N) := by
  obtain ⟨C₀, hC₀, h⟩ := PrimeGaps.coprime_reciprocal_sum_asymptotic
  refine ⟨C₀ + 10, by linarith, fun W hW1 hWsf N hN => ?_⟩
  have hharm := h W hW1 hWsf N (by exact_mod_cast hN)
  rw [coprimeReciprocalSum_eq] at hharm
  obtain ⟨hlow, hhigh⟩ := sum_moebiusSq_div_totient_sub_coprimeReciprocal (W := W) hN
  have ht : (0 : ℝ) ≤ (#W.divisors : ℝ) / N := by positivity
  rw [abs_le] at hharm ⊢
  constructor <;> linarith

/-- **The asymptotic in the form `(φ(W)/W)·(log N + O_W(1))`**, with the `O_W(1)` explicit. Its size
is polynomial in `W/φ(W)`, `τ(W)` and `ℓ_W`, all of which are `(log log x)^{O(1)}` at `W = W(x)`,
so it is `o(log y)` for `log y ≍ β log x`. -/
@[gap212 "lem_moebius_sq_totient_asymptotic"]
theorem sum_moebiusSq_div_totient_coprime_log {W : ℕ} (hW1 : 1 ≤ W) (hWsf : Squarefree W) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑ e ∈ Finset.Icc 1 N with Nat.Coprime W e, ((μ e : ℝ) ^ 2 / (e.totient : ℝ)))
          - (W.totient : ℝ) / (W : ℝ) * Real.log N|
        ≤ (W.totient : ℝ) / (W : ℝ) * D := by
  obtain ⟨C, hC, h⟩ := sum_moebiusSq_div_totient_coprime
  have hr : (0 : ℝ) < W.totient / W :=
    div_pos (Nat.cast_pos.mpr (Nat.totient_pos.mpr hW1)) (Nat.cast_pos.mpr hW1)
  refine ⟨(W : ℝ) / (W.totient : ℝ) * (C * (1 + (#W.divisors : ℝ)))
      + |Real.eulerMascheroniConstant + PrimeGaps.ellV W|, by positivity, fun N hN => ?_⟩
  have hkey := abs_le.mp (h W hW1 hWsf N hN)
  have hc := abs_le.mp (le_refl |Real.eulerMascheroniConstant + PrimeGaps.ellV W|)
  have hdiv : C * (1 + (#W.divisors : ℝ) / N) ≤ C * (1 + #W.divisors) := by
    gcongr
    exact div_le_self (by positivity) (by exact_mod_cast hN)
  have hrr : (W.totient : ℝ) / W * (W / W.totient * (C * (1 + (#W.divisors : ℝ))))
      = C * (1 + #W.divisors) := by
    field_simp
  rw [abs_le]
  constructor <;>
    linarith [mul_le_mul_of_nonneg_left hc.1 hr.le, mul_le_mul_of_nonneg_left hc.2 hr.le]

/-- `ℓ_V = ∑_{p ∣ V} log p/(p-1) ≤ log V` for `V ≥ 1`. -/
theorem ellV_le_log {V : ℕ} (hV : 1 ≤ V) : PrimeGaps.ellV V ≤ Real.log V := by
  have h2 : ∀ p ∈ V.primeFactors, (2 : ℝ) ≤ p := fun p hp ↦ by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  calc PrimeGaps.ellV V ≤ ∑ p ∈ V.primeFactors, Real.log p := by
        refine Finset.sum_le_sum fun p hp ↦ ?_
        have := h2 p hp
        rw [div_le_iff₀ (by linarith)]
        nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ p)]
    _ = Real.log ((∏ p ∈ V.primeFactors, p : ℕ) : ℝ) := by
        rw [Nat.cast_prod, Real.log_prod]
        exact fun p hp ↦ (by linarith [h2 p hp] : (0 : ℝ) < p).ne'
    _ ≤ Real.log V := Real.log_le_log
        (by exact_mod_cast Finset.prod_pos fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).pos)
        (by exact_mod_cast Nat.le_of_dvd hV (Nat.prod_primeFactors_dvd V))

end Gap212.Sieve
