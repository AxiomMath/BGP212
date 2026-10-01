/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.DivisorSumFacts
public import Gap212.Sieve.GramDatum
public import Gap212.Sieve.GramRiemannSum
public import Gap212.Sieve.MertensMoebiusSq
public import Gap212.Sieve.MoebiusTotientAsymptotic
public import Mathlib.NumberTheory.EulerProduct.Basic
public meta import Gap212.Attr

/-!
# The Mertens asymptotic for the totient Gram kernel `μ²/(μ*φ)`

For `W ≥ 2` **even** and squarefree and every `N ≥ 1`,

  `∑_{e ≤ N, (W,e)=1} μ²(e)/(μ*φ)(e)
      = (φ(W)/W)·(∏_{p ∤ W}(1 - 1/(p-1)²))^{-1}·\log N + O(τ(W) + ℓ_W)`

(`Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime`). This is the counting-measure half of the
two inputs of `Gap212.Sieve.totientGramSumLimitOfSupport_iff`; the other is the average evaluation
of `ρ_F`.

The error constant is absolute and its `W`-dependence is explicit, so that the asymptotic can be
read at the growing modulus `W = W(x)` and divided by `\log x`; with `W(x) ≤ (\log\log x)²`
(`Gap212.Sieve.W_le_log_log_sq`) the error `τ(W) + ℓ_W` is `o(\log x)`. The fixed-modulus form
`∀ W, ∃ D, ∀ N` is derived as
`Gap212.Sieve.exists_bound_sum_moebiusSq_div_moebiusTotient_coprime`.

## The constant, and why it is not the reciprocal kernel's

The local factor of this weight at `p ∤ W` is

  `1 + 1/(p(p-2)) = (p-1)²/(p(p-2)) = (1 - 1/(p-1)²)^{-1}`,

which is not `1` (`Gap212.Sieve.local_factor_mul_corr`), whereas the corresponding factor for
`μ²/φ` is exactly `1`. Hence the inverse of the prime product
`∏' p, if p.Prime ∧ ¬ p ∣ W then 1 - 1/(p-1)² else 1`, which
`Gap212.Sieve.tendsto_inv_tprod_corr_W` drives to `1`, appears in the constant.

## The route: an exact reduction to the reciprocal kernel

For odd squarefree `e`, `(μ*φ)(e) = ∏_{p ∣ e}(p-2)` and `1/(p-2) = 1/((p-1)(p-2)) + 1/(p-1)`, so

  `μ²/(μ*φ) = (μ²/(φ·(μ*φ))) ⊛ (μ²/φ)`

over **coprime** factorizations (`Gap212.Sieve.muPhiWeight_eq_tail_mul_totientWeight`). Summing
over `e ≤ N` coprime to `W` and grouping by the first coordinate gives the **exact** identity

  `∑_{e≤N,(e,W)=1}μ²(e)/(μ*φ)(e)
     = ∑_{d≤N,(d,W)=1}(μ²(d)/(φ(d)(μ*φ)(d)))·∑_{m≤N/d,(m,Wd)=1}μ²(m)/φ(m)`

(`Gap212.Sieve.sum_muPhiWeight_eq_sum_tail`), with no error term. The coprimality of the
factorization is enforced by taking the inner modulus to be `Wd` rather than `W`, so that the inner
sum is the `μ²/φ` asymptotic at modulus `Wd`. The outer sum then
converges absolutely, so the main terms assemble into `(φ(W)/W)·K_W·\log N` with

  `K_W = ∑_{(d,W)=1}(μ²(d)/(φ(d)(μ*φ)(d)))·(φ(d)/d) = ∏_{p∤W}(1 + 1/(p(p-2)))`,

and that Euler product is the inverse of the correction product
(`Gap212.Sieve.tsum_constTerm_eq_inv_tprod_corr`).

## Where convergence comes from, elementarily

Everything needed about the outer sum is one criterion:
`Gap212.Sieve.summable_prod_primeFactors` — if `a p ≥ 0` is summable then
`∑_{n squarefree}∏_{p ∣ n}a p` converges, because a finite set of squarefree integers injects into
the powerset of the primes it involves and `∏(1 + a p) ≤ \exp(∑ a p)`. Applied at
`a p = 4√p/((p-1)(p-2))` it gives one majorant (`Gap212.Sieve.muPhiTailBound`) dominating the tail
kernel against every weight needed: `1`, `1 + \log d`, `√d`, and `τ(d)√d`
(`Gap212.Sieve.muPhiTail_mul_weight_le`).

## Where evenness of `W` is used

* Every `e` in the sum is odd, which the summand *requires*: `(μ*φ)(2) = 0`, so the local identity
  `1/((p-1)(p-2)) + 1/(p-1) = 1/(p-2)` fails at `p = 2` (left side `1`, right side `0`) and the
  convolution above is false on even `e`.
* The correction product's factor at `p = 2` is `1 - 1/(2-1)² = 0`. For odd `W` it survives, the
  product is `0`, and the asserted inverse is meaningless. Evenness keeps `p = 2` out.

`W(x)` is an even primorial.

## Main definitions

* `Gap212.Sieve.muPhiWeight`, `Gap212.Sieve.totientWeight`, `Gap212.Sieve.muPhiTail`: the kernels
  `μ²/(μ*φ)`, `μ²/φ` and `μ²/(φ·(μ*φ))`, as multiplicative arithmetic functions.
* `Gap212.Sieve.tailPairs`: the coprime factorization pairs the reindexing runs over.
* `Gap212.Sieve.constTerm`, `Gap212.Sieve.muPhiTailBound`: the summand of the constant, and the
  majorant that makes every series in the file converge.

## Main results

* `Gap212.Sieve.summable_prod_primeFactors`: the elementary summability criterion.
* `Gap212.Sieve.muPhiWeight_eq_tail_mul_totientWeight`: the convolution, on odd squarefree `e`.
* `Gap212.Sieve.sum_muPhiWeight_eq_sum_tail`: the exact reduction to the reciprocal kernel.
* `Gap212.Sieve.tsum_constTerm_eq_inv_tprod_corr`: the constant is the inverse correction product.
* `Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime`: the asymptotic, with one absolute
  error constant for every modulus, and
  `Gap212.Sieve.exists_bound_sum_moebiusSq_div_moebiusTotient_coprime` the fixed-modulus reading
  derived from it.
-/

@[expose] public section

open Finset ArithmeticFunction

namespace Gap212.Sieve

open scoped ArithmeticFunction.Moebius

/-! ## The three kernels -/

/-- `μ*φ` is multiplicative: `moebiusTotient (m * n) = moebiusTotient m * moebiusTotient n` for
coprime `m` and `n`. -/
theorem moebiusTotient_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    moebiusTotient (m * n) = moebiusTotient m * moebiusTotient n := by
  simpa [muPhiAF_apply] using isMultiplicative_muPhiAF.map_mul_of_coprime h

/-- `μ(mn)² = μ(m)²·μ(n)²` in `ℝ` for coprime `m` and `n`. -/
theorem moebiusSq_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    ((μ (m * n) : ℝ)) ^ 2 = ((μ m : ℝ)) ^ 2 * ((μ n : ℝ)) ^ 2 := by
  rw [isMultiplicative_moebius.map_mul_of_coprime h, Int.cast_mul, mul_pow]

/-- **The weight of the totient Gram kernel**, `μ²(e)/(μ*φ)(e)`. -/
noncomputable def muPhiWeight : ArithmeticFunction ℝ :=
  ⟨fun e => (μ e : ℝ) ^ 2 / moebiusTotient e, by simp⟩

/-- **The weight of the reciprocal Gram kernel**, `μ²(e)/φ(e)`. -/
noncomputable def totientWeight : ArithmeticFunction ℝ :=
  ⟨fun e => (μ e : ℝ) ^ 2 / (e.totient : ℝ), by simp⟩

/-- **The tail kernel**, `μ²(d)/(φ(d)(μ*φ)(d))`. -/
noncomputable def muPhiTail : ArithmeticFunction ℝ :=
  ⟨fun d => (μ d : ℝ) ^ 2 / ((d.totient : ℝ) * moebiusTotient d), by simp⟩

/-- `muPhiWeight e = μ(e)²/(μ*φ)(e)`. -/
theorem muPhiWeight_apply (e : ℕ) : muPhiWeight e = (μ e : ℝ) ^ 2 / moebiusTotient e := rfl

/-- `totientWeight e = μ(e)²/φ(e)`. -/
theorem totientWeight_apply (e : ℕ) : totientWeight e = (μ e : ℝ) ^ 2 / (e.totient : ℝ) := rfl

/-- `muPhiTail d = μ(d)²/(φ(d)·(μ*φ)(d))`. -/
theorem muPhiTail_apply (d : ℕ) :
    muPhiTail d = (μ d : ℝ) ^ 2 / ((d.totient : ℝ) * moebiusTotient d) := rfl

/-- The kernel `μ²/(μ*φ)` is multiplicative. -/
theorem isMultiplicative_muPhiWeight : muPhiWeight.IsMultiplicative := by
  refine ⟨by simp [muPhiWeight_apply, moebiusTotient_one], fun {m n} h => ?_⟩
  simp only [muPhiWeight_apply]
  rw [moebiusSq_mul_of_coprime h, moebiusTotient_mul_of_coprime h, div_mul_div_comm]

/-- The kernel `μ²/φ` is multiplicative. -/
theorem isMultiplicative_totientWeight : totientWeight.IsMultiplicative := by
  refine ⟨by simp [totientWeight_apply], fun {m n} h => ?_⟩
  simp only [totientWeight_apply]
  rw [moebiusSq_mul_of_coprime h, Nat.totient_mul h, div_mul_div_comm]
  push_cast
  ring

/-- The kernel `μ²/(φ·(μ*φ))` is multiplicative. -/
theorem isMultiplicative_muPhiTail : muPhiTail.IsMultiplicative := by
  refine ⟨by simp [muPhiTail_apply, moebiusTotient_one], fun {m n} h => ?_⟩
  simp only [muPhiTail_apply]
  rw [moebiusSq_mul_of_coprime h, moebiusTotient_mul_of_coprime h, Nat.totient_mul h,
    div_mul_div_comm]
  push_cast
  ring

/-! ## Values at a prime -/

/-- At a prime `p`, `muPhiWeight p = 1/(p-2)`. -/
theorem muPhiWeight_prime {p : ℕ} (hp : p.Prime) : muPhiWeight p = 1 / ((p : ℝ) - 2) := by
  rw [muPhiWeight_apply, moebiusTotient_prime hp, moebius_apply_prime hp]
  push_cast
  ring

/-- At a prime `p`, `totientWeight p = 1/(p-1)`. -/
theorem totientWeight_prime {p : ℕ} (hp : p.Prime) : totientWeight p = 1 / ((p : ℝ) - 1) := by
  rw [totientWeight_apply, Nat.totient_prime hp, moebius_apply_prime hp, Nat.cast_pred hp.pos]
  push_cast
  ring

/-- At a prime `p`, `muPhiTail p = 1/((p-1)(p-2))`. -/
theorem muPhiTail_prime {p : ℕ} (hp : p.Prime) :
    muPhiTail p = 1 / (((p : ℝ) - 1) * ((p : ℝ) - 2)) := by
  rw [muPhiTail_apply, moebiusTotient_prime hp, Nat.totient_prime hp, moebius_apply_prime hp,
    Nat.cast_pred hp.pos]
  push_cast
  ring

/-- **The local factor of the convolution.** At an odd prime,
`1/((p-1)(p-2)) + 1/(p-1) = 1/(p-2)`: the tail kernel and the reciprocal kernel add up to the
totient kernel. This fails at `p = 2`, where the left side is `0 + 1 = 1` and the right is `0`. -/
theorem muPhiTail_add_totientWeight {p : ℕ} (hp : 3 ≤ p) :
    1 / (((p : ℝ) - 1) * ((p : ℝ) - 2)) + 1 / ((p : ℝ) - 1) = 1 / ((p : ℝ) - 2) := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2 : (p : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- **The convolution identity at a prime.** For an odd prime `p`,
`(muPhiTail * totientWeight) p = muPhiWeight p`. -/
theorem mul_apply_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (muPhiTail * totientWeight) p = muPhiWeight p := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (f := fun a b => muPhiTail a * totientWeight b),
    hp.divisors, Finset.sum_insert (by simpa using Ne.symm hp.ne_one), Finset.sum_singleton,
    Nat.div_one, Nat.div_self hp.pos, isMultiplicative_muPhiTail.map_one,
    isMultiplicative_totientWeight.map_one, one_mul, mul_one, muPhiTail_prime hp,
    totientWeight_prime hp, muPhiWeight_prime hp, add_comm]
  exact muPhiTail_add_totientWeight (hp.two_le.lt_of_ne' hp2)

/-- **The convolution identity.** On an odd squarefree `e`,
`μ²(e)/(μ*φ)(e) = ∑_{d ∣ e} (μ²(d)/(φ(d)(μ*φ)(d)))·(μ²(e/d)/φ(e/d))`.

Both sides are multiplicative, so this reduces to the local identity
`Gap212.Sieve.muPhiTail_add_totientWeight` at each prime dividing `e`. Oddness is needed: at
`p = 2` the local identity fails. -/
theorem muPhiWeight_eq_tail_mul_totientWeight {e : ℕ} (hsf : Squarefree e) (hodd : ¬ 2 ∣ e) :
    muPhiWeight e = (muPhiTail * totientWeight) e := by
  rw [← isMultiplicative_muPhiWeight.prod_primeFactors hsf,
    ← (isMultiplicative_muPhiTail.mul isMultiplicative_totientWeight).prod_primeFactors hsf]
  exact Finset.prod_congr rfl fun p hp => (mul_apply_prime (Nat.prime_of_mem_primeFactors hp)
    fun h => hodd (h ▸ Nat.dvd_of_mem_primeFactors hp)).symm

/-! ## A summability criterion for squarefree-supported multiplicative weights -/

/-- **Summability of a squarefree-supported multiplicative function from summability of its local
factors.** If `a p ≥ 0` and `∑_p a p` converges then `∑_{n squarefree}∏_{p ∣ n}a p` converges, with
the bound `exp(∑_p a p)`.

Partial sums are bounded and the summand is non-negative, which is all that
`summable_of_sum_le` needs. A finite set of squarefree integers injects into the powerset of the
primes it involves — a squarefree number *is* the product of its prime factors — and
`∏_{p ∈ P}(1 + a p) = ∑_{S ⊆ P}∏_{p ∈ S}a p` by `Finset.prod_add`, with
`∏(1 + a p) ≤ ∏\exp(a p) = \exp(∑ a p)`. -/
theorem summable_prod_primeFactors {a : ℕ → ℝ} (ha0 : ∀ p, 0 ≤ a p) (ha : Summable a) :
    Summable fun n : ℕ => if Squarefree n then ∏ p ∈ n.primeFactors, a p else 0 := by
  classical
  refine summable_of_sum_le (c := Real.exp (∑' p, a p)) (fun n => ?_) fun T => ?_
  · exact ite_nonneg (Finset.prod_nonneg fun p _ => ha0 p) le_rfl
  · have hinj : Set.InjOn Nat.primeFactors ↑(T.filter Squarefree) := by
      intro m hm n hn h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hm hn
      rw [← Nat.prod_primeFactors_of_squarefree hm.2, ← Nat.prod_primeFactors_of_squarefree hn.2, h]
    calc ∑ n ∈ T, (if Squarefree n then ∏ p ∈ n.primeFactors, a p else 0)
        = ∑ n ∈ T.filter Squarefree, ∏ p ∈ n.primeFactors, a p :=
          (Finset.sum_filter _ _).symm
      _ = ∑ S ∈ (T.filter Squarefree).image Nat.primeFactors, ∏ p ∈ S, a p :=
          (Finset.sum_image (f := fun S : Finset ℕ => ∏ p ∈ S, a p) hinj).symm
      _ ≤ ∑ S ∈ (T.biUnion Nat.primeFactors).powerset, ∏ p ∈ S, a p := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            fun S _ _ => Finset.prod_nonneg fun p _ => ha0 p
          intro S hS
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hS
          exact Finset.mem_powerset.mpr (Finset.subset_biUnion_of_mem Nat.primeFactors
            (Finset.mem_filter.mp hn).1)
      _ = ∏ p ∈ T.biUnion Nat.primeFactors, (a p + 1) := by
          simp [Finset.prod_add]
      _ ≤ ∏ p ∈ T.biUnion Nat.primeFactors, Real.exp (a p) :=
          Finset.prod_le_prod (fun p _ => by linarith [ha0 p]) fun p _ => Real.add_one_le_exp _
      _ = Real.exp (∑ p ∈ T.biUnion Nat.primeFactors, a p) := (Real.exp_sum _ a).symm
      _ ≤ Real.exp (∑' p, a p) :=
          Real.exp_le_exp.mpr (ha.sum_le_tsum _ fun p _ => ha0 p)

/-! ## The majorant -/

/-- The local factor of the majorant: `4√p/((p-1)(p-2))` at `p ≥ 3`, and `0` below — so the
factor at `p = 2` is `0`, matching the vanishing of `μ²/(φ·(μ*φ))` on even numbers. -/
noncomputable def tailMajorantFactor (p : ℕ) : ℝ :=
  if 3 ≤ p then 4 * Real.sqrt p / (((p : ℝ) - 1) * ((p : ℝ) - 2)) else 0

/-- The local factor of the majorant is non-negative. -/
theorem tailMajorantFactor_nonneg (p : ℕ) : 0 ≤ tailMajorantFactor p := by
  unfold tailMajorantFactor
  split_ifs with h
  · have h3 : (3 : ℝ) ≤ p := by exact_mod_cast h
    exact div_nonneg (by positivity) (by nlinarith)
  · rfl

/-- `4√p/((p-1)(p-2)) ≤ 18/(p√p)`, sharp at `p = 3`: cross-multiplying and using `√p·√p = p`
leaves `0 ≤ 7p² - 27p + 18`, which has its root at `p = 3`. -/
theorem tailMajorantFactor_le {p : ℕ} (hp : 3 ≤ p) :
    tailMajorantFactor p ≤ 18 / ((p : ℝ) * Real.sqrt p) := by
  have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  have hss : Real.sqrt p * Real.sqrt p = (p : ℝ) := Real.mul_self_sqrt (by linarith)
  rw [tailMajorantFactor, if_pos hp, div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith [hss, hs0, h3]

/-- The local factors `tailMajorantFactor p` of the majorant are summable over `p`. -/
theorem summable_tailMajorantFactor : Summable tailMajorantFactor := by
  have hmaj : Summable fun n : ℕ => 18 * (1 / (n : ℝ) ^ ((3 : ℝ) / 2)) :=
    (Real.summable_one_div_nat_rpow.mpr (by norm_num)).mul_left 18
  refine hmaj.of_nonneg_of_le tailMajorantFactor_nonneg fun p => ?_
  by_cases hp : 3 ≤ p
  · rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (Nat.cast_pos.mpr (by omega)),
      Real.rpow_one, ← Real.sqrt_eq_rpow, mul_one_div]
    exact tailMajorantFactor_le hp
  · rw [tailMajorantFactor, if_neg hp]
    positivity

/-- The majorant `∏_{p ∣ d}4√p/((p-1)(p-2))` on squarefree `d`, and `0` elsewhere. It dominates
the tail kernel against every weight this file needs (`Gap212.Sieve.muPhiTail_mul_weight_le`). -/
noncomputable def muPhiTailBound (d : ℕ) : ℝ :=
  if Squarefree d then ∏ p ∈ d.primeFactors, tailMajorantFactor p else 0

/-- The majorant `muPhiTailBound` is summable. -/
theorem summable_muPhiTailBound : Summable muPhiTailBound :=
  summable_prod_primeFactors tailMajorantFactor_nonneg summable_tailMajorantFactor

/-! ## The tail kernel against the majorant -/

/-- On squarefree `d` the tail kernel is `∏_{p ∣ d}1/((p-1)(p-2))`. At `p = 2` that factor is
`1/0 = 0`, so the kernel vanishes on even `d` with no hypothesis needed. -/
theorem muPhiTail_eq_prod {d : ℕ} (hsf : Squarefree d) :
    muPhiTail d = ∏ p ∈ d.primeFactors, 1 / (((p : ℝ) - 1) * ((p : ℝ) - 2)) := by
  rw [← isMultiplicative_muPhiTail.prod_primeFactors hsf]
  exact Finset.prod_congr rfl fun p hp => muPhiTail_prime (Nat.prime_of_mem_primeFactors hp)

/-- The tail kernel vanishes on non-squarefree `d`. -/
theorem muPhiTail_eq_zero_of_not_squarefree {d : ℕ} (hsf : ¬ Squarefree d) : muPhiTail d = 0 := by
  rw [muPhiTail_apply, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
  norm_num

/-- The tail kernel is non-negative. -/
theorem muPhiTail_nonneg (d : ℕ) : 0 ≤ muPhiTail d := by
  by_cases hsf : Squarefree d
  · rw [muPhiTail_eq_prod hsf]
    refine Finset.prod_nonneg fun p hp => ?_
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact div_nonneg zero_le_one (by nlinarith)
  · rw [muPhiTail_eq_zero_of_not_squarefree hsf]

/-- `τ(d) = 2^{ω(d)}` on a squarefree `d`, written as a product over the prime factors. This is
`Gap212.Sieve.card_divisors_of_squarefree` with `Finset.prod_const` run backwards. -/
theorem card_divisors_eq_prod_two {d : ℕ} (hsf : Squarefree d) :
    #d.divisors = ∏ _p ∈ d.primeFactors, 2 := by
  rw [card_divisors_of_squarefree hsf, Finset.prod_const]

/-- On a squarefree `d`, `√d = ∏_{p ∣ d}√p`. -/
theorem sqrt_eq_prod_primeFactors {d : ℕ} (hsf : Squarefree d) :
    Real.sqrt d = ∏ p ∈ d.primeFactors, Real.sqrt p := by
  rw [← Real.sqrt_prod _ fun p _ => Nat.cast_nonneg p, ← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree hsf]

/-- **The tail kernel against its heaviest weight.** `μ²(d)/(φ(d)(μ*φ)(d))·τ(d)·√d ≤` the
majorant, factor by factor: the local factor on the left is `2√p/((p-1)(p-2))`, the majorant's is
`4√p/((p-1)(p-2))`, and at `p = 2` both are `0`. -/
theorem muPhiTail_mul_weight_le (d : ℕ) :
    muPhiTail d * (#d.divisors : ℝ) * Real.sqrt d ≤ muPhiTailBound d := by
  by_cases hsf : Squarefree d
  · rw [muPhiTail_eq_prod hsf, card_divisors_eq_prod_two hsf, sqrt_eq_prod_primeFactors hsf,
      muPhiTailBound, if_pos hsf, Nat.cast_prod, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_
    · have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : (0 : ℝ) ≤ 1 / (((p : ℝ) - 1) * ((p : ℝ) - 2)) := div_nonneg zero_le_one (by nlinarith)
      positivity
    · rcases (Nat.prime_of_mem_primeFactors hp).two_le.eq_or_lt with rfl | h
      · norm_num [tailMajorantFactor]
      · have h3 : (3 : ℝ) ≤ p := by exact_mod_cast h
        rw [tailMajorantFactor, if_pos (show 3 ≤ p from h), Nat.cast_ofNat, one_div_mul_eq_div,
          div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (by linarith [Real.sqrt_nonneg p]) (by nlinarith)
  · simp [muPhiTail_eq_zero_of_not_squarefree hsf, muPhiTailBound, hsf]

/-- The majorant is non-negative. -/
theorem muPhiTailBound_nonneg (d : ℕ) : 0 ≤ muPhiTailBound d :=
  ite_nonneg (Finset.prod_nonneg fun p _ => tailMajorantFactor_nonneg p) le_rfl

/-- `1 + log d ≤ 2√d` for `d ≥ 1`, from `log t ≤ t - 1` at `t = √d`. -/
theorem one_add_log_le_two_mul_sqrt {d : ℕ} (hd : 1 ≤ d) :
    1 + Real.log d ≤ 2 * Real.sqrt d := by
  have hd0 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hs : Real.log (Real.sqrt d) ≤ Real.sqrt d - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith))
  rw [Real.log_sqrt (by linarith)] at hs
  linarith

/-- **One weight at a time.** For `1 ≤ d`, the tail kernel times any weight bounded by `τ(d)√d`
is bounded by the majorant. -/
theorem muPhiTail_mul_le_of_le {d : ℕ} (_hd : 1 ≤ d) {w : ℝ}
    (hw : w ≤ (#d.divisors : ℝ) * Real.sqrt d) : muPhiTail d * w ≤ muPhiTailBound d :=
  (mul_le_mul_of_nonneg_left hw (muPhiTail_nonneg d)).trans
    (by simpa only [mul_assoc] using muPhiTail_mul_weight_le d)

private theorem one_le_card_divisors {d : ℕ} (hd : 1 ≤ d) : (1 : ℝ) ≤ (#d.divisors : ℝ) :=
  Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩)

/-- `1 ≤ τ(d)·√d` for `d ≥ 1`. -/
theorem one_le_card_divisors_mul_sqrt {d : ℕ} (hd : 1 ≤ d) :
    (1 : ℝ) ≤ (#d.divisors : ℝ) * Real.sqrt d :=
  one_le_mul_of_one_le_of_one_le (one_le_card_divisors hd)
    (Real.one_le_sqrt.mpr (by exact_mod_cast hd))

/-- `2√d ≤ τ(d)·√d` for `d ≥ 2`. -/
theorem two_le_card_divisors_mul_sqrt {d : ℕ} (hd : 2 ≤ d) :
    (2 : ℝ) * Real.sqrt d ≤ (#d.divisors : ℝ) * Real.sqrt d := by
  have h : ({1, d} : Finset ℕ) ⊆ d.divisors := Finset.insert_subset
    (Nat.one_mem_divisors.mpr (by omega)) (by simpa using Nat.mem_divisors_self _ (by omega))
  have := Finset.card_le_card h
  rw [Finset.card_pair (by omega)] at this
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) (Real.sqrt_nonneg _)

/-- The tail kernel against the weight `1 + log d` is bounded by the majorant:
`muPhiTail d * (1 + log d) ≤ muPhiTailBound d`. -/
theorem muPhiTail_mul_one_add_log_le (d : ℕ) :
    muPhiTail d * (1 + Real.log d) ≤ muPhiTailBound d := by
  rcases d with _ | _ | d
  · simpa using muPhiTailBound_nonneg 0
  · exact muPhiTail_mul_le_of_le le_rfl (by simp)
  · exact muPhiTail_mul_le_of_le (by omega)
      ((one_add_log_le_two_mul_sqrt (by omega)).trans (two_le_card_divisors_mul_sqrt (by omega)))

/-- The tail kernel is bounded by the majorant: `muPhiTail d ≤ muPhiTailBound d`. -/
theorem muPhiTail_le_bound (d : ℕ) : muPhiTail d ≤ muPhiTailBound d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simpa using muPhiTailBound_nonneg 0
  · simpa using muPhiTail_mul_le_of_le hd (one_le_card_divisors_mul_sqrt hd)

/-- The tail kernel against the weight `√d` is bounded by the majorant:
`muPhiTail d * √d ≤ muPhiTailBound d`. -/
theorem muPhiTail_mul_sqrt_le (d : ℕ) : muPhiTail d * Real.sqrt d ≤ muPhiTailBound d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simpa using muPhiTailBound_nonneg 0
  · exact muPhiTail_mul_le_of_le hd
      (le_mul_of_one_le_left (Real.sqrt_nonneg _) (one_le_card_divisors hd))

/-- The tail kernel `μ²/(φ·(μ*φ))` is summable. -/
theorem summable_muPhiTail : Summable fun d : ℕ => muPhiTail d :=
  summable_muPhiTailBound.of_nonneg_of_le muPhiTail_nonneg muPhiTail_le_bound

/-! ## The constant, and that it is the inverse of the correction product -/

/-- The summand of the constant: `(μ²(d)/(φ(d)(μ*φ)(d)))·(φ(d)/d)` on the `d` coprime to `W`, and
`0` elsewhere. Its Euler factor at `p ∤ W` is `1 + 1/(p(p-2))`. -/
noncomputable def constTerm (W d : ℕ) : ℝ :=
  if Nat.Coprime W d then muPhiTail d * ((d.totient : ℝ) / (d : ℝ)) else 0

/-- `0 ≤ φ(d)/d`. -/
theorem totient_div_nonneg (d : ℕ) : 0 ≤ (d.totient : ℝ) / (d : ℝ) := by positivity

/-- `φ(d)/d ≤ 1`. -/
theorem totient_div_le_one (d : ℕ) : (d.totient : ℝ) / (d : ℝ) ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast Nat.totient_le d) (Nat.cast_nonneg _)

/-- `constTerm W 0 = 0`. -/
theorem constTerm_zero (W : ℕ) : constTerm W 0 = 0 := by
  simp [constTerm]

/-- `constTerm W 1 = 1`. -/
theorem constTerm_one (W : ℕ) : constTerm W 1 = 1 := by
  rw [constTerm, if_pos (Nat.coprime_one_right W), isMultiplicative_muPhiTail.map_one]
  norm_num

/-- `constTerm W` is multiplicative: `constTerm W (m * n) = constTerm W m * constTerm W n` for
coprime `m` and `n`. -/
theorem constTerm_mul {W m n : ℕ} (h : Nat.Coprime m n) :
    constTerm W (m * n) = constTerm W m * constTerm W n := by
  simp only [constTerm]
  by_cases hm : Nat.Coprime W m
  · by_cases hn : Nat.Coprime W n
    · rw [if_pos hm, if_pos hn, if_pos (Nat.coprime_mul_iff_right.mpr ⟨hm, hn⟩),
        isMultiplicative_muPhiTail.map_mul_of_coprime h, Nat.totient_mul h]
      push_cast
      ring
    · rw [if_neg hn, if_neg fun hc => hn (Nat.coprime_mul_iff_right.mp hc).2, mul_zero]
  · rw [if_neg hm, if_neg fun hc => hm (Nat.coprime_mul_iff_right.mp hc).1, zero_mul]

/-- `‖constTerm W d‖ ≤ muPhiTail d`. -/
theorem norm_constTerm_le (W d : ℕ) : ‖constTerm W d‖ ≤ muPhiTail d := by
  rw [constTerm]
  split_ifs
  · rw [Real.norm_of_nonneg (mul_nonneg (muPhiTail_nonneg d) (totient_div_nonneg d))]
    exact mul_le_of_le_one_right (muPhiTail_nonneg d) (totient_div_le_one d)
  · simpa using muPhiTail_nonneg d

/-- The norms `‖constTerm W d‖` are summable over `d`. -/
theorem summable_norm_constTerm (W : ℕ) : Summable fun d : ℕ => ‖constTerm W d‖ :=
  summable_muPhiTail.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_constTerm_le W)

/-- **The Euler factor of the constant.** At a prime `p`, only `j = 0` and `j = 1` contribute,
`μ` vanishing on higher prime powers, and the `j = 1` term is
`(1/((p-1)(p-2)))·((p-1)/p) = 1/(p(p-2))`. -/
theorem tsum_constTerm_prime_pow {W p : ℕ} (hp : p.Prime) :
    ∑' j : ℕ, constTerm W (p ^ j)
      = if p ∣ W then 1 else 1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)) := by
  have hz : ∀ j ∉ ({0, 1} : Finset ℕ), constTerm W (p ^ j) = 0 := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    have hmu : μ (p ^ j) = 0 := by rw [moebius_apply_prime_pow hp hj.1, if_neg hj.2]
    simp [constTerm, muPhiTail_apply, hmu]
  rw [tsum_eq_sum hz, Finset.sum_insert (by simp), Finset.sum_singleton, pow_zero, pow_one,
    constTerm_one, constTerm]
  by_cases hd : p ∣ W
  · rw [if_neg fun hc => (hp.coprime_iff_not_dvd.mp hc.symm) hd, if_pos hd, add_zero]
  · rw [if_pos (Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr hd)), if_neg hd,
      muPhiTail_prime hp, Nat.totient_prime hp, Nat.cast_pred hp.pos]
    rcases hp.two_le.eq_or_lt with h | h
    · subst h
      norm_num
    · have h3 : (3 : ℝ) ≤ p := by exact_mod_cast h
      have h1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
      have h2 : (p : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
      have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith)
      field_simp

/-- **The Euler product for the constant.** For `2 ∣ W`,
`∑_{(d,W)=1}μ²(d)/(φ(d)(μ*φ)(d))·(φ(d)/d) = ∏_{p ∤ W}(1 + 1/(p(p-2)))`. -/
theorem hasProd_constTerm (W : ℕ) :
    HasProd (fun p : ℕ => if p.Prime ∧ ¬ p ∣ W then 1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)) else 1)
      (∑' d : ℕ, constTerm W d) := by
  refine (EulerProduct.eulerProduct_hasProd_mulIndicator (f := constTerm W) (constTerm_one W)
    (fun {_ _} hmn => constTerm_mul hmn) (summable_norm_constTerm W) (constTerm_zero W)).congr_fun
    fun p => ?_
  by_cases hp : p.Prime <;> by_cases hd : p ∣ W <;>
    simp [hp, hd, tsum_constTerm_prime_pow]

/-- **The local factor of the constant is the reciprocal of the correction factor.** For `p ≥ 3`,

  `(1 + 1/(p(p-2)))·(1 - 1/(p-1)²) = 1`,

both sides of the first factor being `(p-1)²/(p(p-2))`. For the `μ²/φ` kernel the corresponding
local factor is `(1 + 1/(p-1))(1 - 1/p) = 1`. At `p = 2` the identity fails, the correction factor
being `0` there. -/
theorem local_factor_mul_corr {p : ℕ} (hp : 3 ≤ p) :
    (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) * (1 - 1 / ((p : ℝ) - 1) ^ 2) = 1 := by
  have h3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2 : (p : ℝ) - 2 ≠ 0 := ne_of_gt (by linarith)
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- **The constant is the inverse of the correction product.** For even `W`,

  `∑_{(d,W)=1}(μ²(d)/(φ(d)(μ*φ)(d)))·(φ(d)/d) = (∏_{p ∤ W}(1 - 1/(p-1)²))^{-1}`.

The two infinite products are reciprocal factor by factor
(`Gap212.Sieve.local_factor_mul_corr`), so their `HasProd`s multiply to `HasProd 1 1`; uniqueness
of the limit gives the product of the two values as `1`, and `Gap212.Sieve.tprod_corr_pos` says the
correction product is nonzero, so the value here is its inverse. For odd `W` the factor
`1 - 1/(2-1)² = 0` at `p = 2` would make the correction product `0`. -/
theorem tsum_constTerm_eq_inv_tprod_corr {W : ℕ} (hW2 : 2 ∣ W) :
    ∑' d : ℕ, constTerm W d
      = (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ W then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)⁻¹ := by
  have hmul : HasProd (fun _ : ℕ => (1 : ℝ))
      ((∑' d : ℕ, constTerm W d)
        * ∏' p : ℕ, if p.Prime ∧ ¬ p ∣ W then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) := by
    refine ((hasProd_constTerm W).mul (multipliable_corr W).hasProd).congr_fun fun p => ?_
    by_cases hc : p.Prime ∧ ¬ p ∣ W
    · rw [if_pos hc, if_pos hc,
        local_factor_mul_corr (hc.1.two_le.lt_of_ne' fun hh => hc.2 (hh ▸ hW2))]
    · rw [if_neg hc, if_neg hc, one_mul]
  exact eq_inv_of_mul_eq_one_left (hasProd_one.unique hmul).symm

/-! ## The reindexing onto the reciprocal kernel -/

/-- The kernel `μ²/φ` vanishes on non-squarefree `m`. -/
theorem totientWeight_eq_zero_of_not_squarefree {m : ℕ} (hsf : ¬ Squarefree m) :
    totientWeight m = 0 := by
  rw [totientWeight_apply, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
  norm_num

/-- The kernel `μ²/(μ*φ)` vanishes on non-squarefree `e`. -/
theorem muPhiWeight_eq_zero_of_not_squarefree {e : ℕ} (hsf : ¬ Squarefree e) :
    muPhiWeight e = 0 := by
  rw [muPhiWeight_apply, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
  norm_num

/-- The pairs the tail sum runs over: `d, m ≥ 1` with `dm ≤ N`, `d` coprime to `W` and `m` coprime
to `Wd`. The modulus `Wd` on the second coordinate is what restricts the pairs to *coprime*
factorizations, which is exactly what makes the fibre over `e` the divisors of `e` and no more. -/
def tailPairs (W N : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 N ×ˢ Icc 1 N).filter
    fun q => Nat.Coprime W q.1 ∧ Nat.Coprime (W * q.1) q.2 ∧ q.1 * q.2 ≤ N

/-- `q ∈ tailPairs W N` if and only if both coordinates lie in `[1, N]`, `q.1` is coprime to `W`,
`q.2` is coprime to `W * q.1`, and `q.1 * q.2 ≤ N`. -/
theorem mem_tailPairs {W N : ℕ} {q : ℕ × ℕ} :
    q ∈ tailPairs W N ↔ ((1 ≤ q.1 ∧ q.1 ≤ N) ∧ (1 ≤ q.2 ∧ q.2 ≤ N)) ∧
      Nat.Coprime W q.1 ∧ Nat.Coprime (W * q.1) q.2 ∧ q.1 * q.2 ≤ N := by
  simp only [tailPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]

/-- **The fibre of the pair set over `e` carries exactly `μ²(e)/(μ*φ)(e)`.** For squarefree `e` the
fibre is the set of divisors, by `d ↦ (d, e/d)`, and the sum is the convolution
`Gap212.Sieve.muPhiWeight_eq_tail_mul_totientWeight`. For non-squarefree `e` every term vanishes:
the two coordinates are coprime, so one of them is not squarefree and its kernel is `0`. -/
theorem sum_fibre_eq_muPhiWeight {W N e : ℕ} (hW2 : 2 ∣ W)
    (he : e ∈ (Icc 1 N).filter fun e => Nat.Coprime W e) :
    ∑ q ∈ tailPairs W N with q.1 * q.2 = e, muPhiTail q.1 * totientWeight q.2
      = muPhiWeight e := by
  classical
  obtain ⟨hmem, hcop⟩ := Finset.mem_filter.mp he
  obtain ⟨he1, heN⟩ := Finset.mem_Icc.mp hmem
  have he0 : e ≠ 0 := by omega
  by_cases hsf : Squarefree e
  · have hodd : ¬ 2 ∣ e := Nat.prime_two.coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hW2)
    rw [muPhiWeight_eq_tail_mul_totientWeight hsf hodd, mul_apply,
      Nat.sum_divisorsAntidiagonal (f := fun a b => muPhiTail a * totientWeight b)]
    -- the fibre is `e.divisors`, by `d ↦ (d, e/d)`
    have hsnd : ∀ q ∈ (tailPairs W N).filter fun q : ℕ × ℕ => q.1 * q.2 = e, e / q.1 = q.2 := by
      intro q hq
      obtain ⟨hmemq, hprod⟩ := Finset.mem_filter.mp hq
      obtain ⟨⟨⟨h11, -⟩, -⟩, -⟩ := mem_tailPairs.mp hmemq
      rw [← hprod, Nat.mul_div_cancel_left _ (by omega)]
    refine Finset.sum_nbij' (i := fun q : ℕ × ℕ => q.1) (j := fun d : ℕ => (d, e / d))
      (fun q hq => Nat.mem_divisors.mpr ⟨⟨q.2, (Finset.mem_filter.mp hq).2.symm⟩, he0⟩)
      (fun d hd => ?_) (fun q hq => ?_)
      (fun d _ => rfl) fun q hq => by rw [hsnd q hq]
    · obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
      have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero he0 hdvd
      have hde : d ≤ e := Nat.le_of_dvd (by omega) hdvd
      have hmul : d * (e / d) = e := Nat.mul_div_cancel' hdvd
      have hcd : Nat.Coprime d (e / d) := (Nat.squarefree_mul_iff.mp (by rwa [hmul])).1
      exact Finset.mem_filter.mpr ⟨mem_tailPairs.mpr
        ⟨⟨⟨by omega, hde.trans heN⟩, ⟨Nat.div_pos hde (by omega), (Nat.div_le_self e d).trans heN⟩⟩,
          hcop.coprime_dvd_right hdvd,
          Nat.coprime_mul_iff_left.mpr ⟨hcop.coprime_dvd_right (Nat.div_dvd_of_dvd hdvd), hcd⟩,
          by rwa [hmul]⟩, hmul⟩
    · exact Prod.ext rfl (hsnd q hq)
  · rw [muPhiWeight_eq_zero_of_not_squarefree hsf]
    refine Finset.sum_eq_zero fun q hq => ?_
    obtain ⟨hmemq, hprod⟩ := Finset.mem_filter.mp hq
    obtain ⟨-, -, hcop2, -⟩ := mem_tailPairs.mp hmemq
    have hcd : Nat.Coprime q.1 q.2 := (Nat.coprime_mul_iff_left.mp hcop2).2
    by_cases h1 : Squarefree q.1
    · by_cases h2 : Squarefree q.2
      · exact absurd (hprod ▸ Nat.squarefree_mul_iff.mpr ⟨hcd, h1, h2⟩) hsf
      · rw [totientWeight_eq_zero_of_not_squarefree h2, mul_zero]
    · rw [muPhiTail_eq_zero_of_not_squarefree h1, zero_mul]

/-- **The pair sum, grouped by the first coordinate**, is the tail sum: the second coordinate runs
over `m ≤ N/d` because `dm ≤ N`. -/
theorem sum_tailPairs_eq_sum_tail (W N : ℕ) :
    ∑ q ∈ tailPairs W N, muPhiTail q.1 * totientWeight q.2
      = ∑ d ∈ Icc 1 N with Nat.Coprime W d,
          muPhiTail d * ∑ m ∈ Icc 1 (N / d) with Nat.Coprime (W * d) m, totientWeight m := by
  classical
  rw [tailPairs, Finset.sum_filter, Finset.sum_product, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
  by_cases hcop : Nat.Coprime W d
  · have hset : ((Icc 1 N).filter fun m => Nat.Coprime (W * d) m ∧ d * m ≤ N)
        = (Icc 1 (N / d)).filter fun m => Nat.Coprime (W * d) m := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.le_div_iff_mul_le hd1, mul_comm d m]
      exact ⟨fun ⟨⟨h1, _⟩, hc, hle⟩ => ⟨⟨h1, hle⟩, hc⟩,
        fun ⟨⟨h1, hle⟩, hc⟩ => ⟨⟨h1, (Nat.le_mul_of_pos_right m hd1).trans hle⟩, hc, hle⟩⟩
    rw [if_pos hcop, ← hset, Finset.mul_sum, Finset.sum_filter]
    exact Finset.sum_congr rfl fun m _ => if_congr (and_iff_right hcop) rfl rfl
  · simp [hcop]

/-- **The reindexing.** For even squarefree `W`,

  `∑_{e≤N,(e,W)=1}μ²(e)/(μ*φ)(e)
     = ∑_{d≤N,(d,W)=1}(μ²(d)/(φ(d)(μ*φ)(d)))·∑_{m≤N/d,(m,Wd)=1}μ²(m)/φ(m)`,

an exact identity. It reduces the sum to `Gap212.Sieve.sum_moebiusSq_div_totient_coprime` at the
moduli `Wd`.

The device is the convolution `μ²/(μ*φ) = (μ²/(φ·(μ*φ))) ⊛ (μ²/φ)` over *coprime* factorizations
only, and the coprimality is enforced by taking the inner modulus to be `Wd` rather than `W`. Both
sides are summed over the same finite set of pairs
(`Gap212.Sieve.sum_fibre_eq_muPhiWeight`, `Gap212.Sieve.sum_tailPairs_eq_sum_tail`). -/
theorem sum_muPhiWeight_eq_sum_tail {W N : ℕ} (hW2 : 2 ∣ W) :
    (∑ e ∈ Icc 1 N with Nat.Coprime W e, muPhiWeight e)
      = ∑ d ∈ Icc 1 N with Nat.Coprime W d,
          muPhiTail d * ∑ m ∈ Icc 1 (N / d) with Nat.Coprime (W * d) m, totientWeight m := by
  classical
  rw [← sum_tailPairs_eq_sum_tail]
  have hmaps : ∀ q ∈ tailPairs W N, q.1 * q.2 ∈ (Icc 1 N).filter fun e => Nat.Coprime W e := by
    intro q hq
    obtain ⟨⟨⟨h11, -⟩, ⟨h21, -⟩⟩, hc1, hc2, hle⟩ := mem_tailPairs.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_le_mul h11 h21, hle⟩,
      Nat.coprime_mul_iff_right.mpr ⟨hc1, (Nat.coprime_mul_iff_left.mp hc2).1⟩⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  exact Finset.sum_congr rfl fun e he => (sum_fibre_eq_muPhiWeight hW2 he).symm

/-! ## Bookkeeping for the assembly -/

/-- The summand of the constant is non-negative. -/
theorem constTerm_nonneg (W d : ℕ) : 0 ≤ constTerm W d :=
  ite_nonneg (mul_nonneg (muPhiTail_nonneg d) (totient_div_nonneg d)) le_rfl

/-- `ℓ_{Wd} = ℓ_W + ℓ_d` on coprime moduli: the prime factors split disjointly. -/
theorem ellV_mul {W d : ℕ} (hW : W ≠ 0) (hd : d ≠ 0) (h : Nat.Coprime W d) :
    PrimeGaps.ellV (W * d) = PrimeGaps.ellV W + PrimeGaps.ellV d := by
  rw [PrimeGaps.ellV, PrimeGaps.ellV, PrimeGaps.ellV, Nat.primeFactors_mul hW hd,
    Finset.sum_union ((Nat.disjoint_primeFactors hW hd).mpr h)]

private theorem cast_le_two_mul_mul_div {N d : ℕ} (hd1 : 1 ≤ d) (hdN : d ≤ N) :
    (N : ℝ) ≤ 2 * (d : ℝ) * ((N / d : ℕ) : ℝ) := by
  have := Nat.div_add_mod N d
  have := Nat.mod_lt N hd1
  have := Nat.le_mul_of_pos_right d ((Nat.one_le_div_iff hd1).mpr hdN)
  have h : N ≤ 2 * d * (N / d) := by rw [mul_assoc]; omega
  exact_mod_cast h

/-- **The truncation of the outer sum costs `log 2 + log d`.** For `1 ≤ d ≤ N` the inner cutoff
`⌊N/d⌋` satisfies `N ≤ 2d⌊N/d⌋`, so `|log N - log⌊N/d⌋| ≤ 1 + log d`. -/
theorem abs_log_sub_log_div_le {N d : ℕ} (hd1 : 1 ≤ d) (hdN : d ≤ N) :
    |Real.log N - Real.log ((N / d : ℕ) : ℝ)| ≤ 1 + Real.log d := by
  have hMR : (1 : ℝ) ≤ ((N / d : ℕ) : ℝ) := by exact_mod_cast (Nat.one_le_div_iff hd1).mpr hdN
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hd1.trans hdN
  have hup : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log N :=
    Real.log_le_log (by linarith) (by exact_mod_cast Nat.div_le_self N d)
  have hlow : Real.log N ≤ Real.log 2 + Real.log d + Real.log ((N / d : ℕ) : ℝ) := by
    rw [← Real.log_mul (by norm_num) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by linarith) (cast_le_two_mul_mul_div hd1 hdN)
  have hlog2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **The tail of the constant's series beyond `N` is `O(1/√N)`.** Every `d > N` has `√d ≥ √N`, so
its term is at most `muPhiTailBound d/√N` (`Gap212.Sieve.muPhiTail_mul_sqrt_le`). -/
theorem abs_tsum_constTerm_sub_sum_le {W N : ℕ} (hN : 1 ≤ N) :
    |(∑' d : ℕ, constTerm W d) - ∑ d ∈ Icc 1 N with Nat.Coprime W d, constTerm W d|
      ≤ (∑' d : ℕ, muPhiTailBound d) / Real.sqrt N := by
  classical
  set s : Finset ℕ := (Icc 1 N).filter fun d => Nat.Coprime W d with hs
  have hNR : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  set G : ℕ → ℝ := fun d => if d ∈ s then 0 else constTerm W d with hG
  have hGle : ∀ d, G d ≤ muPhiTailBound d / Real.sqrt N := by
    intro d
    have h0 := div_nonneg (muPhiTailBound_nonneg d) hNR.le
    simp only [hG, hs, Finset.mem_filter, Finset.mem_Icc]
    split_ifs with hd
    · exact h0
    rcases Nat.eq_zero_or_pos d with rfl | hd1
    · rwa [constTerm_zero]
    by_cases hcop : Nat.Coprime W d
    · have hdN : N < d := not_le.mp fun h => hd ⟨⟨hd1, h⟩, hcop⟩
      rw [le_div_iff₀ hNR]
      calc constTerm W d * Real.sqrt N ≤ muPhiTail d * Real.sqrt d :=
            mul_le_mul ((Real.le_norm_self _).trans (norm_constTerm_le W d))
              (Real.sqrt_le_sqrt (by exact_mod_cast hdN.le)) hNR.le (muPhiTail_nonneg d)
        _ ≤ muPhiTailBound d := muPhiTail_mul_sqrt_le d
    · rwa [constTerm, if_neg hcop]
  have hG0 : ∀ d, 0 ≤ G d := fun d => ite_nonneg le_rfl (constTerm_nonneg W d)
  have hGsum : Summable G := (summable_muPhiTailBound.div_const _).of_nonneg_of_le hG0 hGle
  set I : ℕ → ℝ := fun d => if d ∈ s then constTerm W d else 0
  have hsplit : ∑' d : ℕ, constTerm W d = (∑' d : ℕ, G d) + ∑ d ∈ s, constTerm W d := by
    have hIval : ∑' d : ℕ, I d = ∑ d ∈ s, constTerm W d :=
      (tsum_eq_sum fun d hd => if_neg hd).trans (Finset.sum_congr rfl fun d hd => if_pos hd)
    rw [← hIval, ← hGsum.tsum_add (summable_of_ne_finset_zero (s := s) fun d hd => if_neg hd)]
    exact tsum_congr fun d => by simp only [hG]; split_ifs <;> ring
  rw [hsplit, add_sub_cancel_right, abs_of_nonneg (tsum_nonneg hG0), ← tsum_div_const]
  exact hGsum.tsum_le_tsum hGle (summable_muPhiTailBound.div_const _)

/-! ## The asymptotic -/

/-- The divisor count is multiplicative: `τ(mn) = τ(m)·τ(n)` for coprime `m` and `n`. -/
theorem card_divisors_mul {m n : ℕ} (h : Nat.Coprime m n) :
    #(m * n).divisors = #m.divisors * #n.divisors :=
  h.card_divisors_mul

/-- **The `d`-th term of the reindexed sum against its predicted value.** For `1 ≤ d ≤ N` coprime
to `W`, the inner sum is the `μ²/φ` sum at modulus `Wd` and cutoff `⌊N/d⌋`, so
`Gap212.Sieve.sum_moebiusSq_div_totient_coprime` applies; its error `C(1 + τ(Wd)/⌊N/d⌋)` is
absorbed because `τ(Wd) = τ(W)τ(d)` and `⌊N/d⌋ ≥ 1`, and `μ²(d)/(φ(d)(μ*φ)(d))·τ(d)` is at most
the majorant. On non-squarefree `d` both terms vanish. -/
theorem abs_term_sub_predicted_le {C : ℝ} (hC : 0 < C)
    (hT : ∀ V : ℕ, 1 ≤ V → Squarefree V → ∀ M : ℕ, 1 ≤ M →
      |(∑ e ∈ Icc 1 M with Nat.Coprime V e, ((μ e : ℝ) ^ 2 / (e.totient : ℝ)))
        - (V.totient : ℝ) / (V : ℝ) * (Real.log M + Real.eulerMascheroniConstant
            + PrimeGaps.ellV V)| ≤ C * (1 + (#V.divisors : ℝ) / M))
    {W N d : ℕ} (hWsf : Squarefree W) (hW1 : 1 ≤ W) (hd1 : 1 ≤ d) (hdN : d ≤ N)
    (hcop : Nat.Coprime W d) :
    |muPhiTail d * (∑ m ∈ Icc 1 (N / d) with Nat.Coprime (W * d) m, totientWeight m)
        - (W.totient : ℝ) / (W : ℝ) * constTerm W d
            * (Real.log ((N / d : ℕ) : ℝ) + Real.eulerMascheroniConstant
                + PrimeGaps.ellV W + PrimeGaps.ellV d)|
      ≤ C * (1 + 2 * (#W.divisors : ℝ)) * muPhiTailBound d := by
  have hbd0 := muPhiTailBound_nonneg d
  have hm0 := muPhiTail_nonneg d
  by_cases hsf : Squarefree d
  · have hM1 : 1 ≤ N / d := (Nat.one_le_div_iff (by omega)).mpr hdN
    have hkey := hT (W * d) (Nat.mul_le_mul hW1 hd1) (Nat.squarefree_mul_iff.mpr ⟨hcop, hWsf, hsf⟩)
      (N / d) hM1
    have hphi : ((W * d).totient : ℝ) / ((W * d : ℕ) : ℝ)
        = (W.totient : ℝ) / (W : ℝ) * ((d.totient : ℝ) / (d : ℝ)) := by
      rw [Nat.totient_mul hcop]
      push_cast
      ring
    rw [hphi, ellV_mul (by omega) (by omega) hcop, ← add_assoc] at hkey
    have hτ : (#(W * d).divisors : ℝ) / ((N / d : ℕ) : ℝ) ≤ #W.divisors * #d.divisors := by
      rw [card_divisors_mul hcop, Nat.cast_mul]
      exact div_le_self (by positivity) (by exact_mod_cast hM1)
    have h₁ : muPhiTail d * #d.divisors ≤ muPhiTail d * #d.divisors * Real.sqrt d :=
      le_mul_of_one_le_right (by positivity) (Real.one_le_sqrt.mpr (by exact_mod_cast hd1))
    have h₂ := h₁.trans (muPhiTail_mul_weight_le d)
    rw [constTerm, if_pos hcop, mul_left_comm _ (muPhiTail d), mul_assoc (muPhiTail d), ← mul_sub,
      abs_mul, abs_of_nonneg hm0]
    refine (mul_le_mul_of_nonneg_left
      (hkey.trans (mul_le_mul_of_nonneg_left (add_le_add_right hτ 1) hC.le)) hm0).trans ?_
    have hCτ : (0 : ℝ) ≤ C * #W.divisors := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (muPhiTail_le_bound d) hC.le,
      mul_le_mul_of_nonneg_left h₂ hCτ, mul_nonneg hCτ hbd0]
  · have h0 := muPhiTail_eq_zero_of_not_squarefree hsf
    simp only [constTerm, if_pos hcop, h0, zero_mul, mul_zero, sub_self, abs_zero]
    positivity

/-- The main term's per-`d` truncation error: replacing `\log N` by the shifted
`\log ⌊N/d⌋ + γ + ℓ_W + ℓ_d` costs at most the majorant `muPhiTailBound d` times an absolute
factor. -/
theorem abs_constTerm_mul_log_sub_le (W : ℕ) {N d : ℕ} (hd1 : 1 ≤ d) (hdN : d ≤ N) :
    |constTerm W d * ((Real.log ((N / d : ℕ) : ℝ) + Real.eulerMascheroniConstant
        + PrimeGaps.ellV W + PrimeGaps.ellV d) - Real.log N)|
      ≤ muPhiTailBound d * (2 + |Real.eulerMascheroniConstant| + PrimeGaps.ellV W) := by
  obtain ⟨hlog₁, hlog₂⟩ := abs_le.mp (abs_log_sub_log_div_le hd1 hdN)
  have hlogd := Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hd1)
  have hinner : |(Real.log ((N / d : ℕ) : ℝ) + Real.eulerMascheroniConstant
        + PrimeGaps.ellV W + PrimeGaps.ellV d) - Real.log N|
      ≤ (1 + Real.log d) * (2 + |Real.eulerMascheroniConstant| + PrimeGaps.ellV W) := by
    rw [abs_le]
    constructor <;> nlinarith [neg_abs_le Real.eulerMascheroniConstant,
      le_abs_self Real.eulerMascheroniConstant, PrimeGaps.ellV_nonneg d, PrimeGaps.ellV_nonneg W,
      ellV_le_log hd1]
  rw [abs_mul, abs_of_nonneg (constTerm_nonneg W d)]
  refine (mul_le_mul ((Real.le_norm_self _).trans (norm_constTerm_le W d)) hinner (abs_nonneg _)
    (muPhiTail_nonneg d)).trans ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (muPhiTail_mul_one_add_log_le d)
    (by have := PrimeGaps.ellV_nonneg W; positivity)

/-- **The asymptotic, with the constant written as the series and the error uniform in `W`.** An
intermediate form of `Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime`: the constant appears
as `∑_{(d,W)=1}(μ²(d)/(φ(d)(μ*φ)(d)))(φ(d)/d)`, which
`Gap212.Sieve.tsum_constTerm_eq_inv_tprod_corr` identifies with the inverse correction product.

There is one absolute `C` for every even squarefree `W` and every `N ≥ 1`, the `W`-dependence of
the error being `τ(W) + ℓ_W`. The two pieces of the proof are `C₀(1 + 2τ(W))·S`, from the
reciprocal kernel's error summed over the outer variable, and `S(2 + |γ| + ℓ_W) + 2S`, from the
main term, with `S = ∑_d` the majorant series `Gap212.Sieve.muPhiTailBound`. -/
theorem abs_sum_muPhiWeight_sub_tsum_mul_log_le :
    ∃ C : ℝ, 0 < C ∧ ∀ W : ℕ, 2 ∣ W → Squarefree W → ∀ N : ℕ, 1 ≤ N →
      |(∑ e ∈ Icc 1 N with Nat.Coprime W e, muPhiWeight e)
          - (W.totient : ℝ) / (W : ℝ) * (∑' d : ℕ, constTerm W d) * Real.log N|
        ≤ C * ((#W.divisors : ℝ) + PrimeGaps.ellV W) := by
  classical
  obtain ⟨C, hC, hT⟩ := sum_moebiusSq_div_totient_coprime
  have hB0 : (0 : ℝ) ≤ ∑' d : ℕ, muPhiTailBound d := tsum_nonneg muPhiTailBound_nonneg
  refine ⟨3 * C * (∑' d : ℕ, muPhiTailBound d)
      + (∑' d : ℕ, muPhiTailBound d) * (4 + |Real.eulerMascheroniConstant|)
      + (∑' d : ℕ, muPhiTailBound d) + 1, by positivity, fun W hW2 hWsf N hN => ?_⟩
  have hW1 : 1 ≤ W := Nat.pos_of_ne_zero hWsf.ne_zero
  have hr0 := totient_div_nonneg W
  have hellW := PrimeGaps.ellV_nonneg W
  have hτ1 := one_le_card_divisors hW1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hbdsum : ∑ d ∈ Icc 1 N with Nat.Coprime W d, muPhiTailBound d
      ≤ ∑' d : ℕ, muPhiTailBound d :=
    summable_muPhiTailBound.sum_le_tsum _ fun d _ => muPhiTailBound_nonneg d
  -- the reciprocal kernel's error, summed over the outer variable
  set E := ∑ d ∈ Icc 1 N with Nat.Coprime W d,
      (muPhiTail d * (∑ m ∈ Icc 1 (N / d) with Nat.Coprime (W * d) m, totientWeight m)
        - (W.totient : ℝ) / (W : ℝ) * constTerm W d
          * (Real.log ((N / d : ℕ) : ℝ) + Real.eulerMascheroniConstant
            + PrimeGaps.ellV W + PrimeGaps.ellV d)) with hE
  -- the main term's bookkeeping: the truncated logarithm, then the truncated series
  set P₁ := ∑ d ∈ Icc 1 N with Nat.Coprime W d, constTerm W d
      * ((Real.log ((N / d : ℕ) : ℝ) + Real.eulerMascheroniConstant
        + PrimeGaps.ellV W + PrimeGaps.ellV d) - Real.log N) with hP₁
  set P₂ := ((∑ d ∈ Icc 1 N with Nat.Coprime W d, constTerm W d)
      - ∑' d : ℕ, constTerm W d) * Real.log N with hP₂
  have h₁ : |E| ≤ C * (1 + 2 * (#W.divisors : ℝ)) * ∑' d : ℕ, muPhiTailBound d := by
    rw [hE]
    refine (Finset.abs_sum_le_sum_abs _ _).trans <| (Finset.sum_le_sum fun d hd => ?_).trans <|
      (Finset.mul_sum ..).symm.trans_le (mul_le_mul_of_nonneg_left hbdsum (by positivity))
    obtain ⟨hmem, hcop⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hmem
    exact abs_term_sub_predicted_le hC hT hWsf hW1 hd1 hdN hcop
  have h₂ : |P₁| ≤ (∑' d : ℕ, muPhiTailBound d)
      * (2 + |Real.eulerMascheroniConstant| + PrimeGaps.ellV W) := by
    rw [hP₁]
    refine (Finset.abs_sum_le_sum_abs _ _).trans <| (Finset.sum_le_sum fun d hd => ?_).trans <|
      (Finset.sum_mul ..).symm.trans_le (mul_le_mul_of_nonneg_right hbdsum (by positivity))
    obtain ⟨hmem, -⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hmem
    exact abs_constTerm_mul_log_sub_le W hd1 hdN
  have h₃ : |P₂| ≤ 2 * ∑' d : ℕ, muPhiTailBound d := by
    rw [hP₂, abs_mul, abs_of_nonneg hlogN, abs_sub_comm]
    calc _ ≤ ((∑' d : ℕ, muPhiTailBound d) / Real.sqrt N) * (2 * Real.sqrt N) :=
          mul_le_mul (abs_tsum_constTerm_sub_sum_le hN) (log_le_two_mul_sqrt hNpos) hlogN
            (by positivity)
      _ = 2 * ∑' d : ℕ, muPhiTailBound d := by field_simp
  have h₄ := mul_le_of_le_one_left (add_nonneg (abs_nonneg P₁) (abs_nonneg P₂))
    (totient_div_le_one W)
  rw [sum_muPhiWeight_eq_sum_tail hW2]
  calc _ = |E + (W.totient : ℝ) / (W : ℝ) * (P₁ + P₂)| := by
        congr 1
        simp only [hE, hP₁, hP₂, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul, mul_sub,
          sub_mul, mul_add, mul_assoc]
        ring
    _ ≤ |E| + (W.totient : ℝ) / (W : ℝ) * (|P₁| + |P₂|) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hr0]
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by
        have h4g : (0 : ℝ) ≤ 4 + |Real.eulerMascheroniConstant| := by positivity
        linarith [mul_nonneg (mul_nonneg hC.le hB0) (sub_nonneg.2 hτ1),
          mul_nonneg (mul_nonneg hC.le hB0) hellW, mul_nonneg (mul_nonneg hB0 h4g) hellW,
          mul_nonneg (mul_nonneg hB0 h4g) (sub_nonneg.2 hτ1),
          mul_nonneg hB0 (hτ1.trans' zero_le_one)]

/-- **The Mertens asymptotic for the totient Gram kernel, uniformly in the modulus.** There is one
absolute `C` such that for every even squarefree `W` and every `N ≥ 1`,

  `|∑_{e ≤ N, (W,e)=1} μ²(e)/(μ*φ)(e)
      − (φ(W)/W)·(∏_{p ∤ W}(1 - 1/(p-1)²))^{-1}·\log N| ≤ C·(τ(W) + ℓ_W)`.

It is the counting-measure half of the two inputs of
`Gap212.Sieve.totientGramSumLimitOfSupport_iff`.

The error constant is quantified before `W`, so that the asymptotic can be read at the growing
modulus `W = W(x)`: with `W(x) ≤ (\log\log x)²` (`Gap212.Sieve.W_le_log_log_sq`),
`τ(W(x)) + ℓ_{W(x)} = o(\log x)`. The fixed-modulus form is
`Gap212.Sieve.exists_bound_sum_moebiusSq_div_moebiusTotient_coprime`.

The constant is not `φ(W)/W`, as it is for the reciprocal kernel in
`Gap212.Sieve.sum_moebiusSq_div_totient_coprime`: the local factor here is
`1 + 1/(p(p-2)) = (1 - 1/(p-1)²)^{-1} ≠ 1` (`Gap212.Sieve.local_factor_mul_corr`).

Evenness of `W` makes every `e` in the sum odd, which the convolution
`Gap212.Sieve.muPhiWeight_eq_tail_mul_totientWeight` needs since `(μ*φ)(2) = 0`, and keeps `p = 2`
out of the correction product, whose factor there is `0`
(`Gap212.Sieve.tsum_constTerm_eq_inv_tprod_corr`). The error term is additive and independent of
`N`; at `W` the primorial of `N` the left side is its `e = 1` term `1`. -/
@[gap212 "lem_moebius_sq_mu_phi_asymptotic"]
theorem sum_moebiusSq_div_moebiusTotient_coprime :
    ∃ C : ℝ, 0 < C ∧ ∀ W : ℕ, 2 ∣ W → Squarefree W → ∀ N : ℕ, 1 ≤ N →
      |(∑ e ∈ Icc 1 N with Nat.Coprime W e, ((μ e : ℝ) ^ 2 / moebiusTotient e))
          - (W.totient : ℝ) / (W : ℝ)
            * (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ W then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)⁻¹
            * Real.log N|
        ≤ C * ((#W.divisors : ℝ) + PrimeGaps.ellV W) := by
  obtain ⟨C, hC, hD⟩ := abs_sum_muPhiWeight_sub_tsum_mul_log_le
  refine ⟨C, hC, fun W hW2 hWsf N hN => ?_⟩
  simpa only [← muPhiWeight_apply, ← tsum_constTerm_eq_inv_tprod_corr hW2] using hD W hW2 hWsf N hN

/-- **The fixed-modulus form of the asymptotic.** `∀ W, ∃ D, ∀ N`: a consequence of
`Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime`, taking `D = C(τ(W) + ℓ_W)`. -/
theorem exists_bound_sum_moebiusSq_div_moebiusTotient_coprime {W : ℕ} (hW2 : 2 ∣ W)
    (hWsf : Squarefree W) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 1 ≤ N →
      |(∑ e ∈ Icc 1 N with Nat.Coprime W e, ((μ e : ℝ) ^ 2 / moebiusTotient e))
          - (W.totient : ℝ) / (W : ℝ)
            * (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ W then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)⁻¹
            * Real.log N| ≤ D := by
  obtain ⟨C, hC, hD⟩ := sum_moebiusSq_div_moebiusTotient_coprime
  have hell := PrimeGaps.ellV_nonneg W
  exact ⟨_, by positivity, hD W hW2 hWsf⟩

end Gap212.Sieve
