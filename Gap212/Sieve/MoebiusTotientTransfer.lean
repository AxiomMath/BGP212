/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MoebiusDecay
public import Gap212.Sieve.MoebiusTotientDecay
public import PrimeGapsTheory.Arithmetic.Mertens.Shared

/-!
# The decay of the Möbius–totient partial sums, from the reciprocal weight

A proof of `Gap212.Sieve.MoebiusTotientPartialSumDecay` from the reciprocal-weight decay
`Gap212.Sieve.moebiusPartialSumDecay`. The two partial sums

  `T_e(w) = ∑_{f ≤ w, (f,e)=1} μ(f)/φ(f)`,   `A_e(w) = ∑_{f ≤ w, (f,e)=1} μ(f)/f`

differ termwise by the factor `f/φ(f)`, which is unbounded, so no termwise inequality relates them;
they are related instead by a Dirichlet convolution.

## The route

1. **The convolution.** Write `m_e = Gap212.Sieve.coprimeDivWeight e μ`, so `m_e n = μ(n)/n`
   restricted to `(n,e) = 1` and `summatory m_e = A_e`. Let

     `F n = n μ(n)/φ(n)`   (`Gap212.Sieve.moebiusTotientNum`),
     `G = ζ * F`           (`Gap212.Sieve.moebiusTotientDivisorSum`),

   and let `b_e = coprimeDivWeight e F`, which is `μ(n)/φ(n)` restricted, with
   `summatory b_e = T_e`. Because restriction-and-division-by-`id` is a ring map for Dirichlet
   convolution (`Gap212.Sieve.coprimeDivWeight_mul`) and `μ * ζ = 1`,

     `m_e * (coprimeDivWeight e G) = coprimeDivWeight e (μ * ζ * F) = b_e`.

   This is `Gap212.Sieve.coprimeMoebius_mul_transferWeight`; the transfer weight is defined as
   `coprimeDivWeight e (ζ * F)`, so the identity is an instance of the ring-map property, and the
   prime-power values are needed only for the size of the weight.

2. **The hyperbola identity** `Gap212.Sieve.summatory_hyperbola`, applied to that factorisation,
   gives `Gap212.Sieve.moebiusTotientBelow_eq_sum`:

     `T_e(w) = ∑_{n ≤ w} g_e(n) · A_e(w/n)`,   `g_e = coprimeDivWeight e G`.

3. **The size of `g_e`.** `G` is multiplicative and `G(p^a) = -1/(p-1)` for every `a ≥ 1`
   (`Gap212.Sieve.moebiusTotientDivisorSum_prime_pow`), so `|g_e(n)| ≤ 1/(n ∏_{p ∣ n}(p-1))`. The
   quantity actually estimated is the `√n`-weighted one,
   `H_e(n) = √n |g_e(n)|` (`Gap212.Sieve.transferAbsWeight`), whose local series is geometric with
   ratio `1/√p`. `PrimeGaps.MertensShared.finset_sum_le_exp_tsum_of_local` — the Euler-product
   bound for a nonnegative multiplicative function, over smooth numbers — then gives one constant
   `Γ` with `∑_{n ∈ u} H_e(n) ≤ Γ` for **every** finite `u`
   (`Gap212.Sieve.exists_sum_transferAbsWeight_le`).

4. **The split.** In (2), cut at `n ≤ √w`. On the near range `log(w/n) ≥ (log w)/2`, so
   `|A_e(w/n)| ≤ 4C/(1 + log w)^2` and the contribution is `≤ 4CΓ/(1 + log w)^2`. On the far range
   `√n ≥ w^{1/4}`, so `|g_e(n)| ≤ H_e(n) w^{-1/4}`, and the trivial
   `|A_e(y)| ≤ 1 + log y` (`Gap212.Sieve.abs_moebiusReciprocalBelow_le`) bounds the contribution by
   `Γ (1 + log w) w^{-1/4}`. That is `≤ ΓK/(1 + log w)^2` because `(1 + log w)^3 ≤ K w^{1/4}`
   (`Gap212.Sieve.exists_one_add_log_cube_le_sqrt_sqrt`, from
   `Gap212.Sieve.exists_one_add_log_pow_le_mul` at `w^{1/4}`).

## Main results

* `Gap212.Sieve.coprimeMoebius_mul_transferWeight`: `m_e * g_e = b_e`, the convolution identity.
* `Gap212.Sieve.moebiusTotientBelow_eq_sum`: `T_e(w) = ∑_{n ≤ w} g_e(n) A_e(w/n)`.
* `Gap212.Sieve.exists_sum_transferAbsWeight_le`: `∑_{n ∈ u} √n |g_e(n)| ≤ Γ`, uniformly in `u`.
* `Gap212.Sieve.exists_moebiusTotientBelow_log_sq_decay`: `|T_e(w)| ≤ C (1 + log w)^{-2}` for
  `w ≥ 1`.
* `Gap212.Sieve.moebiusTotientPartialSumDecay`: `Gap212.Sieve.MoebiusTotientPartialSumDecay`, at
  `ε = 1`.
-/

@[expose] public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Gap212.Sieve


/-- `n ↦ n · μ(n)/φ(n)`. -/
noncomputable def moebiusTotientNum : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℝ).pmul
    ((μ : ArithmeticFunction ℝ).pmul invTotient)

/-- The defining formula for `Gap212.Sieve.moebiusTotientNum`, away from `0`. -/
theorem moebiusTotientNum_apply {n : ℕ} (hn : n ≠ 0) :
    moebiusTotientNum n = (n : ℝ) * (μ n : ℝ) / (n.totient : ℝ) := by
  simp only [moebiusTotientNum, pmul_apply, natCoe_apply, id_apply, intCoe_apply,
    invTotient_apply hn]
  ring

/-- `F` is multiplicative, being the pointwise product of `id`, `μ` and `1/φ`. -/
theorem isMultiplicative_moebiusTotientNum : moebiusTotientNum.IsMultiplicative :=
  (isMultiplicative_id.natCast).pmul
    ((isMultiplicative_moebius.intCast).pmul isMultiplicative_invTotient)

/-- `n ↦ ∑_{d ∣ n} d μ(d)/φ(d)`. -/
noncomputable def moebiusTotientDivisorSum : ArithmeticFunction ℝ :=
  (ζ : ArithmeticFunction ℝ) * moebiusTotientNum

/-- `G = ζ * F` is multiplicative, being a Dirichlet product of multiplicative functions. -/
theorem isMultiplicative_moebiusTotientDivisorSum :
    moebiusTotientDivisorSum.IsMultiplicative :=
  (isMultiplicative_zeta.natCast).mul isMultiplicative_moebiusTotientNum

/-- **`G(p^a) = -1/(p-1)` for every `a ≥ 1`.** Only `d = 1` and `d = p` contribute to
`∑_{d ∣ p^a} d μ(d)/φ(d)`, because `μ` kills the higher prime powers, and
`1 + p·(-1)/(p-1) = -1/(p-1)`. The value does not depend on `a`, which is why `|G(n)|` is a product
over the *distinct* primes dividing `n` and is bounded by `1`. -/
theorem moebiusTotientDivisorSum_prime_pow {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a) :
    moebiusTotientDivisorSum (p ^ a) = -1 / ((p : ℝ) - 1) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' ha
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [moebiusTotientDivisorSum, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp,
    sum_range_succ', sum_range_succ', sum_eq_zero fun i _ ↦ ?_]
  · simp [moebiusTotientNum_apply, hp.ne_zero, Nat.totient_prime hp, moebius_apply_prime hp,
      Nat.cast_pred hp.pos]
    field_simp
    ring
  rw [moebiusTotientNum_apply (pow_ne_zero _ hp.ne_zero), moebius_apply_prime_pow hp (by omega)]
  simp

/-- Restricting to the integers coprime to `q` and dividing by `id` preserves multiplicativity. -/
theorem isMultiplicative_coprimeDivWeight (q : ℕ) {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) : (coprimeDivWeight q f).IsMultiplicative := by
  refine ⟨by simp [coprimeDivWeight_apply, hf.map_one], fun {m n} h => ?_⟩
  simp only [coprimeDivWeight_apply, Nat.coprime_mul_iff_left]
  split_ifs <;> simp_all [hf.map_mul_of_coprime h, div_mul_div_comm]

/-- **The convolution identity** `m_e * g_e = b_e`: the restricted Möbius weight `μ(n)/n` convolved
with the transfer weight `g_e = coprimeDivWeight e (ζ * F)` is the restricted weight `μ(n)/φ(n)`. -/
theorem coprimeMoebius_mul_transferWeight (e : ℕ) :
    coprimeDivWeight e (μ : ArithmeticFunction ℝ) * coprimeDivWeight e moebiusTotientDivisorSum
      = coprimeDivWeight e moebiusTotientNum := by
  rw [coprimeDivWeight_mul, moebiusTotientDivisorSum, ← mul_assoc, coe_moebius_mul_coe_zeta,
    one_mul]

/-- The summatory function of the restricted weight `μ/φ` is `T_e`. -/
theorem summatory_coprimeMoebiusTotient (e : ℕ) (t : ℝ) :
    summatory (coprimeDivWeight e moebiusTotientNum) t = moebiusTotientBelow e t := by
  rw [summatory, moebiusTotientBelow, coprimeBelow, sum_filter, ← Icc_add_one_left_eq_Ioc]
  refine sum_congr rfl fun n hn ↦ ?_
  have hn : n ≠ 0 := (mem_Ioc.mp hn).1.ne'
  have := Nat.totient_pos.mpr hn.bot_lt
  rw [coprimeDivWeight_apply, moebiusTotientNum_apply hn]
  split_ifs <;> field_simp

/-- **The hyperbola form** `T_e(w) = ∑_{n ≤ w} g_e(n) · A_e(w/n)`. -/
theorem moebiusTotientBelow_eq_sum (e : ℕ) (w : ℝ) :
    moebiusTotientBelow e w
      = ∑ n ∈ Finset.Ioc 0 ⌊w⌋₊,
          coprimeDivWeight e moebiusTotientDivisorSum n * moebiusReciprocalBelow e (w / n) := by
  rw [← summatory_coprimeMoebiusTotient, summatory, ← coprimeMoebius_mul_transferWeight,
    mul_comm (coprimeDivWeight e (μ : ArithmeticFunction ℝ)), summatory_hyperbola]
  simp only [summatory_coprimeMoebius]

/-- `√n · |g_e n|`. -/
noncomputable def transferAbsWeight (e n : ℕ) : ℝ :=
  Real.sqrt n * |coprimeDivWeight e moebiusTotientDivisorSum n|

/-- `H_e` is nonnegative: it is a square root times an absolute value. -/
theorem transferAbsWeight_nonneg (e n : ℕ) : 0 ≤ transferAbsWeight e n :=
  mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)

/-- `H_e 0 = 0`, which the Euler-product lemma requires. -/
theorem transferAbsWeight_zero (e : ℕ) : transferAbsWeight e 0 = 0 := by
  simp [transferAbsWeight]

/-- `H_e 1 = 1`, the normalisation the Euler-product lemma requires. -/
theorem transferAbsWeight_one (e : ℕ) : transferAbsWeight e 1 = 1 := by
  rw [transferAbsWeight,
    (isMultiplicative_coprimeDivWeight e isMultiplicative_moebiusTotientDivisorSum).map_one]
  simp

/-- `H_e` is multiplicative on coprime arguments: `√·` is completely multiplicative, `g_e` is
multiplicative by `Gap212.Sieve.isMultiplicative_coprimeDivWeight`, and `|·|` respects products. -/
theorem transferAbsWeight_mul_of_coprime (e : ℕ) {m n : ℕ} (h : Nat.Coprime m n) :
    transferAbsWeight e (m * n) = transferAbsWeight e m * transferAbsWeight e n := by
  rw [transferAbsWeight, transferAbsWeight, transferAbsWeight,
    (isMultiplicative_coprimeDivWeight e isMultiplicative_moebiusTotientDivisorSum).2 h,
    abs_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m)]
  ring

/-- **The local values.** For `a ≥ 1`, `H_e(p^a) = 1/((p-1)(√p)^a)` when `p` is coprime to `e`,
and `0` otherwise. This is where the `√n` weight pays: without it the local series would be
`∑_a 1/((p-1)p^a)`, summable all the same, but the resulting bound on `∑_{n ≤ y} |g_e n|` carries
no rate in `y`, which the far range of the split needs. -/
theorem transferAbsWeight_prime_pow (e : ℕ) {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : 1 ≤ j) :
    transferAbsWeight e (p ^ j)
      = if Nat.Coprime (p ^ j) e then 1 / (((p : ℝ) - 1) * Real.sqrt p ^ j) else 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hsp := Real.sqrt_pos.mpr (zero_lt_one.trans hp1)
  have hcast : ((p ^ j : ℕ) : ℝ) = Real.sqrt p ^ j * Real.sqrt p ^ j := by
    rw [← mul_pow, Real.mul_self_sqrt (by positivity), Nat.cast_pow]
  rw [transferAbsWeight, coprimeDivWeight_apply, hcast, Real.sqrt_mul_self (by positivity)]
  split
  · rw [moebiusTotientDivisorSum_prime_pow hp hj, abs_div, abs_div, abs_neg, abs_one,
      abs_of_pos (by linarith : (0 : ℝ) < p - 1), abs_of_pos (by positivity)]
    field_simp
  · simp

/-- `H_e(p^a) ≤ (1/√p)^a`: the local series is dominated by a geometric one of ratio
`1/√p < 1`, which is what makes it summable. -/
theorem transferAbsWeight_prime_pow_le (e : ℕ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    transferAbsWeight e (p ^ j) ≤ (1 / Real.sqrt p) ^ j := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simpa using (transferAbsWeight_one e).le
  rw [transferAbsWeight_prime_pow e hp hj, div_pow, one_pow]
  split
  · refine one_div_le_one_div_of_le (pow_pos hsp j) ?_
    nlinarith [pow_pos hsp j]
  · positivity

/-- `H_e(p^{a+1}) ≤ (1/((p-1)√p))·(1/√p)^a`: the same geometric domination with the factor
`1/(p-1)` kept, which is what makes the sum over primes of the local excess converge. -/
theorem transferAbsWeight_prime_pow_succ_le (e : ℕ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    transferAbsWeight e (p ^ (j + 1))
      ≤ 1 / (((p : ℝ) - 1) * Real.sqrt p) * (1 / Real.sqrt p) ^ j := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [transferAbsWeight_prime_pow e hp (Nat.le_add_left 1 j), div_pow, one_pow]
  split
  · exact le_of_eq (by rw [pow_succ]; field_simp)
  · positivity

/-- The comparison series `8/(k√k)`. -/
noncomputable def transferTailBound (k : ℕ) : ℝ := 8 / ((k : ℝ) * Real.sqrt k)

/-- `8/(k√k) ≥ 0`, with the value `0` at `k = 0`. -/
theorem transferTailBound_nonneg (k : ℕ) : 0 ≤ transferTailBound k :=
  div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg k) (Real.sqrt_nonneg _))

/-- `∑_k 8/(k√k) < ∞`, by comparison with `∑_k k^{-3/2}`. -/
theorem summable_transferTailBound : Summable transferTailBound := by
  have h : Summable (fun k : ℕ => 8 * (1 / (k : ℝ) ^ (3 / 2 : ℝ))) :=
    (Real.summable_one_div_nat_rpow.mpr (by norm_num)).mul_left 8
  refine h.congr fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num [Real.zero_rpow, transferTailBound]
  · have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    rw [transferTailBound, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hk0,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    ring

/-- The local series of `H_e` at a prime is summable, being dominated by a geometric series. -/
theorem summable_transferAbsWeight_prime_pow (e : ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ => ‖transferAbsWeight e (p ^ j)‖) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hsp : 1 < Real.sqrt p := by rw [Real.lt_sqrt zero_le_one]; linarith
  refine .of_nonneg_of_le (fun j ↦ norm_nonneg _) (fun j ↦ ?_)
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one (by linarith)).mpr hsp))
  rw [Real.norm_of_nonneg (transferAbsWeight_nonneg e _)]
  exact transferAbsWeight_prime_pow_le e hp j

/-- **The local factor bound** `∑_{a ≥ 0} H_e(p^a) ≤ exp(8/(p√p))`. Summing the geometric tail
gives `1 + 4/((p-1)√p)`; then `p - 1 ≥ p/2` turns that into `1 + 8/(p√p)`, which `1 + x ≤ exp x`
converts into the exponential shape `Gap212.Sieve.exists_sum_transferAbsWeight_le` consumes. -/
theorem tsum_transferAbsWeight_prime_pow_le (e : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, transferAbsWeight e (p ^ j)) ≤ Real.exp (transferTailBound p) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hsp0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  have hsp : 4 / 3 ≤ Real.sqrt p := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
  have hr0 : 0 ≤ 1 / Real.sqrt p := by positivity
  have hr1 : 1 / Real.sqrt p ≤ 3 / 4 := by
    rw [div_le_div_iff₀ hsp0 (by norm_num)]; linarith
  have hsum : Summable fun j : ℕ ↦ transferAbsWeight e (p ^ j) := by
    simpa [Real.norm_of_nonneg (transferAbsWeight_nonneg e _)] using
      summable_transferAbsWeight_prime_pow e hp
  have hinv : (1 - 1 / Real.sqrt p)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have htail : ∑' j : ℕ, transferAbsWeight e (p ^ (j + 1))
      ≤ 4 / (((p : ℝ) - 1) * Real.sqrt p) := by
    refine ((hsum.comp_injective (add_left_injective 1)).tsum_le_tsum
      (transferAbsWeight_prime_pow_succ_le e hp)
      ((summable_geometric_of_lt_one hr0 (by linarith)).mul_left _)).trans ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 (by linarith)]
    exact (mul_le_mul_of_nonneg_left hinv (by positivity)).trans_eq (by ring)
  have hstep : 4 / (((p : ℝ) - 1) * Real.sqrt p) ≤ transferTailBound p := by
    rw [transferTailBound, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [hsum.tsum_eq_zero_add, pow_zero, transferAbsWeight_one]
  linarith [Real.add_one_le_exp (transferTailBound p)]

/-- **The Euler-product bound**: there is one `Γ > 0` with `∑_{n ∈ u} √n |g_e(n)| ≤ Γ` for every
finite `u`. -/
theorem exists_sum_transferAbsWeight_le (e : ℕ) :
    ∃ Γ : ℝ, 0 < Γ ∧ ∀ u : Finset ℕ, ∑ n ∈ u, transferAbsWeight e n ≤ Γ :=
  ⟨_, Real.exp_pos _, PrimeGaps.MertensShared.finset_sum_le_exp_tsum_of_local _
    (transferAbsWeight_one e) (transferAbsWeight_zero e) (transferAbsWeight_nonneg e)
    (transferAbsWeight_mul_of_coprime e) (summable_transferAbsWeight_prime_pow e)
    transferTailBound transferTailBound_nonneg summable_transferTailBound
    (fun _ ↦ tsum_transferAbsWeight_prime_pow_le e)⟩

/-- The trivial bound `|A_e(y)| ≤ 1 + log y`. -/
theorem abs_moebiusReciprocalBelow_le (e : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    |moebiusReciprocalBelow e y| ≤ 1 + Real.log y := by
  rw [← summatory_coprimeMoebius, summatory]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  simpa using sum_abs_coprimeMoebius_le e hy

/-- `(1 + log w)^3 ≤ K √(√w)`. -/
theorem exists_one_add_log_cube_le_sqrt_sqrt : ∃ K : ℝ, 0 < K ∧ ∀ w : ℝ, 1 ≤ w →
    (1 + Real.log w) ^ 3 ≤ K * Real.sqrt (Real.sqrt w) := by
  obtain ⟨C, hC, hbd⟩ := exists_one_add_log_pow_le_mul 3
  refine ⟨64 * C, by positivity, fun w hw => ?_⟩
  have h := hbd _ (Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hw))
  rw [Real.log_sqrt (Real.sqrt_nonneg w), Real.log_sqrt (by linarith)] at h
  have := Real.log_nonneg hw
  calc (1 + Real.log w) ^ 3 ≤ (4 * (1 + Real.log w / 2 / 2)) ^ 3 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 3
    _ = 64 * (1 + Real.log w / 2 / 2) ^ 3 := by ring
    _ ≤ _ := by linarith

/-- Near-range bound: for `n ≤ √w`, `|g_e(n)| |A_e(w/n)| ≤ H_e(n) · 4 max(C,0)/(1+log w)²`. -/
theorem abs_mul_abs_moebiusReciprocalBelow_le_of_le_sqrt {e : ℕ} {C w : ℝ}
    (hC : ∀ y : ℝ, 1 ≤ y → |moebiusReciprocalBelow e y| ≤ C / (1 + Real.log y) ^ 2)
    (hw : 1 ≤ w) {n : ℕ} (hn1 : (1 : ℝ) ≤ n) (hdiv : 1 ≤ w / n) (hsq : (n : ℝ) ≤ Real.sqrt w) :
    |coprimeDivWeight e moebiusTotientDivisorSum n| * |moebiusReciprocalBelow e (w / n)|
      ≤ transferAbsWeight e n * (4 * max C 0 / (1 + Real.log w) ^ 2) := by
  have hw0 : (0 : ℝ) < w := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hL1 : (1 : ℝ) ≤ 1 + Real.log w := by linarith [Real.log_nonneg hw]
  have hLpos : (0 : ℝ) < (1 + Real.log w) ^ 2 := by positivity
  have hlogn := Real.log_le_log hn0 hsq
  rw [Real.log_sqrt hw0.le] at hlogn
  have hLd : (1 + Real.log w) / 2 ≤ 1 + Real.log (w / n) := by
    rw [Real.log_div hw0.ne' hn0.ne']; linarith
  have hAbd : |moebiusReciprocalBelow e (w / n)| ≤ 4 * max C 0 / (1 + Real.log w) ^ 2 := by
    refine (hC _ hdiv).trans ?_
    rw [div_le_div_iff₀ (by nlinarith) hLpos]
    have h1 : (1 + Real.log w) ^ 2 / 4 ≤ (1 + Real.log (w / n)) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (le_max_right C 0),
      mul_le_mul_of_nonneg_right (le_max_left C 0) hLpos.le]
  exact mul_le_mul (le_mul_of_one_le_left (abs_nonneg _) (Real.one_le_sqrt.mpr hn1))
    hAbd (abs_nonneg _) (transferAbsWeight_nonneg e n)

/-- Far-range termwise bound: for `√w < n ≤ w`,
`|g_e(n)| |A_e(w/n)| ≤ H_e(n) (1+log w)/w^{1/4}`. -/
theorem abs_mul_abs_moebiusReciprocalBelow_le_of_sqrt_lt {e : ℕ} {w : ℝ} (hw : 1 ≤ w) {n : ℕ}
    (hn1 : (1 : ℝ) ≤ n) (hdiv : 1 ≤ w / n) (hsq : Real.sqrt w < n) :
    |coprimeDivWeight e moebiusTotientDivisorSum n| * |moebiusReciprocalBelow e (w / n)|
      ≤ transferAbsWeight e n * ((1 + Real.log w) / Real.sqrt (Real.sqrt w)) := by
  have hw0 : (0 : ℝ) < w := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hqpos : (0 : ℝ) < Real.sqrt (Real.sqrt w) :=
    one_pos.trans_le (Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hw))
  have hAbd : |moebiusReciprocalBelow e (w / n)| ≤ 1 + Real.log w := by
    refine (abs_moebiusReciprocalBelow_le e hdiv).trans ?_
    linarith [Real.log_le_log (by positivity) (div_le_self hw0.le hn1)]
  calc _ ≤ |coprimeDivWeight e moebiusTotientDivisorSum n| * (1 + Real.log w) :=
        mul_le_mul_of_nonneg_left hAbd (abs_nonneg _)
    _ = transferAbsWeight e n * ((1 + Real.log w) / Real.sqrt n) := by
        rw [transferAbsWeight]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left
        (by linarith [Real.log_nonneg hw]) hqpos (Real.sqrt_le_sqrt hsq.le))
        (transferAbsWeight_nonneg e n)

/-- **`|T_e(w)| ≤ C (1 + log w)^{-2}`** for `w ≥ 1`, for some `C` depending on `e`. -/
theorem exists_moebiusTotientBelow_log_sq_decay {e : ℕ} (he : 1 ≤ e) :
    ∃ C : ℝ, ∀ w : ℝ, 1 ≤ w → |moebiusTotientBelow e w| ≤ C / (1 + Real.log w) ^ 2 := by
  obtain ⟨C, hC⟩ := exists_moebiusReciprocalBelow_log_sq_decay he
  obtain ⟨Γ, hΓ, hΓbd⟩ := exists_sum_transferAbsWeight_le e
  obtain ⟨K, hK, hKbd⟩ := exists_one_add_log_cube_le_sqrt_sqrt
  refine ⟨Γ * (4 * max C 0) + Γ * K, fun w hw => ?_⟩
  set g : ℕ → ℝ := fun n => coprimeDivWeight e moebiusTotientDivisorSum n with hg
  set L : ℝ := 1 + Real.log w with hL
  have hw0 : (0 : ℝ) < w := by linarith
  have hLpos : (0 : ℝ) < L ^ 2 := by nlinarith [Real.log_nonneg hw]
  have hqpos : (0 : ℝ) < Real.sqrt (Real.sqrt w) :=
    one_pos.trans_le (Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hw))
  have hbase : ∀ n ∈ Ioc 0 ⌊w⌋₊, (1 : ℝ) ≤ n ∧ 1 ≤ w / (n : ℝ) := by
    intro n hn
    obtain ⟨hn0, hnN⟩ := mem_Ioc.mp hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    exact ⟨hn1, (one_le_div (by linarith)).mpr
      ((Nat.cast_le.mpr hnN).trans (Nat.floor_le hw0.le))⟩
  have hlast : L / Real.sqrt (Real.sqrt w) ≤ K / L ^ 2 := by
    rw [div_le_div_iff₀ hqpos hLpos]
    nlinarith [hKbd w hw]
  calc |moebiusTotientBelow e w|
      ≤ ∑ n ∈ Ioc 0 ⌊w⌋₊, |g n| * |moebiusReciprocalBelow e (w / n)| := by
        rw [moebiusTotientBelow_eq_sum]
        exact (abs_sum_le_sum_abs _ _).trans_eq (by simp only [hg, abs_mul])
    _ = _ := (sum_filter_add_sum_filter_not _ (fun n : ℕ ↦ (n : ℝ) ≤ Real.sqrt w) _).symm
    _ ≤ ∑ n ∈ _, transferAbsWeight e n * (4 * max C 0 / L ^ 2)
        + ∑ n ∈ _, transferAbsWeight e n * (L / Real.sqrt (Real.sqrt w)) := by
        refine add_le_add (sum_le_sum fun n hn ↦ ?_) (sum_le_sum fun n hn ↦ ?_) <;>
          obtain ⟨hn, hsq⟩ := mem_filter.1 hn <;> obtain ⟨hn1, hdiv⟩ := hbase n hn
        · exact abs_mul_abs_moebiusReciprocalBelow_le_of_le_sqrt hC hw hn1 hdiv hsq
        · exact abs_mul_abs_moebiusReciprocalBelow_le_of_sqrt_lt hw hn1 hdiv (not_le.mp hsq)
    _ ≤ Γ * (4 * max C 0 / L ^ 2) + Γ * (K / L ^ 2) := by
        rw [← sum_mul, ← sum_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (hΓbd _) (by positivity))
          (mul_le_mul (hΓbd _) hlast
            (div_nonneg (by linarith [Real.log_nonneg hw]) hqpos.le) hΓ.le)
    _ = (Γ * (4 * max C 0) + Γ * K) / L ^ 2 := by ring

/-- **`Gap212.Sieve.MoebiusTotientPartialSumDecay` holds**, at `ε = 1`.

It follows from `Gap212.Sieve.moebiusPartialSumDecay`, the same statement for the weight `μ(f)/f`,
through the Dirichlet convolution `m_e * g_e = b_e`, whose kernel `g_e` is absolutely summable
against the weight `√n`. -/
@[gap212 "lem_moebius_totient_partial_sum_decay"]
theorem moebiusTotientPartialSumDecay : MoebiusTotientPartialSumDecay := by
  refine ⟨1, one_pos, fun e he => ?_⟩
  obtain ⟨C, hC⟩ := exists_moebiusTotientBelow_log_sq_decay he
  refine ⟨C, fun w hw => ?_⟩
  rw [one_add_one_eq_two, Real.rpow_two]
  exact hC w (by linarith)

end Gap212.Sieve
