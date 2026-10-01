/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MoebiusTotientAsymptotic
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# The reciprocal-weight Möbius Dirichlet series and its zero at `s = 0`

The truncated inner sum with reciprocal weight is governed by the Dirichlet series

  `g_q(s) = ∑_{(f,q)=1} μ(f) f^{-(1+s)} = ∏_{p ∤ q}(1 - p^{-1-s})`,

and the constant of the reciprocal-weight inner sum is the Abel integral
`∫_0^∞ S_q(exp u) du = lim_{s → 0⁺} g_q(s)/s`. Two things are proved here: the Euler product,
and that limit.

## Why the limit is `q/φ(q)`

`g_q` has a *simple zero* at `s = 0`, for **every** `q`. Splitting off the finitely many primes
dividing `q` gives `g_q(s) = g_1(s) / ∏_{p ∣ q}(1 - p^{-1-s})` with `g_1(s) = ζ(1+s)⁻¹`, and
`s ζ(1+s) → 1` is the residue of `ζ` at `1`. So `g_q(s)/s = (s ζ(1+s))⁻¹ / ∏_{p ∣ q}(1 - p^{-1-s})`
tends to `1 / (φ(q)/q) = q/φ(q)`.

Under the *totient* weight `μ(f)/φ(f)` the corresponding product carries
`1 - 1/((p-1)p^s)`, whose factor at `p = 2` vanishes to first order as `s → 0⁺`; the zero is then
double for odd `q` and the limit is `0`. That is the evenness hypothesis at the totient weight, and
it has no counterpart here: the reciprocal weight's zero is simple for every `q`, so
`q = 1` and `q = 3` behave as well as `q = 2`.

## The inner-sum asymptotic

The passage from `lim_{s→0⁺} g_q(s)/s` to `log x · Z_F(q) → -F'(0) q/φ(q)` needs dominated
convergence for the `v`-integral of `Gap212.Sieve.truncated_moebius_reciprocal_partial_summation`,
hence an integrable majorant for `u ↦ S_q(exp u)` on `[0, ∞)`. That majorant is
`Gap212.Sieve.MoebiusPartialSumDecay`, and the asymptotic is
`Gap212.Sieve.tendsto_logx_mul_innerSumReciprocal`.

## Main definitions

* `Gap212.Sieve.moebiusCoprimeTerm`: `μ(f) f^{-(1+s)}` on the `f` coprime to `q`, `0` elsewhere.
* `Gap212.Sieve.moebiusReciprocalSeries`: `g_q(s) = ∑_{(f,q)=1} μ(f) f^{-(1+s)}`.

## Main results

* `Gap212.Sieve.hasProd_moebiusReciprocalSeries`, `moebiusReciprocalSeries_eq_tprod`: the Euler
  product `g_q(s) = ∏_{p ∤ q}(1 - p^{-1-s})` for `s > 0`.
* `Gap212.Sieve.moebiusReciprocalSeries_mul_prod_primeFactors`:
  `g_q(s) ∏_{p ∣ q}(1 - p^{-1-s}) = g_1(s)`.
* `Gap212.Sieve.ofReal_moebiusReciprocalSeries_one`: `g_1(s) = ζ(1+s)⁻¹`.
* `Gap212.Sieve.tendsto_moebiusReciprocalSeries_div`: `g_q(s)/s → q/φ(q)` as `s → 0⁺`.
-/

@[expose] public section

open ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius

namespace Gap212.Sieve

/-- The summand of the reciprocal-weight Dirichlet series: `μ(f) f^{-(1+s)}` on the `f` coprime to
`q`, and `0` elsewhere. -/
noncomputable def moebiusCoprimeTerm (q : ℕ) (s : ℝ) (f : ℕ) : ℝ :=
  if Nat.Coprime f q then (μ f : ℝ) * (f : ℝ) ^ (-(1 + s)) else 0

/-- **The reciprocal-weight Möbius Dirichlet series** `g_q(s) = ∑_{(f,q)=1} μ(f) f^{-(1+s)}`. -/
noncomputable def moebiusReciprocalSeries (q : ℕ) (s : ℝ) : ℝ :=
  ∑' f : ℕ, moebiusCoprimeTerm q s f

/-- The term at `f = 0` vanishes. -/
theorem moebiusCoprimeTerm_zero (q : ℕ) (s : ℝ) : moebiusCoprimeTerm q s 0 = 0 := by
  simp [moebiusCoprimeTerm]

/-- The term at `f = 1` is `1`. -/
theorem moebiusCoprimeTerm_one (q : ℕ) (s : ℝ) : moebiusCoprimeTerm q s 1 = 1 := by
  simp [moebiusCoprimeTerm]

/-- `moebiusCoprimeTerm q s` is multiplicative on coprime arguments. -/
theorem moebiusCoprimeTerm_mul {q : ℕ} {s : ℝ} {m n : ℕ} (hmn : Nat.Coprime m n) :
    moebiusCoprimeTerm q s (m * n) = moebiusCoprimeTerm q s m * moebiusCoprimeTerm q s n := by
  simp only [moebiusCoprimeTerm, Nat.coprime_mul_iff_left, Nat.cast_mul, Int.cast_mul,
    isMultiplicative_moebius.map_mul_of_coprime hmn, Real.mul_rpow m.cast_nonneg n.cast_nonneg]
  split_ifs <;> first | ring1 | simp_all

/-- `|μ(f) f^{-(1+s)}| ≤ f^{-(1+s)}`, which is summable exactly when `s > 0`. -/
theorem summable_norm_moebiusCoprimeTerm (q : ℕ) {s : ℝ} (hs : 0 < s) :
    Summable fun f : ℕ => ‖moebiusCoprimeTerm q s f‖ := by
  have hb : Summable fun f : ℕ => (f : ℝ) ^ (-(1 + s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine hb.of_nonneg_of_le (fun _ => norm_nonneg _) fun f => ?_
  have hnn : (0 : ℝ) ≤ (f : ℝ) ^ (-(1 + s)) := by positivity
  have hmu : |(μ f : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
  unfold moebiusCoprimeTerm
  split_ifs
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
    exact mul_le_of_le_one_left hnn hmu
  · simpa using hnn

/-- The Euler factor: at a prime `p`, `∑_k μ(p^k) p^{-k(1+s)}` restricted to the classes coprime
to `q` is `1 - p^{-1-s}` when `p ∤ q` and `1` when `p ∣ q`. Only `k = 0` and `k = 1` contribute,
`μ` vanishing on higher prime powers. -/
theorem tsum_moebiusCoprimeTerm_prime_pow {q : ℕ} {s : ℝ} {p : ℕ} (hp : p.Prime) :
    ∑' k : ℕ, moebiusCoprimeTerm q s (p ^ k)
      = if p ∣ q then 1 else 1 - (p : ℝ) ^ (-(1 + s)) := by
  have hz : ∀ k ∉ ({0, 1} : Finset ℕ), moebiusCoprimeTerm q s (p ^ k) = 0 := fun k hk ↦ by
    simp_all [moebiusCoprimeTerm, moebius_apply_prime_pow hp]
  rw [tsum_eq_sum hz, Finset.sum_insert (by simp), Finset.sum_singleton, pow_zero, pow_one,
    moebiusCoprimeTerm_one, moebiusCoprimeTerm]
  by_cases hd : p ∣ q <;> simp [hd, hp.coprime_iff_not_dvd, moebius_apply_prime hp, sub_eq_add_neg]

/-- **The Euler product for the reciprocal-weight series.** For `s > 0`,
`g_q(s) = ∏_{p ∤ q}(1 - p^{-1-s})`, stated via `HasProd` over `ℕ` with the non-primes and the
primes dividing `q` contributing the factor `1`. -/
theorem hasProd_moebiusReciprocalSeries (q : ℕ) {s : ℝ} (hs : 0 < s) :
    HasProd (fun p : ℕ => if p.Prime ∧ ¬ p ∣ q then 1 - (p : ℝ) ^ (-(1 + s)) else 1)
      (moebiusReciprocalSeries q s) := by
  have h := EulerProduct.eulerProduct_hasProd_mulIndicator (f := moebiusCoprimeTerm q s)
    (moebiusCoprimeTerm_one q s) moebiusCoprimeTerm_mul
    (summable_norm_moebiusCoprimeTerm q hs) (moebiusCoprimeTerm_zero q s)
  refine h.congr_fun fun p => ?_
  by_cases hp : p.Prime <;> simp [hp, tsum_moebiusCoprimeTerm_prime_pow]

/-- The Euler product in `tprod` form. -/
theorem moebiusReciprocalSeries_eq_tprod (q : ℕ) {s : ℝ} (hs : 0 < s) :
    moebiusReciprocalSeries q s
      = ∏' p : ℕ, (if p.Prime ∧ ¬ p ∣ q then 1 - (p : ℝ) ^ (-(1 + s)) else 1) :=
  ((hasProd_moebiusReciprocalSeries q hs).tprod_eq).symm

/-- Each Euler factor is positive for `s > 0`. -/
theorem one_sub_rpow_pos {p : ℕ} (hp : p.Prime) {s : ℝ} (hs : 0 < s) :
    0 < 1 - (p : ℝ) ^ (-(1 + s)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have : (p : ℝ) ^ (-(1 + s)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  linarith

/-- **Splitting off the primes dividing `q`.** `g_q(s) ∏_{p ∣ q}(1 - p^{-1-s}) = g_1(s)`; the two
Euler products differ in exactly the finitely many factors indexed by the prime factors of `q`. -/
theorem moebiusReciprocalSeries_mul_prod_primeFactors {q : ℕ} (hq : q ≠ 0) {s : ℝ} (hs : 0 < s) :
    moebiusReciprocalSeries q s * ∏ p ∈ q.primeFactors, (1 - (p : ℝ) ^ (-(1 + s)))
      = moebiusReciprocalSeries 1 s := by
  have hC : HasProd (fun p : ℕ => if p.Prime ∧ p ∣ q then 1 - (p : ℝ) ^ (-(1 + s)) else 1)
      (∏ p ∈ q.primeFactors, (1 - (p : ℝ) ^ (-(1 + s)))) := by
    rw [← Finset.prod_ite_of_true (p := fun p ↦ p.Prime ∧ p ∣ q) (fun p hp ↦
      ⟨Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩) _ fun _ ↦ 1]
    exact hasProd_prod_of_ne_finset_one fun p hp ↦
      if_neg fun hh ↦ hp (Nat.mem_primeFactors.2 ⟨hh.1, hh.2, hq⟩)
  refine ((hasProd_moebiusReciprocalSeries q hs).mul hC).unique
    ((hasProd_moebiusReciprocalSeries 1 hs).congr_fun fun p => ?_)
  simp only [Nat.dvd_one]
  split_ifs <;> simp_all [Nat.Prime.ne_one]

/-! ### The value at `q = 1`, and the residue of `ζ` -/

/-- `g_1(s) = ζ(1+s)⁻¹` for `s > 0`: the series is the `L`-series of `μ`, which inverts `ζ`. -/
theorem ofReal_moebiusReciprocalSeries_one {s : ℝ} (hs : 0 < s) :
    ((moebiusReciprocalSeries 1 s : ℝ) : ℂ) = (riemannZeta (1 + (s : ℂ)))⁻¹ := by
  have hre : 1 < (1 + (s : ℂ)).re := by simp [hs]
  have hLm : LSeries (fun n => (μ n : ℂ)) (1 + (s : ℂ)) = (riemannZeta (1 + (s : ℂ)))⁻¹ := by
    have h := LSeries_one_mul_Lseries_moebius hre
    rw [LSeries_one_eq_riemannZeta hre] at h
    have hζ : riemannZeta (1 + (s : ℂ)) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre
    field_simp
    linear_combination h
  rw [← hLm, moebiusReciprocalSeries, Complex.ofReal_tsum, LSeries]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [moebiusCoprimeTerm_zero]
  · rw [LSeries.term_of_ne_zero hn, moebiusCoprimeTerm, if_pos (Nat.coprime_one_right n)]
    have hcast : (((n : ℝ) ^ (-(1 + s)) : ℝ) : ℂ) = ((n : ℂ) ^ (1 + (s : ℂ)))⁻¹ := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      rw [Complex.cpow_neg]
    push_cast
    rw [hcast, div_eq_mul_inv]

/-- `s ζ(1+s) → 1` as `s → 0⁺` along the reals: the residue of `ζ` at `1`. -/
theorem tendsto_mul_riemannZeta_one_add :
    Tendsto (fun s : ℝ => (s : ℂ) * riemannZeta (1 + (s : ℂ))) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 1) := by
  have hz : Tendsto (fun s : ℝ => 1 + (s : ℂ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_const.add Complex.continuous_ofReal).tendsto' 0 1 (by simp)).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      simpa using hs.ne'
  exact (riemannZeta_residue_one.comp hz).congr fun s => by simp

/-- `g_1(s)/s → 1` as `s → 0⁺`: the simple zero of `ζ(1+s)⁻¹` at `s = 0`. -/
theorem tendsto_moebiusReciprocalSeries_one_div :
    Tendsto (fun s : ℝ => moebiusReciprocalSeries 1 s / s) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 1) := by
  have h := tendsto_mul_riemannZeta_one_add.inv₀ one_ne_zero
  rw [inv_one] at h
  have h' : Tendsto (fun s : ℝ => ((moebiusReciprocalSeries 1 s / s : ℝ) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [mul_inv, ← ofReal_moebiusReciprocalSeries_one hs]
    push_cast
    rw [div_eq_mul_inv, mul_comm]
  simpa [Function.comp_def] using (Complex.continuous_re.tendsto (1 : ℂ)).comp h'

/-! ### The limit -/

/-- The finite product over the primes dividing `q` is continuous at `s = 0`, with value
`φ(q)/q`. -/
theorem tendsto_prod_primeFactors_one_sub_rpow {q : ℕ} (hq : q ≠ 0) :
    Tendsto (fun s : ℝ => ∏ p ∈ q.primeFactors, (1 - (p : ℝ) ^ (-(1 + s))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((q.totient : ℝ) / (q : ℝ))) := by
  rw [totient_div_eq_prod_one_sub_inv hq]
  refine tendsto_finsetProd _ fun p hp ↦ ?_
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have h : ContinuousAt (fun s : ℝ ↦ 1 - (p : ℝ) ^ (-(1 + s))) 0 :=
    continuousAt_const.sub ((Real.continuousAt_const_rpow hp0).comp
      (f := fun s : ℝ ↦ -(1 + s)) (by fun_prop))
  simpa [Real.rpow_neg_one] using h.tendsto.mono_left nhdsWithin_le_nhds

/-- For `s > 0`, the product `∏_{p ∣ q} (1 - p^{-(1+s)})` is positive. -/
theorem prod_primeFactors_one_sub_rpow_pos {q : ℕ} {s : ℝ} (hs : 0 < s) :
    0 < ∏ p ∈ q.primeFactors, (1 - (p : ℝ) ^ (-(1 + s))) :=
  Finset.prod_pos fun _ hp => one_sub_rpow_pos (Nat.prime_of_mem_primeFactors hp) hs

/-- **The Abel constant of the reciprocal-weight inner sum.** For `q ≥ 1`,
`g_q(s)/s → q/φ(q)` as `s → 0⁺`.

This is `lim_{s→0⁺} g_q(s)/s = q/φ(q)`, with `g_q(s) = ∏_{p ∤ q}(1 - p^{-1-s})`. The zero of `g_q`
at `s = 0` is simple for **every** `q`: no evenness hypothesis, no
`∏(1 - 1/(p-1)²)` correction, and the constant is the bare `q/φ(q)`. -/
theorem tendsto_moebiusReciprocalSeries_div {q : ℕ} (hq : 1 ≤ q) :
    Tendsto (fun s : ℝ => moebiusReciprocalSeries q s / s) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((q : ℝ) / (q.totient : ℝ))) := by
  have hq0 : q ≠ 0 := by lia
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlim : Tendsto (fun s : ℝ => (moebiusReciprocalSeries 1 s / s)
      / ∏ p ∈ q.primeFactors, (1 - (p : ℝ) ^ (-(1 + s)))) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((q : ℝ) / (q.totient : ℝ))) := by
    have h := tendsto_moebiusReciprocalSeries_one_div.div
      (tendsto_prod_primeFactors_one_sub_rpow hq0) (by positivity)
    rwa [one_div_div] at h
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have hP := prod_primeFactors_one_sub_rpow_pos (q := q) hs
  rw [← moebiusReciprocalSeries_mul_prod_primeFactors hq0 hs]
  field_simp

end Gap212.Sieve
