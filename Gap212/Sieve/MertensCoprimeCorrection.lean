/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.BigOperators.Field

/-!
# The non-coprime part of Mertens' sum

Mertens' theorem for `Λ` is a statement about `∑_{k ≤ y} Λ(k)/k`, whereas a sieve over residues
mod `q` needs the same sum restricted to `k` **coprime** to `q`. The difference between the two is
the sum over `k` *not* coprime to `q`, and this file shows that the difference is harmless: it
converges, with an explicit `O(1/y)` rate, so the coprime-restricted Mertens sum inherits whatever
asymptotic the unrestricted one has, with the same error term up to `O(1/y)`.

The proof is entirely elementary and finite. `Λ k ≠ 0` only at prime powers `k = p^j` with `j ≥ 1`
(`ArithmeticFunction.vonMangoldt_eq_zero_iff`), and for such a `k` the condition
`¬ Nat.Coprime k q` says exactly `p ∣ q`, i.e. `p ∈ q.primeFactors`. Since a prime power determines
its prime, the restricted sum is a *disjoint* union over the finitely many `p ∈ q.primeFactors`:

`∑_{k ≤ Y, ¬coprime(k,q)} Λ(k)/k = ∑_{p ∈ q.primeFactors} ∑_{j=1}^{Nat.log p Y} (log p)/p^j`.

Each inner sum is a truncated geometric series, with tail

`(log p)/(p - 1) - ∑_{j=1}^{J} (log p)/p^j = (log p)/((p - 1) p^J)`,

so the limit is `d = ∑_{p ∈ q.primeFactors} (log p)/(p - 1)` and the defect at truncation
`J = Nat.log p Y` is controlled by `Y < p^{J+1}`: that gives `p^{-J} < p/Y`, and `p/(p-1) ≤ 2` for
`p ≥ 2`, so each prime contributes at most `2 (log p)/Y`. Summing over `q.primeFactors` and
comparing `Y = ⌊y⌋₊` with `y` produces the rate.

The `1 ≤ y < 2` range is degenerate rather than delicate: there `⌊y⌋₊ = 1`, the index set
`Finset.Ioc 0 1 = {1}` contains only `1`, and `1` *is* coprime to `q`, so the sum is empty and the
claim reduces to `d ≤ K/y`, which holds for any `K ≥ 2d` because `y ≤ 2`.

## Main results

* `Gap212.Sieve.sum_vonMangoldt_div_not_coprime_eq`: the reindexing, from a sum over non-coprime
  integers `≤ Y` to a double sum over `q.primeFactors` and exponents.
* `Gap212.Sieve.abs_sum_vonMangoldt_div_not_coprime_sub_le`: the `O(1/Y)` bound at integer
  truncation, with the explicit limit `d` and constant `2 ∑_{p ∣ q} log p`.
* `Gap212.Sieve.exists_sum_vonMangoldt_div_not_coprime_rate`: the non-coprime part of Mertens'
  sum converges at rate `1/y`.
-/

@[expose] public section

open scoped ArithmeticFunction

namespace Gap212.Sieve

/-- Membership in the prime-power index set `⋃_{p ∣ q} {p^j : 1 ≤ j ≤ Nat.log p Y}` is exactly
membership in `Finset.Ioc 0 Y` together with non-coprimality to `q` and `Λ k ≠ 0`.

Both directions are used: left-to-right says the index set really sits inside the range being
summed over, and right-to-left says every term outside the index set has `Λ k = 0`, so dropping
them changes nothing. -/
private lemma mem_primeFactors_biUnion_iff {q Y : ℕ} (hq : 1 ≤ q) (hY : 1 ≤ Y) (k : ℕ) :
    k ∈ q.primeFactors.biUnion (fun p => (Finset.Icc 1 (Nat.log p Y)).image (p ^ ·)) ↔
      (0 < k ∧ k ≤ Y ∧ ¬ Nat.Coprime k q ∧ Λ k ≠ 0) := by
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_Icc, Nat.mem_primeFactors]
  constructor
  · rintro ⟨p, ⟨hp, hpq, -⟩, j, ⟨hj1, hj2⟩, rfl⟩
    have hj0 : j ≠ 0 := by lia
    refine ⟨pow_pos hp.pos j, Nat.pow_le_of_le_log (by lia) hj2, fun hco ↦ hp.coprime_iff_not_dvd.mp
      (Nat.Coprime.coprime_dvd_left (dvd_pow_self p hj0) hco) hpq, ?_⟩
    rw [ArithmeticFunction.vonMangoldt_apply_pow hj0, ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  · rintro ⟨-, hkY, hkco, hkΛ⟩
    obtain ⟨p, j, hp, hj, rfl⟩ :=
      (isPrimePow_nat_iff k).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hkΛ)
    have hpq : p ∣ q := not_not.mp fun h ↦ hkco (.pow_left j (hp.coprime_iff_not_dvd.mpr h))
    exact ⟨p, ⟨hp, hpq, by lia⟩, j, ⟨hj, Nat.le_log_of_pow_le hp.one_lt hkY⟩, rfl⟩

/-- **The reindexing.** The von Mangoldt reciprocal sum over the integers `≤ Y` that are not
coprime to `q` is the double sum over `p ∈ q.primeFactors` and `1 ≤ j ≤ Nat.log p Y` of
`(log p)/p^j`.

The union is disjoint because a prime power `p^j` with `j ≥ 1` determines `p`. -/
theorem sum_vonMangoldt_div_not_coprime_eq {q Y : ℕ} (hq : 1 ≤ q) (hY : 1 ≤ Y) :
    (∑ k ∈ Finset.Ioc 0 Y with ¬ Nat.Coprime k q, Λ k / k)
      = ∑ p ∈ q.primeFactors, ∑ j ∈ Finset.Icc 1 (Nat.log p Y), Real.log p / (p : ℝ) ^ j := by
  classical
  set T : Finset ℕ := q.primeFactors.biUnion (fun p => (Finset.Icc 1 (Nat.log p Y)).image (p ^ ·))
    with hT
  set S : Finset ℕ := {k ∈ Finset.Ioc 0 Y | ¬ Nat.Coprime k q} with hS
  have hdisj : (↑q.primeFactors : Set ℕ).PairwiseDisjoint
      (fun p => (Finset.Icc 1 (Nat.log p Y)).image (p ^ ·)) := by
    intro p hp r hr hpr
    have hp' := Nat.prime_of_mem_primeFactors hp
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image, Finset.mem_Icc]
    rintro k ⟨i, ⟨hi1, -⟩, rfl⟩ ⟨j, ⟨hj1, -⟩, hj⟩
    exact hpr <| (Nat.prime_dvd_prime_iff_eq hp' (Nat.prime_of_mem_primeFactors hr)).mp
      (hp'.dvd_of_dvd_pow (hj ▸ dvd_pow_self p (by lia)))
  have hTS : T ⊆ S := fun k hk ↦ by
    obtain ⟨hk0, hkY, hkco, -⟩ := (mem_primeFactors_biUnion_iff hq hY k).mp hk
    exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨hk0, hkY⟩, hkco⟩
  have hzero : ∀ k ∈ S, k ∉ T → Λ k / (k : ℝ) = 0 := fun k hk hk' ↦ by
    simp only [hS, Finset.mem_filter, Finset.mem_Ioc] at hk
    rw [not_not.mp fun h ↦ hk' ((mem_primeFactors_biUnion_iff hq hY k).mpr
      ⟨hk.1.1, hk.1.2, hk.2, h⟩), zero_div]
  rw [← Finset.sum_subset hTS hzero, hT, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  rw [Finset.sum_image (fun i _ j _ h => Nat.pow_right_injective hp'.two_le h)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.1 hj).1),
    ArithmeticFunction.vonMangoldt_apply_prime hp']
  push_cast
  ring

/-- The truncated geometric series `∑_{j=1}^{J} p^{-j} = 1/(p-1) - 1/((p-1) p^J)`, for `p > 1`.

Proved by induction on `J`, which avoids the coercion bookkeeping of `Finset.geom_sum_eq`. -/
private lemma sum_one_div_pow {p : ℝ} (hp : 1 < p) (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, 1 / p ^ j = 1 / (p - 1) - 1 / ((p - 1) * p ^ J) := by
  have hp0 : p ≠ 0 := by positivity
  have hp1 : p - 1 ≠ 0 := sub_ne_zero_of_ne (by linarith)
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_Icc_succ_top (by lia), ih]
    field_simp
    ring

/-- The defect of the truncated geometric series at `J`, scaled by `log p`:
`(log p)/(p-1) - ∑_{j=1}^{J} (log p)/p^j = (log p)/((p-1) p^J)`. -/
private lemma log_div_sub_sum_eq {p : ℝ} (hp : 1 < p) (J : ℕ) :
    Real.log p / (p - 1) - ∑ j ∈ Finset.Icc 1 J, Real.log p / p ^ j
      = Real.log p / ((p - 1) * p ^ J) := by
  have hp0 : p ≠ 0 := by positivity
  have hp1 : p - 1 ≠ 0 := sub_ne_zero_of_ne (by linarith)
  have h : ∑ j ∈ Finset.Icc 1 J, Real.log p / p ^ j
      = Real.log p * ∑ j ∈ Finset.Icc 1 J, 1 / p ^ j := by
    simp_rw [Finset.mul_sum, mul_one_div]
  rw [h, sum_one_div_pow hp J]
  field_simp
  ring

/-- The per-prime defect is at most `2 (log p)/Y`.

`Nat.log p Y` is maximal with `p^J ≤ Y`, so `Y < p^{J+1} = p · p^J`; hence
`p^{-J} < p/Y` and `p/(p-1) ≤ 2` for `p ≥ 2`. -/
private lemma log_div_mul_pow_log_le {p Y : ℕ} (hp : 2 ≤ p) (hY : 1 ≤ Y) :
    Real.log p / (((p : ℝ) - 1) * (p : ℝ) ^ Nat.log p Y) ≤ 2 * Real.log p / Y := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpJ : (0 : ℝ) < (p : ℝ) ^ Nat.log p Y := by positivity
  have hlt : (Y : ℝ) < p * p ^ Nat.log p Y := by
    exact_mod_cast pow_succ' p _ ▸ Nat.lt_pow_succ_log_self (by lia) Y
  rw [div_le_div_iff₀ (mul_pos (by linarith) hpJ) (by exact_mod_cast hY)]
  nlinarith [mul_le_mul_of_nonneg_left (by nlinarith : (Y : ℝ) ≤ 2 * ((p - 1) * p ^ Nat.log p Y))
    (Real.log_nonneg (by linarith : (1 : ℝ) ≤ p))]

/-- **The `O(1/Y)` bound at integer truncation.** For `1 ≤ q` and `1 ≤ Y`,

`|∑_{k ≤ Y, ¬coprime(k,q)} Λ(k)/k - ∑_{p ∣ q} (log p)/(p-1)| ≤ (2 ∑_{p ∣ q} log p)/Y`,

the sums over `p` running over `q.primeFactors`. The limit is approached from below: each prime's
contribution is a truncation of an increasing geometric series. -/
theorem abs_sum_vonMangoldt_div_not_coprime_sub_le {q Y : ℕ} (hq : 1 ≤ q) (hY : 1 ≤ Y) :
    |(∑ k ∈ Finset.Ioc 0 Y with ¬ Nat.Coprime k q, Λ k / k)
        - ∑ p ∈ q.primeFactors, Real.log p / ((p : ℝ) - 1)|
      ≤ (2 * ∑ p ∈ q.primeFactors, Real.log p) / Y := by
  have hstep : ∀ p ∈ q.primeFactors, (2 : ℝ) ≤ (p : ℝ) := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  rw [sum_vonMangoldt_div_not_coprime_eq hq hY, abs_sub_comm, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun p hp ↦ log_div_sub_sum_eq (by linarith [hstep p hp]) _,
    abs_of_nonneg (Finset.sum_nonneg fun p hp ↦ div_nonneg (Real.log_nonneg
      (by linarith [hstep p hp])) (mul_nonneg (by linarith [hstep p hp]) (by positivity))),
    Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_le_sum fun p hp ↦
    log_div_mul_pow_log_le (Nat.prime_of_mem_primeFactors hp).two_le hY

/-- **The non-coprime part of Mertens' sum converges at rate `1/y`.** For a fixed modulus `q ≥ 1`
there are a real `d` and a constant `K ≥ 0` with

`|∑_{k ≤ y, ¬coprime(k,q)} Λ(k)/k - d| ≤ K/y` for every `y ≥ 1`.

Explicitly `d = ∑_{p ∈ q.primeFactors} (log p)/(p - 1)` and `K = 4 ∑_{p ∈ q.primeFactors} log p +
2 d` work; only the existence is asserted.

This is what lets a Mertens asymptotic for the unrestricted sum be transferred to the sum
restricted to `k` coprime to `q`: the two differ by this sum, which is `d + O(1/y)`. -/
theorem exists_sum_vonMangoldt_div_not_coprime_rate {q : ℕ} (hq : 1 ≤ q) :
    ∃ d K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
      |(∑ k ∈ Finset.Ioc 0 ⌊y⌋₊ with ¬ Nat.Coprime k q, Λ k / k) - d| ≤ K / y := by
  have hlog : ∀ p ∈ q.primeFactors, 0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  set C : ℝ := ∑ p ∈ q.primeFactors, Real.log p
  set d : ℝ := ∑ p ∈ q.primeFactors, Real.log p / ((p : ℝ) - 1)
  have hC0 : 0 ≤ C := Finset.sum_nonneg hlog
  have hd0 : 0 ≤ d := Finset.sum_nonneg fun p hp ↦ div_nonneg (hlog p hp) <| sub_nonneg.2 <| by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
  refine ⟨d, 4 * C + 2 * d, by linarith, fun y hy => ?_⟩
  have hy0 : (0 : ℝ) < y := by linarith
  rcases lt_or_ge y 2 with hy2 | hy2
  · have hfl : ⌊y⌋₊ = 1 :=
      Nat.floor_eq_iff (by linarith) |>.mpr ⟨by exact_mod_cast hy, by push_cast; linarith⟩
    simp only [hfl, Nat.Ioc_succ_singleton, zero_add, Finset.filter_singleton, Nat.gcd_one_left,
      ne_eq, not_true_eq_false, ↓reduceIte, Finset.sum_empty, zero_sub, abs_neg,
      abs_of_nonneg hd0, le_div_iff₀ hy0]
    nlinarith
  · have hYn : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
    have hYlt : y - 1 < (⌊y⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one y]
    have hY0 : (0 : ℝ) < (⌊y⌋₊ : ℝ) := by linarith
    refine (abs_sum_vonMangoldt_div_not_coprime_sub_le hq hYn).trans ?_
    rw [div_le_div_iff₀ hY0 hy0]
    nlinarith [mul_nonneg hd0 hY0.le,
      mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ (⌊y⌋₊ : ℝ) - y / 2)]

end Gap212.Sieve
