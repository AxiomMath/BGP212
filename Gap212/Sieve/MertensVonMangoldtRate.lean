/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.Mertens.CoprimeHarmonic
public import PrimeNumberTheoremAnd.MediumPNT

/-!
# Mertens' first theorem with a log-power rate

`∑_{k ≤ y} Λ(k)/k = log y + c + O((1 + log y)^{-m})` for every fixed `m : ℕ`, with a constant `c`.

The elementary Mertens estimate gives an error `O(1)`, and the sharpening to `o(1)` is already a
prime-number-theorem statement; an error smaller than every power of the logarithm comes from the
error-term prime number theorem.

## The route

Write `R(y) = ψ(y) - y` for the Chebyshev error term.

1. `PrimeNumberTheoremAnd.MediumPNT` is
   `∃ c > 0, (ψ - id) =O[atTop] fun x ↦ x * exp (-c * (log x)^{1/10})`. Since
   `exp u ≥ (u/k)^k` for every `k ≥ 1` (`Gap212.Sieve.div_pow_le_exp`, itself just
   `Real.add_one_le_exp` raised to the `k`-th power), taking `k = 10 m` turns
   `exp (-c t^{1/10})` into `O(t^{-m})`, so the prime number theorem's saving beats every
   power of the logarithm: `Gap212.Sieve.exists_abs_psi_sub_self_le`.
2. A discrete Abel summation, `Gap212.Sieve.sum_vonMangoldt_div_eq`, converts the sum over
   `Λ(k)/k` into `ψ(N)/N + ∑_{n < N} ψ(n)/(n(n+1))`; it is proved by induction, from
   `ψ(n+1) - ψ(n) = Λ(n+1)` and `1/n - 1/(n+1) = 1/(n(n+1))`.
3. Substituting `ψ(n) = n + R(n)` splits the second sum into the harmonic number `H_N` and a
   series in `R`. The harmonic constant with its rate is
   `PrimeGaps.harmonic_bound_int : |H_N - (log N + γ)| ≤ 1/N`.
4. The series `∑ R(n)/(n(n+1))` converges absolutely, with tail
   `O((1 + log N)^{-m})`: step 1 at exponent `m+1` bounds its terms by
   `K/(n (1 + log n)^{m+1})`, and `Gap212.Sieve.sum_Ioc_one_div_mul_one_add_log_pow_le`
   telescopes that against `1/(m (1 + log n)^m)` using the Bernoulli inequality
   `one_add_mul_le_pow` and `log(1 + 1/n) ≥ 1/(n+1)`.
5. Both the error `1/N` of step 3 and the passage from the integer `N = ⌊y⌋₊` to the real `y`
   are absorbed by `(1 + log N)^m ≤ m^m e N` (`Gap212.Sieve.one_add_log_pow_le`, again just
   `div_pow_le_exp`) and by `1 + log y ≤ 2 (1 + log N)`.

The constant is left anonymous: it is `γ` plus the value of the series in step 4.

## Main results

* `Gap212.Sieve.exists_abs_psi_sub_self_le`: `|ψ(y) - y| ≤ K y (1 + log y)^{-m}`, the
  error-term prime number theorem in log-power form.
* `Gap212.Sieve.sum_Ioc_one_div_mul_one_add_log_pow_le`: the tail bound
  `∑_{N < n ≤ M} 1/(n (1 + log n)^{m+1}) ≤ 1/(m (1 + log N)^m)`.
* `Gap212.Sieve.exists_sum_vonMangoldt_div_sub_log_rate`: **Mertens' first theorem with a
  log-power rate**, `|∑_{k ≤ y} Λ(k)/k - log y - c| ≤ K (1 + log y)^{-m}`.
-/

@[expose] public section

open Filter Finset Real
open scoped ArithmeticFunction Chebyshev

namespace Gap212.Sieve

/-! ### Elementary comparisons between `exp` and powers -/

/-- `(u/k)^k ≤ exp u` for `k ≥ 1` and `u ≥ 0`: the `k`-th power of `u/k ≤ exp (u/k)`. -/
theorem div_pow_le_exp (k : ℕ) (hk : 1 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    (u / k) ^ k ≤ Real.exp u := by
  calc (u / k) ^ k ≤ (Real.exp (u / k)) ^ k := by gcongr; linarith [Real.add_one_le_exp (u / k)]
    _ = Real.exp u := by rw [← Real.exp_nat_mul, mul_div_cancel₀ _ (by positivity)]

/-- `(1 + log y)^m ≤ m^m e y` for `y ≥ 1` and `m ≥ 1`: every power of the logarithm is
dominated by the argument. -/
theorem one_add_log_pow_le {m : ℕ} (hm : 1 ≤ m) {y : ℝ} (hy : 1 ≤ y) :
    (1 + Real.log y) ^ m ≤ (m:ℝ) ^ m * Real.exp 1 * y := by
  have h := div_pow_le_exp m hm (u := 1 + Real.log y) (by linarith [Real.log_nonneg hy])
  rw [Real.exp_add, Real.exp_log (by linarith), div_pow, div_le_iff₀ (by positivity)] at h
  exact h.trans_eq (by ring)

/-- `exp (-c t^{1/10}) = O(t^{-m})`, in the uniform form `≤ K (1 + t)^{-m}` on `t ≥ 0`. -/
theorem exists_exp_neg_rpow_le (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 ≤ t →
      Real.exp (-c * t ^ ((1:ℝ)/10)) ≤ K / (1 + t) ^ m := by
  have hle (t : ℝ) (ht : 0 ≤ t) : Real.exp (-c * t ^ ((1:ℝ)/10)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]; positivity
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨1, one_pos, fun t ht => by simpa using hle t ht⟩
  set k : ℕ := 10 * m with hkdef
  have hk1 : 1 ≤ k := by omega
  have hA : (0:ℝ) ≤ (k:ℝ) ^ k / c ^ k := by positivity
  refine ⟨2 ^ m * (1 + (k:ℝ) ^ k / c ^ k), by positivity, fun t ht => ?_⟩
  rcases le_or_gt t 1 with ht1 | ht1
  · refine (hle t ht).trans ?_
    rw [le_div_iff₀ (by positivity), one_mul]
    calc (1 + t) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ 2 ^ m * (1 + (k:ℝ) ^ k / c ^ k) := le_mul_of_one_le_right (by positivity) (by linarith)
  · have ht0 : (0:ℝ) < t := by linarith
    have hpow : (t ^ ((1:ℝ)/10)) ^ k = t ^ m := by
      rw [← Real.rpow_natCast (t ^ ((1:ℝ)/10)) k, ← Real.rpow_mul ht0.le, hkdef]
      push_cast
      rw [show (1:ℝ)/10 * (10 * (m:ℝ)) = (m:ℝ) by ring, Real.rpow_natCast]
    have hE : (c:ℝ) ^ k * t ^ m / (k:ℝ) ^ k ≤ Real.exp (c * t ^ ((1:ℝ)/10)) := by
      simpa only [div_pow, mul_pow, hpow] using
        div_pow_le_exp k hk1 (u := c * t ^ ((1:ℝ)/10)) (by positivity)
    calc Real.exp (-c * t ^ ((1:ℝ)/10))
        = (Real.exp (c * t ^ ((1:ℝ)/10)))⁻¹ := by rw [← Real.exp_neg, neg_mul]
      _ ≤ ((c:ℝ) ^ k * t ^ m / (k:ℝ) ^ k)⁻¹ := inv_anti₀ (by positivity) hE
      _ = ((k:ℝ) ^ k / c ^ k) / t ^ m := by rw [inv_div]; field_simp
      _ ≤ (1 + (k:ℝ) ^ k / c ^ k) / t ^ m := by gcongr; linarith
      _ = (2 ^ m * (1 + (k:ℝ) ^ k / c ^ k)) / (2 ^ m * t ^ m) := by
          rw [mul_div_mul_left _ _ (by positivity : (2:ℝ) ^ m ≠ 0)]
      _ ≤ (2 ^ m * (1 + (k:ℝ) ^ k / c ^ k)) / (1 + t) ^ m := by
          gcongr; rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) m

/-! ### The Chebyshev error term -/

/-- The crude two-sided Chebyshev bound `|ψ(y) - y| ≤ (log 4 + 5) y`, used on the compact
range where the prime number theorem's asymptotic statement says nothing. -/
theorem abs_psi_sub_self_le_crude {y : ℝ} (hy : 0 ≤ y) :
    |Chebyshev.psi y - y| ≤ (Real.log 4 + 5) * y := by
  have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> nlinarith [Chebyshev.psi_le_const_mul_self hy, Chebyshev.psi_nonneg y]

/-- `ψ(y) - y` decays faster than every power of the logarithm. -/
theorem exists_abs_psi_sub_self_le (m : ℕ) :
    ∃ K : ℝ, ∀ y : ℝ, 1 ≤ y → |Chebyshev.psi y - y| ≤ K * y / (1 + Real.log y) ^ m := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  obtain ⟨K₀, hK₀, hrate⟩ := exists_exp_neg_rpow_le m hc
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.1 hO
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 hC
  set y₁ : ℝ := max y₀ 1
  set B : ℝ := (1 + Real.log y₁) ^ m
  have hB0 : 0 < B := pow_pos (by linarith [Real.log_nonneg (le_max_right y₀ 1)]) m
  refine ⟨max (|C| * K₀) ((Real.log 4 + 5) * B), fun y hy => ?_⟩
  have hly : (0:ℝ) ≤ Real.log y := Real.log_nonneg hy
  have hden : (0:ℝ) < (1 + Real.log y) ^ m := pow_pos (by linarith) m
  have hy0 : (0:ℝ) < y := by linarith
  rw [le_div_iff₀ hden]
  rcases le_or_gt y y₁ with hcase | hcase
  · calc |Chebyshev.psi y - y| * (1 + Real.log y) ^ m ≤ (Real.log 4 + 5) * y * B := by
          gcongr
          · exact abs_psi_sub_self_le_crude hy0.le
          · exact pow_le_pow_left₀ (by linarith) (by linarith [Real.log_le_log hy0 hcase]) m
      _ = (Real.log 4 + 5) * B * y := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · have h := hy₀ y ((le_max_left _ _).trans hcase.le)
    simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_mul, abs_of_pos hy0, Real.abs_exp] at h
    calc |Chebyshev.psi y - y| * (1 + Real.log y) ^ m
        ≤ |C| * (y * Real.exp (-c * Real.log y ^ ((1:ℝ)/10))) * (1 + Real.log y) ^ m := by
          gcongr
          exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
      _ ≤ |C| * (y * (K₀ / (1 + Real.log y) ^ m)) * (1 + Real.log y) ^ m := by
          gcongr; exact hrate _ hly
      _ = |C| * K₀ * y := by field_simp
      _ ≤ _ := by gcongr; exact le_max_left _ _

/-! ### Finset bookkeeping -/

/-- Reindexing a `Finset.range` sum as a sum over `Finset.Ioc`. -/
theorem sum_range_shift {M : Type*} [AddCommMonoid M] (g : ℕ → M) (N n : ℕ) :
    ∑ i ∈ Finset.range n, g (i + (N + 1)) = ∑ j ∈ Finset.Ioc N (N + n), g j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, show N + (n + 1) = N + n + 1 by omega,
        Finset.sum_Ioc_succ_top (Nat.le_add_right N n), show n + (N + 1) = N + n + 1 by omega]

/-- `∑_{n < N} 1/(n+1)` is the harmonic number `H_N`. -/
theorem sum_range_one_div_succ (N : ℕ) :
    ∑ n ∈ Finset.range N, (1:ℝ) / ((n : ℝ) + 1) = ∑ j ∈ Finset.Icc 1 N, (1:ℝ) / (j : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
      push_cast
      ring

/-! ### The tail of the comparison series -/

/-- The tail of `∑ 1/(n (1+log n)^(m+1))`. -/
theorem sum_Ioc_one_div_mul_one_add_log_pow_le {m : ℕ} (hm : 1 ≤ m) (N M : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc N M, 1 / ((n : ℝ) * (1 + Real.log n) ^ (m + 1))
      ≤ 1 / ((m : ℝ) * (1 + Real.log N) ^ m) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  set F : ℕ → ℝ := fun n => 1 / ((m : ℝ) * (1 + Real.log n) ^ m) with hFdef
  have hFpos (n : ℕ) : 0 < F n := by
    have := Real.log_natCast_nonneg n
    simp only [hFdef]
    positivity
  have key : ∀ n : ℕ, 1 ≤ n →
      1 / (((n + 1 : ℕ) : ℝ) * (1 + Real.log ((n + 1 : ℕ) : ℝ)) ^ (m + 1))
        ≤ F n - F (n + 1) := by
    intro n hn
    have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simp only [hFdef, Nat.cast_add, Nat.cast_one]
    set a : ℝ := 1 + Real.log (n : ℝ) with hadef
    set d : ℝ := 1 + Real.log ((n : ℝ) + 1) with hddef
    have ha1 : (1:ℝ) ≤ a := by linarith [Real.log_natCast_nonneg n]
    have had : a ≤ d := by linarith [Real.log_le_log (by linarith) (by linarith : (n : ℝ) ≤ n + 1)]
    have ha0 : 0 < a := by linarith
    have hd0 : 0 < d := by linarith
    have hda : 1 / ((n : ℝ) + 1) ≤ d - a := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (n : ℝ) / ((n : ℝ) + 1) by positivity)
      rw [Real.log_div (by linarith) (by linarith), div_sub_one (by linarith),
        sub_add_cancel_left, neg_div] at h
      linarith
    have hkey : (m : ℝ) * a ^ m * ((d - a) / a) ≤ d ^ m - a ^ m := by
      have h := one_add_mul_le_pow
        (show (-2:ℝ) ≤ (d - a) / a by linarith [div_nonneg (sub_nonneg.2 had) ha0.le]) m
      rw [show (1:ℝ) + (d - a) / a = d / a by field_simp; ring, div_pow,
        le_div_iff₀ (by positivity)] at h
      linarith
    calc 1 / (((n : ℝ) + 1) * d ^ (m + 1))
        = (1 / ((n : ℝ) + 1)) / d ^ (m + 1) := by rw [div_div]
      _ ≤ (d - a) / (a * d ^ m) := by
          gcongr
          rw [pow_succ']
          exact mul_le_mul_of_nonneg_right had (by positivity)
      _ = ((m : ℝ) * a ^ m * ((d - a) / a)) / ((m : ℝ) * a ^ m * d ^ m) := by field_simp
      _ ≤ (d ^ m - a ^ m) / ((m : ℝ) * a ^ m * d ^ m) := by gcongr
      _ = 1 / ((m : ℝ) * a ^ m) - 1 / ((m : ℝ) * d ^ m) := by field_simp
  have tele : ∀ M : ℕ, N ≤ M → ∑ n ∈ Finset.Ioc N M,
      1 / ((n : ℝ) * (1 + Real.log n) ^ (m + 1)) ≤ F N - F M := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
        rw [Finset.sum_Ioc_succ_top hM]
        linarith [key M (hN.trans hM)]
  rcases le_or_gt N M with h | h
  · exact (tele M h).trans (sub_le_self _ (hFpos M).le)
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    exact (hFpos N).le

/-! ### The discrete Abel summation -/

/-- `ψ(N) = ∑_{0 < n ≤ N} Λ(n)` at integer arguments. -/
theorem psi_natCast (N : ℕ) :
    Chebyshev.psi (N : ℝ) = ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n := by
  rw [Chebyshev.psi, Nat.floor_natCast]

/-- `ψ(N+1) = ψ(N) + Λ(N+1)`. -/
theorem psi_succ_natCast (N : ℕ) :
    Chebyshev.psi ((N + 1 : ℕ) : ℝ)
      = Chebyshev.psi (N : ℝ) + ArithmeticFunction.vonMangoldt (N + 1) := by
  rw [psi_natCast, psi_natCast, Finset.sum_Ioc_succ_top (Nat.zero_le N)]

/-- Abel summation for `∑ Λ(k)/k`:
`∑_{0 < k ≤ N} Λ(k)/k = ψ(N)/N + ∑_{n < N} ψ(n)/(n(n+1))`. -/
theorem sum_vonMangoldt_div_eq {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt k / (k : ℝ)
      = Chebyshev.psi (N : ℝ) / (N : ℝ)
        + ∑ n ∈ Finset.range N, Chebyshev.psi (n : ℝ) / ((n : ℝ) * ((n : ℝ) + 1)) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [ArithmeticFunction.vonMangoldt_apply_one, Chebyshev.psi_one]
  | succ N hN ih =>
      have hN0 : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), Finset.sum_range_succ, ih, psi_succ_natCast]
      push_cast
      field_simp
      ring

/-! ### Assembling Mertens' first theorem -/


/-- Mertens' first theorem with a log-power rate, for a positive exponent. The constant is
`γ` plus the value of the series `∑ (ψ(n) - n)/(n(n+1))`; it is never identified. -/
theorem exists_sum_vonMangoldt_div_sub_log_rate_of_one_le {m : ℕ} (hm : 1 ≤ m) :
    ∃ c K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
      |(∑ k ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt k / (k : ℝ))
          - Real.log y - c| ≤ K / (1 + Real.log y) ^ m := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  obtain ⟨K₁, hK₁⟩ := exists_abs_psi_sub_self_le (m + 1)
  have hK₁1 : (1:ℝ) ≤ K₁ := by
    have h1 := hK₁ 1 le_rfl
    norm_num [Chebyshev.psi_one] at h1
    linarith
  have hlog1 (n : ℕ) : (1:ℝ) ≤ 1 + Real.log (n : ℝ) := by linarith [Real.log_natCast_nonneg n]
  set w : ℕ → ℝ := fun n => (Chebyshev.psi (n : ℝ) - (n : ℝ)) / ((n : ℝ) * ((n : ℝ) + 1))
    with hwdef
  set v : ℕ → ℝ := fun n => 1 / ((n : ℝ) * (1 + Real.log (n : ℝ)) ^ (m + 1)) with hvdef
  have hvnn (n : ℕ) : 0 ≤ v n := by
    have := Real.log_natCast_nonneg n
    simp only [hvdef]
    positivity
  have hwv : ∀ n : ℕ, |w n| ≤ K₁ * v n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hwdef, hvdef]
    · have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hb := hlog1 n
      have hR := hK₁ (n : ℝ) hn1
      simp only [hwdef, abs_div, abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ) * ((n:ℝ) + 1) by positivity)]
      calc |Chebyshev.psi (n:ℝ) - (n:ℝ)| / ((n : ℝ) * ((n : ℝ) + 1))
          ≤ (K₁ * (n:ℝ) / (1 + Real.log (n:ℝ)) ^ (m + 1)) / ((n : ℝ) * ((n : ℝ) + 1)) := by
            gcongr
        _ = K₁ / ((1 + Real.log (n:ℝ)) ^ (m + 1) * ((n:ℝ) + 1)) := by field_simp
        _ ≤ K₁ / ((1 + Real.log (n:ℝ)) ^ (m + 1) * (n:ℝ)) := by gcongr; linarith
        _ = K₁ * v n := by simp only [hvdef]; field_simp
  have hsum_v : Summable v := by
    refine (summable_nat_add_iff 2).1 ?_
    refine summable_of_sum_range_le (c := 1 / ((m:ℝ) * (1 + Real.log ((1:ℕ):ℝ)) ^ m))
      (fun n => hvnn _) (fun n => ?_)
    have heq : ∑ i ∈ Finset.range n, v (i + 2) = ∑ j ∈ Finset.Ioc 1 (1 + n), v j := by
      simpa using sum_range_shift v 1 n
    rw [heq]
    simp only [hvdef]
    exact sum_Ioc_one_div_mul_one_add_log_pow_le hm 1 (1 + n) le_rfl
  have hsum_abs : Summable (fun n => |w n|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hwv (hsum_v.mul_left K₁)
  have hsum_w : Summable w := hsum_abs.of_abs
  have hvtail : ∀ N : ℕ, 1 ≤ N →
      ∑' i : ℕ, v (i + N) ≤ (1 + 1/(m:ℝ)) / (1 + Real.log (N:ℝ)) ^ m := by
    intro N hN
    have hb := hlog1 N
    have hn1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hvN : v N ≤ 1 / (1 + Real.log (N:ℝ)) ^ m := by
      simp only [hvdef]
      refine one_div_le_one_div_of_le (pow_pos (by linarith) m) ?_
      exact (pow_le_pow_right₀ hb m.le_succ).trans
        (le_mul_of_one_le_left (pow_pos (by linarith) _).le hn1)
    have htail : ∑' i : ℕ, v (i + (N + 1)) ≤ 1 / ((m:ℝ) * (1 + Real.log (N:ℝ)) ^ m) := by
      refine tsum_le_of_sum_range_le (fun i => hvnn _) (fun n => ?_)
      rw [sum_range_shift v N n]
      exact sum_Ioc_one_div_mul_one_add_log_pow_le hm N (N + n) hN
    have hsplit := ((summable_nat_add_iff N).2 hsum_v).tsum_eq_zero_add
    simp only [zero_add, add_assoc, add_comm 1 N] at hsplit
    rw [hsplit, add_div, div_div]
    linarith
  have hwtail : ∀ N : ℕ, 1 ≤ N →
      |∑' i : ℕ, w (i + N)| ≤ (K₁ * (1 + 1/(m:ℝ))) / (1 + Real.log (N:ℝ)) ^ m := by
    intro N hN
    have hsa : Summable (fun i => |w (i + N)|) := (summable_nat_add_iff N).2 hsum_abs
    calc |∑' i : ℕ, w (i + N)| ≤ ∑' i : ℕ, |w (i + N)| := by
          simpa [Real.norm_eq_abs] using
            norm_tsum_le_tsum_norm (f := fun i => w (i + N)) (by simpa [Real.norm_eq_abs] using hsa)
      _ ≤ ∑' i : ℕ, K₁ * v (i + N) :=
          Summable.tsum_le_tsum (fun i => hwv _) hsa
            (((summable_nat_add_iff N).2 hsum_v).mul_left K₁)
      _ = K₁ * ∑' i : ℕ, v (i + N) := tsum_mul_left
      _ ≤ (K₁ * (1 + 1/(m:ℝ))) / (1 + Real.log (N:ℝ)) ^ m := by
          rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left (hvtail N hN) (by linarith)
  set K₂ : ℝ := (m:ℝ) ^ m * Real.exp 1 + K₁ + K₁ * (1 + 1/(m:ℝ)) with hK₂def
  have hK₂0 : 0 ≤ K₂ := by
    have : 0 ≤ K₁ := by linarith
    rw [hK₂def]; positivity
  have hrecip : ∀ N : ℕ, 1 ≤ N →
      1/(N:ℝ) ≤ ((m:ℝ) ^ m * Real.exp 1) / (1 + Real.log (N:ℝ)) ^ m := by
    intro N hN
    have hn1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    rw [div_le_div_iff₀ (by linarith) (pow_pos (by linarith [hlog1 N]) m)]
    linarith [one_add_log_pow_le hm hn1]
  have hint : ∀ N : ℕ, 1 ≤ N →
      |(∑ k ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt k / (k:ℝ))
          - Real.log (N:ℝ) - (Real.eulerMascheroniConstant + ∑' n : ℕ, w n)|
        ≤ K₂ / (1 + Real.log (N:ℝ)) ^ m := by
    intro N hN
    have hn1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hb := hlog1 N
    have hsplit : ∑ n ∈ Finset.range N,
        ((1:ℝ)/((n:ℝ) + 1) + w n - Chebyshev.psi (n:ℝ) / ((n:ℝ) * ((n:ℝ) + 1))) = 1 := by
      rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (by omega)) ?_]
      · simp [hwdef]
      · intro b _ hb0
        have : (b:ℝ) ≠ 0 := by exact_mod_cast hb0
        simp only [hwdef]
        field_simp
        ring
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_range_one_div_succ,
      ← PrimeGaps.harmonic_cast_eq_sum] at hsplit
    have hpsiN : Chebyshev.psi (N:ℝ) / (N:ℝ) = 1 + (Chebyshev.psi (N:ℝ) - (N:ℝ)) / (N:ℝ) := by
      field_simp
      ring
    have hb2 : |(Chebyshev.psi (N:ℝ) - (N:ℝ)) / (N:ℝ)| ≤ K₁ / (1 + Real.log (N:ℝ)) ^ m := by
      rw [abs_div, abs_of_nonneg (show (0:ℝ) ≤ (N:ℝ) by linarith)]
      have hR := hK₁ (N:ℝ) hn1
      calc |Chebyshev.psi (N:ℝ) - (N:ℝ)| / (N:ℝ)
          ≤ (K₁ * (N:ℝ) / (1 + Real.log (N:ℝ)) ^ (m + 1)) / (N:ℝ) := by gcongr
        _ = K₁ / (1 + Real.log (N:ℝ)) ^ (m + 1) := by field_simp
        _ ≤ K₁ / (1 + Real.log (N:ℝ)) ^ m := by gcongr; linarith
    have hb1 := PrimeGaps.harmonic_bound_int N hN
    have hb3 := hwtail N hN
    have := hsum_w.sum_add_tsum_nat_add N
    have := sum_vonMangoldt_div_eq hN
    have := hrecip N hN
    rw [hK₂def, add_div, add_div, abs_le]
    rw [abs_le] at hb1 hb2 hb3
    constructor <;> linarith
  refine ⟨Real.eulerMascheroniConstant + ∑' n : ℕ, w n,
    2 ^ m * (K₂ + (m:ℝ) ^ m * Real.exp 1), by positivity, fun y hy => ?_⟩
  set N : ℕ := ⌊y⌋₊
  have hN1 : 1 ≤ N := (Nat.one_le_floor_iff y).2 hy
  have hn0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  have hNy : (N:ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyN : y < (N:ℝ) + 1 := Nat.lt_floor_add_one y
  have hb := hlog1 N
  have hly : (0:ℝ) ≤ Real.log y := Real.log_nonneg hy
  have hD : (0:ℝ) < (1 + Real.log (N:ℝ)) ^ m := pow_pos (by linarith) m
  have hDy : (0:ℝ) < (1 + Real.log y) ^ m := pow_pos (by linarith) m
  have hlogmono : Real.log (N:ℝ) ≤ Real.log y := Real.log_le_log hn0 hNy
  have hlogdiff : Real.log y - Real.log (N:ℝ) ≤ 1/(N:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((N:ℝ) + 1)/(N:ℝ) by positivity)
    rw [Real.log_div (by linarith) hn0.ne', add_div, div_self hn0.ne', add_sub_cancel_left] at h
    linarith [Real.log_le_log (by linarith) hyN.le]
  have hpow : (1 + Real.log y) ^ m ≤ 2 ^ m * (1 + Real.log (N:ℝ)) ^ m := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by linarith) ?_ m
    linarith [(div_le_one hn0).2 (by exact_mod_cast hN1 : (1:ℝ) ≤ N)]
  have hratio : (K₂ + (m:ℝ) ^ m * Real.exp 1) / (1 + Real.log (N:ℝ)) ^ m
      ≤ 2 ^ m * (K₂ + (m:ℝ) ^ m * Real.exp 1) / (1 + Real.log y) ^ m := by
    rw [div_le_div_iff₀ hD hDy]
    nlinarith [mul_le_mul_of_nonneg_left hpow
      (by positivity : (0:ℝ) ≤ K₂ + (m:ℝ) ^ m * Real.exp 1)]
  have hmain := hint N hN1
  have := hrecip N hN1
  have := add_div K₂ ((m:ℝ) ^ m * Real.exp 1) ((1 + Real.log (N:ℝ)) ^ m)
  rw [abs_le] at hmain ⊢
  constructor <;> linarith

/-- **Mertens' first theorem with a log-power rate.** For every `m`, there are constants `c`
and `K` with `|∑_{0 < k ≤ y} Λ(k)/k - log y - c| ≤ K (1 + log y)^{-m}` for all `y ≥ 1`. -/
theorem exists_sum_vonMangoldt_div_sub_log_rate (m : ℕ) :
    ∃ c K : ℝ, ∀ y : ℝ, 1 ≤ y →
      |(∑ k ∈ Finset.Ioc 0 ⌊y⌋₊, Λ k / k) - Real.log y - c| ≤ K / (1 + Real.log y) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨c, K, hK0, hK⟩ := exists_sum_vonMangoldt_div_sub_log_rate_of_one_le (m := 1) le_rfl
    refine ⟨c, K, fun y hy => ?_⟩
    have hly : (0:ℝ) ≤ Real.log y := Real.log_nonneg hy
    refine (hK y hy).trans ?_
    rw [pow_zero, div_one, pow_one, div_le_iff₀ (by linarith)]
    nlinarith
  · obtain ⟨c, K, _, hK⟩ := exists_sum_vonMangoldt_div_sub_log_rate_of_one_le hm
    exact ⟨c, K, hK⟩

end Gap212.Sieve
