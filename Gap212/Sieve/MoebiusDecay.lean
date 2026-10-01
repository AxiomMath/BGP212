/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MertensCoprimeCorrection
public import Gap212.Sieve.MertensVonMangoldtRate
public import Gap212.Sieve.MoebiusPartialSumDecay
public import Gap212.Sieve.RenewalBootstrap

/-!
# The decay of the coprime Möbius partial sums

A proof of `Gap212.Sieve.MoebiusPartialSumDecay`:

  `∃ ε > 0, ∀ q ≥ 1, ∃ C, ∀ w ≥ 2, |S_q(w)| ≤ C (1 + log w)^{-1-ε}`,
  `S_q(w) = ∑_{f ≤ w, (f,q)=1} μ(f)/f`,

and it holds at `ε = 1`: `Gap212.Sieve.moebiusPartialSumDecay`.

## The route

Three ingredients, none of them a contour integral:

1. **Mertens' first theorem with a log-power rate**, for the integers coprime to `q`:
   `∑_{k ≤ y, (k,q)=1} Λ(k)/k = log y + c_q + O_m((1 + log y)^{-m})` for every `m`
   (`Gap212.Sieve.exists_sum_vonMangoldt_div_coprime_rate`). This is the only non-elementary
   input, and it is exactly the prime number theorem with an error term:
   `Gap212.Sieve.MertensVonMangoldtRate` derives it from `PrimeNumberTheoremAnd.MediumPNT` by
   discrete Abel summation, and `Gap212.Sieve.MertensCoprimeCorrection` removes the primes
   dividing `q` at rate `O_q(1/y)`.
2. **The renewal identity** `S_q(x) log x = -∑_{n ≤ x} (μ(n)/n)(W_q(x/n) - log(x/n))` over the
   integers coprime to `q`, from `Gap212.Sieve.MoebiusRenewal` applied to the weight
   `b_q = μ·1_{(·,q)=1}/id`. Its hypothesis `b * β = -(b ⬝ log)` holds because coprimality to `q`
   is completely multiplicative, so restricting and dividing by `id` respects Dirichlet
   convolution (`Gap212.Sieve.coprimeDivWeight_mul`), and Mathlib's
   `ArithmeticFunction.sum_moebius_mul_log_eq` gives `μ * Λ = -(μ ⬝ log)`.
3. **The bootstrap** of `Gap212.Sieve.RenewalBootstrap`, which turns those two into
   `|S_q(w)| ≤ C_q (1 + log w)^{-2}`.

## Main results

* `Gap212.Sieve.coprimeDivWeight`: the weight `n ↦ f n / n` restricted to `(n,q) = 1`, and
  `Gap212.Sieve.coprimeDivWeight_mul`, that this respects Dirichlet convolution.
* `Gap212.Sieve.exists_sum_vonMangoldt_div_coprime_rate`: Mertens with a rate, coprime to `q`.
* `Gap212.Sieve.exists_moebiusReciprocalBelow_log_sq_decay`: `|S_q(w)| ≤ C (1 + log w)^{-2}`.
* `Gap212.Sieve.moebiusPartialSumDecay`: `Gap212.Sieve.MoebiusPartialSumDecay`, at `ε = 1`. -/

@[expose] public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction ArithmeticFunction.Moebius

namespace Gap212.Sieve

/-- `n ↦ f n / n`, restricted to `n` coprime to `q`. -/
noncomputable def coprimeDivWeight (q : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if Nat.Coprime n q then f n / n else 0, by simp⟩

/-- The defining formula for `Gap212.Sieve.coprimeDivWeight`. -/
@[simp] theorem coprimeDivWeight_apply (q : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    coprimeDivWeight q f n = if Nat.Coprime n q then f n / n else 0 := rfl

/-- Restricting to the integers coprime to `q` and dividing by `id` is a ring map for Dirichlet
convolution: coprimality to `q` is completely multiplicative, and `d * (n / d) = n`. -/
theorem coprimeDivWeight_mul (q : ℕ) (f g : ArithmeticFunction ℝ) :
    coprimeDivWeight q f * coprimeDivWeight q g = coprimeDivWeight q (f * g) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [mul_apply, coprimeDivWeight_apply]
  rcases Decidable.em (Nat.Coprime n q) with hcop | hcop
  · rw [if_pos hcop, mul_apply, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hpn, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hcop' : Nat.Coprime p.1 q ∧ Nat.Coprime p.2 q := by
      rw [← hpn] at hcop
      exact Nat.coprime_mul_iff_left.mp hcop
    have hp1 : p.1 ≠ 0 := by
      rintro h; rw [h, zero_mul] at hpn; exact hn hpn.symm
    have hp2 : p.2 ≠ 0 := by
      rintro h; rw [h, mul_zero] at hpn; exact hn hpn.symm
    have hp1R : ((p.1 : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hp1
    have hp2R : ((p.2 : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hp2
    rw [coprimeDivWeight_apply, coprimeDivWeight_apply, if_pos hcop'.1, if_pos hcop'.2, ← hpn]
    push_cast
    field_simp
  · rw [if_neg hcop]
    refine Finset.sum_eq_zero fun p hp => ?_
    obtain ⟨hpn, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    rw [coprimeDivWeight_apply, coprimeDivWeight_apply]
    rcases Decidable.em (Nat.Coprime p.1 q) with h1 | h1
    · rcases Decidable.em (Nat.Coprime p.2 q) with h2 | h2
      · exact absurd (hpn ▸ Nat.coprime_mul_iff_left.mpr ⟨h1, h2⟩) hcop
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

/-- Restriction commutes with pointwise multiplication by `log` and with negation, so the renewal
identity's hypothesis transports from `f` to its restriction. -/
theorem coprimeDivWeight_neg_pmul_log (q : ℕ) (f : ArithmeticFunction ℝ) :
    coprimeDivWeight q (-(f.pmul ArithmeticFunction.log))
      = -((coprimeDivWeight q f).pmul ArithmeticFunction.log) := by
  ext n
  rcases Decidable.em (Nat.Coprime n q) with h | h
  · simp only [coprimeDivWeight_apply, ArithmeticFunction.neg_apply, pmul_apply, log_apply,
      if_pos h]
    ring
  · simp only [coprimeDivWeight_apply, ArithmeticFunction.neg_apply, pmul_apply, log_apply,
      if_neg h]
    ring

/-- The convolution relation at the coprimality-restricted Moebius weight. -/
theorem coprimeMoebius_mul_coprimeVonMangoldt (q : ℕ) :
    coprimeDivWeight q (μ : ArithmeticFunction ℝ) * coprimeDivWeight q vonMangoldt
      = -((coprimeDivWeight q (μ : ArithmeticFunction ℝ)).pmul ArithmeticFunction.log) := by
  rw [coprimeDivWeight_mul, moebius_mul_vonMangoldt, coprimeDivWeight_neg_pmul_log]

/-- The summatory function of the restricted Möbius weight **is** `S_q`. -/
theorem summatory_coprimeMoebius (q : ℕ) (t : ℝ) :
    summatory (coprimeDivWeight q (μ : ArithmeticFunction ℝ)) t
      = moebiusReciprocalBelow q t := by
  have hIcc : Finset.Icc 1 ⌊t⌋₊ = Finset.Ioc 0 ⌊t⌋₊ := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [summatory]
  simp only [coprimeDivWeight_apply, intCoe_apply]
  rw [← Finset.sum_filter, moebiusReciprocalBelow, coprimeBelow, hIcc]

/-- The summatory function of the restricted von Mangoldt weight is the coprimality-restricted
Mertens sum `W_q`. -/
theorem summatory_coprimeVonMangoldt (q : ℕ) (t : ℝ) :
    summatory (coprimeDivWeight q vonMangoldt) t
      = ∑ k ∈ Finset.Ioc 0 ⌊t⌋₊ with Nat.Coprime k q, Λ k / k := by
  rw [summatory]
  simp only [coprimeDivWeight_apply]
  rw [← Finset.sum_filter]

/-- `∑_{n ≤ y, (n,q)=1} |μ(n)|/n ≤ 1 + log y`, the weight bound the bootstrap needs: `|μ| ≤ 1` and
the harmonic sum. -/
theorem sum_abs_coprimeMoebius_le (q : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, |coprimeDivWeight q (μ : ArithmeticFunction ℝ) n|
      ≤ 1 * (1 + Real.log y) := by
  have hstep : ∀ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      |coprimeDivWeight q (μ : ArithmeticFunction ℝ) n| ≤ ((n:ℝ))⁻¹ := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hn0R : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
    rw [coprimeDivWeight_apply]
    rcases Decidable.em (Nat.Coprime n q) with h | h
    · rw [if_pos h, abs_div, abs_of_nonneg hn0R.le, ← one_div, div_le_div_iff₀ hn0R hn0R]
      have h1 : |((μ n : ℤ) : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast abs_moebius_le_one
      simpa using mul_le_mul_of_nonneg_right h1 hn0R.le
    · rw [if_neg h, abs_zero]
      positivity
  refine le_trans (Finset.sum_le_sum hstep) ?_
  have hharm : ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ((n:ℝ))⁻¹ = ((harmonic ⌊y⌋₊ : ℚ) : ℝ) := by
    have hIcc : Finset.Icc 1 ⌊y⌋₊ = Finset.Ioc 0 ⌊y⌋₊ := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [harmonic_eq_sum_Icc, hIcc]
    push_cast
    rfl
  rw [hharm, one_mul]
  exact harmonic_floor_le_one_add_log y hy

/-- **Mertens' first theorem with a log-power rate, restricted to the integers coprime to `q`.** -/
theorem exists_sum_vonMangoldt_div_coprime_rate {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    ∃ c K : ℝ, ∀ y : ℝ, 1 ≤ y →
      |(∑ k ∈ Finset.Ioc 0 ⌊y⌋₊ with Nat.Coprime k q, Λ k / k) - Real.log y - c|
        ≤ K / (1 + Real.log y) ^ m := by
  obtain ⟨c₁, K₁, h₁⟩ := exists_sum_vonMangoldt_div_sub_log_rate m
  obtain ⟨d, K₂, hK₂, h₂⟩ := exists_sum_vonMangoldt_div_not_coprime_rate hq
  obtain ⟨C₃, hC₃, h₃⟩ := exists_one_add_log_pow_le_mul m
  refine ⟨c₁ - d, K₁ + K₂ * C₃, fun y hy => ?_⟩
  have hsplit : (∑ k ∈ Finset.Ioc 0 ⌊y⌋₊ with Nat.Coprime k q, Λ k / k)
      = (∑ k ∈ Finset.Ioc 0 ⌊y⌋₊, Λ k / k)
        - ∑ k ∈ Finset.Ioc 0 ⌊y⌋₊ with ¬ Nat.Coprime k q, Λ k / k := by
    rw [eq_sub_iff_add_eq, Finset.sum_filter_add_sum_filter_not]
  have hpos : (0:ℝ) < (1 + Real.log y) ^ m := by
    have := one_le_one_add_log hy; positivity
  have e3 : K₂ / y ≤ K₂ * C₃ / (1 + Real.log y) ^ m := by
    rw [div_le_div_iff₀ (by linarith) hpos]
    calc K₂ * (1 + Real.log y) ^ m ≤ K₂ * (C₃ * y) :=
          mul_le_mul_of_nonneg_left (h₃ y hy) hK₂
      _ = K₂ * C₃ * y := by ring
  have hdiv : (K₁ + K₂ * C₃) / (1 + Real.log y) ^ m
      = K₁ / (1 + Real.log y) ^ m + K₂ * C₃ / (1 + Real.log y) ^ m := by ring
  rw [hsplit, show (∑ k ∈ Finset.Ioc 0 ⌊y⌋₊, Λ k / k)
        - (∑ k ∈ Finset.Ioc 0 ⌊y⌋₊ with ¬ Nat.Coprime k q, Λ k / k) - Real.log y - (c₁ - d)
      = ((∑ k ∈ Finset.Ioc 0 ⌊y⌋₊, Λ k / k) - Real.log y - c₁)
        - ((∑ k ∈ Finset.Ioc 0 ⌊y⌋₊ with ¬ Nat.Coprime k q, Λ k / k) - d) from by ring, hdiv]
  exact le_trans (abs_sub _ _) (add_le_add (h₁ y hy) (le_trans (h₂ y hy) e3))

/-- **The truncated Möbius partial sum decays like `(log w)^{-2}`**: for every `q ≥ 1` there is a
`C` with `|S_q(w)| ≤ C (1 + log w)^{-2}` for all `w ≥ 1`. This is
`Gap212.Sieve.MoebiusPartialSumDecay` at `ε = 1`, valid from `w ≥ 1` rather than `w ≥ 2`. -/
theorem exists_moebiusReciprocalBelow_log_sq_decay {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ w : ℝ, 1 ≤ w → |moebiusReciprocalBelow q w| ≤ C / (1 + Real.log w) ^ 2 := by
  obtain ⟨c, K, hρ⟩ := exists_sum_vonMangoldt_div_coprime_rate hq 4
  obtain ⟨C, hC⟩ := exists_summatory_decay
    (b := coprimeDivWeight q (μ : ArithmeticFunction ℝ))
    (β := coprimeDivWeight q vonMangoldt)
    (coprimeMoebius_mul_coprimeVonMangoldt q)
    (fun n => by
      rw [coprimeDivWeight_apply]
      split
      · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
      · exact le_rfl)
    (K₁ := 1) (fun y hy => sum_abs_coprimeMoebius_le q hy)
    (m := 4) le_rfl
    (fun y hy => by rw [summatory_coprimeVonMangoldt]; exact hρ y hy)
  refine ⟨C, fun w hw => ?_⟩
  rw [← summatory_coprimeMoebius]
  exact hC w hw

/-- **`Gap212.Sieve.MoebiusPartialSumDecay` holds**, at `ε = 1`.

The proof: `PrimeNumberTheoremAnd`'s `MediumPNT` gives
`ψ(x) - x ≪ x (log x)^{-m}` for every `m`; Abel summation turns that into Mertens' first theorem
with a rate; the renewal identity reduces the Möbius sum to that; and summation by parts over a
short range converts the elementary `O(1/log w)` into `O((log w)^{-2})`. No contour integral and no
zero-free region are used. -/
@[gap212 "lem_moebius_partial_sum_decay"]
theorem moebiusPartialSumDecay : MoebiusPartialSumDecay := by
  refine ⟨1, one_pos, fun q hq => ?_⟩
  obtain ⟨C, hC⟩ := exists_moebiusReciprocalBelow_log_sq_decay hq
  refine ⟨C, fun w hw => ?_⟩
  have h := hC w (by linarith)
  rwa [show (1 + Real.log w) ^ (1 + (1:ℝ)) = (1 + Real.log w) ^ (2:ℕ) from by
    rw [show (1 + (1:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]]

end Gap212.Sieve

