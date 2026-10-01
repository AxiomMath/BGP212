/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MoebiusReciprocalSeries
public import PrimeGapsTheory.ArithmeticFunction.Estimates
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The totient-weight Möbius Dirichlet series and its zero at `s = 0`

The truncated inner sum with totient weight is governed by the Dirichlet series

  `h_e(s) = ∑_{(f,e)=1} μ(f)/(φ(f) f^s) = ∏_{p ∤ e}(1 - 1/((p-1)p^s))`,

and the constant of the totient-weight inner sum is the Abel integral
`∫_0^∞ T_e(exp u) du = lim_{s → 0⁺} h_e(s)/s`, where `T_e(w) = ∑_{f ≤ w, (f,e)=1} μ(f)/φ(f)`.

## The factorisation, and the shape of the zero

Against the reciprocal-weight series
`g_e(s) = ∑_{(f,e)=1} μ(f) f^{-1-s} = ∏_{p ∤ e}(1 - p^{-1-s})` the quotient factors exactly:

  `(1 - p^{-1-s}) · (1 - 1/((p-1)(p^{1+s} - 1))) = 1 - 1/((p-1)p^s)`,

an identity in `p` and `s` (`Gap212.Sieve.one_sub_rpow_mul_totientCorrFactor`). So

  `h_e(s) = g_e(s) · R_e(s)`,   `R_e(s) = ∏_{p ∤ e}(1 - 1/((p-1)(p^{1+s} - 1)))`,

which is the factorisation `h_e(s) = ζ(s+1)^{-1} ∏_{p ∣ e}(1 - p^{-s-1})^{-1} R_e(s)`, with the
first two factors already assembled into `g_e`. The third product `R_e` is absolutely convergent,
uniformly for `s ≥ 0`: its `p`-th deficiency is
`1/((p-1)(p^{1+s} - 1)) ≤ 1/(p-1)^2` since `p^{1+s} ≥ p`. Hence `R_e` is continuous at `s = 0`,
where its value is `∏_{p ∤ e}(1 - 1/(p-1)^2)`, the product of
`Gap212.Sieve.MoebiusTotientAsymptotic`.

Since `g_e(s)/s → e/φ(e)` (`Gap212.Sieve.tendsto_moebiusReciprocalSeries_div`), the zero of `h_e`
at `s = 0` is simple exactly when `R_e(0) ≠ 0`, and

  `h_e(s)/s → (e/φ(e)) · ∏_{p ∤ e}(1 - 1/(p-1)^2) = c_e`.

## Where evenness of `e` is used

The factor of `R_e` at `p = 2` is `1 - 1/(2^{1+s} - 1)`, which tends to `0` as `s → 0⁺`. For odd
`e` that factor is present, `R_e(0) = 0`, the zero of `h_e` is *double*, and the limit above is `0`
rather than `c_e`. For even `e` the prime `2` divides `e` and is excluded from the product, every
surviving factor is at a prime `p ≥ 3` with deficiency at most `1/4`, and the limit is positive.
Nothing here needs `e` squarefree: `c_e` depends on `e` only through which primes divide it.

## Main definitions

* `Gap212.Sieve.moebiusTotientCoprimeTerm`: `μ(f)/(φ(f) f^s)` on the `f` coprime to `e`, `0`
  elsewhere.
* `Gap212.Sieve.moebiusTotientSeries`: `h_e(s) = ∑_{(f,e)=1} μ(f)/(φ(f) f^s)`.
* `Gap212.Sieve.totientCorrFactor`: the `p`-th factor `1 - 1/((p-1)(p^{1+s} - 1))` of `R_e`.

## Main results

* `Gap212.Sieve.summable_abs_moebius_div_totient_mul_rpow`,
  `Gap212.Sieve.summable_norm_moebiusTotientCoprimeTerm`: absolute convergence for `s > 0`, off the
  dependency's `ArithmeticFunction.summable_moebius_sq_mul_tau_div_totient_mul_rpow`.
* `Gap212.Sieve.hasProd_moebiusTotientSeries`: the Euler product
  `h_e(s) = ∏_{p ∤ e}(1 - 1/((p-1)p^s))`.
* `Gap212.Sieve.moebiusTotientSeries_eq_mul_tprod`: the factorisation `h_e(s) = g_e(s) R_e(s)`.
* `Gap212.Sieve.tendsto_tprod_totientCorrFactor`: `R_e(s) → ∏_{p ∤ e}(1 - 1/(p-1)^2)` as `s → 0⁺`,
  for even `e`.
* `Gap212.Sieve.tendsto_moebiusTotientSeries_div`: `h_e(s)/s → c_e` as `s → 0⁺`, for even `e ≥ 1`.
-/

@[expose] public section

open ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Gap212.Sieve

/-! ### The series and its absolute convergence -/

/-- The summand of the totient-weight Dirichlet series: `μ(f)/(φ(f) f^s)` on the `f` coprime to
`e`, and `0` elsewhere. -/
noncomputable def moebiusTotientCoprimeTerm (e : ℕ) (s : ℝ) (f : ℕ) : ℝ :=
  if Nat.Coprime f e then (μ f : ℝ) / ((f.totient : ℝ) * (f : ℝ) ^ s) else 0

/-- **The totient-weight Möbius Dirichlet series** `h_e(s) = ∑_{(f,e)=1} μ(f)/(φ(f) f^s)`. -/
noncomputable def moebiusTotientSeries (e : ℕ) (s : ℝ) : ℝ :=
  ∑' f : ℕ, moebiusTotientCoprimeTerm e s f

/-- The summand `moebiusTotientCoprimeTerm e s` vanishes at `0`. -/
theorem moebiusTotientCoprimeTerm_zero (e : ℕ) (s : ℝ) : moebiusTotientCoprimeTerm e s 0 = 0 := by
  simp [moebiusTotientCoprimeTerm]

/-- The summand `moebiusTotientCoprimeTerm e s` equals `1` at `1`. -/
theorem moebiusTotientCoprimeTerm_one (e : ℕ) (s : ℝ) : moebiusTotientCoprimeTerm e s 1 = 1 := by
  simp [moebiusTotientCoprimeTerm]

/-- The summand `moebiusTotientCoprimeTerm e s` is multiplicative on coprime arguments. -/
theorem moebiusTotientCoprimeTerm_mul {e : ℕ} {s : ℝ} {m n : ℕ} (hmn : Nat.Coprime m n) :
    moebiusTotientCoprimeTerm e s (m * n)
      = moebiusTotientCoprimeTerm e s m * moebiusTotientCoprimeTerm e s n := by
  unfold moebiusTotientCoprimeTerm
  by_cases hm : m.Coprime e
  · by_cases hn : n.Coprime e
    · rw [if_pos hm, if_pos hn, if_pos (Nat.coprime_mul_iff_left.2 ⟨hm, hn⟩),
        isMultiplicative_moebius.map_mul_of_coprime hmn, Nat.totient_mul hmn, Nat.cast_mul m n,
        Real.mul_rpow (by positivity) (by positivity), div_mul_div_comm]
      push_cast
      ring
    · simp [hn, Nat.coprime_mul_iff_left]
  · simp [hm, Nat.coprime_mul_iff_left]

/-- **`∑_f |μ(f)|/(φ(f) f^s) < ∞` for every `s > 0`.**

The Euler product below needs absolute convergence; the bound `|μ(f)|/φ(f) ≤ 1` does not give it,
since `∑ f^{-s}` diverges at every `s ≤ 1`. The dependency's
`ArithmeticFunction.summable_moebius_sq_mul_tau_div_totient_mul_rpow` supplies it at every `s > 0`,
through `n/φ(n) ≪_ε n^ε`. -/
theorem summable_abs_moebius_div_totient_mul_rpow {s : ℝ} (hs : 0 < s) :
    Summable fun f : ℕ => |(μ f : ℝ)| / ((f.totient : ℝ) * (f : ℝ) ^ s) := by
  refine (summable_moebius_sq_mul_tau_div_totient_mul_rpow (r := 1) hs).of_nonneg_of_le
    (fun _ => by positivity) fun f => ?_
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rw [pow_one, zeta_apply_ne hf]
  rcases Int.abs_le_one_iff.mp (abs_moebius_le_one (n := f)) with h | h | h <;> simp [h]

/-- The series is absolutely convergent for `s > 0`. -/
theorem summable_norm_moebiusTotientCoprimeTerm (e : ℕ) {s : ℝ} (hs : 0 < s) :
    Summable fun f : ℕ => ‖moebiusTotientCoprimeTerm e s f‖ := by
  refine (summable_abs_moebius_div_totient_mul_rpow hs).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun f ↦ ?_
  unfold moebiusTotientCoprimeTerm
  split_ifs
  · rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (a := (f.totient : ℝ) * (f : ℝ) ^ s)
      (by positivity)]
  · rw [norm_zero]
    positivity

/-! ### The Euler product -/

/-- The Euler factor: at a prime `p`, `∑_k μ(p^k)/(φ(p^k) p^{ks})` restricted to the classes
coprime to `e` is `1 - 1/((p-1)p^s)` when `p ∤ e` and `1` when `p ∣ e`. Only `k = 0` and `k = 1`
contribute, `μ` vanishing on higher prime powers. -/
theorem tsum_moebiusTotientCoprimeTerm_prime_pow {e : ℕ} {s : ℝ} {p : ℕ} (hp : p.Prime) :
    ∑' k : ℕ, moebiusTotientCoprimeTerm e s (p ^ k)
      = if p ∣ e then 1 else 1 - 1 / (((p : ℝ) - 1) * (p : ℝ) ^ s) := by
  have hz : ∀ k ∉ ({0, 1} : Finset ℕ), moebiusTotientCoprimeTerm e s (p ^ k) = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    have hmu : μ (p ^ k) = 0 := by rw [moebius_apply_prime_pow hp hk.1, if_neg hk.2]
    simp [moebiusTotientCoprimeTerm, hmu]
  rw [tsum_eq_sum hz, Finset.sum_insert (by simp), Finset.sum_singleton, pow_zero, pow_one,
    moebiusTotientCoprimeTerm_one, moebiusTotientCoprimeTerm]
  by_cases hd : p ∣ e
  · rw [if_neg fun h => ((hp.coprime_iff_not_dvd).1 h) hd, if_pos hd, add_zero]
  · rw [if_pos ((hp.coprime_iff_not_dvd).2 hd), if_neg hd, moebius_apply_prime hp,
      Nat.totient_prime hp, Nat.cast_pred hp.pos]
    push_cast
    ring

/-- **The Euler product for the totient-weight series.** For `s > 0`,
`h_e(s) = ∏_{p ∤ e}(1 - 1/((p-1)p^s))`, stated via `HasProd` over `ℕ` with the non-primes and the
primes dividing `e` contributing the factor `1`. -/
theorem hasProd_moebiusTotientSeries (e : ℕ) {s : ℝ} (hs : 0 < s) :
    HasProd (fun p : ℕ => if p.Prime ∧ ¬ p ∣ e then 1 - 1 / (((p : ℝ) - 1) * (p : ℝ) ^ s) else 1)
      (moebiusTotientSeries e s) := by
  have h := EulerProduct.eulerProduct_hasProd_mulIndicator (f := moebiusTotientCoprimeTerm e s)
    (moebiusTotientCoprimeTerm_one e s) moebiusTotientCoprimeTerm_mul
    (summable_norm_moebiusTotientCoprimeTerm e hs) (moebiusTotientCoprimeTerm_zero e s)
  refine h.congr_fun fun p => ?_
  simp only [Set.mulIndicator_apply, Set.mem_ofPred_eq]
  by_cases hp : p.Prime <;> by_cases hd : p ∣ e <;>
    simp [hp, hd, tsum_moebiusTotientCoprimeTerm_prime_pow]

/-! ### The convergent correction `R_e` -/

/-- The `p`-th factor of `R_e`: `1 - 1/((p-1)(p^{1+s} - 1))` at a prime `p ∤ e`, and `1`
elsewhere. At `s = 0` this is `1 - 1/(p-1)^2`. -/
noncomputable def totientCorrFactor (e : ℕ) (s : ℝ) (p : ℕ) : ℝ :=
  if p.Prime ∧ ¬ p ∣ e then 1 - 1 / (((p : ℝ) - 1) * ((p : ℝ) ^ (1 + s) - 1)) else 1

/-- At `s = 0` the correction's factor is `1 - 1/(p-1)^2`, the factor of
`Gap212.Sieve.MoebiusTotientAsymptotic`. -/
theorem totientCorrFactor_zero (e : ℕ) (p : ℕ) :
    totientCorrFactor e 0 p = if p.Prime ∧ ¬ p ∣ e then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 := by
  simp only [totientCorrFactor, add_zero, Real.rpow_one, ← sq]

/-- `(p-1)(p^{1+s} - 1) ≥ (p-1)^2 > 0` for a prime `p` and `s ≥ 0`: the deficiency of the `p`-th
correction factor is at most `1/(p-1)^2`, uniformly in `s ≥ 0`. -/
theorem sq_le_mul_rpow_sub_one {p : ℕ} (hp : p.Prime) {s : ℝ} (hs : 0 ≤ s) :
    ((p : ℝ) - 1) ^ 2 ≤ ((p : ℝ) - 1) * ((p : ℝ) ^ (1 + s) - 1) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have := Real.rpow_le_rpow_of_exponent_le hp1 (le_add_of_nonneg_right hs : (1 : ℝ) ≤ 1 + s)
  rw [Real.rpow_one] at this
  rw [sq]
  exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-- The deficiency `1 - totientCorrFactor e s p` equals `1/((p-1)(p^{1+s} - 1))` at a prime
`p ∤ e`, and `0` elsewhere. -/
theorem one_sub_totientCorrFactor (e : ℕ) (s : ℝ) (p : ℕ) :
    1 - totientCorrFactor e s p
      = if p.Prime ∧ ¬ p ∣ e then 1 / (((p : ℝ) - 1) * ((p : ℝ) ^ (1 + s) - 1)) else 0 := by
  simp only [totientCorrFactor]
  split_ifs <;> ring

/-- The deficiency of the `p`-th factor is between `0` and `1/(p-1)^2`, for every `s ≥ 0`. -/
theorem one_sub_totientCorrFactor_bounds (e : ℕ) {s : ℝ} (hs : 0 ≤ s) (p : ℕ) :
    0 ≤ 1 - totientCorrFactor e s p ∧
      1 - totientCorrFactor e s p
        ≤ if p.Prime ∧ ¬ p ∣ e then 1 / ((p : ℝ) - 1) ^ 2 else 0 := by
  rw [one_sub_totientCorrFactor]
  split_ifs with h
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.1.two_le
    have hsq : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
    have hle := sq_le_mul_rpow_sub_one h.1 hs
    exact ⟨(one_div_pos.2 (hsq.trans_le hle)).le, one_div_le_one_div_of_le hsq hle⟩
  · simp

/-- The correction's deficiencies are summable, uniformly in `s ≥ 0`: they are bounded by the
`1/(p-1)^2` of `Gap212.Sieve.summable_corr_aux`. -/
theorem summable_one_sub_totientCorrFactor (e : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    Summable fun p : ℕ => 1 - totientCorrFactor e s p :=
  (summable_corr_aux e).of_nonneg_of_le (fun p => (one_sub_totientCorrFactor_bounds e hs p).1)
    fun p => (one_sub_totientCorrFactor_bounds e hs p).2

/-- The factors `totientCorrFactor e s` are multipliable for every `s ≥ 0`. -/
theorem multipliable_totientCorrFactor (e : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    Multipliable (totientCorrFactor e s) := by
  simpa using Real.multipliable_one_add_of_summable (summable_one_sub_totientCorrFactor e hs).neg

/-! ### The factorisation `h_e = g_e · R_e` -/

/-- **The Euler factors factorise exactly.** For a prime `p` and `s > 0`,

  `(1 - p^{-1-s}) · (1 - 1/((p-1)(p^{1+s} - 1))) = 1 - 1/((p-1)p^s)`,

which is the identity behind `h_e(s) = g_e(s) R_e(s)`. Writing `t = p^s`, both sides are
`(pt - t - 1)/((p-1)t)`. -/
theorem one_sub_rpow_mul_totientCorrFactor (e : ℕ) {s : ℝ} (hs : 0 < s) (p : ℕ) :
    (if p.Prime ∧ ¬ p ∣ e then 1 - (p : ℝ) ^ (-(1 + s)) else 1) * totientCorrFactor e s p
      = if p.Prime ∧ ¬ p ∣ e then 1 - 1 / (((p : ℝ) - 1) * (p : ℝ) ^ s) else 1 := by
  unfold totientCorrFactor
  split_ifs with h
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast h.1.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have ht1 : 1 < (p : ℝ) ^ s := Real.one_lt_rpow (by linarith) hs
    have hpm : (p : ℝ) - 1 ≠ 0 := by linarith [sub_pos.2 (by linarith : (1 : ℝ) < p)]
    have hPm : (p : ℝ) * p ^ s - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < p * p ^ s - 1).ne'
    rw [Real.rpow_neg hp0.le, Real.rpow_add hp0, Real.rpow_one]
    field_simp
    ring
  · rw [one_mul]

/-- **The factorisation.** For `s > 0`, `h_e(s) = g_e(s) · R_e(s)`: the totient-weight series is
the reciprocal-weight series times the absolutely convergent correction. Written out, this is
`g_e(s) = ζ(s+1)^{-1} ∏_{p ∣ e}(1 - p^{-s-1})^{-1} ∏_{p ∤ e}(1 - 1/((p-1)(p^{s+1}-1)))` with the
first two factors already assembled into `Gap212.Sieve.moebiusReciprocalSeries`. -/
theorem moebiusTotientSeries_eq_mul_tprod (e : ℕ) {s : ℝ} (hs : 0 < s) :
    moebiusTotientSeries e s
      = moebiusReciprocalSeries e s * ∏' p : ℕ, totientCorrFactor e s p :=
  HasProd.unique (hasProd_moebiusTotientSeries e hs)
    (((hasProd_moebiusReciprocalSeries e hs).mul
      (multipliable_totientCorrFactor e hs.le).hasProd).congr_fun
        fun p => (one_sub_rpow_mul_totientCorrFactor e hs p).symm)

/-! ### `R_e` is continuous at `s = 0` -/

/-- **Every factor of `R_e` is at least `3/4`, for even `e` and `s ≥ 0`.** The prime `2` is the
only one whose factor could vanish — `1 - 1/(2^{1+s} - 1)` is `0` at `s = 0` — and `2 ∣ e` excludes
it; the remaining primes satisfy `(p-1)^2 ≥ 4`, so the deficiency is at most `1/4`. -/
theorem totientCorrFactor_ge {e : ℕ} (he2 : 2 ∣ e) {s : ℝ} (hs : 0 ≤ s) (p : ℕ) :
    3 / 4 ≤ totientCorrFactor e s p := by
  have h := (one_sub_totientCorrFactor_bounds e hs p).2
  by_cases hc : p.Prime ∧ ¬ p ∣ e
  · rw [if_pos hc] at h
    have hne2 : p ≠ 2 := fun hh ↦ hc.2 (hh ▸ he2)
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (by have := hc.1.two_le; lia : 3 ≤ p)
    have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    linarith
  · rw [totientCorrFactor, if_neg hc]
    norm_num

/-- Every factor `totientCorrFactor e s p` is positive, for even `e` and `s ≥ 0`. -/
theorem totientCorrFactor_pos {e : ℕ} (he2 : 2 ∣ e) {s : ℝ} (hs : 0 ≤ s) (p : ℕ) :
    0 < totientCorrFactor e s p :=
  lt_of_lt_of_le (by norm_num) (totientCorrFactor_ge he2 hs p)

/-- `|log(1 - δ)| ≤ 2δ` for `0 ≤ δ ≤ 1/2`, from `log x ≤ x - 1` at `x = (1-δ)⁻¹`. This is the
uniform majorant that makes the correction's logarithms summable independently of `s`. -/
theorem abs_log_one_sub_le {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 2) :
    |Real.log (1 - δ)| ≤ 2 * δ := by
  have hpos : (0 : ℝ) < 1 - δ := by linarith
  rw [abs_of_nonpos (Real.log_nonpos hpos.le (by linarith)), ← Real.log_inv]
  refine (Real.log_le_sub_one_of_pos (inv_pos.2 hpos)).trans ?_
  rw [inv_eq_one_div, div_sub_one hpos.ne', div_le_iff₀ hpos]
  nlinarith

private theorem norm_log_totientCorrFactor_le {e : ℕ} (he2 : 2 ∣ e) {s : ℝ} (hs : 0 ≤ s)
    (p : ℕ) : ‖Real.log (totientCorrFactor e s p)‖ ≤
      2 * (if p.Prime ∧ ¬ p ∣ e then 1 / ((p : ℝ) - 1) ^ 2 else 0) := by
  obtain ⟨hlow, hhigh⟩ := one_sub_totientCorrFactor_bounds e hs p
  have := abs_log_one_sub_le hlow (by linarith [totientCorrFactor_ge he2 hs p])
  rw [sub_sub_cancel] at this
  rw [Real.norm_eq_abs]
  linarith

/-- The correction's logarithms are summable, with a majorant `2/(p-1)^2` independent of
`s ≥ 0`. -/
theorem summable_log_totientCorrFactor {e : ℕ} (he2 : 2 ∣ e) {s : ℝ} (hs : 0 ≤ s) :
    Summable fun p : ℕ => Real.log (totientCorrFactor e s p) :=
  .of_norm_bounded ((summable_corr_aux e).mul_left 2) (norm_log_totientCorrFactor_le he2 hs)

/-- Each factor of `R_e` is continuous at `s = 0`: the denominator `(p-1)(p^{1+s} - 1)` is
`(p-1)^2 ≠ 0` there. -/
theorem tendsto_totientCorrFactor {e : ℕ} (p : ℕ) :
    Tendsto (fun s : ℝ => totientCorrFactor e s p) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (totientCorrFactor e 0 p)) := by
  refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
  unfold totientCorrFactor
  split_ifs with hc
  · have hp1 : (1 : ℝ) < p := by exact_mod_cast hc.1.one_lt
    have hden : ((p : ℝ) - 1) * ((p : ℝ) ^ (1 + (0 : ℝ)) - 1) ≠ 0 := by
      rw [add_zero, Real.rpow_one]
      exact (mul_pos (sub_pos.2 hp1) (sub_pos.2 hp1)).ne'
    refine (continuousAt_const.sub (continuousAt_const.div (continuousAt_const.mul
      (((Real.continuousAt_const_rpow (by positivity)).comp (by fun_prop)).sub
        continuousAt_const)) hden)).tendsto
  · exact tendsto_const_nhds

/-- **`R_e` is continuous at `s = 0`**, with value `∏_{p ∤ e}(1 - 1/(p-1)^2)`, the product
`Gap212.Sieve.MoebiusTotientAsymptotic` works with. Dominated convergence on the logarithms:
the majorant `2/(p-1)^2` is independent of `s ≥ 0`, and each factor is continuous at `0`. -/
theorem tendsto_tprod_totientCorrFactor {e : ℕ} (he2 : 2 ∣ e) :
    Tendsto (fun s : ℝ => ∏' p : ℕ, totientCorrFactor e s p) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ e then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)) := by
  have hlog : Tendsto (fun s : ℝ => ∑' p : ℕ, Real.log (totientCorrFactor e s p))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∑' p : ℕ, Real.log (totientCorrFactor e 0 p))) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun p : ℕ => 2 * (if p.Prime ∧ ¬ p ∣ e then 1 / ((p : ℝ) - 1) ^ 2 else 0))
      ((summable_corr_aux e).mul_left 2) (fun p => ?_) ?_
    · exact ((Real.continuousAt_log (totientCorrFactor_pos he2 le_rfl p).ne').tendsto).comp
        (tendsto_totientCorrFactor p)
    · filter_upwards [self_mem_nhdsWithin] with s hs p
      using norm_log_totientCorrFactor_le he2 (le_of_lt hs) p
  have hexp := (Real.continuous_exp.tendsto _).comp hlog
  have hzero : Real.exp (∑' p : ℕ, Real.log (totientCorrFactor e 0 p))
      = ∏' p : ℕ, if p.Prime ∧ ¬ p ∣ e then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 := by
    rw [Real.rexp_tsum_eq_tprod (fun p => totientCorrFactor_pos he2 le_rfl p)
      (summable_log_totientCorrFactor he2 le_rfl)]
    exact tprod_congr fun p => totientCorrFactor_zero e p
  rw [← hzero]
  refine hexp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact Real.rexp_tsum_eq_tprod (fun p => totientCorrFactor_pos he2 (le_of_lt hs) p)
    (summable_log_totientCorrFactor he2 (le_of_lt hs))

/-! ### The limit -/

/-- **The Abel constant of the totient-weight inner sum.** For `e ≥ 1` even,

  `h_e(s)/s ⟶ (e/φ(e)) · ∏_{p ∤ e}(1 - 1/(p-1)^2) = c_e`   (`s → 0⁺`).

The zero of `h_e` at `s = 0` is simple: it is the simple zero of `g_e` times the correction `R_e`,
which is nonzero at `s = 0` because `2 ∣ e` removes the one factor that vanishes there. For odd `e`
the factor at `p = 2` is present, `R_e(0) = 0`, and the limit is `0` — so evenness cannot be
dropped.

`c_e = e^γ` times the Möbius–totient limit at `V = e`: the product here is literally the
`∏' p, if p.Prime ∧ ¬ p ∣ V then 1 - 1/(p-1)^2 else 1` of
`Gap212.Sieve.tendsto_log_mul_prod_one_sub_inv_sub_one`, and only the Mertens `e^{-γ}` differs. -/
theorem tendsto_moebiusTotientSeries_div {e : ℕ} (he : 1 ≤ e) (he2 : 2 ∣ e) :
    Tendsto (fun s : ℝ => moebiusTotientSeries e s / s) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((e : ℝ) / (e.totient : ℝ)) *
        ∏' p : ℕ, if p.Prime ∧ ¬ p ∣ e then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)) := by
  have h := (tendsto_moebiusReciprocalSeries_div he).mul (tendsto_tprod_totientCorrFactor he2)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [moebiusTotientSeries_eq_mul_tprod e hs]
  ring

end Gap212.Sieve
