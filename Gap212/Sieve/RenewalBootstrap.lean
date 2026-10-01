/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.AbelSummationBound
public import Gap212.Sieve.MoebiusRenewal

/-!
# The log-power decay of a summatory function, by bootstrapping the renewal identity

`Gap212.Sieve.MoebiusRenewal` proves the exact identity

  `S(x) · log x = -∑_{n ≤ x} b n · (V(x/n) - log (x/n))`,   (R)

for `b` an arithmetic function, `β` minus its Dirichlet logarithm, and `S`, `V` their summatory
functions. This file turns (R) into **decay of `S`**, given only that `V` satisfies Mertens' first
theorem with a log-power rate:

  `|V(y) - log y - c| ≤ K (1 + log y)^{-m}`   for one constant `c` and some `m ≥ 4`.

The conclusion is `|S(y)| ≤ C (1 + log y)^{-2}` (`Gap212.Sieve.exists_summatory_decay`).

## Why this is not circular, and where the gain comes from

Subtracting the constant `c` from (R) gives the exact relation

  `S(x) · (log x + c) = -∑_{n ≤ x} b n · ρ(x/n)`,   `ρ(y) = V(y) - log y - c`,

and the whole content is the bound on the right. Split it at `N = x / T`, with
`log T = √(log x)`:

* for `n ≤ N` the argument `x/n` is at least `T`, so `ρ(x/n)` is already small — of size
  `(log T)^{-m} = (log x)^{-m/2}` — and the weights contribute only `∑_{n ≤ N} |b n| ≪ log x`.
* for `n > N` the argument `x/n` is *bounded*, so `ρ(x/n)` is merely `O(1)` and this range is where
  a naive absolute bound stalls at `S(x) ≪ 1/log x` — the elementary Mertens barrier. The gain is
  recovered by **summation by parts** (`Gap212.Sieve.abs_sum_Ioc_mul_le`): over the short range
  `(N, x]` the partial sums of `b` are all *differences of `S` at arguments of size `x`*, hence
  small by the inductive hypothesis, while `ρ(x/·)` has total variation only
  `O(log T) = O(√(log x))`. That is a saving of `√(log x)` over the trivial estimate, and it is
  what makes the induction advance.

So one step improves the exponent by `1/2`, and six steps carry it from the trivial `-1` to `2`.
The self-improvement is legitimate because the improvement comes from the *narrowness* of the range
`(N, x]`, not from the conclusion: the inductive hypothesis is used only at arguments `≥ N`, where
`S` is nearly constant.

Exponents are tracked as integer powers of `Q(y) = √(1 + log y)`, so that a half-integer power of
`1 + log y` is an ordinary `zpow`; this is why the induction runs over `j : ℤ` from `-2` to `4`.

## Main results

* `Gap212.Sieve.summatory_decay_step`: **one bootstrap step** — `|S(y)| ≤ C Q(y)^{-j}` for all
  `y ≥ 1` implies `|S(y)| ≤ C' Q(y)^{-j-1}`, provided `j + 1 ≤ m`.
* `Gap212.Sieve.exists_summatory_decay`: six steps, giving `|S(y)| ≤ C (1 + log y)^{-2}`.
* `Gap212.Sieve.exists_one_add_log_pow_le_mul`: `(1 + log y)^m ≤ C y`, used to absorb `O(1/y)`
  error terms into the log-power shape.
* `Gap212.Sieve.zpow_le_two_pow_mul_zpow`, `Gap212.Sieve.sum_Ioo_telescope`: the two elementary
  facts the step spends, comparison of integer powers of comparable bases and telescoping.
-/

@[expose] public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction ArithmeticFunction.Moebius

namespace Gap212.Sieve


/-- `1 + log y ≥ 1` for `y ≥ 1`: the base of every power below is at least `1`, which is what makes
the monotonicity arguments in the exponent go the right way. -/
theorem one_le_one_add_log {y : ℝ} (hy : 1 ≤ y) : 1 ≤ 1 + Real.log y := by
  linarith [Real.log_nonneg hy]

/-- `Q(y) = √(1 + log y) ≥ 1` for `y ≥ 1`. -/
theorem one_le_sqrt_one_add_log {y : ℝ} (hy : 1 ≤ y) :
    1 ≤ Real.sqrt (1 + Real.log y) :=
  Real.one_le_sqrt.mpr (one_le_one_add_log hy)

/-- `Q(y)^2 = 1 + log y`: two steps of the induction are one power of `1 + log y`. -/
theorem sq_sqrt_one_add_log {y : ℝ} (hy : 1 ≤ y) :
    Real.sqrt (1 + Real.log y) ^ 2 = 1 + Real.log y :=
  Real.sq_sqrt (by linarith [one_le_one_add_log hy])

/-- Comparing integer powers of two comparable bases: if `B/2 ≤ A ≤ B` then
`A ^ i ≤ 2 ^ |i| * B ^ i` for every integer `i`, of either sign. -/
theorem zpow_le_two_pow_mul_zpow {A B : ℝ} (hA : 0 < A) (hhalf : B / 2 ≤ A) (hAB : A ≤ B)
    (i : ℤ) : A ^ i ≤ 2 ^ i.natAbs * B ^ i := by
  have hB : 0 < B := hA.trans_le hAB
  rcases le_or_gt 0 i with hi | hi
  · lift i to ℕ using hi with k
    simp only [zpow_natCast, Int.natAbs_natCast]
    exact (pow_le_pow_left₀ hA.le hAB k).trans
      (le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num)))
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨i.natAbs, by omega⟩
    rw [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    refine (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hhalf k)).trans_eq ?_
    rw [div_pow, inv_div, div_eq_mul_inv]

/-- `A ^ i ≤ B ^ |i|` when `1 ≤ A ≤ B`: for `i < 0` the left side is at most `1`. -/
theorem zpow_le_pow_natAbs {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) (i : ℤ) :
    A ^ i ≤ B ^ i.natAbs := by
  rcases le_or_gt 0 i with hi | hi
  · lift i to ℕ using hi with k
    simp only [zpow_natCast, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (by linarith) hAB k
  · exact (zpow_le_one_of_nonpos₀ hA hi.le).trans (one_le_pow₀ (hA.trans hAB))

/-- Telescoping over `Finset.Ioo`: `∑_{a < n < b} (f n - f (n+1)) = f (a+1) - f b`. This is what
turns the total variation of `ρ(x/·)` over the short range into `V(T) + log T`. -/
theorem sum_Ioo_telescope {a b : ℕ} (hab : a + 1 ≤ b) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.Ioo a b, (f n - f (n + 1)) = f (a + 1) - f b := by
  rw [← Finset.Ico_add_one_left_eq_Ioo, Finset.sum_Ico_eq_sum_range]
  refine (Finset.sum_range_sub' (fun i => f (a + 1 + i)) _).trans ?_
  congr 2
  omega

section Step

variable {b β : ArithmeticFunction ℝ}

/-- The renewal identity with a constant subtracted:
`S(y) (log y + c) = -∑_{n ≤ y} b n · (V(y/n) - log (y/n) - c)`. -/
theorem summatory_mul_log_add_eq (hbβ : b * β = -(b.pmul ArithmeticFunction.log)) {y : ℝ}
    (hy : 0 < y) (c : ℝ) :
    summatory b y * (Real.log y + c)
      = -∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, b n * (summatory β (y / n) - Real.log (y / n) - c) := by
  have h1 : ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, b n * (summatory β (y / n) - Real.log (y / n) - c)
      = (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, b n * (summatory β (y / n) - Real.log (y / n)))
        - c * summatory b y := by
    rw [summatory, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [h1]
  linarith [summatory_mul_log hbβ hy]

/-- If `(1 + log y)/4 ≤ 1 + log w` and `1 ≤ w ≤ y`, the hypothesis `|S(w)| Q(w)^j ≤ C` gives
`|S(w)| ≤ 2^|j| C Q(y)^{-j}`: `Q(w)` and `Q(y)` are comparable. -/
theorem abs_summatory_le_of_near {C : ℝ} {j : ℤ}
    (hA : ∀ y : ℝ, 1 ≤ y → |summatory b y| * Real.sqrt (1 + Real.log y) ^ j ≤ C) (hC : 0 ≤ C)
    {y w : ℝ} (hw : 1 ≤ w) (hlow : (1 + Real.log y) / 4 ≤ 1 + Real.log w) (hwy : w ≤ y) :
    |summatory b w| ≤ 2 ^ j.natAbs * C * Real.sqrt (1 + Real.log y) ^ (-j) := by
  have hQw : 0 < Real.sqrt (1 + Real.log w) := one_pos.trans_le (one_le_sqrt_one_add_log hw)
  have hhalf : Real.sqrt (1 + Real.log y) / 2 ≤ Real.sqrt (1 + Real.log w) :=
    Real.le_sqrt_of_sq_le (by rw [div_pow, sq_sqrt_one_add_log (hw.trans hwy)]; linarith)
  have hle : Real.sqrt (1 + Real.log w) ≤ Real.sqrt (1 + Real.log y) :=
    Real.sqrt_le_sqrt (by linarith [Real.log_le_log (by linarith : (0:ℝ) < w) hwy])
  have h2 := zpow_le_two_pow_mul_zpow hQw hhalf hle (-j)
  rw [Int.natAbs_neg] at h2
  calc |summatory b w| ≤ C * Real.sqrt (1 + Real.log w) ^ (-j) := by
        rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ (zpow_pos hQw j)]
        exact hA w hw
    _ ≤ C * (2 ^ j.natAbs * Real.sqrt (1 + Real.log y) ^ (-j)) := mul_le_mul_of_nonneg_left h2 hC
    _ = 2 ^ j.natAbs * C * Real.sqrt (1 + Real.log y) ^ (-j) := by ring

/-- Differences of `S` over the short range: if `2 ≤ N ≤ y` and `(1 + log y)/4 ≤ log N - 1`, then
`|S(n) - S(N)| ≤ 2 · 2^|j| C Q(y)^{-j}` for every integer `n ∈ [⌊N⌋, ⌊y⌋]`. -/
theorem abs_summatory_sub_le_of_near {C : ℝ} {j : ℤ}
    (hA : ∀ y : ℝ, 1 ≤ y → |summatory b y| * Real.sqrt (1 + Real.log y) ^ j ≤ C) (hC : 0 ≤ C)
    {y N : ℝ} (hN2 : 2 ≤ N) (hNy : N ≤ y) (hlogN : (1 + Real.log y) / 4 ≤ Real.log N - 1)
    {n : ℕ} (han : ⌊N⌋₊ ≤ n) (hnb : n ≤ ⌊y⌋₊) :
    |summatory b n - summatory b N|
      ≤ 2 * (2 ^ j.natAbs * C * Real.sqrt (1 + Real.log y) ^ (-j)) := by
  have hNa : N < ⌊N⌋₊ + 1 := Nat.lt_floor_add_one N
  have hnRa : (⌊N⌋₊ : ℝ) ≤ n := by exact_mod_cast han
  have hlow : (1 + Real.log y) / 4 ≤ 1 + Real.log (n:ℝ) := by
    have h1 := Real.log_le_log (by linarith) (by linarith : N / 2 ≤ (n:ℝ))
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  linarith [abs_sub (summatory b n) (summatory b N),
    abs_summatory_le_of_near hA hC (by linarith) hlow
      ((Nat.cast_le.mpr hnb).trans (Nat.floor_le (by linarith))),
    abs_summatory_le_of_near hA hC (by linarith) (by linarith) hNy]

/-- The deviation `g n = ρ(y/n)` has total variation at most `2s + |c| + K` over the short range
`(⌊N⌋, ⌊y⌋)` when `y / N = exp s`: both `V(y/·)` and `log (y/·)` are monotone there. -/
theorem sum_abs_sub_deviation_le (hβ0 : ∀ n, 0 ≤ β n) {c K : ℝ}
    (hK : ∀ w : ℝ, 1 ≤ w → |summatory β w - Real.log w - c| ≤ K) {y N s : ℝ}
    (hN1 : 1 ≤ N) (hNy : N ≤ y) (hs : 0 ≤ s) (hyN : y / N = Real.exp s) {g : ℕ → ℝ}
    (hg : g = fun n : ℕ => summatory β (y / n) - Real.log (y / n) - c) :
    ∑ n ∈ Finset.Ioo ⌊N⌋₊ ⌊y⌋₊, |g n - g (n + 1)| ≤ 2 * s + |c| + K := by
  subst hg
  have hypos : 0 < y := by linarith
  have ha1 : 1 ≤ ⌊N⌋₊ := Nat.le_floor (by exact_mod_cast hN1)
  have hNa : N < ⌊N⌋₊ + 1 := Nat.lt_floor_add_one N
  have hbby : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hypos.le
  rcases le_or_gt ⌊y⌋₊ (⌊N⌋₊ + 1) with hba | hba
  · rw [Finset.eq_empty_of_forall_notMem (s := Finset.Ioo _ _) fun n hn => by
      rw [Finset.mem_Ioo] at hn; omega, Finset.sum_empty]
    linarith [abs_nonneg c, (abs_nonneg _).trans (hK 1 le_rfl)]
  have hbbR1 : (1:ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast (by omega : 1 ≤ ⌊y⌋₊)
  have hmono := monotone_summatory hβ0
  have hdiv1 : y / ((⌊N⌋₊ + 1 : ℕ) : ℝ) ≤ Real.exp s := by
    rw [← hyN]
    exact div_le_div_of_nonneg_left hypos.le (by linarith) (by push_cast; linarith)
  have hWtop : summatory β (y / ((⌊N⌋₊ + 1 : ℕ) : ℝ)) ≤ s + |c| + K := by
    have h2 := hK (Real.exp s) (Real.one_le_exp hs)
    rw [Real.log_exp] at h2
    linarith [le_abs_self c, (abs_le.mp h2).2, hmono hdiv1]
  have hGtop : Real.log (y / ((⌊N⌋₊ + 1 : ℕ) : ℝ)) ≤ s :=
    (Real.log_le_log (by positivity) hdiv1).trans_eq (Real.log_exp s)
  have hWbot : (0:ℝ) ≤ summatory β (y / (⌊y⌋₊ : ℝ)) := summatory_nonneg hβ0 _
  have hGbot : (0:ℝ) ≤ Real.log (y / (⌊y⌋₊ : ℝ)) :=
    Real.log_nonneg ((one_le_div (by linarith)).mpr hbby)
  have hstep : ∀ n ∈ Finset.Ioo ⌊N⌋₊ ⌊y⌋₊,
      |(summatory β (y / n) - Real.log (y / n) - c)
        - (summatory β (y / ((n + 1 : ℕ) : ℝ)) - Real.log (y / ((n + 1 : ℕ) : ℝ)) - c)|
      ≤ (summatory β (y / (n:ℝ)) - summatory β (y / ((n + 1 : ℕ) : ℝ)))
        + (Real.log (y / (n:ℝ)) - Real.log (y / ((n + 1 : ℕ) : ℝ))) := by
    intro n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast ha1.trans (Finset.mem_Ioo.mp hn).1.le
    have hdec : y / ((n + 1 : ℕ) : ℝ) ≤ y / (n:ℝ) :=
      div_le_div_of_nonneg_left hypos.le (by linarith) (by push_cast; linarith)
    rw [abs_le]
    constructor <;> linarith [hmono hdec, Real.log_le_log (by positivity) hdec]
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_add_distrib, sum_Ioo_telescope hba.le (fun n : ℕ => summatory β (y / (n:ℝ))),
    sum_Ioo_telescope hba.le (fun n : ℕ => Real.log (y / (n:ℝ)))]
  linarith

/-- The long range `n ≤ N` of the renewal sum, where `y / n ≥ exp s`: there
`|ρ(y/n)| ≤ K (1 + s)^{-m}`, against total weight `∑_{n ≤ N} |b n| ≤ K₁ (1 + log y)`. -/
theorem abs_sum_mul_deviation_le {K₁ : ℝ} (hK₁ : 0 ≤ K₁)
    (hV1 : ∀ y : ℝ, 1 ≤ y → ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, |b n| ≤ K₁ * (1 + Real.log y))
    {c K : ℝ} {m : ℕ} (hK : 0 ≤ K)
    (hρ : ∀ y : ℝ, 1 ≤ y → |summatory β y - Real.log y - c| ≤ K / (1 + Real.log y) ^ m)
    {y N s : ℝ} (hN1 : 1 ≤ N) (hNy : N ≤ y) (hs : 0 ≤ s) (hyN : y / N = Real.exp s)
    {g : ℕ → ℝ} (hg : g = fun n : ℕ => summatory β (y / n) - Real.log (y / n) - c) :
    |∑ n ∈ Finset.Ioc 0 ⌊N⌋₊, b n * g n| ≤ K₁ * (1 + Real.log y) * (K / (1 + s) ^ m) := by
  subst hg
  have hypos : 0 < y := by linarith
  have hPpos : (0:ℝ) < (1 + s) ^ m := by positivity
  calc |∑ n ∈ Finset.Ioc 0 ⌊N⌋₊, b n * (summatory β (y / n) - Real.log (y / n) - c)|
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊N⌋₊, |b n| * (K / (1 + s) ^ m) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
        obtain ⟨hn0, hna⟩ := Finset.mem_Ioc.mp hn
        have hexp : Real.exp s ≤ y / (n:ℝ) := by
          rw [← hyN]
          exact div_le_div_of_nonneg_left hypos.le (by exact_mod_cast hn0)
            ((Nat.cast_le.mpr hna).trans (Nat.floor_le (by linarith)))
        have hlogs : s ≤ Real.log (y / (n:ℝ)) :=
          (Real.le_log_iff_exp_le (by linarith [Real.exp_pos s])).mpr hexp
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ((hρ _ ((Real.one_le_exp hs).trans hexp)).trans ?_)
          (abs_nonneg _)
        exact div_le_div_of_nonneg_left hK hPpos (pow_le_pow_left₀ (by linarith) (by linarith) m)
    _ = (∑ n ∈ Finset.Ioc 0 ⌊N⌋₊, |b n|) * (K / (1 + s) ^ m) := by rw [Finset.sum_mul]
    _ ≤ K₁ * (1 + Real.log y) * (K / (1 + s) ^ m) :=
        mul_le_mul_of_nonneg_right ((hV1 N hN1).trans (mul_le_mul_of_nonneg_left
          (by linarith [Real.log_le_log (by linarith) hNy]) hK₁)) (by positivity)

/-- The long-range term of the step, multiplied back by `Q^{j+1}`, is at most `4 K K₁`. -/
theorem first_term_le {K K₁ L s Q : ℝ} {j : ℤ} {m : ℕ} (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁)
    (hL : 16 ≤ L) (hs : 0 ≤ s) (hQ1 : 1 ≤ Q) (hQs : Q ≤ 1 + s) (hjm : j + 1 ≤ (m : ℤ)) :
    (2 / L) * (K₁ * (1 + L) * (K / (1 + s) ^ m)) * Q ^ (j + 1) ≤ 4 * K * K₁ := by
  have hL0 : L ≠ 0 := (by linarith : (0:ℝ) < L).ne'
  have hZP : Q ^ (j + 1) ≤ (1 + s) ^ m :=
    ((zpow_le_zpow_right₀ hQ1 hjm).trans_eq (zpow_natCast Q m)).trans
      (pow_le_pow_left₀ (by linarith) hQs m)
  calc (2 / L) * (K₁ * (1 + L) * (K / (1 + s) ^ m)) * Q ^ (j + 1)
      ≤ (2 / L) * (K₁ * (1 + L) * (K / (1 + s) ^ m)) * ((1 + s) ^ m) :=
        mul_le_mul_of_nonneg_left hZP (by positivity)
    _ = 2 * K₁ * (1 + L) * K / L := by field_simp
    _ ≤ 4 * K * K₁ := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg (mul_nonneg hK hK₁) (by linarith : (0:ℝ) ≤ L - 1)]

/-- The short-range term of the step, multiplied back by `Q^{j+1}`, is
at most `2^{|j|+3} C (3K + 2 + |c|)`: the variation `O(s)` is paid for by `Q ≤ 1 + s ≪ s^2 / s`. -/
theorem second_term_le {K C c L s Q : ℝ} {j : ℤ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hs2 : s ^ 2 = L)
    (hs4 : 4 ≤ s) (hQ : 0 < Q) (hQs : Q ≤ 1 + s) :
    (2 / L) * (2 * (2 ^ j.natAbs * C * Q ^ (-j)) * (K + (2 * s + |c| + K))) * Q ^ (j + 1)
      ≤ 2 ^ (j.natAbs + 3) * C * (3 * K + 2 + |c|) := by
  have hL : 16 ≤ L := by nlinarith
  have hQprod : Q ^ (-j) * Q ^ (j + 1) = Q := by
    rw [← zpow_add₀ hQ.ne', show -j + (j + 1) = 1 by ring, zpow_one]
  have hWQ : (K + (2 * s + |c| + K)) * Q ≤ 2 * L * (3 * K + 2 + |c|) := by
    calc (K + (2 * s + |c| + K)) * Q ≤ (s * (2 * K + 2 + |c|)) * (2 * s) :=
          mul_le_mul (by nlinarith [abs_nonneg c]) (by linarith) hQ.le (by positivity)
      _ ≤ 2 * L * (3 * K + 2 + |c|) := by
          rw [← hs2]
          nlinarith [mul_nonneg (sq_nonneg s) hK]
  rw [show (2 / L) * (2 * (2 ^ j.natAbs * C * Q ^ (-j)) * (K + (2 * s + |c| + K)))
      * Q ^ (j + 1) = 4 * (2 ^ j.natAbs * C)
        * ((K + (2 * s + |c| + K)) * (Q ^ (-j) * Q ^ (j + 1))) / L by ring,
    hQprod, div_le_iff₀ (by linarith), pow_add]
  nlinarith [mul_le_mul_of_nonneg_left hWQ (by positivity : (0:ℝ) ≤ 4 * (2 ^ j.natAbs * C))]

/-- **The bootstrap step for large `y`**, `log y ≥ max 16 (4|c|)`: split the renewal sum at
`N = y / exp √(log y)`, bound the long range directly and the short range by summation by parts. -/
theorem abs_summatory_mul_zpow_le_of_large
    (hbβ : b * β = -(b.pmul ArithmeticFunction.log)) (hβ0 : ∀ n, 0 ≤ β n)
    {K₁ : ℝ} (hK₁ : 0 ≤ K₁)
    (hV1 : ∀ y : ℝ, 1 ≤ y → ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, |b n| ≤ K₁ * (1 + Real.log y))
    {c K : ℝ} {m : ℕ} (hK : 0 ≤ K)
    (hρ : ∀ y : ℝ, 1 ≤ y → |summatory β y - Real.log y - c| ≤ K / (1 + Real.log y) ^ m)
    {j : ℤ} (hjm : j + 1 ≤ (m : ℤ)) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ y : ℝ, 1 ≤ y → |summatory b y| * Real.sqrt (1 + Real.log y) ^ j ≤ C)
    {y : ℝ} (hy : 1 ≤ y) (hL16 : 16 ≤ Real.log y) (hLc : 4 * |c| ≤ Real.log y) :
    |summatory b y| * Real.sqrt (1 + Real.log y) ^ (j + 1)
      ≤ 4 * K * K₁ + 2 ^ (j.natAbs + 3) * C * (3 * K + 2 + |c|) := by
  have hrho : ∀ w : ℝ, 1 ≤ w → |summatory β w - Real.log w - c| ≤ K := fun w hw =>
    (hρ w hw).trans (div_le_self hK (one_le_pow₀ (one_le_one_add_log hw)))
  have hypos : (0:ℝ) < y := by linarith
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (Real.log y) := ⟨_, rfl⟩
  have hs2 : s ^ 2 = Real.log y := by rw [hsdef, Real.sq_sqrt (by linarith)]
  have hs4 : (4:ℝ) ≤ s := hsdef ▸ Real.le_sqrt_of_sq_le (by linarith)
  obtain ⟨N, hNdef⟩ : ∃ N, N = Real.exp (Real.log y - s) := ⟨_, rfl⟩
  have hlogN : Real.log N = Real.log y - s := by rw [hNdef, Real.log_exp]
  have hN2 : (2:ℝ) ≤ N := hNdef ▸ le_trans (by linarith [Real.add_one_le_exp (1:ℝ)])
    (Real.exp_le_exp.mpr (by nlinarith : (1:ℝ) ≤ Real.log y - s))
  have hNy : N ≤ y := by
    rw [hNdef, ← Real.exp_log hypos]
    exact Real.exp_le_exp.mpr (by rw [Real.log_exp]; linarith)
  have hyN : y / N = Real.exp s := by
    rw [hNdef, Real.exp_sub, Real.exp_log hypos, div_div_cancel₀ hypos.ne']
  have hab : ⌊N⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hNy
  set g : ℕ → ℝ := fun n => summatory β (y / n) - Real.log (y / n) - c with hgdef
  have hQ1 : 1 ≤ Real.sqrt (1 + Real.log y) := one_le_sqrt_one_add_log hy
  have hQs : Real.sqrt (1 + Real.log y) ≤ 1 + s :=
    (Real.sqrt_le_sqrt (by nlinarith : 1 + Real.log y ≤ (1 + s) ^ 2)).trans_eq
      (Real.sqrt_sq (by linarith))
  have hSig1 := abs_sum_mul_deviation_le hK₁ hV1 hK hρ (by linarith) hNy (by linarith) hyN hgdef
  have hgbb : |g ⌊y⌋₊| ≤ K := hrho _ ((one_le_div (by exact_mod_cast Nat.floor_pos.mpr hy)).mpr
    (Nat.floor_le hypos.le))
  have hSig2 := (abs_sum_Ioc_mul_le (u := ⇑b) (S := fun n => summatory b n - summatory b N) hab
    (fun n han _ => by
      obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [summatory_natCast, summatory_natCast, Finset.sum_Ioc_succ_top (Nat.zero_le p)]
      ring)
    (sub_eq_zero.mpr (summatory_natCast b _))
    (fun n han hnb => abs_summatory_sub_le_of_near hA hC hN2 hNy (by nlinarith) han hnb)
    (sum_abs_sub_deviation_le hβ0 hrho (by linarith) hNy (by linarith) hyN hgdef)).trans
    (mul_le_mul_of_nonneg_left (add_le_add hgbb le_rfl) (by positivity))
  have hkey := summatory_mul_log_add_eq hbβ hypos c
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hab] at hkey
  have hmain : |summatory b y| * (Real.log y / 2) ≤ |summatory b y * (Real.log y + c)| := by
    rw [abs_mul, abs_of_nonneg (by linarith [neg_abs_le c] : (0:ℝ) ≤ Real.log y + c)]
    exact mul_le_mul_of_nonneg_left (by linarith [neg_abs_le c]) (abs_nonneg _)
  rw [hkey, abs_neg] at hmain
  have hSy : |summatory b y| ≤ (2 / Real.log y) * (K₁ * (1 + Real.log y) * (K / (1 + s) ^ m)
      + 2 * (2 ^ j.natAbs * C * Real.sqrt (1 + Real.log y) ^ (-j)) * (K + (2 * s + |c| + K))) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    linarith [hmain.trans ((abs_add_le _ _).trans (add_le_add hSig1 hSig2))]
  linarith [mul_le_mul_of_nonneg_right hSy (zpow_pos (one_pos.trans_le hQ1) (j + 1)).le,
    first_term_le hK hK₁ hL16 (by linarith) hQ1 hQs hjm,
    second_term_le (c := c) (j := j) hK hC hs2 hs4 (one_pos.trans_le hQ1) hQs]

/-- **One bootstrap step.** Assume `β` is minus the Dirichlet logarithm of `b`, that `β ≥ 0`, that
`∑_{n ≤ y} |b n| ≤ K₁ (1 + log y)`, and that `V = summatory β` satisfies Mertens' first theorem to
order `m`:  `|V(y) - log y - c| ≤ K (1 + log y)^{-m}`.  Then the bound
`|S(y)| ≤ C · Q(y)^{-j}` for all `y ≥ 1` upgrades to `|S(y)| ≤ C' · Q(y)^{-j-1}`, where
`Q(y) = √(1 + log y)` — a gain of half a power of `1 + log y` — provided `j + 1 ≤ m`.

Both hypothesis and conclusion are written multiplicatively (`|S(y)| * Q(y)^j ≤ C`) so that no
division by a power appears, and the exponent is an *integer* power of `Q`, which is how a
half-integer power of `1 + log y` is kept inside `zpow`.

The proof is the split described in this file's module docstring: `Σ₁` over `n ≤ N`, where the
deviation `ρ(x/n)` is small because `x/n ≥ exp √(log x)`, and `Σ₂` over `N < n ≤ x`, where it is
only `O(1)` and the gain comes from summation by parts against the inductive hypothesis. -/
theorem summatory_decay_step
    (hbβ : b * β = -(b.pmul ArithmeticFunction.log)) (hβ0 : ∀ n, 0 ≤ β n)
    {K₁ : ℝ}
    (hV1 : ∀ y : ℝ, 1 ≤ y → ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, |b n| ≤ K₁ * (1 + Real.log y))
    {c K : ℝ} {m : ℕ}
    (hρ : ∀ y : ℝ, 1 ≤ y → |summatory β y - Real.log y - c| ≤ K / (1 + Real.log y) ^ m)
    {j : ℤ} (hjm : j + 1 ≤ (m : ℤ)) {C : ℝ}
    (hA : ∀ y : ℝ, 1 ≤ y → |summatory b y| * Real.sqrt (1 + Real.log y) ^ j ≤ C) :
    ∃ C' : ℝ, ∀ y : ℝ, 1 ≤ y →
      |summatory b y| * Real.sqrt (1 + Real.log y) ^ (j + 1) ≤ C' := by
  have hK : 0 ≤ K := by simpa using (abs_nonneg _).trans (hρ 1 le_rfl)
  have hK₁ : 0 ≤ K₁ := by
    simpa using (Finset.sum_nonneg fun n _ => abs_nonneg (b n)).trans (hV1 1 le_rfl)
  have hC : 0 ≤ C := (mul_nonneg (abs_nonneg _) (by positivity)).trans (hA 1 le_rfl)
  have habs : ∀ y : ℝ, 1 ≤ y → |summatory b y| ≤ K₁ * (1 + Real.log y) := fun y hy =>
    (Finset.abs_sum_le_sum_abs _ _).trans (hV1 y hy)
  set L₀ : ℝ := max 16 (4 * |c|)
  refine ⟨max (K₁ * (1 + L₀) * (1 + L₀) ^ (j + 1).natAbs)
    (4 * K * K₁ + 2 ^ (j.natAbs + 3) * C * (3 * K + 2 + |c|)), fun y hy => ?_⟩
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  rcases le_or_gt (Real.log y) L₀ with hsmall | hbig
  · have hQ1 := one_le_sqrt_one_add_log hy
    have hQ2 : Real.sqrt (1 + Real.log y) ≤ 1 + L₀ := by
      linarith [Real.sqrt_le_self_iff.mpr (Or.inr (one_le_one_add_log hy))]
    exact le_trans (mul_le_mul ((habs y hy).trans (mul_le_mul_of_nonneg_left (by linarith) hK₁))
      (zpow_le_pow_natAbs hQ1 hQ2 _) (zpow_pos (one_pos.trans_le hQ1) _).le (by positivity))
      (le_max_left _ _)
  exact (abs_summatory_mul_zpow_le_of_large hbβ hβ0 hK₁ hV1 hK hρ hjm hC hA hy
    ((le_max_left _ _).trans hbig.le) ((le_max_right _ _).trans hbig.le)).trans (le_max_right _ _)





/-- `(1 + log y)^m ≤ C y` for one `C` and all `y ≥ 1`: a log power is dominated by the identity. -/
theorem exists_one_add_log_pow_le_mul (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 ≤ y → (1 + Real.log y) ^ m ≤ C * y := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := m)).def (by norm_num : (0:ℝ) < 1)
  obtain ⟨y₁, hy₁⟩ := (Filter.eventually_atTop.mp
    (h.and (Filter.eventually_ge_atTop (Real.exp 1))))
  set y₀ := max y₁ (Real.exp 1)
  have hy₀1 : (1:ℝ) ≤ y₀ :=
    le_trans (by linarith [Real.add_one_le_exp (1:ℝ)]) (le_max_right _ _)
  refine ⟨max ((2:ℝ) ^ m) ((1 + Real.log y₀) ^ m), by positivity, fun y hy => ?_⟩
  have hy0 : (0:ℝ) < y := by linarith
  rcases le_or_gt y y₀ with hle | hgt
  · exact (pow_le_pow_left₀ (by linarith [Real.log_nonneg hy])
      (by linarith [Real.log_le_log hy0 hle]) m).trans
      ((le_max_right _ _).trans (le_mul_of_one_le_right (by positivity) hy))
  obtain ⟨hbound, hey⟩ := hy₁ y (le_trans (le_max_left _ _) hgt.le)
  have hylog : (1:ℝ) ≤ Real.log y := (Real.le_log_iff_exp_le hy0).mpr hey
  have h2 : Real.log y ^ m ≤ y := by
    simpa [abs_of_nonneg hy0.le, abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.log y)] using hbound
  calc (1 + Real.log y) ^ m ≤ (2 * Real.log y) ^ m :=
        pow_le_pow_left₀ (by linarith) (by linarith) m
    _ = 2 ^ m * Real.log y ^ m := mul_pow _ _ _
    _ ≤ max ((2:ℝ) ^ m) ((1 + Real.log y₀) ^ m) * y :=
        mul_le_mul (le_max_left _ _) h2 (by positivity) (by positivity)

/-- **The decay, by six bootstrap steps.** Under the hypotheses of
`Gap212.Sieve.summatory_decay_step` with `m ≥ 4`, `|S(y)| ≤ C (1 + log y)^{-2}` for all `y ≥ 1`.

The induction starts at the trivial `|S(y)| ≤ K₁ (1 + log y)`, i.e. exponent `j = -2` in powers of
`Q(y) = √(1 + log y)`, and six steps carry `j` to `4`, which is `(1 + log y)^2`. Each step needs
`j + 1 ≤ m`, so `m ≥ 4` is exactly what the last one spends. -/
theorem exists_summatory_decay
    (hbβ : b * β = -(b.pmul ArithmeticFunction.log)) (hβ0 : ∀ n, 0 ≤ β n)
    {K₁ : ℝ}
    (hV1 : ∀ y : ℝ, 1 ≤ y → ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, |b n| ≤ K₁ * (1 + Real.log y))
    {c K : ℝ} {m : ℕ} (hm : 4 ≤ m)
    (hρ : ∀ y : ℝ, 1 ≤ y → |summatory β y - Real.log y - c| ≤ K / (1 + Real.log y) ^ m) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y → |summatory b y| ≤ C / (1 + Real.log y) ^ 2 := by
  have hstart : ∀ y : ℝ, 1 ≤ y →
      |summatory b y| * Real.sqrt (1 + Real.log y) ^ (-2 : ℤ) ≤ K₁ := by
    intro y hy
    rw [show (-2 : ℤ) = -((2:ℕ):ℤ) by norm_num, zpow_neg, zpow_natCast, sq_sqrt_one_add_log hy,
      mul_inv_le_iff₀ (by linarith [one_le_one_add_log hy])]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (hV1 y hy)
  obtain ⟨C1, h1⟩ := summatory_decay_step hbβ hβ0 hV1 hρ (j := (-2 : ℤ)) (by omega) hstart
  obtain ⟨C2, h2⟩ := summatory_decay_step hbβ hβ0 hV1 hρ (j := (-2 : ℤ) + 1) (by omega) h1
  obtain ⟨C3, h3⟩ := summatory_decay_step hbβ hβ0 hV1 hρ (j := (-2 : ℤ) + 1 + 1) (by omega) h2
  obtain ⟨C4, h4⟩ :=
    summatory_decay_step hbβ hβ0 hV1 hρ (j := (-2 : ℤ) + 1 + 1 + 1) (by omega) h3
  obtain ⟨C5, h5⟩ :=
    summatory_decay_step hbβ hβ0 hV1 hρ (j := (-2 : ℤ) + 1 + 1 + 1 + 1) (by omega) h4
  obtain ⟨C6, h6⟩ :=
    summatory_decay_step hbβ hβ0 hV1 hρ (j := (-2 : ℤ) + 1 + 1 + 1 + 1 + 1) (by omega) h5
  refine ⟨C6, fun y hy => ?_⟩
  have h := h6 y hy
  rw [show ((-2 : ℤ) + 1 + 1 + 1 + 1 + 1 + 1) = ((2 * 2 : ℕ) : ℤ) by norm_num, zpow_natCast,
    pow_mul, sq_sqrt_one_add_log hy] at h
  rwa [le_div_iff₀ (pow_pos (by linarith [one_le_one_add_log hy]) 2)]

end Step

end Gap212.Sieve
