/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MertensMuPhi
public import Gap212.Sieve.OneCoordLcmSelberg
public import Gap212.Sieve.OneCoordTotientRefutation
public import Gap212.Sieve.TotientGramRiemannSum

/-!
# Selberg diagonalisation of the totient one-coordinate estimate for supported profiles

`Gap212.Sieve.OneCoordTotientDecayAtLevelOfSupport` has no slack, for the same reason as the
reciprocal-kernel statement `Gap212.Sieve.OneCoordLcmDecayAtLevelOfSupport`: the pair sum is
`≍1/B_x` already at `e = 1` while the diagonal alone is much larger, so no term-by-term bound can
prove it. What can is the Selberg change of variables
`Gap212.Sieve.sum_pairs_div_totient_lcm_eq_sum_moebiusTotient_mul`, which replaces the pair sum by

  `∑_{r ≤ B} (μ*φ)(r)·z_r·z'_r`,
  `z_r = ∑_{d ∈ [1,B], (d,W)=1, r ∣ d} μ(d)F(\log_xd)/φ(d)`,

after which absolute values are no longer lossy. This file proves that implication at **every**
modulus `e`, at `s = 3/4`.

## The one-variable input, and how it differs from the reciprocal kernel's

`Gap212.Sieve.SmoothMoebiusTotientInnerBound` asks

  `|z_r| ≤ C·(W/φ(W))/((μ*φ)(r)·\log x)`,  uniformly in `r ≥ 1` and in `B ≥ x^β`.

**The denominator is `(μ*φ)(r)`, not `φ(r)` and not `r`.** This is where the two kernels
differ. With `d = rm` and `u = \log_xr`,

  `z_r = (μ(r)/φ(r))·∑_{(m,rW)=1}μ(m)F(u + \log_xm)/φ(m)`,

and the inner sum's local correction at a modulus `q` is `∏_{p ∣ q, p > 2}(p-1)/(p-2)` — the
Dirichlet series is `∏_{p ∤ q}(1 - 1/((p-1)p^s))`, whose `p ∣ q` factors are removed at `s = 0` —
so the correction at `q = rW` contributes `φ(r)/(μ*φ)(r)`, which cancels the `1/φ(r)` in front and
leaves `1/(μ*φ)(r)`. The reciprocal kernel has correction `q/φ(q)` instead, contributing `r/φ(r)`
against a `1/r`, leaving `1/φ(r)`. The two weights `1/φ(r)` and `1/(μ*φ)(r)` differ by
`∏_{p ∣ r}(p-1)/(p-2)`, which is unbounded on the moduli in play, so neither statement implies the
other.

**Calibration against the two witnesses that decide the denominator.** The consistency check is the
modulus sum: with the diagonalisation weight `(μ*φ)(r)` the square of the input integrates
`(μ*φ)(r)/(μ*φ)(r)^2 = 1/(μ*φ)(r)`, and
`Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime` — a *different* Mertens sum from the
reciprocal kernel's, with the extra constant `(∏_{p ∤ W}(1-1/(p-1)^2))^{-1}` — sums that over the
class to `(φ(W)/W)\log N` up to a factor tending to `1`. The two `W/φ(W)` of the input then cancel
one `φ(W)/W` and leave `K/B_x` exactly. Both the reciprocal kernel's `1/r` and the reciprocal
kernel's `1/φ(r)` fail this check here: `1/r` by the factor `r/(μ*φ)(r)`, unbounded, and `1/φ(r)` by
`φ(r)/(μ*φ)(r)`, also unbounded — so the primorial-block witness that refutes the `1/r` reading of
the reciprocal kernel's input refutes both readings of this one.

**Quantifier order.** `C` is chosen **before** `x`, `B` and `r`: `∀ β, ∀ F, ∃ C, ∀ᶠ x, ∀ B r`. A
constant quantified after the modulus would be inert — the consumer drives `x → ∞` with `C` fixed
and sums over `r`, so a `C` depending on either says nothing.

## Main results

`Gap212.Sieve.oneCoordTotientDecayAtLevelOfSupport_of_smoothMoebiusTotientInnerBound`:
`Gap212.Sieve.OneCoordTotientDecayAtLevelOfSupport (3/4)` in full, at every modulus, from the
one-variable input alone; and `1/2 < 3/4`, so
`Gap212.Sieve.tendsto_boxDivisorSum_sub_sievedDivisorSum_of_smoothInnerBound` chains it into the
sieving error. (Without the support clause the two-variable estimate is false:
`Gap212.Sieve.not_oneCoordTotientDecay`, `Gap212.Sieve.not_oneCoordTotientDecayAtLevel`.)

**And the one-variable input is a theorem**, `Gap212.Sieve.smoothMoebiusTotientInnerBound` in
`Gap212.Sieve.SmoothTotientInner`, so nothing here is conditional:
`Gap212.Sieve.oneCoordTotientDecayAtLevelOfSupport_three_quarters` and
`Gap212.Sieve.totientSievingError` are unconditional; in particular
`Gap212.Sieve.TotientSievingError 44`, which is stated at `β ≥ 1`, is proved.

**All three hypotheses are used.** The truncation `x^β ≤ B` is what the
pointwise input is quantified over. The support clause makes `z_r` vanish for `r > x^β`
(`Gap212.Sieve.innerMoebiusTotientSum_eq_zero_of_rpow_lt`), so the modulus sum has length `β\log x`
rather than `\log B` — and without it the input is false at exactly the moduli `r ≍ x^β` where
`Gap212.Sieve.not_oneCoordTotientDecayAtLevel` lives, since there `z_r` is the single term
`μ(r)F(\log_xr)/φ(r)` and `φ(r)/(μ*φ)(r)\to\infty`. And `s < 1` pays for the divisor factors: the
whole `e`-dependence is `432^{ω(e)}/e`, and `432^{ω(e)} ≤ e^{1/4}` only because every prime factor
of `e` exceeds `432^4` (`Gap212.Sieve.pow_card_primeFactors_le_self`), which holds because `e` is
coprime to `W(x)`. At `s = 1` there is nothing to pay with.

## Where evenness of `W(x)` is spent

`(μ*φ)(2) = 0`, so every weight in this file is positive only on the **odd** squarefree integers.
The box is coprime to `W(x)`, which is even, so every modulus the diagonalisation sees is odd — and
that is used at each denominator, through
`Gap212.Sieve.one_le_moebiusTotient_of_odd_squarefree`. The same evenness is a hypothesis of
`Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime`.
-/

@[expose] public section

namespace Gap212.Sieve

open Asymptotics Filter Finset Gap212.Defs Gap212.GPY
open scoped ArithmeticFunction.Moebius

/-! ## Oddness, inherited from coprimality to an even modulus -/

/-- **A number coprime to an even modulus is odd.** Every weight of this file is positive only on
the odd integers, `(μ*φ)(2)` being `0`, and this is the one fact that supplies it. -/
theorem not_two_dvd_of_coprime {W r : ℕ} (hW : 2 ∣ W) (h : Nat.Coprime W r) : ¬ 2 ∣ r := fun h2 ↦
  absurd (Nat.dvd_one.mp (h ▸ Nat.dvd_gcd hW h2)) (by norm_num)

/-- **The lcm of two odd numbers is odd**, since it divides their product. -/
theorem not_two_dvd_lcm {r m : ℕ} (hr : ¬ 2 ∣ r) (hm : ¬ 2 ∣ m) : ¬ 2 ∣ Nat.lcm r m := fun h ↦
  (Nat.prime_two.dvd_mul.mp (h.trans (Nat.lcm_dvd_mul r m))).elim hr hm

/-! ## The Gram weight on the odd squarefree integers -/

/-- **Every prime factor of an odd number is at least `3`.** -/
theorem three_le_of_mem_primeFactors_of_odd {r p : ℕ} (hodd : ¬ 2 ∣ r) (hp : p ∈ r.primeFactors) :
    (3 : ℝ) ≤ (p : ℝ) := by
  have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
  have hp2 : p ≠ 2 := fun h ↦ hodd (h ▸ Nat.dvd_of_mem_primeFactors hp)
  exact_mod_cast show 3 ≤ p by omega

/-- **`(μ*φ)(r) ≥ 1` on an odd squarefree `r`**: it is `∏_{p ∣ r}(p-2)` and every prime factor is
at least `3`. This is what makes every denominator of the diagonalisation positive, and it is false
without oddness — `(μ*φ)(2) = 0`. -/
theorem one_le_moebiusTotient_of_odd_squarefree {r : ℕ} (hsf : Squarefree r) (hodd : ¬ 2 ∣ r) :
    1 ≤ moebiusTotient r := by
  rw [moebiusTotient_of_squarefree hsf]
  calc (1 : ℝ) = ∏ _p ∈ r.primeFactors, (1 : ℝ) := (Finset.prod_const_one).symm
    _ ≤ ∏ p ∈ r.primeFactors, ((p : ℝ) - 2) :=
        Finset.prod_le_prod (fun _ _ ↦ by norm_num)
          fun p hp ↦ by linarith [three_le_of_mem_primeFactors_of_odd hodd hp]

/-- **`(μ*φ)(r) ≤ r` on a squarefree `r`**, factor by factor. -/
theorem moebiusTotient_le_self {r : ℕ} (hsf : Squarefree r) : moebiusTotient r ≤ (r : ℝ) := by
  rw [moebiusTotient_of_squarefree hsf,
    show (r : ℝ) = ∏ p ∈ r.primeFactors, (p : ℝ) from by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsf]]
  refine Finset.prod_le_prod (fun p hp ↦ ?_) fun _ _ ↦ by linarith
  linarith [show (2 : ℝ) ≤ (p : ℝ) from by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le]

/-- **`(μ*φ)(r) ≤ φ(r)` on a squarefree `r`**, factor by factor: `p - 2 ≤ p - 1`.

With `Gap212.Sieve.moebiusTotient_le_self` this orders the three candidate denominators of the
one-variable input, `(μ*φ)(r) ≤ φ(r) ≤ r`, so the form
`Gap212.Sieve.SmoothMoebiusTotientInnerBound` states is the **strongest** of the three and the two
rejected readings are strictly weaker statements — the choice is not a weakening that dodges the
witnesses. It is also the step that makes the input's own calibration at `r ≍ x^β` come out: there
the left side is the single term `|F(\log_xr)|/φ(r)`, and the right side dominates it precisely
because `(μ*φ)(r) ≤ φ(r)`. -/
theorem moebiusTotient_le_totient {r : ℕ} (hsf : Squarefree r) :
    moebiusTotient r ≤ (Nat.totient r : ℝ) := by
  rw [moebiusTotient_of_squarefree hsf, totient_of_squarefree hsf]
  refine Finset.prod_le_prod (fun p hp ↦ ?_) fun _ _ ↦ by linarith
  linarith [show (2 : ℝ) ≤ (p : ℝ) from by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le]

/-- **`r ≤ 3^{ω(r)}·(μ*φ)(r)` on an odd squarefree `r`**: `p ≤ 3(p-2)` for `p ≥ 3`. The analogue of
`Gap212.Sieve.self_le_two_pow_card_primeFactors_mul_totient` for this kernel, with base `3` in
place of `2` — the local ratio is `p/(p-2)`, not `p/(p-1)`. -/
theorem self_le_three_pow_card_primeFactors_mul_moebiusTotient {r : ℕ} (hsf : Squarefree r)
    (hodd : ¬ 2 ∣ r) : (r : ℝ) ≤ 3 ^ #r.primeFactors * moebiusTotient r := by
  have hp3 : ∀ p ∈ r.primeFactors, (3 : ℝ) ≤ (p : ℝ) := fun _ ↦
    three_le_of_mem_primeFactors_of_odd hodd
  rw [moebiusTotient_of_squarefree hsf,
    show (r : ℝ) = ∏ p ∈ r.primeFactors, (p : ℝ) from by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsf],
    show (3 : ℝ) ^ #r.primeFactors = ∏ _p ∈ r.primeFactors, (3 : ℝ) from
      (Finset.prod_const _).symm,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun p hp ↦ by linarith [hp3 p hp])
    fun p hp ↦ by linarith [hp3 p hp]

/-- **`(μ*φ)(r)(μ*φ)(m) ≤ (r,m)·(μ*φ)([r,m])` on squarefree arguments** — the inequality that makes
the modulus-restricted diagonalisation summable, and the exact analogue of
`Gap212.Sieve.totient_mul_totient_le_gcd_mul_totient_lcm` for this kernel.

Both sides are products over primes: `∏_{p ∣ r}∏_{p ∣ m} = ∏_{p ∣ [r,m]}∏_{p ∣ (r,m)}`
(`Finset.prod_union_inter`, with `Nat.primeFactors_lcm` and `Nat.primeFactors_gcd`), so what is
left is `∏_{p ∣ (r,m)}(p-2) ≤ ∏_{p ∣ (r,m)}p`, i.e. `(μ*φ)((r,m)) ≤ (r,m)`. -/
theorem moebiusTotient_mul_le_gcd_mul_moebiusTotient_lcm {r m : ℕ} (hr : Squarefree r)
    (hm : Squarefree m) :
    moebiusTotient r * moebiusTotient m
      ≤ (Nat.gcd r m : ℝ) * moebiusTotient (Nat.lcm r m) := by
  have hgsf : Squarefree (Nat.gcd r m) := Squarefree.squarefree_of_dvd (Nat.gcd_dvd_left r m) hr
  have hlsf : Squarefree (Nat.lcm r m) := squarefree_lcm hr hm
  have hsplit : moebiusTotient (Nat.lcm r m) * moebiusTotient (Nat.gcd r m)
      = moebiusTotient r * moebiusTotient m := by
    rw [moebiusTotient_of_squarefree hr, moebiusTotient_of_squarefree hm,
      moebiusTotient_of_squarefree hlsf, moebiusTotient_of_squarefree hgsf,
      Nat.primeFactors_lcm hr.ne_zero hm.ne_zero, Nat.primeFactors_gcd hr.ne_zero hm.ne_zero]
    exact Finset.prod_union_inter
  rw [← hsplit, mul_comm (Nat.gcd r m : ℝ)]
  exact mul_le_mul_of_nonneg_left (moebiusTotient_le_self hgsf)
    (moebiusTotient_nonneg_of_squarefree hlsf)

/-! ## The bilinear Selberg diagonalisation at the totient denominator -/

/-- **The Selberg diagonalisation of a pair sum at the totient denominator, bilinear form.** For
weights `l`, `l'` on a finset `D ⊆ [1,B]`,

  `∑_{d,d' ∈ D} l(d)l'(d')/φ([d,d'])
     = ∑_{r ≤ B} (μ*φ)(r)·(∑_{d ∈ D, r ∣ d} l(d)/φ(d))(∑_{d' ∈ D, r ∣ d'} l'(d')/φ(d'))`.

`Gap212.Sieve.sum_pairs_div_totient_lcm_eq_sum_moebiusTotient_mul_sq` is the case `l = l'`; the
proof is the same `1/φ([d,d']) = φ((d,d'))/(φ(d)φ(d'))`, `∑_{r ∣ n}(μ*φ)(r) = φ(n)` and one
exchange of summation. The bilinear form is what a pair sum with two profiles needs. -/
theorem sum_pairs_div_totient_lcm_eq_sum_moebiusTotient_mul (B : ℕ) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ B) (l l' : ℕ → ℝ) :
    ∑ d ∈ D, ∑ d' ∈ D, l d * l' d' / (Nat.totient (Nat.lcm d d') : ℝ)
      = ∑ r ∈ Icc 1 B, moebiusTotient r * ((∑ d ∈ D with r ∣ d, l d / (Nat.totient d : ℝ))
          * ∑ d' ∈ D with r ∣ d', l' d' / (Nat.totient d' : ℝ)) := by
  simp_rw [Finset.sum_filter, Finset.sum_mul_sum, Finset.mul_sum, ite_zero_mul_ite_zero,
    mul_ite, mul_zero]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d' hd' ↦ ?_
  obtain ⟨hd1, hdB⟩ := hD d hd
  rw [← Finset.sum_filter, ← Finset.sum_mul, sum_filter_Icc_moebiusTotient_eq_totient_gcd hd1 hdB,
    div_totient_lcm_eq hd1 (hD d' hd').1]
  ring

/-! ## The one-variable sum the diagonalisation produces -/

/-- **The inner Möbius sum of the totient diagonalisation**,
`z_r = ∑_{d ∈ [1,B], (d,W(x))=1, r ∣ d} μ(d)F(\log_xd)/φ(d)` — the one-variable quantity that
carries all of the cancellation. Note the weight `1/φ(d)`, not the reciprocal kernel's `1/d`. -/
noncomputable def innerMoebiusTotientSum (x : ℝ) (F : ℝ → ℝ) (B r : ℕ) : ℝ :=
  ∑ d ∈ wBox x B with r ∣ d, (μ d : ℝ) * F (Notation.logx x d) / (Nat.totient d : ℝ)

/-- **Above the support the inner sum is empty of content.** If `F` vanishes from `β` on and
`x^β < r`, every `d` counted by `z_r` is `≥ r > x^β`. This makes the unbounded truncation `B`
harmless: the modulus sum runs over `r ≤ x^β`, not over `r ≤ B`. -/
theorem innerMoebiusTotientSum_eq_zero_of_rpow_lt {x : ℝ} (hx : 1 < x) {β : ℝ} {F : ℝ → ℝ}
    (hFβ : ∀ t : ℝ, β ≤ t → F t = 0) {B r : ℕ} (hr : x ^ β < (r : ℝ)) :
    innerMoebiusTotientSum x F B r = 0 := by
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  obtain ⟨hdB, hrd⟩ := Finset.mem_filter.mp hd
  have hrd' : (r : ℝ) ≤ d := by exact_mod_cast Nat.le_of_dvd (mem_wBox.mp hdB).1.1 hrd
  have h1 : Real.log (x ^ β) < Real.log d := Real.log_lt_log (by positivity) (hr.trans_le hrd')
  rw [Real.log_rpow (by linarith)] at h1
  rw [hFβ _ (by rw [Notation.logx, le_div_iff₀ (Real.log_pos hx)]; linarith), mul_zero, zero_div]

/-- **A modulus sharing a factor with `W(x)` sees nothing.** -/
theorem innerMoebiusTotientSum_eq_zero_of_not_coprime {x : ℝ} {F : ℝ → ℝ} {B r : ℕ}
    (hr : ¬ Nat.Coprime (W x) r) : innerMoebiusTotientSum x F B r = 0 := by
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  obtain ⟨hdB, hrd⟩ := Finset.mem_filter.mp hd
  exact absurd ((mem_wBox.mp hdB).2.coprime_dvd_right hrd) hr

/-- **A non-squarefree modulus sees only Möbius zeros.** -/
theorem innerMoebiusTotientSum_eq_zero_of_not_squarefree {x : ℝ} {F : ℝ → ℝ} {B r : ℕ}
    (hr : ¬ Squarefree r) : innerMoebiusTotientSum x F B r = 0 := by
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    fun h ↦ hr (h.squarefree_of_dvd (Finset.mem_filter.mp hd).2)]

/-- **The inner sum at an lcm modulus is the doubly-divisible sum.** -/
theorem innerMoebiusTotientSum_lcm (x : ℝ) (F : ℝ → ℝ) (B r m : ℕ) :
    innerMoebiusTotientSum x F B (Nat.lcm r m)
      = ∑ d ∈ wBox x B with (r ∣ d ∧ m ∣ d),
          (μ d : ℝ) * F (Notation.logx x d) / (Nat.totient d : ℝ) := by
  simp only [innerMoebiusTotientSum, Nat.lcm_dvd_iff]

/-! ## The one-variable input -/

/-- **The pointwise bound on the inner Möbius sum at the totient weight** — the one-variable input
the Selberg diagonalisation reduces the two-variable estimate to. For every profile vanishing from
`β` on there is a constant `C` with

  `|z_r| = |∑_{d ≤ B, (d,W)=1, r ∣ d} μ(d)F(\log_xd)/φ(d)| ≤ C·(W/φ(W))/((μ*φ)(r)\log x)`

for every large `x`, every truncation `B ≥ x^β` and every modulus `r ≥ 1`.

**`(μ*φ)(r)` is the right denominator and the reciprocal kernel's `φ(r)` is not.** With `d = rm` and
`u = \log_xr`, `z_r = (μ(r)/φ(r))∑_{(m,rW)=1}μ(m)F(u+\log_xm)/φ(m)`, and the inner sum's local
correction at modulus `q` is `∏_{p ∣ q, p>2}(p-1)/(p-2)`, which at `q = rW` contributes
`φ(r)/(μ*φ)(r)` and cancels the `1/φ(r)`. Three checks. At `r = 1` the statement is the classical
smoothed bound `≍1/\log x` and the constant is attained, so the power of `\log x` is sharp. At
`r > x^β` the left side is zero (`Gap212.Sieve.innerMoebiusTotientSum_eq_zero_of_rpow_lt`), which
is what makes the unbounded truncation harmless. And at `r ∈ (x^β/2, x^β)` the left side is the
single term `|F(\log_xr)|/φ(r) ≪ \|F'\|_∞\log2/(φ(r)\log x)`, which the right side dominates
because `(μ*φ)(r) ≤ φ(r)` (`Gap212.Sieve.moebiusTotient_le_totient`).

**The primorial witness.** Take `r = ∏_{v<p≤z}p` with `v = \log\log\log x`, so `r` is coprime to
`W(x)` and odd, and `z` with `r ≍ x^β/z`, so `m = 1` is the only survivor and
`z_r = μ(r)F(\log_xr)/φ(r)` with
`|F(\log_xr)| ≍ \|F'\|\log z/\log x`. The asserted bound reads
`\|F'\|_∞\log z·((μ*φ)(r)/φ(r)) ≤ C(W/φ(W))`, and
`(μ*φ)(r)/φ(r) = ∏_{v<p≤z}(1-1/(p-1)) ≍ \log v/\log z`, so both sides are `≍\log\log\log\log x` and
it survives on the constant — the same margin the reciprocal-kernel statement has, reached through a
*different* local factor. With `r` in place of `(μ*φ)(r)` the same witness refutes it by
`\log z/\log v`, and with `φ(r)` in place of `(μ*φ)(r)` it refutes it too, by the whole factor
`∏_{v<p≤z}(p-1)/(p-2) ≍ \log z/\log v`. So the denominator is pinned from both sides.

**A partial-sum bound would not do.** Even the modulus-aware
`|∑_{f≤w,(f,q)=1}μ(f)/φ(f)| ≤ C(q/φ(q))/(1+\log w)` loses a `\log\log x` under Abel summation
against the profile, which is why the profile is summed against the Möbius weight directly here.

**This is a theorem**, `Gap212.Sieve.smoothMoebiusTotientInnerBound`
(`Gap212.Sieve.SmoothTotientInner`). The route is *not* the reciprocal kernel's single smooth-number
decomposition: this kernel's local factor `1 - 1/((p-1)p^s)` vanishes at `s = 0` for `p = 2`, so
the weight that would remove the modulus in one step has infinite mass, and the modulus is instead
carried down to the reciprocal kernel at the *same* modulus first
(`Gap212.Sieve.moebiusTotientBelow_eq_sum_smoothDivWeight`). The `(μ*φ)(r)` of the denominator then
comes out of the *inequality* `r/φ(r)^2 ≤ 1/(μ*φ)(r)`
(`Gap212.Sieve.self_div_totient_sq_le_inv_moebiusTotient`), where the reciprocal kernel had an
identity. -/
def SmoothMoebiusTotientInnerBound : Prop :=
  ∀ β : ℝ, 0 < β → ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F →
    (∀ t : ℝ, β ≤ t → F t = 0) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, ∀ B r : ℕ, x ^ β ≤ (B : ℝ) → 1 ≤ r →
        |innerMoebiusTotientSum x F B r|
          ≤ C * ((W x : ℝ) / ((W x).totient : ℝ)) / (moebiusTotient r * Real.log x)


/-! ## The arithmetic of one class of the partition -/

/-- **The two moduli of one partition class, in one inequality.** For squarefree `e`, `a ∣ e` and
`c ∣ e/a`, writing `m = [[r,a],c]` and `n = [r,e/a]`,

  `(μ*φ)(r)^2(μ*φ)(e)(μ*φ)(c) ≤ (r,ce)·c·(μ*φ)(m)(μ*φ)(n)`.

The exact analogue of `Gap212.Sieve.totient_sq_mul_le_gcd_mul_totient_lcm_mul`, with
`Gap212.Sieve.moebiusTotient_mul_le_gcd_mul_moebiusTotient_lcm` for the two lcm steps and
`Gap212.Sieve.moebiusTotient_mul_of_coprime` for the factorisation
`(μ*φ)(ac)(μ*φ)(e/a) = (μ*φ)(e)(μ*φ)(c)`. The gcd collapse
`(r,ac)(r,e/a) ≤ (r,ce)·c` is kernel-independent and is reused from the reciprocal kernel
(`Gap212.Sieve.gcd_mul_gcd_dvd_mul_gcd`, `Gap212.Sieve.gcd_gcd_of_dvd`). -/
theorem moebiusTotient_sq_mul_le_gcd_mul_lcm_mul {e a c r : ℕ} (hesf : Squarefree e)
    (hae : a ∣ e) (hc : c ∣ e / a) (hrsf : Squarefree r) :
    moebiusTotient r * moebiusTotient r * (moebiusTotient e * moebiusTotient c)
      ≤ (Nat.gcd r (c * e) : ℝ) * (c : ℝ)
        * (moebiusTotient (Nat.lcm (Nat.lcm r a) c) * moebiusTotient (Nat.lcm r (e / a))) := by
  set b : ℕ := e / a
  have hmul : a * b = e := Nat.mul_div_cancel' hae
  have hcopab : Nat.Coprime a b :=
    (Nat.squarefree_mul_iff.mp (show Squarefree (a * b) by rw [hmul]; exact hesf)).1
  have hcopac : Nat.Coprime a c := hcopab.coprime_dvd_right hc
  have hbsf : Squarefree b := hesf.squarefree_of_dvd (Dvd.intro_left a hmul)
  have hasf : Squarefree a := hesf.squarefree_of_dvd hae
  have hcsf : Squarefree c := hbsf.squarefree_of_dvd hc
  have hacsf : Squarefree (a * c) := Nat.squarefree_mul_iff.mpr ⟨hcopac, hasf, hcsf⟩
  rw [Nat.lcm_assoc, hcopac.lcm_eq_mul]
  have hQ : a * c * b = c * e := by rw [← hmul]; ring
  -- the two lcm inequalities
  have h1 := moebiusTotient_mul_le_gcd_mul_moebiusTotient_lcm hrsf hacsf
  have h2 := moebiusTotient_mul_le_gcd_mul_moebiusTotient_lcm hrsf hbsf
  -- the gcds collapse
  have hcollapse : Nat.gcd r (a * c) * Nat.gcd r b ∣ Nat.gcd r (c * e) * c := by
    have h := gcd_mul_gcd_dvd_mul_gcd (Nat.gcd r (c * e)) (a * c) b
    rwa [gcd_gcd_of_dvd ⟨b, hQ.symm⟩, gcd_gcd_of_dvd ⟨a * c, hQ.symm.trans (mul_comm _ _)⟩,
      hcopab.gcd_mul_left_cancel c, Nat.gcd_eq_left hc] at h
  have he0 : 0 < e := Nat.pos_of_ne_zero hesf.ne_zero
  have hc0 : 0 < c := Nat.pos_of_ne_zero hcsf.ne_zero
  have hgle : (Nat.gcd r (a * c) * Nat.gcd r b : ℝ) ≤ (Nat.gcd r (c * e) * c : ℝ) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.mul_pos (Nat.gcd_pos_of_pos_right r (Nat.mul_pos hc0 he0)) hc0) hcollapse
  -- nonnegativity of every factor
  have hnr : 0 ≤ moebiusTotient r := moebiusTotient_nonneg_of_squarefree hrsf
  have hnb : 0 ≤ moebiusTotient b := moebiusTotient_nonneg_of_squarefree hbsf
  have hnm : 0 ≤ moebiusTotient (Nat.lcm r (a * c)) :=
    moebiusTotient_nonneg_of_squarefree (squarefree_lcm hrsf hacsf)
  have hnn : 0 ≤ moebiusTotient (Nat.lcm r b) :=
    moebiusTotient_nonneg_of_squarefree (squarefree_lcm hrsf hbsf)
  calc moebiusTotient r * moebiusTotient r * (moebiusTotient e * moebiusTotient c)
      = (moebiusTotient r * moebiusTotient (a * c)) * (moebiusTotient r * moebiusTotient b) := by
        rw [moebiusTotient_mul_of_coprime hcopac, ← hmul, moebiusTotient_mul_of_coprime hcopab]
        ring
    _ ≤ ((Nat.gcd r (a * c) : ℝ) * moebiusTotient (Nat.lcm r (a * c)))
          * ((Nat.gcd r b : ℝ) * moebiusTotient (Nat.lcm r b)) :=
        mul_le_mul h1 h2 (mul_nonneg hnr hnb) (by positivity)
    _ = ((Nat.gcd r (a * c) : ℝ) * (Nat.gcd r b : ℝ))
          * (moebiusTotient (Nat.lcm r (a * c)) * moebiusTotient (Nat.lcm r b)) := by ring
    _ ≤ ((Nat.gcd r (c * e) : ℝ) * (c : ℝ))
          * (moebiusTotient (Nat.lcm r (a * c)) * moebiusTotient (Nat.lcm r b)) :=
        mul_le_mul_of_nonneg_right hgle (mul_nonneg hnm hnn)

/-! ## Divisor factors, absorbed by the large prime factors of the modulus -/

/-- `k/(μ*φ)(k) ≤ 3^{ω(N)}` for every odd squarefree divisor `k` of `N`. Base `3`, not the
reciprocal kernel's `2`: the local ratio is `p/(p-2)`. -/
theorem self_div_moebiusTotient_le_three_pow {N k : ℕ} (hN : N ≠ 0) (hk : k ∣ N)
    (hksf : Squarefree k) (hkodd : ¬ 2 ∣ k) :
    (k : ℝ) / moebiusTotient k ≤ 3 ^ #N.primeFactors := by
  have hφ : (1 : ℝ) ≤ moebiusTotient k := one_le_moebiusTotient_of_odd_squarefree hksf hkodd
  rw [div_le_iff₀ (by linarith)]
  exact (self_le_three_pow_card_primeFactors_mul_moebiusTotient hksf hkodd).trans
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) (Finset.card_le_card (Nat.primeFactors_mono hk hN)))
      (by linarith))

/-- **The divisor sum of `k/(μ*φ)(k)` over the odd squarefree divisors of `Q ∣ e^2` is at most
`12^{ω(e)}`**: at most `4^{ω(e)}` divisors, each with `k/(μ*φ)(k) ≤ 3^{ω(e)}`. The even and
non-squarefree divisors are excluded from the sum because they are exactly the `k` no fibre of
`Gap212.Sieve.sum_gcd_div_moebiusTotient_le` can hit — `(μ*φ)` vanishes on the even ones. -/
theorem sum_divisors_self_div_moebiusTotient_le {Q e : ℕ} (he : Squarefree e) (hQ : Q ∣ e * e)
    (hQ0 : Q ≠ 0) :
    ∑ k ∈ Q.divisors with (Squarefree k ∧ ¬ 2 ∣ k), (k : ℝ) / moebiusTotient k
      ≤ 12 ^ #e.primeFactors := by
  have he0 : e ≠ 0 := he.ne_zero
  have hee : e * e ≠ 0 := mul_ne_zero he0 he0
  have hpfee : (e * e).primeFactors = e.primeFactors := by
    rw [Nat.primeFactors_mul he0 he0, Finset.union_self]
  have hcard : #Q.divisors ≤ 4 ^ #e.primeFactors := by
    rw [Nat.card_divisors hQ0]
    calc Q.primeFactors.prod (Q.factorization · + 1)
        ≤ ∏ _p ∈ Q.primeFactors, 4 := Finset.prod_le_prod' fun p _ ↦ by
          have h1 := (Nat.factorization_le_iff_dvd hQ0 hee).mpr hQ p
          rw [Nat.factorization_mul he0 he0, Finsupp.add_apply] at h1
          have := he.natFactorization_le_one p
          omega
      _ = 4 ^ #Q.primeFactors := Finset.prod_const _
      _ ≤ 4 ^ #e.primeFactors := Nat.pow_le_pow_right (by norm_num)
          (Finset.card_le_card (hpfee ▸ Nat.primeFactors_mono hQ hee))
  have hterm : ∀ k ∈ {k ∈ Q.divisors | Squarefree k ∧ ¬ 2 ∣ k},
      (k : ℝ) / moebiusTotient k ≤ 3 ^ #e.primeFactors := fun k hk ↦ by
    obtain ⟨hkd, hksf, hkodd⟩ := Finset.mem_filter.mp hk
    simpa [hpfee] using self_div_moebiusTotient_le_three_pow hee
      ((Nat.dvd_of_mem_divisors hkd).trans hQ) hksf hkodd
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul, show (12 : ℝ) = 4 * 3 by norm_num, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast (Finset.card_filter_le _ _).trans hcard) (by positivity)

/-- **The three divisor factors of one class multiply to `108^{ω(e)}/e`**: `c/(μ*φ)(c) ≤ 3^{ω(e)}`,
`1/(μ*φ)(e) ≤ 3^{ω(e)}/e` and the divisor sum is at most `12^{ω(e)}`. -/
theorem self_div_mul_sum_divisors_self_div_moebiusTotient_le {e c : ℕ} (hesf : Squarefree e)
    (heodd : ¬ 2 ∣ e) (hce : c ∣ e) :
    (c : ℝ) / (moebiusTotient e * moebiusTotient c)
        * ∑ k ∈ (c * e).divisors with (Squarefree k ∧ ¬ 2 ∣ k), (k : ℝ) / moebiusTotient k
      ≤ (108 : ℝ) ^ #e.primeFactors / (e : ℝ) := by
  have he0 : e ≠ 0 := hesf.ne_zero
  have hcsf : Squarefree c := hesf.squarefree_of_dvd hce
  have heR : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero he0
  have hφe := one_le_moebiusTotient_of_odd_squarefree hesf heodd
  have hfac : (1 : ℝ) / moebiusTotient e ≤ 3 ^ #e.primeFactors / (e : ℝ) := by
    rw [div_le_div_iff₀ (by linarith) heR]
    linarith [self_le_three_pow_card_primeFactors_mul_moebiusTotient hesf heodd]
  calc _ = (c : ℝ) / moebiusTotient c * ((1 : ℝ) / moebiusTotient e)
        * ∑ k ∈ (c * e).divisors with (Squarefree k ∧ ¬ 2 ∣ k), (k : ℝ) / moebiusTotient k := by
        ring
    _ ≤ 3 ^ #e.primeFactors * (3 ^ #e.primeFactors / (e : ℝ)) * 12 ^ #e.primeFactors := by
        refine mul_le_mul (mul_le_mul (self_div_moebiusTotient_le_three_pow he0 hce hcsf
          fun h ↦ heodd (h.trans hce)) hfac (div_nonneg zero_le_one (by linarith))
          (by positivity)) (sum_divisors_self_div_moebiusTotient_le hesf
          (mul_dvd_mul hce dvd_rfl) (mul_ne_zero hcsf.ne_zero he0))
          (Finset.sum_nonneg fun k hk ↦ ?_) (by positivity)
        obtain ⟨-, hksf, hkodd⟩ := Finset.mem_filter.mp hk
        exact div_nonneg (Nat.cast_nonneg _)
          (by linarith [one_le_moebiusTotient_of_odd_squarefree hksf hkodd])
    _ = _ := by rw [show (108 : ℝ) = 3 * 3 * 12 by norm_num, mul_pow, mul_pow]; ring

/-- **`432^{ω(e)} ≤ e^{1/4}`** for a squarefree `e` whose prime factors all exceed `432^4`. -/
theorem pow_card_primeFactors_le_rpow_quarter {e : ℕ} (hesf : Squarefree e)
    (hD : ∀ p ∈ e.primeFactors, 432 ^ 4 ≤ p) :
    (432 : ℝ) ^ #e.primeFactors ≤ (e : ℝ) ^ (1 / 4 : ℝ) := by
  have hR : ((432 : ℝ) ^ #e.primeFactors) ^ (4 : ℕ) ≤ (e : ℝ) := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact_mod_cast pow_card_primeFactors_le_self hesf hD
  refine (pow_le_pow_iff_left₀ (n := 4) (by positivity) (by positivity) (by norm_num)).mp ?_
  rwa [← Real.rpow_natCast ((e : ℝ) ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul (Nat.cast_nonneg _),
    show (1 / 4 : ℝ) * (4 : ℕ) = 1 by norm_num, Real.rpow_one]

/-- Every divisor of a squarefree `e` has at most `2^{ω(e)}` divisors. -/
theorem card_divisors_le_two_pow_of_dvd {e n : ℕ} (hesf : Squarefree e) (hn : n ∣ e) :
    #n.divisors ≤ 2 ^ #e.primeFactors := by
  simpa [card_divisors_of_squarefree hesf] using
    Finset.card_le_card (Nat.divisors_subset_of_dvd hesf.ne_zero hn)

/-! ## The modulus sum with a gcd weight -/

/-- **The gcd-weighted Mertens sum for this kernel.** For `W` even and `Q ≠ 0`,

  `∑_{r ≤ N, (r,W)=1, r sf} (r,Q)/(μ*φ)(r)
     ≤ (∑_{k ∣ Q, k odd sf} k/(μ*φ)(k))·∑_{r ≤ N, (r,W)=1, r sf} 1/(μ*φ)(r)`,

by fibering over `k = (r,Q)`. The fibre is contained in `{kr' : r' ∈ T, (k,r')=1}`, and on a
squarefree `r = kr'` the factorisation is exact —
`(μ*φ)(kr') = (μ*φ)(k)(μ*φ)(r')` (`Gap212.Sieve.moebiusTotient_mul_of_coprime`) — where the
reciprocal kernel had to appeal to super-multiplicativity of `φ`. **Evenness of `W` is what makes
every `r` odd**, hence `(μ*φ)(r) ≥ 1`, hence every denominator positive; the divisor index is
restricted to the odd squarefree `k` for the same reason, and that is exactly the set the fibre map
can hit. -/
theorem sum_gcd_div_moebiusTotient_le {W : ℕ} (hW2 : 2 ∣ W) (N Q : ℕ) (hQ : Q ≠ 0) :
    ∑ r ∈ Icc 1 N with (Nat.Coprime W r ∧ Squarefree r), (Nat.gcd r Q : ℝ) / moebiusTotient r
      ≤ (∑ k ∈ Q.divisors with (Squarefree k ∧ ¬ 2 ∣ k), (k : ℝ) / moebiusTotient k)
        * ∑ r ∈ Icc 1 N with (Nat.Coprime W r ∧ Squarefree r), (1 : ℝ) / moebiusTotient r := by
  set T : Finset ℕ := {r ∈ Icc 1 N | Nat.Coprime W r ∧ Squarefree r}
  have hTfacts : ∀ r ∈ T, (1 ≤ r ∧ r ≤ N) ∧ Nat.Coprime W r ∧ Squarefree r ∧ ¬ 2 ∣ r := by
    intro r hr
    obtain ⟨hmem, hcop, hsf⟩ := Finset.mem_filter.mp hr
    exact ⟨Finset.mem_Icc.mp hmem, hcop, hsf, not_two_dvd_of_coprime hW2 hcop⟩
  have hTpos : ∀ r ∈ T, (1 : ℝ) ≤ moebiusTotient r := fun r hr ↦
    one_le_moebiusTotient_of_odd_squarefree (hTfacts r hr).2.2.1 (hTfacts r hr).2.2.2
  have hmaps : ∀ r ∈ T, Nat.gcd r Q ∈ {k ∈ Q.divisors | Squarefree k ∧ ¬ 2 ∣ k} := by
    intro r hr
    obtain ⟨-, -, hsf, hodd⟩ := hTfacts r hr
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right r Q, hQ⟩,
      hsf.squarefree_of_dvd (Nat.gcd_dvd_left r Q), fun h2 ↦ hodd (h2.trans (Nat.gcd_dvd_left r Q))⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk ↦ ?_
  obtain ⟨-, hksf, hkodd⟩ := Finset.mem_filter.mp hk
  have hk0 : 0 < k := Nat.pos_of_ne_zero hksf.ne_zero
  have hφk : (1 : ℝ) ≤ moebiusTotient k := one_le_moebiusTotient_of_odd_squarefree hksf hkodd
  set T' : Finset ℕ := {r' ∈ T | Nat.Coprime k r'}
  have hsub : {r ∈ T | Nat.gcd r Q = k} ⊆ T'.image (k * ·) := by
    intro r hr
    obtain ⟨hrT, hgcd⟩ := Finset.mem_filter.mp hr
    obtain ⟨⟨h1, h2⟩, hcop, hsf, -⟩ := hTfacts r hrT
    obtain ⟨r', rfl⟩ := hgcd ▸ Nat.gcd_dvd_left r Q
    have hr'0 : 0 < r' := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
    exact Finset.mem_image.mpr ⟨r', Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hr'0, (Nat.le_mul_of_pos_left _ hk0).trans h2⟩,
        hcop.coprime_dvd_right (dvd_mul_left r' k), hsf.squarefree_of_dvd (dvd_mul_left r' k)⟩,
      (Nat.squarefree_mul_iff.mp hsf).1⟩, rfl⟩
  calc ∑ r ∈ T with Nat.gcd r Q = k, (Nat.gcd r Q : ℝ) / moebiusTotient r
      = k * ∑ r ∈ T with Nat.gcd r Q = k, (1 : ℝ) / moebiusTotient r := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r hr ↦ by rw [(Finset.mem_filter.mp hr).2]; ring
    _ ≤ k * ∑ r ∈ T'.image (k * ·), (1 : ℝ) / moebiusTotient r := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub
          fun r hr _ ↦ ?_) (Nat.cast_nonneg k)
        obtain ⟨r', hr', rfl⟩ := Finset.mem_image.mp hr
        obtain ⟨hr'T, hcopkr⟩ := Finset.mem_filter.mp hr'
        rw [moebiusTotient_mul_of_coprime hcopkr]
        have := hTpos r' hr'T
        positivity
    _ = k * ∑ r' ∈ T', (1 / moebiusTotient k) * ((1 : ℝ) / moebiusTotient r') := by
        rw [Finset.sum_image fun a _ b _ h ↦ Nat.eq_of_mul_eq_mul_left hk0 h]
        refine congrArg _ (Finset.sum_congr rfl fun r' hr' ↦ ?_)
        rw [moebiusTotient_mul_of_coprime (Finset.mem_filter.mp hr').2, one_div_mul_one_div]
    _ ≤ k * ∑ r' ∈ T, (1 / moebiusTotient k) * ((1 : ℝ) / moebiusTotient r') := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) fun r' hr' _ ↦ ?_) (Nat.cast_nonneg k)
        have := hTpos r' hr'
        positivity
    _ = (k : ℝ) / moebiusTotient k * ∑ r ∈ T, (1 : ℝ) / moebiusTotient r := by
        rw [← Finset.mul_sum]; ring

/-! ## The Mertens sum over the moduli the support clause leaves -/

/-- **The modulus sum of the diagonalisation, bounded once and for all.** For every large `x` and
every `β > 0`,

  `∑_{r ≤ x^β, (r,W)=1} μ^2(r)/(μ*φ)(r) ≤ (2β + C)·(φ(W)/W)\log x`

with an absolute `C`. This is `Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime` with its
error discharged — and it is a *different* Mertens sum from the reciprocal kernel's
`Gap212.Sieve.sum_moebiusSq_div_totient_coprime`: this kernel's local factor at `p ∤ W` is
`(1 - 1/(p-1)^2)^{-1}`, not `1`, so the asymptotic carries the extra product
`(∏_{p ∤ W}(1-1/(p-1)^2))^{-1}`, which is why the factor `2` appears in front of `β`. That product
tends to `1` along the primorials (`Gap212.Sieve.tendsto_inv_tprod_corr_W`), so bounding it by `2`
eventually costs nothing; the remaining error `τ(W) + ℓ_W` is at most `2W ≤ 2(φ(W)/W)\log x`
because `W(x)^2 ≤ \log x`. Evenness of `W(x)`, which the Mertens statement requires, comes from
`Gap212.Sieve.eventually_dvd_W_of_prime_le` at `2`. -/
theorem eventually_sum_moebiusSq_div_moebiusTotient_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ β : ℝ, 0 < β →
      ∑ r ∈ Icc 1 ⌊x ^ β⌋₊ with Nat.Coprime (W x) r, ((μ r : ℝ) ^ 2 / moebiusTotient r)
        ≤ (2 * β + C) * ((((W x).totient : ℝ) / (W x : ℝ)) * Real.log x) := by
  obtain ⟨C₀, hC₀, hmert⟩ := sum_moebiusSq_div_moebiusTotient_coprime
  refine ⟨4 * C₀, by positivity, ?_⟩
  filter_upwards [eventually_W_facts, eventually_gt_atTop (1 : ℝ), eventually_dvd_W_of_prime_le 2,
    tendsto_inv_tprod_corr_W.eventually_lt_const (show (1 : ℝ) < 2 by norm_num)] with
    x ⟨hL1, hφ1, hφW, hWsq, hτW, hℓW⟩ hx1 hxW2 hP β hβ
  have hW0 : (0 : ℝ) < (W x : ℝ) := by linarith
  have hN₀1 : 1 ≤ ⌊x ^ β⌋₊ := Nat.le_floor (by exact_mod_cast Real.one_le_rpow hx1.le hβ.le)
  have hN₀R : (1 : ℝ) ≤ ((⌊x ^ β⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN₀1
  have habs := (abs_le.mp
    (hmert (W x) (hxW2 2 Nat.prime_two le_rfl) (squarefree_primorial _) ⌊x ^ β⌋₊ hN₀1)).2
  have hlogN₀ : Real.log ⌊x ^ β⌋₊ ≤ β * Real.log x := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log (by linarith) (Nat.floor_le (by positivity))
  have hlogN₀0 : 0 ≤ Real.log ⌊x ^ β⌋₊ := Real.log_nonneg hN₀R
  have hratio : (0 : ℝ) < ((W x).totient : ℝ) / (W x : ℝ) := by positivity
  have huL : (W x : ℝ) ≤ (((W x).totient : ℝ) / (W x : ℝ)) * Real.log x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hW0]
    nlinarith
  have hmain : ((W x).totient : ℝ) / (W x : ℝ)
      * (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ W x then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)⁻¹
      * Real.log ⌊x ^ β⌋₊
      ≤ (((W x).totient : ℝ) / (W x : ℝ)) * Real.log x * (2 * β) := by
    have hstep : ((W x).totient : ℝ) / (W x : ℝ)
        * (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ W x then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)⁻¹
        * Real.log ⌊x ^ β⌋₊
        ≤ ((W x).totient : ℝ) / (W x : ℝ) * 2 * Real.log ⌊x ^ β⌋₊ := by gcongr
    nlinarith [hstep, hlogN₀, hratio]
  have herr : C₀ * ((#(W x).divisors : ℝ) + PrimeGaps.ellV (W x))
      ≤ (((W x).totient : ℝ) / (W x : ℝ)) * Real.log x * (4 * C₀) := by
    nlinarith [huL, hC₀.le]
  nlinarith [habs, hmain, herr]

/-! ## The moduli that see no pair at all -/

/-- **A non-squarefree modulus contributes nothing.** `e ∣ [d,d']` forces `[d,d']` non-squarefree,
hence one of `d`, `d'` non-squarefree, and `μ` kills the term. -/
theorem restrictedSum_pairWeightTotient_eq_zero_of_not_squarefree (x : ℝ) (F G : ℝ → ℝ) (B : ℕ)
    {e : ℕ} (he : ¬ Squarefree e) :
    restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeightTotient x F G) e = 0 := by
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  have hdvd := (Finset.mem_filter.mp hp).2
  by_cases hd : Squarefree p.1
  · by_cases hd' : Squarefree p.2
    · exact absurd ((squarefree_lcm hd hd').squarefree_of_dvd hdvd) he
    · simp [pairWeightTotient, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd']
  · simp [pairWeightTotient, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]

/-- **A modulus sharing a factor with `W(x)` contributes nothing**: the whole box is coprime to
`W(x)`, hence so is `[d,d']`, hence so is every divisor of it. -/
theorem restrictedSum_pairWeightTotient_eq_zero_of_not_coprime (x : ℝ) (F G : ℝ → ℝ) (B : ℕ)
    {e : ℕ} (he : ¬ Nat.Coprime (W x) e) :
    restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeightTotient x F G) e = 0 := by
  refine Finset.sum_eq_zero fun p hp ↦ absurd ?_ he
  obtain ⟨hmem, hdvd⟩ := Finset.mem_filter.mp hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
  exact (((mem_wBox.mp h1).2.mul_right (mem_wBox.mp h2).2).coprime_dvd_right
    (Nat.lcm_dvd_mul p.1 p.2)).coprime_dvd_right hdvd

/-! ## The modulus, split between the two coordinates -/

/-- **The inner sum over one class of the partition, expanded by Möbius.** For squarefree `e` and
`a ∣ e`,

  `∑_{d ∈ [1,B], (d,W)=1, r ∣ d, (e,d)=a} μ(d)F(\log_xd)/φ(d) = ∑_{c ∣ e/a} μ(c)·z_{[[r,a],c]}`.

The reciprocal kernel's `Gap212.Sieve.sum_filter_gcd_eq_sum_divisors_moebius_mul` with `1/φ(d)` for
`1/d`; the combinatorics — the coprimality `(d, e/a) = 1` detected by `∑_{c ∣ (e/a,d)}μ(c)` — is the
same, and `Gap212.Sieve.gcd_eq_iff_coprime_div` and
`Gap212.Sieve.filter_dvd_divisors_eq_divisors_gcd` are reused unchanged. -/
theorem sum_filter_gcd_eq_sum_divisors_moebius_mul_totient {x : ℝ} (F : ℝ → ℝ) (B : ℕ) {e a : ℕ}
    (hesf : Squarefree e) (hae : a ∣ e) (r : ℕ) :
    ∑ d ∈ wBox x B with (r ∣ d ∧ Nat.gcd e d = a),
        (μ d : ℝ) * F (Notation.logx x d) / (Nat.totient d : ℝ)
      = ∑ c ∈ (e / a).divisors,
          (μ c : ℝ) * innerMoebiusTotientSum x F B (Nat.lcm (Nat.lcm r a) c) := by
  have hb0 : e / a ≠ 0 := fun h ↦ hesf.ne_zero (by rw [← Nat.mul_div_cancel' hae, h, mul_zero])
  have hRHS : ∑ c ∈ (e / a).divisors,
        (μ c : ℝ) * innerMoebiusTotientSum x F B (Nat.lcm (Nat.lcm r a) c)
      = ∑ d ∈ wBox x B, ∑ c ∈ (e / a).divisors,
          (if Nat.lcm (Nat.lcm r a) c ∣ d then
            (μ c : ℝ) * ((μ d : ℝ) * F (Notation.logx x d) / (Nat.totient d : ℝ)) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [innerMoebiusTotientSum, Finset.mul_sum, Finset.sum_filter]
  rw [hRHS, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  set w : ℝ := (μ d : ℝ) * F (Notation.logx x d) / (Nat.totient d : ℝ)
  by_cases hra : r ∣ d ∧ a ∣ d
  · have hstep : ∑ c ∈ (e / a).divisors,
        (if Nat.lcm (Nat.lcm r a) c ∣ d then (μ c : ℝ) * w else 0)
        = (∑ c ∈ (e / a).divisors with c ∣ d, (μ c : ℝ)) * w := by
      rw [Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      simp only [Nat.lcm_dvd_iff, hra, true_and, ite_mul, zero_mul]
    rw [hstep, filter_dvd_divisors_eq_divisors_gcd hb0, sum_divisors_moebius_real]
    simp [gcd_eq_iff_coprime_div hesf hae hra.2, hra.1]
  · rw [if_neg fun ⟨hr, hg⟩ ↦ hra ⟨hr, hg ▸ Nat.gcd_dvd_right e d⟩]
    refine (Finset.sum_eq_zero fun c _ ↦ if_neg fun hdvd ↦ hra ?_).symm
    rw [Nat.lcm_dvd_iff, Nat.lcm_dvd_iff] at hdvd
    exact hdvd.1

/-- **The modulus-restricted totient pair sum, partitioned and diagonalised.** For squarefree `e`,

  `|T_e| ≤ ∑_{a ∣ e}∑_{c ∣ e/a}∑_{r ≤ B} (μ*φ)(r)·|z_F([[r,a],c])|·|z_G([r,e/a])|`.

The reciprocal kernel's `Gap212.Sieve.abs_restrictedSum_le_sum_divisors` with the weight `(μ*φ)(r)`
for `φ(r)` and `1/φ(d)` for `1/d`: the pairs with `e ∣ [d,d']` are partitioned by `a = (e,d)`
(`Gap212.Sieve.dvd_lcm_iff_div_gcd_dvd`, reused), each class is diagonalised by
`Gap212.Sieve.sum_pairs_div_totient_lcm_eq_sum_moebiusTotient_mul`, and the `d`-side factor is a
signed combination of `τ(e/a)` inner sums. **Only then are absolute values taken.**

One step is not the reciprocal kernel's. Pulling `(μ*φ)(r)` out of an absolute value needs it
nonnegative, which holds on the squarefree `r` (`Gap212.Sieve.moebiusTotient_nonneg_of_squarefree`)
and is not claimed elsewhere; at a non-squarefree `r` both sides are zero instead, every `d` in the
inner sum being a multiple of `r` and hence non-squarefree. -/
theorem abs_restrictedSum_totient_le_sum_divisors {x : ℝ} (F G : ℝ → ℝ) (B : ℕ) {e : ℕ}
    (hesf : Squarefree e) :
    |restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeightTotient x F G) e|
      ≤ ∑ a ∈ e.divisors, ∑ c ∈ (e / a).divisors, ∑ r ∈ Icc 1 B,
          moebiusTotient r * (|innerMoebiusTotientSum x F B (Nat.lcm (Nat.lcm r a) c)|
            * |innerMoebiusTotientSum x G B (Nat.lcm r (e / a))|) := by
  have hpart : restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeightTotient x F G) e
      = ∑ a ∈ e.divisors, ∑ d ∈ wBox x B with Nat.gcd e d = a,
          ∑ d' ∈ wBox x B with (e / a) ∣ d', pairWeightTotient x F G (d, d') := by
    rw [restrictedSum, ← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ ↦ Nat.gcd e p.1)
      (f := pairWeightTotient x F G)
      fun p _ ↦ Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left e p.1, hesf.ne_zero⟩]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hset : {p ∈ {p ∈ wBox x B ×ˢ wBox x B | e ∣ lcmPair p} | Nat.gcd e p.1 = a}
        = {d ∈ wBox x B | Nat.gcd e d = a} ×ˢ {d' ∈ wBox x B | (e / a) ∣ d'} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, hdvd⟩, rfl⟩
        exact ⟨⟨h1, rfl⟩, h2, (dvd_lcm_iff_div_gcd_dvd hesf).mp hdvd⟩
      · rintro ⟨⟨h1, rfl⟩, h2, hb⟩
        exact ⟨⟨⟨h1, h2⟩, (dvd_lcm_iff_div_gcd_dvd hesf).mpr hb⟩, rfl⟩
    rw [hset, Finset.sum_product]
  rw [hpart]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a ha ↦ ?_)
  obtain ⟨hae, -⟩ := Nat.mem_divisors.mp ha
  set L : ℕ → ℝ := fun d ↦ if Nat.gcd e d = a then (μ d : ℝ) * F (Notation.logx x d) else 0
    with hLdef
  set M : ℕ → ℝ := fun d ↦ if (e / a) ∣ d then (μ d : ℝ) * G (Notation.logx x d) else 0 with hMdef
  have hinner : ∑ d ∈ wBox x B with Nat.gcd e d = a,
        ∑ d' ∈ wBox x B with (e / a) ∣ d', pairWeightTotient x F G (d, d')
      = ∑ d ∈ wBox x B, ∑ d' ∈ wBox x B,
          L d * M d' / (Nat.totient (Nat.lcm d d') : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [Finset.sum_filter]
    by_cases hP : Nat.gcd e d = a
    · refine (if_pos hP).trans (Finset.sum_congr rfl fun d' _ ↦ ?_)
      by_cases hQ : e / a ∣ d' <;> simp [hLdef, hMdef, hP, hQ, pairWeightTotient, lcmPair]
    · simp [hLdef, hP]
  rw [hinner, sum_pairs_div_totient_lcm_eq_sum_moebiusTotient_mul B (wBox x B)
    (fun d hd ↦ (mem_wBox.mp hd).1)]
  have hA : ∀ r : ℕ, ∑ d ∈ wBox x B with r ∣ d, L d / (Nat.totient d : ℝ)
      = ∑ c ∈ (e / a).divisors,
          (μ c : ℝ) * innerMoebiusTotientSum x F B (Nat.lcm (Nat.lcm r a) c) := by
    intro r
    rw [← sum_filter_gcd_eq_sum_divisors_moebius_mul_totient F B hesf hae r, Finset.sum_filter,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    by_cases h1 : r ∣ d <;> by_cases h2 : Nat.gcd e d = a <;> simp [hLdef, h1, h2]
  have hBfac : ∀ r : ℕ, ∑ d' ∈ wBox x B with r ∣ d', M d' / (Nat.totient d' : ℝ)
      = innerMoebiusTotientSum x G B (Nat.lcm r (e / a)) := by
    intro r
    rw [innerMoebiusTotientSum_lcm, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    by_cases h1 : r ∣ d <;> by_cases h2 : e / a ∣ d <;> simp [hMdef, h1, h2]
  refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ ↦ ?_)).trans_eq
    Finset.sum_comm
  by_cases hrsf : Squarefree r
  · have hφr : (0 : ℝ) ≤ moebiusTotient r := moebiusTotient_nonneg_of_squarefree hrsf
    rw [hA r, hBfac r, abs_mul, abs_of_nonneg hφr, abs_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)) hφr
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ ↦ ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_real_le_one c)
  · have hzeroL : ∑ d ∈ wBox x B with r ∣ d, L d / (Nat.totient d : ℝ) = 0 :=
      Finset.sum_eq_zero fun d hd ↦ by
        simp [hLdef, ArithmeticFunction.moebius_eq_zero_of_not_squarefree
          fun h ↦ hrsf (h.squarefree_of_dvd (Finset.mem_filter.mp hd).2)]
    rw [hzeroL, zero_mul, mul_zero, abs_zero]
    refine Finset.sum_nonneg fun c _ ↦ ?_
    rw [innerMoebiusTotientSum_eq_zero_of_not_squarefree fun h ↦ hrsf (h.squarefree_of_dvd
      ((Nat.dvd_lcm_left r a).trans (Nat.dvd_lcm_left (Nat.lcm r a) c))), abs_zero, zero_mul,
      mul_zero]

/-! ## The totient estimate for supported profiles, from the one-variable input -/

/-- **`Gap212.Sieve.OneCoordTotientDecayAtLevelOfSupport (3/4)` holds, given
`Gap212.Sieve.SmoothMoebiusTotientInnerBound`.** Since `1/2 < 3/4`, this is exactly what
`Gap212.Sieve.tendsto_boxDivisorSum_sub_sievedDivisorSum_of_support` consumes, so on this one input
the totient sieving error closes.

The proof is Selberg's change of variables and then only inequalities. The moduli `e` that are not
squarefree or not coprime to `W(x)` have no pair to sum over
(`Gap212.Sieve.restrictedSum_pairWeightTotient_eq_zero_of_not_squarefree`,
`..._of_not_coprime`). For the rest,
`Gap212.Sieve.abs_restrictedSum_totient_le_sum_divisors` partitions the pairs by `a = (e,d)` and
diagonalises each class, leaving `∑_{a ∣ e}∑_{c ∣ e/a}∑_r(μ*φ)(r)|z_F([[r,a],c])||z_G([r,e/a])|`,
at which point the input bounds each factor and nothing further cancels.

Two mechanisms carry the estimate. The support clause makes
every `z` vanish above `x^β`, so the modulus sum runs over `r ≤ x^β` however large `B` is, and
`Gap212.Sieve.eventually_sum_moebiusSq_div_moebiusTotient_le` bounds it by
`(2β + C)(φ(W)/W)\log x`; against the `(W/φ(W))^2/\log^2x` of the two inner bounds that is exactly
`K/B_x`, with no slack. The exponent `3/4 < 1` pays for the divisor factors, and **the constants
are not the reciprocal kernel's**: the local ratios of this kernel are `p/(p-2)` and `p/(p-1)^2`, so
the three factors are `3^{ω(e)}`, `3^{ω(e)}/e` and `12^{ω(e)}`
(`Gap212.Sieve.self_div_moebiusTotient_le_three_pow`,
`Gap212.Sieve.sum_divisors_self_div_moebiusTotient_le`) where the reciprocal kernel's were `2`, `2`
and `8`, and with the two divisor counts the `e`-dependence is `432^{ω(e)}/e` against the reciprocal
kernel's `128^{ω(e)}/e`. That costs nothing because the threshold is free: `e` is coprime to `W(x)`,
which collects every prime up to `\log\log\log x`, so every prime factor of `e` exceeds `432^4`
eventually and `432^{ω(e)} ≤ e^{1/4}` (`Gap212.Sieve.pow_card_primeFactors_le_self`). At `s = 1`
that step is unavailable. -/
theorem oneCoordTotientDecayAtLevelOfSupport_of_smoothMoebiusTotientInnerBound
    (hin : SmoothMoebiusTotientInnerBound) : OneCoordTotientDecayAtLevelOfSupport (3 / 4) := by
  intro β hβ F G hF hFc hG hGc hFβ hGβ
  obtain ⟨CF, hCF, hevF⟩ := hin β hβ F hF hFc hFβ
  obtain ⟨CG, hCG, hevG⟩ := hin β hβ G hG hGc hGβ
  obtain ⟨C₀, hC₀, hmert⟩ := eventually_sum_moebiusSq_div_moebiusTotient_le
  refine ⟨CF * CG * (2 * β + C₀), by positivity, ?_⟩
  filter_upwards [hevF, hevG, eventually_W_facts, eventually_gt_atTop (1 : ℝ), hmert,
    eventually_dvd_W_of_prime_le (432 ^ 4)]
    with x hxF hxG ⟨hL1, hφ1, hφW, _⟩ hx1 hxM hxP B e hB he
  set L : ℝ := Real.log x
  set Wr : ℝ := (W x : ℝ)
  set φW : ℝ := ((W x).totient : ℝ)
  have hL0 : 0 < L := by linarith
  have hφ0 : 0 < φW := by linarith
  have hW0 : 0 < Wr := by linarith
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hrpow : (0 : ℝ) < (e : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos heR _
  have hnn : 0 ≤ CF * CG * (2 * β + C₀) / (φW / Wr * L * (e : ℝ) ^ (3 / 4 : ℝ)) := by positivity
  have hW2 : 2 ∣ W x := hxP 2 Nat.prime_two (by norm_num)
  obtain hesf | hesf := em' (Squarefree e)
  · rw [restrictedSum_pairWeightTotient_eq_zero_of_not_squarefree x F G B hesf, abs_zero]
    exact hnn
  obtain hecop | hecop := em' (Nat.Coprime (W x) e)
  · rw [restrictedSum_pairWeightTotient_eq_zero_of_not_coprime x F G B hecop, abs_zero]
    exact hnn
  -- the main case
  have heodd : ¬ 2 ∣ e := not_two_dvd_of_coprime hW2 hecop
  set w : ℕ := #e.primeFactors
  set N₀ : ℕ := ⌊x ^ β⌋₊
  set S' : Finset ℕ := {r ∈ Icc 1 N₀ | Nat.Coprime (W x) r ∧ Squarefree r} with hS'def
  have he0 : e ≠ 0 := hesf.ne_zero
  have hN₀B : N₀ ≤ B := Nat.floor_le_of_le hB
  set Ms : ℝ := ∑ r ∈ S', (1 : ℝ) / moebiusTotient r with hMsdef
  set K₁ : ℝ := CF * CG * (Wr / φW) ^ 2 / L ^ 2 with hK₁def
  have hS'facts : ∀ r ∈ S', (1 ≤ r ∧ r ≤ N₀) ∧ Squarefree r ∧ ¬ 2 ∣ r := by
    intro r hr
    obtain ⟨hmem, hcop, hsf⟩ := Finset.mem_filter.mp hr
    exact ⟨Finset.mem_Icc.mp hmem, hsf, not_two_dvd_of_coprime hW2 hcop⟩
  have hS'pos : ∀ r ∈ S', (1 : ℝ) ≤ moebiusTotient r := fun r hr ↦
    one_le_moebiusTotient_of_odd_squarefree (hS'facts r hr).2.1 (hS'facts r hr).2.2
  have hMs0 : (0 : ℝ) ≤ Ms :=
    Finset.sum_nonneg fun r hr ↦ div_nonneg zero_le_one (by linarith [hS'pos r hr])
  have hK₁0 : (0 : ℝ) ≤ K₁ := by positivity
  -- the Mertens bound, on the squarefree part of the range
  have hMs : Ms ≤ (2 * β + C₀) * (φW / Wr * L) := by
    refine le_trans ?_ (hxM β hβ)
    calc Ms = ∑ r ∈ S', ((μ r : ℝ) ^ 2 / moebiusTotient r) :=
          Finset.sum_congr rfl fun r hr ↦ by
            rw [show ((μ r : ℤ) : ℝ) ^ 2 = 1 by exact_mod_cast
              ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hS'facts r hr).2.1]
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun r hr ↦ Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2.1⟩) fun i hi _ ↦ ?_
          obtain ⟨-, hcop⟩ := Finset.mem_filter.mp hi
          by_cases hsf : Squarefree i
          · have := one_le_moebiusTotient_of_odd_squarefree hsf (not_two_dvd_of_coprime hW2 hcop)
            exact div_nonneg (sq_nonneg _) (by linarith)
          · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
  -- every prime factor of `e` is large, so every divisor factor is a small power of `e`
  have hDp : ∀ p ∈ e.primeFactors, 432 ^ 4 ≤ p := fun p hp ↦ by
    by_contra hcon
    have hpp := Nat.prime_of_mem_primeFactors hp
    exact hpp.ne_one (Nat.eq_one_of_dvd_coprimes hecop (hxP p hpp (by omega))
      (Nat.dvd_of_mem_primeFactors hp))
  have h432 : (432 : ℝ) ^ w ≤ (e : ℝ) ^ (1 / 4 : ℝ) :=
    pow_card_primeFactors_le_rpow_quarter hesf hDp
  have hφe1 : (1 : ℝ) ≤ moebiusTotient e := one_le_moebiusTotient_of_odd_squarefree hesf heodd
  -- the bound for one class of the partition
  have hrm : ∀ r a c : ℕ, r ∣ Nat.lcm (Nat.lcm r a) c :=
    fun r a c ↦ (Nat.dvd_lcm_left r a).trans (Nat.dvd_lcm_left _ c)
  have hsub : S' ⊆ Icc 1 B := fun r hr ↦ by
    obtain ⟨⟨h1, h2⟩, -, -⟩ := hS'facts r hr
    exact Finset.mem_Icc.mpr ⟨h1, h2.trans hN₀B⟩
  have hkey : ∀ a ∈ e.divisors, ∀ c ∈ (e / a).divisors,
      ∑ r ∈ Icc 1 B, moebiusTotient r
          * (|innerMoebiusTotientSum x F B (Nat.lcm (Nat.lcm r a) c)|
            * |innerMoebiusTotientSum x G B (Nat.lcm r (e / a))|)
        ≤ K₁ * ((108 : ℝ) ^ w / (e : ℝ)) * Ms := by
    intro a ha c hc
    obtain ⟨hae, -⟩ := Nat.mem_divisors.mp ha
    obtain ⟨hcb, hb0⟩ := Nat.mem_divisors.mp hc
    have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
    have hc0 : 0 < c := Nat.pos_of_mem_divisors hc
    have hce : c ∣ e := hcb.trans (Nat.div_dvd_of_dvd hae)
    have hbe : (e / a) ∣ e := Nat.div_dvd_of_dvd hae
    have hasf : Squarefree a := hesf.squarefree_of_dvd hae
    have hcsf : Squarefree c := hesf.squarefree_of_dvd hce
    have hbsf : Squarefree (e / a) := hesf.squarefree_of_dvd hbe
    have haodd : ¬ 2 ∣ a := fun h ↦ heodd (h.trans hae)
    have hcodd : ¬ 2 ∣ c := fun h ↦ heodd (h.trans hce)
    have hbodd : ¬ 2 ∣ (e / a) := fun h ↦ heodd (h.trans hbe)
    have hφc1 : (1 : ℝ) ≤ moebiusTotient c := one_le_moebiusTotient_of_odd_squarefree hcsf hcodd
    have hzero : ∀ r ∈ Icc 1 B, r ∉ S' →
        moebiusTotient r * (|innerMoebiusTotientSum x F B (Nat.lcm (Nat.lcm r a) c)|
          * |innerMoebiusTotientSum x G B (Nat.lcm r (e / a))|) = 0 := by
      intro r hr hrS
      have hr1 := (Finset.mem_Icc.mp hr).1
      suffices innerMoebiusTotientSum x F B (Nat.lcm (Nat.lcm r a) c) = 0 by
        rw [this, abs_zero, zero_mul, mul_zero]
      by_cases hcop : Nat.Coprime (W x) r
      · by_cases hsfr : Squarefree r
        · refine innerMoebiusTotientSum_eq_zero_of_rpow_lt hx1 hFβ ((Nat.lt_of_floor_lt
            (lt_of_not_ge fun h ↦ hrS (Finset.mem_filter.mpr
              ⟨Finset.mem_Icc.mpr ⟨hr1, h⟩, hcop, hsfr⟩))).trans_le ?_)
          exact_mod_cast Nat.le_of_dvd (Nat.lcm_pos (Nat.lcm_pos hr1 ha0) hc0) (hrm r a c)
        · exact innerMoebiusTotientSum_eq_zero_of_not_squarefree
            fun hsf ↦ hsfr (hsf.squarefree_of_dvd (hrm r a c))
      · exact innerMoebiusTotientSum_eq_zero_of_not_coprime
          fun hcp ↦ hcop (hcp.coprime_dvd_right (hrm r a c))
    rw [← Finset.sum_subset hsub hzero]
    have hterm : ∀ r ∈ S', moebiusTotient r
        * (|innerMoebiusTotientSum x F B (Nat.lcm (Nat.lcm r a) c)|
          * |innerMoebiusTotientSum x G B (Nat.lcm r (e / a))|)
        ≤ K₁ * ((Nat.gcd r (c * e) : ℝ) * (c : ℝ)
            / (moebiusTotient r * moebiusTotient e * moebiusTotient c)) := by
      intro r hr
      obtain ⟨⟨hr1, -⟩, hrsf, hrodd⟩ := hS'facts r hr
      have hm1 : 1 ≤ Nat.lcm (Nat.lcm r a) c := Nat.lcm_pos (Nat.lcm_pos hr1 ha0) hc0
      have hn1 : 1 ≤ Nat.lcm r (e / a) := Nat.lcm_pos hr1 (Nat.pos_of_ne_zero hb0)
      have hφm : (1 : ℝ) ≤ moebiusTotient (Nat.lcm (Nat.lcm r a) c) :=
        one_le_moebiusTotient_of_odd_squarefree (squarefree_lcm (squarefree_lcm hrsf hasf) hcsf)
          (not_two_dvd_lcm (not_two_dvd_lcm hrodd haodd) hcodd)
      have hφn : (1 : ℝ) ≤ moebiusTotient (Nat.lcm r (e / a)) :=
        one_le_moebiusTotient_of_odd_squarefree (squarefree_lcm hrsf hbsf)
          (not_two_dvd_lcm hrodd hbodd)
      have hφr : (1 : ℝ) ≤ moebiusTotient r := one_le_moebiusTotient_of_odd_squarefree hrsf hrodd
      have hlem := moebiusTotient_sq_mul_le_gcd_mul_lcm_mul hesf hae hcb hrsf
      calc moebiusTotient r
            * (|innerMoebiusTotientSum x F B (Nat.lcm (Nat.lcm r a) c)|
              * |innerMoebiusTotientSum x G B (Nat.lcm r (e / a))|)
          ≤ moebiusTotient r
              * ((CF * (Wr / φW) / (moebiusTotient (Nat.lcm (Nat.lcm r a) c) * L))
                * (CG * (Wr / φW) / (moebiusTotient (Nat.lcm r (e / a)) * L))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hxF B _ hB hm1) (hxG B _ hB hn1)
              (abs_nonneg _) (div_nonneg (mul_nonneg hCF (div_nonneg hW0.le hφ0.le))
                (mul_pos (by linarith) hL0).le)) (by linarith)
        _ = K₁ * (moebiusTotient r
              / (moebiusTotient (Nat.lcm (Nat.lcm r a) c)
                * moebiusTotient (Nat.lcm r (e / a)))) := by
            have h1 : moebiusTotient (Nat.lcm (Nat.lcm r a) c) ≠ 0 := by linarith
            have h2 : moebiusTotient (Nat.lcm r (e / a)) ≠ 0 := by linarith
            rw [hK₁def]
            field_simp
        _ ≤ K₁ * ((Nat.gcd r (c * e) : ℝ) * (c : ℝ)
              / (moebiusTotient r * moebiusTotient e * moebiusTotient c)) := by
            refine mul_le_mul_of_nonneg_left ?_ hK₁0
            rw [div_le_div_iff₀ (mul_pos (by linarith) (by linarith))
              (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))]
            nlinarith [hlem]
    have hgcdsum := sum_gcd_div_moebiusTotient_le hW2 N₀ (c * e) (Nat.mul_ne_zero hc0.ne' he0)
    rw [← hS'def, ← hMsdef] at hgcdsum
    have hcc := self_div_mul_sum_divisors_self_div_moebiusTotient_le hesf heodd hce
    calc ∑ r ∈ S', moebiusTotient r
          * (|innerMoebiusTotientSum x F B (Nat.lcm (Nat.lcm r a) c)|
            * |innerMoebiusTotientSum x G B (Nat.lcm r (e / a))|)
        ≤ ∑ r ∈ S', K₁ * ((Nat.gcd r (c * e) : ℝ) * (c : ℝ)
            / (moebiusTotient r * moebiusTotient e * moebiusTotient c)) :=
          Finset.sum_le_sum hterm
      _ = K₁ * ((c : ℝ) / (moebiusTotient e * moebiusTotient c))
            * ∑ r ∈ S', (Nat.gcd r (c * e) : ℝ) / moebiusTotient r := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun r _ ↦ by ring
      _ ≤ K₁ * ((c : ℝ) / (moebiusTotient e * moebiusTotient c))
            * ((∑ k ∈ (c * e).divisors with (Squarefree k ∧ ¬ 2 ∣ k),
                (k : ℝ) / moebiusTotient k) * Ms) :=
          mul_le_mul_of_nonneg_left hgcdsum (mul_nonneg hK₁0 (div_nonneg (Nat.cast_nonneg _)
            (mul_pos (by linarith) (by linarith)).le))
      _ = K₁ * ((c : ℝ) / (moebiusTotient e * moebiusTotient c)
            * ∑ k ∈ (c * e).divisors with (Squarefree k ∧ ¬ 2 ∣ k),
              (k : ℝ) / moebiusTotient k) * Ms := by ring
      _ ≤ K₁ * ((108 : ℝ) ^ w / (e : ℝ)) * Ms :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcc hK₁0) hMs0
  -- sum the classes
  have hdivcard : ∀ n : ℕ, n ∣ e → (#n.divisors : ℝ) ≤ (2 : ℝ) ^ w := fun n hn ↦ by
    exact_mod_cast card_divisors_le_two_pow_of_dvd hesf hn
  have h108 : 0 ≤ K₁ * ((108 : ℝ) ^ w / (e : ℝ)) := mul_nonneg hK₁0 (by positivity)
  refine (abs_restrictedSum_totient_le_sum_divisors F G B hesf).trans ?_
  calc ∑ a ∈ e.divisors, ∑ c ∈ (e / a).divisors, ∑ r ∈ Icc 1 B, moebiusTotient r
          * (|innerMoebiusTotientSum x F B (Nat.lcm (Nat.lcm r a) c)|
            * |innerMoebiusTotientSum x G B (Nat.lcm r (e / a))|)
      ≤ ∑ a ∈ e.divisors, ∑ _c ∈ (e / a).divisors, K₁ * ((108 : ℝ) ^ w / (e : ℝ)) * Ms :=
        Finset.sum_le_sum fun a ha ↦ Finset.sum_le_sum (hkey a ha)
    _ ≤ ∑ _a ∈ e.divisors, (2 : ℝ) ^ w * (K₁ * ((108 : ℝ) ^ w / (e : ℝ)) * Ms) :=
        Finset.sum_le_sum fun a ha ↦ by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right
            (hdivcard _ (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors ha))) (mul_nonneg h108 hMs0)
    _ ≤ (2 : ℝ) ^ w * ((2 : ℝ) ^ w * (K₁ * ((108 : ℝ) ^ w / (e : ℝ)) * Ms)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hdivcard e dvd_rfl)
          (mul_nonneg (by positivity) (mul_nonneg h108 hMs0))
    _ ≤ (2 : ℝ) ^ w * ((2 : ℝ) ^ w
          * (K₁ * ((108 : ℝ) ^ w / (e : ℝ)) * ((2 * β + C₀) * (φW / Wr * L)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hMs h108) (by positivity)) (by positivity)
    _ = CF * CG * (2 * β + C₀) * (Wr / φW) / L * ((432 : ℝ) ^ w / (e : ℝ)) := by
        rw [hK₁def, show (432 : ℝ) = 2 * 2 * 108 by norm_num, mul_pow, mul_pow]
        field_simp
    _ ≤ CF * CG * (2 * β + C₀) * (Wr / φW) / L * (1 / (e : ℝ) ^ (3 / 4 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_div_iff₀ heR hrpow, one_mul]
        calc (432 : ℝ) ^ w * (e : ℝ) ^ (3 / 4 : ℝ)
            ≤ (e : ℝ) ^ (1 / 4 : ℝ) * (e : ℝ) ^ (3 / 4 : ℝ) :=
              mul_le_mul_of_nonneg_right h432 hrpow.le
          _ = (e : ℝ) := by rw [← Real.rpow_add heR]; norm_num
    _ = CF * CG * (2 * β + C₀) / (φW / Wr * L * (e : ℝ) ^ (3 / 4 : ℝ)) := by field_simp

/-- **The totient sieving error, from the one-variable Möbius bound.** This is
`Gap212.Sieve.oneCoordTotientDecayAtLevelOfSupport_of_smoothMoebiusTotientInnerBound` fed to
`Gap212.Sieve.tendsto_boxDivisorSum_sub_sievedDivisorSum_of_support` at `s = 3/4`, admissible
because `1/2 < 3/4`: the conclusion is the content of `Gap212.Sieve.TotientSievingError m`, which
is stated at `β ≥ 1`. So
`Gap212.Sieve.SmoothMoebiusTotientInnerBound` — a bound on a *one-variable* Möbius sum, at the
weight `1/φ(d)` and with the denominator `(μ*φ)(r)` this kernel forces — is the only input for the
totient sieving error.

That input is a theorem (`Gap212.Sieve.smoothMoebiusTotientInnerBound`), so
`Gap212.Sieve.tendsto_boxDivisorSum_sub_sievedDivisorSum` is this conclusion with nothing assumed
and `Gap212.Sieve.totientSievingError` follows. -/
theorem tendsto_boxDivisorSum_sub_sievedDivisorSum_of_smoothInnerBound
    (hin : SmoothMoebiusTotientInnerBound) (p : SupportParams) {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) {m : ℕ}
    {j j' : Fin p.n} {i₀ : Fin (m + 1)} (F G : Fin m → ℝ → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    (hFc : ∀ i, HasCompactSupport (F i)) (hG : ∀ i, ContDiff ℝ 1 (G i))
    (hGc : ∀ i, HasCompactSupport (G i)) (hsupp : IsReducedRetreat p m j j' ε₀ i₀ F G)
    {β : ℝ} (hβ1 : 1 ≤ β) (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦
        (boxDivisorSum x (B x) F G - sievedDivisorSum x (B x) F G) / divisorSumNorm m x)
      atTop (nhds 0) :=
  tendsto_boxDivisorSum_sub_sievedDivisorSum_of_support (by norm_num)
    (oneCoordTotientDecayAtLevelOfSupport_of_smoothMoebiusTotientInnerBound hin) p hε₀ F G hF hFc
    hG hGc hsupp hβ1 B hB

end Gap212.Sieve
