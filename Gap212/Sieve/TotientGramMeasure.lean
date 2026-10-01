/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MertensMuPhi
public import Gap212.Sieve.TotientGramRiemannSum

/-!
# The totient Gram-sum limit, reduced to one analytic statement about its inner sums

`Gap212.Sieve.totientGramSumLimitOfSupport_iff` (`Gap212.Sieve.TotientGramRiemannSum`) proves
`Gap212.Sieve.TotientGramSumLimitOfSupport` *equivalent* to a Riemann sum against the weight
`μ²(e)/(μ*φ)(e)`,

  `(φ(W)/W)\log x·𝓖_x(F,G) = κ_x·∑_{e≤B,(e,W)=1}(μ²(e)/(μ*φ)(e))·ρ_F(e)ρ_G(e)`,
  `κ_x = (W/φ(W))/\log x`,  `ρ_F(e) = \log x·Y_F(e)·((μ*φ)(e)/φ(e))·(φ(W)/W)`,

and leaves two inputs: the Mertens asymptotic for that weight, and the evaluation of `ρ_F`. The
first is a theorem (`Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime`). This file spends it,
and restates the Gram-sum limit as the second.

## The measure

`Gap212.Sieve.tendsto_mertensKappa_mul_muPhiWeightedSum`: for `H` continuous and vanishing on
`[β,∞)` and any truncation `B(x) ≥ x^β`,

  `κ_x·∑_{e≤B(x),(e,W)=1}(μ²(e)/(μ*φ)(e))·H(\log_xe) ⟶ ∫_0^∞H`.

The normalized `μ²/(μ*φ)` weight *is* Lebesgue measure in the variable `\log_xe`, with **no**
correction factor surviving.

Two things had to be supplied that the reciprocal kernel needs neither of.

* **The correction factor.** At *fixed* `W` the limit is `(∏_{p∤W}(1-1/(p-1)²))^{-1}·∫_0^∞H` — the
  inverse twin-prime constant `1.5148` at `W = 2`. What removes it is that `W = W(x)` grows along
  the primorials (`Gap212.Sieve.tendsto_inv_tprod_corr_W`).
* **Uniformity of the error in `W`.** An asymptotic of the shape `∀ W, ∃ D, ∀ N` cannot be divided
  by `\log x` when `W = W(x)`, so `Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime` states
  one absolute constant and displays the `W`-dependence of the error as `τ(W) + ℓ_W`, and
  `Gap212.Sieve.tendsto_mertensKappa_mul_muPhiErr` then kills it against
  `Gap212.Sieve.W_le_log_log_sq`, a sharpening of `Gap212.Sieve.W_le_log_div_log_log` that the
  totient error's `τ(W)` makes necessary.

## The defect statement, and that it is equivalent to the Gram-sum limit

`Gap212.Sieve.TotientGramRatioDefectVanishes` is the statement that the *defect* between the true
summand and `F'(\log_xe)G'(\log_xe)` has vanishing normalized weighted sum, and
`Gap212.Sieve.totientGramSumLimitOfSupport_iff_totientGramRatioDefectVanishes` proves it
**equivalent** to `Gap212.Sieve.TotientGramSumLimitOfSupport`: it is the Gram-sum limit with the
arithmetic removed — no Mertens sum, no `φ(W)/W`, and no correction factor.
`Gap212.Sieve.TotientNormalizedInnerRatioL1` is the weighted-`ℓ¹` form, which forbids cancellation
between the `e`'s.

`Gap212.Sieve.TotientGramDefectMeanSquare` takes it one step further: the `B` quantifier is
inert (`Gap212.Sieve.totientGramRatioDefectVanishes_iff_atCut`), Cauchy–Schwarz decouples the two
profiles, and the Gram-sum limit follows from the **one-profile** mean square
`Gap212.Sieve.TotientNormalizedInnerL2` — with or without the correction factor, the two forms
being equivalent there. `Gap212.Sieve.TotientGramDefectTopBlock` then removes the one-term top
block from that mean square, which removes summands and not work
(`Gap212.Sieve.totientBulkInnerL2_iff`).

## Why it has to be an average, and that this kernel's difficulty is not the other's

`Gap212.Sieve.innerTotient_eq_of_lt_primorial_bound`, the analogue of
`Gap212.Sieve.innerRecip_eq_of_lt_primorial_bound`, collapses the inner sum to its single term
`F(\log_xe)` for every `e ∈ (B/(z+1),B]` with `z = ⌊\log\log\log x⌋`. So the top of the `e`-range
has no cancellation in this kernel either, `ρ_F(e)` is of size `\log(z+1)` there against a
prediction near `F'(β) = 0`, and no pointwise form of the defect statement is true. It is carried
by the support hypothesis and by that regime's normalized weight being `O(\log(z+1)/\log x)`.

The two kernels' defect statements are **not the same statement**, and the difference is visible in
the definitions rather than in the analysis. `Gap212.Sieve.innerRecip` weights the Möbius sum by
`1/f` and `Gap212.Sieve.innerTotient` by `1/φ(f)`; the normalizations differ (`φ(eW)/(eW)` against
`((μ*φ)(e)/φ(e))(φ(W)/W)`, which on a squarefree `e` coprime to `W` differ by the factor
`∏_{p∣e}(1-1/(p-1)²)`); and the averaging weights differ (`μ²/φ` against `μ²/(μ*φ)`, a ratio of
`∏_{p∣e}(p-1)/(p-2)`). The difficulty is shared in *kind* — Möbius cancellation uniform in the
growing modulus `eW(x)`, on average over `e` — and neither statement is available from the other.

## Main definitions

* `Gap212.Sieve.muPhiWeightCut`, `Gap212.Sieve.muPhiWeightAt`: the `μ²/(μ*φ)` weight below `x^s`,
  and the weight switched off outside the coprimality class.
* `Gap212.Sieve.TotientGramRatioDefectVanishes`: the defect statement, equivalent to the Gram-sum
  limit.
* `Gap212.Sieve.TotientNormalizedInnerRatioL1`: its weighted-`ℓ¹` strengthening.

## Main results

* `Gap212.Sieve.W_le_log_log_sq`, `Gap212.Sieve.tendsto_mertensKappa_mul_muPhiErr`: the error of
  `Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime`, normalized, vanishes.
* `Gap212.Sieve.tendsto_mertensKappa_mul_muPhiWeightCut`: the normalized weighted count below `x^s`
  converges to `s` — the measure, at one cutoff, with the correction factor spent.
* `Gap212.Sieve.tendsto_mertensKappa_mul_muPhiWeightedSum`: the Riemann sum against a continuous
  profile, and `Gap212.Sieve.tendsto_mertensKappa_mul_muPhiWeightedSum_gramCex` an instance with a
  positive limit.
* `Gap212.Sieve.innerTotient_eq_of_lt_primorial_bound`: the top of the `e`-range is the one-term
  regime in this kernel too.
* `Gap212.Sieve.totientGramSumLimitOfSupport_iff_totientGramRatioDefectVanishes`: the Gram-sum
  limit is equivalent to the defect statement.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY
open scoped ArithmeticFunction.Moebius

/-! ## The pre-sieving modulus is polylogarithmic, and the error it carries vanishes -/

/-- **`W(x) ≤ (\log\log x)²` for large `x`.** `Gap212.Sieve.W_le_log_div_log_log` is too weak here:
the totient error term carries `τ(W) ≤ W`, so the argument needs `W(x)² = o(\log x)` and not
merely `W(x) = O(\log x/\log\log x)`. The sharper bound is what
`primorial_le_four_pow` gives directly — `W(x) ≤ 4^{⌊\log u⌋} ≤ u^{\log 4}` with
`u = \log\log x`, and `\log 4 = 1.3863 ≤ 2`. Nothing is lost by rounding the exponent up to `2`:
the error is divided by `\log x`, against which every power of `\log\log x` is negligible. -/
theorem W_le_log_log_sq :
    ∀ᶠ x : ℝ in atTop, (W x : ℝ) ≤ Real.log (Real.log x) ^ 2 := by
  have hl4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with x (hu1 : 1 ≤ Real.log (Real.log x))
  set u := Real.log (Real.log x)
  calc (W x : ℝ) ≤ ((4 : ℕ) ^ (⌊Real.log u⌋₊ : ℕ) : ℕ) := by
        exact_mod_cast primorial_le_four_pow _
    _ = (4 : ℝ) ^ ((⌊Real.log u⌋₊ : ℕ) : ℝ) := by push_cast [Real.rpow_natCast]; ring
    _ ≤ (4 : ℝ) ^ Real.log u :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le (Real.log_nonneg hu1))
    _ = Real.exp (Real.log u * Real.log 4) := by
        rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
    _ ≤ Real.exp (Real.log u * 2) := Real.exp_le_exp.mpr (by nlinarith [Real.log_nonneg hu1])
    _ = u ^ 2 := by rw [← Real.rpow_two, Real.rpow_def_of_pos (by linarith)]

/-- **`(\log\log x)⁴ = o(\log x)`.** The one growth comparison the totient kernel's error needs,
`Gap212.Sieve.W_le_log_log_sq` squared. Read at `v = \log x`, it is `(\log v)⁴ = o(v)`, which is
`isLittleO_log_rpow_atTop` at the exponent `1/4` raised to the fourth power. -/
theorem tendsto_log_log_pow_four_div_log :
    Tendsto (fun x : ℝ ↦ Real.log (Real.log x) ^ 4 / Real.log x) atTop (nhds 0) := by
  have hbase : Tendsto (fun v : ℝ ↦ Real.log v / v ^ (1 / 4 : ℝ)) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (r := 1 / 4) (by norm_num)).tendsto_div_nhds_zero
  have hpow : Tendsto (fun v : ℝ ↦ (Real.log v / v ^ (1 / 4 : ℝ)) ^ 4) atTop (nhds 0) := by
    simpa using hbase.pow 4
  have hcongr : Tendsto (fun v : ℝ ↦ Real.log v ^ 4 / v) atTop (nhds 0) := by
    refine hpow.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
    rw [div_pow, ← Real.rpow_natCast (v ^ _) 4, ← Real.rpow_mul hv.le]
    norm_num
  simpa [Function.comp_def] using hcongr.comp Real.tendsto_log_atTop

/-- **The error of the uniform asymptotic, normalized, vanishes.** `κ_x·(τ(W(x)) + ℓ_{W(x)}) ⟶ 0`.

This is the step that a `∀ W, ∃ D, ∀ N` form cannot supply, and the reason
`Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime` names its error: `κ_x = (W/φ(W))/\log x`
and the error are both `W`-dependent, and the product is bounded by
`2W(x)²/\log x ≤ 2(\log\log x)⁴/\log x` only because the `W`-dependence of the error is named.
Every factor is crude — `W/φ(W) ≤ W`,
`τ(W) ≤ W`, `ℓ_W ≤ \log W ≤ W` — and the margin is enormous, `W(x)` being polylogarithmic in
`\log x`. -/
theorem tendsto_mertensKappa_mul_muPhiErr :
    Tendsto (fun x : ℝ ↦ mertensKappa x *
        ((#(W x).divisors : ℝ) + PrimeGaps.ellV (W x))) atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_
    (by simpa using tendsto_log_log_pow_four_div_log.const_mul (2 : ℝ))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (mertensKappa_nonneg hx)
      (add_nonneg (Nat.cast_nonneg _) (PrimeGaps.ellV_nonneg _))
  · filter_upwards [W_le_log_log_sq, eventually_gt_atTop (1 : ℝ)] with x hW hx1
    have hL : 0 < Real.log x := Real.log_pos hx1
    have hW1 : 1 ≤ W x := primorial_pos _
    have hWR : (1 : ℝ) ≤ (W x : ℝ) := by exact_mod_cast hW1
    have hτ : ((#(W x).divisors : ℕ) : ℝ) ≤ (W x : ℝ) := by
      exact_mod_cast Nat.card_divisors_le_self (W x)
    have hell : PrimeGaps.ellV (W x) ≤ (W x : ℝ) := (ellV_le_log hW1).trans
      (by linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (W x : ℝ))])
    have hkap : mertensKappa x ≤ (W x : ℝ) / Real.log x :=
      div_le_div_of_nonneg_right
        (div_le_self (by positivity) (by exact_mod_cast Nat.totient_pos.mpr hW1)) hL.le
    have hsq : (W x : ℝ) ^ 2 ≤ Real.log (Real.log x) ^ 4 := by
      simpa [← pow_mul] using pow_le_pow_left₀ (by positivity) hW 2
    calc mertensKappa x * ((#(W x).divisors : ℝ) + PrimeGaps.ellV (W x))
        ≤ ((W x : ℝ) / Real.log x) * (2 * (W x : ℝ)) :=
          mul_le_mul hkap (by linarith)
            (add_nonneg (Nat.cast_nonneg _) (PrimeGaps.ellV_nonneg _)) (by positivity)
      _ = 2 * ((W x : ℝ) ^ 2 / Real.log x) := by ring
      _ ≤ 2 * (Real.log (Real.log x) ^ 4 / Real.log x) := by gcongr

/-! ## The weighted counting function at a power cutoff -/

/-- **The weight `μ²(e)/(μ*φ)(e)` is nonnegative.** On a squarefree `e` it is `∏_{p ∣ e}(p-2)^{-1}`
with every factor nonnegative (and the value `0` at an even `e`, where the factor at `p = 2`
vanishes and Lean's division by zero returns `0`); off the squarefree numbers `μ(e) = 0`. -/
theorem muPhiWeight_term_nonneg (e : ℕ) : 0 ≤ (μ e : ℝ) ^ 2 / moebiusTotient e := by
  by_cases hsf : Squarefree e
  · refine div_nonneg (sq_nonneg _) ?_
    rw [moebiusTotient_of_squarefree hsf]
    refine Finset.prod_nonneg fun p hp ↦ ?_
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
    simp

/-- **The `μ²/(μ*φ)` weight summed over the coprimality class below `x^s`**, the counting function
whose normalized increments are the Riemann-sum measure of
`Gap212.Sieve.TotientMuPhiWeightedGramLimit`. -/
noncomputable def muPhiWeightCut (x s : ℝ) : ℝ :=
  ∑ e ∈ Icc 1 ⌊x ^ s⌋₊ with Nat.Coprime (W x) e, ((μ e : ℝ) ^ 2 / moebiusTotient e)

/-- At `s = 0` the cutoff is `1` and the only term is `e = 1`, where the weight is `1`. -/
theorem muPhiWeightCut_zero {x : ℝ} : muPhiWeightCut x 0 = 1 := by
  simp [muPhiWeightCut, Finset.filter_singleton, moebiusTotient_one]

/-- The weighted count `muPhiWeightCut x s` is non-negative. -/
theorem muPhiWeightCut_nonneg (x s : ℝ) : 0 ≤ muPhiWeightCut x s :=
  Finset.sum_nonneg fun e _ ↦ muPhiWeight_term_nonneg e

/-- **The pre-sieving modulus is eventually even.** The one-liner the Mertens asymptotic's evenness
hypothesis needs: `W(x)` is the primorial of `⌊\log\log\log x⌋`, which absorbs `p = 2` as soon as
that bound reaches `2` (`Gap212.Sieve.eventually_dvd_W_of_prime_le`). It is *not* true for all `x`,
and it does not have to be — every consumer is a limit at `atTop`. -/
theorem eventually_two_dvd_W : ∀ᶠ x : ℝ in atTop, 2 ∣ W x := by
  filter_upwards [eventually_dvd_W_of_prime_le 2] with x hx
  exact hx 2 Nat.prime_two le_rfl

/-- **`\log⌊x^s⌋/\log x ⟶ s`.** The floor costs at most `\log 2`, which the division by `\log x`
kills. -/
theorem tendsto_log_floor_rpow_div_log {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ ↦ Real.log ((⌊x ^ s⌋₊ : ℕ) : ℝ) / Real.log x) atTop (nhds s) := by
  have hlog2 : Tendsto (fun x : ℝ ↦ s - Real.log 2 / Real.log x) atTop (nhds s) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlog2 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_floor_rpow hs, eventually_gt_atTop (1 : ℝ)] with x hfl hx1
    obtain ⟨h2le, hlo, hhi, -⟩ := hfl
    have hL : 0 < Real.log x := Real.log_pos hx1
    have hxpos : (0 : ℝ) < x := by linarith
    have h1 : Real.log (x ^ s / 2) ≤ Real.log ((⌊x ^ s⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hlo
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hxpos] at h1
    rw [le_div_iff₀ hL, sub_mul, div_mul_cancel₀ _ (ne_of_gt hL)]
    linarith
  · filter_upwards [eventually_floor_rpow hs, eventually_gt_atTop (1 : ℝ)] with x hfl hx1
    obtain ⟨h2le, hlo, hhi, -⟩ := hfl
    have hL : 0 < Real.log x := Real.log_pos hx1
    have hxpos : (0 : ℝ) < x := by linarith
    rw [div_le_iff₀ hL, ← Real.log_rpow hxpos]
    exact Real.log_le_log (by linarith) hhi

/-- **The normalized weighted count below `x^s` converges to `s`.** The Mertens asymptotic
`Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime` read at `W = W(x)` and `N = ⌊x^s⌋`,
divided by its own prefactor:

  `κ_x·A_W(⌊x^s⌋) = (∏_{p∤W(x)}(1-1/(p-1)²))^{-1}·\log⌊x^s⌋/\log x + κ_x·E`,

because `κ_x·(φ(W)/W) = 1/\log x` exactly. Three things then have to vanish and all three do: the
floor costs `\log 2/\log x` (`Gap212.Sieve.tendsto_log_floor_rpow_div_log`), the error is
`κ_x·O(τ(W(x)) + ℓ_{W(x)}) → 0` (`Gap212.Sieve.tendsto_mertensKappa_mul_muPhiErr`), and — the one
step with no counterpart on the reciprocal side — the **correction factor's inverse tends to `1`**
(`Gap212.Sieve.tendsto_inv_tprod_corr_W`). At a *fixed* `W` the limit would be
`(∏_{p∤W}(1-1/(p-1)²))^{-1}·s`, which is `1.5148·s` at `W = 2`; it is the growth of `W(x)` along
the primorials that removes the factor. -/
theorem tendsto_mertensKappa_mul_muPhiWeightCut {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ ↦ mertensKappa x * muPhiWeightCut x s) atTop (nhds s) := by
  obtain ⟨C, hC, hasym⟩ := sum_moebiusSq_div_moebiusTotient_coprime
  have hmain : Tendsto (fun x : ℝ ↦
      (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ W x then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)⁻¹ *
        (Real.log ((⌊x ^ s⌋₊ : ℕ) : ℝ) / Real.log x)) atTop (nhds s) := by
    simpa using tendsto_inv_tprod_corr_W.mul (tendsto_log_floor_rpow_div_log hs)
  have hdiff : Tendsto (fun x : ℝ ↦ mertensKappa x * muPhiWeightCut x s
      - (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ W x then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)⁻¹ *
        (Real.log ((⌊x ^ s⌋₊ : ℕ) : ℝ) / Real.log x)) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_
      (by simpa using tendsto_mertensKappa_mul_muPhiErr.const_mul C)
    filter_upwards [eventually_two_dvd_W, eventually_floor_rpow hs,
      eventually_gt_atTop (1 : ℝ)] with x h2 hfl hx1
    obtain ⟨-, -, -, hN1⟩ := hfl
    have hL : 0 < Real.log x := Real.log_pos hx1
    have hW1 : 1 ≤ W x := primorial_pos _
    have hWR : (0 : ℝ) < (W x : ℝ) := by exact_mod_cast hW1
    have hphi : (0 : ℝ) < ((W x).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hW1
    have hkmul : mertensKappa x * (((W x).totient : ℝ) / (W x : ℝ)) = 1 / Real.log x := by
      rw [mertensKappa]; field_simp
    set c := (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ W x then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)⁻¹
    set L := Real.log ((⌊x ^ s⌋₊ : ℕ) : ℝ)
    have hk := mertensKappa_nonneg hx1.le
    have hrw : mertensKappa x * muPhiWeightCut x s - c * (L / Real.log x)
        = mertensKappa x * (muPhiWeightCut x s - ((W x).totient : ℝ) / (W x : ℝ) * c * L) := by
      linear_combination (c * L) * hkmul
    rw [Real.norm_eq_abs, hrw, abs_mul, abs_of_nonneg hk]
    exact (mul_le_mul_of_nonneg_left (hasym (W x) h2 (squarefree_primorial _) _ hN1) hk).trans_eq
      (by ring)
  simpa using hdiff.add hmain

/-- The normalized weighted count converges to `s` for every `s ≥ 0`: at `s = 0` the count is the
single term `e = 1` and the normalization itself tends to `0`. -/
theorem tendsto_mertensKappa_mul_muPhiWeightCut_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun x : ℝ ↦ mertensKappa x * muPhiWeightCut x s) atTop (nhds s) := by
  rcases hs.eq_or_lt with rfl | h
  · simpa [muPhiWeightCut_zero] using tendsto_mertensKappa
  · exact tendsto_mertensKappa_mul_muPhiWeightCut h

/-! ## The Riemann sum against a continuous profile -/

/-- **The `μ²/(μ*φ)` weight switched off outside the coprimality class.** Writing the filtered sums
of the Gram-sum limit as plain sums over an interval is what lets the `e`-range be chopped at the
partition points by `Gap212.Sieve.sum_Ioc_chain`. -/
noncomputable def muPhiWeightAt (x : ℝ) (e : ℕ) : ℝ :=
  if Nat.Coprime (W x) e then (μ e : ℝ) ^ 2 / moebiusTotient e else 0

/-- The switched-off weight `muPhiWeightAt x e` is non-negative. -/
theorem muPhiWeightAt_nonneg (x : ℝ) (e : ℕ) : 0 ≤ muPhiWeightAt x e :=
  ite_nonneg (muPhiWeight_term_nonneg e) le_rfl

/-- The weighted count below `x^t` is the plain sum of `muPhiWeightAt x e` over
`1 ≤ e ≤ ⌊x^t⌋`. -/
theorem muPhiWeightCut_eq_sum (x t : ℝ) :
    muPhiWeightCut x t = ∑ e ∈ Finset.Icc 1 ⌊x ^ t⌋₊, muPhiWeightAt x e := by
  rw [muPhiWeightCut, Finset.sum_filter]
  rfl

/-- **The measure half of the totient Gram-sum limit.** For `H` continuous and vanishing on
`[β,∞)` and any truncation `B(x) ≥ x^β`,

  `(W/φ(W))/\log x · ∑_{e ≤ B(x), (W,e)=1}(μ²(e)/(μ*φ)(e))·H(\log_xe) ⟶ ∫_0^∞H`.

This is the statement that the `μ²/(μ*φ)` weight, normalized as
`Gap212.Sieve.TotientMuPhiWeightedGramLimit` normalizes it, *is* Lebesgue measure in the variable
`\log_xe` — the counting-measure input that
`Gap212.Sieve.totientGramSumLimitOfSupport_iff` leaves. It is a theorem, not a hypothesis: the
arithmetic it uses is the proved Mertens asymptotic for this weight
(`Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime`, whose error is uniform in the modulus)
read at the partition points `⌊x^{jβ/n}⌋`, together with `Gap212.Sieve.tendsto_inv_tprod_corr_W`
for the correction factor its constant carries.

Only continuity of `H` is assumed, as needed: the profile is `F'G'` with `F`
and `G` merely `C¹`, so no integration by parts is available. The proof is a Riemann sum against
the counting function — the `e`-range `[1,x^β]` cut at `⌊x^{jβ/n}⌋`, the asymptotic evaluating each
block's normalized mass as `β/n + o(1)`, and `H` uniformly continuous on the compact `[0,β]` hence
constant to within `ε` on each block.

The support hypothesis is what makes the statement independent of `B`: above `⌊x^β⌋` every term
vanishes, so the `e`-range is really `[1,x^β]` and its normalized mass converges to `β` rather than
to the unbounded `\log B(x)/\log x`. Like `Gap212.Sieve.TotientGramSumLimitOfSupport`, this
statement bounds `B` only from below: a truncation far above `x^β` is handled, not excluded.
`Gap212.Sieve.tendsto_mertensKappa_mul_muPhiWeightedSum_gramCex` exhibits an instance whose limit
is positive. -/
theorem tendsto_mertensKappa_mul_muPhiWeightedSum {H : ℝ → ℝ} (hH : Continuous H) {β : ℝ}
    (hβ : 0 < β) (hHv : ∀ t, β ≤ t → H t = 0) (B : ℝ → ℕ)
    (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦ mertensKappa x *
        ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / moebiusTotient e) * H (Notation.logx x e))
      atTop (nhds (∫ t in Set.Ioi (0 : ℝ), H t)) := by
  classical
  have hIeq : (∫ t in Set.Ioi (0 : ℝ), H t) = ∫ t in (0 : ℝ)..β, H t := by
    rw [intervalIntegral.integral_of_le hβ.le]
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self ?_
    intro t ht
    simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_Ioc, not_and, not_le] at ht
    exact hHv t (ht.2 ht.1).le
  rw [hIeq, Metric.tendsto_nhds]
  intro η hη
  have hβ1 : (0 : ℝ) < β + 1 := by linarith
  set ε : ℝ := η / (4 * (β + 1)) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  obtain ⟨δ, hδ, hδH⟩ := (Metric.uniformContinuousOn_iff_le.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := β)).uniformContinuousOn_of_continuous
      hH.continuousOn)) ε hε
  obtain ⟨n, hnlt⟩ := exists_nat_gt (β / δ)
  have hnR : (0 : ℝ) < (n : ℝ) := (div_pos hβ hδ).trans hnlt
  have hmesh : β / (n : ℝ) ≤ δ := by
    rw [div_lt_iff₀ hδ] at hnlt
    rw [div_le_iff₀ hnR]
    linarith
  set s : ℕ → ℝ := fun j ↦ (j : ℝ) * β / (n : ℝ) with hsdef
  have hs0 : s 0 = 0 := by simp [hsdef]
  have hsn : s n = β := by rw [hsdef]; field_simp
  have hsdiff : ∀ j, s (j + 1) - s j = β / (n : ℝ) := by
    intro j; rw [hsdef]; push_cast; ring
  have hsmono : ∀ j, s j ≤ s (j + 1) := fun j ↦ by linarith [hsdiff j, div_pos hβ hnR]
  have hsnn : ∀ j, 0 ≤ s j := by
    intro j; rw [hsdef]; positivity
  have hsle : ∀ j, j ≤ n → s j ≤ β := by
    intro j hj
    rw [hsdef, div_le_iff₀ hnR]
    nlinarith [(by exact_mod_cast hj : (j : ℝ) ≤ (n : ℝ))]
  have hsmem : ∀ j, j ≤ n → s j ∈ Set.Icc (0 : ℝ) β := fun j hj => ⟨hsnn j, hsle j hj⟩
  -- the Riemann sum of `H` at the right endpoints is within `ε β` of the integral
  have hRint : |(∑ j ∈ Finset.range n, H (s (j + 1)) * (s (j + 1) - s j))
      - ∫ t in (0 : ℝ)..β, H t| ≤ ε * β := by
    have hterm : ∀ k ∈ Finset.range n,
        |H (s (k + 1)) * (s (k + 1) - s k) - ∫ t in (s k)..(s (k + 1)), H t|
          ≤ ε * (s (k + 1) - s k) := by
      intro k hk
      have hkn : k + 1 ≤ n := Finset.mem_range.mp hk
      have hle : s k ≤ s (k + 1) := hsmono k
      have hrw : H (s (k + 1)) * (s (k + 1) - s k) - ∫ t in (s k)..(s (k + 1)), H t
          = ∫ t in (s k)..(s (k + 1)), (H (s (k + 1)) - H t) := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const
          (hH.intervalIntegrable _ _), intervalIntegral.integral_const, smul_eq_mul]
        ring
      rw [hrw]
      have hbd : ∀ t ∈ Set.uIoc (s k) (s (k + 1)), ‖H (s (k + 1)) - H t‖ ≤ ε := by
        intro t ht
        rw [Set.uIoc_of_le hle] at ht
        have htmem : t ∈ Set.Icc (0 : ℝ) β :=
          ⟨le_trans (hsnn k) ht.1.le, le_trans ht.2 (hsle _ hkn)⟩
        have hdist : dist (s (k + 1)) t ≤ δ := by
          rw [Real.dist_eq, abs_of_nonneg (by linarith [ht.2])]
          linarith [ht.1, hsdiff k]
        exact hδH (s (k + 1)) (hsmem _ hkn) t htmem hdist
      exact (intervalIntegral.norm_integral_le_of_norm_le_const hbd).trans_eq
        (by rw [abs_of_nonneg (sub_nonneg.2 hle)])
    have hsplit : (∫ t in (0 : ℝ)..β, H t)
        = ∑ k ∈ Finset.range n, ∫ t in (s k)..(s (k + 1)), H t := by
      rw [intervalIntegral.sum_integral_adjacent_intervals
        (fun k _ => hH.intervalIntegrable _ _), hs0, hsn]
    rw [hsplit, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_range_sub s, hs0, hsn, sub_zero]
  -- the three limits
  have hG : Tendsto (fun x : ℝ ↦ ∑ j ∈ Finset.range n, H (s (j + 1)) *
        (mertensKappa x * (muPhiWeightCut x (s (j + 1)) - muPhiWeightCut x (s j))))
      atTop (nhds (∑ j ∈ Finset.range n, H (s (j + 1)) * (s (j + 1) - s j))) := by
    refine tendsto_finsetSum _ fun j _ ↦ Tendsto.congr (fun x ↦ by ring)
      (((tendsto_mertensKappa_mul_muPhiWeightCut_of_nonneg (hsnn (j + 1))).sub
        (tendsto_mertensKappa_mul_muPhiWeightCut_of_nonneg (hsnn j))).const_mul _)
  have hK0 : Tendsto (fun x : ℝ ↦ mertensKappa x * |H 0|) atTop (nhds 0) := by
    simpa using tendsto_mertensKappa.mul_const |H 0|
  filter_upwards [hB, eventually_gt_atTop (1 : ℝ),
    Metric.tendsto_nhds.1 hG (η / 8) (by linarith),
    Metric.tendsto_nhds.1 (tendsto_mertensKappa_mul_muPhiWeightCut hβ) 1 one_pos,
    Metric.tendsto_nhds.1 hK0 (η / 8) (by linarith)] with x hBx hx1 hGx hAx hKx
  have hxpos : (0 : ℝ) < x := by linarith
  have hLx : 0 < Real.log x := Real.log_pos hx1
  have hkpos : 0 ≤ mertensKappa x := mertensKappa_nonneg hx1.le
  -- the partition points
  have hMmono : ∀ j, ⌊x ^ s j⌋₊ ≤ ⌊x ^ s (j + 1)⌋₊ := fun j =>
    Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hx1.le (hsmono j))
  have hMmono' : Monotone (fun j => ⌊x ^ s j⌋₊) := monotone_nat_of_le_succ hMmono
  have hM0 : ⌊x ^ s 0⌋₊ = 1 := by rw [hs0, Real.rpow_zero, Nat.floor_one]
  have hMn : ⌊x ^ s n⌋₊ = ⌊x ^ β⌋₊ := by rw [hsn]
  -- `log_x e` at the partition points
  have hlogxlo : ∀ (j : ℕ) (e : ℕ), ⌊x ^ s j⌋₊ < e → s j < Notation.logx x e := by
    intro j e he
    rw [Notation.logx, lt_div_iff₀ hLx, ← Real.log_rpow hxpos]
    exact Real.log_lt_log (by positivity) ((Nat.floor_lt (by positivity)).1 he)
  have hlogxhi : ∀ (j : ℕ) (e : ℕ), 1 ≤ e → e ≤ ⌊x ^ s j⌋₊ → Notation.logx x e ≤ s j := by
    intro j e he1 he
    rw [Notation.logx, div_le_iff₀ hLx, ← Real.log_rpow hxpos]
    exact Real.log_le_log (by exact_mod_cast he1) ((Nat.le_floor_iff (by positivity)).1 he)
  -- rewrite the sum as a plain sum of `muPhiWeightAt`
  have step1 : (∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
        ((μ e : ℝ) ^ 2 / moebiusTotient e) * H (Notation.logx x e))
      = ∑ e ∈ Finset.Icc 1 (B x), muPhiWeightAt x e * H (Notation.logx x e) := by
    simp only [Finset.sum_filter, muPhiWeightAt, ite_mul, zero_mul]
  have hfloorB : ⌊x ^ β⌋₊ ≤ B x := by simpa using Nat.floor_le_floor hBx
  have step2 : (∑ e ∈ Finset.Icc 1 (B x), muPhiWeightAt x e * H (Notation.logx x e))
      = ∑ e ∈ Finset.Icc 1 ⌊x ^ β⌋₊, muPhiWeightAt x e * H (Notation.logx x e) := by
    refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hfloorB) ?_).symm
    intro e he hne
    have hgt : ⌊x ^ β⌋₊ < e := by
      simp only [Finset.mem_Icc, not_and, not_le] at he hne
      exact hne he.1
    have := hlogxlo n e (by rwa [hMn])
    rw [hsn] at this
    rw [hHv _ this.le, mul_zero]
  have hM1 : ∀ j : ℕ, 1 ≤ ⌊x ^ s j⌋₊ := fun j ↦ hM0 ▸ hMmono' j.zero_le
  have hsplit : ∀ (f : ℕ → ℝ) {a b : ℕ}, a ≤ b →
      ∑ e ∈ Finset.Icc 1 b, f e = ∑ e ∈ Finset.Icc 1 a, f e + ∑ e ∈ Finset.Ioc a b, f e := by
    intro f a b hab
    rw [← Finset.sum_union (Finset.disjoint_left.2 fun e he he' ↦ by
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at he he'; omega)]
    congr 1
    ext e
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have step3 : (∑ e ∈ Finset.Icc 1 ⌊x ^ β⌋₊, muPhiWeightAt x e * H (Notation.logx x e))
      = H 0 + ∑ j ∈ Finset.range n,
          ∑ e ∈ Finset.Ioc ⌊x ^ s j⌋₊ ⌊x ^ s (j + 1)⌋₊,
            muPhiWeightAt x e * H (Notation.logx x e) := by
    rw [← hMn, sum_Ioc_chain hMmono, hM0, hsplit _ (hM1 n)]
    simp [muPhiWeightAt, Notation.logx, moebiusTotient_one]
  -- the normalized mass of each block
  have hWtblk : ∀ j : ℕ, (∑ e ∈ Finset.Ioc ⌊x ^ s j⌋₊ ⌊x ^ s (j + 1)⌋₊, muPhiWeightAt x e)
      = muPhiWeightCut x (s (j + 1)) - muPhiWeightCut x (s j) := by
    intro j
    rw [muPhiWeightCut_eq_sum, muPhiWeightCut_eq_sum, hsplit _ (hMmono j)]
    ring
  -- the block estimate
  have hblk : ∀ j ∈ Finset.range n,
      |(∑ e ∈ Finset.Ioc ⌊x ^ s j⌋₊ ⌊x ^ s (j + 1)⌋₊, muPhiWeightAt x e * H (Notation.logx x e))
          - H (s (j + 1)) * (muPhiWeightCut x (s (j + 1)) - muPhiWeightCut x (s j))|
        ≤ ε * (muPhiWeightCut x (s (j + 1)) - muPhiWeightCut x (s j)) := by
    intro j hj
    have hjn : j + 1 ≤ n := Finset.mem_range.mp hj
    have hgb : ∀ e ∈ Finset.Ioc ⌊x ^ s j⌋₊ ⌊x ^ s (j + 1)⌋₊,
        |H (Notation.logx x e) - H (s (j + 1))| ≤ ε := by
      intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_Ioc.mp he
      have he1' : 1 ≤ e := le_trans (hM1 j) he1.le
      have hlo := hlogxlo j e he1
      have hhi := hlogxhi (j + 1) e he1' he2
      have hmem : Notation.logx x e ∈ Set.Icc (0 : ℝ) β :=
        ⟨le_trans (hsnn j) hlo.le, le_trans hhi (hsle _ hjn)⟩
      have hd : dist (Notation.logx x e) (s (j + 1)) ≤ δ := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith)]
        linarith [hsdiff j]
      exact hδH _ hmem _ (hsmem _ hjn) hd
    rw [← hWtblk j]
    exact abs_sum_sub_const_mul_le (fun e _ ↦ muPhiWeightAt_nonneg x e) hgb
  have hblksum : |(∑ j ∈ Finset.range n, ∑ e ∈ Finset.Ioc ⌊x ^ s j⌋₊ ⌊x ^ s (j + 1)⌋₊,
          muPhiWeightAt x e * H (Notation.logx x e))
        - ∑ j ∈ Finset.range n, H (s (j + 1)) *
            (muPhiWeightCut x (s (j + 1)) - muPhiWeightCut x (s j))|
      ≤ ε * (muPhiWeightCut x β - 1) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hblk).trans_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun j ↦ muPhiWeightCut x (s j)), hs0, hsn,
      muPhiWeightCut_zero]
  -- assemble
  have hQ : mertensKappa x * (∑ j ∈ Finset.range n, H (s (j + 1)) *
        (muPhiWeightCut x (s (j + 1)) - muPhiWeightCut x (s j)))
      = ∑ j ∈ Finset.range n, H (s (j + 1)) *
        (mertensKappa x * (muPhiWeightCut x (s (j + 1)) - muPhiWeightCut x (s j))) := by
    rw [Finset.mul_sum]
    ring_nf
  have hSid : mertensKappa x * (∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
        ((μ e : ℝ) ^ 2 / moebiusTotient e) * H (Notation.logx x e))
      = mertensKappa x * H 0 + mertensKappa x *
          ∑ j ∈ Finset.range n, ∑ e ∈ Finset.Ioc ⌊x ^ s j⌋₊ ⌊x ^ s (j + 1)⌋₊,
            muPhiWeightAt x e * H (Notation.logx x e) := by
    rw [step1, step2, step3, mul_add]
  -- the numerical bounds
  rw [Real.dist_eq] at hGx hAx hKx
  set P : ℝ := ∑ j ∈ Finset.range n, ∑ e ∈ Finset.Ioc ⌊x ^ s j⌋₊ ⌊x ^ s (j + 1)⌋₊,
    muPhiWeightAt x e * H (Notation.logx x e)
  set Q : ℝ := ∑ j ∈ Finset.range n, H (s (j + 1)) *
    (muPhiWeightCut x (s (j + 1)) - muPhiWeightCut x (s j))
  set Gv : ℝ := ∑ j ∈ Finset.range n, H (s (j + 1)) *
    (mertensKappa x * (muPhiWeightCut x (s (j + 1)) - muPhiWeightCut x (s j)))
  set R : ℝ := ∑ j ∈ Finset.range n, H (s (j + 1)) * (s (j + 1) - s j)
  set I : ℝ := ∫ t in (0 : ℝ)..β, H t
  have hεβ : ε * (β + 1) = η / 4 := by rw [hεdef]; field_simp
  have hAlt : mertensKappa x * muPhiWeightCut x β < β + 1 := by linarith [(abs_lt.1 hAx).2]
  have hb1 : |mertensKappa x * H 0| < η / 8 := by
    rw [abs_mul, abs_of_nonneg hkpos]
    linarith [(abs_lt.1 hKx).2]
  have hb2 : |mertensKappa x * P - Gv| ≤ η / 4 := by
    rw [← hQ, ← mul_sub, abs_mul, abs_of_nonneg hkpos]
    nlinarith [mul_le_mul_of_nonneg_left hblksum hkpos, muPhiWeightCut_nonneg x β]
  rw [hSid, Real.dist_eq, show mertensKappa x * H 0 + mertensKappa x * P - I
      = mertensKappa x * H 0 + (mertensKappa x * P - Gv) + (Gv - R) + (R - I) by ring]
  linarith [hRint,
    abs_add_le (mertensKappa x * H 0 + (mertensKappa x * P - Gv) + (Gv - R)) (R - I),
    abs_add_three (mertensKappa x * H 0) (mertensKappa x * P - Gv) (Gv - R)]

/-- **An instance of the measure theorem with a positive limit.** Every hypothesis of
`Gap212.Sieve.tendsto_mertensKappa_mul_muPhiWeightedSum` is met by `H = (F')²` at
`F = Gap212.Sieve.gramCexProfile`, the `C^∞` bump with `tsupport F = [2,4]`, which is continuous
and vanishes on `[5,∞)`; `β = 5 > 0`; and `B(x) = ⌊x^5⌋+1 ≥ x^5`. The limit is then `∫_0^∞(F')²`,
which is **positive** (`Gap212.Sieve.integral_deriv_gramCexProfile_sq_pos`). The totient
counterpart of `Gap212.Sieve.tendsto_mertensKappa_mul_weightedSum_gramCex`, at the same bump and
the same `β`. -/
theorem tendsto_mertensKappa_mul_muPhiWeightedSum_gramCex :
    (0 < ∫ t in Set.Ioi (0 : ℝ), deriv gramCexProfile t * deriv gramCexProfile t)
      ∧ Tendsto (fun x : ℝ ↦ mertensKappa x *
          ∑ e ∈ Icc 1 (⌊x ^ (5 : ℝ)⌋₊ + 1) with Nat.Coprime (W x) e,
            ((μ e : ℝ) ^ 2 / moebiusTotient e) *
              (deriv gramCexProfile (Notation.logx x e) * deriv gramCexProfile (Notation.logx x e)))
        atTop (nhds (∫ t in Set.Ioi (0 : ℝ), deriv gramCexProfile t * deriv gramCexProfile t)) := by
  have hvan : ∀ t : ℝ, (5 : ℝ) ≤ t → gramCexProfile t = 0 := by
    intro t ht
    refine image_eq_zero_of_notMem_tsupport ?_
    rw [gramCexProfile_tsupport, Metric.mem_closedBall, Real.dist_eq]
    intro hc
    linarith [(abs_le.mp hc).2]
  have hcont : Continuous fun t : ℝ ↦ deriv gramCexProfile t * deriv gramCexProfile t :=
    gramCexProfile_contDiff_one.continuous_deriv_one.mul
      gramCexProfile_contDiff_one.continuous_deriv_one
  refine ⟨integral_deriv_gramCexProfile_sq_pos,
    tendsto_mertensKappa_mul_muPhiWeightedSum (β := 5) hcont (by norm_num) (fun t ht ↦ ?_) _ ?_⟩
  · rw [deriv_eq_zero_of_eventually_zero gramCexProfile_contDiff_one hvan t ht, zero_mul]
  · filter_upwards with x
    push_cast
    linarith [Nat.lt_floor_add_one (x ^ (5 : ℝ))]

/-! ## The defect statement: the normalized inner sums, and nothing else -/

/-- **The totient Gram sum's inner sum degenerates to a single term at the top of the `e`-range.**
If every prime up to `B/e` divides `eW` then `Gap212.Sieve.innerTotient` is just its `f = 1` term,
`F(\log_xe)`: no cancellation is available there, because there is nothing to cancel. The totient
counterpart of `Gap212.Sieve.innerRecip_eq_of_primes_dvd`, and it holds for the same reason — the
`f`-range is the integers below `B/e` coprime to `eW`, and coprimality to a modulus divisible by
every prime in range leaves only `f = 1`. The weight `1/φ(f)` of this kernel against the `1/f` of
the reciprocal one plays no part. -/
theorem innerTotient_eq_of_primes_dvd {W e B : ℕ} {x : ℝ} (he : 0 < e) (heB : e ≤ B)
    (hq : ∀ p : ℕ, p.Prime → p ≤ B / e → p ∣ e * W) (F : ℝ → ℝ) :
    innerTotient W e F x B = F (Notation.logx x e) := by
  classical
  have hset : ({f ∈ Icc 1 (B / e) | Nat.Coprime e f ∧ Nat.Coprime W f} : Finset ℕ) = {1} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hf1, hfw⟩, hef, hWf⟩
      by_contra hne
      obtain ⟨p, hp, hpf⟩ := Nat.exists_prime_and_dvd hne
      exact hp.coprime_iff_not_dvd.1 ((hef.mul_left hWf).coprime_dvd_left
        (hq p hp ((Nat.le_of_dvd (by omega) hpf).trans hfw))) hpf
    · rintro rfl
      exact ⟨⟨le_rfl, (Nat.one_le_div_iff he).mpr heB⟩, Nat.coprime_one_right _,
        Nat.coprime_one_right _⟩
  simp [innerTotient, hset]

/-- **The top of the totient Gram sum's own `e`-range is the one-term regime, named.** At
`W = W(x)`, the primorial of `z = ⌊\log\log\log x⌋`, every `e` with `B/e < z+1` — that is, every
`e ∈ (B/(z+1), B]` — has a one-term inner sum, because a prime `p ≤ B/e` is then `≤ z` and so
divides the primorial. This is the totient analogue of
`Gap212.Sieve.innerRecip_eq_of_lt_primorial_bound`: the regime is present in this kernel too, at
exactly the same range of `e`, so the defect statement
`Gap212.Sieve.TotientGramRatioDefectVanishes` has to be an *average* over `e` and not a pointwise
bound. There `\log x·Y_F(e) = \log x·F(\log_xe)`, which the support hypothesis makes small only
through `\log_xe ≥ \log_xB - \log(z+1)/\log x ≥ β - \log(z+1)/\log x`. -/
theorem innerTotient_eq_of_lt_primorial_bound {x : ℝ} {e B : ℕ} (he : 0 < e) (heB : e ≤ B)
    (hz : (B : ℝ) / (e : ℝ) < (⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1) (F : ℝ → ℝ) :
    innerTotient (W x) e F x B = F (Notation.logx x e) := by
  refine innerTotient_eq_of_primes_dvd he heB (fun p hp hple ↦ ?_) F
  have hfl : B / e ≤ ⌊Real.log (Real.log (Real.log x))⌋₊ :=
    Nat.lt_succ_iff.1 (by exact_mod_cast Nat.cast_div_le.trans_lt hz)
  exact (hp.dvd_primorial_iff.2 (hple.trans hfl)).mul_left e

/-- Pulling the normalization through a difference of `μ²/(μ*φ)`-weighted sums. -/
theorem mertensKappa_mul_muPhiSum_sub (x : ℝ) (N : ℕ) (a b : ℕ → ℝ) :
    mertensKappa x * ∑ e ∈ Icc 1 N with Nat.Coprime (W x) e,
        ((μ e : ℝ) ^ 2 / moebiusTotient e) * (a e - b e)
      = (mertensKappa x * ∑ e ∈ Icc 1 N with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / moebiusTotient e) * a e)
        - mertensKappa x * ∑ e ∈ Icc 1 N with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / moebiusTotient e) * b e := by
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun e _ ↦ by ring)

/-- **The totient Gram-sum limit, as a defect statement.** With
`ρ_F(e) = \log x·Y_F(e)·((μ*φ)(e)/φ(e))·(φ(W)/W)` the normalized inner sum
(`Gap212.Sieve.innerTotientRatio`) and `κ_x = (W/φ(W))/\log x`, this says that the *defect* between
the true summand and `F'(\log_xe)G'(\log_xe)` has vanishing normalized weighted sum:

  `κ_x·∑_{e≤B,(e,W)=1}(μ²(e)/(μ*φ)(e))·(ρ_F(e)ρ_G(e) − F'(\log_xe)G'(\log_xe)) ⟶ 0`.

`Gap212.Sieve.totientGramSumLimitOfSupport_iff_totientGramRatioDefectVanishes` proves this
**equivalent** to `Gap212.Sieve.TotientGramSumLimitOfSupport`: it is the Gram-sum limit with the
arithmetic removed.

**What is removed is more than on the reciprocal side.** Three things are gone and each was a
separate hazard: the Mertens sum for `μ²/(μ*φ)`, whose constant is *not* `φ(W)/W`; the factor
`φ(W)/W` itself; and the correction factor `∏_{p∤W}(1-1/(p-1)²)`, which at fixed `W` is the
twin-prime constant `0.660162` and is *not* present here — the predicted value of `ρ_F(e)` carries
two powers of it and the weight's Mertens constant one inverse power
(`Gap212.Sieve.innerSumTotientConst_mul_normalization`), and
`Gap212.Sieve.tendsto_mertensKappa_mul_muPhiWeightedSum` has already spent the surviving power
against `Gap212.Sieve.tendsto_inv_tprod_corr_W`. So this statement identifies no constant at all.

**The statement must be an average.** At the top of the
`e`-range `Gap212.Sieve.innerTotient_eq_of_lt_primorial_bound` collapses the inner sum to its
single term `F(\log_xe)`: every `e ∈ (B/(z+1), B]` with `z = ⌊\log\log\log x⌋` is in that regime,
because a prime `p ≤ B/e < z+1` divides the primorial `W(x)`. There `ρ_F(e)` is of size `\log(z+1)`
— unbounded — against a prediction near `F'(β) = 0`, so no *pointwise* statement
`ρ_F(e) → -F'(\log_xe)·∏_{p∤W}(1-1/(p-1)²)` is true. What makes the regime harmless is that `F`
vanishes from
`β` on and `B ≥ x^β`, forcing `|F(\log_xe)| ≤ ‖F'‖_∞·\log(z+1)/\log x` there, together with the
same Mertens asymptotic making its normalized weight `O(\log(z+1)/\log x)`.

The profiles are `C^∞`, as in `Gap212.Sieve.TotientGramSumLimitOfSupport`. -/
def TotientGramRatioDefectVanishes : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → ContDiff ℝ (⊤ : ℕ∞) G →
    HasCompactSupport G →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) → (∀ t, β ≤ t → G t = 0) →
      ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
        Filter.Tendsto (fun x : ℝ ↦ mertensKappa x *
            ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
              ((μ e : ℝ) ^ 2 / moebiusTotient e) *
                (innerTotientRatio (W x) e F x (B x) * innerTotientRatio (W x) e G x (B x)
                  - deriv F (Notation.logx x e) * deriv G (Notation.logx x e)))
          Filter.atTop (nhds 0)

/-- **The Riemann form and the defect form are the same statement.** Both sides are compared
against the one limit that is a theorem: the predicted summand's normalized weighted sum converges
to `∫_0^∞F'G'` (`Gap212.Sieve.tendsto_mertensKappa_mul_muPhiWeightedSum` at `H = F'G'`, continuous
and vanishing on `[β,∞)` by `Gap212.Sieve.deriv_eq_zero_of_eventually_zero`). Subtracting it turns
the Riemann form into the defect statement and adding it back turns the defect statement into the
Riemann form, so nothing is weakened in either direction. -/
theorem totientMuPhiWeightedGramLimit_iff_totientGramRatioDefectVanishes :
    TotientMuPhiWeightedGramLimit ↔ TotientGramRatioDefectVanishes := by
  have hmeas : ∀ (F G : ℝ → ℝ), ContDiff ℝ 1 F → ContDiff ℝ 1 G → ∀ β : ℝ, 0 < β →
      (∀ t, β ≤ t → F t = 0) → ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
      Tendsto (fun x : ℝ ↦ mertensKappa x *
          ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
            ((μ e : ℝ) ^ 2 / moebiusTotient e) *
              (deriv F (Notation.logx x e) * deriv G (Notation.logx x e)))
        atTop (nhds (∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t)) := by
    intro F G hF hG β hβ hFv B hB
    have hcont : Continuous fun t : ℝ ↦ deriv F t * deriv G t :=
      hF.continuous_deriv_one.mul hG.continuous_deriv_one
    refine tendsto_mertensKappa_mul_muPhiWeightedSum hcont hβ (fun t ht ↦ ?_) B hB
    rw [deriv_eq_zero_of_eventually_zero hF hFv t ht, zero_mul]
  -- `hmeas` is the `C¹` statement; both sides now supply `C^∞`, which is a `C¹`.
  have hdown : ∀ H : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) H → ContDiff ℝ 1 H :=
    fun _ hH ↦ hH.of_le (by exact_mod_cast le_top)
  constructor
  · intro h F G hF hFc hG hGc β hβ hFv hGv B hB
    have h1 := h F G hF hFc hG hGc β hβ hFv hGv B hB
    simp only [mertensKappa_eq] at h1
    simpa only [mertensKappa_mul_muPhiSum_sub, sub_self] using
      h1.sub (hmeas F G (hdown F hF) (hdown G hG) β hβ hFv B hB)
  · intro h F G hF hFc hG hGc β hβ hFv hGv B hB
    have h1 := h F G hF hFc hG hGc β hβ hFv hGv B hB
    simp only [mertensKappa_mul_muPhiSum_sub] at h1
    simpa only [zero_add, sub_add_cancel, mertensKappa] using
      h1.add (hmeas F G (hdown F hF) (hdown G hG) β hβ hFv B hB)

/-- **`Gap212.Sieve.TotientGramSumLimitOfSupport` is equivalent to the defect statement.** The two
equivalences composed: `Gap212.Sieve.totientGramSumLimitOfSupport_iff` removes the normalization
and `Gap212.Sieve.totientMuPhiWeightedGramLimit_iff_totientGramRatioDefectVanishes` the arithmetic,
leaving `Gap212.Sieve.TotientGramRatioDefectVanishes`, a purely analytic statement about the inner
sums with no Mertens sum, no `φ(W)/W` and no constant to identify. -/
theorem totientGramSumLimitOfSupport_iff_totientGramRatioDefectVanishes :
    TotientGramSumLimitOfSupport ↔ TotientGramRatioDefectVanishes :=
  totientGramSumLimitOfSupport_iff.trans
    totientMuPhiWeightedGramLimit_iff_totientGramRatioDefectVanishes

/-- **The weighted-`ℓ¹` form of the defect statement**: the *absolute* defect has vanishing
normalized weighted sum. Sufficient for `Gap212.Sieve.TotientGramSumLimitOfSupport`
(`Gap212.Sieve.totientGramSumLimitOfSupport_of_totientNormalizedInnerRatioL1`) and strictly
stronger than the equivalent `Gap212.Sieve.TotientGramRatioDefectVanishes`, since it forbids
cancellation between the `e`'s.

The profiles here are `C¹`, while `Gap212.Sieve.TotientGramSumLimitOfSupport` and
`Gap212.Sieve.TotientGramRatioDefectVanishes` are stated for `C^∞` profiles; since this `Prop` only
implies them, the `of_le` in
`Gap212.Sieve.totientGramRatioDefectVanishes_of_totientNormalizedInnerRatioL1` passes from `C^∞` to
`C¹`. -/
def TotientNormalizedInnerRatioL1 : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F → ContDiff ℝ 1 G → HasCompactSupport G →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) → (∀ t, β ≤ t → G t = 0) →
      ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
        Filter.Tendsto (fun x : ℝ ↦ mertensKappa x *
            ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
              ((μ e : ℝ) ^ 2 / moebiusTotient e) *
                |innerTotientRatio (W x) e F x (B x) * innerTotientRatio (W x) e G x (B x)
                  - deriv F (Notation.logx x e) * deriv G (Notation.logx x e)|)
          Filter.atTop (nhds 0)

/-- The `ℓ¹` form implies the defect form: a sum is at most the sum of the absolute values, the
weight `μ²(e)/(μ*φ)(e)` being nonnegative (`Gap212.Sieve.muPhiWeight_term_nonneg`). -/
theorem totientGramRatioDefectVanishes_of_totientNormalizedInnerRatioL1
    (h : TotientNormalizedInnerRatioL1) : TotientGramRatioDefectVanishes := by
  intro F G hF hFc hG hGc β hβ hFv hGv B hB
  replace hF : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast le_top)
  replace hG : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast le_top)
  refine squeeze_zero_norm' ?_ (h F G hF hFc hG hGc β hβ hFv hGv B hB)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mertensKappa_nonneg hx)]
  refine mul_le_mul_of_nonneg_left ?_ (mertensKappa_nonneg hx)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun e _ ↦ ?_)
  rw [abs_mul, abs_of_nonneg (muPhiWeight_term_nonneg e)]

/-- **The totient Gram-sum limit, from the weighted-`ℓ¹` input.** -/
theorem totientGramSumLimitOfSupport_of_totientNormalizedInnerRatioL1
    (h : TotientNormalizedInnerRatioL1) : TotientGramSumLimitOfSupport :=
  totientGramSumLimitOfSupport_iff_totientGramRatioDefectVanishes.2
    (totientGramRatioDefectVanishes_of_totientNormalizedInnerRatioL1 h)

end Gap212.Sieve
