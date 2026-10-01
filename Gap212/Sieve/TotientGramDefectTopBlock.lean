/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.GramDefectTopBlock
public import Gap212.Sieve.TotientGramDefectMeanSquare

/-!
# The totient mean square split at the one-term top block

`Gap212.Sieve.TotientGramDefectMeanSquare` reduces the totient Gram-sum limit
`Gap212.Sieve.TotientGramSumLimitOfSupport` to the one-profile mean
square `Gap212.Sieve.TotientNormalizedInnerL2`,

  `κ_x·∑_{e≤B,(e,W)=1}(μ²(e)/(μ*φ)(e))·a_F(e)² ⟶ 0`,  `a_F(e) = ρ_F(e) + F'(log_xe)`,

and bounds the *size* of `a_F` in the one place where the pointwise limit is provably false: the
top of the `e`-range, `e ∈ (B/(z+1),B]` with `z = ⌊log log log x⌋`, where
`Gap212.Sieve.innerTotient_eq_of_lt_primorial_bound` collapses the inner sum to a single term. It
does not bound that block's *weight*. This file supplies the weight, and with it the block.

## The top block

The truncation is fixed at `B(x) = ⌊x^β⌋+1`, which costs nothing
(`Gap212.Sieve.totientNormalizedInnerL2_iff_atCut`, an `iff`). There the block is the integer
condition `B < e(z+1)`, sitting inside `(N,B]` with `N = ⌊B/(z+1)⌋`. Two readings of
`Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime`, at `N` and at `B`, leave
(`Gap212.Sieve.exists_kappa_mul_muPhiWeightUpTo_sub_le`,
`Gap212.Sieve.exists_kappa_mul_muPhiTopBlockWeight_le`)

  `κ_x·∑_{block}μ²(e)/(μ*φ)(e) ≤ (∏_{p∤W}(1-1/(p-1)²))^{-1}(log(z+1)+1)/log x + Cκ_x(τ(W)+ℓ_W)`,

since `B ≤ 2(z+1)N` and `log 2 ≤ 1`. Multiplied by the size bound
`|a_F(e)| ≤ ‖F'‖_∞(log(z+1)+1)` this gives `Gap212.Sieve.kappa_mul_totientGramTopSum_le`, and both
terms vanish (`Gap212.Sieve.tendsto_kappa_mul_totientGramTopSum`).

## Where this differs from the reciprocal kernel

Four places, and each is a constant or an estimate rather than a rearrangement.

* **The main term carries the inverse correction factor.** It is bounded only by
  `Gap212.Sieve.eventually_inv_muPhiCorr_le_two`, from the proved
  `Gap212.Sieve.tendsto_inv_tprod_corr_W`; nothing of the kind appears in
  `Gap212.Sieve.exists_kappa_mul_weightUpTo_sub_le`, whose Mertens constant is `φ(W)/W` exactly.
* **The Mertens error is additive and `N`-free**, `C(τ(W)+ℓ_W)`, against the reciprocal kernel's
  `C(1+τ(W)/N)`. So the block hypothesis is `2(z+1) ≤ B` and not `2(z+1)(W+1) ≤ B`: this kernel
  needs no `W ≤ N`.
* **That error needs a rate, and one is proved here.** The limit is all
  `Gap212.Sieve.tendsto_mertensKappa_mul_muPhiErr` gives, and the block multiplies the error by
  `(log log log x+1)²`, which tends to infinity. The rate `O((log log x)⁴/log x)` is exposed by
  `Gap212.Sieve.eventually_mertensKappa_mul_muPhiErr_le`, and the product is killed by
  `Gap212.Sieve.tendsto_logLogLog_pow_mul_muPhiErr`. The reciprocal side's corresponding step is
  `Gap212.Sieve.tendsto_logLogLog_pow_mul_mertensKappa`, about `κ_x` alone.
* **The pointwise bound is conditional on squarefreeness**,
  and the summand is bounded by a case split on it
  (`Gap212.Sieve.muPhiWeight_mul_sq_le_of_topBlock`): off the squarefree `e` the weight is `0`. The
  reciprocal kernel's pointwise bound needs no hypothesis.

The proved bound is of order `(log log log log x)²(log log x)⁴/log x`, the Mertens error
dominating; the predicted main term is `(log log log log x)³/log x`. **Neither rate is
claimed by the conclusion**, which is the limit only.

## The bulk statement

`Gap212.Sieve.TotientBulkInnerL2`: the same mean square with the sum restricted to `e ≤ B/(z+1)`.
It implies `Gap212.Sieve.TotientGramSumLimitOfSupport`
(`Gap212.Sieve.totientGramSumLimitOfSupport_of_totientBulkInnerL2`), and since the removed summands
are nonnegative with vanishing normalized sum it is **equivalent** to
`Gap212.Sieve.TotientNormalizedInnerL2` (`Gap212.Sieve.totientBulkInnerL2_iff`). The split removes
summands from a sum; it does not make the bulk statement logically weaker. What it buys is that the
one regime in which the per-`e` asymptotic is false is outside `Gap212.Sieve.TotientBulkInnerL2`.
That statement is not proved in this repository; `Gap212.Sieve.TotientGramSumLimitOfSupport` itself
follows from `Gap212.Sieve.polymath41Totient` by
`Gap212.Sieve.totientGramSumLimitOfSupport_iff_polymath41Totient`.

## Main definitions

* `Gap212.Sieve.muPhiWeightUpTo`: the `μ²/(μ*φ)` weight below a general `N`.
* `Gap212.Sieve.totientGramTopSum`, `Gap212.Sieve.totientGramBulkSum`: the two halves at the cut.
* `Gap212.Sieve.TotientNormalizedInnerL2AtCut`, `Gap212.Sieve.TotientBulkInnerL2`.

## Main results

* `Gap212.Sieve.eventually_mertensKappa_mul_muPhiErr_le`,
  `Gap212.Sieve.tendsto_logLogLog_pow_mul_muPhiErr`: the rate of this kernel's Mertens error.
* `Gap212.Sieve.exists_kappa_mul_muPhiWeightUpTo_sub_le`,
  `Gap212.Sieve.exists_kappa_mul_muPhiTopBlockWeight_le`: the normalized weight of a block, and of
  the top block.
* `Gap212.Sieve.tendsto_kappa_mul_totientGramTopSum`: the top block contributes nothing.
* `Gap212.Sieve.totientNormalizedInnerL2_iff_atCut`: the truncation quantifier is spurious.
* `Gap212.Sieve.totientBulkInnerL2_iff`,
  `Gap212.Sieve.totientGramSumLimitOfSupport_of_totientBulkInnerL2`: the Gram-sum limit from the
  bulk, and that the bulk is equivalent to the whole mean square.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY
open scoped ArithmeticFunction.Moebius

/-! ## The rate the `μ²/(μ*φ)` Mertens error vanishes at -/

private theorem muPhiErr_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ mertensKappa x * ((#(W x).divisors : ℝ) + PrimeGaps.ellV (W x)) :=
  mul_nonneg (mertensKappa_nonneg hx) (add_nonneg (Nat.cast_nonneg _) (PrimeGaps.ellV_nonneg _))

/-- **The normalized Mertens error is `O((log log x)⁴/log x)`.** The rate behind
`Gap212.Sieve.tendsto_mertensKappa_mul_muPhiErr`: `κ_x ≤ W(x)/log x`,
`τ(W) ≤ W`, `ℓ_W ≤ log W ≤ W` and `W(x) ≤ (log log x)²`
(`Gap212.Sieve.W_le_log_log_sq`). The top block needs the rate and not only the limit, because it
multiplies this error by a factor that tends to infinity. -/
theorem eventually_mertensKappa_mul_muPhiErr_le :
    ∀ᶠ x : ℝ in atTop, mertensKappa x * ((#(W x).divisors : ℝ) + PrimeGaps.ellV (W x))
      ≤ 2 * (Real.log (Real.log x) ^ 4 / Real.log x) := by
  filter_upwards [W_le_log_log_sq, eventually_gt_atTop (1 : ℝ)] with x hW hx1
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hW1 : 1 ≤ W x := primorial_pos _
  have hWR : (1 : ℝ) ≤ (W x : ℝ) := by exact_mod_cast hW1
  have hphi1 : (1 : ℝ) ≤ ((W x).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hW1
  have hτ : ((#(W x).divisors : ℕ) : ℝ) ≤ (W x : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self (W x)
  have hell : PrimeGaps.ellV (W x) ≤ (W x : ℝ) := (ellV_le_log hW1).trans <| by
    linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (W x : ℝ))]
  have hkap : mertensKappa x ≤ (W x : ℝ) / Real.log x := by
    rw [mertensKappa, div_le_div_iff_of_pos_right hL, div_le_iff₀ (by linarith)]
    nlinarith
  calc _ ≤ ((W x : ℝ) / Real.log x) * (2 * (W x : ℝ)) :=
        mul_le_mul hkap (by linarith) (add_nonneg (Nat.cast_nonneg _) (PrimeGaps.ellV_nonneg _))
          (by positivity)
    _ = 2 * ((W x : ℝ) ^ 2 / Real.log x) := by ring
    _ ≤ _ := by
        gcongr
        exact (pow_le_pow_left₀ (by positivity) hW 2).trans_eq (by ring)

/-- **`(log log log x + 1)^n·κ_x·(τ(W(x)) + ℓ_{W(x)}) ⟶ 0`.** The normalized Mertens error still
vanishes after multiplication by any fixed power of `log log log x`: by
`Gap212.Sieve.eventually_mertensKappa_mul_muPhiErr_le` the product is at most
`2(log log x + 1)^{n+4}/log x`, which is `Gap212.Sieve.tendsto_pow_log_add_one_div` read at
`t = log x`. This is the totient kernel's counterpart of
`Gap212.Sieve.tendsto_logLogLog_pow_mul_mertensKappa`, and it is a different statement: that one
carries `κ_x` alone, this one the whole `W`-dependent error `τ(W) + ℓ_W` that this kernel's Mertens
asymptotic names. -/
theorem tendsto_logLogLog_pow_mul_muPhiErr (n : ℕ) :
    Tendsto (fun x : ℝ ↦ (Real.log (Real.log (Real.log x)) + 1) ^ n *
        (mertensKappa x * ((#(W x).divisors : ℝ) + PrimeGaps.ellV (W x)))) atTop (nhds 0) := by
  have hmaj : Tendsto (fun x : ℝ ↦
      2 * ((Real.log (Real.log x) + 1) ^ (n + 4) / Real.log x)) atTop (nhds 0) := by
    simpa using ((tendsto_pow_log_add_one_div (n + 4)).comp Real.tendsto_log_atTop).const_mul 2
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_logLogLog_le, eventually_ge_atTop (1 : ℝ)] with x hlll hx1
    exact mul_nonneg (pow_nonneg (by linarith [hlll.1]) n) (muPhiErr_nonneg hx1)
  · filter_upwards [eventually_logLogLog_le, eventually_mertensKappa_mul_muPhiErr_le,
      eventually_gt_atTop (1 : ℝ)] with x ⟨hlll0, hlll2, _⟩ herr hx1
    have hL : 0 < Real.log x := Real.log_pos hx1
    have hll : 0 ≤ Real.log (Real.log x) := by linarith
    calc _ ≤ (Real.log (Real.log x) + 1) ^ n * (2 * (Real.log (Real.log x) ^ 4 / Real.log x)) :=
          mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) n) herr
            (muPhiErr_nonneg hx1.le) (by positivity)
      _ ≤ (Real.log (Real.log x) + 1) ^ n
            * (2 * ((Real.log (Real.log x) + 1) ^ 4 / Real.log x)) := by
          gcongr
          linarith
      _ = _ := by ring

/-! ## The `μ²/(μ*φ)` weight of a block, and of the top block -/

/-- **The `μ²/(μ*φ)` weight summed over the coprimality class below a general `N`.**
`Gap212.Sieve.muPhiWeightCut` is its value at `N = ⌊x^s⌋`; the split of the mean square is at a
cutoff that is not a power of `x`. -/
noncomputable def muPhiWeightUpTo (x : ℝ) (N : ℕ) : ℝ :=
  ∑ e ∈ Icc 1 N with Nat.Coprime (W x) e, ((μ e : ℝ) ^ 2 / moebiusTotient e)

/-- `muPhiWeightCut x s` is `muPhiWeightUpTo` at the cutoff `N = ⌊x ^ s⌋₊`. -/
theorem muPhiWeightCut_eq_upTo (x s : ℝ) : muPhiWeightCut x s = muPhiWeightUpTo x ⌊x ^ s⌋₊ := rfl

/-- **The inverse correction factor tends to `1`**, at the abbreviation. -/
theorem tendsto_inv_muPhiCorr : Tendsto (fun x : ℝ ↦ (muPhiCorr x)⁻¹) atTop (nhds 1) :=
  tendsto_inv_tprod_corr_W

/-- **The inverse correction factor is eventually at most `2`.** This is all the top block needs
of it. -/
theorem eventually_inv_muPhiCorr_le_two : ∀ᶠ x : ℝ in atTop, (muPhiCorr x)⁻¹ ≤ 2 :=
  (tendsto_inv_muPhiCorr.eventually_lt_const (by norm_num)).mono fun _ ↦ le_of_lt

/-- **The normalized `μ²/(μ*φ)` weight of a block `(N₁,N₂]`.** Two readings of
`Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime`, at `N₁` and at `N₂`, cancel the `log N`
main term's constant against itself and leave

  `κ_x·(A_W(N₂) - A_W(N₁)) ≤ (∏_{p∤W}(1-1/(p-1)²))^{-1}(log N₂ - log N₁)/log x + Cκ_x(τ(W)+ℓ_W)`,

since `κ_x·(φ(W)/W) = 1/log x` exactly.

**Two differences from the reciprocal kernel's `Gap212.Sieve.exists_kappa_mul_weightUpTo_sub_le`.**
The main term carries the correction factor's inverse, which is why
`Gap212.Sieve.eventually_inv_muPhiCorr_le_two` is needed downstream and nothing of the kind is
needed there. And the error is **additive and independent of `N`**, where the reciprocal kernel's
is `C(1 + τ(W)/N)`: so this statement needs no lower bound on `N₁` beyond `1`, and the consumer
needs no `W ≤ N₁`. Evenness of `W` is required, as everywhere in this kernel, because
`(μ*φ)(2) = 0`. -/
theorem exists_kappa_mul_muPhiWeightUpTo_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → 2 ∣ W x → ∀ N₁ N₂ : ℕ, 1 ≤ N₁ → N₁ ≤ N₂ →
      mertensKappa x * (muPhiWeightUpTo x N₂ - muPhiWeightUpTo x N₁)
        ≤ (muPhiCorr x)⁻¹ * (Real.log N₂ - Real.log N₁) / Real.log x
          + C * (mertensKappa x * ((#(W x).divisors : ℝ) + PrimeGaps.ellV (W x))) := by
  obtain ⟨C, hC, hasym⟩ := sum_moebiusSq_div_moebiusTotient_coprime
  refine ⟨2 * C, by linarith, fun x hx h2 N₁ N₂ h1 h12 ↦ ?_⟩
  have hW1 : 1 ≤ W x := primorial_pos _
  have hL : 0 < Real.log x := Real.log_pos hx
  have hκ : 0 ≤ mertensKappa x := mertensKappa_nonneg hx.le
  have hWR : (0 : ℝ) < (W x : ℝ) := by exact_mod_cast hW1
  have hphiR : (0 : ℝ) < ((W x).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hW1
  have hkmul : mertensKappa x * (((W x).totient : ℝ) / (W x : ℝ)) = 1 / Real.log x := by
    rw [mertensKappa]; field_simp
  have e1 := (abs_le.mp (hasym (W x) h2 (squarefree_primorial _) N₁ h1)).1
  have e2 := (abs_le.mp (hasym (W x) h2 (squarefree_primorial _) N₂ (h1.trans h12))).2
  calc _ ≤ mertensKappa x * (((W x).totient : ℝ) / (W x : ℝ) * (muPhiCorr x)⁻¹
          * (Real.log N₂ - Real.log N₁)
          + 2 * (C * ((#(W x).divisors : ℝ) + PrimeGaps.ellV (W x)))) := by
        gcongr
        rw [muPhiWeightUpTo, muPhiWeightUpTo, muPhiCorr]
        linarith
    _ = _ := by linear_combination (muPhiCorr x)⁻¹ * (Real.log N₂ - Real.log N₁) * hkmul

/-- **The top block of the `e`-range carries normalized weight `O(log(z+1)/log x)`.** The block is
`e ∈ (B/(z+1), B]` at the truncation `B = ⌊x^β⌋+1` and `z = ⌊log log log x⌋`, written as the
integer condition `B < e(z+1)`. It sits inside `(N₁, B]` with `N₁ = ⌊B/(z+1)⌋`, and the hypothesis
`2(z+1) ≤ B` makes `B ≤ 2(z+1)N₁` and `N₁ ≥ 1`. Folding `log 2 ≤ 1` into the numerator produces the
`log(z+1)+1` of the statement — the same quantity that bounds the defect's *size* there, so the
product of the two is a cube.

The reciprocal kernel's counterpart needs `2(z+1)(W+1) ≤ B`, because its Mertens error carries
`τ(W)/N₁`; this kernel's error is `N`-free, so the hypothesis is weaker. -/
theorem exists_kappa_mul_muPhiTopBlockWeight_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x β D : ℝ, 1 < x → 2 ∣ W x → 0 ≤ D → (muPhiCorr x)⁻¹ ≤ D →
      2 * ((⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1) ≤ ((⌊x ^ β⌋₊ + 1 : ℕ) : ℝ) →
        mertensKappa x * ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e
              ∧ ⌊x ^ β⌋₊ + 1 < e * (⌊Real.log (Real.log (Real.log x))⌋₊ + 1),
            ((μ e : ℝ) ^ 2 / moebiusTotient e)
          ≤ D * (Real.log ((⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1) + 1) / Real.log x
            + C * (mertensKappa x * ((#(W x).divisors : ℝ) + PrimeGaps.ellV (W x))) := by
  obtain ⟨C, hC, hblock⟩ := exists_kappa_mul_muPhiWeightUpTo_sub_le
  refine ⟨C, hC, fun x β D hx h2 hD0 hD hbig ↦ ?_⟩
  set z : ℕ := ⌊Real.log (Real.log (Real.log x))⌋₊
  set B : ℕ := ⌊x ^ β⌋₊ + 1
  set N : ℕ := ⌊(B : ℝ) / ((z : ℝ) + 1)⌋₊ with hNdef
  have hL : 0 < Real.log x := Real.log_pos hx
  have hκ : 0 ≤ mertensKappa x := mertensKappa_nonneg hx.le
  have hz1 : (1 : ℝ) ≤ (z : ℝ) + 1 := le_add_of_nonneg_left z.cast_nonneg
  have hB2 : (2 : ℝ) ≤ (B : ℝ) := by nlinarith
  have hN1 : 1 ≤ N := Nat.le_floor (by push_cast; rw [le_div_iff₀ (by linarith)]; nlinarith)
  have hNB : N ≤ B := Nat.floor_le_of_le (div_le_self (by positivity) hz1)
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hBN : (B : ℝ) ≤ 2 * ((z : ℝ) + 1) * (N : ℝ) := by
    have := Nat.lt_floor_add_one ((B : ℝ) / ((z : ℝ) + 1))
    rw [← hNdef, div_lt_iff₀ (by linarith)] at this
    nlinarith
  have hsub : ({e ∈ Icc 1 B | Nat.Coprime (W x) e ∧ B < e * (z + 1)} : Finset ℕ)
      ⊆ {e ∈ Icc 1 B | Nat.Coprime (W x) e} \ {e ∈ Icc 1 N | Nat.Coprime (W x) e} := by
    intro e he
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc] at he ⊢
    refine ⟨⟨he.1, he.2.1⟩, fun h ↦ he.2.2.not_ge ?_⟩
    have := (Nat.le_floor_iff (by positivity)).1 h.1.2
    rw [le_div_iff₀ (by linarith)] at this
    exact_mod_cast this
  have hwsum : ∑ e ∈ Icc 1 B with Nat.Coprime (W x) e ∧ B < e * (z + 1),
        ((μ e : ℝ) ^ 2 / moebiusTotient e)
      ≤ muPhiWeightUpTo x B - muPhiWeightUpTo x N := by
    rw [muPhiWeightUpTo, muPhiWeightUpTo,
      ← Finset.sum_sdiff_eq_sub (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl hNB))]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun e _ _ ↦ muPhiWeight_term_nonneg e
  have hlogB : Real.log (B : ℝ) - Real.log (N : ℝ) ≤ Real.log ((z : ℝ) + 1) + 1 := by
    have h1 : Real.log (B : ℝ) ≤ Real.log (2 * ((z : ℝ) + 1) * (N : ℝ)) :=
      Real.log_le_log (by linarith) hBN
    rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) (by linarith)]
      at h1
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogNB : 0 ≤ Real.log (B : ℝ) - Real.log (N : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log (by linarith) (by exact_mod_cast hNB))
  calc _ ≤ mertensKappa x * (muPhiWeightUpTo x B - muPhiWeightUpTo x N) := by gcongr
    _ ≤ _ := hblock x hx h2 N B hN1 hNB
    _ ≤ _ := by gcongr

/-! ## The mean square split at the one-term top block -/

/-- **The top block's share of the totient mean square**, at the truncation `B(x) = ⌊x^β⌋+1`: the
`e` with `B < e(z+1)`, `z = ⌊log log log x⌋`, the regime
`Gap212.Sieve.innerTotient_eq_of_lt_primorial_bound` collapses to one term. -/
noncomputable def totientGramTopSum (F : ℝ → ℝ) (x β : ℝ) : ℝ :=
  ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e
      ∧ ⌊x ^ β⌋₊ + 1 < e * (⌊Real.log (Real.log (Real.log x))⌋₊ + 1),
    ((μ e : ℝ) ^ 2 / moebiusTotient e)
      * (innerTotientRatio (W x) e F x (⌊x ^ β⌋₊ + 1) + deriv F (Notation.logx x e)) ^ 2

/-- **The bulk's share**: the complementary range `e(z+1) ≤ B`, where no bound on the defect is
available at all. -/
noncomputable def totientGramBulkSum (F : ℝ → ℝ) (x β : ℝ) : ℝ :=
  ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e
      ∧ ¬ ⌊x ^ β⌋₊ + 1 < e * (⌊Real.log (Real.log (Real.log x))⌋₊ + 1),
    ((μ e : ℝ) ^ 2 / moebiusTotient e)
      * (innerTotientRatio (W x) e F x (⌊x ^ β⌋₊ + 1) + deriv F (Notation.logx x e)) ^ 2

/-- **The two blocks partition the mean square at the cut.** -/
theorem totientGramTopSum_add_totientGramBulkSum (F : ℝ → ℝ) (x β : ℝ) :
    totientGramTopSum F x β + totientGramBulkSum F x β
      = ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / moebiusTotient e)
            * (innerTotientRatio (W x) e F x (⌊x ^ β⌋₊ + 1) + deriv F (Notation.logx x e)) ^ 2 := by
  rw [totientGramTopSum, totientGramBulkSum, ← Finset.filter_filter, ← Finset.filter_filter]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

private theorem rpow_le_floor_add_one (x β : ℝ) : x ^ β ≤ ((⌊x ^ β⌋₊ + 1 : ℕ) : ℝ) := by
  exact_mod_cast (Nat.lt_floor_add_one (x ^ β)).le

/-- **The defect is at most `‖F'‖_∞(log(z+1)+1)` on the squarefree part of the top block.** The
triangle inequality between `Gap212.Sieve.abs_innerTotientRatio_le_log_primorial_bound` and the
uniform bound on `F'`. The squarefreeness hypothesis is this kernel's, carried by
`Gap212.Sieve.abs_innerTotientNorm_le_one`; off the squarefree `e` the weight is `0` and the
summand needs no bound (`Gap212.Sieve.muPhiWeight_mul_sq_le_of_topBlock`). -/
theorem abs_innerTotientDefect_le_of_topBlock {x β M : ℝ} (hx : 1 < x) {e : ℕ} (he : 0 < e)
    (hsf : Squarefree e) (heB : e ≤ ⌊x ^ β⌋₊ + 1)
    (hcond : ⌊x ^ β⌋₊ + 1 < e * (⌊Real.log (Real.log (Real.log x))⌋₊ + 1))
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hM : ∀ t, |deriv F t| ≤ M)
    (hFv : ∀ t, β ≤ t → F t = 0) :
    |innerTotientRatio (W x) e F x (⌊x ^ β⌋₊ + 1) + deriv F (Notation.logx x e)|
      ≤ M * (Real.log ((⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1) + 1) := by
  have hzlt : ((⌊x ^ β⌋₊ + 1 : ℕ) : ℝ) / (e : ℝ)
      < (⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1 := by
    rw [div_lt_iff₀ (by exact_mod_cast he), mul_comm]
    exact_mod_cast hcond
  have h1 := abs_innerTotientRatio_le_log_primorial_bound hx he hsf heB hzlt
    (rpow_le_floor_add_one x β) hF hM hFv
  exact (abs_add_le _ _).trans (by rw [mul_add, mul_one]; linarith [hM (Notation.logx x e)])

/-- **The summand of the top block is at most `(‖F'‖_∞Z)²` times its weight.** On a squarefree `e`
this is `Gap212.Sieve.abs_innerTotientDefect_le_of_topBlock` squared; off the squarefree integers
`μ(e) = 0`, the weight vanishes and both sides are `0`. That case split is what replaces the
reciprocal kernel's unconditional pointwise bound. -/
theorem muPhiWeight_mul_sq_le_of_topBlock {x β M Z : ℝ} (hx : 1 < x) (hM0 : 0 ≤ M) {e : ℕ}
    (he : 0 < e) (heB : e ≤ ⌊x ^ β⌋₊ + 1)
    (hcond : ⌊x ^ β⌋₊ + 1 < e * (⌊Real.log (Real.log (Real.log x))⌋₊ + 1))
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hM : ∀ t, |deriv F t| ≤ M)
    (hFv : ∀ t, β ≤ t → F t = 0)
    (hZ : Real.log ((⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1) + 1 ≤ Z) :
    ((μ e : ℝ) ^ 2 / moebiusTotient e)
        * (innerTotientRatio (W x) e F x (⌊x ^ β⌋₊ + 1) + deriv F (Notation.logx x e)) ^ 2
      ≤ (M * Z) ^ 2 * ((μ e : ℝ) ^ 2 / moebiusTotient e) := by
  by_cases hsf : Squarefree e
  · obtain ⟨hlo, hhi⟩ := abs_le.mp ((abs_innerTotientDefect_le_of_topBlock hx he hsf heB hcond
      hF hM hFv).trans (mul_le_mul_of_nonneg_left hZ hM0))
    rw [mul_comm ((M * Z) ^ 2)]
    exact mul_le_mul_of_nonneg_left (sq_le_sq' hlo hhi) (muPhiWeight_term_nonneg e)
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]

/-- **The top block's contribution: size bound times block weight.** With `Z` any upper bound for
`log(z+1)+1` and `E` the normalized Mertens error, the defect is at most `MZ` on the block and the
block's normalized weight at most `2Z/log x + CE`, so the contribution is at most
`2M²Z³/log x + CM²Z²E`. The cube arises because the same `log(z+1)` appears squared from the size
and once from the weight. -/
theorem kappa_mul_totientGramTopSum_le {x β M C Z E : ℝ} (hx : 1 < x) (hM0 : 0 ≤ M)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hM : ∀ t, |deriv F t| ≤ M)
    (hFv : ∀ t, β ≤ t → F t = 0)
    (hZ : Real.log ((⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1) + 1 ≤ Z)
    (hwt : mertensKappa x * ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e
            ∧ ⌊x ^ β⌋₊ + 1 < e * (⌊Real.log (Real.log (Real.log x))⌋₊ + 1),
          ((μ e : ℝ) ^ 2 / moebiusTotient e)
        ≤ 2 * Z / Real.log x + C * E) :
    mertensKappa x * totientGramTopSum F x β
      ≤ 2 * M ^ 2 * (Z ^ 3 / Real.log x) + C * M ^ 2 * (Z ^ 2 * E) := by
  have hstep : totientGramTopSum F x β
      ≤ (M * Z) ^ 2 * ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e
            ∧ ⌊x ^ β⌋₊ + 1 < e * (⌊Real.log (Real.log (Real.log x))⌋₊ + 1),
          ((μ e : ℝ) ^ 2 / moebiusTotient e) := by
    rw [totientGramTopSum, Finset.mul_sum]
    refine Finset.sum_le_sum fun e he ↦ ?_
    obtain ⟨heI, -, hcond⟩ := Finset.mem_filter.mp he
    exact muPhiWeight_mul_sq_le_of_topBlock hx hM0 (Finset.mem_Icc.mp heI).1
      (Finset.mem_Icc.mp heI).2 hcond hF hM hFv hZ
  linear_combination mul_le_mul_of_nonneg_left hstep (mertensKappa_nonneg hx.le) +
    mul_le_mul_of_nonneg_left hwt (sq_nonneg (M * Z))

/-- **The top block contributes nothing to the totient mean square.** Taking
`Z = log log log x + 1` and `E = κ_x(τ(W(x)) + ℓ_{W(x)})`, the contribution is at most

  `2‖F'‖_∞²(log log log x+1)³/log x + C‖F'‖_∞²(log log log x+1)²·κ_x(τ(W)+ℓ_W)`,

and both terms tend to `0` (`Gap212.Sieve.tendsto_logLogLog_pow_div_log`,
`Gap212.Sieve.tendsto_logLogLog_pow_mul_muPhiErr`). The `2` is the eventual bound on the inverse
correction factor (`Gap212.Sieve.eventually_inv_muPhiCorr_le_two`), which the reciprocal kernel's
counterpart `Gap212.Sieve.tendsto_kappa_mul_gramTopSum` does not carry; the second term is this
kernel's Mertens error, bounded through `W(x) ≤ (log log x)²` and of proved order
`(log log log log x)²(log log x)⁴/log x`. Only the limit is claimed, neither rate.

Nothing here bounds the defect off this block; `Gap212.Sieve.TotientBulkInnerL2` is the mean square
there. -/
theorem tendsto_kappa_mul_totientGramTopSum {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {β : ℝ} (hβ : 0 < β) (hFv : ∀ t, β ≤ t → F t = 0) :
    Tendsto (fun x : ℝ ↦ mertensKappa x * totientGramTopSum F x β) atTop (nhds 0) := by
  obtain ⟨M, hMn⟩ := hFc.deriv.exists_bound_of_continuous hF.continuous_deriv_one
  have hM : ∀ t : ℝ, |deriv F t| ≤ M := fun t ↦ by simpa [Real.norm_eq_abs] using hMn t
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM 0)
  obtain ⟨C, hC, hw⟩ := exists_kappa_mul_muPhiTopBlockWeight_le
  have hmaj : Tendsto (fun x : ℝ ↦
      2 * M ^ 2 * ((Real.log (Real.log (Real.log x)) + 1) ^ 3 / Real.log x)
        + C * M ^ 2 * ((Real.log (Real.log (Real.log x)) + 1) ^ 2 *
          (mertensKappa x * ((#(W x).divisors : ℝ) + PrimeGaps.ellV (W x)))))
      atTop (nhds 0) := by
    simpa using ((tendsto_logLogLog_pow_div_log 3).const_mul (2 * M ^ 2)).add
      ((tendsto_logLogLog_pow_mul_muPhiErr 2).const_mul (C * M ^ 2))
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (mertensKappa_nonneg hx.le)
      (Finset.sum_nonneg fun e _ ↦ mul_nonneg (muPhiWeight_term_nonneg e) (sq_nonneg _))
  · filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_logLogLog_le, eventually_two_dvd_W,
      eventually_inv_muPhiCorr_le_two,
      eventually_two_mul_succ_mul_W_le_gramCut hβ] with x hx hlll h2 hcorr hbig
    have hL : 0 < Real.log x := Real.log_pos hx
    have hznn : (0 : ℝ) ≤ (⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) := Nat.cast_nonneg _
    have hW1 : (1 : ℝ) ≤ (W x : ℝ) := by
      exact_mod_cast primorial_pos (⌊Real.log (Real.log (Real.log x))⌋₊)
    have hbig' : 2 * ((⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1)
        ≤ ((⌊x ^ β⌋₊ + 1 : ℕ) : ℝ) := by nlinarith
    refine kappa_mul_totientGramTopSum_le hx hM0 hF hM hFv (log_floor_add_one_le hlll.1) ?_
    refine (hw x β 2 hx h2 (by norm_num) hcorr hbig').trans ?_
    gcongr 2 * ?_ / _ + _
    linarith [log_floor_add_one_le hlll.1]

/-! ## The mean square at the cut, and the bulk -/

/-- **The totient mean square at the single truncation `B(x) = ⌊x^β⌋+1`.** -/
def TotientNormalizedInnerL2AtCut : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) →
      Tendsto (fun x : ℝ ↦ mertensKappa x *
          ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e,
            ((μ e : ℝ) ^ 2 / moebiusTotient e)
              * (innerTotientRatio (W x) e F x (⌊x ^ β⌋₊ + 1)
                  + deriv F (Notation.logx x e)) ^ 2) atTop (nhds 0)

/-- **The truncation quantifier of the mean square is spurious too.** The same collapse that proves
`Gap212.Sieve.totientGramRatioDefectVanishes_iff_atCut`. -/
theorem totientNormalizedInnerL2_iff_atCut :
    TotientNormalizedInnerL2 ↔ TotientNormalizedInnerL2AtCut := by
  refine ⟨fun h F hF hFc β hβ hFv ↦ h F hF hFc β hβ hFv _
    (.of_forall fun x ↦ rpow_le_floor_add_one x β), fun h F hF hFc β hβ hFv B hB ↦ ?_⟩
  have hdF := deriv_eq_zero_of_eventually_zero hF hFv
  refine (h F hF hFc β hβ hFv).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), hB] with x hx hBx
  have hz : ∀ B' : ℕ, ∀ e : ℕ, ⌊x ^ β⌋₊ < e →
      ((μ e : ℝ) ^ 2 / moebiusTotient e) *
        (innerTotientRatio (W x) e F x B' + deriv F (Notation.logx x e)) ^ 2 = 0 := by
    intro B' e he
    obtain ⟨he0, hle⟩ := rpow_le_of_floor_lt he
    rw [innerTotientRatio_eq_zero_of_rpow_le hx he0 hle hFv, hdF _ (le_logx_of_rpow_le hx hle)]
    simp
  rw [sum_filter_Icc_collapse (Nat.le_succ ⌊x ^ β⌋₊) _ (hz _),
    sum_filter_Icc_collapse (floor_rpow_le_of_le hBx) _ (hz _)]
  refine congrArg _ (Finset.sum_congr rfl fun e he ↦ ?_)
  rw [innerTotientRatio_eq_of_rpow_le hx (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
    (rpow_le_floor_add_one x β) hBx hFv]

/-- **The totient mean square over the bulk of the `e`-range**, `e` with `e(z+1) ≤ B`,
`z = ⌊log log log x⌋`, `B(x) = ⌊x^β⌋+1` — the `e` whose inner sum has more than one term.

The *sum* is strictly smaller. The *statement* is not: it is logically equivalent to
`Gap212.Sieve.TotientNormalizedInnerL2` (`Gap212.Sieve.totientBulkInnerL2_iff`), the dropped
summands being nonnegative with vanishing normalized sum. **The split removes summands, not work**,
and the same was true of the reciprocal kernel's
(`Gap212.Sieve.bulkInnerRecipL2_iff`).

**No bound on `|a_F(e)|` is proved on the bulk, of any size.** What the split buys is that the one
regime where the pointwise asymptotic is *refuted* — the one-term top, where
`Gap212.Sieve.innerTotient_eq_of_lt_primorial_bound` leaves nothing to cancel — is outside this
statement. -/
def TotientBulkInnerL2 : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) →
      Tendsto (fun x : ℝ ↦ mertensKappa x * totientGramBulkSum F x β) atTop (nhds 0)

/-- **The bulk alone implies the full mean square.** -/
theorem totientNormalizedInnerL2_of_totientBulkInnerL2 (h : TotientBulkInnerL2) :
    TotientNormalizedInnerL2 := by
  rw [totientNormalizedInnerL2_iff_atCut]
  intro F hF hFc β hβ hFv
  have hsum := (tendsto_kappa_mul_totientGramTopSum hF hFc hβ hFv).add (h F hF hFc β hβ hFv)
  rw [add_zero] at hsum
  exact hsum.congr fun x ↦ by rw [← mul_add, totientGramTopSum_add_totientGramBulkSum]

/-- **The bulk mean square is equivalent to the full mean square.** -/
theorem totientBulkInnerL2_iff : TotientBulkInnerL2 ↔ TotientNormalizedInnerL2 := by
  refine ⟨totientNormalizedInnerL2_of_totientBulkInnerL2, fun h F hF hFc β hβ hFv ↦ ?_⟩
  have hsub := ((totientNormalizedInnerL2_iff_atCut.mp h) F hF hFc β hβ hFv).sub
    (tendsto_kappa_mul_totientGramTopSum hF hFc hβ hFv)
  rw [sub_zero] at hsub
  refine hsub.congr fun x ↦ ?_
  rw [← totientGramTopSum_add_totientGramBulkSum F x β]
  ring

/-- **The totient Gram-sum limit from the bulk mean square.** The composite:
`Gap212.Sieve.TotientGramSumLimitOfSupport` from `Gap212.Sieve.TotientBulkInnerL2` alone.

The Gram-sum limit is stated for `ContDiff ℝ (⊤ : ℕ∞)` profiles and this input for `ContDiff ℝ 1`
ones; the `of_le` passing between them is in
`Gap212.Sieve.totientGramRatioDefectVanishes_of_totientNormalizedInnerRatioL1`. -/
theorem totientGramSumLimitOfSupport_of_totientBulkInnerL2 (h : TotientBulkInnerL2) :
    TotientGramSumLimitOfSupport :=
  totientGramSumLimitOfSupport_of_totientNormalizedInnerL2
    (totientNormalizedInnerL2_of_totientBulkInnerL2 h)

end Gap212.Sieve
