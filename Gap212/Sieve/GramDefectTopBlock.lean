/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.GramDefectMeanSquare

/-!
# The reciprocal mean square split at the one-term top block

`Gap212.Sieve.GramDefectMeanSquare` derives the reciprocal Gram-sum limit
`Gap212.Sieve.LcmGramSumLimitOfSupport` from the one-profile mean square
`Gap212.Sieve.NormalizedInnerRecipL2`,

  `κ_x·∑_{e≤B,(e,W)=1}(μ²(e)/φ(e))·a_F(e)² ⟶ 0`,  `a_F(e) = r_F(e) + F'(log_xe)`,

and bounds the size of `a_F` at the top of the `e`-range, `e ∈ (B/(z+1),B]` with
`z = ⌊log log log x⌋`, where the inner sum has a single term
(`Gap212.Sieve.innerRecip_eq_of_lt_primorial_bound`,
`Gap212.Sieve.abs_innerRecipRatio_le_log_primorial_bound`) and the pointwise limit
`r_F(e) → -F'(log_xe)` fails. This file bounds the weight of that block and shows that its
contribution to the mean square tends to `0`.

## The top block

The truncation is fixed at `B(x) = ⌊x^β⌋+1` (`Gap212.Sieve.normalizedInnerRecipL2_iff_atCut`). There
the block is the integer condition `B < e(z+1)`, and it sits inside `(N,B]` with `N = ⌊B/(z+1)⌋`.
Two readings of the Mertens asymptotic `Gap212.Sieve.sum_moebiusSq_div_totient_coprime`, at `N` and
at `B`, cancel its `W`-dependent constants `γ + ℓ_W` and leave
(`Gap212.Sieve.exists_kappa_mul_weightUpTo_sub_le`,
`Gap212.Sieve.exists_kappa_mul_topBlockWeight_le`)

  `κ_x·∑_{block}μ²(e)/φ(e) ≤ log(B/N)/log x + O(κ_x) ≤ (log(z+1) + 1)/log x + O(κ_x)`,

since `B ≤ 2(z+1)N` and `log 2 ≤ 1`. Multiplied by the size bound
`|a_F(e)| ≤ ‖F'‖_∞(log(z+1)+1)` this gives (`Gap212.Sieve.kappa_mul_gramTopSum_le`)

  `κ_x·∑_{block}(μ²(e)/φ(e))·a_F(e)² ≤ ‖F'‖_∞²(log(z+1)+1)³/log x + O((log(z+1)+1)²·κ_x)`,

and both terms vanish (`Gap212.Sieve.tendsto_kappa_mul_gramTopSum`): `log(z+1)+1 ≤ log log log x+1`
(`Gap212.Sieve.log_floor_add_one_le`), while `(log log log x+1)³ = o(log x)` and
`κ_x ≤ 1/log log x` (`Gap212.Sieve.mertensKappa_le_inv_log_log`, from
`Gap212.Sieve.W_le_log_div_log_log`). With this bound on `κ_x` the second term is the larger, of
order `(log log log log x)²/log log x`.

## The bulk

`Gap212.Sieve.BulkInnerRecipL2` is the same mean square with the sum restricted to `e ≤ B/(z+1)`.
It implies the Gram-sum limit (`Gap212.Sieve.lcmGramSumLimitOfSupport_of_bulkInnerRecipL2`), and,
since the removed summands are nonnegative with vanishing normalized sum, it is equivalent to
`Gap212.Sieve.NormalizedInnerRecipL2` (`Gap212.Sieve.bulkInnerRecipL2_iff`). The Gram-sum limit
itself follows from `Gap212.Sieve.polymath41Recip` by
`Gap212.Sieve.lcmGramSumLimitOfSupport_iff_polymath41Recip`.

## The kernel

Reciprocal throughout: weight `μ²(e)/φ(e)`, Mertens prefactor `φ(W)/W`, normalization
`κ_x = (W/φ(W))/log x`. No `(∏_{p∤W}(1-1/(p-1)²))^{-1}` correction appears, and no oddness or
`2 ∣ W` hypothesis is used. Those belong to the totient kernel (`Gap212.Sieve.TotientGramMeasure`),
whose weight is `μ²/(μ*φ)`, whose local factor at `p ∤ W` is not `1`, and for which
`(μ*φ)(2) = 0`.

## Main definitions

* `Gap212.Sieve.mertensWeightUpTo`: the `μ²/φ` weight over the coprimality class below a general
  `N`, of which `Gap212.Sieve.mertensWeightCut` is the value at `N = ⌊x^s⌋`.
* `Gap212.Sieve.gramTopSum`, `Gap212.Sieve.gramBulkSum`: the two halves of the mean square at the
  cut.
* `Gap212.Sieve.NormalizedInnerRecipL2AtCut`: the mean square at `B(x) = ⌊x^β⌋+1`.
* `Gap212.Sieve.BulkInnerRecipL2`: the mean square over the bulk `e ≤ B/(z+1)` of the `e`-range.

## Main results

* `Gap212.Sieve.exists_kappa_mul_weightUpTo_sub_le`: the normalized weight of a block `(N₁,N₂]`.
* `Gap212.Sieve.exists_kappa_mul_topBlockWeight_le`: the normalized weight of the top block.
* `Gap212.Sieve.tendsto_kappa_mul_gramTopSum`: the top block's contribution tends to `0`.
* `Gap212.Sieve.normalizedInnerRecipL2_iff_atCut`: the mean square at one truncation.
* `Gap212.Sieve.bulkInnerRecipL2_iff`,
  `Gap212.Sieve.lcmGramSumLimitOfSupport_of_bulkInnerRecipL2`: the bulk mean square is equivalent
  to the whole, and implies the Gram-sum limit.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY
open scoped ArithmeticFunction.Moebius

/-! ## Two analytic facts about iterated logarithms -/

/-- **`(log t + 1)^n = o(t)`.** Substituting `t = e^s` turns this into
`(s+1)^n e^{-s} → 0`, which is `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero` after a shift. -/
theorem tendsto_pow_log_add_one_div (n : ℕ) :
    Tendsto (fun t : ℝ ↦ (Real.log t + 1) ^ n / t) atTop (nhds 0) := by
  have hg : Tendsto (fun s : ℝ ↦ (s + 1) ^ n * Real.exp (-(s + 1))) atTop (nhds 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_id)
  have hg2 : Tendsto (fun s : ℝ ↦ (s + 1) ^ n * Real.exp (-s)) atTop (nhds 0) := by
    refine (mul_zero (Real.exp 1) ▸ hg.const_mul (Real.exp 1)).congr fun s ↦ ?_
    rw [neg_add, Real.exp_add, Real.exp_neg 1]
    field_simp
  refine (hg2.comp Real.tendsto_log_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Function.comp_apply, Real.exp_neg, Real.exp_log ht, div_eq_mul_inv]

/-- **`κ_x ≤ 1/log log x`.** The rate behind `Gap212.Sieve.tendsto_mertensKappa`, extracted:
`W/φ(W) ≤ W ≤ log x/log log x` (`Gap212.Sieve.W_le_log_div_log_log`). -/
theorem mertensKappa_le_inv_log_log :
    ∀ᶠ x : ℝ in atTop, mertensKappa x ≤ 1 / Real.log (Real.log x) := by
  have hll : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [W_le_log_div_log_log, hll.eventually_gt_atTop 0,
    eventually_gt_atTop (1 : ℝ)] with x hW hu hx1
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hphi : (1 : ℝ) ≤ ((W x).totient : ℝ) := mod_cast Nat.totient_pos.mpr (primorial_pos _)
  have h3 : Real.log x / Real.log (Real.log x) / Real.log x = 1 / Real.log (Real.log x) := by
    rw [div_right_comm, div_self (ne_of_gt hL)]
  rw [show mertensKappa x = (W x : ℝ) / ((W x).totient : ℝ) / Real.log x from rfl, ← h3,
    div_le_div_iff_of_pos_right hL]
  exact (div_le_self (Nat.cast_nonneg _) hphi).trans hW

/-! ## The `μ²/φ` weight over an arbitrary initial segment -/

/-- **The `μ²/φ` weight summed over the coprimality class below `N`.**
`Gap212.Sieve.mertensWeightCut` is its value at `N = ⌊x^s⌋`; the split of the mean square is at a
cutoff that is not a power of `x`, so the counting function is needed at a general `N`. -/
noncomputable def mertensWeightUpTo (x : ℝ) (N : ℕ) : ℝ :=
  ∑ e ∈ Icc 1 N with Nat.Coprime (W x) e, ((μ e : ℝ) ^ 2 / (e.totient : ℝ))

/-- `mertensWeightCut x s` is `mertensWeightUpTo x N` at `N = ⌊x ^ s⌋₊`. -/
theorem mertensWeightCut_eq_upTo (x s : ℝ) :
    mertensWeightCut x s = mertensWeightUpTo x ⌊x ^ s⌋₊ := rfl

/-- **The normalized weight of a block `(N₁,N₂]`, from the Mertens asymptotic at both ends.**
Subtracting the asymptotic at `N₁` from the one at `N₂` cancels the two `W`-dependent constants
`γ + ℓ_W` exactly, and `κ_x·(φ(W)/W) = 1/log x`, so the main term is `log(N₂/N₁)/log x` with an
error that is `κ_x` times the two `O(1 + τ(W)/N)`'s. The divisor count is bounded by `W` itself.

This is the reciprocal kernel's weight `μ²(e)/φ(e)` with the reciprocal kernel's prefactor
`φ(W)/W` — no `∏_{p∤W}(1-1/(p-1)²)` correction, which belongs to the totient kernel. -/
theorem exists_kappa_mul_weightUpTo_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 < x → ∀ N₁ N₂ : ℕ, 1 ≤ N₁ → N₁ ≤ N₂ →
      mertensKappa x * (mertensWeightUpTo x N₂ - mertensWeightUpTo x N₁)
        ≤ (Real.log N₂ - Real.log N₁) / Real.log x
          + C * mertensKappa x * (1 + (W x : ℝ) / (N₁ : ℝ)) := by
  obtain ⟨C, hC, hasym⟩ := sum_moebiusSq_div_totient_coprime
  refine ⟨2 * C, by linarith, fun x hx N₁ N₂ h1 h12 ↦ ?_⟩
  have hW1 : 1 ≤ W x := primorial_pos _
  have hWsf : Squarefree (W x) := squarefree_primorial _
  have hκ : 0 ≤ mertensKappa x := mertensKappa_nonneg hx.le
  have hkmul : mertensKappa x * (((W x).totient : ℝ) / (W x : ℝ)) = 1 / Real.log x := by
    rw [mertensKappa]; field_simp
  have hN1R : (1 : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast h1
  have hN12R : (N₁ : ℝ) ≤ (N₂ : ℝ) := by exact_mod_cast h12
  have htau : ((#(W x).divisors : ℕ) : ℝ) ≤ (W x : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self (W x)
  have e1 := (abs_le.1 (hasym (W x) hW1 hWsf N₁ h1)).1
  have e2 := (abs_le.1 (hasym (W x) hW1 hWsf N₂ (h1.trans h12))).2
  have hb : C * (1 + ((#(W x).divisors : ℕ) : ℝ) / (N₂ : ℝ))
      ≤ C * (1 + (W x : ℝ) / (N₁ : ℝ)) := by gcongr
  have hb' : C * (1 + ((#(W x).divisors : ℕ) : ℝ) / (N₁ : ℝ))
      ≤ C * (1 + (W x : ℝ) / (N₁ : ℝ)) := by gcongr
  calc _ ≤ mertensKappa x * (((W x).totient : ℝ) / (W x : ℝ) * (Real.log N₂ - Real.log N₁)
          + 2 * (C * (1 + (W x : ℝ) / (N₁ : ℝ)))) := by
        gcongr
        rw [mertensWeightUpTo, mertensWeightUpTo]
        linarith
    _ = _ := by rw [mul_add, ← mul_assoc, hkmul]; ring

/-! ## The normalized weight of the one-term top block -/

/-- **The top block of the `e`-range carries normalized weight `O(log(z+1)/log x)`.**
The block is `e ∈ (B/(z+1), B]` at the single truncation `B = ⌊x^β⌋+1` and `z = ⌊log log log x⌋`,
written as the integer condition `B < e(z+1)`. It sits inside `(N₁, B]` with
`N₁ = ⌊B/(z+1)⌋`, and the hypothesis `2(z+1)(W+1) ≤ B` — which holds for all large `x`, by
`Gap212.Sieve.eventually_two_mul_succ_mul_W_le_gramCut` — makes `B ≤ 2(z+1)N₁` and `W ≤ N₁`, so
`Gap212.Sieve.exists_kappa_mul_weightUpTo_sub_le` gives

  `κ_x·∑_{block}μ²(e)/φ(e) ≤ (log 2 + log(z+1))/log x + 2C·κ_x`.

Folding `log 2 ≤ 1` into the numerator is what produces the `(log(z+1)+1)` of the statement: the
same quantity that bounds the defect's *size* there, so the product of the two is a cube. -/
theorem exists_kappa_mul_topBlockWeight_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x β : ℝ, 1 < x →
      2 * ((⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1) * ((W x : ℝ) + 1)
          ≤ ((⌊x ^ β⌋₊ + 1 : ℕ) : ℝ) →
        mertensKappa x * ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e
              ∧ ⌊x ^ β⌋₊ + 1 < e * (⌊Real.log (Real.log (Real.log x))⌋₊ + 1),
            ((μ e : ℝ) ^ 2 / (e.totient : ℝ))
          ≤ (Real.log ((⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1) + 1) / Real.log x
            + C * mertensKappa x := by
  obtain ⟨C, hC, hblock⟩ := exists_kappa_mul_weightUpTo_sub_le
  refine ⟨2 * C, by linarith, fun x β hx hbig ↦ ?_⟩
  set z : ℕ := ⌊Real.log (Real.log (Real.log x))⌋₊
  set B : ℕ := ⌊x ^ β⌋₊ + 1
  set N : ℕ := ⌊(B : ℝ) / ((z : ℝ) + 1)⌋₊
  have hL : 0 < Real.log x := Real.log_pos hx
  have hκ : 0 ≤ mertensKappa x := mertensKappa_nonneg hx.le
  have hz1 : (1 : ℝ) ≤ (z : ℝ) + 1 := le_add_of_nonneg_left z.cast_nonneg
  have hW1 : (1 : ℝ) ≤ (W x : ℝ) := mod_cast primorial_pos _
  -- the three consequences of `2(z+1)(W+1) ≤ B`
  have hB2z : 2 * ((z : ℝ) + 1) ≤ (B : ℝ) := by nlinarith
  have hqlo : 2 * ((W x : ℝ) + 1) ≤ (B : ℝ) / ((z : ℝ) + 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hN1 : 1 ≤ N := Nat.le_floor (by push_cast; linarith)
  have hWN : (W x : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr (Nat.le_floor (by linarith))
  have hNB : N ≤ B := Nat.floor_le_of_le (div_le_self (Nat.cast_nonneg _) hz1)
  have hBN : (B : ℝ) ≤ 2 * ((z : ℝ) + 1) * (N : ℝ) := by
    have := Nat.lt_floor_add_one ((B : ℝ) / ((z : ℝ) + 1))
    rw [div_lt_iff₀ (by linarith)] at this
    linarith
  -- the block sits inside `(N, B]`
  have hsub : ({e ∈ Icc 1 B | Nat.Coprime (W x) e ∧ B < e * (z + 1)} : Finset ℕ)
      ⊆ {e ∈ Icc 1 B | Nat.Coprime (W x) e} \ {e ∈ Icc 1 N | Nat.Coprime (W x) e} := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc] at he ⊢
    refine ⟨⟨he.1, he.2.1⟩, fun h ↦ he.2.2.not_ge ?_⟩
    exact_mod_cast (le_div_iff₀ (by positivity)).1 ((Nat.le_floor_iff (by positivity)).1 h.1.2)
  -- the Mertens block bound, with the two logarithms compared
  have hlogB : Real.log (B : ℝ) - Real.log (N : ℝ)
      ≤ Real.log ((z : ℝ) + 1) + 1 := by
    have h1 := Real.log_le_log (by linarith) hBN
    rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) (by linarith)]
      at h1
    linarith [Real.log_two_lt_d9]
  have hkw : C * mertensKappa x * (1 + (W x : ℝ) / (N : ℝ)) ≤ 2 * C * mertensKappa x := by
    nlinarith [mul_nonneg hC.le hκ, div_le_one_of_le₀ hWN (by linarith : (0 : ℝ) ≤ N)]
  calc _ ≤ mertensKappa x * (mertensWeightUpTo x B - mertensWeightUpTo x N) := by
        gcongr
        rw [mertensWeightUpTo, mertensWeightUpTo, ← Finset.sum_sdiff_eq_sub
          (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hNB))]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun e _ _ ↦ by positivity
    _ ≤ _ := hblock x hx N B hN1 hNB
    _ ≤ _ := by linarith [(div_le_div_iff_of_pos_right hL).2 hlogB]

/-- **The iterated logarithms are nonnegative and decreasing**, twice `log y ≤ y - 1`. -/
theorem eventually_logLogLog_le :
    ∀ᶠ x : ℝ in atTop, 0 ≤ Real.log (Real.log (Real.log x))
      ∧ Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log x)
      ∧ Real.log (Real.log x) ≤ Real.log x := by
  have hll : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hll.eventually_ge_atTop 1, eventually_gt_atTop (1 : ℝ)] with x hu hx1
  have h₁ := Real.log_le_sub_one_of_pos (Real.log_pos hx1)
  have h₂ := Real.log_le_sub_one_of_pos (show 0 < Real.log (Real.log x) by linarith)
  exact ⟨Real.log_nonneg hu, by linarith, by linarith⟩

/-- **The hypothesis of `Gap212.Sieve.exists_kappa_mul_topBlockWeight_le` holds eventually.**
Both `z + 1 = ⌊log log log x⌋ + 1` and `W(x) + 1` are at most `log x + 1`
(`Gap212.Sieve.W_le_log`), so the left side is at most `2(log x + 1)²`, while the cut is at least
`x^β`; and `log x = o(x^{β/2})`. -/
theorem eventually_two_mul_succ_mul_W_le_gramCut {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ x : ℝ in atTop,
      2 * ((⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1) * ((W x : ℝ) + 1)
        ≤ ((⌊x ^ β⌋₊ + 1 : ℕ) : ℝ) := by
  have hs : 0 < β / 2 := by linarith
  have hinv : Tendsto (fun x : ℝ ↦ 1 / x ^ (β / 2)) atTop (nhds 0) := by
    refine (tendsto_rpow_atTop hs).inv_tendsto_atTop.congr fun x ↦ ?_
    rw [Pi.inv_apply, one_div]
  have hquot : Tendsto (fun x : ℝ ↦ (Real.log x + 1) / x ^ (β / 2)) atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero.add hinv
    rw [add_zero] at h
    exact h.congr fun x ↦ by ring
  filter_upwards [eventually_logLogLog_le, W_le_log, eventually_gt_atTop (1 : ℝ),
    hquot.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with x hlll hWlog hx1 hq
  obtain ⟨hlll0, hlll2, hlll3⟩ := hlll
  have hx0 : (0 : ℝ) < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hxs : (0 : ℝ) < x ^ (β / 2) := Real.rpow_pos_of_pos hx0 _
  have hsq : x ^ (β / 2) * x ^ (β / 2) = x ^ β := by
    rw [← Real.rpow_add hx0]; norm_num
  have hlt : Real.log x + 1 < x ^ (β / 2) / 2 := by
    rw [div_lt_iff₀ hxs] at hq; linarith
  have hfl : (⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) ≤ Real.log x :=
    (Nat.floor_le hlll0).trans (hlll2.trans hlll3)
  calc _ ≤ 2 * (Real.log x + 1) * (Real.log x + 1) := by gcongr
    _ ≤ x ^ β := by nlinarith
    _ ≤ _ := mod_cast (Nat.lt_floor_add_one (x ^ β)).le

/-! ## Two decay rates -/

/-- **`(log log log x + 1)^n = o(log x)`.** With `u = log x` this is
`(log log u + 1)^n = o(u)`, weakened to `(log u + 1)^n = o(u)`
(`Gap212.Sieve.tendsto_pow_log_add_one_div`). -/
theorem tendsto_logLogLog_pow_div_log (n : ℕ) :
    Tendsto (fun x : ℝ ↦ (Real.log (Real.log (Real.log x)) + 1) ^ n / Real.log x)
      atTop (nhds 0) := by
  have hcomp : Tendsto (fun x : ℝ ↦ (Real.log (Real.log x) + 1) ^ n / Real.log x)
      atTop (nhds 0) := (tendsto_pow_log_add_one_div n).comp Real.tendsto_log_atTop
  refine squeeze_zero' ?_ ?_ hcomp <;>
    filter_upwards [eventually_logLogLog_le, eventually_gt_atTop (1 : ℝ)] with x hlll hx <;>
    have := Real.log_pos hx <;>
    have : (0 : ℝ) ≤ Real.log (Real.log (Real.log x)) + 1 := by linarith [hlll.1]
  · positivity
  · gcongr ?_ ^ _ / _; linarith [hlll.2.1]

/-- **`(log log log x + 1)^n·κ_x → 0`.** Here `κ_x ≤ 1/log log x`
(`Gap212.Sieve.mertensKappa_le_inv_log_log`) and, with `v = log log x`, the quotient is exactly
`(log v + 1)^n/v`. This is what makes the top block's Mertens error term vanish. -/
theorem tendsto_logLogLog_pow_mul_mertensKappa (n : ℕ) :
    Tendsto (fun x : ℝ ↦ (Real.log (Real.log (Real.log x)) + 1) ^ n * mertensKappa x)
      atTop (nhds 0) := by
  have hll : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hcomp : Tendsto (fun x : ℝ ↦
      (Real.log (Real.log (Real.log x)) + 1) ^ n / Real.log (Real.log x)) atTop (nhds 0) :=
    (tendsto_pow_log_add_one_div n).comp hll
  refine squeeze_zero' ?_ ?_ hcomp
  · filter_upwards [eventually_logLogLog_le, eventually_gt_atTop (1 : ℝ)] with x hlll hx1
    have h0 : (0 : ℝ) ≤ Real.log (Real.log (Real.log x)) + 1 := by linarith [hlll.1]
    have hκ : 0 ≤ mertensKappa x := mertensKappa_nonneg hx1.le
    positivity
  · filter_upwards [eventually_logLogLog_le, mertensKappa_le_inv_log_log,
      hll.eventually_gt_atTop 0] with x hlll hκle hv
    have h0 : (0 : ℝ) ≤ Real.log (Real.log (Real.log x)) + 1 := by linarith [hlll.1]
    rw [← mul_one_div]
    gcongr

/-! ## The mean square split at the one-term top block -/

/-- **The top block's share of the mean square**, at the single truncation `B(x) = ⌊x^β⌋+1`: the
`e` with `B < e·(z+1)`, `z = ⌊log log log x⌋`, which is the regime
`Gap212.Sieve.innerRecip_eq_of_lt_primorial_bound` collapses to one term. -/
noncomputable def gramTopSum (F : ℝ → ℝ) (x β : ℝ) : ℝ :=
  ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e
      ∧ ⌊x ^ β⌋₊ + 1 < e * (⌊Real.log (Real.log (Real.log x))⌋₊ + 1),
    ((μ e : ℝ) ^ 2 / (e.totient : ℝ))
      * (innerRecipRatio (W x) e F x (⌊x ^ β⌋₊ + 1) + deriv F (Notation.logx x e)) ^ 2

/-- **The bulk's share of the mean square**: the complementary range `e·(z+1) ≤ B`, i.e.
`e ≤ B/(z+1)`. -/
noncomputable def gramBulkSum (F : ℝ → ℝ) (x β : ℝ) : ℝ :=
  ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e
      ∧ ¬ ⌊x ^ β⌋₊ + 1 < e * (⌊Real.log (Real.log (Real.log x))⌋₊ + 1),
    ((μ e : ℝ) ^ 2 / (e.totient : ℝ))
      * (innerRecipRatio (W x) e F x (⌊x ^ β⌋₊ + 1) + deriv F (Notation.logx x e)) ^ 2

/-- **The two blocks partition the mean square at the cut.** -/
theorem gramTopSum_add_gramBulkSum (F : ℝ → ℝ) (x β : ℝ) :
    gramTopSum F x β + gramBulkSum F x β
      = ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / (e.totient : ℝ))
            * (innerRecipRatio (W x) e F x (⌊x ^ β⌋₊ + 1) + deriv F (Notation.logx x e)) ^ 2 := by
  rw [gramTopSum, gramBulkSum, ← Finset.filter_filter, ← Finset.filter_filter]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- **The defect is at most `‖F'‖_∞(log(z+1)+1)` on the top block.** The triangle inequality
between `Gap212.Sieve.abs_innerRecipRatio_le_log_primorial_bound` and the uniform bound on `F'`. -/
theorem abs_innerRecipDefect_le_of_topBlock {x β M : ℝ} (hx : 1 < x) {e : ℕ} (he : 0 < e)
    (heB : e ≤ ⌊x ^ β⌋₊ + 1)
    (hcond : ⌊x ^ β⌋₊ + 1 < e * (⌊Real.log (Real.log (Real.log x))⌋₊ + 1))
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hM : ∀ t, |deriv F t| ≤ M)
    (hFv : ∀ t, β ≤ t → F t = 0) :
    |innerRecipRatio (W x) e F x (⌊x ^ β⌋₊ + 1) + deriv F (Notation.logx x e)|
      ≤ M * (Real.log ((⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1) + 1) := by
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hcut : x ^ β ≤ ((⌊x ^ β⌋₊ + 1 : ℕ) : ℝ) := mod_cast (Nat.lt_floor_add_one (x ^ β)).le
  have hzlt : ((⌊x ^ β⌋₊ + 1 : ℕ) : ℝ) / (e : ℝ)
      < (⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1 := by
    rw [div_lt_iff₀ heR, mul_comm]
    exact_mod_cast hcond
  linarith [abs_add_le (innerRecipRatio (W x) e F x (⌊x ^ β⌋₊ + 1)) (deriv F (Notation.logx x e)),
    abs_innerRecipRatio_le_log_primorial_bound hx he heB hzlt hcut hF hM hFv,
    hM (Notation.logx x e)]

/-- **`log(⌊y⌋+1) + 1 ≤ y + 1`** for `y ≥ 0`, since `log(⌊y⌋+1) ≤ ⌊y⌋ ≤ y`. This is what makes
`log(z+1)`, `z = ⌊log log log x⌋`, at most `log log log x`. -/
theorem log_floor_add_one_le {y : ℝ} (hy : 0 ≤ y) :
    Real.log ((⌊y⌋₊ : ℝ) + 1) + 1 ≤ y + 1 := by
  linarith [Nat.floor_le hy, Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < ⌊y⌋₊ + 1)]

/-- **The top block's contribution: size bound times block weight.** With `Z` any upper bound for
`log(z+1)+1`, the defect is at most `M·Z` pointwise on the block and the block's normalized weight
at most `Z/log x + C·κ_x`, so the contribution is at most `M²Z³/log x + C·M²·Z²κ_x`. -/
theorem kappa_mul_gramTopSum_le {x β M C Z : ℝ} (hx : 1 < x) (hM0 : 0 ≤ M)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hM : ∀ t, |deriv F t| ≤ M)
    (hFv : ∀ t, β ≤ t → F t = 0)
    (hZ : Real.log ((⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1) + 1 ≤ Z)
    (hwt : mertensKappa x * ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e
            ∧ ⌊x ^ β⌋₊ + 1 < e * (⌊Real.log (Real.log (Real.log x))⌋₊ + 1),
          ((μ e : ℝ) ^ 2 / (e.totient : ℝ))
        ≤ Z / Real.log x + C * mertensKappa x) :
    mertensKappa x * gramTopSum F x β
      ≤ M ^ 2 * (Z ^ 3 / Real.log x) + C * M ^ 2 * (Z ^ 2 * mertensKappa x) := by
  have hstep : gramTopSum F x β
      ≤ (M * Z) ^ 2 * ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e
            ∧ ⌊x ^ β⌋₊ + 1 < e * (⌊Real.log (Real.log (Real.log x))⌋₊ + 1),
          ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) := by
    rw [gramTopSum, Finset.mul_sum]
    refine Finset.sum_le_sum fun e he ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at he
    obtain ⟨⟨he1, heB⟩, -, hcond⟩ := he
    obtain ⟨hlo, hhi⟩ := abs_le.mp ((abs_innerRecipDefect_le_of_topBlock hx he1 heB hcond hF hM
      hFv).trans (mul_le_mul_of_nonneg_left hZ hM0))
    rw [mul_comm ((M * Z) ^ 2)]
    exact mul_le_mul_of_nonneg_left (sq_le_sq' hlo hhi) (by positivity)
  refine (mul_le_mul_of_nonneg_left hstep (mertensKappa_nonneg hx.le)).trans ?_
  rw [mul_left_comm (mertensKappa x)]
  refine (mul_le_mul_of_nonneg_left hwt (sq_nonneg _)).trans_eq ?_
  ring

/-- **The top block's contribution to the mean square tends to `0`.** Taking
`Z = log log log x + 1` in
`Gap212.Sieve.kappa_mul_gramTopSum_le`, the contribution is at most

  `‖F'‖_∞²·(log log log x + 1)³/log x + C‖F'‖_∞²·(log log log x + 1)²·κ_x`,

and both terms tend to `0` (`Gap212.Sieve.tendsto_logLogLog_pow_div_log`,
`Gap212.Sieve.tendsto_logLogLog_pow_mul_mertensKappa`). -/
theorem tendsto_kappa_mul_gramTopSum {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {β : ℝ} (hβ : 0 < β) (hFv : ∀ t, β ≤ t → F t = 0) :
    Tendsto (fun x : ℝ ↦ mertensKappa x * gramTopSum F x β) atTop (nhds 0) := by
  obtain ⟨M, hMn⟩ := hFc.deriv.exists_bound_of_continuous hF.continuous_deriv_one
  have hM : ∀ t : ℝ, |deriv F t| ≤ M := fun t ↦ by simpa using hMn t
  obtain ⟨C, hC, hw⟩ := exists_kappa_mul_topBlockWeight_le
  have hmaj : Tendsto (fun x : ℝ ↦
      M ^ 2 * ((Real.log (Real.log (Real.log x)) + 1) ^ 3 / Real.log x)
        + C * M ^ 2 * ((Real.log (Real.log (Real.log x)) + 1) ^ 2 * mertensKappa x))
      atTop (nhds 0) := by
    simpa using ((tendsto_logLogLog_pow_div_log 3).const_mul (M ^ 2)).add
      ((tendsto_logLogLog_pow_mul_mertensKappa 2).const_mul (C * M ^ 2))
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (mertensKappa_nonneg hx.le) (Finset.sum_nonneg fun e _ ↦ by positivity)
  · filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_logLogLog_le,
      eventually_two_mul_succ_mul_W_le_gramCut hβ] with x hx hlll hbig
    refine kappa_mul_gramTopSum_le hx ((abs_nonneg _).trans (hM 0)) hF hM hFv
      (log_floor_add_one_le hlll.1) ((hw x β hx hbig).trans ?_)
    linarith [(div_le_div_iff_of_pos_right (Real.log_pos hx)).mpr (log_floor_add_one_le hlll.1)]

/-! ## The mean square at the cut, and the bulk -/

/-- **The one-profile mean square at the single truncation `B(x) = ⌊x^β⌋+1`.** -/
def NormalizedInnerRecipL2AtCut : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) →
      Tendsto (fun x : ℝ ↦ mertensKappa x *
          ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e,
            ((μ e : ℝ) ^ 2 / (e.totient : ℝ))
              * (innerRecipRatio (W x) e F x (⌊x ^ β⌋₊ + 1)
                  + deriv F (Notation.logx x e)) ^ 2) atTop (nhds 0)

/-- **The mean square at one truncation.** `Gap212.Sieve.NormalizedInnerRecipL2` is equivalent to
`Gap212.Sieve.NormalizedInnerRecipL2AtCut`, by the collapse behind
`Gap212.Sieve.gramRatioDefectVanishes_iff_atCut`: the defect `a_F(e)` vanishes for `e > ⌊x^β⌋` and
does not depend on `B` below that. -/
theorem normalizedInnerRecipL2_iff_atCut :
    NormalizedInnerRecipL2 ↔ NormalizedInnerRecipL2AtCut := by
  refine ⟨fun h F hF hFc β hβ hFv ↦
    h F hF hFc β hβ hFv _ (.of_forall fun x ↦ mod_cast (Nat.lt_floor_add_one (x ^ β)).le),
    fun h F hF hFc β hβ hFv B hB ↦ ?_⟩
  have hdF := deriv_eq_zero_of_eventually_zero hF hFv
  refine (h F hF hFc β hβ hFv).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), hB] with x hx hBx
  have hcut : x ^ β ≤ ((⌊x ^ β⌋₊ + 1 : ℕ) : ℝ) := mod_cast (Nat.lt_floor_add_one (x ^ β)).le
  have hz : ∀ B' : ℕ, ∀ e : ℕ, ⌊x ^ β⌋₊ < e →
      ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
        (innerRecipRatio (W x) e F x B' + deriv F (Notation.logx x e)) ^ 2 = 0 := by
    intro B' e he
    obtain ⟨he0, hle⟩ := rpow_le_of_floor_lt he
    rw [innerRecipRatio_eq_zero_of_rpow_le hx he0 hle hFv,
      hdF _ (le_logx_of_rpow_le hx hle)]
    simp
  rw [sum_filter_Icc_collapse (Nat.le_succ ⌊x ^ β⌋₊) _ (hz _),
    sum_filter_Icc_collapse (floor_rpow_le_of_le hBx) _ (hz _)]
  refine congrArg _ (Finset.sum_congr rfl fun e he ↦ ?_)
  have he0 : 0 < e := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
  rw [innerRecipRatio_eq_of_rpow_le hx he0 hcut hBx hFv]

/-- **The mean square over the bulk of the `e`-range.** Same statement as
`Gap212.Sieve.NormalizedInnerRecipL2` except that the sum runs only over `e ≤ B/(z+1)` with
`z = ⌊log log log x⌋` and `B(x) = ⌊x^β⌋+1`, the `e` for which the inner sum has more than one term.

It is equivalent to `Gap212.Sieve.NormalizedInnerRecipL2` (`Gap212.Sieve.bulkInnerRecipL2_iff`),
the complementary summands being nonnegative with vanishing normalized sum
(`Gap212.Sieve.tendsto_kappa_mul_gramTopSum`). It excludes the range where the pointwise limit
`r_F(e) → -F'(log_xe)` fails (`Gap212.Sieve.innerRecip_eq_of_lt_primorial_bound`). -/
def BulkInnerRecipL2 : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) →
      Tendsto (fun x : ℝ ↦ mertensKappa x * gramBulkSum F x β) atTop (nhds 0)

/-- **The bulk alone implies the full mean square.** Top plus bulk is the whole sum at the cut
(`Gap212.Sieve.gramTopSum_add_gramBulkSum`), the top tends to `0`, and the mean square at the cut
is the whole mean square (`Gap212.Sieve.normalizedInnerRecipL2_iff_atCut`). -/
theorem normalizedInnerRecipL2_of_bulkInnerRecipL2 (h : BulkInnerRecipL2) :
    NormalizedInnerRecipL2 := by
  refine normalizedInnerRecipL2_iff_atCut.2 fun F hF hFc β hβ hFv ↦ ?_
  simpa only [add_zero, ← mul_add, gramTopSum_add_gramBulkSum] using
    (tendsto_kappa_mul_gramTopSum hF hFc hβ hFv).add (h F hF hFc β hβ hFv)

/-- **The bulk mean square is equivalent to the whole.** The top block's summands are nonnegative
and their normalized sum tends to `0`. -/
theorem bulkInnerRecipL2_iff : BulkInnerRecipL2 ↔ NormalizedInnerRecipL2 := by
  refine ⟨normalizedInnerRecipL2_of_bulkInnerRecipL2, fun h F hF hFc β hβ hFv ↦ ?_⟩
  have := ((normalizedInnerRecipL2_iff_atCut.mp h) F hF hFc β hβ hFv).sub
    (tendsto_kappa_mul_gramTopSum hF hFc hβ hFv)
  rw [sub_zero] at this
  exact this.congr fun x ↦ by rw [← gramTopSum_add_gramBulkSum F x β]; ring

/-- **The reciprocal Gram-sum limit from the bulk mean square**:
`Gap212.Sieve.LcmGramSumLimitOfSupport` from `Gap212.Sieve.BulkInnerRecipL2`.

The Gram-sum limit is stated for `C^∞` profiles and the mean square for `C¹` ones; the passage is
in `Gap212.Sieve.gramRatioDefectVanishes_of_normalizedInnerRatioL1`. -/
theorem lcmGramSumLimitOfSupport_of_bulkInnerRecipL2 (h : BulkInnerRecipL2) :
    LcmGramSumLimitOfSupport :=
  lcmGramSumLimitOfSupport_of_normalizedInnerRecipL2
    (normalizedInnerRecipL2_of_bulkInnerRecipL2 h)

end Gap212.Sieve
