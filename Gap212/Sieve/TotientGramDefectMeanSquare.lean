/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.GramDefectMeanSquare
public import Gap212.Sieve.TotientGramMeasure

/-!
# The totient Gram-sum limit from a one-profile mean square

`Gap212.Sieve.TotientGramMeasure` shows the totient Gram-sum limit
`Gap212.Sieve.TotientGramSumLimitOfSupport` *equivalent* to
`Gap212.Sieve.TotientGramRatioDefectVanishes`, the statement that the **bilinear** defect

  `κ_x·∑_{e≤B,(e,W)=1}(μ²(e)/(μ*φ)(e))·(ρ_F(e)ρ_G(e) − F'(log_xe)G'(log_xe)) ⟶ 0`,

and records its `ℓ¹` strengthening `Gap212.Sieve.TotientNormalizedInnerRatioL1`. Both couple the
two profiles. This file removes the coupling by the two moves used for the reciprocal kernel in
`Gap212.Sieve.GramDefectMeanSquare`, with the constants, weights and limits of this kernel.

## The truncation quantifier is inert

Once the profiles vanish on `[β,∞)` the inner sum `Gap212.Sieve.innerTotient` is zero for `e > x^β`
(`Gap212.Sieve.innerTotient_eq_zero_of_rpow_le`: every term reads `F` at `log_x(ef) ≥ log_xe ≥ β`)
and does not see `B` below that (`Gap212.Sieve.innerTotient_eq_of_rpow_le`: raising `B` adds only
`f > B/e`, where `ef > B ≥ x^β`). So the quantifier `∀ B ≥ x^β` may be discharged at the single
truncation `B(x) = ⌊x^β⌋+1` and nothing is weakened —
`Gap212.Sieve.totientGramRatioDefectVanishes_iff_atCut` is an `iff`. That collapse is also what
makes the total mass finite, which is what licenses the Cauchy–Schwarz below: `κ_x∑_{e≤B}w` is
`≈ log B(x)/log x` and `B` is bounded only from below.

## Decoupling by Cauchy–Schwarz

With `a_F(e) = ρ_F(e) + F'(log_xe)` the identity `ρ_Fρ_G − F'G' = a_Fa_G − a_FG' − a_GF'` is exact,
so `Gap212.Sieve.kappa_weighted_bilinear_defect_le` — kernel-free, and reused from the reciprocal
kernel — bounds the bilinear defect by the two mean squares and the total mass.
`Gap212.Sieve.TotientNormalizedInnerL2`, one profile and quadratic, therefore implies the Gram-sum
limit (`Gap212.Sieve.totientGramSumLimitOfSupport_of_totientNormalizedInnerL2`).

**Three inputs of that step are this kernel's own.** The weight is `μ²(e)/(μ*φ)(e)`, not
`μ²(e)/φ(e)`; its nonnegativity is `Gap212.Sieve.muPhiWeight_term_nonneg`. The total mass is
evaluated by `Gap212.Sieve.tendsto_mertensKappa_mul_muPhiWeightCut`, whose Mertens constant is
`(φ(W)/W)·(∏_{p∤W}(1-1/(p-1)²))^{-1}` and which therefore already spends
`Gap212.Sieve.tendsto_inv_tprod_corr_W`: on the reciprocal side the same step needs no correction
factor at all. And the pointwise size bound below needs `e` squarefree, because the normalization
`((μ*φ)(e)/φ(e))(φ(W)/W)` is bounded by `1` only there, where the reciprocal kernel's `φ(eW)/(eW)`
is bounded outright.

## The mean-square input does not depend on `W(x) ⟶ ∞`

At *fixed* `W` the predicted value of `ρ_F(e)` is not `-F'(log_xe)` but
`-F'(log_xe)·∏_{p∤W}(1-1/(p-1)²)` (`Gap212.Sieve.innerSumTotientConst_mul_normalization`), so the
mean square against the pointwise prediction is `Gap212.Sieve.TotientCorrectedInnerL2`.
`Gap212.Sieve.totientNormalizedInnerL2_iff_corrected` proves the two mean squares **equivalent**:
`a² ≤ 2b² + 2(a-b)²` against the weight (`Gap212.Sieve.kappa_weighted_sq_shift_le`), the
discrepancy being `(1-c_x)²` times `κ_x∑w·F'(log_xe)²`, which converges to `∫_0^∞(F')²`
(`Gap212.Sieve.tendsto_mertensKappa_mul_muPhiDerivSqSum`) while `c_x ⟶ 1`
(`Gap212.Sieve.tendsto_muPhiCorr`). So the correction factor may be carried or dropped in the
mean-square input, although the Gram-sum limit itself holds only jointly in `W`.

## Scope

`Gap212.Sieve.TotientNormalizedInnerL2` is a **sufficient** condition: the implication runs one
way only, squares forbidding cancellation between the `e`'s just as the absolute values of
`Gap212.Sieve.TotientNormalizedInnerRatioL1` do, and it is not proved in this repository
(`Gap212.Sieve.TotientGramRatioDefectVanishes`, being equivalent to the Gram-sum limit, follows
from `Gap212.Sieve.polymath41Totient`). The bound on `|a_F(e)|` proved here is
`Gap212.Sieve.abs_innerTotientRatio_le_log_primorial_bound`, which covers the one-term top
`e ∈ (B/(z+1),B]`, `z = ⌊log log log x⌋`, and says `|ρ_F(e)| = O(log log log log x)` there.

## Main definitions

* `Gap212.Sieve.TotientGramRatioDefectVanishesAtCut`: the defect statement at `B(x) = ⌊x^β⌋+1`.
* `Gap212.Sieve.TotientNormalizedInnerL2`: the one-profile mean-square input.
* `Gap212.Sieve.muPhiCorr`, `Gap212.Sieve.TotientCorrectedInnerL2`: the correction factor at
  `W(x)`, and the mean square against the pointwise prediction it carries.

## Main results

* `Gap212.Sieve.innerTotient_eq_zero_of_rpow_le`, `Gap212.Sieve.innerTotient_eq_of_rpow_le`: the
  inner sum vanishes once `e` alone exhausts the support, and does not depend on the truncation.
* `Gap212.Sieve.totientGramRatioDefectVanishes_iff_atCut`: the `B` quantifier is spurious.
* `Gap212.Sieve.totientNormalizedInnerRatioL1_of_totientNormalizedInnerL2`,
  `Gap212.Sieve.totientGramSumLimitOfSupport_of_totientNormalizedInnerL2`: the Gram-sum limit from
  the one-profile mean square.
* `Gap212.Sieve.totientNormalizedInnerL2_iff_corrected`: the correction factor may be carried or
  dropped.
* `Gap212.Sieve.abs_innerTotientRatio_le_log_primorial_bound`: the size of the defect on the
  one-term top block.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY
open scoped ArithmeticFunction.Moebius

/-! ## The support hypothesis truncates the `e`-range and erases the truncation `B` -/

/-- **The totient inner sum vanishes as soon as `e` alone exhausts the profile's support.** -/
theorem innerTotient_eq_zero_of_rpow_le {x β : ℝ} (hx : 1 < x) {W e B : ℕ} (he : 0 < e)
    (hle : x ^ β ≤ (e : ℝ)) {F : ℝ → ℝ} (hFv : ∀ t, β ≤ t → F t = 0) :
    innerTotient W e F x B = 0 := by
  refine Finset.sum_eq_zero fun f hf ↦ ?_
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hf).1).1
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  rw [hFv _ (le_logx_of_rpow_le hx (by nlinarith)), mul_zero, zero_div]

/-- **The normalized totient inner sum vanishes there too.** -/
theorem innerTotientRatio_eq_zero_of_rpow_le {x β : ℝ} (hx : 1 < x) {W e B : ℕ} (he : 0 < e)
    (hle : x ^ β ≤ (e : ℝ)) {F : ℝ → ℝ} (hFv : ∀ t, β ≤ t → F t = 0) :
    innerTotientRatio W e F x B = 0 := by
  rw [innerTotientRatio, innerTotient_eq_zero_of_rpow_le hx he hle hFv]
  simp

/-- **The totient inner sum does not depend on the truncation, above `x^β`.** -/
theorem innerTotient_eq_of_rpow_le {x β : ℝ} (hx : 1 < x) {W e B B' : ℕ} (he : 0 < e)
    (hB : x ^ β ≤ (B : ℝ)) (hBB' : B ≤ B') {F : ℝ → ℝ} (hFv : ∀ t, β ≤ t → F t = 0) :
    innerTotient W e F x B' = innerTotient W e F x B := by
  refine (Finset.sum_subset (Finset.filter_subset_filter _
    (Finset.Icc_subset_Icc le_rfl (Nat.div_le_div_right hBB'))) fun f hf hnf ↦ ?_).symm
  obtain ⟨hfI, hcop⟩ := Finset.mem_filter.mp hf
  have hlt : B / e < f := not_le.mp fun hc ↦
    hnf (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hfI).1, hc⟩, hcop⟩)
  have hBef : B ≤ e * f := by
    rw [Nat.mul_comm]
    exact ((Nat.div_lt_iff_lt_mul he).mp hlt).le
  rw [hFv _ (le_logx_of_rpow_le hx (hB.trans (by exact_mod_cast hBef))), mul_zero, zero_div]

/-- Truncation-independence of `Gap212.Sieve.innerTotient`, symmetrically in the two cutoffs. -/
theorem innerTotient_eq_of_rpow_le_of_rpow_le {x β : ℝ} (hx : 1 < x) {W e B B' : ℕ} (he : 0 < e)
    (hB : x ^ β ≤ (B : ℝ)) (hB' : x ^ β ≤ (B' : ℝ)) {F : ℝ → ℝ}
    (hFv : ∀ t, β ≤ t → F t = 0) :
    innerTotient W e F x B = innerTotient W e F x B' := by
  rcases le_total B B' with hle | hle
  · exact (innerTotient_eq_of_rpow_le hx he hB hle hFv).symm
  · exact innerTotient_eq_of_rpow_le hx he hB' hle hFv

/-- **The normalized totient inner sum does not depend on the truncation either.** -/
theorem innerTotientRatio_eq_of_rpow_le {x β : ℝ} (hx : 1 < x) {W e B B' : ℕ} (he : 0 < e)
    (hB : x ^ β ≤ (B : ℝ)) (hB' : x ^ β ≤ (B' : ℝ)) {F : ℝ → ℝ}
    (hFv : ∀ t, β ≤ t → F t = 0) :
    innerTotientRatio W e F x B = innerTotientRatio W e F x B' := by
  rw [innerTotientRatio, innerTotientRatio,
    innerTotient_eq_of_rpow_le_of_rpow_le hx he hB hB' hFv]

/-- Above `⌊x^β⌋` both halves of a defect summand vanish: the normalized inner sum and `F'`. -/
private theorem innerTotientRatio_eq_zero_and_deriv_eq_zero {x β : ℝ} (hx : 1 < x) {W e B : ℕ}
    (he : ⌊x ^ β⌋₊ < e) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFv : ∀ t, β ≤ t → F t = 0) :
    innerTotientRatio W e F x B = 0 ∧ deriv F (Notation.logx x e) = 0 := by
  obtain ⟨he0, hle⟩ := rpow_le_of_floor_lt he
  exact ⟨innerTotientRatio_eq_zero_of_rpow_le hx he0 hle hFv,
    deriv_eq_zero_of_eventually_zero hF hFv _ (le_logx_of_rpow_le hx hle)⟩

/-- **The totient defect statement at the single truncation `B(x) = ⌊x^β⌋+1`.**
`Gap212.Sieve.TotientGramRatioDefectVanishes` quantifies over every `B` with `B(x) ≥ x^β`; this
fixes the smallest admissible one.

The profiles are `C^∞`, as in `Gap212.Sieve.TotientGramRatioDefectVanishes`. -/
def TotientGramRatioDefectVanishesAtCut : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → ContDiff ℝ (⊤ : ℕ∞) G →
    HasCompactSupport G →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) → (∀ t, β ≤ t → G t = 0) →
      Tendsto (fun x : ℝ ↦ mertensKappa x *
          ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e,
            ((μ e : ℝ) ^ 2 / moebiusTotient e) *
              (innerTotientRatio (W x) e F x (⌊x ^ β⌋₊ + 1)
                  * innerTotientRatio (W x) e G x (⌊x ^ β⌋₊ + 1)
                - deriv F (Notation.logx x e) * deriv G (Notation.logx x e)))
        atTop (nhds 0)

/-- **The `B` quantifier of the totient defect statement is spurious.** Given the support
hypothesis the dependence on the truncation is nil: the `e`-range above `⌊x^β⌋`
contributes nothing (`Gap212.Sieve.innerTotientRatio_eq_zero_of_rpow_le` and
`Gap212.Sieve.deriv_eq_zero_of_eventually_zero` kill both halves of each summand separately) and
the inner sums below it do not see `B` at all
(`Gap212.Sieve.innerTotientRatio_eq_of_rpow_le`). So it suffices to prove the statement at the one
truncation `B(x) = ⌊x^β⌋+1`, and nothing is weakened — this is an `iff`.

Composed with `Gap212.Sieve.totientGramSumLimitOfSupport_iff_totientGramRatioDefectVanishes`,
`Gap212.Sieve.TotientGramSumLimitOfSupport` is equivalent to a statement in the two profiles and
`β` alone. -/
theorem totientGramRatioDefectVanishes_iff_atCut :
    TotientGramRatioDefectVanishes ↔ TotientGramRatioDefectVanishesAtCut := by
  constructor
  · intro h F G hF hFc hG hGc β hβ hFv hGv
    refine h F G hF hFc hG hGc β hβ hFv hGv _ (Filter.Eventually.of_forall fun x ↦ ?_)
    push_cast
    exact (Nat.lt_floor_add_one (x ^ β)).le
  · intro h F G hF hFc hG hGc β hβ hFv hGv B hB
    refine (h F G hF hFc hG hGc β hβ hFv hGv).congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ), hB] with x hx hBx
    have hcut : x ^ β ≤ ((⌊x ^ β⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      exact (Nat.lt_floor_add_one (x ^ β)).le
    have hz : ∀ B' : ℕ, ∀ e : ℕ, ⌊x ^ β⌋₊ < e →
        ((μ e : ℝ) ^ 2 / moebiusTotient e) *
          (innerTotientRatio (W x) e F x B' * innerTotientRatio (W x) e G x B'
            - deriv F (Notation.logx x e) * deriv G (Notation.logx x e)) = 0 := by
      intro B' e he
      obtain ⟨h1, h2⟩ := innerTotientRatio_eq_zero_and_deriv_eq_zero (W := W x) (B := B') hx he
        (hF.of_le (by exact_mod_cast le_top)) hFv
      simp [h1, h2]
    rw [sum_filter_Icc_collapse (Nat.le_succ ⌊x ^ β⌋₊) _ (hz _),
      sum_filter_Icc_collapse (floor_rpow_le_of_le hBx) _ (hz _)]
    refine congrArg _ (Finset.sum_congr rfl fun e he ↦ ?_)
    have he0 : 0 < e := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
    rw [innerTotientRatio_eq_of_rpow_le hx he0 hcut hBx hFv,
      innerTotientRatio_eq_of_rpow_le hx he0 hcut hBx hGv]

/-! ## The one-profile mean square, and the Gram-sum limit from it -/

/-- **The totient kernel's one-profile mean square.** With `a_F(e) = ρ_F(e) + F'(log_xe)` the
defect of the normalized inner sum `Gap212.Sieve.innerTotientRatio` against `-F'(log_xe)`, this
asks

  `κ_x·∑_{e≤B,(e,W)=1}(μ²(e)/(μ*φ)(e))·a_F(e)² ⟶ 0`.

One profile, not two; quadratic, not bilinear. It implies the Gram-sum limit
(`Gap212.Sieve.totientGramSumLimitOfSupport_of_totientNormalizedInnerL2`) through
`Gap212.Sieve.TotientNormalizedInnerRatioL1`, and only that: it is a **sufficient** condition for
the equivalent `Gap212.Sieve.TotientGramRatioDefectVanishes`, no converse is proved, and squaring
does forbid cancellation between the `e`'s that the defect statement would allow.

The weight is the totient kernel's `μ²(e)/(μ*φ)(e)` — positive only on the odd squarefree `e`,
since `(μ*φ)(2) = 0`, and supplied there by coprimality to the eventually even `W(x)`
(`Gap212.Sieve.eventually_two_dvd_W`) — against the reciprocal kernel's `μ²(e)/φ(e)`. The
normalization `κ_x = (W/φ(W))/log x` is shared; the arithmetic is not. -/
def TotientNormalizedInnerL2 : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) →
      ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
        Tendsto (fun x : ℝ ↦ mertensKappa x *
            ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
              ((μ e : ℝ) ^ 2 / moebiusTotient e) *
                (innerTotientRatio (W x) e F x (B x) + deriv F (Notation.logx x e)) ^ 2)
          atTop (nhds 0)

/-- **The mean square gives the weighted `ℓ¹` defect, hence the Gram-sum limit.** Cauchy–Schwarz
against the normalized measure (`Gap212.Sieve.kappa_weighted_bilinear_defect_le`), with the total
mass evaluated by `Gap212.Sieve.tendsto_mertensKappa_mul_muPhiWeightCut` after the `e`-range
collapses to `[1,⌊x^β⌋]`. That mass evaluation is where this kernel differs: its Mertens constant
carries `(∏_{p∤W}(1-1/(p-1)²))^{-1}`, so the step consumes `Gap212.Sieve.tendsto_inv_tprod_corr_W`,
which the reciprocal kernel's corresponding step does not need. -/
theorem totientNormalizedInnerRatioL1_of_totientNormalizedInnerL2
    (h : TotientNormalizedInnerL2) : TotientNormalizedInnerRatioL1 := by
  intro F G hF hFc hG hGc β hβ hFv hGv B hB
  obtain ⟨MF, hMFn⟩ := hFc.deriv.exists_bound_of_continuous hF.continuous_deriv_one
  obtain ⟨MG, hMGn⟩ := hGc.deriv.exists_bound_of_continuous hG.continuous_deriv_one
  have hMF : ∀ t : ℝ, |deriv F t| ≤ MF := fun t ↦ by simpa using hMFn t
  have hMG : ∀ t : ℝ, |deriv G t| ≤ MG := fun t ↦ by simpa using hMGn t
  have hglim : Tendsto (fun x : ℝ ↦
      Real.sqrt (mertensKappa x * ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / moebiusTotient e) *
            (innerTotientRatio (W x) e F x (B x) + deriv F (Notation.logx x e)) ^ 2)
        * Real.sqrt (mertensKappa x * ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / moebiusTotient e) *
            (innerTotientRatio (W x) e G x (B x) + deriv G (Notation.logx x e)) ^ 2)
      + MG * (Real.sqrt (mertensKappa x * ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / moebiusTotient e) *
            (innerTotientRatio (W x) e F x (B x) + deriv F (Notation.logx x e)) ^ 2)
        * Real.sqrt (mertensKappa x * muPhiWeightCut x β))
      + MF * (Real.sqrt (mertensKappa x * ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / moebiusTotient e) *
            (innerTotientRatio (W x) e G x (B x) + deriv G (Notation.logx x e)) ^ 2)
        * Real.sqrt (mertensKappa x * muPhiWeightCut x β))) atTop (nhds 0) := by
    have s1 := (h F hF hFc β hβ hFv B hB).sqrt
    have s2 := (h G hG hGc β hβ hGv B hB).sqrt
    have s3 := (tendsto_mertensKappa_mul_muPhiWeightCut hβ).sqrt
    simpa using ((s1.mul s2).add ((s1.mul s3).const_mul MG)).add ((s2.mul s3).const_mul MF)
  refine squeeze_zero' ?_ ?_ hglim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (mertensKappa_nonneg hx.le)
      (Finset.sum_nonneg fun e _ ↦ mul_nonneg (muPhiWeight_term_nonneg e) (abs_nonneg _))
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hB] with x hx hBx
    have hNB : ⌊x ^ β⌋₊ ≤ B x := floor_rpow_le_of_le hBx
    have hzF e (he : ⌊x ^ β⌋₊ < e) := innerTotientRatio_eq_zero_and_deriv_eq_zero (W := W x)
      (B := B x) hx he hF hFv
    have hzG e (he : ⌊x ^ β⌋₊ < e) := innerTotientRatio_eq_zero_and_deriv_eq_zero (W := W x)
      (B := B x) hx he hG hGv
    rw [sum_filter_Icc_collapse hNB _ fun e he ↦ by simp [hzF e he],
      sum_filter_Icc_collapse hNB _ fun e he ↦ by simp [hzF e he],
      sum_filter_Icc_collapse hNB _ fun e he ↦ by simp [hzG e he], muPhiWeightCut]
    simpa using kappa_weighted_bilinear_defect_le (κ := mertensKappa x)
      (S := {e ∈ Icc 1 ⌊x ^ β⌋₊ | Nat.Coprime (W x) e})
      (w := fun e ↦ ((μ e : ℝ) ^ 2 / moebiusTotient e))
      (a := fun e ↦ innerTotientRatio (W x) e F x (B x) + deriv F (Notation.logx x e))
      (b := fun e ↦ innerTotientRatio (W x) e G x (B x) + deriv G (Notation.logx x e))
      (p := fun e ↦ deriv F (Notation.logx x e)) (q := fun e ↦ deriv G (Notation.logx x e))
      (mertensKappa_nonneg hx.le) (fun e _ ↦ muPhiWeight_term_nonneg e)
      ((abs_nonneg _).trans (hMF 0)) ((abs_nonneg _).trans (hMG 0)) (fun e _ ↦ hMF _)
      (fun e _ ↦ hMG _)

/-- **The totient Gram-sum limit from the one-profile mean square.** -/
theorem totientGramSumLimitOfSupport_of_totientNormalizedInnerL2
    (h : TotientNormalizedInnerL2) : TotientGramSumLimitOfSupport :=
  totientGramSumLimitOfSupport_of_totientNormalizedInnerRatioL1
    (totientNormalizedInnerRatioL1_of_totientNormalizedInnerL2 h)

/-! ## The correction factor: the pointwise prediction, and that it changes nothing -/

/-- **The correction factor at the pre-sieving modulus**, `∏_{p∤W(x)}(1-1/(p-1)²)`: the
`e`-independent factor the fixed-`W` prediction for `Gap212.Sieve.innerTotientRatio` carries
(`Gap212.Sieve.innerSumTotientConst_mul_normalization`), the twin-prime constant `0.660162` at
`W = 2`. -/
noncomputable def muPhiCorr (x : ℝ) : ℝ :=
  ∏' p : ℕ, if p.Prime ∧ ¬ p ∣ W x then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

/-- `Gap212.Sieve.tendsto_tprod_corr_W` at the abbreviation: `∏_{p∤W(x)}(1-1/(p-1)²) → 1`. -/
theorem tendsto_muPhiCorr : Tendsto muPhiCorr atTop (nhds 1) := tendsto_tprod_corr_W

/-- **The mean square against the pointwise prediction `-F'(log_xe)·∏_{p∤W}(1-1/(p-1)²)`.** This is
the form matching the pointwise prediction: at fixed `W` it is `ρ_F(e) + c_W·F'(log_xe)` and not
`ρ_F(e) + F'(log_xe)` that the fixed-modulus asymptotic predicts to be small, the two differing by
`(1-c_W)F'` — which is `34%` of `F'` at `W = 2`, not a perturbation.
`Gap212.Sieve.totientNormalizedInnerL2_iff_corrected` shows the distinction does not survive
`x ⟶ ∞`: the two mean squares are equivalent. -/
def TotientCorrectedInnerL2 : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) →
      ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
        Tendsto (fun x : ℝ ↦ mertensKappa x *
            ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
              ((μ e : ℝ) ^ 2 / moebiusTotient e) *
                (innerTotientRatio (W x) e F x (B x)
                  + muPhiCorr x * deriv F (Notation.logx x e)) ^ 2)
          atTop (nhds 0)

/-- **`a² ≤ 2b² + 2(a-b)²` summed against a nonnegative weight**, the normalization folded in. The
pointwise inequality is `(a-2b)² ≥ 0`. This is what makes two mean squares whose predictions differ
by a vanishing multiple of a fixed profile interchangeable. -/
theorem kappa_weighted_sq_shift_le {κ : ℝ} (hκ : 0 ≤ κ) {S : Finset ℕ} {w a b : ℕ → ℝ}
    (hw : ∀ e ∈ S, 0 ≤ w e) :
    κ * ∑ e ∈ S, w e * a e ^ 2
      ≤ 2 * (κ * ∑ e ∈ S, w e * b e ^ 2) + 2 * (κ * ∑ e ∈ S, w e * (a e - b e) ^ 2) := by
  rw [mul_left_comm 2 κ, mul_left_comm 2 κ, ← mul_add]
  gcongr
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  gcongr with e he
  nlinarith [mul_nonneg (hw e he) (sq_nonneg (a e - 2 * b e))]

/-- **The `μ²/(μ*φ)`-weighted mean square of `F'` converges to `∫₀^∞(F')²`.** The measure theorem
`Gap212.Sieve.tendsto_mertensKappa_mul_muPhiWeightedSum` at `H = (F')²`. -/
theorem tendsto_mertensKappa_mul_muPhiDerivSqSum {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) {β : ℝ}
    (hβ : 0 < β) (hFv : ∀ t, β ≤ t → F t = 0) (B : ℝ → ℕ)
    (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦ mertensKappa x *
        ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / moebiusTotient e) * deriv F (Notation.logx x e) ^ 2)
      atTop (nhds (∫ t in Set.Ioi (0 : ℝ), deriv F t ^ 2)) := by
  refine tendsto_mertensKappa_mul_muPhiWeightedSum (hF.continuous_deriv_one.pow 2) hβ
    (fun t ht ↦ ?_) B hB
  simp [deriv_eq_zero_of_eventually_zero hF hFv t ht]

/-- **The two mean squares are the same statement.** Taking `a = ρ_F + F'`, `b = ρ_F + c_xF'` in
`Gap212.Sieve.kappa_weighted_sq_shift_le`, the discrepancy is `2(1-c_x)²·κ_x∑w·F'(log_xe)²`, and
the second factor converges to `∫_0^∞(F')²` while `(1-c_x)² ⟶ 0`. Symmetrically in the other
direction.

The Gram-sum limit is joint in `W`: at fixed `W` the totient Gram sum tends to
`(∏_{p∤W}(1-1/(p-1)²))·∫F'G'` and not to `∫F'G'`, which is why `Gap212.Sieve.tendsto_tprod_corr_W`
is needed. The mean-square **input**, by contrast, need not carry the factor. The reciprocal
kernel's fixed-`W` statement is already the joint one. -/
theorem totientNormalizedInnerL2_iff_corrected :
    TotientNormalizedInnerL2 ↔ TotientCorrectedInnerL2 := by
  have key : ∀ c₁ c₂ : ℝ → ℝ, Tendsto (fun x ↦ c₁ x - c₂ x) atTop (nhds 0) →
      ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) →
      ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
      Tendsto (fun x : ℝ ↦ mertensKappa x *
          ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
            ((μ e : ℝ) ^ 2 / moebiusTotient e) *
              (innerTotientRatio (W x) e F x (B x) + c₂ x * deriv F (Notation.logx x e)) ^ 2)
        atTop (nhds 0) →
      Tendsto (fun x : ℝ ↦ mertensKappa x *
          ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
            ((μ e : ℝ) ^ 2 / moebiusTotient e) *
              (innerTotientRatio (W x) e F x (B x) + c₁ x * deriv F (Notation.logx x e)) ^ 2)
        atTop (nhds 0) := by
    intro c₁ c₂ hc F hF β hβ hFv B hB hA
    have hmaj := (hA.const_mul 2).add
      (((hc.pow 2).mul (tendsto_mertensKappa_mul_muPhiDerivSqSum hF hβ hFv B hB)).const_mul 2)
    rw [zero_pow two_ne_zero, zero_mul, mul_zero, add_zero] at hmaj
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact mul_nonneg (mertensKappa_nonneg hx.le)
        (Finset.sum_nonneg fun e _ ↦ mul_nonneg (muPhiWeight_term_nonneg e) (sq_nonneg _))
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      refine (kappa_weighted_sq_shift_le (κ := mertensKappa x)
        (S := {e ∈ Icc 1 (B x) | Nat.Coprime (W x) e})
        (w := fun e ↦ ((μ e : ℝ) ^ 2 / moebiusTotient e))
        (a := fun e ↦ innerTotientRatio (W x) e F x (B x) + c₁ x * deriv F (Notation.logx x e))
        (b := fun e ↦ innerTotientRatio (W x) e F x (B x) + c₂ x * deriv F (Notation.logx x e))
        (mertensKappa_nonneg hx.le) fun e _ ↦ muPhiWeight_term_nonneg e).trans_eq ?_
      congr 2
      rw [mul_left_comm ((c₁ x - c₂ x) ^ 2)]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ ↦ by ring
  constructor
  · intro h F hF hFc β hβ hFv B hB
    exact key muPhiCorr (fun _ ↦ 1) (by simpa using tendsto_muPhiCorr.sub_const 1) F hF β hβ hFv
      B hB (by simpa using h F hF hFc β hβ hFv B hB)
  · intro h F hF hFc β hβ hFv B hB
    simpa using key (fun _ ↦ 1) muPhiCorr (by simpa using tendsto_muPhiCorr.const_sub 1) F hF β
      hβ hFv B hB (h F hF hFc β hβ hFv B hB)

/-! ## How large the defect is at the top of the `e`-range -/

/-- **The local factors of the correction product lie in `[0,1]`.** `1 - 1/(p-1)² ∈ [0,1]` for
every prime `p`, with the value `0` at `p = 2`. -/
theorem one_sub_inv_sub_one_sq_mem {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ 1 - 1 / ((p : ℝ) - 1) ^ 2 ∧ 1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpos : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
  refine ⟨by rw [sub_nonneg, div_le_one hpos]; nlinarith, by nlinarith [one_div_pos.mpr hpos]⟩

/-- **`(μ*φ)(e)/φ(e) ∈ [0,1]` on a squarefree `e`**, through the identity
`e(μ*φ)(e)/φ(e)² = ∏_{p∣e}(1-1/(p-1)²)`
(`Gap212.Sieve.mul_moebiusTotient_div_totient_sq`): the ratio is that product times `φ(e)/e`, and
both factors lie in `[0,1]`. -/
theorem moebiusTotient_div_totient_mem {e : ℕ} (he : 0 < e) (hsf : Squarefree e) :
    0 ≤ moebiusTotient e / (e.totient : ℝ) ∧ moebiusTotient e / (e.totient : ℝ) ≤ 1 := by
  have hpe : (0 : ℝ) < (e.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr he
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hP := mul_moebiusTotient_div_totient_sq hsf
  have hmem p (hp : p ∈ e.primeFactors) :=
    one_sub_inv_sub_one_sq_mem (Nat.prime_of_mem_primeFactors hp).two_le
  have hphi : (e.totient : ℝ) / (e : ℝ) ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast Nat.totient_le e) heR.le
  have hratio : moebiusTotient e / (e.totient : ℝ)
      = (∏ p ∈ e.primeFactors, (1 - 1 / ((p : ℝ) - 1) ^ 2)) * ((e.totient : ℝ) / (e : ℝ)) := by
    rw [← hP]
    field_simp
  rw [hratio]
  exact ⟨mul_nonneg (Finset.prod_nonneg fun p hp ↦ (hmem p hp).1) (by positivity),
    mul_le_one₀ (Finset.prod_le_one (fun p hp ↦ (hmem p hp).1) fun p hp ↦ (hmem p hp).2)
      (by positivity) hphi⟩

/-- **The normalization of `Gap212.Sieve.innerTotientRatio` is at most `1` on a squarefree `e`.**
`(μ*φ)(e)/φ(e) ∈ [0,1]` there (`Gap212.Sieve.moebiusTotient_div_totient_mem`) and `φ(W) ≤ W`.
This is the totient kernel's replacement for the reciprocal kernel's `φ(eW)/(eW) ≤ 1`, which needs
no hypothesis at all. -/
theorem abs_innerTotientNorm_le_one {W e : ℕ} (he : 0 < e) (hsf : Squarefree e) :
    |moebiusTotient e / (e.totient : ℝ) * ((W.totient : ℝ) / (W : ℝ))| ≤ 1 := by
  obtain ⟨h1, h2⟩ := moebiusTotient_div_totient_mem he hsf
  have h3 : 0 ≤ (W.totient : ℝ) / (W : ℝ) := by positivity
  rw [abs_of_nonneg (mul_nonneg h1 h3)]
  exact mul_le_one₀ h2 h3 (div_le_one_of_le₀ (by exact_mod_cast Nat.totient_le W) (by positivity))

/-- **In the one-term regime the normalized totient inner sum is at most `‖F'‖_∞·log(x^β/e)`.**
Where `Gap212.Sieve.innerTotient` collapses to its `f = 1` term `F(log_xe)`, no cancellation is
available and `ρ_F(e) = log x·F(log_xe)·((μ*φ)(e)/φ(e))(φ(W)/W)`. The arithmetic factor is at most
`1` (`Gap212.Sieve.abs_innerTotientNorm_le_one`) and the support hypothesis bounds `|F(log_xe)|` by
`‖F'‖_∞(β - log_xe)`; multiplying by `log x` turns that into `log(x^β/e)`. -/
theorem abs_innerTotientRatio_le_of_innerTotient_eq {x β M : ℝ} (hx : 1 < x) {W e B : ℕ}
    (he : 0 < e) (hsf : Squarefree e) {F : ℝ → ℝ}
    (hone : innerTotient W e F x B = F (Notation.logx x e)) (hF : ContDiff ℝ 1 F)
    (hM : ∀ t, |deriv F t| ≤ M) (hFv : ∀ t, β ≤ t → F t = 0) (hle : (e : ℝ) ≤ x ^ β) :
    |innerTotientRatio W e F x B| ≤ M * Real.log (x ^ β / (e : ℝ)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hM0 : (0 : ℝ) ≤ M := (abs_nonneg _).trans (hM 0)
  have ht : Notation.logx x (e : ℝ) ≤ β := by
    rw [Notation.logx, div_le_iff₀ hlogx, ← Real.log_rpow hx0]
    exact Real.log_le_log heR hle
  have hFb : |F (Notation.logx x (e : ℝ))| ≤ M * (β - Notation.logx x (e : ℝ)) :=
    abs_le_deriv_bound_mul_sub hF hM hFv ht
  have hkey : Real.log x * (β - Notation.logx x (e : ℝ)) = Real.log (x ^ β / (e : ℝ)) := by
    rw [Real.log_div (by positivity) heR.ne', Real.log_rpow hx0, Notation.logx]
    field_simp
  rw [innerTotientRatio, hone, mul_assoc (Real.log x * _), abs_mul, abs_mul, abs_of_pos hlogx]
  calc _ ≤ Real.log x * (M * (β - Notation.logx x (e : ℝ))) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hFb hlogx.le)
          (abs_innerTotientNorm_le_one he hsf) (abs_nonneg _)
          (mul_nonneg hlogx.le (mul_nonneg hM0 (by linarith)))
    _ = M * Real.log (x ^ β / (e : ℝ)) := by rw [mul_one, ← hkey]; ring

/-- **The size of the totient defect at the top of the `e`-range.** For every squarefree
`e ∈ (B/(z+1), B]` with `z = ⌊log log log x⌋` — the regime where
`Gap212.Sieve.innerTotient_eq_of_lt_primorial_bound` collapses the inner sum to a single term, and
where the pointwise limit is therefore **false** —

  `|ρ_F(e)| ≤ ‖F'‖_∞·log(z+1)`,

unbounded, but only by `log log log log x`. The totient counterpart of
`Gap212.Sieve.abs_innerRecipRatio_le_log_primorial_bound`, with a squarefreeness hypothesis and the
arithmetic factor `((μ*φ)(e)/φ(e))(φ(W)/W)` in place of `φ(eW)/(eW)`.

This bounds the normalized inner sum only, not the total weight of the regime. -/
theorem abs_innerTotientRatio_le_log_primorial_bound {x β M : ℝ} (hx : 1 < x) {e B : ℕ}
    (he : 0 < e) (hsf : Squarefree e) (heB : e ≤ B)
    (hzlt : (B : ℝ) / (e : ℝ) < (⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1)
    (hB : x ^ β ≤ (B : ℝ)) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hM : ∀ t, |deriv F t| ≤ M)
    (hFv : ∀ t, β ≤ t → F t = 0) :
    |innerTotientRatio (W x) e F x B|
      ≤ M * Real.log ((⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1) := by
  have hM0 : (0 : ℝ) ≤ M := (abs_nonneg _).trans (hM 0)
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  rcases le_or_gt ((e : ℝ)) (x ^ β) with hle | hgt
  · refine (abs_innerTotientRatio_le_of_innerTotient_eq hx he hsf
      (innerTotient_eq_of_lt_primorial_bound he heB hzlt F) hF hM hFv hle).trans ?_
    have h1 : x ^ β / (e : ℝ) ≤ (B : ℝ) / (e : ℝ) := by gcongr
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (h1.trans hzlt.le)) hM0
  · rw [innerTotientRatio_eq_zero_of_rpow_le hx he hgt.le hFv, abs_zero]
    exact mul_nonneg hM0 (Real.log_nonneg (by simp))

end Gap212.Sieve
