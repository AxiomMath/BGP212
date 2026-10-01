/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.GramRiemannSum

/-!
# The reciprocal Gram-sum limit from a one-profile mean square

`Gap212.Sieve.GramRiemannSum` shows the reciprocal Gram-sum limit
`Gap212.Sieve.LcmGramSumLimitOfSupport` equivalent to `Gap212.Sieve.GramRatioDefectVanishes`, the
statement that the bilinear defect

  `κ_x·∑_{e≤B,(e,W)=1}(μ²(e)/φ(e))·(r_F(e)r_G(e) − F'(log_xe)G'(log_xe)) ⟶ 0`,

and states its `ℓ¹` strengthening `Gap212.Sieve.NormalizedInnerRatioL1`. Both couple the two
profiles. Writing `a_F(e) = r_F(e) + F'(log_xe)` for the one-profile defect,

  `r_F(e)r_G(e) − F'G' = a_Fa_G − a_F·G' − a_G·F'`,

so Cauchy–Schwarz against the normalized measure `κ_x·μ²(e)/φ(e)` bounds the defect by the two mean
squares and the total mass:

  `κ_x∑w|r_Fr_G − F'G'| ≤ √(κ_x∑w a_F²)·√(κ_x∑w a_G²)
     + ‖G'‖_∞√(κ_x∑w a_F²)·√(κ_x∑w) + ‖F'‖_∞√(κ_x∑w a_G²)·√(κ_x∑w)`.

The total mass is evaluated by `Gap212.Sieve.tendsto_mertensKappa_mul_weightCut`:
`κ_x·A_W(x^β) → β`. So the one-profile mean square `Gap212.Sieve.NormalizedInnerRecipL2` implies the
Gram-sum limit. It is a sufficient condition only; the Gram-sum limit itself follows from
`Gap212.Sieve.polymath41Recip`.

## The support hypothesis truncates the `e`-range

`κ_x∑_{e≤B}w` is `≈ log B(x)/log x`, unbounded since only `B(x) ≥ x^β` is assumed. But the
one-profile defect `a_F(e)` vanishes identically for `e > x^β`
(`Gap212.Sieve.innerRecipRatio_eq_zero_of_rpow_le`,
`Gap212.Sieve.deriv_eq_zero_of_eventually_zero`), so every sum collapses to the range `e ≤ ⌊x^β⌋`,
where the mass is `mertensWeightCut x β`. In particular the defect statement does not depend on `B`
once the profiles vanish from `β` on, and may be stated at the single truncation `B(x) = ⌊x^β⌋+1`
(`Gap212.Sieve.innerRecip_eq_of_rpow_le`, `Gap212.Sieve.gramRatioDefectVanishes_iff_atCut`).

## The top of the `e`-range

On the range `e ∈ (B/(z+1),B]`, `z = ⌊log log log x⌋`, where the inner sum has a single term,
`Gap212.Sieve.abs_innerRecipRatio_le_log_primorial_bound` gives `|a_F(e)| = O(log log log log x)`;
the contribution of that block to the defect is `Gap212.Sieve.tendsto_kappa_mul_gramTopSum`.

The kernel is the reciprocal one throughout: the weight is `μ²(e)/φ(e)` and the normalization
`κ_x = (W/φ(W))/log x`, with no `∏_{p∤W}(1−1/(p−1)²)` correction, which belongs to the totient
kernel.

## Main definitions

* `Gap212.Sieve.NormalizedInnerRecipL2`: the one-profile mean square.
* `Gap212.Sieve.GramRatioDefectVanishesAtCut`: the defect statement at the single truncation
  `B(x) = ⌊x^β⌋+1`.

## Main results

* `Gap212.Sieve.innerRecip_eq_zero_of_rpow_le`, `Gap212.Sieve.innerRecipRatio_eq_zero_of_rpow_le`:
  the inner sum vanishes once `e` alone exhausts the support.
* `Gap212.Sieve.innerRecip_eq_of_rpow_le`: the inner sum does not depend on the truncation `B`
  above `x^β`.
* `Gap212.Sieve.gramRatioDefectVanishes_iff_atCut`: the defect statement at one truncation.
* `Gap212.Sieve.kappa_weighted_bilinear_defect_le`: the Cauchy–Schwarz bound, abstractly.
* `Gap212.Sieve.normalizedInnerRatioL1_of_normalizedInnerRecipL2` and
  `Gap212.Sieve.lcmGramSumLimitOfSupport_of_normalizedInnerRecipL2`: the Gram-sum limit from the
  one-profile mean square.
* `Gap212.Sieve.abs_innerRecipRatio_le_log_primorial_bound`:
  `|r_F(e)| ≤ ‖F'‖_∞·log(⌊log log log x⌋+1)` at the top of the `e`-range.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY
open scoped ArithmeticFunction.Moebius

/-! ## The support hypothesis truncates the `e`-range and erases the truncation `B` -/

/-- `x^β ≤ y` and `1 < x` give `β ≤ log_xy`: the logarithm is monotone and `log(x^β) = β log x`. -/
theorem le_logx_of_rpow_le {x β y : ℝ} (hx : 1 < x) (hle : x ^ β ≤ y) :
    β ≤ Notation.logx x y := by
  have hx0 : (0 : ℝ) < x := by linarith
  rw [Notation.logx, le_div_iff₀ (Real.log_pos hx), ← Real.log_rpow hx0]
  exact Real.log_le_log (Real.rpow_pos_of_pos hx0 β) hle

/-- **The inner sum vanishes as soon as `e` alone exhausts the profile's support.** Every term of
`Gap212.Sieve.innerRecip` reads `F` at `log_x(ef)` with `f ≥ 1`, hence at an argument at least
`log_xe ≥ β`, where `F` is zero. This is the companion of
`Gap212.Sieve.innerRecip_eq_zero_of_profile_vanishing`, for a profile supported above the
truncation; here the profile is supported below `β` and `e` is large. -/
theorem innerRecip_eq_zero_of_rpow_le {x β : ℝ} (hx : 1 < x) {W e B : ℕ} (he : 0 < e)
    (hle : x ^ β ≤ (e : ℝ)) {F : ℝ → ℝ} (hFv : ∀ t, β ≤ t → F t = 0) :
    innerRecip W e F x B = 0 := by
  refine Finset.sum_eq_zero fun f hf ↦ ?_
  have hf1 : (1 : ℝ) ≤ f := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mem_coprimeBelow.mp hf).1
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  rw [hFv _ (le_logx_of_rpow_le hx (hle.trans (by nlinarith))), mul_zero, zero_div]

/-- **The normalized inner sum vanishes there too**, being a multiple of the inner sum. -/
theorem innerRecipRatio_eq_zero_of_rpow_le {x β : ℝ} (hx : 1 < x) {W e B : ℕ} (he : 0 < e)
    (hle : x ^ β ≤ (e : ℝ)) {F : ℝ → ℝ} (hFv : ∀ t, β ≤ t → F t = 0) :
    innerRecipRatio W e F x B = 0 := by
  rw [innerRecipRatio, innerRecip_eq_zero_of_rpow_le hx he hle hFv, mul_zero, zero_mul]

/-- **The inner sum does not depend on the truncation, above `x^β`.** Raising `B` to `B'` adds the
`f` with `f > B/e ≥ x^β/e`, and those read `F` at `log_x(ef) ≥ β`, where it vanishes. -/
theorem innerRecip_eq_of_rpow_le {x β : ℝ} (hx : 1 < x) {W e B B' : ℕ} (he : 0 < e)
    (hB : x ^ β ≤ (B : ℝ)) (hBB' : B ≤ B') {F : ℝ → ℝ} (hFv : ∀ t, β ≤ t → F t = 0) :
    innerRecip W e F x B' = innerRecip W e F x B := by
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  refine (Finset.sum_subset (fun f hf ↦ ?_) (fun f hf hnf ↦ ?_)).symm
  · rw [mem_coprimeBelow] at hf ⊢
    exact ⟨hf.1, hf.2.1.trans (by gcongr), hf.2.2⟩
  · have hf' := mem_coprimeBelow.mp hf
    have hmul : (B : ℝ) < f * e := (div_lt_iff₀ heR).mp <| not_le.mp fun hc ↦
      hnf (mem_coprimeBelow.mpr ⟨hf'.1, hc, hf'.2.2⟩)
    rw [hFv _ (le_logx_of_rpow_le hx (by nlinarith)), mul_zero, zero_div]

/-- The truncation-independence of `Gap212.Sieve.innerRecip`, symmetrically in the two cutoffs. -/
theorem innerRecip_eq_of_rpow_le_of_rpow_le {x β : ℝ} (hx : 1 < x) {W e B B' : ℕ} (he : 0 < e)
    (hB : x ^ β ≤ (B : ℝ)) (hB' : x ^ β ≤ (B' : ℝ)) {F : ℝ → ℝ}
    (hFv : ∀ t, β ≤ t → F t = 0) :
    innerRecip W e F x B = innerRecip W e F x B' := by
  rcases le_total B B' with hle | hle
  · exact (innerRecip_eq_of_rpow_le hx he hB hle hFv).symm
  · exact innerRecip_eq_of_rpow_le hx he hB' hle hFv

/-- **The normalized inner sum does not depend on the truncation either.** -/
theorem innerRecipRatio_eq_of_rpow_le {x β : ℝ} (hx : 1 < x) {W e B B' : ℕ} (he : 0 < e)
    (hB : x ^ β ≤ (B : ℝ)) (hB' : x ^ β ≤ (B' : ℝ)) {F : ℝ → ℝ}
    (hFv : ∀ t, β ≤ t → F t = 0) :
    innerRecipRatio W e F x B = innerRecipRatio W e F x B' := by
  rw [innerRecipRatio, innerRecipRatio, innerRecip_eq_of_rpow_le_of_rpow_le hx he hB hB' hFv]

/-- **A filtered sum over `[1,B]` collapses to `[1,N]`** when every term above `N` vanishes. -/
theorem sum_filter_Icc_collapse {N B : ℕ} (hNB : N ≤ B) (P : ℕ → Prop) [DecidablePred P]
    {g : ℕ → ℝ} (hg : ∀ e : ℕ, N < e → g e = 0) :
    ∑ e ∈ Icc 1 B with P e, g e = ∑ e ∈ Icc 1 N with P e, g e := by
  refine (Finset.sum_subset (fun e he ↦ ?_) (fun e he hne ↦ hg e ?_)).symm <;>
    simp only [Finset.mem_filter, Finset.mem_Icc] at * <;> grind

/-- Above `⌊x^β⌋` an integer exceeds `x^β`, so the vanishing lemmas apply. -/
theorem rpow_le_of_floor_lt {x β : ℝ} {e : ℕ} (he : ⌊x ^ β⌋₊ < e) : 0 < e ∧ x ^ β ≤ (e : ℝ) :=
  ⟨by omega, (Nat.lt_of_floor_lt he).le⟩

/-- `⌊x^β⌋ ≤ B` whenever `x^β ≤ B`. -/
theorem floor_rpow_le_of_le {x β : ℝ} {B : ℕ} (hB : x ^ β ≤ (B : ℝ)) : ⌊x ^ β⌋₊ ≤ B :=
  Nat.floor_le_of_le hB

/-- Above `⌊x^β⌋` both the normalized inner sum and the predicted derivative vanish. -/
private theorem ratio_deriv_eq_zero_of_floor_lt {x β : ℝ} (hx : 1 < x) {F : ℝ → ℝ}
    (hFv : ∀ t, β ≤ t → F t = 0) (hdF : ∀ t, β ≤ t → deriv F t = 0) {e : ℕ}
    (he : ⌊x ^ β⌋₊ < e) :
    (∀ W B, innerRecipRatio W e F x B = 0) ∧ deriv F (Notation.logx x e) = 0 :=
  have ⟨he0, hle⟩ := rpow_le_of_floor_lt he
  ⟨fun _ _ ↦ innerRecipRatio_eq_zero_of_rpow_le hx he0 hle hFv,
    hdF _ (le_logx_of_rpow_le hx hle)⟩

/-- **The defect statement at the single truncation `B(x) = ⌊x^β⌋+1`.**
`Gap212.Sieve.GramRatioDefectVanishes` quantifies over every `B` with `B(x) ≥ x^β`; this fixes the
smallest admissible one. The profiles are `C^∞`, as in `Gap212.Sieve.GramRatioDefectVanishes`. -/
def GramRatioDefectVanishesAtCut : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → ContDiff ℝ (⊤ : ℕ∞) G →
    HasCompactSupport G →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) → (∀ t, β ≤ t → G t = 0) →
      Filter.Tendsto (fun x : ℝ ↦ mertensKappa x *
          ∑ e ∈ Icc 1 (⌊x ^ β⌋₊ + 1) with Nat.Coprime (W x) e,
            ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
              (innerRecipRatio (W x) e F x (⌊x ^ β⌋₊ + 1)
                  * innerRecipRatio (W x) e G x (⌊x ^ β⌋₊ + 1)
                - deriv F (Notation.logx x e) * deriv G (Notation.logx x e)))
        Filter.atTop (nhds 0)

/-- **The defect statement at one truncation.** `Gap212.Sieve.GramRatioDefectVanishes` is equivalent
to `Gap212.Sieve.GramRatioDefectVanishesAtCut`: given the support hypothesis, the `e`-range above
`⌊x^β⌋` contributes nothing and the inner sums below it do not depend on `B`.

Composed with `Gap212.Sieve.lcmGramSumLimitOfSupport_iff_gramRatioDefectVanishes`, the Gram-sum
limit is equivalent to a statement in the two profiles and `β` alone. -/
theorem gramRatioDefectVanishes_iff_atCut :
    GramRatioDefectVanishes ↔ GramRatioDefectVanishesAtCut := by
  refine ⟨fun h F G hF hFc hG hGc β hβ hFv hGv ↦ h F G hF hFc hG hGc β hβ hFv hGv _
    (.of_forall fun x ↦ by exact_mod_cast (Nat.lt_floor_add_one (x ^ β)).le),
    fun h F G hF hFc hG hGc β hβ hFv hGv B hB ↦ ?_⟩
  have hdF := deriv_eq_zero_of_eventually_zero (hF.of_le (by exact_mod_cast le_top)) hFv
  refine (h F G hF hFc hG hGc β hβ hFv hGv).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), hB] with x hx hBx
  have hcut : x ^ β ≤ ((⌊x ^ β⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.lt_floor_add_one (x ^ β)).le
  have hz : ∀ B' : ℕ, ∀ e : ℕ, ⌊x ^ β⌋₊ < e →
      ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
        (innerRecipRatio (W x) e F x B' * innerRecipRatio (W x) e G x B'
          - deriv F (Notation.logx x e) * deriv G (Notation.logx x e)) = 0 := fun B' e he ↦ by
    simp [ratio_deriv_eq_zero_of_floor_lt hx hFv hdF he]
  rw [sum_filter_Icc_collapse (Nat.le_succ ⌊x ^ β⌋₊) _ (hz _),
    sum_filter_Icc_collapse (floor_rpow_le_of_le hBx) _ (hz _)]
  refine congrArg _ (Finset.sum_congr rfl fun e he ↦ ?_)
  have he0 : 0 < e := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
  rw [innerRecipRatio_eq_of_rpow_le hx he0 hcut hBx hFv,
    innerRecipRatio_eq_of_rpow_le hx he0 hcut hBx hGv]

/-! ## Cauchy–Schwarz against the normalized weight -/

/-- **Cauchy–Schwarz for a nonnegatively weighted sum, with the normalization folded in.** -/
theorem kappa_weighted_cauchy_schwarz {κ : ℝ} (hκ : 0 ≤ κ) {S : Finset ℕ} {w a b : ℕ → ℝ}
    (hw : ∀ e ∈ S, 0 ≤ w e) :
    κ * ∑ e ∈ S, w e * (|a e| * |b e|)
      ≤ Real.sqrt (κ * ∑ e ∈ S, w e * a e ^ 2) * Real.sqrt (κ * ∑ e ∈ S, w e * b e ^ 2) := by
  have hk : ∀ e ∈ S, 0 ≤ κ * w e := fun e he ↦ mul_nonneg hκ (hw e he)
  have hsq : ∀ f : ℕ → ℝ, ∑ e ∈ S, (√(κ * w e) * |f e|) ^ 2 = κ * ∑ e ∈ S, w e * f e ^ 2 :=
    fun f ↦ Finset.mul_sum S _ κ ▸ Finset.sum_congr rfl fun e he ↦ by
      rw [mul_pow, Real.sq_sqrt (hk e he), sq_abs, mul_assoc]
  rw [← hsq, ← hsq, Finset.mul_sum]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun e he ↦ ?_) (Real.sum_mul_le_sqrt_mul_sqrt S _ _)
  rw [mul_mul_mul_comm, Real.mul_self_sqrt (hk e he)]; ring

/-- The `ℓ¹` case: Cauchy–Schwarz against the constant profile `1`. -/
theorem kappa_weighted_abs_le {κ : ℝ} (hκ : 0 ≤ κ) {S : Finset ℕ} {w a : ℕ → ℝ}
    (hw : ∀ e ∈ S, 0 ≤ w e) :
    κ * ∑ e ∈ S, w e * |a e|
      ≤ Real.sqrt (κ * ∑ e ∈ S, w e * a e ^ 2) * Real.sqrt (κ * ∑ e ∈ S, w e) := by
  simpa using kappa_weighted_cauchy_schwarz hκ (a := a) (b := fun _ ↦ (1 : ℝ)) hw

/-- **The bilinear defect is controlled by the two one-profile mean squares and the total mass.**
With `a - p` and `b - q` the quantities and `p, q` their predictions, the exact identity
`(a-p)(b-q) - pq = ab - aq - bp` turns the bilinear defect into three terms, each of which
Cauchy–Schwarz bounds by mean squares. This is the step that decouples the two profiles of
`Gap212.Sieve.GramRatioDefectVanishes`. -/
theorem kappa_weighted_bilinear_defect_le {κ : ℝ} (hκ : 0 ≤ κ) {S : Finset ℕ}
    {w a b p q : ℕ → ℝ} (hw : ∀ e ∈ S, 0 ≤ w e) {MP MQ : ℝ} (hMP0 : 0 ≤ MP) (hMQ0 : 0 ≤ MQ)
    (hMP : ∀ e ∈ S, |p e| ≤ MP) (hMQ : ∀ e ∈ S, |q e| ≤ MQ) :
    κ * ∑ e ∈ S, w e * |(a e - p e) * (b e - q e) - p e * q e|
      ≤ Real.sqrt (κ * ∑ e ∈ S, w e * a e ^ 2) * Real.sqrt (κ * ∑ e ∈ S, w e * b e ^ 2)
        + MQ * (Real.sqrt (κ * ∑ e ∈ S, w e * a e ^ 2) * Real.sqrt (κ * ∑ e ∈ S, w e))
        + MP * (Real.sqrt (κ * ∑ e ∈ S, w e * b e ^ 2) * Real.sqrt (κ * ∑ e ∈ S, w e)) := by
  have hsum : ∑ e ∈ S, w e * |(a e - p e) * (b e - q e) - p e * q e|
      ≤ (∑ e ∈ S, w e * (|a e| * |b e|)) + MQ * ∑ e ∈ S, w e * |a e|
        + MP * ∑ e ∈ S, w e * |b e| := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun e he ↦ ?_
    have h : |(a e - p e) * (b e - q e) - p e * q e|
        ≤ |a e| * |b e| + MQ * |a e| + MP * |b e| := by
      rw [show (a e - p e) * (b e - q e) - p e * q e = a e * b e - a e * q e - b e * p e by ring]
      linarith [abs_sub (a e * b e - a e * q e) (b e * p e), abs_sub (a e * b e) (a e * q e),
        abs_mul (a e) (b e), abs_mul (a e) (q e), abs_mul (b e) (p e),
        mul_le_mul_of_nonneg_left (hMQ e he) (abs_nonneg (a e)),
        mul_le_mul_of_nonneg_left (hMP e he) (abs_nonneg (b e))]
    linarith [mul_le_mul_of_nonneg_left h (hw e he)]
  have c := kappa_weighted_cauchy_schwarz hκ (a := a) (b := b) hw
  linarith [mul_le_mul_of_nonneg_left hsum hκ,
    mul_le_mul_of_nonneg_left (kappa_weighted_abs_le hκ (a := a) hw) hMQ0,
    mul_le_mul_of_nonneg_left (kappa_weighted_abs_le hκ (a := b) hw) hMP0]

/-! ## The one-profile mean square, and the Gram-sum limit from it -/

/-- **The one-profile mean square.** With `a_F(e) = r_F(e) + F'(log_xe)` the defect of the
normalized inner sum against its prediction (`Gap212.Sieve.innerRecipRatio`, whose predicted value
is `-F'(log_xe)`), this asks

  `κ_x·∑_{e≤B,(e,W)=1}(μ²(e)/φ(e))·a_F(e)² ⟶ 0`.

It implies the Gram-sum limit `Gap212.Sieve.LcmGramSumLimitOfSupport`
(`Gap212.Sieve.lcmGramSumLimitOfSupport_of_normalizedInnerRecipL2`) through
`Gap212.Sieve.NormalizedInnerRatioL1`; it is a sufficient condition for
`Gap212.Sieve.GramRatioDefectVanishes`, not an equivalent one, since squaring forbids cancellation
between the `e`'s. The weight is `μ²(e)/φ(e)` and the normalization `κ_x = (W/φ(W))/log x`. -/
def NormalizedInnerRecipL2 : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) →
      ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
        Filter.Tendsto (fun x : ℝ ↦ mertensKappa x *
            ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
              ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
                (innerRecipRatio (W x) e F x (B x) + deriv F (Notation.logx x e)) ^ 2)
          Filter.atTop (nhds 0)

/-- **The mean square gives the weighted `ℓ¹` defect.** Cauchy–Schwarz
against the normalized measure, with the total mass evaluated by
`Gap212.Sieve.tendsto_mertensKappa_mul_weightCut` after the `e`-range collapses to `[1,⌊x^β⌋]`. -/
theorem normalizedInnerRatioL1_of_normalizedInnerRecipL2 (h : NormalizedInnerRecipL2) :
    NormalizedInnerRatioL1 := by
  intro F G hF hFc hG hGc β hβ hFv hGv B hB
  obtain ⟨MF, hMF⟩ := hFc.deriv.exists_bound_of_continuous hF.continuous_deriv_one
  obtain ⟨MG, hMG⟩ := hGc.deriv.exists_bound_of_continuous hG.continuous_deriv_one
  have hdF := deriv_eq_zero_of_eventually_zero hF hFv
  have hdG := deriv_eq_zero_of_eventually_zero hG hGv
  have hA := h F hF hFc β hβ hFv B hB
  have hBl := h G hG hGc β hβ hGv B hB
  have hC := tendsto_mertensKappa_mul_weightCut hβ
  have hglim : Tendsto (fun x : ℝ ↦
      Real.sqrt (mertensKappa x * ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
            (innerRecipRatio (W x) e F x (B x) + deriv F (Notation.logx x e)) ^ 2)
        * Real.sqrt (mertensKappa x * ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
            (innerRecipRatio (W x) e G x (B x) + deriv G (Notation.logx x e)) ^ 2)
      + MG * (Real.sqrt (mertensKappa x * ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
            (innerRecipRatio (W x) e F x (B x) + deriv F (Notation.logx x e)) ^ 2)
        * Real.sqrt (mertensKappa x * mertensWeightCut x β))
      + MF * (Real.sqrt (mertensKappa x * ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
            (innerRecipRatio (W x) e G x (B x) + deriv G (Notation.logx x e)) ^ 2)
        * Real.sqrt (mertensKappa x * mertensWeightCut x β))) atTop (nhds 0) := by
    simpa using ((hA.sqrt.mul hBl.sqrt).add ((hA.sqrt.mul hC.sqrt).const_mul MG)).add
      ((hBl.sqrt.mul hC.sqrt).const_mul MF)
  refine squeeze_zero' ?_ ?_ hglim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (mertensKappa_nonneg hx.le) (Finset.sum_nonneg fun e _ ↦ by positivity)
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hB] with x hx hBx
    have hNB : ⌊x ^ β⌋₊ ≤ B x := floor_rpow_le_of_le hBx
    have hz1 : ∀ e : ℕ, ⌊x ^ β⌋₊ < e →
        ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
          |innerRecipRatio (W x) e F x (B x) * innerRecipRatio (W x) e G x (B x)
            - deriv F (Notation.logx x e) * deriv G (Notation.logx x e)| = 0 := fun e he ↦ by
      simp [ratio_deriv_eq_zero_of_floor_lt hx hFv hdF he]
    have hz2 : ∀ e : ℕ, ⌊x ^ β⌋₊ < e →
        ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
          (innerRecipRatio (W x) e F x (B x) + deriv F (Notation.logx x e)) ^ 2 = 0 := fun e he ↦ by
      simp [ratio_deriv_eq_zero_of_floor_lt hx hFv hdF he]
    have hz3 : ∀ e : ℕ, ⌊x ^ β⌋₊ < e →
        ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
          (innerRecipRatio (W x) e G x (B x) + deriv G (Notation.logx x e)) ^ 2 = 0 := fun e he ↦ by
      simp [ratio_deriv_eq_zero_of_floor_lt hx hGv hdG he]
    rw [sum_filter_Icc_collapse hNB _ hz1, sum_filter_Icc_collapse hNB _ hz2,
      sum_filter_Icc_collapse hNB _ hz3, mertensWeightCut]
    simpa using kappa_weighted_bilinear_defect_le (κ := mertensKappa x)
      (S := {e ∈ Icc 1 ⌊x ^ β⌋₊ | Nat.Coprime (W x) e})
      (w := fun e ↦ ((μ e : ℝ) ^ 2 / (e.totient : ℝ)))
      (a := fun e ↦ innerRecipRatio (W x) e F x (B x) + deriv F (Notation.logx x e))
      (b := fun e ↦ innerRecipRatio (W x) e G x (B x) + deriv G (Notation.logx x e))
      (p := fun e ↦ deriv F (Notation.logx x e)) (q := fun e ↦ deriv G (Notation.logx x e))
      (mertensKappa_nonneg hx.le) (fun e _ ↦ by positivity) ((abs_nonneg _).trans (hMF 0))
      ((abs_nonneg _).trans (hMG 0)) (fun e _ ↦ hMF _) (fun e _ ↦ hMG _)

/-- **The Gram-sum limit `Gap212.Sieve.LcmGramSumLimitOfSupport` from the one-profile mean
square.** -/
theorem lcmGramSumLimitOfSupport_of_normalizedInnerRecipL2 (h : NormalizedInnerRecipL2) :
    LcmGramSumLimitOfSupport :=
  lcmGramSumLimitOfSupport_of_normalizedInnerRatioL1
    (normalizedInnerRatioL1_of_normalizedInnerRecipL2 h)

/-! ## How large the defect is at the top of the `e`-range -/

/-- **A `C¹` profile vanishing from `β` on is at most `‖F'‖_∞·(β-t)` below `β`.** The mean value
inequality between `t` and `β`, where `F` is zero. -/
theorem abs_le_deriv_bound_mul_sub {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) {M : ℝ}
    (hM : ∀ t, |deriv F t| ≤ M) {β : ℝ} (hFv : ∀ t, β ≤ t → F t = 0) {t : ℝ} (ht : t ≤ β) :
    |F t| ≤ M * (β - t) := by
  simpa [Real.norm_eq_abs, hFv β le_rfl, abs_sub_comm t β, abs_of_nonneg (sub_nonneg.2 ht)]
    using (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun u _ ↦ (hF.differentiable (by norm_num)) u)
      (fun u _ ↦ (Real.norm_eq_abs _).symm ▸ hM u) (Set.mem_univ β) (Set.mem_univ t)

/-- **In the one-term regime the normalized inner sum is at most `‖F'‖_∞·log(x^β/e)`.** Where the
inner sum collapses to its `f = 1` term (`Gap212.Sieve.innerRecip_eq_of_primes_dvd`), no
cancellation is available and `r_F(e) = log x·F(log_xe)·φ(eW)/(eW)`. The arithmetic factor is at
most `1`, and the support hypothesis bounds `|F(log_xe)|` by `‖F'‖_∞(β - log_xe)`; multiplying by
`log x` turns that into `log(x^β/e)` exactly. -/
theorem abs_innerRecipRatio_le_of_innerRecip_eq {x β M : ℝ} (hx : 1 < x) {W e B : ℕ}
    (he : 0 < e) {F : ℝ → ℝ} (hone : innerRecip W e F x B = F (Notation.logx x e))
    (hF : ContDiff ℝ 1 F) (hM : ∀ t, |deriv F t| ≤ M) (hFv : ∀ t, β ≤ t → F t = 0)
    (hle : (e : ℝ) ≤ x ^ β) :
    |innerRecipRatio W e F x B| ≤ M * Real.log (x ^ β / (e : ℝ)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have ht : Notation.logx x (e : ℝ) ≤ β := by
    rw [Notation.logx, div_le_iff₀ hlogx, ← Real.log_rpow hx0]
    exact Real.log_le_log heR hle
  have hphi : |(((e * W).totient : ℝ) / ((e * W : ℕ) : ℝ))| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_one_of_le₀ (by exact_mod_cast Nat.totient_le _) (by positivity)
  rw [innerRecipRatio, hone, abs_mul, abs_mul, abs_of_pos hlogx]
  calc Real.log x * |F (Notation.logx x (e : ℝ))|
        * |(((e * W).totient : ℝ) / ((e * W : ℕ) : ℝ))|
      ≤ Real.log x * (M * (β - Notation.logx x (e : ℝ))) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (abs_le_deriv_bound_mul_sub hF hM hFv ht) hlogx.le)
          hphi (abs_nonneg _)
          (mul_nonneg hlogx.le (mul_nonneg ((abs_nonneg _).trans (hM 0)) (by linarith)))
    _ = M * Real.log (x ^ β / (e : ℝ)) := by
      rw [Real.log_div (Real.rpow_pos_of_pos hx0 β).ne' heR.ne', Real.log_rpow hx0, Notation.logx]
      field_simp

/-- **The normalized inner sum at the top of the `e`-range.** For every `e ∈ (B/(z+1), B]` with
`z = ⌊log log log x⌋` — the range where `Gap212.Sieve.innerRecip_eq_of_lt_primorial_bound`
collapses the inner sum to a single term, so that `r_F(e) → -F'(log_xe)` fails there —

  `|r_F(e)| ≤ ‖F'‖_∞·log(z+1)`.

No hypothesis `e ≤ x^β` is needed: above `x^β` the ratio is `0`
(`Gap212.Sieve.innerRecipRatio_eq_zero_of_rpow_le`). This bounds the size of the defect only; the
contribution of the block is `Gap212.Sieve.tendsto_kappa_mul_gramTopSum`. -/
theorem abs_innerRecipRatio_le_log_primorial_bound {x β M : ℝ} (hx : 1 < x) {e B : ℕ}
    (he : 0 < e) (heB : e ≤ B)
    (hzlt : (B : ℝ) / (e : ℝ) < (⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1)
    (hB : x ^ β ≤ (B : ℝ)) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hM : ∀ t, |deriv F t| ≤ M)
    (hFv : ∀ t, β ≤ t → F t = 0) :
    |innerRecipRatio (W x) e F x B|
      ≤ M * Real.log ((⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1) := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM 0)
  rcases le_or_gt (e : ℝ) (x ^ β) with hle | hgt
  · refine (abs_innerRecipRatio_le_of_innerRecip_eq hx he
      (innerRecip_eq_of_lt_primorial_bound he heB hzlt F) hF hM hFv hle).trans ?_
    gcongr
    exact (div_le_div_of_nonneg_right hB (Nat.cast_nonneg _)).trans hzlt.le
  · rw [innerRecipRatio_eq_zero_of_rpow_le hx he hgt.le hFv, abs_zero]
    exact mul_nonneg hM0 (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg _)))

end Gap212.Sieve
