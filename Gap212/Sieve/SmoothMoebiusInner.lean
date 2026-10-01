/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.SmoothNumberSum
public import Gap212.Sieve.OneCoordLcmSelberg

/-!
# The one-variable Möbius bound for the Selberg diagonalisation

`Gap212.Sieve.SmoothMoebiusInnerBound` is the single input of
`Gap212.Sieve.oneCoordLcmDecayAtLevelOfSupport_of_smoothMoebiusInnerBound`, hence of the Selberg
sieving error. It is a theorem: `Gap212.Sieve.smoothMoebiusInnerBound`.

## Where the `\log\log x` goes

Write `y_r = (μ(r)/r)∑_{m,(m,rW)=1}μ(m)F(\log_xr + \log_xm)/m` (`d = rm`; the terms with
`(m,r) > 1` carry `μ(d) = 0`). Summation by parts turns the inner sum into
`-∫_0^∞F'(\log_xr + v)S_{rW}(x^v)dv`, and there the *partial-sum* route stalls: the bound available
at a modulus is `|S_q(w)| ≤ C_q(1 + \log w)^{-1-ε}` with a constant depending on `q`
(`Gap212.Sieve.moebiusPartialSumDecay`), its modulus-uniform form is false
(`Gap212.Sieve.not_uniformMoebiusPartialSumDecay`), and the uniform form one *could* hope for,
`|S_q(w)| ≤ C(q/φ(q))/(1 + \log w)`, gives
`∫_0^{β}dv/(1 + v\log x) = \log(1 + β\log x)/\log x` — the target times `\log\log x`. Sharpening
the exponent there is not available either: at `q` the primorial of `z` and `w = z` the left side
is `1` while `(q/φ(q))(1 + \log z)^{-2} ≍ 1/\log z`, so the `(1 + \log w)^{-2}` form *with* the
`q/φ(q)` factor is itself false.

What the smoothing buys is that the modulus can be removed *before* the integration, by
`Gap212.Sieve.moebiusReciprocalBelow_eq_sum_smoothDivWeight`:

  `S_Q(x^v) = ∑_{b ≤ N₀, b ∣ Q^∞}(1/b)M(x^v/b)`,  `M` the modulus-free partial sum,

after which each `b` contributes `∫_0^∞|M(x^v/b)|dv ≤ C₀/\log x` — the full strength of the
modulus-free `(1 + \log w)^{-2}` rate, with no loss, since the `b`-shift only translates the
integrand — and the `b`-sum is the mass `Q/φ(Q)`
(`Gap212.Sieve.sum_inv_smoothSet_le_self_div_totient`). So the `\log\log x` is not recovered by the
`C¹` profile against a partial-sum bound; it is never lost, because the profile is summed against
the Möbius weight at the modulus-free scale. The `C¹` hypothesis is spent only on `‖F'‖_∞` and the
integration by parts.

`x^β ≤ B` is spent exactly once, and cannot be dropped: it is what makes `min(x^v, B/r) = x^v`
throughout the support of `v ↦ F'(\log_xr + v)`, i.e. what makes the truncation invisible.

## The constant

`C = C₀‖F'‖_∞` with `C₀` the modulus-free Möbius decay constant of
`Gap212.Sieve.exists_moebiusReciprocalBelow_log_sq_decay` at `q = 1`. The denominator `φ(r)` comes
out of `(1/r)(rW/φ(rW)) = (W/φ(W))/φ(r)`, which is an identity and not an estimate — this is the
reciprocal kernel, where the weight is `1/d`; the totient kernel's `1/φ(d)` produces a different
mass and a different denominator, and the two must not be read across.

## Main results

* `Gap212.Sieve.sum_coprimeBelow_mul_profile`: summation by parts with a free shift, modulus and
  truncation.
* `Gap212.Sieve.integrableOn_and_integral_abs_moebiusReciprocalBelow_one`:
  `∫_0^∞|M(x^v/b)|dv ≤ C₀/\log x`.
* `Gap212.Sieve.smoothMoebiusInnerBound`: the one-variable bound.
* `Gap212.Sieve.oneCoordLcmDecayAtLevelOfSupport_three_quarters`: the two-variable estimate.
* `Gap212.Sieve.tendsto_boxPairSum_sub_sievedPairSum`: the sieving error at every `β ≥ 1`.
* `Gap212.Sieve.selbergSievingError`: `Gap212.Sieve.SelbergSievingError m`, at every `m`.

## The range `β ≥ 1`

`Gap212.Sieve.SelbergSievingError m` is stated at `β ≥ 1`, which is what the argument gives, so
`Gap212.Sieve.selbergSievingError` proves it at every `m`, in particular at `m = 44`. With it,
`Gap212.Sieve.nuDenominator_of_lcmGramSumLimitOfSupport` concludes `Gap212.Sieve.NuDenominator 45`
from `Gap212.Sieve.LcmGramSumLimitOfSupport` alone.

The two-variable estimate is fed the profiles' support clause, which the retreat condition supplies
only from `1` on (`Gap212.Sieve.tendsto_boxPairSum_sub_sievedPairSum_of_support`). At `β < 1` a
truncation `B ≍ x^β` cuts a retreated profile's support, the top block of moduli survives
uncancelled, and the one-coordinate sums are `≍φ(W)/W` rather than `≍1/B_x`
(`Gap212.Sieve.not_oneCoordLcmDecayAtLevel`).
-/

@[expose] public section

open ArithmeticFunction Filter Gap212.Defs Gap212.GPY MeasureTheory Real Set
open scoped ArithmeticFunction.Moebius

namespace Gap212.Sieve

/-! ## The derivative of a profile that vanishes from `β` on -/

/-- A `C¹` profile vanishing on `[β,∞)` has vanishing derivative on `[β,∞)` — at `β` itself too,
which is where continuity of `F'` is used. This is what confines the `v`-integration of the
summation by parts to `v < β - \log_xr`. -/
theorem deriv_eq_zero_of_profile_vanishes {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) {β : ℝ}
    (hFβ : ∀ t : ℝ, β ≤ t → F t = 0) {t : ℝ} (ht : β ≤ t) : deriv F t = 0 := by
  have hgt : ∀ s : ℝ, β < s → deriv F s = 0 := fun s hs ↦ by
    rw [(eventuallyEq_of_mem (Ioi_mem_nhds hs) fun u hu ↦ hFβ u (le_of_lt hu) :
      F =ᶠ[nhds s] fun _ ↦ 0).deriv_eq, deriv_const]
  rcases ht.eq_or_lt with rfl | h
  · exact tendsto_nhds_unique (f := deriv F) (l := nhdsWithin β (Ioi β))
      (((hF.continuous_deriv le_rfl).tendsto β).mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun u hu ↦ (hgt u hu).symm))
  · exact hgt t h

/-! ## Summation by parts with a free shift, modulus and truncation -/

/-- **Partial summation, with the shift, the modulus and the truncation independent.** For `F` of
class `C¹` with compact support and `x > 1`,

  `∑_{f ≤ y, (f,q)=1} g(f)F(c + \log_xf) = -∫_0^∞F'(c + v)∑_{f ≤ min(x^v,y), (f,q)=1}g(f)dv`.

`Gap212.Sieve.truncated_partial_summation_weighted` is the case `c = \log_xe`, `y = B/e`, `q = e`,
where one symbol plays all three roles; the Selberg diagonalisation needs them separate, because
the modulus of the inner sum is `rW(x)` while the shift and the truncation are those of `r`. The
proof is the same: `F(c + \log_xf) = -∫_{\log_xf}^∞F'(c + v)dv` term by term, and the translation
`u = c + v` has no Jacobian. -/
theorem sum_coprimeBelow_mul_profile {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    {x : ℝ} (hx : 1 < x) (q : ℕ) (c y : ℝ) (g : ℕ → ℝ) :
    ∑ f ∈ coprimeBelow q y, g f * F (c + Notation.logx x f)
      = -∫ v in Ioi (0 : ℝ), deriv F (c + v) * ∑ f ∈ coprimeBelow q (min (x ^ v) y), g f := by
  have hsum : ∀ v : ℝ, deriv F (c + v) * ∑ f ∈ coprimeBelow q (min (x ^ v) y), g f
      = ∑ f ∈ coprimeBelow q y, (Ici (Notation.logx x f)).indicator
          (fun v ↦ g f * deriv F (c + v)) v := by
    intro v
    rw [sum_coprimeBelow_min, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f hf ↦ ?_
    have hf0 : (0 : ℝ) < f := by exact_mod_cast Nat.pos_of_ne_zero (mem_coprimeBelow.mp hf).1
    simp only [Set.indicator_apply, mem_Ici, logx_eq_logb, Real.logb_le_iff_le_rpow hx hf0]
    split_ifs <;> ring
  have hcont : Continuous fun v : ℝ ↦ deriv F (c + v) :=
    (hF.continuous_deriv le_rfl).comp (continuous_const.add continuous_id)
  have hdcs : HasCompactSupport fun v : ℝ ↦ deriv F (c + v) := by
    simpa [Function.comp_def] using hFc.deriv.comp_homeomorph (Homeomorph.addLeft c)
  have hint : ∀ f ∈ coprimeBelow q y, IntegrableOn
      ((Ici (Notation.logx x f)).indicator fun v ↦ g f * deriv F (c + v)) (Ici (0 : ℝ)) :=
    fun f _ ↦ (((hcont.integrable_of_hasCompactSupport hdcs).const_mul (g f)).indicator
      measurableSet_Ici).integrableOn
  have hexch : ∫ v in Ici (0 : ℝ), deriv F (c + v)
        * ∑ f ∈ coprimeBelow q (min (x ^ v) y), g f
      = ∑ f ∈ coprimeBelow q y, ∫ v in Ici (0 : ℝ),
          (Ici (Notation.logx x f)).indicator (fun v ↦ g f * deriv F (c + v)) v := by
    simp_rw [hsum]
    exact integral_finsetSum _ hint
  have hterm : ∀ f ∈ coprimeBelow q y, (∫ v in Ici (0 : ℝ),
        (Ici (Notation.logx x f)).indicator (fun v ↦ g f * deriv F (c + v)) v)
      = -(g f * F (c + Notation.logx x f)) := by
    intro f hf
    have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast Nat.pos_of_ne_zero (mem_coprimeBelow.mp hf).1
    have hf0 : 0 ≤ Notation.logx x f := div_nonneg (Real.log_nonneg hf1) (Real.log_pos hx).le
    rw [setIntegral_indicator measurableSet_Ici, Ici_inter_Ici, max_eq_right hf0,
      ← setIntegral_congr_set (Ioi_ae_eq_Ici (a := Notation.logx x f)),
      integral_const_mul, integral_Ioi_deriv_comp_const_add hF hFc]
    ring
  rw [setIntegral_congr_set Ioi_ae_eq_Ici, hexch, Finset.sum_congr rfl hterm,
    Finset.sum_neg_distrib, neg_neg]

/-! ## The modulus-free Möbius integral -/

/-- Below `1` the truncated Möbius sum is empty. -/
theorem moebiusReciprocalBelow_eq_zero_of_lt_one (q : ℕ) {t : ℝ} (ht : t < 1) :
    moebiusReciprocalBelow q t = 0 := by
  simp [moebiusReciprocalBelow, coprimeBelow, Nat.floor_eq_zero.mpr ht]

/-- The elementary majorant of the shifted decay, integrated: for `L > 0`,
`∫_{v₀}^∞C₀(1 + (v - v₀)L)^{-2}dv = C₀/L`, and the integrand is integrable there. The whole point
is the exponent `2`: at exponent `1` this integral diverges, which is the `\log\log x` the
partial-sum route loses. -/
theorem integrableOn_and_integral_shifted_majorant {L C₀ : ℝ} (hL : 0 < L) (hC₀ : 0 ≤ C₀)
    (v₀ : ℝ) :
    IntegrableOn (fun v ↦ C₀ / (1 + (v - v₀) * L) ^ 2) (Ioi v₀) volume
      ∧ ∫ v in Ioi v₀, C₀ / (1 + (v - v₀) * L) ^ 2 = C₀ / L := by
  set G : ℝ → ℝ := fun v ↦ -(C₀ / L) * (1 + (v - v₀) * L)⁻¹ with hG
  have hderiv : ∀ v ∈ Ici v₀, HasDerivAt G (C₀ / (1 + (v - v₀) * L) ^ 2) v := by
    intro v (hv : v₀ ≤ v)
    have hu : 0 < 1 + (v - v₀) * L := by nlinarith
    have h1 : HasDerivAt (fun v : ℝ ↦ 1 + (v - v₀) * L) L v := by
      simpa using (((hasDerivAt_id v).sub_const v₀).mul_const L).const_add (1 : ℝ)
    refine ((h1.inv hu.ne').const_mul (-(C₀ / L))).congr_deriv ?_
    field_simp
  have htend : Tendsto G atTop (nhds 0) := by
    have h1 : Tendsto (fun v : ℝ ↦ 1 + (v - v₀) * L) atTop atTop :=
      tendsto_atTop_add_const_left _ 1
        ((tendsto_atTop_add_const_right _ (-v₀) tendsto_id).atTop_mul_const hL)
    simpa [hG] using h1.inv_tendsto_atTop.const_mul (-(C₀ / L))
  have hpos : ∀ v ∈ Ioi v₀, 0 ≤ C₀ / (1 + (v - v₀) * L) ^ 2 := fun _ _ ↦ by positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htend, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos htend, hG]
  simp

/-- **The modulus-free Möbius sum, integrated against the scale.** With `C₀` the constant of
`Gap212.Sieve.exists_moebiusReciprocalBelow_log_sq_decay` at `q = 1` and any `b ≥ 1`,

  `∫_0^∞|M(x^v/b)|dv ≤ C₀/\log x`,

and the integrand is integrable. The shift by `b` is harmless: `M` vanishes below `1`, so the
integral is the same as at `b = 1` after a translation — which is exactly why the smooth-number
decomposition costs nothing beyond the mass `∑_b1/b`. -/
theorem integrableOn_and_integral_abs_moebiusReciprocalBelow_one {x : ℝ} (hx : 1 < x) {C₀ : ℝ}
    (hM : ∀ w : ℝ, 1 ≤ w → |moebiusReciprocalBelow 1 w| ≤ C₀ / (1 + Real.log w) ^ 2)
    {b : ℕ} (hb : 1 ≤ b) :
    IntegrableOn (fun v ↦ |moebiusReciprocalBelow 1 (x ^ v / b)|) (Ioi (0 : ℝ)) volume
      ∧ ∫ v in Ioi (0 : ℝ), |moebiusReciprocalBelow 1 (x ^ v / b)| ≤ C₀ / Real.log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hC₀ : 0 ≤ C₀ := by simpa using (abs_nonneg _).trans (hM 1 le_rfl)
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  set v₀ : ℝ := Real.log b / Real.log x with hv₀
  have hv₀0 : 0 ≤ v₀ := div_nonneg (Real.log_nonneg hbR) hL.le
  set maj : ℝ → ℝ := (Ici v₀).indicator fun v ↦ C₀ / (1 + (v - v₀) * Real.log x) ^ 2 with hmaj
  obtain ⟨hmajint, hmajval⟩ := integrableOn_and_integral_shifted_majorant hL hC₀ v₀
  have hbpos : (0 : ℝ) < b := by linarith
  have hxv₀ : x ^ v₀ = b := Real.rpow_logb hx0 hx.ne' hbpos
  -- the pointwise majorisation
  have hle : ∀ v : ℝ, |moebiusReciprocalBelow 1 (x ^ v / b)| ≤ maj v := by
    intro v
    rcases lt_or_ge v v₀ with hv | hv
    · have hlt : x ^ v / b < 1 := by
        rw [div_lt_one hbpos, ← hxv₀]
        exact Real.rpow_lt_rpow_of_exponent_lt hx hv
      rw [moebiusReciprocalBelow_eq_zero_of_lt_one 1 hlt, abs_zero, hmaj]
      exact Set.indicator_apply_nonneg fun _ ↦ by positivity
    · have hge : (1 : ℝ) ≤ x ^ v / b := by
        rw [one_le_div hbpos, ← hxv₀]
        exact Real.rpow_le_rpow_of_exponent_le hx.le hv
      have hlogdiv : Real.log (x ^ v / b) = (v - v₀) * Real.log x := by
        rw [Real.log_div (by positivity) hbpos.ne', Real.log_rpow hx0, hv₀]
        field_simp
      rw [hmaj, Set.indicator_of_mem (Set.mem_Ici.mpr hv), ← hlogdiv]
      exact hM _ hge
  have hmeas : Measurable fun v : ℝ ↦ |moebiusReciprocalBelow 1 (x ^ v / b)| :=
    ((measurable_moebiusReciprocalBelow 1).comp
      ((Real.continuous_const_rpow hx0.ne').measurable.div_const _)).abs
  have hmajIntegrable : Integrable maj volume :=
    (hmajint.congr_set_ae Ioi_ae_eq_Ici.symm).integrable_indicator measurableSet_Ici
  refine ⟨hmajIntegrable.integrableOn.mono' hmeas.aestronglyMeasurable
    (.of_forall fun v ↦ by simpa using hle v), (integral_mono_of_nonneg
    (.of_forall fun v ↦ abs_nonneg _) hmajIntegrable.integrableOn (.of_forall hle)).trans ?_⟩
  calc ∫ v in Ioi (0 : ℝ), maj v ≤ ∫ v, maj v := setIntegral_le_integral hmajIntegrable
        (.of_forall fun _ ↦ Set.indicator_apply_nonneg fun _ ↦ by positivity)
    _ = C₀ / Real.log x := by
      rw [hmaj, integral_indicator measurableSet_Ici, ← setIntegral_congr_set Ioi_ae_eq_Ici,
        hmajval]

/-! ## The inner sum after `d = rm` -/

/-- **The inner Möbius sum in the shifted coprime form.** For `r ≥ 1` squarefree and coprime to
`W(x)`,

  `y_r = (μ(r)/r)∑_{f ≤ B/r, (f,rW)=1}(μ(f)/f)F(\log_xr + \log_xf)`.

Writing `d = rf`, the terms of `y_r` with `(f,r) > 1` carry a non-squarefree `d` and vanish, so the
sum over the box is the sum over the `f` coprime to `rW(x)` — where the modulus is `rW(x)` but the
shift and the truncation are those of `r` alone. -/
theorem innerMoebiusSum_eq_mul_sum_coprimeBelow {x : ℝ} {F : ℝ → ℝ} {B r : ℕ} (hr1 : 1 ≤ r)
    (hrsf : Squarefree r) (hrW : Nat.Coprime (W x) r) :
    innerMoebiusSum x F B r
      = (μ r : ℝ) / (r : ℝ) * ∑ f ∈ coprimeBelow (r * W x) ((B : ℝ) / (r : ℝ)),
          (μ f : ℝ) / (f : ℝ) * F (Notation.logx x r + Notation.logx x f) := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr1
  set S : Finset ℕ := coprimeBelow (r * W x) ((B : ℝ) / (r : ℝ))
  have hterm : ∀ f ∈ S, (μ (r * f) : ℝ) * F (Notation.logx x ((r * f : ℕ) : ℝ)) / ((r * f : ℕ) : ℝ)
      = (μ r : ℝ) / (r : ℝ) *
        ((μ f : ℝ) / (f : ℝ) * F (Notation.logx x r + Notation.logx x f)) := by
    intro f hf
    obtain ⟨hf0, -, hfcop⟩ := mem_coprimeBelow.mp hf
    have hfR : (0 : ℝ) < f := by exact_mod_cast Nat.pos_of_ne_zero hf0
    rw [isMultiplicative_moebius.map_mul_of_coprime (Nat.coprime_mul_iff_right.mp hfcop).1.symm]
    simp only [Notation.logx, Nat.cast_mul, Int.cast_mul, Real.log_mul hrR.ne' hfR.ne', add_div]
    field_simp
  rw [innerMoebiusSum, Finset.mul_sum, ← Finset.sum_congr rfl hterm,
    ← Finset.sum_image (f := fun d ↦ (μ d : ℝ) * F (Notation.logx x d) / (d : ℝ))
      fun _ _ _ _ h ↦ Nat.eq_of_mul_eq_mul_left hr1 h]
  refine (Finset.sum_subset ?_ fun d hd hdn ↦ ?_).symm
  · rintro _ hd
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hf0, hfB, hfcop⟩ := mem_coprimeBelow.mp hf
    refine Finset.mem_filter.mpr ⟨mem_wBox.mpr ⟨⟨Nat.mul_pos hr1 (Nat.pos_of_ne_zero hf0), ?_⟩,
      hrW.mul_right (Nat.coprime_mul_iff_right.mp hfcop).2.symm⟩, dvd_mul_right r f⟩
    exact_mod_cast (le_div_iff₀' hrR).mp hfB
  obtain ⟨hdbox, m, rfl⟩ := Finset.mem_filter.mp hd
  obtain ⟨⟨hd1, hdB⟩, hdW⟩ := mem_wBox.mp hdbox
  have hm0 : m ≠ 0 := by rintro rfl; omega
  have hmr : ¬ Nat.Coprime m r := fun hcop ↦ hdn (Finset.mem_image.mpr ⟨m,
    mem_coprimeBelow.mpr ⟨hm0, (le_div_iff₀' hrR).mpr (by exact_mod_cast hdB),
      hcop.mul_right (hdW.coprime_dvd_right (dvd_mul_left m r)).symm⟩, rfl⟩)
  obtain ⟨p, hp, hpm, hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp hmr
  rw [moebius_eq_zero_of_not_squarefree fun h ↦ hp.not_isUnit (h p (mul_dvd_mul hpr hpm))]
  simp

/-! ## The one-variable input, proved -/

/-- **The shifted coprime Möbius sum against a profile.** If `F` is `C¹`, compactly supported and
vanishes on `[β,∞)`, `‖F'‖ ≤ D`, and `C₀` is a modulus-free Möbius decay constant, then for
`x > 1`, `Q ≠ 0` and a truncation `y ≥ x^{β - c}`,

  `|∑_{f ≤ y, (f,Q)=1}(μ(f)/f)F(c + \log_xf)| ≤ DC₀(Q/φ(Q))/\log x`. -/
theorem abs_sum_coprimeBelow_moebius_mul_profile_le {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {β : ℝ} (hFβ : ∀ t : ℝ, β ≤ t → F t = 0) {D : ℝ}
    (hD : ∀ t, ‖deriv F t‖ ≤ D) {C₀ : ℝ}
    (hC₀ : ∀ w : ℝ, 1 ≤ w → |moebiusReciprocalBelow 1 w| ≤ C₀ / (1 + Real.log w) ^ 2)
    {x : ℝ} (hx1 : 1 < x) {Q : ℕ} (hQ0 : Q ≠ 0) (c y : ℝ) (hy : x ^ (β - c) ≤ y) :
    |∑ f ∈ coprimeBelow Q y, (μ f : ℝ) / (f : ℝ) * F (c + Notation.logx x f)|
      ≤ D * C₀ * ((Q : ℝ) / (Q.totient : ℝ)) / Real.log x := by
  have hC₀0 : 0 ≤ C₀ := by simpa using (abs_nonneg _).trans (hC₀ 1 le_rfl)
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  set N₀ : ℕ := ⌊y⌋₊
  have habel := sum_coprimeBelow_mul_profile hF hFc hx1 Q c y (fun f ↦ (μ f : ℝ) / (f : ℝ))
  have hint : ∀ b ∈ Finset.Ioc 0 N₀, _ := fun b hb ↦
    integrableOn_and_integral_abs_moebiusReciprocalBelow_one hx1 hC₀ (Finset.mem_Ioc.mp hb).1
  have hbint : ∀ b ∈ Finset.Ioc 0 N₀,
      IntegrableOn (fun v ↦ smoothDivWeight Q b * |moebiusReciprocalBelow 1 (x ^ v / b)|)
        (Ioi (0 : ℝ)) volume := fun b hb ↦ (hint b hb).1.const_mul _
  -- the pointwise majorant
  have hmajor : ∀ v ∈ Ioi (0 : ℝ),
      |deriv F (c + v) * moebiusReciprocalBelow Q (min (x ^ v) y)|
        ≤ D * ∑ b ∈ Finset.Ioc 0 N₀,
            smoothDivWeight Q b * |moebiusReciprocalBelow 1 (x ^ v / b)| := by
    intro v _
    rcases le_or_gt β (c + v) with hvβ | hvβ
    · rw [deriv_eq_zero_of_profile_vanishes hF hFβ hvβ, zero_mul, abs_zero]
      exact mul_nonneg hD0
        (Finset.sum_nonneg fun b _ ↦ mul_nonneg (smoothDivWeight_nonneg Q b) (abs_nonneg _))
    -- inside the support: the truncation is invisible
    have hxvy : x ^ v ≤ y :=
      (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)).trans hy
    rw [min_eq_left hxvy,
      moebiusReciprocalBelow_eq_sum_smoothDivWeight hQ0 (Nat.floor_le_floor hxvy), abs_mul]
    refine mul_le_mul (by simpa using hD (c + v)) ((Finset.abs_sum_le_sum_abs _ _).trans_eq
      (Finset.sum_congr rfl fun b _ ↦ ?_)) (abs_nonneg _) hD0
    rw [abs_mul, abs_of_nonneg (smoothDivWeight_nonneg Q b)]
  have hmass : ∑ b ∈ Finset.Ioc 0 N₀, smoothDivWeight Q b ≤ (Q : ℝ) / (Q.totient : ℝ) := by
    refine Eq.trans_le ?_ (sum_inv_smoothSet_le_self_div_totient hQ0 N₀)
    rw [smoothSet, Finset.sum_filter]
    refine Finset.sum_congr ?_ fun b _ ↦ rfl
    ext b
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [habel, abs_neg]
  calc _ ≤ ∫ v in Ioi (0 : ℝ), D * ∑ b ∈ Finset.Ioc 0 N₀,
          smoothDivWeight Q b * |moebiusReciprocalBelow 1 (x ^ v / b)| :=
        abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
          (.of_forall fun v ↦ abs_nonneg _) ((integrable_finsetSum _ hbint).const_mul _)
          ((ae_restrict_mem measurableSet_Ioi).mono hmajor))
    _ ≤ D * ∑ b ∈ Finset.Ioc 0 N₀, smoothDivWeight Q b * (C₀ / Real.log x) := by
        rw [integral_const_mul, integral_finsetSum _ hbint]
        gcongr with b hb
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hint b hb).2 (smoothDivWeight_nonneg Q b)
    _ ≤ D * ((Q : ℝ) / (Q.totient : ℝ) * (C₀ / Real.log x)) := by
        rw [← Finset.sum_mul]
        gcongr
    _ = _ := by ring

/-- **`Gap212.Sieve.SmoothMoebiusInnerBound` is a theorem.** For every `C¹` profile `F` vanishing
on `[β,∞)` there is a `C` — namely `C₀‖F'‖_∞` — with

  `|∑_{d ≤ B, (d,W)=1, r ∣ d}μ(d)F(\log_xd)/d| ≤ C(W/φ(W))/(φ(r)\log x)`

for every large `x`, every `B ≥ x^β` and every `r ≥ 1`.

The proof is four steps and no analysis beyond the modulus-free Möbius rate. The moduli that are
not squarefree or not coprime to `W(x)` give `y_r = 0`. For the rest,
`Gap212.Sieve.innerMoebiusSum_eq_mul_sum_coprimeBelow` writes `d = rf`, and
`Gap212.Sieve.sum_coprimeBelow_mul_profile` integrates by parts at the modulus `Q = rW(x)`. In the
support of `v ↦ F'(\log_xr + v)` one has `v < β - \log_xr`, hence `x^v < x^β/r ≤ B/r`, so the
truncation is invisible — this is the one place `x^β ≤ B` is spent. Then
`Gap212.Sieve.moebiusReciprocalBelow_eq_sum_smoothDivWeight` replaces `S_Q(x^v)` by the
modulus-free `M(x^v/b)` against the mass `∑_{b ∣ Q^∞}1/b ≤ Q/φ(Q)`, each term contributing
`C₀/\log x` by `Gap212.Sieve.integrableOn_and_integral_abs_moebiusReciprocalBelow_one`. The
`(1/r)(Q/φ(Q)) = (W/φ(W))/φ(r)` at the end is an identity, `φ` being multiplicative on the coprime
pair `(r, W(x))`: the `φ(r)` of the statement is not an estimate but the mass of the smooth numbers
divided by `r`. -/
theorem smoothMoebiusInnerBound : SmoothMoebiusInnerBound := by
  classical
  intro β hβ F hF hFc hFβ
  obtain ⟨C₀, hC₀⟩ := exists_moebiusReciprocalBelow_log_sq_decay (q := 1) le_rfl
  have hC₀0 : 0 ≤ C₀ := by simpa using (abs_nonneg _).trans (hC₀ 1 le_rfl)
  obtain ⟨D, hD⟩ := hFc.deriv.exists_bound_of_continuous (hF.continuous_deriv le_rfl)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  refine ⟨C₀ * D, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx1
  intro B r hB hr1
  have hx0 : (0 : ℝ) < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hW0 : 0 < W x := primorial_pos _
  have hφW : (0 : ℝ) < (W x).totient := by exact_mod_cast Nat.totient_pos.mpr hW0
  have hφr : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr hr1
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr1
  by_cases hrsf : Squarefree r; swap
  · rw [innerMoebiusSum_eq_zero_of_not_squarefree hrsf, abs_zero]
    positivity
  by_cases hrW : Nat.Coprime (W x) r; swap
  · rw [innerMoebiusSum_eq_zero_of_not_coprime hrW, abs_zero]
    positivity
  set Q : ℕ := r * W x with hQ
  set c : ℝ := Notation.logx x r with hc
  set y : ℝ := (B : ℝ) / (r : ℝ)
  have hQ0 : Q ≠ 0 := Nat.mul_ne_zero (by omega) hW0.ne'
  have hxc : x ^ c = r := by
    rw [hc, logx_eq_logb]
    exact Real.rpow_logb hx0 hx1.ne' hrR
  have hintbound :=
    abs_sum_coprimeBelow_moebius_mul_profile_le hF hFc hFβ hD hC₀ hx1 hQ0 c y (by
      rw [Real.rpow_sub hx0, hxc]; exact div_le_div_of_nonneg_right hB hrR.le)
  -- assemble
  rw [innerMoebiusSum_eq_mul_sum_coprimeBelow hr1 hrsf hrW, abs_mul]
  have habsmu : |(μ r : ℝ) / (r : ℝ)| ≤ 1 / (r : ℝ) := by
    rw [abs_div, abs_of_pos hrR]
    gcongr
    exact_mod_cast abs_moebius_le_one
  calc _ ≤ 1 / (r : ℝ) * (D * C₀ * ((Q : ℝ) / (Q.totient : ℝ)) / Real.log x) :=
        mul_le_mul habsmu hintbound (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [hQ, Nat.totient_mul hrW.symm]
      push_cast
      field_simp

/-! ## The chain to the sieving error -/

/-- **`Gap212.Sieve.OneCoordLcmDecayAtLevelOfSupport (3/4)` holds**:
`Gap212.Sieve.oneCoordLcmDecayAtLevelOfSupport_of_smoothMoebiusInnerBound` applied to
`Gap212.Sieve.smoothMoebiusInnerBound`. -/
theorem oneCoordLcmDecayAtLevelOfSupport_three_quarters :
    OneCoordLcmDecayAtLevelOfSupport (3 / 4) :=
  oneCoordLcmDecayAtLevelOfSupport_of_smoothMoebiusInnerBound smoothMoebiusInnerBound

/-- **The Selberg sieving error at every `β ≥ 1`.** For retreated profiles and a truncation
`B(x) ≥ x^β` with `β ≥ 1`,

  `B_x^{m+1}(Σ^{box}_x - Σ^{sv}_x) → 0`,

which is the content of `Gap212.Sieve.SelbergSievingError m`. -/
theorem tendsto_boxPairSum_sub_sievedPairSum (p : SupportParams) {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) {m : ℕ}
    {j j' : Fin p.n} (F G : Fin (m + 1) → ℝ → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    (hFc : ∀ i, HasCompactSupport (F i)) (hG : ∀ i, ContDiff ℝ 1 (G i))
    (hGc : ∀ i, HasCompactSupport (G i)) (hsupp : IsRetreatedPair p (m + 1) j j' ε₀ F G)
    {β : ℝ} (hβ1 : 1 ≤ β) (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦ (((W x).totient : ℝ) / (W x : ℝ) * Real.log x) ^ (m + 1) *
        (boxPairSum x (B x) F G - sievedPairSum x (B x) F G)) atTop (nhds 0) :=
  tendsto_boxPairSum_sub_sievedPairSum_of_smoothMoebiusInnerBound smoothMoebiusInnerBound p hε₀ F G
    hF hFc hG hGc hsupp hβ1 B hB

/-- **`Gap212.Sieve.SelbergSievingError m` holds, at every `m`.**
`Gap212.Sieve.tendsto_boxPairSum_sub_sievedPairSum` is exactly its conclusion, at every `β ≥ 1`. -/
@[gap212 "lem_selberg_sieving_error"]
theorem selbergSievingError (m : ℕ) : SelbergSievingError m :=
  fun p _ε₀ hε₀ _ _j _j' F G hF hFc hG hGc hsupp _β hβ1 B hB ↦
    tendsto_boxPairSum_sub_sievedPairSum p hε₀.le F G hF hFc hG hGc hsupp hβ1 B hB

end Gap212.Sieve
