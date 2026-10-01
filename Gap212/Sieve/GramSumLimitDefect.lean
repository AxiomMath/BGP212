/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.SelbergMainTerm
public import Gap212.Sieve.DivisorSumOverQstar

/-!
# The Gram-sum limits without a support hypothesis are false

`Gap212.Sieve.LcmGramSumLimit` (`Gap212.Sieve.SelbergMainTerm`) and
`Gap212.Sieve.TotientGramSumLimit` (`Gap212.Sieve.DivisorSumOverQstar`) quantify over the profiles
`F, G` and over the truncation `B ≥ x^β` independently. Both Gram sums read the profiles only at
`\log_x(ef)` with `e ≤ B` and `ef ≤ B` (`Gap212.Sieve.innerRecip`, `Gap212.Sieve.innerTotient`), so
they depend on `F` and `G` only through their restriction to `[0,\log_xB]`, while the asserted limit
`∫₀^∞F'G'` sees all of them. A profile supported above `\log_xB` makes the whole sum vanish while
the target integral does not.

`Gap212.Sieve.not_lcmGramSumLimit` refutes the first, in `Gap212.Sieve.SelbergMainTerm`;
`Gap212.Sieve.not_totientGramSumLimit` refutes the second. Both use the witness `β = 1`,
`B(x) = ⌊x⌋+1` — which satisfies `x^β ≤ B(x)` for every `x` — and
`F = G = Gap212.Sieve.gramCexProfile`, a bump supported in `(2,4)`, whose derivative has support in
`[2,4] ⊆ (0,∞)` so that `∫₀^∞(F')² > 0` (`Gap212.Sieve.integral_deriv_gramCexProfile_sq_pos`).

The forms with the support hypothesis, in which the profiles vanish from `β` on so that the
truncation reaches past their support, are `Gap212.Sieve.LcmGramSumLimitOfSupport` and
`Gap212.Sieve.TotientGramSumLimitOfSupport`. These are stated for `C^∞` profiles
(`ContDiff ℝ (⊤ : ℕ∞)`), the regularity of Polymath8b, Lemma 4.1, rather than for `C¹` ones; every
profile they are applied to comes from `Gap212.GPY.TensorDatum.smooth`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY MeasureTheory
open scoped ArithmeticFunction.Moebius

/-- **The totient-weight inner sum vanishes when the truncation does not reach the profile's
support.** The companion of `Gap212.Sieve.innerRecip_eq_zero_of_profile_vanishing`: every term of
`Gap212.Sieve.innerTotient` is read at `\log_x(ef)` with `ef ≤ B`, hence at an argument at most
`\log_xB ≤ c`, where `F` vanishes. -/
theorem innerTotient_eq_zero_of_profile_vanishing {x : ℝ} (hx : 1 < x) {B e W : ℕ} {c : ℝ}
    (hB : Real.log (B : ℝ) ≤ c * Real.log x) {F : ℝ → ℝ} (hF : ∀ u ≤ c, F u = 0) :
    innerTotient W e F x B = 0 := by
  classical
  refine Finset.sum_eq_zero fun f hf => ?_
  obtain ⟨hf1, hfle⟩ := mem_Icc.mp (mem_filter.mp hf).1
  have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; rw [Nat.div_zero] at hfle; omega)
  have hefR : (e : ℝ) * f ≤ B := by
    rw [mul_comm]; exact_mod_cast (Nat.le_div_iff_mul_le he0).mp hfle
  have hle : Notation.logx x ((e : ℝ) * (f : ℝ)) ≤ c := by
    rw [Notation.logx, div_le_iff₀ (Real.log_pos hx)]
    exact (Real.log_le_log (mul_pos (by exact_mod_cast he0) (by exact_mod_cast hf1)) hefR).trans hB
  rw [hF _ hle, mul_zero, zero_div]

/-- **The totient-weight Gram sum vanishes when the truncation does not reach the profile's
support**: every `e`-term carries the inner sum of `F` as a factor. -/
theorem gramSumTotient_eq_zero_of_profile_vanishing {x : ℝ} (hx : 1 < x) {B W : ℕ} {c : ℝ}
    (hB : Real.log (B : ℝ) ≤ c * Real.log x) {F G : ℝ → ℝ} (hF : ∀ u ≤ c, F u = 0) :
    gramSumTotient W B x F G = 0 := by
  classical
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [innerTotient_eq_zero_of_profile_vanishing hx hB hF, zero_mul, mul_zero]

/-- **`Gap212.Sieve.TotientGramSumLimit` is false**, by the same witness that refutes
`Gap212.Sieve.LcmGramSumLimit`: at `β = 1`, `B(x) = ⌊x⌋+1` and `F = G` a bump supported in `(2,4)`,
the normalized Gram sum is identically `0` for `x ≥ 2` — every argument `\log_x(ef)` is at most
`2`, since `ef ≤ B(x) ≤ x²` — so it tends to `0`, while the asserted limit `∫₀^∞(F')²` is
positive. -/
theorem not_totientGramSumLimit : ¬ TotientGramSumLimit := by
  intro h
  have hBge : ∀ᶠ x : ℝ in atTop, x ^ (1 : ℝ) ≤ ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
    filter_upwards with x
    rw [Real.rpow_one]
    exact_mod_cast (Nat.lt_floor_add_one x).le
  have hlim := h gramCexProfile gramCexProfile gramCexProfile_contDiff_one
    gramCexProfile_hasCompactSupport gramCexProfile_contDiff_one
    gramCexProfile_hasCompactSupport 1 one_pos (fun x => ⌊x⌋₊ + 1) hBge
  have hzero : (fun x : ℝ ↦ ((W x).totient : ℝ) / (W x : ℝ) * Real.log x *
        gramSumTotient (W x) (⌊x⌋₊ + 1) x gramCexProfile gramCexProfile)
      =ᶠ[atTop] fun _ ↦ (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx1 : (1 : ℝ) < x := by linarith
    have hfl : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hB : Real.log (((⌊x⌋₊ + 1 : ℕ) : ℝ)) ≤ 2 * Real.log x := by
      rw [← Real.log_rpow (by linarith), Real.rpow_two]
      exact Real.log_le_log (by positivity) (by push_cast; nlinarith)
    rw [gramSumTotient_eq_zero_of_profile_vanishing hx1 hB
      (fun u hu => gramCexProfile_eq_zero_of_le_two hu), mul_zero]
  exact integral_deriv_gramCexProfile_sq_pos.ne
    (tendsto_nhds_unique (tendsto_const_nhds.congr' hzero.symm) hlim)

end Gap212.Sieve
