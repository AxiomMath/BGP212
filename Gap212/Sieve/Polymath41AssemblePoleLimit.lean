/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssemblePoleFactors
public import Gap212.Sieve.Polymath41AssembleLimitParseval

/-!
# The kernel asymptotic: `B_x·K_W(ξ,ξ') = (1+o(1))·limitKernel ξ ξ'`

The source's step 4 ends at the kernel asymptotic:

  `K(ξ,ξ') = (1+o(1)) B^{-1} (1+iξ)(1+iξ')/(2+iξ+iξ')`,

which at `k = 1, N = 1` and in this repository's normalisation is
`B_x · K_{W(x)}(ξ,ξ') = (1+o(1))·Gap212.Sieve.limitKernel ξ ξ'`. This file proves it, in two halves
that are kept apart on purpose.

## The identity, with no analysis in it

`Gap212.Sieve.normalized_coprimeRecipKernel_eq` is an **equation**, valid for every `x > 1` and
every `ξ, ξ'`:

  `(φ(W)/W)·log x · K_W(kernelArg x ξ, kernelArg x ξ')
     = limitKernel ξ ξ' · Gap212.Sieve.kernelQuality W x ξ ξ'`,

where `kernelQuality` is the quotient of the seven factors of
`Gap212.Sieve.coprimeRecipKernel_eq_zeta_quotient_mul` in their `1+o(1)` form:
`s·ζ(1+s)` in place of `ζ(1+s)`, `w(t)/(φ(W)/W)` in place of `w(t)`. The `limitKernel` appears
because `s·s'/(s+s')` is `u·v/(L(u+v))` with `u = limitNum ξ`, `v = limitNum ξ'`, `L = log x` — and
`B_x = (φ(W)/W)·L` cancels the `L` and the `φ(W)/W`. Nothing is estimated: the whole content is
`Gap212.Sieve.normalized_zeta_quotient_eq`, a field identity in eleven atoms.

The `2` of the source's denominator is not transcribed anywhere here. It arrives as
`limitNum ξ + limitNum ξ'`, whose real part is `2` by `Gap212.Sieve.limitNum_add_re`.

## The estimate, with no algebra in it

`Gap212.Sieve.eventually_forall_norm_kernelQuality_sub_one_le` says `kernelQuality → 1` uniformly
over `|ξ|, |ξ'| ≤ √(log x)`. It is the seven bounds of
`Gap212.Sieve.Polymath41AssemblePoleFactors` and
`Gap212.Sieve.Polymath41AssemblePoleTail` combined by six applications of
`Gap212.Sieve.norm_mul_sub_one_le_three_mul` and one of `Gap212.Sieve.norm_inv_sub_one_le`. The
factor `162` in the proof is the resulting `2·3⁴`; it is not sharp and does not need to be.

## Main definitions

* `Gap212.Sieve.kernelQuality`: the quotient of the display's seven factors, each in its `1+o(1)`
  form.

## Main results

* `Gap212.Sieve.normalized_zeta_quotient_eq`: the field identity behind the normalisation.
* `Gap212.Sieve.normalized_coprimeRecipKernel_eq`: the identity
  `B_x·K_W = limitKernel · kernelQuality`, exact.
* `Gap212.Sieve.eventually_forall_norm_kernelQuality_sub_one_le`: `kernelQuality → 1`, uniformly.
* `Gap212.Sieve.eventually_forall_norm_normalizedKernel_sub_limitKernel_le`: **the source's
  kernel asymptotic**.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY Real
open scoped ArithmeticFunction.Moebius

/-! ## The identity -/

/-- **The field identity behind the normalisation.** With `s = u/L`, `s' = v/L`,

  `D·L·(ζ1⁻¹ζ2⁻¹ζ3·(w3/(w1w2))·E)
     = (uv/(u+v))·(((s+s')ζ3·(w3/D)·E) / ((sζ1)(s'ζ2)(w1/D)(w2/D)))`.

Stated abstractly so that the eleven quantities are atoms and `field_simp` can clear the
denominators; the `uv/(u+v)` on the right is what becomes `Gap212.Sieve.limitKernel`. -/
theorem normalized_zeta_quotient_eq {L u v s s' ζ1 ζ2 ζ3 w1 w2 w3 D E : ℂ}
    (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u + v ≠ 0) (hζ1 : ζ1 ≠ 0) (hζ2 : ζ2 ≠ 0)
    (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0) (hD : D ≠ 0) (hs : s = u / L) (hs' : s' = v / L) :
    D * L * (ζ1⁻¹ * ζ2⁻¹ * ζ3 * (w3 / (w1 * w2)) * E)
      = u * v / (u + v) *
        ((s + s') * ζ3 * (w3 / D) * E / (s * ζ1 * (s' * ζ2) * (w1 / D) * (w2 / D))) := by
  subst hs hs'
  field_simp

/-- **The seven factors of the display, in their `1+o(1)` form, as one quotient.** Numerator:
`(s+s')ζ(1+(s+s'))`, `w(s+s')/(φ(W)/W)`, and the correction product. Denominator: `s·ζ(1+s)`,
`s'·ζ(1+s')`, `w(s)/(φ(W)/W)`, `w(s')/(φ(W)/W)`. Each is `1+o(1)` uniformly on the truncation
range, which is `Gap212.Sieve.eventually_forall_norm_kernelQuality_sub_one_le`. -/
noncomputable def kernelQuality (W : ℕ) (x ξ ξ' : ℝ) : ℂ :=
  (kernelArg x ξ + kernelArg x ξ') *
        riemannZeta (1 + (kernelArg x ξ + kernelArg x ξ')) *
      (wTwistedProduct W (kernelArg x ξ + kernelArg x ξ') / wDensity W) *
      (∏' p : Nat.Primes, coprimeKpError W (kernelArg x ξ) (kernelArg x ξ') p) /
    (kernelArg x ξ * riemannZeta (1 + kernelArg x ξ) *
        (kernelArg x ξ' * riemannZeta (1 + kernelArg x ξ')) *
      (wTwistedProduct W (kernelArg x ξ) / wDensity W) *
      (wTwistedProduct W (kernelArg x ξ') / wDensity W))

/-- `Gap212.Sieve.poleArg` and `Gap212.Sieve.kernelArg` are the same term. Recorded as a lemma only
so that `rw` can be used; it is `rfl`. -/
theorem poleArg_eq_kernelArg (x ξ : ℝ) : poleArg x ξ = kernelArg x ξ := rfl

/-- `Gap212.Sieve.kernelArg x ξ = limitNum ξ / log x`, by definition. -/
theorem kernelArg_eq_limitNum_div (x ξ : ℝ) :
    kernelArg x ξ = limitNum ξ / (Real.log x : ℂ) := rfl

/-- The normalising factor `B_x = (φ(W)/W)·log x`, as a real number and in terms of
`Gap212.Sieve.wDensity`. -/
theorem ofReal_normalizer_eq {W : ℕ} (hW : W ≠ 0) (x : ℝ) :
    ((((W.totient : ℝ) / (W : ℝ)) * Real.log x : ℝ) : ℂ)
      = wDensity W * (Real.log x : ℂ) := by
  rw [wDensity_eq_totient_div hW]
  push_cast
  ring

/-- **The identity `B_x · K_W = limitKernel · kernelQuality`**, for every `x > 1` and every
`ξ, ξ'`. Exact: `Gap212.Sieve.coprimeRecipKernel_eq_zeta_quotient_mul` fed through
`Gap212.Sieve.normalized_zeta_quotient_eq`. -/
theorem normalized_coprimeRecipKernel_eq {W : ℕ} (hW : W ≠ 0) {x : ℝ} (hx : 1 < x) (ξ ξ' : ℝ) :
    wDensity W * (Real.log x : ℂ) *
        coprimeRecipKernel W (kernelArg x ξ) (kernelArg x ξ')
      = limitKernel ξ ξ' * kernelQuality W x ξ ξ' := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hσ : 0 < 1 / Real.log x := by positivity
  have hs : 0 < (kernelArg x ξ).re := kernelArg_re x ξ ▸ hσ
  have hs' : 0 < (kernelArg x ξ').re := kernelArg_re x ξ' ▸ hσ
  rw [coprimeRecipKernel_eq_zeta_quotient_mul hW hσ (kernelArg_re x ξ) (kernelArg_re x ξ'),
    limitKernel, kernelQuality]
  exact normalized_zeta_quotient_eq (mod_cast hlx.ne') (limitNum_ne_zero ξ) (limitNum_ne_zero ξ')
    (limitNum_add_ne_zero ξ ξ') (riemannZeta_ne_zero_of_one_lt_re (by simpa using hs))
    (riemannZeta_ne_zero_of_one_lt_re (by simpa using hs')) (wTwistedProduct_ne_zero W hs)
    (wTwistedProduct_ne_zero W hs') (wDensity_ne_zero W) rfl rfl

/-! ## The estimate -/

/-- **`kernelQuality → 1`, uniformly over the truncation range.** The seven factor bounds combined:
six applications of `Gap212.Sieve.norm_mul_sub_one_le_three_mul` and one of
`Gap212.Sieve.norm_inv_sub_one_le`, at a common `δ = min (ε/162) (1/108)`. The constant
`162 = 2·3⁴` is what that chaining produces and is not sharp. -/
theorem eventually_forall_norm_kernelQuality_sub_one_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ, |ξ| ≤ Real.sqrt (Real.log x) →
      |ξ'| ≤ Real.sqrt (Real.log x) →
      ‖kernelQuality (W x) x ξ ξ' - 1‖ ≤ ε := by
  obtain ⟨δ, hδ0, hδ108, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 108 ∧ 162 * δ ≤ ε :=
    ⟨min (ε / 162) (1 / 108), by positivity, min_le_right _ _,
      by linarith [min_le_left (ε / 162) (1 / 108)]⟩
  filter_upwards [eventually_forall_norm_poleArg_mul_riemannZeta_sub_one_le hδ0,
    eventually_forall_norm_kernelArgAdd_mul_riemannZeta_sub_one_le hδ0,
    eventually_forall_norm_wTwistedProduct_div_sub_one_le hδ0,
    eventually_forall_norm_tprod_coprimeKpError_sub_one_le hδ0,
    eventually_gt_atTop (1 : ℝ)] with x hpole hsum hwp herr hx1 ξ ξ' hξ hξ'
  have hlx : 0 < Real.log x := Real.log_pos hx1
  -- the two single W-exponents obey the truncation-scale bound
  have hR : ∀ ζ : ℝ, |ζ| ≤ Real.sqrt (Real.log x) →
      ‖wTwistedProduct (W x) (kernelArg x ζ) / wDensity (W x) - 1‖ ≤ δ := fun ζ hζ ↦ by
    have h : ‖kernelArg x ζ‖ ≤ (1 + 2 * π * Real.sqrt (Real.log x)) / Real.log x :=
      (norm_poleArg_le hx1 ζ).trans (by gcongr)
    exact hwp _ (by linarith [(norm_nonneg _).trans h])
  have hE : ‖(∏' p : Nat.Primes, coprimeKpError (W x) (kernelArg x ξ) (kernelArg x ξ') p)
      - 1‖ ≤ δ := herr _ _ (by rw [kernelArg_re]; positivity) (by rw [kernelArg_re]; positivity)
  -- chain the seven bounds: numerator, then denominator, then the quotient
  have hN := norm_mul_sub_one_le_three_mul (by linarith)
    (norm_mul_sub_one_le_three_mul (by linarith) (hsum ξ ξ' hξ hξ')
      (hwp _ (norm_kernelArgAdd_le hx1 hξ hξ'))) (hE.trans (by linarith))
  have hD := norm_inv_sub_one_le (by linarith) <| norm_mul_sub_one_le_three_mul (by linarith)
    (norm_mul_sub_one_le_three_mul (by linarith)
      (norm_mul_sub_one_le_three_mul (by linarith) (hpole ξ hξ) (hpole ξ' hξ'))
      ((hR ξ hξ).trans (by linarith))) ((hR ξ' hξ').trans (by linarith))
  rw [kernelQuality, div_eq_mul_inv]
  exact (norm_mul_sub_one_le_three_mul (by linarith) (hN.trans (by linarith)) hD).trans
    (by linarith)

/-- **The source's kernel asymptotic**, at `k = 1, N = 1`: for every `ε > 0`, once `x` is large
enough, *every* `ξ, ξ'` with `|ξ|, |ξ'| ≤ √(log x)` satisfies

  `‖B_x·K_{W(x)}(ξ,ξ') - limitKernel ξ ξ'‖ ≤ ε·‖limitKernel ξ ξ'‖`,

with `B_x = (φ(W(x))/W(x))·log x` the source's normalization. The relative form is the one the
source uses and the one the integral step wants, since `limitKernel` grows in `ξ` and the profiles'
decay is what tames it. -/
theorem eventually_forall_norm_normalizedKernel_sub_limitKernel_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ, |ξ| ≤ Real.sqrt (Real.log x) →
      |ξ'| ≤ Real.sqrt (Real.log x) →
      ‖((((W x).totient : ℝ) / (W x : ℝ) * Real.log x : ℝ) : ℂ) *
          coprimeRecipKernel (W x) (kernelArg x ξ) (kernelArg x ξ') - limitKernel ξ ξ'‖
        ≤ ε * ‖limitKernel ξ ξ'‖ := by
  filter_upwards [eventually_forall_norm_kernelQuality_sub_one_le hε,
    eventually_gt_atTop (1 : ℝ)] with x hq hx1 ξ ξ' hξ hξ'
  have hW0 : W x ≠ 0 := (primorial_pos _).ne'
  rw [ofReal_normalizer_eq hW0, normalized_coprimeRecipKernel_eq hW0 hx1 ξ ξ', ← mul_sub_one,
    norm_mul, mul_comm ε]
  exact mul_le_mul_of_nonneg_left (hq ξ ξ' hξ hξ') (norm_nonneg _)

end Gap212.Sieve
