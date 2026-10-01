/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssemblePoleFactors
public import Gap212.Sieve.Polymath41CloseBounds

/-!
# `B_x·K_{W(x)} = limitKernel · (1+o(1))`, as an identity and then as an estimate

The source's step 4 replaces `B_x·K_{W(x)}(ξ,ξ')` by `(1+iξ)(1+iξ')/(2+iξ+iξ')`. This
file makes that replacement exact: the normalised kernel **is** `Gap212.Sieve.limitKernel ξ ξ'`
times a named quotient of seven quantities,

  `Gap212.Sieve.closeRatio W s s' E`
    `= (s+s')ζ(1+s+s') · (w(s+s')/ρ) · E · (sζ(1+s))⁻¹ (s'ζ(1+s'))⁻¹ (w(s)/ρ)⁻¹ (w(s')/ρ)⁻¹`,

with `ρ = Gap212.Sieve.wDensity W = φ(W)/W`. Six of the seven are `1+o(1)` uniformly over the
truncation range by `Gap212.Sieve.Polymath41AssemblePoleFactors`; the seventh is the
Euler-factor correction `E`, and it is left as a **parameter**, because the source's closing
paragraph says the totient kernel is this same display at a different `E`.

## Why the identity is exactly divisible

Written at `s = u/\log x`, `s' = v/\log x` with `u = Gap212.Sieve.limitNum ξ`, the three
`ζ`-factors of `Gap212.Sieve.eq_zeta_quotient_mul_of_hasProd` contribute `uv/(\log x·(u+v))` and
the three `W`-products contribute `1/ρ`. The normalisation `B_x = ρ·\log x` cancels **both** of
those exactly: no constant survives, which is the arithmetic cross-check that
`Gap212.Sieve.limitKernel`'s denominator is `u+v` and not something else. The cancellation is
carried out once, on atoms, in `Gap212.Sieve.mul_zeta_quotient_eq_mul_closeRatio`; nothing about
`ζ` or about `W` enters it.

## What the estimate says

`Gap212.Sieve.eventually_forall_norm_mul_kernel_sub_limitKernel_le`: for every `ε > 0`, once `x` is
large enough, **every** `ξ, ξ'` with `|ξ|, |ξ'| ≤ √(\log x)` satisfies

  `‖B_x·K_{W(x)}(ξ,ξ') - limitKernel ξ ξ'‖ ≤ ε·‖1+2πiξ‖·‖1+2πiξ'‖`.

The right-hand side is not `ε`: the two numerators are the honest size of
`Gap212.Sieve.limitKernel` (`Gap212.Sieve.norm_limitKernel_le`), and keeping them is what makes the
bound integrable against the transforms rather than merely small pointwise.

## Main definitions

* `Gap212.Sieve.closeRatio`: the quotient of the seven `1+o(1)` factors, at an arbitrary
  correction.

## Main results

* `Gap212.Sieve.mul_kernel_eq_limitKernel_mul_closeRatio`: **the exact identity.**
* `Gap212.Sieve.eventually_forall_norm_closeRatio_sub_one_le`: the quotient is `1+o(1)`, uniformly.
* `Gap212.Sieve.eventually_forall_norm_mul_kernel_sub_limitKernel_le`: the estimate.
* `Gap212.Sieve.mul_coprimeRecipKernel_eq_limitKernel_mul_closeRatio`,
  `Gap212.Sieve.eventually_forall_norm_mul_coprimeRecipKernel_sub_limitKernel_le`: the reciprocal
  kernel's instances.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Gap212.GPY Real
open scoped ArithmeticFunction.Moebius

/-! ## The algebra of the cancellation, on atoms -/

/-- **The cancellation of `B_x = ρ·L` against the Euler-factor estimate, on atoms.** With `z₁,z₂,z₃`
for the three `ζ`-values, `w₁,w₂,w₃` for the three `W`-products, `ρ` for `φ(W)/W` and `E` for the
correction,

  `(ρL)·(z₁⁻¹z₂⁻¹z₃·(w₃/(w₁w₂))·E)`
    `= (Ls)(Ls')/(Ls+Ls') · ((s+s')z₃·(w₃/ρ)·E·(sz₁)⁻¹(s'z₂)⁻¹(w₁/ρ)⁻¹(w₂/ρ)⁻¹)`.

Both `ρ` and `L` cancel identically — the left side has one factor of each and the right side
recovers them from `(Ls)(Ls')/(Ls+Ls')` and from the four inverted factors. Nothing here is about
`ζ` or about `W`; the hypotheses are only that the quantities being divided by are nonzero. -/
theorem mul_zeta_quotient_eq_mul_closeRatio {ρ Lc s s' z₁ z₂ z₃ w₁ w₂ w₃ E : ℂ} (hρ : ρ ≠ 0)
    (hL : Lc ≠ 0) (hs : s ≠ 0) (hs' : s' ≠ 0) (hss : s + s' ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) :
    ρ * Lc * (z₁⁻¹ * z₂⁻¹ * z₃ * (w₃ / (w₁ * w₂)) * E)
      = Lc * s * (Lc * s') / (Lc * s + Lc * s') *
          ((s + s') * z₃ * (w₃ / ρ) * E * (s * z₁)⁻¹ * (s' * z₂)⁻¹ * (w₁ / ρ)⁻¹ * (w₂ / ρ)⁻¹) := by
  have hsum : Lc * s + Lc * s' = Lc * (s + s') := by ring
  rw [hsum]
  field_simp

/-! ## The seven factors, named -/

/-- **The quotient of the seven `1+o(1)` factors of the source's step 4.** At `s = u/\log x`,
`s' = v/\log x` the normalised kernel `B_x·K_W` is `Gap212.Sieve.limitKernel` times this
(`Gap212.Sieve.mul_kernel_eq_limitKernel_mul_closeRatio`).

Three numerators — the `ζ`-value and the `W`-product at the *sum* of the exponents, and the
Euler-factor correction `E` — and four denominators, the `ζ`-values and `W`-products at the two
exponents separately. Written as a product of inverses rather than as a division so that
`Gap212.Sieve.norm_mul_sub_one_le_three_mul` and `Gap212.Sieve.norm_inv_sub_one_le` apply factor by
factor.

The correction is a parameter and not a function of `W, s, s'`: the reciprocal and totient kernels
of Lemma 4.1 have the same six other factors and differ only in this one, which is the content of
the closing sentence of the source's proof. -/
noncomputable def closeRatio (W : ℕ) (s s' E : ℂ) : ℂ :=
  ((s + s') * riemannZeta (1 + (s + s'))) * (wTwistedProduct W (s + s') / wDensity W) * E *
      (s * riemannZeta (1 + s))⁻¹ * (s' * riemannZeta (1 + s'))⁻¹ *
      (wTwistedProduct W s / wDensity W)⁻¹ * (wTwistedProduct W s' / wDensity W)⁻¹

/-! ## The exact identity -/

/-- **The source's step 4, exact**: for `x > 1` and any kernel value `K` satisfying the Euler-factor
estimate of `Gap212.Sieve.eq_zeta_quotient_mul_of_hasProd` at the exponents
`Gap212.Sieve.kernelArg x ξ`, `Gap212.Sieve.kernelArg x ξ'`,

  `(φ(W)/W)·\log x · K = limitKernel ξ ξ' · closeRatio W (kernelArg x ξ) (kernelArg x ξ') E`.

The only thing joining the display to the cancellation is that `Gap212.Sieve.kernelArg x ξ` **is**
`Gap212.Sieve.limitNum ξ / \log x`, which is true by definition. -/
theorem mul_kernel_eq_limitKernel_mul_closeRatio {W : ℕ} {x : ℝ} (hx : 1 < x) (ξ ξ' : ℝ) {K E : ℂ}
    (hfac : K = (riemannZeta (1 + kernelArg x ξ))⁻¹ * (riemannZeta (1 + kernelArg x ξ'))⁻¹ *
      riemannZeta (1 + (kernelArg x ξ + kernelArg x ξ')) *
      (wTwistedProduct W (kernelArg x ξ + kernelArg x ξ') /
        (wTwistedProduct W (kernelArg x ξ) * wTwistedProduct W (kernelArg x ξ'))) * E) :
    wDensity W * (Real.log x : ℂ) * K
      = limitKernel ξ ξ' * closeRatio W (kernelArg x ξ) (kernelArg x ξ') E := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hL : (Real.log x : ℂ) ≠ 0 := by simpa using hlx.ne'
  have hσ : (0 : ℝ) < 1 / Real.log x := by positivity
  have hs0 : (0 : ℝ) < (kernelArg x ξ).re := by rw [kernelArg_re]; exact hσ
  have hs'0 : (0 : ℝ) < (kernelArg x ξ').re := by rw [kernelArg_re]; exact hσ
  have hone1 : 1 < (1 + kernelArg x ξ).re := by
    rw [Complex.add_re, Complex.one_re]; linarith
  have hone2 : 1 < (1 + kernelArg x ξ').re := by
    rw [Complex.add_re, Complex.one_re]; linarith
  have hu : (Real.log x : ℂ) * kernelArg x ξ = limitNum ξ := by
    rw [show kernelArg x ξ = limitNum ξ / (Real.log x : ℂ) from rfl]
    field_simp
  have hv : (Real.log x : ℂ) * kernelArg x ξ' = limitNum ξ' := by
    rw [show kernelArg x ξ' = limitNum ξ' / (Real.log x : ℂ) from rfl]
    field_simp
  rw [hfac, closeRatio, limitKernel, ← hu, ← hv]
  exact mul_zeta_quotient_eq_mul_closeRatio (wDensity_ne_zero W) hL (poleArg_ne_zero hx ξ)
    (poleArg_ne_zero hx ξ') (kernelArgAdd_ne_zero hx ξ ξ')
    (riemannZeta_ne_zero_of_one_lt_re hone1) (riemannZeta_ne_zero_of_one_lt_re hone2)
    (wTwistedProduct_ne_zero W hs0) (wTwistedProduct_ne_zero W hs'0)

/-- **The reciprocal kernel's instance of the exact identity.** -/
theorem mul_coprimeRecipKernel_eq_limitKernel_mul_closeRatio {W : ℕ} (hW : W ≠ 0) {x : ℝ}
    (hx : 1 < x) (ξ ξ' : ℝ) :
    wDensity W * (Real.log x : ℂ) *
        coprimeRecipKernel W (kernelArg x ξ) (kernelArg x ξ')
      = limitKernel ξ ξ' * closeRatio W (kernelArg x ξ) (kernelArg x ξ')
          (∏' p : Nat.Primes, coprimeKpError W (kernelArg x ξ) (kernelArg x ξ') p) := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hσ : (0 : ℝ) < 1 / Real.log x := by positivity
  exact mul_kernel_eq_limitKernel_mul_closeRatio hx ξ ξ'
    (coprimeRecipKernel_eq_zeta_quotient_mul hW hσ (kernelArg_re x ξ) (kernelArg_re x ξ'))

/-! ## The seven factors are uniformly `1 + o(1)` -/

/-- **Seven factors within `d` of `1` make a product within `3⁶d` of `1`**, provided `3⁵d ≤ 1`. Six
applications of `Gap212.Sieve.norm_mul_sub_one_le_three_mul`, left-associated exactly as
`Gap212.Sieve.closeRatio` is written. -/
theorem norm_prod_seven_sub_one_le {a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ℂ} {d : ℝ} (hd : 243 * d ≤ 1)
    (h₁ : ‖a₁ - 1‖ ≤ d) (h₂ : ‖a₂ - 1‖ ≤ d) (h₃ : ‖a₃ - 1‖ ≤ d) (h₄ : ‖a₄ - 1‖ ≤ d)
    (h₅ : ‖a₅ - 1‖ ≤ d) (h₆ : ‖a₆ - 1‖ ≤ d) (h₇ : ‖a₇ - 1‖ ≤ d) :
    ‖a₁ * a₂ * a₃ * a₄ * a₅ * a₆ * a₇ - 1‖ ≤ 729 * d := by
  have hd0 : 0 ≤ d := le_trans (norm_nonneg _) h₁
  have e₁ : ‖a₁ * a₂ - 1‖ ≤ 3 * d :=
    norm_mul_sub_one_le_three_mul (by linarith) h₁ h₂
  have e₂ : ‖a₁ * a₂ * a₃ - 1‖ ≤ 3 * (3 * d) :=
    norm_mul_sub_one_le_three_mul (by linarith) e₁ (h₃.trans (by linarith))
  have e₃ : ‖a₁ * a₂ * a₃ * a₄ - 1‖ ≤ 3 * (9 * d) :=
    norm_mul_sub_one_le_three_mul (by linarith) (by linarith) (h₄.trans (by linarith))
  have e₄ : ‖a₁ * a₂ * a₃ * a₄ * a₅ - 1‖ ≤ 3 * (27 * d) :=
    norm_mul_sub_one_le_three_mul (by linarith) (by linarith) (h₅.trans (by linarith))
  have e₅ : ‖a₁ * a₂ * a₃ * a₄ * a₅ * a₆ - 1‖ ≤ 3 * (81 * d) :=
    norm_mul_sub_one_le_three_mul (by linarith) (by linarith) (h₆.trans (by linarith))
  have e₆ : ‖a₁ * a₂ * a₃ * a₄ * a₅ * a₆ * a₇ - 1‖ ≤ 3 * (243 * d) :=
    norm_mul_sub_one_le_three_mul (by linarith) (by linarith) (h₇.trans (by linarith))
  linarith

/-- **The quotient of the seven factors is `1+o(1)`, uniformly over the truncation range.** For
every `ε > 0`, once `x` is large enough, *every* `ξ, ξ'` with `|ξ|, |ξ'| ≤ √(\log x)` satisfies
`‖closeRatio (W x) (kernelArg x ξ) (kernelArg x ξ') (E x ξ ξ') - 1‖ ≤ ε`, given only that the
correction family is itself uniformly `1+o(1)`.

Six of the seven bounds are `Gap212.Sieve.Polymath41AssemblePoleFactors`' conclusions — the
three `ζ`-values from the residue, the three `W`-products from
`Gap212.Sieve.eventually_forall_norm_wTwistedProduct_div_sub_one_le` (one statement for all three,
since it is quantified over the exponent) — and the four inverted ones are put on the same footing
by `Gap212.Sieve.norm_inv_sub_one_le`. The seventh is the hypothesis. -/
theorem eventually_forall_norm_closeRatio_sub_one_le {E : ℝ → ℝ → ℝ → ℂ}
    (hE : ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ, ‖E x ξ ξ' - 1‖ ≤ η)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ, |ξ| ≤ Real.sqrt (Real.log x) →
      |ξ'| ≤ Real.sqrt (Real.log x) →
      ‖closeRatio (W x) (kernelArg x ξ) (kernelArg x ξ') (E x ξ ξ') - 1‖ ≤ ε := by
  set d : ℝ := min (ε / 1458) (1 / 1458) with hddef
  have hd0 : 0 < d := lt_min (by positivity) (by norm_num)
  have hdε : 1458 * d ≤ ε := by
    have := min_le_left (ε / 1458) (1 / 1458)
    rw [← hddef] at this
    linarith
  have hdhalf : d ≤ 1 / 2 := by
    have := min_le_right (ε / 1458) (1 / 1458)
    rw [← hddef] at this
    linarith
  have hd243 : 243 * (2 * d) ≤ 1 := by
    have := min_le_right (ε / 1458) (1 / 1458)
    rw [← hddef] at this
    linarith
  filter_upwards [eventually_forall_norm_poleArg_mul_riemannZeta_sub_one_le hd0,
    eventually_forall_norm_kernelArgAdd_mul_riemannZeta_sub_one_le hd0,
    eventually_forall_norm_wTwistedProduct_div_sub_one_le hd0, hE d hd0,
    eventually_gt_atTop (1 : ℝ)] with x hZ hZ₃ hV hEx hx1 ξ ξ' hξ hξ'
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  have hone : (0 : ℝ) ≤ (1 + 2 * π * Real.sqrt (Real.log x)) / Real.log x := by positivity
  have hsn : ‖kernelArg x ξ‖ ≤ 2 * ((1 + 2 * π * Real.sqrt (Real.log x)) / Real.log x) := by
    refine (norm_poleArg_le hx1 ξ).trans ?_
    have : (1 + 2 * π * |ξ|) / Real.log x
        ≤ (1 + 2 * π * Real.sqrt (Real.log x)) / Real.log x := by gcongr
    linarith
  have hs'n : ‖kernelArg x ξ'‖ ≤ 2 * ((1 + 2 * π * Real.sqrt (Real.log x)) / Real.log x) := by
    refine (norm_poleArg_le hx1 ξ').trans ?_
    have : (1 + 2 * π * |ξ'|) / Real.log x
        ≤ (1 + 2 * π * Real.sqrt (Real.log x)) / Real.log x := by gcongr
    linarith
  rw [closeRatio]
  refine le_trans (norm_prod_seven_sub_one_le hd243 ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by linarith)
  · exact (hZ₃ ξ ξ' hξ hξ').trans (by linarith)
  · exact (hV _ (norm_kernelArgAdd_le hx1 hξ hξ')).trans (by linarith)
  · exact (hEx ξ ξ').trans (by linarith)
  · exact norm_inv_sub_one_le hdhalf (hZ ξ hξ)
  · exact norm_inv_sub_one_le hdhalf (hZ ξ' hξ')
  · exact norm_inv_sub_one_le hdhalf (hV _ hsn)
  · exact norm_inv_sub_one_le hdhalf (hV _ hs'n)

/-! ## The estimate on the truncated range -/

/-- **The source's step 4 as an estimate, uniformly over the truncation range.** For every `ε > 0`,
once `x` is large enough, *every* `ξ, ξ'` with `|ξ|, |ξ'| ≤ √(\log x)` satisfies

  `‖B_x·K x ξ ξ' - limitKernel ξ ξ'‖ ≤ ε·‖1+2πiξ‖·‖1+2πiξ'‖`.

`hid` turns the difference into `limitKernel ξ ξ'·(closeRatio - 1)`; the two numerators on the
right are `Gap212.Sieve.norm_limitKernel_le`. They are kept rather than absorbed into `ε` because
what the closing limit integrates this bound against is `f(ξ)g(ξ')`, and `‖(1+2πiξ)f(ξ)‖` is
integrable while a bare `ε` would give nothing.

This is the `hres` hypothesis of `Gap212.Sieve.eventually_forall_norm_closeDiff_le`. -/
theorem eventually_forall_norm_mul_kernel_sub_limitKernel_le {K E : ℝ → ℝ → ℝ → ℂ}
    (hid : ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ, wDensity (W x) * (Real.log x : ℂ) * K x ξ ξ'
      = limitKernel ξ ξ' * closeRatio (W x) (kernelArg x ξ) (kernelArg x ξ') (E x ξ ξ'))
    (hE : ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ, ‖E x ξ ξ' - 1‖ ≤ η)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ, |ξ| ≤ Real.sqrt (Real.log x) →
      |ξ'| ≤ Real.sqrt (Real.log x) →
      ‖wDensity (W x) * (Real.log x : ℂ) * K x ξ ξ' - limitKernel ξ ξ'‖
        ≤ ε * (‖limitNum ξ‖ * ‖limitNum ξ'‖) := by
  filter_upwards [eventually_forall_norm_closeRatio_sub_one_le hE hε, hid] with x hR hI ξ ξ' hξ hξ'
  have hkey : wDensity (W x) * (Real.log x : ℂ) * K x ξ ξ' - limitKernel ξ ξ'
      = limitKernel ξ ξ' *
        (closeRatio (W x) (kernelArg x ξ) (kernelArg x ξ') (E x ξ ξ') - 1) := by
    rw [hI ξ ξ']
    ring
  rw [hkey, norm_mul]
  calc ‖limitKernel ξ ξ'‖ *
        ‖closeRatio (W x) (kernelArg x ξ) (kernelArg x ξ') (E x ξ ξ') - 1‖
      ≤ (‖limitNum ξ‖ * ‖limitNum ξ'‖) * ε :=
        mul_le_mul (norm_limitKernel_le ξ ξ') (hR ξ ξ' hξ hξ') (norm_nonneg _) (by positivity)
    _ = ε * (‖limitNum ξ‖ * ‖limitNum ξ'‖) := by ring

/-- **The reciprocal kernel's correction product is uniformly `1+o(1)`** — the seventh factor, from
`Gap212.Sieve.eventually_forall_norm_tprod_coprimeKpError_sub_one_le`, which needs only
`Re s ≥ 0`. -/
theorem eventually_forall_norm_tprod_coprimeKpError_kernelArg_sub_one_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ,
      ‖(∏' p : Nat.Primes, coprimeKpError (W x) (kernelArg x ξ) (kernelArg x ξ') p) - 1‖ ≤ η := by
  filter_upwards [eventually_forall_norm_tprod_coprimeKpError_sub_one_le hη,
    eventually_gt_atTop (1 : ℝ)] with x hx hx1 ξ ξ'
  have hlx : 0 < Real.log x := Real.log_pos hx1
  refine hx _ _ ?_ ?_
  · rw [kernelArg_re]; positivity
  · rw [kernelArg_re]; positivity

/-- **The reciprocal kernel's instance of the estimate**, which is the `hres` hypothesis
`Gap212.Sieve.Polymath41CloseRecip` supplies. -/
theorem eventually_forall_norm_mul_coprimeRecipKernel_sub_limitKernel_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ ξ ξ' : ℝ, |ξ| ≤ Real.sqrt (Real.log x) →
      |ξ'| ≤ Real.sqrt (Real.log x) →
      ‖wDensity (W x) * (Real.log x : ℂ) *
          coprimeRecipKernel (W x) (kernelArg x ξ) (kernelArg x ξ') - limitKernel ξ ξ'‖
        ≤ ε * (‖limitNum ξ‖ * ‖limitNum ξ'‖) := by
  refine eventually_forall_norm_mul_kernel_sub_limitKernel_le ?_
    (fun η hη ↦ eventually_forall_norm_tprod_coprimeKpError_kernelArg_sub_one_le hη) hε
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx1 ξ ξ'
  exact mul_coprimeRecipKernel_eq_limitKernel_mul_closeRatio (primorial_pos _).ne' hx1 ξ ξ'

end Gap212.Sieve
