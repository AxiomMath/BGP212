/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssemblePoleZeta

/-!
# The source's Euler-factor estimate, as an exact identity for the kernel

The source's step 3 ends at

  `K = (1+o(1)) · ζ_W(1+s+s') / (ζ_W(1+s) ζ_W(1+s'))`.

This file proves that display for the kernel of the sieve, `Gap212.Sieve.coprimeRecipKernel`, **as
an equation**, with the `(1+o(1))` not an asymptotic notation but a named convergent product:

  `Gap212.Sieve.coprimeRecipKernel_eq_zeta_quotient_mul`:
  `K_W(s,s') = ζ(1+s)⁻¹ ζ(1+s')⁻¹ ζ(1+(s+s')) · (w(s+s')/(w(s)w(s'))) · ∏_{p ∤ W} kpError_p`,

where `w(t) = Gap212.Sieve.wTwistedProduct W t = ∏_{p ∣ W}(1 - p^{-1-t})` and
`∏_{p ∤ W} kpError_p` is the `Gap212.Sieve.coprimeKpError` product, bounded by
`Gap212.Sieve.norm_tprod_kpError_sub_one_le` uniformly in `s, s'`. The `ζ_W` of the source has been
eliminated in favour of `riemannZeta` and `w` through
`Gap212.Sieve.tprod_coprimeFactor_one_add_eq`.

## How the four products are combined without ever dividing an infinite product

The per-prime identity is cleared of denominators before any product is taken:

  `Gap212.Sieve.coprimeLocalFactor_mul_coprimeFactor`:
  `K_p · (1 - p^{-1-s-s'}) = (1 - p^{-1-s})(1 - p^{-1-s'}) · kpError_p`,

which at `p ∣ W` reads `1·1 = 1·1·1` and at `p ∤ W` is
`Gap212.Sieve.localFactorRecip_mul_one_sub` together with the definition of
`Gap212.Sieve.kpError`. Each of the four families is `Multipliable`, so `HasProd.mul` turns the
per-prime identity into an identity of four infinite products
(`Gap212.Sieve.coprimeRecipKernel_mul_tprod_coprimeFactor`), and only *then* is the single nonzero
factor `∏_{p ∤ W}(1 - p^{-1-s-s'}) = ζ(1+s+s')⁻¹/w(s+s')` divided out. No infinite product is ever
inverted, and the one that is divided by has been shown nonzero from `ζ(1+s+s') ≠ 0` and
`Gap212.Sieve.wTwistedProduct_ne_zero`.

## The algebra, and where the limits are taken

This file settles the *algebra* of the source's Euler-factor computation: the kernel of the sieve
is an explicit expression in `riemannZeta`, the finite `W`-products estimated in
`Gap212.Sieve.Polymath41PoleWProduct`, and a product whose distance from `1` is bounded
uniformly. The *limits* that lead from here to `Gap212.Sieve.Polymath41Recip`, through the
reduction `Gap212.Sieve.polymath41Recip_of_tendsto_integral`, are three:

1. the pole, i.e. `ζ(1+t) = (1+o(1))/t` uniformly over the truncation range
   (`Gap212.Sieve.eventually_forall_norm_poleArg_mul_riemannZeta_sub_one_le`), combined with
   `w(t) = (1+o(1))φ(W)/W` and with `∏ kpError → 1`, whose smallness needs the *omitted* primes to
   be the small ones, a fact about `W(x)`; together these are
   `Gap212.Sieve.eventually_forall_norm_normalizedKernel_sub_limitKernel_le`;
2. the truncation `|ξ| ≤ √(log x)` as a bound on the discarded **integral**, whose pointwise half
   is `Gap212.Sieve.eventually_forall_norm_profileFourier_tail_le`; the limit of the integral is
   `Gap212.Sieve.tendsto_integral_of_forall_norm_closeDiff_le`;
3. the closing computation `∫∫ (1+2πiξ)(1+2πiξ')/(2+2πi(ξ+ξ')) f(ξ)g(ξ') = ∫₀^∞ F'G'`, which is
   `Gap212.Sieve.integral_profileFourier_mul_limitKernel_eq`.

## Main definitions

* `Gap212.Sieve.coprimeKpError`: the Euler-factor correction restricted to `p ∤ W`.

## Main results

* `Gap212.Sieve.coprimeLocalFactor_mul_coprimeFactor`: the cleared per-prime identity.
* `Gap212.Sieve.coprimeRecipKernel_mul_tprod_coprimeFactor`: the same for the four products.
* `Gap212.Sieve.coprimeRecipKernel_eq_zeta_quotient_mul`: **the source's Euler-factor estimate**,
  exact.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset
open scoped ArithmeticFunction.Moebius

/-! ## `p^{-s}/p` is `p^{-1-s}` -/

/-- `p^{-1} = 1/p`, as a `Complex.cpow`. -/
theorem primeCpow_neg_one (p : Nat.Primes) :
    ((p : ℕ) : ℂ) ^ (-1 : ℂ) = (((p : ℕ) : ℂ))⁻¹ := by
  rw [Complex.cpow_neg, Complex.cpow_one]

/-- **`p^{-s}/p = p^{-(1+s)}`.** The bookkeeping that turns the `u/p` of
`Gap212.Sieve.localFactorRecip` into the `p^{-1-s}` of the source's Euler-factor estimate. -/
theorem primeCpow_div_eq (p : Nat.Primes) (s : ℂ) :
    ((p : ℕ) : ℂ) ^ (-s) / ((p : ℕ) : ℂ) = ((p : ℕ) : ℂ) ^ (-(1 + s)) := by
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 p.2.ne_zero
  rw [show -(1 + s) = -s + (-1 : ℂ) by ring, Complex.cpow_add _ _ hp0, primeCpow_neg_one,
    div_eq_mul_inv]

/-- **`p^{-s}·p^{-s'}/p = p^{-(1+(s+s'))}`**, the companion of `Gap212.Sieve.primeCpow_div_eq` for
the `uv/p` of `Gap212.Sieve.localFactorRecip`. -/
theorem primeCpow_mul_div_eq (p : Nat.Primes) (s s' : ℂ) :
    ((p : ℕ) : ℂ) ^ (-s) * ((p : ℕ) : ℂ) ^ (-s') / ((p : ℕ) : ℂ)
      = ((p : ℕ) : ℂ) ^ (-(1 + (s + s'))) := by
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 p.2.ne_zero
  rw [show -(1 + (s + s')) = -s + -s' + (-1 : ℂ) by ring, Complex.cpow_add _ _ hp0,
    Complex.cpow_add _ _ hp0, primeCpow_neg_one, div_eq_mul_inv]

/-- The field identity the `p ∤ W` case of `Gap212.Sieve.coprimeLocalFactor_mul_coprimeFactor`
reduces to: `ab·(1 - e/(P·ab)) = ab - e/P`. As with
`Gap212.Sieve.mul_one_sub_div_eq_sub_div`, it is stated separately so that the nonvanishing
hypotheses sit on the atoms. -/
theorem mul_one_sub_div_eq_sub {K : Type*} [Field K] {a b e P : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hP : P ≠ 0) : a * b * (1 - e / (P * (a * b))) = a * b - e / P := by
  field_simp

/-! ## The restricted correction -/

/-- **The Euler-factor correction at `p ∤ W`**, and `1` at `p ∣ W`: the source's
`∏_{p ∤ W}(1+O(1/p²))` written as a product over all primes. -/
noncomputable def coprimeKpError (W : ℕ) (s s' : ℂ) (p : Nat.Primes) : ℂ :=
  if (p : ℕ) ∣ W then 1
  else kpError ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s'))

/-- **`∏_{p ∤ W} kpError_p` converges**, dominated by the unrestricted product of
`Gap212.Sieve.multipliable_kpError`. -/
theorem multipliable_coprimeKpError (W : ℕ) {s s' : ℂ} (hs : 0 ≤ s.re) (hs' : 0 ≤ s'.re) :
    Multipliable (coprimeKpError W s s') := by
  have hsum : Summable fun p : Nat.Primes ↦ ‖coprimeKpError W s s' p - 1‖ := by
    refine Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) (fun p ↦ ?_)
      summable_sixteen_div_prime_sq
    rw [coprimeKpError]
    split
    · simp only [sub_self, norm_zero]
      positivity
    · exact norm_kpError_cpow_sub_one_le p hs hs'
  simpa using multipliable_one_add_of_summable
    (f := fun p : Nat.Primes ↦ coprimeKpError W s s' p - 1) hsum

/-! ## The cleared per-prime identity -/

/-- **The Euler-factor estimate cleared of denominators, prime by prime**:

  `K_p · (1 - p^{-1-s-s'}) = (1 - p^{-1-s})(1 - p^{-1-s'}) · kpError_p`,

for every prime, with the convention that all four factors are `1` at `p ∣ W`. At `p ∤ W` it is
`Gap212.Sieve.localFactorRecip_mul_one_sub` read through
`Gap212.Sieve.primeCpow_div_eq`; the only thing needed beyond that identity is
`(1 - p^{-1-s})(1 - p^{-1-s'}) ≠ 0`, which is `Gap212.Sieve.one_sub_primeCpow_ne_zero`. -/
theorem coprimeLocalFactor_mul_coprimeFactor (W : ℕ) {s s' : ℂ} (hs : 0 < s.re) (hs' : 0 < s'.re)
    (p : Nat.Primes) :
    (if (p : ℕ) ∣ W then 1
        else localFactorRecip ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s'))) *
        coprimeFactor W (1 + (s + s')) p
      = coprimeFactor W (1 + s) p * coprimeFactor W (1 + s') p * coprimeKpError W s s' p := by
  by_cases hdvd : (p : ℕ) ∣ W
  · simp only [coprimeFactor, coprimeKpError, if_pos hdvd, mul_one]
  simp only [coprimeFactor, coprimeKpError, if_neg hdvd]
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 p.2.ne_zero
  rw [← primeCpow_mul_div_eq p s s', localFactorRecip_mul_one_sub hp0, kpError,
    ← primeCpow_div_eq p s, ← primeCpow_div_eq p s']
  refine (mul_one_sub_div_eq_sub ?_ ?_ (pow_ne_zero 2 hp0)).symm <;> rw [primeCpow_div_eq] <;>
    exact one_sub_primeCpow_ne_zero (by simp [hs, hs']) p

/-! ## The four infinite products -/

/-- The Euler product of `Gap212.Sieve.Polymath41AssembleRecipCoprime` in `HasProd` form,
which is what lets it be multiplied by other convergent products. -/
theorem hasProd_coprimeLocalFactorRecip (W : ℕ) {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ} (hs : s.re = σ)
    (hs' : s'.re = σ) :
    HasProd (fun p : Nat.Primes ↦ if (p : ℕ) ∣ W then 1
        else localFactorRecip ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s')))
      (coprimeRecipKernel W s s') := by
  have h := (isMultiplicative_restrictCoprime W
    (isMultiplicative_kernelArith s s')).eulerProduct_hasProd
      (summable_norm_restrictCoprime_kernelArith W hσ hs hs')
  rw [← coprimeRecipKernel_eq_tsum hσ hs hs'] at h
  refine h.congr_fun fun p ↦ ?_
  rw [tsum_restrictCoprime_prime_pow W (isMultiplicative_kernelArith s s') p.2,
    tsum_kernelArith_prime_pow p.2]

/-- **The cleared Euler-factor estimate for the infinite products, at any kernel.** `HasProd.mul`
applied to a per-prime identity of the shape of
`Gap212.Sieve.coprimeLocalFactor_mul_coprimeFactor`; every one of the four families is
`Multipliable`, so nothing here is a formal manipulation.

Stated for an arbitrary local-factor family `L` with product `K` and an arbitrary error family `E`
because the source's own last paragraph says the totient kernel is this same statement
at a different `E`: "the only change … is that the `1/p` term in [`K_p`] is replaced by `1/(p-1)`;
but this modification may be absorbed into the `1+O(1/p²)` factor in [the Euler-factor
estimate]". The three `ζ`-side families are not parameters — they are the same for both kernels. -/
theorem hasProd_mul_tprod_coprimeFactor (W : ℕ) {s s' : ℂ} (hs : 0 < s.re) (hs' : 0 < s'.re)
    {K : ℂ} {L E : Nat.Primes → ℂ} (hK : HasProd L K) (hEm : Multipliable E)
    (hper : ∀ p : Nat.Primes, L p * coprimeFactor W (1 + (s + s')) p
      = coprimeFactor W (1 + s) p * coprimeFactor W (1 + s') p * E p) :
    K * ∏' p : Nat.Primes, coprimeFactor W (1 + (s + s')) p
      = (∏' p : Nat.Primes, coprimeFactor W (1 + s) p) *
          (∏' p : Nat.Primes, coprimeFactor W (1 + s') p) * ∏' p : Nat.Primes, E p := by
  have hw1 : 1 < (1 + s).re := by simp [hs]
  have hw2 : 1 < (1 + s').re := by simp [hs']
  have hw3 : 1 < (1 + (s + s')).re := by simp [add_pos hs hs']
  have hlhs := hK.mul (multipliable_coprimeFactor W hw3).hasProd
  rw [funext hper] at hlhs
  exact hlhs.unique (((multipliable_coprimeFactor W hw1).hasProd.mul
    (multipliable_coprimeFactor W hw2).hasProd).mul hEm.hasProd)

/-- The reciprocal kernel's instance of `Gap212.Sieve.hasProd_mul_tprod_coprimeFactor`. -/
theorem coprimeRecipKernel_mul_tprod_coprimeFactor (W : ℕ) {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ}
    (hs : s.re = σ) (hs' : s'.re = σ) :
    coprimeRecipKernel W s s' * ∏' p : Nat.Primes, coprimeFactor W (1 + (s + s')) p
      = (∏' p : Nat.Primes, coprimeFactor W (1 + s) p) *
          (∏' p : Nat.Primes, coprimeFactor W (1 + s') p) *
          ∏' p : Nat.Primes, coprimeKpError W s s' p := by
  have hsre : 0 < s.re := hs ▸ hσ
  have hs're : 0 < s'.re := hs' ▸ hσ
  exact hasProd_mul_tprod_coprimeFactor W hsre hs're (hasProd_coprimeLocalFactorRecip W hσ hs hs')
    (multipliable_coprimeKpError W hsre.le hs're.le)
    (coprimeLocalFactor_mul_coprimeFactor W hsre hs're)

/-! ## The source's display -/

/-- **`Gap212.Sieve.wTwistedProduct W t ≠ 0` for `Re t > 0`**, since each factor `1 - p^{-1-t}` is
nonzero. -/
theorem wTwistedProduct_ne_zero (W : ℕ) {t : ℂ} (ht : 0 < t.re) : wTwistedProduct W t ≠ 0 := by
  rw [← prod_dividing_one_add_eq_wTwistedProduct W t]
  exact prod_dividing_ne_zero W (by simp [ht])

/-- **The source's Euler-factor estimate**, exact:

  `K_W(s,s') = ζ(1+s)⁻¹ ζ(1+s')⁻¹ ζ(1+(s+s')) · (w(s+s')/(w(s)w(s'))) · ∏_{p ∤ W} kpError_p`,

with `w(t) = Gap212.Sieve.wTwistedProduct W t`. The source writes this as
`(1+o(1))·ζ_W(1+s+s')/(ζ_W(1+s)ζ_W(1+s'))`; here `ζ_W` is eliminated by
`Gap212.Sieve.tprod_coprimeFactor_one_add_eq` and the `(1+o(1))` is the named product, whose
distance from `1` is bounded uniformly in `s, s'` by
`Gap212.Sieve.norm_tprod_kpError_sub_one_le`.

Nothing is asymptotic and nothing is divided by an unchecked quantity: `ζ(1+(s+s')) ≠ 0` because
`Re(1+(s+s')) > 1`, and `w(s+s') ≠ 0` by `Gap212.Sieve.wTwistedProduct_ne_zero`. -/
theorem eq_zeta_quotient_mul_of_hasProd {W : ℕ} (hW : W ≠ 0) {s s' : ℂ} (hs : 0 < s.re)
    (hs' : 0 < s'.re) {K : ℂ} {L E : Nat.Primes → ℂ} (hK : HasProd L K) (hEm : Multipliable E)
    (hper : ∀ p : Nat.Primes, L p * coprimeFactor W (1 + (s + s')) p
      = coprimeFactor W (1 + s) p * coprimeFactor W (1 + s') p * E p) :
    K = (riemannZeta (1 + s))⁻¹ * (riemannZeta (1 + s'))⁻¹ * riemannZeta (1 + (s + s')) *
          (wTwistedProduct W (s + s') / (wTwistedProduct W s * wTwistedProduct W s')) *
          ∏' p : Nat.Primes, E p := by
  have hsum : 0 < (s + s').re := by simp [add_pos hs hs']
  have hZ₁ := riemannZeta_ne_zero_of_one_lt_re (s := 1 + s) (by simp [hs])
  have hZ₂ := riemannZeta_ne_zero_of_one_lt_re (s := 1 + s') (by simp [hs'])
  have hZ₃ := riemannZeta_ne_zero_of_one_lt_re (s := 1 + (s + s')) (by simp [add_pos hs hs'])
  have hv₁ := wTwistedProduct_ne_zero W hs
  have hv₂ := wTwistedProduct_ne_zero W hs'
  have hkey := hasProd_mul_tprod_coprimeFactor W hs hs' hK hEm hper
  rw [tprod_coprimeFactor_one_add_eq hW hs, tprod_coprimeFactor_one_add_eq hW hs',
    tprod_coprimeFactor_one_add_eq hW hsum] at hkey
  rw [(eq_div_iff (div_ne_zero (inv_ne_zero hZ₃) (wTwistedProduct_ne_zero W hsum))).2 hkey]
  field_simp

/-- **The reciprocal kernel's instance of the source's display.** -/
theorem coprimeRecipKernel_eq_zeta_quotient_mul {W : ℕ} (hW : W ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    {s s' : ℂ} (hs : s.re = σ) (hs' : s'.re = σ) :
    coprimeRecipKernel W s s'
      = (riemannZeta (1 + s))⁻¹ * (riemannZeta (1 + s'))⁻¹ * riemannZeta (1 + (s + s')) *
          (wTwistedProduct W (s + s') / (wTwistedProduct W s * wTwistedProduct W s')) *
          ∏' p : Nat.Primes, coprimeKpError W s s' p := by
  have hsre : 0 < s.re := hs ▸ hσ
  have hs're : 0 < s'.re := hs' ▸ hσ
  exact eq_zeta_quotient_mul_of_hasProd hW hsre hs're (hasProd_coprimeLocalFactorRecip W hσ hs hs')
    (multipliable_coprimeKpError W hsre.le hs're.le)
    (coprimeLocalFactor_mul_coprimeFactor W hsre hs're)

end Gap212.Sieve
