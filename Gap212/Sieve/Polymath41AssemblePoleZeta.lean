/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssemblePoleKpEst
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# The source's `ζ_{W}`, identified: `ζ_W(w) = ζ(w) · ∏_{p ∣ W}(1 - p^{-w})`

The source defines (just after the Euler-factor estimate)

  `ζ_{WN}(s) := ∏_{p ∤ WN} (1 - p^{-s})^{-1}`   for `Re s > 1`,

and then reads the Euler-factor product as `ζ_W(1+s+s')/(ζ_W(1+s)ζ_W(1+s'))`. This file identifies
the one product that appears, `∏_{p ∤ W}(1 - p^{-w})`, in terms of Mathlib's `riemannZeta` and the
finite product `Gap212.Sieve.wTwistedProduct` that `Gap212.Sieve.Polymath41PoleWProduct`
already estimates:

  `∏_{p ∤ W}(1 - p^{-w}) = ζ(w)⁻¹ / ∏_{p ∣ W}(1 - p^{-w})`
  (`Gap212.Sieve.tprod_coprimeFactor_eq_div`),

and at `w = 1 + s` the denominator **is** `Gap212.Sieve.wTwistedProduct W s`
(`Gap212.Sieve.tprod_coprimeFactor_one_add_eq`). With
`Gap212.Sieve.norm_wTwistedProduct_div_sub_one_le'` already giving
`∏_{p ∣ W}(1 - p^{-1-s}) = (1+o(1))φ(W)/W`, that is the whole of the source's step from `ζ_W` to
`ζ` and the normalization `B_x`.

## Why the finite/cofinite split is done by hand

`Multipliable.prod_mul_tprod_compl` wants a `CommGroup`, and `ℂ` is not one under multiplication —
the missing inverse at `0` is exactly the difficulty. So the split is done through `HasProd`:
`Gap212.Sieve.prod_dividing_mul_tprod_coprimeFactor` multiplies the restricted product by the
*complementary* family `Gap212.Sieve.dividingFactor`, which is `1` off a finite set and therefore
has a `HasProd` by `hasProd_prod_of_ne_finset_one` (`Gap212.Sieve.hasProd_dividingFactor`), and the
product of the two families is the unrestricted one term by term
(`Gap212.Sieve.dividingFactor_mul_coprimeFactor`). Uniqueness of `HasProd` finishes it. Nothing is
divided by anything not shown nonzero: every factor `1 - p^{-w}` has `‖p^{-w}‖ < 1` for `Re w > 1`
(`Gap212.Sieve.one_sub_primeCpow_ne_zero`).

## Main definitions

* `Gap212.Sieve.primesDividing`: the primes dividing `W`, as a `Finset Nat.Primes`.
* `Gap212.Sieve.coprimeFactor`: `1 - p^{-w}` at `p ∤ W` and `1` at `p ∣ W`, the factor of
  `ζ_W(w)⁻¹`.

## Main results

* `Gap212.Sieve.tprod_one_sub_primeCpow`: `∏_p (1 - p^{-w}) = ζ(w)⁻¹` for `Re w > 1`. Mathlib has
  the Euler product for `ζ` itself; this is it inverted, with the non-vanishing supplied.
* `Gap212.Sieve.tprod_coprimeFactor_eq_div`:
  `∏_{p ∤ W}(1 - p^{-w}) = ζ(w)⁻¹/∏_{p ∣ W}(1 - p^{-w})`, i.e.
  `ζ_W(w) = ζ(w)·∏_{p ∣ W}(1 - p^{-w})`.
* `Gap212.Sieve.tprod_coprimeFactor_one_add_eq`: the same at `w = 1 + s`, with the finite product
  named as `Gap212.Sieve.wTwistedProduct`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset
open scoped ArithmeticFunction.Moebius

/-! ## The local factor of `ζ(w)⁻¹`, and its size -/

/-- **`‖p^{-w}‖ < 1` for `Re w > 1`.** The one inequality behind every non-vanishing here. -/
theorem norm_primeCpow_neg_lt_one {w : ℂ} (hw : 1 < w.re) (p : Nat.Primes) :
    ‖((p : ℕ) : ℂ) ^ (-w)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (mod_cast p.2.one_lt) (by linarith)

/-- **`1 - p^{-w} ≠ 0` for `Re w > 1`.** -/
theorem one_sub_primeCpow_ne_zero {w : ℂ} (hw : 1 < w.re) (p : Nat.Primes) :
    1 - ((p : ℕ) : ℂ) ^ (-w) ≠ 0 :=
  sub_ne_zero.2 fun h ↦ by simpa [← h] using norm_primeCpow_neg_lt_one hw p

/-- **`∑_p ‖p^{-w}‖` converges for `Re w > 1`** — the injection `Nat.Primes → ℕ` applied to
`∑_n n^{-Re w}`. -/
theorem summable_norm_primeCpow_neg {w : ℂ} (hw : 1 < w.re) :
    Summable fun p : Nat.Primes ↦ ‖((p : ℕ) : ℂ) ^ (-w)‖ := by
  refine ((Real.summable_nat_rpow.2 (neg_lt_neg hw)).comp_injective
    Subtype.val_injective).congr fun p ↦ ?_
  rw [Function.comp_apply, Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]

/-- **`∏_p (1 - p^{-w})` converges** for `Re w > 1`. -/
theorem multipliable_one_sub_primeCpow {w : ℂ} (hw : 1 < w.re) :
    Multipliable fun p : Nat.Primes ↦ 1 - ((p : ℕ) : ℂ) ^ (-w) := by
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable
    (f := fun p : Nat.Primes ↦ -(((p : ℕ) : ℂ) ^ (-w)))
    (by simpa using summable_norm_primeCpow_neg hw)

/-- **`∏_p (1 - p^{-w}) = ζ(w)⁻¹`** for `Re w > 1`. Mathlib's `riemannZeta_eulerProduct_hasProd`
gives the product of the *inverses*; multiplying the two families term by term gives the constant
family `1`, whose product is `1`, so the two values are reciprocal. No non-vanishing of `ζ` is
needed for this direction — only `1 - p^{-w} ≠ 0`, which is
`Gap212.Sieve.one_sub_primeCpow_ne_zero`. -/
theorem tprod_one_sub_primeCpow {w : ℂ} (hw : 1 < w.re) :
    ∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-w)) = (riemannZeta w)⁻¹ := by
  have hmul := (multipliable_one_sub_primeCpow hw).hasProd.mul (riemannZeta_eulerProduct_hasProd hw)
  simp_rw [mul_inv_cancel₀ (one_sub_primeCpow_ne_zero hw _)] at hmul
  exact eq_inv_of_mul_eq_one_left (hmul.unique hasProd_one)

/-! ## Splitting off the primes dividing `W` -/

/-- **The primes dividing `W`, as a `Finset Nat.Primes`.** -/
noncomputable def primesDividing (W : ℕ) : Finset Nat.Primes :=
  Finset.subtype Nat.Prime W.primeFactors

/-- Membership in `Gap212.Sieve.primesDividing` is divisibility, for `W ≠ 0`. -/
theorem mem_primesDividing {W : ℕ} (hW : W ≠ 0) (p : Nat.Primes) :
    p ∈ primesDividing W ↔ (p : ℕ) ∣ W :=
  ⟨fun h ↦ (Nat.mem_primeFactors.1 (mem_subtype.1 h)).2.1,
    fun h ↦ mem_subtype.2 (Nat.mem_primeFactors.2 ⟨p.2, h, hW⟩)⟩

/-- **The factor of `ζ_W(w)⁻¹` at the prime `p`**: `1 - p^{-w}` when `p ∤ W`, and `1` when `p ∣ W`.
Writing the source's `∏_{p ∤ W}` as a product over *all* primes with trivial factors at `p ∣ W` is
what lets it be compared with `Gap212.Sieve.tprod_one_sub_primeCpow`, and it is the same shape the
Euler product of `Gap212.Sieve.tprod_localFactorRecip_eq_coprimeRecipKernel` already uses. -/
noncomputable def coprimeFactor (W : ℕ) (w : ℂ) (p : Nat.Primes) : ℂ :=
  if (p : ℕ) ∣ W then 1 else 1 - ((p : ℕ) : ℂ) ^ (-w)

/-- The complementary family: `1 - p^{-w}` at `p ∣ W` and `1` elsewhere. It is `1` off the finite
set `Gap212.Sieve.primesDividing W`, which is why it has a `HasProd` with no analysis at all. -/
noncomputable def dividingFactor (W : ℕ) (w : ℂ) (p : Nat.Primes) : ℂ :=
  if (p : ℕ) ∣ W then 1 - ((p : ℕ) : ℂ) ^ (-w) else 1

/-- **The two families multiply to the unrestricted one**, prime by prime. -/
theorem dividingFactor_mul_coprimeFactor (W : ℕ) (w : ℂ) (p : Nat.Primes) :
    dividingFactor W w p * coprimeFactor W w p = 1 - ((p : ℕ) : ℂ) ^ (-w) := by
  rw [dividingFactor, coprimeFactor]
  split_ifs <;> simp

/-- **The complementary family's product is the finite product over `p ∣ W`.** -/
theorem hasProd_dividingFactor {W : ℕ} (hW : W ≠ 0) (w : ℂ) :
    HasProd (dividingFactor W w) (∏ p ∈ primesDividing W, (1 - ((p : ℕ) : ℂ) ^ (-w))) := by
  rw [← prod_congr rfl fun p hp ↦
    (if_pos ((mem_primesDividing hW p).1 hp) : dividingFactor W w p = _)]
  exact hasProd_prod_of_ne_finset_one fun p hp ↦ if_neg fun h ↦ hp ((mem_primesDividing hW p).2 h)

/-- **`∏_{p ∤ W}(1 - p^{-w})` converges.** Its factors are those of
`Gap212.Sieve.multipliable_one_sub_primeCpow` with some replaced by `1`, so the summable bound
transfers with no new estimate. -/
theorem multipliable_coprimeFactor (W : ℕ) {w : ℂ} (hw : 1 < w.re) :
    Multipliable (coprimeFactor W w) := by
  have hsum : Summable fun p : Nat.Primes ↦ ‖coprimeFactor W w p - 1‖ :=
    .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦ by rw [coprimeFactor]; split_ifs <;> simp)
      (summable_norm_primeCpow_neg hw)
  simpa using multipliable_one_add_of_summable hsum

/-- **The split**: the finite product over `p ∣ W` times the restricted product over `p ∤ W` is the
unrestricted product `ζ(w)⁻¹`. Done through `HasProd` rather than
`Multipliable.prod_mul_tprod_compl`, which needs a `CommGroup`. -/
theorem prod_dividing_mul_tprod_coprimeFactor {W : ℕ} (hW : W ≠ 0) {w : ℂ} (hw : 1 < w.re) :
    (∏ p ∈ primesDividing W, (1 - ((p : ℕ) : ℂ) ^ (-w))) *
        ∏' p : Nat.Primes, coprimeFactor W w p
      = (riemannZeta w)⁻¹ := by
  have hsplit := (hasProd_dividingFactor hW w).mul (multipliable_coprimeFactor W hw).hasProd
  rw [funext fun p ↦ dividingFactor_mul_coprimeFactor W w p] at hsplit
  rw [← tprod_one_sub_primeCpow hw]
  exact hsplit.unique (multipliable_one_sub_primeCpow hw).hasProd

/-- **The finite product over `p ∣ W` is nonzero.** -/
theorem prod_dividing_ne_zero (W : ℕ) {w : ℂ} (hw : 1 < w.re) :
    (∏ p ∈ primesDividing W, (1 - ((p : ℕ) : ℂ) ^ (-w))) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun p _ ↦ one_sub_primeCpow_ne_zero hw p

/-- **`ζ_W(w) = ζ(w) · ∏_{p ∣ W}(1 - p^{-w})`**, in the form the source's Euler-factor estimate
needs:

  `∏_{p ∤ W}(1 - p^{-w}) = ζ(w)⁻¹ / ∏_{p ∣ W}(1 - p^{-w})`. -/
theorem tprod_coprimeFactor_eq_div {W : ℕ} (hW : W ≠ 0) {w : ℂ} (hw : 1 < w.re) :
    ∏' p : Nat.Primes, coprimeFactor W w p
      = (riemannZeta w)⁻¹ / ∏ p ∈ primesDividing W, (1 - ((p : ℕ) : ℂ) ^ (-w)) := by
  rw [eq_div_iff (prod_dividing_ne_zero W hw), mul_comm]
  exact prod_dividing_mul_tprod_coprimeFactor hW hw

/-! ## At the sieve's exponent `w = 1 + s` -/

/-- **The finite product over `p ∣ W` at `w = 1 + s` is `Gap212.Sieve.wTwistedProduct W s`.** This
is the object `Gap212.Sieve.Polymath41PoleWProduct` estimates: it is `(1+o(1))φ(W)/W`, with
the `o(1)` named there. -/
theorem prod_dividing_one_add_eq_wTwistedProduct (W : ℕ) (s : ℂ) :
    (∏ p ∈ primesDividing W, (1 - ((p : ℕ) : ℂ) ^ (-(1 + s)))) = wTwistedProduct W s := by
  have h := prod_subtype_eq_prod_filter (s := W.primeFactors) (p := Nat.Prime)
    (fun n : ℕ ↦ 1 - ((n : ℂ)) ^ (-(1 + s)))
  rwa [filter_true_of_mem fun p hp ↦ Nat.prime_of_mem_primeFactors hp] at h

/-- **The source's `ζ_W(1+s)`, identified**:

  `∏_{p ∤ W}(1 - p^{-1-s}) = ζ(1+s)⁻¹ / wTwistedProduct W s`,

i.e. `ζ_W(1+s) = ζ(1+s) · ∏_{p ∣ W}(1 - p^{-1-s})`. Combining this with the pole of `ζ` at `1`
(`Gap212.Sieve.exists_norm_mul_riemannZeta_one_add_sub_one_le`) and
`Gap212.Sieve.norm_wTwistedProduct_div_sub_one_le'` is precisely the source's

  `ζ_W(1 + (1+iξ)/log x) = (1+o(1))·B_x/(1+iξ)`,

with `B_x = (φ(W)/W)·log x`. That final composition, a statement about `W(x)` and about the
truncation range, is `Gap212.Sieve.eventually_forall_norm_normalizedKernel_sub_limitKernel_le`. -/
theorem tprod_coprimeFactor_one_add_eq {W : ℕ} (hW : W ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    ∏' p : Nat.Primes, coprimeFactor W (1 + s) p
      = (riemannZeta (1 + s))⁻¹ / wTwistedProduct W s := by
  rw [tprod_coprimeFactor_eq_div hW (by simpa using hs), prod_dividing_one_add_eq_wTwistedProduct]

end Gap212.Sieve
