/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssemblePoleKernel
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The source's `∏_{p>w}(1+O(1/p²)) = 1+o(1)`, with the `o(1)` proved — for any error family

`Gap212.Sieve.Polymath41AssemblePoleKernel` makes the sieve's kernel an exact expression whose
only inexplicit factor is `∏_{p ∤ W} Gap212.Sieve.kpError_p`
(`Gap212.Sieve.coprimeRecipKernel_eq_zeta_quotient_mul`), and
`Gap212.Sieve.Polymath41AssemblePoleKpEst` bounds that product uniformly in `s, s'` but by a
constant, not by something small. Making the bound *small* needs to know that the primes the
product omits are the small ones, a fact about `W(x)`.

This file supplies it. At `W = W(x) = primorial ⌊log log log x⌋₊` the omitted primes are literally
`p ≤ ⌊log log log x⌋₊` (`Gap212.Sieve.prime_dvd_W_iff`, which is `Nat.Prime.dvd_primorial_iff`),
so a per-prime bound supported on `p > ⌊log log log x⌋₊` has a sum that is a **tail** of a
convergent series. Tails of convergent series vanish, so:

  `Gap212.Sieve.eventually_forall_norm_tprod_coprimeRestrict_sub_one_le`:
  for every `ε > 0`, eventually in `x`, *every* `s, s'` with `Re s, Re s' ≥ 0` satisfies
  `‖∏_{p ∤ W(x)} E_{s,s'}(p) - 1‖ ≤ ε`.

The quantifier order is the point, as it was in `Gap212.Sieve.Polymath41PoleUniform`: `x` is
chosen before `s, s'`, so the estimate holds uniformly over the whole `ξ`-integral and not just at
each fixed `ξ`. The source's `∏_{p>w}(1+O(1/p²)) = 1+o(1)` asserts exactly this, and the `o(1)` is
in `w` rather than in `s` — which is why an `s`-free per-prime bound is the right thing to sum.

## Generic in the error family

The source's own final paragraph (immediately after the closing display) says that the totient
kernel changes nothing in the argument except that the `1/p` of `K_p` becomes `1/(p-1)`, "but this
modification may be absorbed into the `1+O(1/p²)` factor in [the Euler-factor estimate]". So the
*second* kernel is not a second limit computation: it is this same statement at a **different error
family**. Accordingly the engine below is stated for an arbitrary family `E` with an arbitrary
summable majorant `b`, supplied as a hypothesis rather than fixed to `16/p²`:

* `Gap212.Sieve.coprimeRestrict W E` neutralises the primes dividing `W` in any family;
* `Gap212.Sieve.norm_tprod_coprimeRestrict_sub_one_le` bounds its product by `exp(∑) - 1`;
* `Gap212.Sieve.eventually_forall_norm_tprod_coprimeRestrict_sub_one_le` drives that to `0`.

`Gap212.Sieve.eventually_forall_norm_tprod_coprimeKpError_sub_one_le` is then a one-line instance
at the reciprocal kernel's family. The totient kernel's family needs only its own `‖E_p - 1‖ ≤ b p`
with `b` summable, and `Gap212.Sieve.norm_localFactorTotient_sub_localFactorRecip_cpow_le` is the
`O(1/p²)` the source's sentence points at. Taking `b` as a hypothesis rather than a constant also
avoids duplicating `Gap212.Sieve.summable_const_div_prime_sq`.

## Every factor is estimated

Every factor of `Gap212.Sieve.coprimeRecipKernel_eq_zeta_quotient_mul` now has an estimate:
`riemannZeta` through the pole
(`Gap212.Sieve.eventually_forall_norm_poleArg_mul_riemannZeta_sub_one_le`), the `W`-products
through `Gap212.Sieve.norm_wTwistedProduct_div_sub_one_le'`, and the correction through this file.

## Main definitions

* `Gap212.Sieve.coprimeRestrict`: a per-prime family with the primes dividing `W` replaced by `1`.
* `Gap212.Sieve.restrictBound`, `Gap212.Sieve.thresholdBound`: a majorant cut at divisibility, and
  the same cut at a numerical threshold.

## Main results

* `Gap212.Sieve.norm_tprod_coprimeRestrict_sub_one_le`: `‖∏_{p ∤ W} E_p - 1‖ ≤ exp(∑) - 1`.
* `Gap212.Sieve.tendsto_tsum_thresholdBound`: the tail of a convergent series vanishes.
* `Gap212.Sieve.prime_dvd_W_iff`: `p ∣ W(x)` iff `p ≤ ⌊log log log x⌋₊`.
* `Gap212.Sieve.eventually_forall_norm_tprod_coprimeRestrict_sub_one_le`: **the source's
  `∏_{p>w}(1+O(1/p²)) = 1+o(1)`**, uniform in `s, s'`, at any error family.
* `Gap212.Sieve.eventually_forall_norm_tprod_coprimeKpError_sub_one_le`: its instance at the
  reciprocal kernel.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY
open scoped ArithmeticFunction.Moebius

/-! ## Neutralising the primes that divide the modulus -/

/-- **A per-prime family with the primes dividing `W` replaced by `1`.** The source's `∏_{p ∤ W}`
written as a product over all primes, for an arbitrary family. At the reciprocal kernel's family
this is `Gap212.Sieve.coprimeKpError`. -/
noncomputable def coprimeRestrict (W : ℕ) (E : Nat.Primes → ℂ) (p : Nat.Primes) : ℂ :=
  if (p : ℕ) ∣ W then 1 else E p

/-- `Gap212.Sieve.coprimeKpError` is `Gap212.Sieve.coprimeRestrict` at the reciprocal kernel's
error family. -/
theorem coprimeKpError_eq_coprimeRestrict (W : ℕ) (s s' : ℂ) :
    coprimeKpError W s s'
      = coprimeRestrict W fun p : Nat.Primes ↦
          kpError ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s')) := by
  funext p
  rw [coprimeKpError, coprimeRestrict]

/-- **A majorant with the primes dividing `W` zeroed out.** -/
noncomputable def restrictBound (W : ℕ) (b : Nat.Primes → ℝ) (p : Nat.Primes) : ℝ :=
  if (p : ℕ) ∣ W then 0 else b p

/-- For a non-negative majorant `b`, `restrictBound W b p` is non-negative. -/
theorem restrictBound_nonneg {b : Nat.Primes → ℝ} (hb0 : ∀ p, 0 ≤ b p) (W : ℕ) (p : Nat.Primes) :
    0 ≤ restrictBound W b p := by
  rw [restrictBound]
  split
  · exact le_rfl
  · exact hb0 p

/-- For a non-negative majorant `b`, `restrictBound W b p ≤ b p`. -/
theorem restrictBound_le {b : Nat.Primes → ℝ} (hb0 : ∀ p, 0 ≤ b p) (W : ℕ) (p : Nat.Primes) :
    restrictBound W b p ≤ b p := by
  rw [restrictBound]
  split
  · exact hb0 p
  · exact le_rfl

/-- The restricted majorant is summable whenever the majorant is. -/
theorem summable_restrictBound {b : Nat.Primes → ℝ} (hb0 : ∀ p, 0 ≤ b p) (hb : Summable b)
    (W : ℕ) : Summable (restrictBound W b) :=
  Summable.of_nonneg_of_le (restrictBound_nonneg hb0 W) (restrictBound_le hb0 W) hb

/-- The restricted family is within the restricted majorant of `1`, prime by prime: at `p ∣ W` the
factor *is* `1`, so the bound is an equality there. -/
theorem norm_coprimeRestrict_sub_one_le (W : ℕ) {E : Nat.Primes → ℂ} {b : Nat.Primes → ℝ}
    (hE : ∀ p, ‖E p - 1‖ ≤ b p) (p : Nat.Primes) :
    ‖coprimeRestrict W E p - 1‖ ≤ restrictBound W b p := by
  rw [coprimeRestrict, restrictBound]
  split
  · rw [sub_self, norm_zero]
  · exact hE p

/-- **The restricted product converges.** The same statement as
`Gap212.Sieve.multipliable_coprimeKpError`, at an arbitrary family. -/
theorem multipliable_coprimeRestrict (W : ℕ) {E : Nat.Primes → ℂ} {b : Nat.Primes → ℝ}
    (hb0 : ∀ p, 0 ≤ b p) (hb : Summable b) (hE : ∀ p, ‖E p - 1‖ ≤ b p) :
    Multipliable (coprimeRestrict W E) := by
  have hsum : Summable fun p : Nat.Primes ↦ ‖coprimeRestrict W E p - 1‖ :=
    Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _)
      (norm_coprimeRestrict_sub_one_le W hE) (summable_restrictBound hb0 hb W)
  have h := multipliable_one_add_of_summable
    (f := fun p : Nat.Primes ↦ coprimeRestrict W E p - 1) hsum
  simpa using h

/-- The finite-product form of the bound. -/
theorem norm_prod_coprimeRestrict_sub_one_le (W : ℕ) {E : Nat.Primes → ℂ} {b : Nat.Primes → ℝ}
    (hE : ∀ p, ‖E p - 1‖ ≤ b p) (t : Finset Nat.Primes) :
    ‖(∏ p ∈ t, coprimeRestrict W E p) - 1‖
      ≤ Real.exp (∑ p ∈ t, restrictBound W b p) - 1 := by
  have hrw : ∀ p : Nat.Primes,
      coprimeRestrict W E p = 1 + (coprimeRestrict W E p - 1) := fun p ↦ by ring
  rw [Finset.prod_congr rfl fun p _ ↦ hrw p]
  refine (Finset.norm_prod_one_add_sub_one_le t _).trans ?_
  have hmono : ∑ p ∈ t, ‖coprimeRestrict W E p - 1‖ ≤ ∑ p ∈ t, restrictBound W b p :=
    Finset.sum_le_sum fun p _ ↦ norm_coprimeRestrict_sub_one_le W hE p
  have := Real.exp_le_exp.2 hmono
  linarith

/-- **`‖∏_{p ∤ W} E_p - 1‖ ≤ exp(∑_{p ∤ W} b_p) - 1`.** The right-hand side is a *tail* once the
omitted primes are known to be the small ones, which is what
`Gap212.Sieve.restrictBound_W_eq` supplies. -/
theorem norm_tprod_coprimeRestrict_sub_one_le (W : ℕ) {E : Nat.Primes → ℂ} {b : Nat.Primes → ℝ}
    (hb0 : ∀ p, 0 ≤ b p) (hb : Summable b) (hE : ∀ p, ‖E p - 1‖ ≤ b p) :
    ‖(∏' p : Nat.Primes, coprimeRestrict W E p) - 1‖
      ≤ Real.exp (∑' p : Nat.Primes, restrictBound W b p) - 1 := by
  have hm := multipliable_coprimeRestrict W hb0 hb hE
  have hten : Tendsto (fun t : Finset Nat.Primes ↦
      ‖(∏ p ∈ t, coprimeRestrict W E p) - 1‖) atTop
      (nhds ‖(∏' p : Nat.Primes, coprimeRestrict W E p) - 1‖) :=
    (continuous_norm.tendsto _).comp (hm.hasProd.sub_const 1)
  refine le_of_tendsto hten (Filter.Eventually.of_forall fun t ↦ ?_)
  refine (norm_prod_coprimeRestrict_sub_one_le W hE t).trans ?_
  have hle : ∑ p ∈ t, restrictBound W b p ≤ ∑' p : Nat.Primes, restrictBound W b p :=
    (summable_restrictBound hb0 hb W).sum_le_tsum t fun p _ ↦ restrictBound_nonneg hb0 W p
  have := Real.exp_le_exp.2 hle
  linarith

/-! ## Tails of a convergent series over the primes vanish -/

/-- **A majorant cut at a threshold**: `0` for `p ≤ y` and `b p` beyond. -/
noncomputable def thresholdBound (y : ℕ) (b : Nat.Primes → ℝ) (p : Nat.Primes) : ℝ :=
  if (p : ℕ) ≤ y then 0 else b p

/-- **The tail of a convergent series over the primes tends to `0`.** Dominated convergence for
series: each term vanishes once the threshold passes its prime, and every term is dominated by the
summable majorant. This is the whole content of the source's `∏_{p>w}(1+O(1/p²)) = 1+o(1)` — the
`o(1)` is in `w`. -/
theorem tendsto_tsum_thresholdBound {b : Nat.Primes → ℝ} (hb0 : ∀ p, 0 ≤ b p)
    (hb : Summable b) :
    Tendsto (fun y : ℕ ↦ ∑' p : Nat.Primes, thresholdBound y b p) atTop (nhds 0) := by
  have hptwise : ∀ p : Nat.Primes,
      Tendsto (fun y : ℕ ↦ thresholdBound y b p) atTop (nhds (0 : ℝ)) := by
    intro p
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (p : ℕ)] with y hy
    rw [thresholdBound, if_pos hy]
  have hdom : ∀ᶠ y : ℕ in atTop, ∀ p : Nat.Primes, ‖thresholdBound y b p‖ ≤ b p := by
    refine Filter.Eventually.of_forall fun y p ↦ ?_
    rw [thresholdBound]
    split
    · rw [norm_zero]
      exact hb0 p
    · rw [Real.norm_of_nonneg (hb0 p)]
  have h := tendsto_tsum_of_dominated_convergence hb hptwise hdom
  simpa using h

/-! ## At `W = W(x)` the omitted primes are the small ones -/

/-- **`p ∣ W(x)` exactly when `p ≤ ⌊log log log x⌋₊`.** `Gap212.GPY.W` is a primorial, so this is
`Nat.Prime.dvd_primorial_iff`. It is the one arithmetic fact that turns a restricted sum into a
tail. -/
theorem prime_dvd_W_iff (x : ℝ) (p : Nat.Primes) :
    (p : ℕ) ∣ W x ↔ (p : ℕ) ≤ ⌊Real.log (Real.log (Real.log x))⌋₊ :=
  p.2.dvd_primorial_iff

/-- The restricted majorant at `W = W(x)` **is** the threshold majorant at
`y = ⌊log log log x⌋₊` — an equality, not an estimate. -/
theorem restrictBound_W_eq (x : ℝ) (b : Nat.Primes → ℝ) (p : Nat.Primes) :
    restrictBound (W x) b p = thresholdBound ⌊Real.log (Real.log (Real.log x))⌋₊ b p := by
  rw [restrictBound, thresholdBound]
  by_cases h : (p : ℕ) ≤ ⌊Real.log (Real.log (Real.log x))⌋₊
  · rw [if_pos ((prime_dvd_W_iff x p).2 h), if_pos h]
  · rw [if_neg fun hd ↦ h ((prime_dvd_W_iff x p).1 hd), if_neg h]

/-- `⌊log log log x⌋₊ → ∞`, which is what lets the threshold be pushed out. -/
theorem tendsto_logLogLogFloor_atTop :
    Tendsto (fun x : ℝ ↦ ⌊Real.log (Real.log (Real.log x))⌋₊) atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop))

/-! ## The source's `1 + o(1)`, at any error family -/

/-- **The source's `∏_{p>w}(1+O(1/p²)) = 1+o(1)`** (the sentence after the Euler-factor estimate),
for an arbitrary error family and uniformly in `s, s'` on the closed half-plane `Re ≥ 0`: for every
`ε > 0`, once `x` is large enough, *every* such `s, s'` satisfies

  `‖∏_{p ∤ W(x)} E_{s,s'}(p) - 1‖ ≤ ε`.

The quantifier order — `x` before `s, s'` — is what makes this usable under the `ξ`-integral, and
it is available because the majorant `b` carries no `s`. The `o(1)` is driven by
`Gap212.Sieve.tendsto_tsum_thresholdBound`, i.e. by the convergence of `∑_p b_p`, together with
`Gap212.Sieve.prime_dvd_W_iff`, which says the omitted primes are `p ≤ ⌊log log log x⌋₊`.

It is stated at a general family because the source's own last paragraph says the
totient kernel is this same statement at a different family: "the only change … is that the `1/p`
term in [`K_p`] is replaced by `1/(p-1)`; but this modification may be absorbed into the
`1+O(1/p²)` factor in [the Euler-factor estimate]". -/
theorem eventually_forall_norm_tprod_coprimeRestrict_sub_one_le
    {E : ℂ → ℂ → Nat.Primes → ℂ} {b : Nat.Primes → ℝ} (hb0 : ∀ p, 0 ≤ b p) (hb : Summable b)
    (hE : ∀ s s' : ℂ, 0 ≤ s.re → 0 ≤ s'.re → ∀ p, ‖E s s' p - 1‖ ≤ b p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ s s' : ℂ, 0 ≤ s.re → 0 ≤ s'.re →
      ‖(∏' p : Nat.Primes, coprimeRestrict (W x) (E s s') p) - 1‖ ≤ ε := by
  have hexp : Tendsto
      (fun y : ℕ ↦ Real.exp (∑' p : Nat.Primes, thresholdBound y b p) - 1) atTop (nhds 0) := by
    have h1 : Tendsto (fun y : ℕ ↦ Real.exp (∑' p : Nat.Primes, thresholdBound y b p)) atTop
        (nhds 1) := by
      simpa [Function.comp_def] using
        (Real.continuous_exp.tendsto 0).comp (tendsto_tsum_thresholdBound hb0 hb)
    simpa using h1.sub_const 1
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 (hexp.eventually (gt_mem_nhds hε))
  filter_upwards [tendsto_logLogLogFloor_atTop.eventually_ge_atTop y₀] with x hx s s' hs hs'
  refine (norm_tprod_coprimeRestrict_sub_one_le (W x) hb0 hb (hE s s' hs hs')).trans ?_
  rw [tsum_congr fun p ↦ restrictBound_W_eq x b p]
  exact (hy₀ _ hx).le

/-- **The reciprocal kernel's instance**: for every `ε > 0`, eventually in `x`, every `s, s'` with
`Re s, Re s' ≥ 0` has `‖∏_{p ∤ W(x)} kpError_p - 1‖ ≤ ε`. This is the last factor of
`Gap212.Sieve.coprimeRecipKernel_eq_zeta_quotient_mul` shown to be `1 + o(1)`, and the majorant it
supplies is the `s`-free `16/p²` of `Gap212.Sieve.norm_kpError_sub_one_le'`. -/
theorem eventually_forall_norm_tprod_coprimeKpError_sub_one_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ s s' : ℂ, 0 ≤ s.re → 0 ≤ s'.re →
      ‖(∏' p : Nat.Primes, coprimeKpError (W x) s s' p) - 1‖ ≤ ε := by
  have h := eventually_forall_norm_tprod_coprimeRestrict_sub_one_le
    (E := fun (s s' : ℂ) (p : Nat.Primes) ↦
      kpError ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s')))
    (b := fun p : Nat.Primes ↦ 16 / ((p : ℕ) : ℝ) ^ 2) (fun p ↦ by positivity)
    summable_sixteen_div_prime_sq (fun s s' hs hs' p ↦ norm_kpError_cpow_sub_one_le p hs hs') hε
  filter_upwards [h] with x hxall s s' hs hs'
  rw [coprimeKpError_eq_coprimeRestrict]
  exact hxall s s' hs hs'

end Gap212.Sieve
