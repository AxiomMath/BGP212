/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.SelbergMainTerm
public import Gap212.Sieve.DivisorSumOverQstar

/-!
# Polymath8b Lemma 4.1 at `k = 1`, `N = 1`: the two Gram obligations, restated

The two Gram obligations of the sieve are `Gap212.Sieve.LcmGramSumLimitOfSupport` and
`Gap212.Sieve.TotientGramSumLimitOfSupport`. This file:

1. states the source result they are instances of — Polymath8b [Pol] Lemma 4.1 at `k = 1` and
   `N = 1` — as `Gap212.Sieve.Polymath41Recip` and `Gap212.Sieve.Polymath41Totient`, stated at the
   *pair* sums `Gap212.Sieve.pairSumRecip` and `Gap212.Sieve.pairSumTotient`, which are literally
   the source's left-hand side;
2. proves that each obligation is **equivalent** to its Polymath form
   (`Gap212.Sieve.lcmGramSumLimitOfSupport_iff_polymath41Recip`,
   `Gap212.Sieve.totientGramSumLimitOfSupport_iff_polymath41Totient`), by showing the `∀ B`
   quantifier the obligations carry is vacuous: under the support hypothesis every admissible
   truncation gives the *same* sum;
3. proves the exact algebra of the source's Euler-factor step — the identity behind the
   Euler-factor estimate and the identity behind the closing sentence of the lemma's proof — so
   that the one place where the two kernels differ is a derived equation.

## The source's route

The two obligations do not reduce to a large sieve or to Barban–Davenport–Halberstam. Stadlmann's
main-term step [Sta] splits `S_M + S_E` and invokes Polymath8b Lemma
4.1 for `S_M`, with `[d_i,d_i']` replaced by `φ([d_i,d_i'])`; at
`k = 1, N = 1` that lemma is the two obligations, **in its own regularity class and with nothing
left over**. The two obligations and the two `Prop`s below are quantified over
`ContDiff ℝ (⊤ : ℕ∞)` profiles, which is the source's "fixed smooth compactly supported functions";
every consumer's profile comes from `Gap212.GPY.TensorDatum.smooth`. The
identification of the truncated sum with the source's unrestricted one is exact
(`Gap212.Sieve.le_logx_of_lt_of_rpow_le`), and at `k = 1` the source's coprimality condition
"`[d,d'], W, N` coprime" with `N = 1` is exactly the obligations' filter. Nothing in this file uses
a mean square, and nothing here uses `Gap212.Sieve.BulkInnerRecipL2` or
`Gap212.Sieve.TotientBulkInnerL2`.

The one modelling choice is not a discrepancy. The source's profiles are `[0,+∞) → ℝ`, while these
`Prop`s take `F G : ℝ → ℝ` with `HasCompactSupport` on all of `ℝ` — and that is the class the
source's *own proof* works in: its first step is that "`t ↦ e^tF_j(t)`, `t ↦ e^tG_j(t)` may be
extended to smooth compactly supported functions on all of `ℝ`".

## The `∀ B` quantifier is vacuous

Both obligations quantify over a truncation `B : ℝ → ℕ` with `x ^ β ≤ B x`, and both require the
profiles to vanish on `[β, ∞)` — without that hypothesis both limits are false
(`Gap212.Sieve.not_lcmGramSumLimit`, `Gap212.Sieve.not_totientGramSumLimit`). Those two clauses
together pin the sum down: a divisor `d > B ≥ x ^ β` has `log_x d ≥ β`, so its profile factor
vanishes, and the double sum over `Icc 1 B` therefore does not depend on `B` at all as long as
`x ^ β ≤ B` (`Gap212.Sieve.pairSumRecip_congr_of_rpow_le`,
`Gap212.Sieve.pairSumTotient_congr_of_rpow_le`). So each obligation is equivalent to its own
instance at the canonical truncation `⌈x ^ β⌉₊`, which is the source's untruncated sum: every term
the source sums and this one omits is zero.

This is what makes the identification with Lemma 4.1 exact rather than approximate. The source's
normalization `B := (φ(W)/W) \log x` is the obligations' normalizing factor
verbatim, and at `k = 1` the source's right-hand side `(c + o(1)) B^{-k} N^k/φ(N)^k` with `N = 1`
is `(c + o(1))/B` with `c = ∫₀^∞ F'G'`, i.e. exactly `B ·` the sum tending to `∫₀^∞ F'G'`. Note
that the development's `Gap212.Sieve.mertensKappa` is the *reciprocal* `(W/φ(W))/\log x` of this
`B`, not `B` itself.

## What the two kernels share, and where they part

Polymath's proof establishes both kernels at once, and the closing sentence of the proof says why:
the local factor's `1/p` becomes `1/(p-1)`, and the difference is absorbed into the `1 + O(1/p²)`
of the Euler-factor estimate
`K_p = (1+O(1/p²))·(1-p^{-1-s})(1-p^{-1-s'})/(1-p^{-1-s-s'})`. Both halves of that sentence are
proved here as exact identities over any field, with `u = p^{-s}`, `v = p^{-s'}`:

* `Gap212.Sieve.localFactorRecip_mul_one_sub`:
  `K_p · (1 - uv/p) = (1 - u/p)(1 - v/p) - uv(1-u)(1-v)/p²`.
  This is the Euler-factor estimate with the `O(1/p²)` written out, so the passage from the exact
  Euler factor to the `ζ`-quotient is an equation.
* `Gap212.Sieve.localFactorTotient_eq_sub`:
  `K_p^φ = K_p - (u + v - uv)/(p(p-1))`, the closing sentence's `1/p ↦ 1/(p-1)`, again `O(1/p²)`.

And the constant the totient kernel carries at fixed `W` is *derived*, not asserted:
`Gap212.Sieve.localFactorTotient_one_one_eq_mul` says
`K_p^φ(1,1) = K_p(1,1) · (1 - 1/(p-1)²)`, and `1 - 1/(p-1)²` is exactly the factor whose inverse
appears in the totient kernel's Mertens sum
`Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime`. Why those two occurrences are reciprocal
is itself an identity here, prime by prime: each kernel's local factor at `u = v = 1` inverts the
local factor of its *own* Mertens weight, `1 + 1/φ(p) = 1 + 1/(p-1)` for `μ²/φ` and
`1 + 1/(μ*φ)(p) = 1 + 1/(p-2)` for `μ²/(μ*φ)`
(`Gap212.Sieve.localFactorRecip_one_one_mul_mertensFactor`,
`Gap212.Sieve.localFactorTotient_one_one_mul_mertensFactor`). The second needs `p ≠ 2`, which is
the `2 ∣ W` of the totient Mertens sum; the first needs nothing, its Mertens sum
`Gap212.Sieve.sum_moebiusSq_div_totient_coprime` having constant `φ(W)/W` alone. That asymmetry is
the kernel discipline in one line, and it is why a modulus-removal route proved on the reciprocal
side does not transpose to the totient one.

The analytic core of Lemma 4.1 is not proved in this file: `Gap212.Sieve.Polymath41Recip` and
`Gap212.Sieve.Polymath41Totient` are `Prop`s here, proved as `Gap212.Sieve.polymath41Recip` and
`Gap212.Sieve.polymath41Totient`.

## Main definitions

* `Gap212.Sieve.Polymath41Recip`, `Gap212.Sieve.Polymath41Totient`: Lemma 4.1 at `k = 1, N = 1`,
  at the canonical truncation.
* `Gap212.Sieve.localFactorRecip`, `Gap212.Sieve.localFactorTotient`: the source's local Euler
  factor `K_p` for the two kernels at `k = 1`.

## Main results

* `Gap212.Sieve.pairSumRecip_congr_of_rpow_le`, `Gap212.Sieve.pairSumTotient_congr_of_rpow_le`: the
  truncation is immaterial once it reaches `x ^ β`.
* `Gap212.Sieve.lcmGramSumLimitOfSupport_iff_polymath41Recip`,
  `Gap212.Sieve.totientGramSumLimitOfSupport_iff_polymath41Totient`: each obligation is equivalent
  to Lemma 4.1 at `k = 1, N = 1`.
* `Gap212.Sieve.localFactorRecip_mul_one_sub`, `Gap212.Sieve.localFactorTotient_eq_sub`,
  `Gap212.Sieve.localFactorTotient_one_one_eq_mul`: the Euler-factor algebra of the proof.

## References

* [Pol] D. H. J. Polymath, *Variants of the Selberg sieve, and bounded intervals containing many
  primes*, Res. Math. Sci. 1 (2014), https://arxiv.org/abs/1407.4897 ("Polymath8b").
* [Sta] J. Stadlmann, *Bounded gaps between primes*, https://arxiv.org/abs/2608.31126.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY MeasureTheory
open scoped ArithmeticFunction.Moebius

/-! ## A divisor past the truncation is past the profiles' support -/

/-- **Beyond the truncation the profile argument is beyond `β`.** If `x ^ β ≤ B` and `B < d` then
`\log_x d ≥ β`, so a profile vanishing on `[β,∞)` kills the `d`-term. This is the one arithmetic
fact behind the vacuity of the `∀ B` quantifier of the two obligations. -/
theorem le_logx_of_lt_of_rpow_le {x : ℝ} (hx : 1 < x) {β : ℝ} {B d : ℕ}
    (hB : x ^ β ≤ (B : ℝ)) (hd : B < d) : β ≤ Notation.logx x d := by
  have hx0 : (0 : ℝ) < x := by linarith
  rw [Notation.logx, le_div_iff₀ (Real.log_pos hx), ← Real.log_rpow hx0]
  exact Real.log_le_log (by positivity) (hB.trans (by exact_mod_cast hd.le))

/-- **A filtered pair sum does not see the range past its factors' vanishing.** If `u` and `v`
vanish beyond `B`, the double sum over `Icc 1 B'` coincides with the one over `Icc 1 B` for every
`B' ≥ B`, whatever the denominator `den` is. Stated for a general `den` because the two kernels of
this development — `1/[d,d']` and `1/φ([d,d'])` — use it identically. -/
theorem sum_pair_filter_congr_of_vanishing (W : ℕ) (u v : ℕ → ℝ) (den : ℕ → ℕ → ℝ)
    {B B' : ℕ} (hBB' : B ≤ B') (hu : ∀ d, B < d → u d = 0) (hv : ∀ d, B < d → v d = 0) :
    ∑ d ∈ Icc 1 B' with Nat.Coprime W d, ∑ d' ∈ Icc 1 B' with Nat.Coprime W d',
        u d * v d' / den d d'
      = ∑ d ∈ Icc 1 B with Nat.Coprime W d, ∑ d' ∈ Icc 1 B with Nat.Coprime W d',
        u d * v d' / den d d' := by
  have hsub := filter_subset_filter (Nat.Coprime W) (Icc_subset_Icc_right (a := 1) hBB')
  have hlt : ∀ d ∈ (Icc 1 B').filter (Nat.Coprime W),
      d ∉ (Icc 1 B).filter (Nat.Coprime W) → B < d := by
    simp only [mem_filter, mem_Icc]
    grind
  rw [← sum_subset hsub fun d hd hnot ↦ sum_eq_zero fun d' _ ↦ by simp [hu d (hlt d hd hnot)]]
  exact sum_congr rfl fun d _ ↦
    (sum_subset hsub fun d' hd' hnot ↦ by simp [hv d' (hlt d' hd' hnot)]).symm

/-! ## The truncation of the two pair sums is immaterial -/

/-- The truncation argument behind `Gap212.Sieve.pairSumRecip_congr_of_rpow_le` and
`Gap212.Sieve.pairSumTotient_congr_of_rpow_le`, for an arbitrary denominator. -/
private theorem sum_pair_congr_of_rpow_le {x : ℝ} (hx : 1 < x) {β : ℝ} {F G : ℝ → ℝ}
    (hF : ∀ t, β ≤ t → F t = 0) (hG : ∀ t, β ≤ t → G t = 0) (W : ℕ) (den : ℕ → ℕ → ℝ)
    {B₁ B₂ : ℕ} (h₁ : x ^ β ≤ (B₁ : ℝ)) (h₂ : x ^ β ≤ (B₂ : ℝ)) :
    ∑ d ∈ Icc 1 B₁ with Nat.Coprime W d, ∑ d' ∈ Icc 1 B₁ with Nat.Coprime W d',
        (μ d : ℝ) * F (Notation.logx x d) * ((μ d' : ℝ) * G (Notation.logx x d')) / den d d'
      = ∑ d ∈ Icc 1 B₂ with Nat.Coprime W d, ∑ d' ∈ Icc 1 B₂ with Nat.Coprime W d',
        (μ d : ℝ) * F (Notation.logx x d) * ((μ d' : ℝ) * G (Notation.logx x d')) / den d d' := by
  have hmin : x ^ β ≤ ((min B₁ B₂ : ℕ) : ℝ) := by simp [h₁, h₂]
  have hu : ∀ H : ℝ → ℝ, (∀ t, β ≤ t → H t = 0) →
      ∀ d, min B₁ B₂ < d → (μ d : ℝ) * H (Notation.logx x d) = 0 :=
    fun H hH d hd ↦ by rw [hH _ (le_logx_of_lt_of_rpow_le hx hmin hd), mul_zero]
  rw [sum_pair_filter_congr_of_vanishing W _ _ den (min_le_left B₁ B₂) (hu F hF) (hu G hG),
    sum_pair_filter_congr_of_vanishing W _ _ den (min_le_right B₁ B₂) (hu F hF) (hu G hG)]

/-- **The reciprocal pair sum is the same at every truncation reaching `x ^ β`.** Both `B₁` and
`B₂` exceed `x ^ β` and the profiles vanish on `[β,∞)`, so every divisor in either range but not in
the smaller one contributes `0`. -/
theorem pairSumRecip_congr_of_rpow_le {x : ℝ} (hx : 1 < x) {β : ℝ} {F G : ℝ → ℝ}
    (hF : ∀ t, β ≤ t → F t = 0) (hG : ∀ t, β ≤ t → G t = 0) (W : ℕ) {B₁ B₂ : ℕ}
    (h₁ : x ^ β ≤ (B₁ : ℝ)) (h₂ : x ^ β ≤ (B₂ : ℝ)) :
    pairSumRecip W B₁ x F G = pairSumRecip W B₂ x F G :=
  sum_pair_congr_of_rpow_le hx hF hG W _ h₁ h₂

/-- **The totient pair sum is the same at every truncation reaching `x ^ β`**, for the same reason
as `Gap212.Sieve.pairSumRecip_congr_of_rpow_le`: the argument reads only the profile factors, and
the denominator `φ([d,d'])` is never touched. -/
theorem pairSumTotient_congr_of_rpow_le {x : ℝ} (hx : 1 < x) {β : ℝ} {F G : ℝ → ℝ}
    (hF : ∀ t, β ≤ t → F t = 0) (hG : ∀ t, β ≤ t → G t = 0) (W : ℕ) {B₁ B₂ : ℕ}
    (h₁ : x ^ β ≤ (B₁ : ℝ)) (h₂ : x ^ β ≤ (B₂ : ℝ)) :
    pairSumTotient W B₁ x F G = pairSumTotient W B₂ x F G :=
  sum_pair_congr_of_rpow_le hx hF hG W _ h₁ h₂

/-! ## Lemma 4.1 at `k = 1`, `N = 1` -/

/-- **Polymath8b Lemma 4.1, reciprocal kernel, `k = 1`, `N = 1`.** With
`B_x = (φ(W(x))/W(x))\log x` the source's normalization,

  `B_x·∑_{d,d' ≤ ⌈x^β⌉, (dd',W(x))=1}μ(d)μ(d')F(\log_xd)G(\log_xd')/[d,d'] ⟶ ∫₀^∞F'G'`.
This is the source's multidimensional asymptotic at `k = 1, N = 1`: its right-hand side
`(c+o(1))B^{-k}N^k/φ(N)^k` is `(c+o(1))/B_x` there, with `c = ∫₀^∞F'G'`, so multiplying by `B_x`
gives exactly this limit. The truncation at `⌈x^β⌉₊` loses nothing the source keeps: the profiles
vanish on `[β,∞)`, so a divisor past `x^β` contributes `0`
(`Gap212.Sieve.le_logx_of_lt_of_rpow_le`), and the source's unrestricted `d,d'`-sum has the same
value. The profiles are `C^∞`, which is the source's own hypothesis ("fixed
smooth compactly supported functions").

`Gap212.Sieve.lcmGramSumLimitOfSupport_iff_polymath41Recip` proves this **equivalent** to the
obligation `Gap212.Sieve.LcmGramSumLimitOfSupport`.

It is proved as `Gap212.Sieve.polymath41Recip`, by the source's own route, in four steps:

1. *Fourier expansion.* Turn `F(\log_xd)` into `∫_ℝ f(ξ)d^{-(1+iξ)/\log x}dξ`:
   `Gap212.Sieve.ofReal_logx_eq_integral_profileFourier` in `Gap212.Sieve.Polymath41Fourier`
   is that display, and `Gap212.Sieve.integrable_fourier_of_contDiff` is the integrability of `𝓕`
   that the `C^∞` hypothesis supplies.
2. *Fubini.* Its arithmetic-side hypothesis
   `∑_{d,d'}|μ(d)μ(d')|/([d,d']d^{1/\log x}(d')^{1/\log x}) ≤ ζ(1+1/\log x)^3` is
   `Gap212.Sieve.tsum_pairMajorant_le` in `Gap212.Sieve.Polymath41Majorant`, together with
   `Gap212.Sieve.summable_pairMajorant`.
3. *Euler factorisation of the kernel.* The local factor is
   `Gap212.Sieve.localFactorRecip p (p^{-s}) (p^{-s'})`, and that it **is** the kernel's local
   factor is `Gap212.Sieve.one_add_kernelCoeff_prime` in `Gap212.Sieve.Polymath41Kernel`.
   The Euler-factor estimate — here exactly `Gap212.Sieve.localFactorRecip_mul_one_sub` — then
   replaces the factor by `ζ_W(1+s+s')/(ζ_W(1+s)ζ_W(1+s'))` at the cost of a convergent
   `∏_p(1+O(1/p²))`.
4. *The pole.* The simple pole of `ζ` at `s = 1` evaluates that quotient, uniformly over
   `|ξ| ≤ √(\log x)`, and `∏_{p∣W}(1-p^{-1-s}) = (1+o(1))φ(W)/W` puts the normalization `B_x` in
   place. Mathlib supplies the two analytic ingredients directly: `riemannZeta_residue_one` for the
   pole and `riemannZeta_eulerProduct_tprod` for the product.

**Every hypothesis of the source's proof is granted**, smoothness included: at `C¹` the transform
of `e^tF(t)` is merely `o(1/|ξ|)` and Mathlib's inversion theorem carries `Integrable (𝓕 f)` as a
hypothesis, while at `C^∞` the transform is rapidly decaying and that hypothesis is available.

The exponent is `(⊤ : ℕ∞)` and **not** a bare `⊤`: `(⊤ : WithTop ℕ∞)` is `ω`, i.e. analyticity,
and an analytic function on `ℝ` with compact support vanishes identically, which would make this
`Prop` vacuous. See `Gap212.GPY.TensorDatum.smooth`. -/
def Polymath41Recip : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → ContDiff ℝ (⊤ : ℕ∞) G →
    HasCompactSupport G →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) → (∀ t, β ≤ t → G t = 0) →
      Tendsto (fun x : ℝ ↦ ((W x).totient : ℝ) / (W x : ℝ) * Real.log x *
          pairSumRecip (W x) ⌈x ^ β⌉₊ x F G) atTop
        (nhds (∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t))

/-- **Polymath8b Lemma 4.1, totient kernel, `k = 1`, `N = 1`.** The same statement with `[d,d']`
replaced by `φ([d,d'])`, which is the closing sentence of the source's proof and the form
Stadlmann's main-term step invokes [Sta].

**This is a distinct assertion from `Gap212.Sieve.Polymath41Recip`, not a rearrangement of it.**
The two kernels diagonalize against different weights — `μ²(e)φ(e)/e²` against
`(μ*φ)(e)(μ(e)/φ(e))²`, hence `μ²(e)/φ(e)` against `μ²(e)/(μ*φ)(e)` after normalization — and the
totient one carries the correction `∏_{p∤W}(1-1/(p-1)²)` at fixed `W`, which
`Gap212.Sieve.localFactorTotient_one_one_eq_mul` derives here and
`Gap212.Sieve.tendsto_tprod_corr_W` drives to `1` at `W = W(x)`. The normalization is nevertheless
the same `B_x`, with no correction visible in the statement, precisely because `W = W(x)` grows.

`Gap212.Sieve.totientGramSumLimitOfSupport_iff_polymath41Totient` proves this **equivalent** to the
obligation `Gap212.Sieve.TotientGramSumLimitOfSupport`.

It is proved as `Gap212.Sieve.polymath41Totient`, by the route of `Gap212.Sieve.Polymath41Recip`
with the one change the source names: the local factor's `1/p` becomes `1/(p-1)`
(`Gap212.Sieve.localFactorTotient_eq_sub` is that replacement, exactly), and the difference is
absorbed by the same `∏_p(1+O(1/p²))` that the Euler-factor estimate already carries. What is *not*
legitimate is to transport the reciprocal kernel's modulus-removal step, which diverges at `p = 2`
where `(μ*φ)(2) = 0`.

What is shared with the reciprocal case, and what is not, is explicit. Step 1 is shared outright:
`Gap212.Sieve.Polymath41Fourier` mentions neither denominator. Step 3's local computation is
*not* shared but is done for this kernel too, as `Gap212.Sieve.one_add_kernelCoeffTotient_prime`.
Step 2's majorant is **not** shared: `Gap212.Sieve.tsum_pairMajorant_le` bounds the sum with
`1/[d,d']`, and `φ([d,d']) ≤ [d,d']` makes the totient terms larger, so it does not transfer in the
direction wanted. The totient kernel's own pair-sum majorant is
`Gap212.Sieve.tsum_pairTotientMajorant_le_sharp`.

The profiles are `C^∞`, the source's own hypothesis, for the reasons recorded at
`Gap212.Sieve.Polymath41Recip`; and the exponent is `(⊤ : ℕ∞)` and not a bare `⊤`, which would be
`ω` and would make this `Prop` vacuous. -/
def Polymath41Totient : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → ContDiff ℝ (⊤ : ℕ∞) G →
    HasCompactSupport G →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) → (∀ t, β ≤ t → G t = 0) →
      Tendsto (fun x : ℝ ↦ ((W x).totient : ℝ) / (W x : ℝ) * Real.log x *
          pairSumTotient (W x) ⌈x ^ β⌉₊ x F G) atTop
        (nhds (∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t))

/-! ## The two obligations are Lemma 4.1 -/

/-- **The reciprocal obligation is Polymath8b Lemma 4.1 at `k = 1, N = 1`.** An `iff`, so nothing
is weakened by moving to the source's form: the `∀ B` quantifier is vacuous
(`Gap212.Sieve.pairSumRecip_congr_of_rpow_le`) and the pair sum is the Gram sum
(`Gap212.Sieve.pairSumRecip_eq_gramSum`). -/
theorem lcmGramSumLimitOfSupport_iff_polymath41Recip :
    LcmGramSumLimitOfSupport ↔ Polymath41Recip := by
  refine ⟨fun h F G hF hFc hG hGc β hβ hFv hGv ↦ by
    simpa only [pairSumRecip_eq_gramSum] using
      h F G hF hFc hG hGc β hβ hFv hGv _ (.of_forall fun x ↦ Nat.le_ceil _),
    fun h F G hF hFc hG hGc β hβ hFv hGv B hB ↦ (h F G hF hFc hG hGc β hβ hFv hGv).congr' ?_⟩
  filter_upwards [hB, eventually_gt_atTop (1 : ℝ)] with x hBx hx
  rw [pairSumRecip_congr_of_rpow_le hx hFv hGv (W x) (Nat.le_ceil _) hBx, pairSumRecip_eq_gramSum]

/-- **The totient obligation is Polymath8b Lemma 4.1 at `k = 1, N = 1`, totient kernel.** The
companion of `Gap212.Sieve.lcmGramSumLimitOfSupport_iff_polymath41Recip`, through
`Gap212.Sieve.pairSumTotient_eq_gramSumTotient`. The two are proved separately because the two
kernels are separate assertions; only the truncation argument is shared. -/
theorem totientGramSumLimitOfSupport_iff_polymath41Totient :
    TotientGramSumLimitOfSupport ↔ Polymath41Totient := by
  refine ⟨fun h F G hF hFc hG hGc β hβ hFv hGv ↦ by
    simpa only [pairSumTotient_eq_gramSumTotient] using
      h F G hF hFc hG hGc β hβ hFv hGv _ (.of_forall fun x ↦ Nat.le_ceil _),
    fun h F G hF hFc hG hGc β hβ hFv hGv B hB ↦ (h F G hF hFc hG hGc β hβ hFv hGv).congr' ?_⟩
  filter_upwards [hB, eventually_gt_atTop (1 : ℝ)] with x hBx hx
  rw [pairSumTotient_congr_of_rpow_le hx hFv hGv (W x) (Nat.le_ceil _) hBx,
    pairSumTotient_eq_gramSumTotient]

/-! ## `k = 1` suffices: the multidimensional asymptotic at every `k`, from `k = 1` -/

/-- **Lemma 4.1 at `k = 1` gives Lemma 4.1 at every `k`, reciprocal kernel, `N = 1`.** With
profiles `Fᵢ, Gᵢ` all vanishing on `[β,∞)`,

  `B_x^k·∑_{d,d'}(∏ᵢμ(dᵢ)Fᵢ(\log_xdᵢ))(∏ᵢμ(d'ᵢ)Gᵢ(\log_xd'ᵢ))/∏ᵢ[dᵢ,d'ᵢ] ⟶ ∏ᵢ∫₀^∞F'ᵢG'ᵢ`

over the box of divisors up to `⌈x^β⌉₊` coprime to `W(x)`.

**This is not the source's multidimensional asymptotic verbatim for `k ≥ 2`, and the difference is
not cosmetic.** The source sums over tuples whose `[dᵢ,d'ᵢ]` are *mutually* coprime (its condition
reads "`[d_1,d'_1],…,[d_k,d'_k], W, N` coprime"), while this sums over a full box; the difference
between the two families is the sieving error `Gap212.Sieve.SelbergSievingError`, which on this
kernel is already a theorem (`Gap212.Sieve.selbergSievingError`). At `k = 1` there is nothing to be
pairwise with and the two conditions coincide, which is why `Gap212.Sieve.Polymath41Recip` is
faithful as stated.

What this theorem does show is why `k = 1` is enough and no generalization is wanted: the
coordinates separate over a full box with no coprimality hypothesis at all
(`Gap212.Sieve.normalized_boxPairSum_eq_prod_gramSum`, which is
`Gap212.Sieve.sum_pair_prod_moebius_div_prod_lcm_eq_prod` followed by
`Gap212.Sieve.pairSumRecip_eq_gramSum` in each coordinate), so the `k`-fold limit is a finite
product of one-coordinate limits and nothing is lost.

The totient kernel has no such free separation — `1/φ(∏ᵢ[dᵢ,d'ᵢ])` is a product only on tuples
whose least common multiples are pairwise coprime — and its `k`-fold form therefore runs through
`Gap212.Sieve.DivisorSumOverQstar` instead, where the difference from a full box is the
sieving error `Gap212.Sieve.totientSievingError`, already a theorem. -/
theorem tendsto_normalized_boxPairSum_of_polymath41Recip (h : Polymath41Recip) {k : ℕ}
    (F G : Fin k → ℝ → ℝ) (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    {β : ℝ} (hβ : 0 < β) (hFv : ∀ i, ∀ t, β ≤ t → F i t = 0)
    (hGv : ∀ i, ∀ t, β ≤ t → G i t = 0) :
    Tendsto (fun x : ℝ ↦ (((W x).totient : ℝ) / (W x : ℝ) * Real.log x) ^ k *
        ∑ d ∈ Fintype.piFinset fun _ : Fin k ↦ {d ∈ Icc 1 ⌈x ^ β⌉₊ | Nat.Coprime (W x) d},
          ∑ d' ∈ Fintype.piFinset fun _ : Fin k ↦ {d ∈ Icc 1 ⌈x ^ β⌉₊ | Nat.Coprime (W x) d},
            (∏ i, (μ (d i) : ℝ) * F i (Notation.logx x (d i))) *
                (∏ i, (μ (d' i) : ℝ) * G i (Notation.logx x (d' i)))
              / ∏ i, (Nat.lcm (d i) (d' i) : ℝ)) atTop
      (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) := by
  simpa only [normalized_boxPairSum_eq_prod_gramSum, ← pairSumRecip_eq_gramSum] using
    tendsto_finsetProd univ fun i _ ↦
      h (F i) (G i) (hF i) (hFc i) (hG i) (hGc i) β hβ (hFv i) (hGv i)

/-! ## The Euler factor of the proof, for both kernels -/

/-- **The local Euler factor `K_p` of the reciprocal kernel at `k = 1`**: the local factor of

  `∑_{d,d'}μ(d)μ(d')/([d,d']d^s(d')^{s'})`

at a prime `p`, with `u = p^{-s}` and `v = p^{-s'}`. Only `d,d' ∈ {1,p}` contribute, `[d,d'] = p`
on the three non-trivial pairs, and `μ(p) = -1`, giving `1 + (-u-v+uv)/p`. -/
def localFactorRecip {K : Type*} [Field K] (p u v : K) : K := 1 - u / p - v / p + u * v / p

/-- **The local Euler factor of the totient kernel at `k = 1`**: the same local factor with
`[d,d'] = p` replaced by `φ([d,d']) = p - 1`. This is the substitution of the lemma's closing
sentence, and the only change it makes to the whole proof. -/
def localFactorTotient {K : Type*} [Field K] (p u v : K) : K :=
  1 - u / (p - 1) - v / (p - 1) + u * v / (p - 1)

/-- **The Euler-factor estimate as an exact identity.** The source estimates the Euler factor by

  `K_p = (1+O(1/p²))·(1-p^{-1-s})(1-p^{-1-s'})/(1-p^{-1-s-s'})`;

cleared of the denominator and with the error written out, that is

  `K_p·(1-uv/p) = (1-u/p)(1-v/p) - uv(1-u)(1-v)/p²`,

an identity in `u, v` over any field. So the passage from the exact local factor to the quotient of
`ζ_W`-factors costs exactly `∏_p(1 - uv(1-u)(1-v)/(p²(1-u/p)(1-v/p)))`, and that product converges
— which is the source's `∏_{p>w}(1+O(1/p²)) = 1+o(1)`. -/
theorem localFactorRecip_mul_one_sub {K : Type*} [Field K] {p : K} (hp : p ≠ 0) (u v : K) :
    localFactorRecip p u v * (1 - u * v / p)
      = (1 - u / p) * (1 - v / p) - u * v * (1 - u) * (1 - v) / p ^ 2 := by
  rw [localFactorRecip]
  field_simp
  ring

/-- **The closing sentence of the proof of Lemma 4.1, as an exact identity.** Replacing `1/p` by
`1/(p-1)` in the local factor changes it by `(u+v-uv)/(p(p-1))`, which is `O(1/p²)` for bounded
`u, v` and so is absorbed by the same `1+O(1/p²)` that `Gap212.Sieve.localFactorRecip_mul_one_sub`
already carries. This is the whole of what the totient kernel costs over the reciprocal one in
Polymath's proof. -/
theorem localFactorTotient_eq_sub {K : Type*} [Field K] {p : K} (hp : p ≠ 0) (hp1 : p - 1 ≠ 0)
    (u v : K) :
    localFactorTotient p u v = localFactorRecip p u v - (u + v - u * v) / (p * (p - 1)) := by
  rw [localFactorTotient, localFactorRecip]
  field_simp
  ring

/-- **The reciprocal local factor at `u = v = 1` is `1 - 1/p`.** The value at `s = s' = 0`, which
is the leading behaviour as `x → ∞` at a fixed prime, `p^{-(1+iξ)/\log x} → 1`. -/
theorem localFactorRecip_one_one {K : Type*} [Field K] {p : K} (hp : p ≠ 0) :
    localFactorRecip p 1 1 = 1 - 1 / p := by
  rw [localFactorRecip]
  field_simp
  ring

/-- **The totient local factor at `u = v = 1` is `1 - 1/(p-1)`.** -/
theorem localFactorTotient_one_one {K : Type*} [Field K] {p : K} (hp1 : p - 1 ≠ 0) :
    localFactorTotient p 1 1 = 1 - 1 / (p - 1) := by
  rw [localFactorTotient]
  field_simp
  ring

/-- **The totient kernel's correction factor, derived.** At `u = v = 1` the two local factors
differ by exactly `1 - 1/(p-1)²`:

  `1 - 1/(p-1) = (1 - 1/p)·(1 - 1/(p-1)²)`.

This is where the constant `∏_{p∤W}(1-1/(p-1)²)` of the totient kernel comes from, and it is
derived here. Its *inverse* is the constant of the totient Mertens
sum `Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime`, the Mertens series summing the sieve
weight `μ²/(μ*φ)` while the kernel is the Dirichlet series of its Möbius inverse; the reciprocal
kernel's Mertens sum `Gap212.Sieve.sum_moebiusSq_div_totient_coprime` has constant `φ(W)/W` and no
such factor. `Gap212.Sieve.tendsto_tprod_corr_W` is what removes it at `W = W(x)`. -/
theorem localFactorTotient_one_one_eq_mul {K : Type*} [Field K] {p : K} (hp : p ≠ 0)
    (hp1 : p - 1 ≠ 0) :
    localFactorTotient p 1 1 = localFactorRecip p 1 1 * (1 - 1 / (p - 1) ^ 2) := by
  rw [localFactorTotient_one_one hp1, localFactorRecip_one_one hp]
  field_simp
  ring

/-- **Why the two correction factors are reciprocal, exactly.** The reciprocal kernel's local
factor at `u = v = 1` is the inverse of the local factor `1 + 1/φ(p) = 1 + 1/(p-1)` of its own
Mertens weight `μ²/φ`:

  `(1 - 1/p)·(1 + 1/(p-1)) = 1`.

So `Gap212.Sieve.sum_moebiusSq_div_totient_coprime` and the kernel cannot disagree about a
constant: one is the reciprocal of the other prime by prime. -/
theorem localFactorRecip_one_one_mul_mertensFactor {K : Type*} [Field K] {p : K} (hp : p ≠ 0)
    (hp1 : p - 1 ≠ 0) : localFactorRecip p 1 1 * (1 + 1 / (p - 1)) = 1 := by
  rw [localFactorRecip_one_one hp]
  field_simp
  ring

/-- **The same reciprocity for the totient kernel, and the oddness it forces.** The totient
kernel's local factor at `u = v = 1` is the inverse of the local factor
`1 + 1/(μ*φ)(p) = 1 + 1/(p-2)` of its Mertens weight `μ²/(μ*φ)`
(`Gap212.Sieve.moebiusTotient_prime` gives `(μ*φ)(p) = p - 2`):

  `(1 - 1/(p-1))·(1 + 1/(p-2)) = 1`.

The hypothesis `p - 2 ≠ 0` is not a convenience: at `p = 2` the weight `μ²/(μ*φ)` has a vanishing
denominator, so `2` must divide the pre-sieving modulus. That is exactly the `2 ∣ W` hypothesis of
`Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime`, and it is why the totient kernel needs
oddness while the reciprocal one — whose weight `μ²/φ` has `φ(p) = p - 1 ≠ 0` at every prime — does
not. A route that removes the modulus on the reciprocal side therefore does not transpose. -/
theorem localFactorTotient_one_one_mul_mertensFactor {K : Type*} [Field K] {p : K} (hp1 : p - 1 ≠ 0)
    (hp2 : p - 2 ≠ 0) : localFactorTotient p 1 1 * (1 + 1 / (p - 2)) = 1 := by
  rw [localFactorTotient_one_one hp1]
  field_simp
  ring

end Gap212.Sieve
