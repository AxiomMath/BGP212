/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41Fubini
public import Gap212.Sieve.Polymath41MajorantTotientSharp

/-!
# The interchange for the **totient** kernel

The closing sentence of Polymath8b Lemma 4.1 replaces `1/[d,d']` by `1/φ([d,d'])`
throughout the proof. This file carries the
interchange of `Gap212.Sieve.Polymath41Fubini` across that substitution:

  `∑_{d,d'} μ(d)μ(d')/φ([d,d']) · F(log_x d) · G(log_x d')`
  `  = ∫∫ f(ξ) g(ξ') K^φ(ξ,ξ') dξ dξ'`,  `K^φ = ∑_{d,d'} μ(d)μ(d')/(φ([d,d']) d^{s} (d')^{s'})`,

as `Gap212.Sieve.tsum_totientPairSum_eq_integral` and
`Gap212.Sieve.tsum_totientPairSum_eq_integral_integral`.

## The interchange is kernel-agnostic

The interchange itself is kernel-agnostic: `Gap212.Sieve.tsum_weightPairSum_eq_integral` is stated
for an arbitrary weight `c : ℕ × ℕ → ℂ` and consumes only that `c` vanishes on the degenerate pairs
and that `∑_{d,d'} ‖c(d,d')‖ d^{-σ}(d')^{-σ}` converges at `σ = 1/log x`. Everything specific to a
kernel lives in that second fact — the majorant — and the two kernels' majorants are genuinely
different theorems, proved separately in `Gap212.Sieve.Polymath41Majorant` and
`Gap212.Sieve.Polymath41MajorantTotient` because `φ([d,d']) ≤ [d,d']` points the wrong way for
monotonicity to transfer one to the other.

So all that is owed here is the identification

  `weightMajorant totientPairWeight σ = pairTotientMajorant σ`

(`Gap212.Sieve.weightMajorant_totientPairWeight`), and the instantiation. Note where the
*arithmetic* difference between the kernels sits after this: nowhere in the interchange, and
entirely in the constant it produces. `Gap212.Sieve.norm_totientKernel_le_sharp` is the one to
consume — `‖K^φ‖ ≤ Z(2)⁶ Z(1+σ)³`, the reciprocal kernel's own `σ`-rate
(`Gap212.Sieve.norm_recipKernel_le`) times an absolute constant, hence `≪ log³x` at
`σ = 1/log x` as in the source. `Gap212.Sieve.norm_totientKernel_le` is the crude `Z(1+σ)⁶` that
comes out of `n ≤ τ₂(n)φ(n)`; it needs no shifted-divisor argument, but its `σ`-rate is `σ^{-6}`,
i.e. `log⁶x`, three powers of `log x` more than the kernel's true size.

## Main definitions

* `Gap212.Sieve.totientPairWeight`: the weight `μ(d)μ(d')/φ([d,d'])`.
* `Gap212.Sieve.totientKernel`: the source's `K` with `φ([d,d'])` in the denominator.

## Main results

* `Gap212.Sieve.weightMajorant_totientPairWeight`: the weight's majorant is
  `Gap212.Sieve.pairTotientMajorant`.
* `Gap212.Sieve.norm_totientKernel_le_sharp`: `‖K^φ‖ ≤ Z(2)⁶ Z(1+σ)³`, uniformly in `ξ,ξ'` — the
  source's rate. `Gap212.Sieve.norm_totientKernel_le` is the crude `Z(1+σ)⁶`.
* `Gap212.Sieve.tsum_totientPairSum_eq_integral`,
  `Gap212.Sieve.tsum_totientPairSum_eq_integral_integral`: **the interchange**, over the product
  measure and iterated.
-/

@[expose] public section

namespace Gap212.Sieve

open MeasureTheory Real
open scoped FourierTransform ContDiff SchwartzMap ArithmeticFunction.Moebius

/-- **The totient kernel's arithmetic weight**: `μ(d)μ(d')/φ([d,d'])`. A *distinct*
arithmetic function from `Gap212.Sieve.recipPairWeight`, not a rescaling of it — at `[d,d'] = 2`
the denominator is `1` rather than `2`. -/
noncomputable def totientPairWeight (p : ℕ × ℕ) : ℂ :=
  (μ p.1 : ℂ) * (μ p.2 : ℂ) / (Nat.totient (Nat.lcm p.1 p.2) : ℂ)

/-- The totient weight vanishes on the degenerate pairs — `μ(0) = 0` — so summing over all of
`ℕ × ℕ` is the source's sum over positive `d, d'`. -/
theorem totientPairWeight_eq_zero :
    ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → totientPairWeight p = 0 := by
  rintro ⟨d, d'⟩ (h | h) <;> simp only at h <;> subst h <;> simp [totientPairWeight]

/-- **The totient kernel `K^φ(ξ,ξ')`**:
`K^φ = ∑_{d,d'} μ(d)μ(d') / (φ([d,d']) d^s (d')^{s'})`. -/
noncomputable def totientKernel (s s' : ℂ) : ℂ := pairKernel totientPairWeight s s'

/-- **The totient majorant is the totient weight's majorant**: step 2's
`Gap212.Sieve.pairTotientMajorant σ (d,d')` is `‖μ(d)μ(d')/φ([d,d'])‖ d^{-σ}(d')^{-σ}`. This one
computation is the whole arithmetic content of instantiating the interchange at the totient
kernel. -/
theorem weightMajorant_totientPairWeight (σ : ℝ) (p : ℕ × ℕ) :
    weightMajorant totientPairWeight σ p = pairTotientMajorant σ p := by
  obtain ⟨d, d'⟩ := p
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp [weightMajorant, totientPairWeight, pairTotientMajorant]
  rcases Nat.eq_zero_or_pos d' with hd' | hd'
  · subst hd'; simp [weightMajorant, totientPairWeight, pairTotientMajorant]
  have hlcm : (Nat.totient (Nat.lcm d d') : ℝ) ≠ 0 := by
    have hne : Nat.lcm d d' ≠ 0 := Nat.lcm_ne_zero (by omega) (by omega)
    have : Nat.totient (Nat.lcm d d') ≠ 0 := by
      simpa only [ne_eq, Nat.totient_eq_zero] using hne
    exact_mod_cast this
  have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdr' : (0 : ℝ) < (d' : ℝ) := by exact_mod_cast hd'
  have hp : ((d : ℝ) ^ σ) ≠ 0 := by positivity
  have hp' : ((d' : ℝ) ^ σ) ≠ 0 := by positivity
  rw [weightMajorant, totientPairWeight, pairTotientMajorant, norm_div,
    Real.rpow_neg hdr.le, Real.rpow_neg hdr'.le]
  simp only [norm_mul, Complex.norm_intCast, Complex.norm_natCast]
  field_simp

/-- The totient side of step 2's summability, in the shape the generic interchange asks for. -/
theorem summable_weightMajorant_totientPairWeight {σ : ℝ} (hσ : 0 < σ) :
    Summable (weightMajorant totientPairWeight σ) := by
  simpa only [funext fun p ↦ weightMajorant_totientPairWeight σ p] using
    summable_pairTotientMajorant hσ

/-- **The modulus of a totient-kernel term is exactly the totient majorant.** -/
theorem norm_totientKernelTerm_of_re {s s' : ℂ} {σ : ℝ} (hs : s.re = σ) (hs' : s'.re = σ)
    (p : ℕ × ℕ) : ‖pairKernelTerm totientPairWeight s s' p‖ = pairTotientMajorant σ p := by
  rw [norm_pairKernelTerm_of_re totientPairWeight_eq_zero hs hs',
    weightMajorant_totientPairWeight]

/-- **The totient kernel converges absolutely** wherever both exponents have real part `σ > 0`. -/
theorem summable_totientPairKernelTerm {s s' : ℂ} {σ : ℝ} (hσ : 0 < σ) (hs : s.re = σ)
    (hs' : s'.re = σ) : Summable fun p : ℕ × ℕ ↦ pairKernelTerm totientPairWeight s s' p :=
  summable_pairKernelTerm totientPairWeight_eq_zero
    (summable_weightMajorant_totientPairWeight hσ) hs hs'

/-- **The totient kernel is bounded uniformly in `ξ,ξ'`**: if both exponents have real part
`σ > 0` then `‖K^φ‖ ≤ Z(1+σ)⁶`. The exponent is `6`, not the reciprocal kernel's `3`, and at
`σ = 1/log x` that is `log⁶x` where the source has `log³x`; this is the crude bound and
`Gap212.Sieve.norm_totientKernel_le_sharp` is the one at the source's rate. -/
theorem norm_totientKernel_le {s s' : ℂ} {σ : ℝ} (hσ : 0 < σ) (hs : s.re = σ) (hs' : s'.re = σ) :
    ‖totientKernel s s'‖ ≤ zetaSeries (1 + σ) ^ 6 := by
  rw [totientKernel]
  refine (norm_pairKernel_le_tsum totientPairWeight_eq_zero
    (summable_weightMajorant_totientPairWeight hσ) hs hs').trans ?_
  rw [tsum_congr fun p ↦ weightMajorant_totientPairWeight σ p]
  exact tsum_pairTotientMajorant_le hσ

/-- **The totient kernel at the source's rate**, uniformly in `ξ,ξ'`: if both exponents have real
part `σ > 0` then

  `‖K^φ(ξ,ξ')‖ ≤ Z(2)⁶ · Z(1+σ)³`.

The `σ`-dependence is the reciprocal kernel's own `Z(1+σ)³` of
`Gap212.Sieve.norm_recipKernel_le`; the totient kernel's whole price is the absolute constant
`Z(2)⁶`, not a power of `log x`. At `σ = 1/log x` this is the source's `≪ log³x`, and it is this
bound — not `Gap212.Sieve.norm_totientKernel_le` — that a consumer needing the rate should cite. -/
theorem norm_totientKernel_le_sharp {s s' : ℂ} {σ : ℝ} (hσ : 0 < σ) (hs : s.re = σ)
    (hs' : s'.re = σ) : ‖totientKernel s s'‖ ≤ zetaSeries 2 ^ 6 * zetaSeries (1 + σ) ^ 3 := by
  rw [totientKernel]
  refine (norm_pairKernel_le_tsum totientPairWeight_eq_zero
    (summable_weightMajorant_totientPairWeight hσ) hs hs').trans ?_
  rw [tsum_congr fun p ↦ weightMajorant_totientPairWeight σ p]
  exact tsum_pairTotientMajorant_le_sharp hσ

/-- **The interchange for the totient kernel**: for smooth compactly supported profiles
`F, G` and `x > 1`,

  `∑_{d,d'} μ(d)μ(d')/φ([d,d']) · F(log_x d) · G(log_x d')`
  `  = ∫_{ℝ²} f(ξ) g(ξ') K^φ(ξ,ξ') d(ξ,ξ')`.

The `d = 0` and `d' = 0` terms of the left-hand sum vanish, since `μ(0) = 0`, so the sum over all
of `ℕ × ℕ` is the source's sum over positive `d, d'`. -/
theorem tsum_totientPairSum_eq_integral {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) {x : ℝ}
    (hx : 1 < x) :
    ∑' p : ℕ × ℕ, (μ p.1 : ℂ) * (μ p.2 : ℂ) / (Nat.totient (Nat.lcm p.1 p.2) : ℂ) *
        ((F (Notation.logx x p.1) : ℂ) * (G (Notation.logx x p.2) : ℂ))
      = ∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 *
          totientKernel (kernelArg x w.1) (kernelArg x w.2) := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  exact tsum_weightPairSum_eq_integral totientPairWeight_eq_zero hF hFc hG hGc hx
    (summable_weightMajorant_totientPairWeight (by positivity))

/-- **The interchange for the totient kernel, in the source's iterated form** `∫ dξ ∫ dξ'`. -/
theorem tsum_totientPairSum_eq_integral_integral {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) {x : ℝ}
    (hx : 1 < x) :
    ∑' p : ℕ × ℕ, (μ p.1 : ℂ) * (μ p.2 : ℂ) / (Nat.totient (Nat.lcm p.1 p.2) : ℂ) *
        ((F (Notation.logx x p.1) : ℂ) * (G (Notation.logx x p.2) : ℂ))
      = ∫ ξ : ℝ, ∫ ξ' : ℝ, profileFourier F ξ * profileFourier G ξ' *
          totientKernel (kernelArg x ξ) (kernelArg x ξ') := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  exact tsum_weightPairSum_eq_integral_integral totientPairWeight_eq_zero hF hFc hG hGc hx
    (summable_weightMajorant_totientPairWeight (by positivity))

end Gap212.Sieve
