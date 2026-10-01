/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41Fourier
public import Gap212.Sieve.Polymath41Majorant
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The interchange in Polymath8b Lemma 4.1: the `d,d'`-sum meets the `ξ,ξ'`-integrals

Step 1 (`Gap212.Sieve.Polymath41Fourier`) expands each profile value as an integral,

  `F(log_x d) = ∫_ℝ f(ξ) · d^{-(1+2πiξ)/log x} dξ`

(`Gap212.Sieve.ofReal_logx_eq_integral_profileFourier`), and step 2
(`Gap212.Sieve.Polymath41Majorant`) bounds the arithmetic sum of the moduli,

  `∑_{d,d'} |μ(d)μ(d')| / ([d,d'] d^σ (d')^σ) ≤ Z(1+σ)³`

(`Gap212.Sieve.tsum_pairMajorant_le`). This file performs the interchange those two steps are
for: substituting the expansion into the pair sum and exchanging
`∑_{d,d'}` with `∫∫ dξ dξ'` turns

  `∑_{d,d'} μ(d)μ(d')/[d,d'] · F(log_x d) · G(log_x d')`

into

  `∫∫ f(ξ) g(ξ') K(ξ,ξ') dξ dξ'`,  `K(ξ,ξ') = ∑_{d,d'} μ(d)μ(d') / ([d,d'] d^{s(ξ)} (d')^{s(ξ')})`,

with `s(ξ) = (1+2πiξ)/log x` the normalised form of the source's `(1+iξ)/log x`. The two displays
are `Gap212.Sieve.tsum_recipPairSum_eq_integral` (over the product measure on `ℝ × ℝ`) and
`Gap212.Sieve.tsum_recipPairSum_eq_integral_integral` (iterated, the source's own shape).

## The interchange does not know which kernel it is interchanging

Everything here is proved for an arbitrary **weight** `c : ℕ × ℕ → ℂ` — the arithmetic factor
attached to the pair `(d,d')`, which for the source's reciprocal kernel is `μ(d)μ(d')/[d,d']` and
for the totient kernel of the lemma's closing sentence is `μ(d)μ(d')/φ([d,d'])`. The
interchange consumes exactly two facts about `c`:

* it vanishes when `d = 0` or `d' = 0`, so that summing over all of `ℕ × ℕ` is the source's sum
  over positive `d,d'` (`Gap212.Sieve.recipPairWeight_eq_zero`);
* `∑_{d,d'} ‖c(d,d')‖ d^{-σ} (d')^{-σ}` converges at `σ = 1/log x`, which is step 2.

Nothing else. In particular the interchange is *not* where the two kernels part company: they part
company in their majorants, `Gap212.Sieve.pairMajorant` and `Gap212.Sieve.pairTotientMajorant`,
which is why the generic layer here is instantiated twice — once below, once in
`Gap212.Sieve.Polymath41FubiniTotient`.

## Why the interchange is legitimate here

The hypothesis Mathlib's `MeasureTheory.integral_tsum_of_summable_integral_norm` asks for is that
each term be integrable and that `∑_{d,d'} ∫ ‖term‖` converge. Both are exactly what steps 1 and 2
supply, and they meet with no loss: the modulus of the term factors *completely*,

  `‖f(ξ) g(ξ') c(d,d') d^{-s(ξ)} (d')^{-s(ξ')}‖ = ‖f(ξ)‖ ‖g(ξ')‖ · ‖c(d,d')‖ d^{-σ} (d')^{-σ}`

at `σ = 1/log x` (`Gap212.Sieve.norm_pairFubiniTerm`), because
`‖d^{-(1+2πiξ)/log x}‖ = d^{-1/log x}` carries no `ξ`
(`Gap212.Sieve.norm_natCast_cpow_profileExponent`). So `∫ ‖term‖` is *equal* to
`(∫‖f‖)(∫‖g‖) · ‖c(d,d')‖ d^{-σ} (d')^{-σ}` (`Gap212.Sieve.integral_norm_pairFubiniTerm`) — not
merely bounded by it — and its summability is step 2 scaled by a constant. No
dominated-convergence estimate beyond step 2 is needed, and the `σ > 0` that step 2 requires is
`1/log x > 0`, i.e. `x > 1`.

## The kernel

`Gap212.Sieve.pairKernel c s s'` is the source's `K` at general complex exponents, a double
Dirichlet series in `(s,s')`, and `Gap212.Sieve.recipKernel` is it at the source's weight. Its
convergence and its size both come from step 2 as soon as `s.re = s'.re = σ` with the weight
summable at `σ`: `Gap212.Sieve.summable_pairKernelTerm` and
`Gap212.Sieve.norm_pairKernel_le_tsum`, the latter giving the source's `≪ log³x` in the form
`‖K(ξ,ξ')‖ ≤ Z(1+1/log x)³` uniformly in `ξ,ξ'` (`Gap212.Sieve.norm_recipKernel_le`). That uniform
bound is what makes the integrand of the interchanged integral integrable
(`Gap212.Sieve.integrable_pairKernel_mul`) and hence what licenses passing from the product measure
to the iterated integral.

`Gap212.Sieve.recipKernel` is a *pair* sum, not the Dirichlet series
`∑_n Gap212.Sieve.kernelCoeff s s' n` of `Gap212.Sieve.Polymath41Kernel`. The two are equal —
collecting the pair sum by `n = [d,d']` is the content of that file's `lcmFibre` — and the equality
is `Gap212.Sieve.recipKernel_eq_tsum_kernelCoeff` in
`Gap212.Sieve.Polymath41AssembleDirichlet`.

## Main definitions

* `Gap212.Sieve.kernelArg`: `s(ξ) = (1+2πiξ)/log x`, the normalised exponent of the source.
* `Gap212.Sieve.weightMajorant`: `‖c(d,d')‖ d^{-σ} (d')^{-σ}`, the modulus of a kernel term and the
  thing step 2 must sum. `Gap212.Sieve.weightMajorant_recipPairWeight` identifies it with
  `Gap212.Sieve.pairMajorant`.
* `Gap212.Sieve.pairKernelTerm` / `Gap212.Sieve.pairKernel`: the summand and the sum of the
  source's `K(ξ,ξ')`, at general complex `(s,s')` and general weight;
  `Gap212.Sieve.recipKernel` at the source's weight `Gap212.Sieve.recipPairWeight`.
* `Gap212.Sieve.pairFubiniTerm`: the `(d,d')`-th summand of the integrand, i.e. what the
  interchange moves past the integral sign.

## Main results

* `Gap212.Sieve.norm_pairKernelTerm_of_re`: the modulus of a kernel term *is* the majorant.
* `Gap212.Sieve.summable_pairKernelTerm`, `Gap212.Sieve.norm_pairKernel_le_tsum`: the kernel
  converges and is bounded by the majorant's sum; `Gap212.Sieve.norm_recipKernel_le` is the
  source's `‖K‖ ≤ Z(1+σ)³`.
* `Gap212.Sieve.integral_pairFubiniTerm`: one term integrates to
  `c(d,d') · F(log_x d) · G(log_x d')` — step 1, applied twice through Fubini for a product of
  one-variable functions.
* `Gap212.Sieve.tsum_weightPairSum_eq_integral`: **the interchange**, at a general weight;
  `Gap212.Sieve.tsum_recipPairSum_eq_integral` at the source's.
* `Gap212.Sieve.tsum_recipPairSum_eq_integral_integral`: the interchange in the source's iterated
  form.
-/

@[expose] public section

namespace Gap212.Sieve

open MeasureTheory Real
open scoped FourierTransform ContDiff SchwartzMap ArithmeticFunction.Moebius

/-! ## The normalised exponent -/

/-- **The source's `(1+iξ)/log x`**, in this repository's normalisation of the Fourier
transform, where the source's `ξ` is scaled by `2π`. Step 1's expansion reads
`F(log_x d) = ∫ f(ξ) d^{-kernelArg x ξ} dξ`. -/
noncomputable def kernelArg (x ξ : ℝ) : ℂ :=
  (1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ)) / (Real.log x : ℂ)

/-- `Gap212.Sieve.kernelArg` matches the exponent step 1 produces. -/
theorem neg_kernelArg (x ξ : ℝ) :
    -kernelArg x ξ = -(1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ)) / (Real.log x : ℂ) := by
  rw [kernelArg, neg_div]

/-- **The real part of the exponent is `1/log x`, with no `ξ` in it.** This is the reason a single
`σ` controls the whole double integral, and hence the reason step 2's majorant — a function of `σ`
alone — suffices to license the interchange. -/
theorem kernelArg_re (x ξ : ℝ) : (kernelArg x ξ).re = 1 / Real.log x := by
  rw [kernelArg, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re]
  simp

/-! ## The kernel `K(ξ,ξ')`, at a general arithmetic weight -/

/-- **The summand of the source's kernel** at a general weight and general complex
exponents: `c(d,d') d^{-s} (d')^{-s'}`. At `c = Gap212.Sieve.recipPairWeight` this is the source's
`μ(d)μ(d')/([d,d'] d^s (d')^{s'})`. -/
noncomputable def pairKernelTerm (c : ℕ × ℕ → ℂ) (s s' : ℂ) (p : ℕ × ℕ) : ℂ :=
  c p * (p.1 : ℂ) ^ (-s) * (p.2 : ℂ) ^ (-s')

/-- **The source's kernel `K(ξ,ξ')`** at a general weight:
`K = ∑_{d,d'} c(d,d') d^{-s} (d')^{-s'}`. Convergent as soon as the weight's majorant is summable
(`Gap212.Sieve.summable_pairKernelTerm`). -/
noncomputable def pairKernel (c : ℕ × ℕ → ℂ) (s s' : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, pairKernelTerm c s s' p

/-- **What step 2 has to sum**: `‖c(d,d')‖ d^{-σ} (d')^{-σ}`, the modulus of a kernel term whose
exponents have real part `σ`. For the source's weight this is `Gap212.Sieve.pairMajorant`
(`Gap212.Sieve.weightMajorant_recipPairWeight`); for the totient weight it is
`Gap212.Sieve.pairTotientMajorant`. -/
noncomputable def weightMajorant (c : ℕ × ℕ → ℂ) (σ : ℝ) (p : ℕ × ℕ) : ℝ :=
  ‖c p‖ * (p.1 : ℝ) ^ (-σ) * (p.2 : ℝ) ^ (-σ)

/-- `Gap212.Sieve.weightMajorant` is non-negative. -/
theorem weightMajorant_nonneg (c : ℕ × ℕ → ℂ) (σ : ℝ) (p : ℕ × ℕ) :
    0 ≤ weightMajorant c σ p := by
  rw [weightMajorant]
  positivity

/-- **The modulus of a kernel term is exactly the majorant.** For exponents whose real parts are
both `σ`,

  `‖c(d,d') d^{-s} (d')^{-s'}‖ = ‖c(d,d')‖ d^{-σ} (d')^{-σ}`.

An equality, not a bound: the imaginary parts of the exponents contribute nothing to the modulus
(`Gap212.Sieve.norm_natCast_cpow_profileExponent`), which is why the interchange needs no estimate
beyond step 2. The degenerate pairs are covered by the weight's vanishing there — for them the
factor `0^{-σ}` is `0` or `1` according to the sign of `σ`, and neither answer is the majorant. -/
theorem norm_pairKernelTerm_of_re {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) {s s' : ℂ} {σ : ℝ} (hs : s.re = σ)
    (hs' : s'.re = σ) (p : ℕ × ℕ) : ‖pairKernelTerm c s s' p‖ = weightMajorant c σ p := by
  obtain ⟨d, d'⟩ := p
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp [pairKernelTerm, weightMajorant, hc (0, d') (Or.inl rfl)]
  rcases Nat.eq_zero_or_pos d' with hd' | hd'
  · subst hd'; simp [pairKernelTerm, weightMajorant, hc (d, 0) (Or.inr rfl)]
  rw [pairKernelTerm, weightMajorant, norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos hd, Complex.norm_natCast_cpow_of_pos hd',
    Complex.neg_re, Complex.neg_re, hs, hs']

/-- **The kernel converges absolutely** wherever both exponents have real part `σ` and the majorant
is summable at `σ` — which for the source's weight is step 2's
`Gap212.Sieve.summable_pairMajorant`. -/
theorem summable_pairKernelTerm {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) {σ : ℝ}
    (hsum : Summable (weightMajorant c σ)) {s s' : ℂ} (hs : s.re = σ) (hs' : s'.re = σ) :
    Summable fun p : ℕ × ℕ ↦ pairKernelTerm c s s' p := by
  refine Summable.of_norm ?_
  simpa only [norm_pairKernelTerm_of_re hc hs hs'] using hsum

/-- **The source's `K ≪ log³x`** in its general form, uniform in `ξ,ξ'`: the kernel is
bounded by the sum of its majorant. -/
theorem norm_pairKernel_le_tsum {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) {σ : ℝ}
    (hsum : Summable (weightMajorant c σ)) {s s' : ℂ} (hs : s.re = σ) (hs' : s'.re = σ) :
    ‖pairKernel c s s'‖ ≤ ∑' p : ℕ × ℕ, weightMajorant c σ p := by
  have hnorm : Summable fun p : ℕ × ℕ ↦ ‖pairKernelTerm c s s' p‖ := by
    simpa only [norm_pairKernelTerm_of_re hc hs hs'] using hsum
  rw [pairKernel]
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  exact le_of_eq (tsum_congr fun p ↦ norm_pairKernelTerm_of_re hc hs hs' p)

/-- Each kernel term is continuous in `(ξ,ξ')`. For `d = 0` or `d' = 0` the term vanishes
identically, so no continuity of `0 ^ z` is needed. -/
theorem continuous_pairKernelTerm_comp {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) (x : ℝ) (p : ℕ × ℕ) :
    Continuous fun w : ℝ × ℝ ↦ pairKernelTerm c (kernelArg x w.1) (kernelArg x w.2) p := by
  have hker : Continuous fun ξ : ℝ ↦ kernelArg x ξ := by unfold kernelArg; fun_prop
  obtain ⟨d, d'⟩ := p
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hz : (fun w : ℝ × ℝ ↦ pairKernelTerm c (kernelArg x w.1) (kernelArg x w.2) (0, d'))
        = fun _ ↦ (0 : ℂ) := by
      funext w; simp [pairKernelTerm, hc (0, d') (Or.inl rfl)]
    rw [hz]; exact continuous_const
  rcases Nat.eq_zero_or_pos d' with hd' | hd'
  · subst hd'
    have hz : (fun w : ℝ × ℝ ↦ pairKernelTerm c (kernelArg x w.1) (kernelArg x w.2) (d, 0))
        = fun _ ↦ (0 : ℂ) := by
      funext w; simp [pairKernelTerm, hc (d, 0) (Or.inr rfl)]
    rw [hz]; exact continuous_const
  refine Continuous.mul (Continuous.mul continuous_const ?_) ?_
  · exact Continuous.const_cpow ((hker.comp continuous_fst).neg)
      (Or.inl (Nat.cast_ne_zero.2 (by omega)))
  · exact Continuous.const_cpow ((hker.comp continuous_snd).neg)
      (Or.inl (Nat.cast_ne_zero.2 (by omega)))

/-- **The kernel is continuous in `(ξ,ξ')`.** The series converges uniformly, being dominated term
by term by the `ξ`-free summable majorant of step 2, so `continuous_tsum` applies. This is what
supplies measurability of the integrand of the interchanged integral. -/
theorem continuous_pairKernel_comp {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) {x : ℝ}
    (hsum : Summable (weightMajorant c (1 / Real.log x))) :
    Continuous fun w : ℝ × ℝ ↦ pairKernel c (kernelArg x w.1) (kernelArg x w.2) := by
  simp only [pairKernel]
  refine continuous_tsum (u := weightMajorant c (1 / Real.log x))
    (fun p ↦ continuous_pairKernelTerm_comp hc x p) hsum fun p w ↦ ?_
  exact le_of_eq (norm_pairKernelTerm_of_re hc (kernelArg_re x w.1) (kernelArg_re x w.2) p)

/-! ## The term the interchange moves -/

/-- **The `(d,d')`-th summand of the integrand**: `f(ξ) g(ξ') c(d,d') d^{-s(ξ)} (d')^{-s(ξ')}`.
Summing over `(d,d')` first gives `f(ξ)g(ξ')K(ξ,ξ')` (`Gap212.Sieve.tsum_pairFubiniTerm`);
integrating first gives `c(d,d') · F(log_x d) · G(log_x d')`
(`Gap212.Sieve.integral_pairFubiniTerm`). The interchange is the assertion that the two agree. -/
noncomputable def pairFubiniTerm (c : ℕ × ℕ → ℂ) (F G : ℝ → ℝ) (x : ℝ) (p : ℕ × ℕ) (w : ℝ × ℝ) :
    ℂ :=
  profileFourier F w.1 * profileFourier G w.2 *
    pairKernelTerm c (kernelArg x w.1) (kernelArg x w.2) p

/-- `Gap212.Sieve.pairFubiniTerm` written as a constant times a product of a function of `ξ` and a
function of `ξ'` — the shape both Fubini for products and `MeasureTheory.Integrable.mul_prod`
require. -/
theorem pairFubiniTerm_eq (c : ℕ × ℕ → ℂ) (F G : ℝ → ℝ) (x : ℝ) (p : ℕ × ℕ) (w : ℝ × ℝ) :
    pairFubiniTerm c F G x p w
      = c p * ((profileFourier F w.1 * (p.1 : ℂ) ^ (-(1 + 2 * (π : ℂ) * Complex.I * (w.1 : ℂ)) /
              (Real.log x : ℂ))) *
            (profileFourier G w.2 * (p.2 : ℂ) ^ (-(1 + 2 * (π : ℂ) * Complex.I * (w.2 : ℂ)) /
              (Real.log x : ℂ)))) := by
  rw [pairFubiniTerm, pairKernelTerm, ← neg_kernelArg, ← neg_kernelArg]
  ring

/-- **The modulus of the summand factors completely**, into `‖f(ξ)‖`, `‖g(ξ')‖` and the majorant at
`σ = 1/log x`. The `ξ`-independence of the third factor is `Gap212.Sieve.kernelArg_re`. -/
theorem norm_pairFubiniTerm {c : ℕ × ℕ → ℂ} (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0)
    (F G : ℝ → ℝ) (x : ℝ) (p : ℕ × ℕ) (w : ℝ × ℝ) :
    ‖pairFubiniTerm c F G x p w‖
      = ‖profileFourier F w.1‖ * ‖profileFourier G w.2‖ *
          weightMajorant c (1 / Real.log x) p := by
  rw [pairFubiniTerm, norm_mul, norm_mul,
    norm_pairKernelTerm_of_re hc (kernelArg_re x w.1) (kernelArg_re x w.2)]

/-- **Each summand is integrable** over `ℝ × ℝ`: step 1's
`Gap212.Sieve.integrable_profileFourier_mul_cpow` in each variable, multiplied into a product
measure. For `d = 0` or `d' = 0` the summand vanishes. -/
theorem integrable_pairFubiniTerm {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) {x : ℝ}
    (hx : 1 < x) (p : ℕ × ℕ) : Integrable (pairFubiniTerm c F G x p) := by
  obtain ⟨d, d'⟩ := p
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hz : pairFubiniTerm c F G x (0, d') = fun _ ↦ (0 : ℂ) := by
      funext w; simp [pairFubiniTerm, pairKernelTerm, hc (0, d') (Or.inl rfl)]
    rw [hz]; exact integrable_zero _ _ _
  rcases Nat.eq_zero_or_pos d' with hd' | hd'
  · subst hd'
    have hz : pairFubiniTerm c F G x (d, 0) = fun _ ↦ (0 : ℂ) := by
      funext w; simp [pairFubiniTerm, pairKernelTerm, hc (d, 0) (Or.inr rfl)]
    rw [hz]; exact integrable_zero _ _ _
  have h1 := integrable_profileFourier_mul_cpow hF hFc hx hd
  have h2 := integrable_profileFourier_mul_cpow hG hGc hx hd'
  rw [funext fun w ↦ pairFubiniTerm_eq c F G x (d, d') w, Measure.volume_eq_prod]
  exact (h1.mul_prod h2).const_mul _

/-- **Integrating one summand is step 1, twice.** Fubini for a product of one-variable functions
(`MeasureTheory.integral_prod_mul`, which needs no integrability hypothesis) splits the integral,
and each factor is `Gap212.Sieve.ofReal_logx_eq_integral_profileFourier`:

  `∫∫ f(ξ)g(ξ') c(d,d') d^{-s(ξ)}(d')^{-s(ξ')} = c(d,d') · F(log_x d) G(log_x d')`. -/
theorem integral_pairFubiniTerm {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) {x : ℝ}
    (hx : 1 < x) (p : ℕ × ℕ) :
    ∫ w : ℝ × ℝ, pairFubiniTerm c F G x p w
      = c p * ((F (Notation.logx x p.1) : ℂ) * (G (Notation.logx x p.2) : ℂ)) := by
  obtain ⟨d, d'⟩ := p
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hz : pairFubiniTerm c F G x (0, d') = fun _ ↦ (0 : ℂ) := by
      funext w; simp [pairFubiniTerm, pairKernelTerm, hc (0, d') (Or.inl rfl)]
    rw [hz]; simp [hc (0, d') (Or.inl rfl)]
  rcases Nat.eq_zero_or_pos d' with hd' | hd'
  · subst hd'
    have hz : pairFubiniTerm c F G x (d, 0) = fun _ ↦ (0 : ℂ) := by
      funext w; simp [pairFubiniTerm, pairKernelTerm, hc (d, 0) (Or.inr rfl)]
    rw [hz]; simp [hc (d, 0) (Or.inr rfl)]
  have key := @MeasureTheory.integral_prod_mul ℝ ℝ _ _ (volume : Measure ℝ) (volume : Measure ℝ)
    _ _ ℂ _
    (fun ξ : ℝ ↦ profileFourier F ξ *
      (d : ℂ) ^ (-(1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ)) / (Real.log x : ℂ)))
    (fun ξ : ℝ ↦ profileFourier G ξ *
      (d' : ℂ) ^ (-(1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ)) / (Real.log x : ℂ)))
  rw [funext fun w ↦ pairFubiniTerm_eq c F G x (d, d') w, Measure.volume_eq_prod,
    MeasureTheory.integral_const_mul, key,
    ← ofReal_logx_eq_integral_profileFourier hF hFc hx hd,
    ← ofReal_logx_eq_integral_profileFourier hG hGc hx hd']

/-! ## The two hypotheses of the interchange, and the interchange -/

/-- **The integral of the modulus of one summand, computed exactly.** Equal to `(∫‖f‖)(∫‖g‖)` times
the majorant — so summing over `(d,d')` is step 2 times a constant. -/
theorem integral_norm_pairFubiniTerm {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) (F G : ℝ → ℝ) (x : ℝ) (p : ℕ × ℕ) :
    ∫ w : ℝ × ℝ, ‖pairFubiniTerm c F G x p w‖
      = ((∫ ξ : ℝ, ‖profileFourier F ξ‖) * ∫ ξ : ℝ, ‖profileFourier G ξ‖) *
          weightMajorant c (1 / Real.log x) p := by
  have key := @MeasureTheory.integral_prod_mul ℝ ℝ _ _ (volume : Measure ℝ) (volume : Measure ℝ)
    _ _ ℝ _ (fun ξ : ℝ ↦ ‖profileFourier F ξ‖) (fun ξ : ℝ ↦ ‖profileFourier G ξ‖)
  rw [funext fun w ↦ norm_pairFubiniTerm hc F G x p w, Measure.volume_eq_prod,
    MeasureTheory.integral_mul_const, key]

/-- **The summability hypothesis of the interchange**: `∑_{d,d'} ∫ ‖term‖ < ∞`. This is step 2 at
`σ = 1/log x`, scaled by `(∫‖f‖)(∫‖g‖)`. -/
theorem summable_integral_norm_pairFubiniTerm {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) (F G : ℝ → ℝ) {x : ℝ}
    (hsum : Summable (weightMajorant c (1 / Real.log x))) :
    Summable fun p : ℕ × ℕ ↦ ∫ w : ℝ × ℝ, ‖pairFubiniTerm c F G x p w‖ := by
  simpa only [integral_norm_pairFubiniTerm hc F G x] using hsum.mul_left _

/-- **Summing the summand over `(d,d')` reproduces `f(ξ)g(ξ')K(ξ,ξ')`.** Pure algebra: the profile
factors do not depend on `(d,d')`. -/
theorem tsum_pairFubiniTerm (c : ℕ × ℕ → ℂ) (F G : ℝ → ℝ) (x : ℝ) (w : ℝ × ℝ) :
    ∑' p : ℕ × ℕ, pairFubiniTerm c F G x p w
      = profileFourier F w.1 * profileFourier G w.2 *
          pairKernel c (kernelArg x w.1) (kernelArg x w.2) := by
  rw [pairKernel]
  exact tsum_mul_left

/-- **The interchange** at a general weight: for smooth compactly
supported profiles `F, G`, `x > 1`, and a weight vanishing on the
degenerate pairs whose majorant is summable at `1/log x`,

  `∑_{d,d'} c(d,d') · F(log_x d) · G(log_x d') = ∫_{ℝ²} f(ξ) g(ξ') K(ξ,ξ') d(ξ,ξ')`,

where `f = Gap212.Sieve.profileFourier F`, `g = Gap212.Sieve.profileFourier G` and `K` is
`Gap212.Sieve.pairKernel c` at the exponents `Gap212.Sieve.kernelArg x ξ`,
`Gap212.Sieve.kernelArg x ξ'`.

The `d = 0` and `d' = 0` terms of the left-hand sum vanish by hypothesis, so the sum over all of
`ℕ × ℕ` is the source's sum over positive `d, d'`. -/
theorem tsum_weightPairSum_eq_integral {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) {x : ℝ}
    (hx : 1 < x) (hsum : Summable (weightMajorant c (1 / Real.log x))) :
    ∑' p : ℕ × ℕ, c p * ((F (Notation.logx x p.1) : ℂ) * (G (Notation.logx x p.2) : ℂ))
      = ∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 *
          pairKernel c (kernelArg x w.1) (kernelArg x w.2) := by
  calc ∑' p : ℕ × ℕ, c p * ((F (Notation.logx x p.1) : ℂ) * (G (Notation.logx x p.2) : ℂ))
      = ∑' p : ℕ × ℕ, ∫ w : ℝ × ℝ, pairFubiniTerm c F G x p w :=
        tsum_congr fun p ↦ (integral_pairFubiniTerm hc hF hFc hG hGc hx p).symm
    _ = ∫ w : ℝ × ℝ, ∑' p : ℕ × ℕ, pairFubiniTerm c F G x p w :=
        MeasureTheory.integral_tsum_of_summable_integral_norm
          (fun p ↦ integrable_pairFubiniTerm hc hF hFc hG hGc hx p)
          (summable_integral_norm_pairFubiniTerm hc F G hsum)
    _ = ∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 *
          pairKernel c (kernelArg x w.1) (kernelArg x w.2) :=
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun w ↦ tsum_pairFubiniTerm c F G x w)

/-- **The interchanged integrand is integrable.** `f(ξ)g(ξ')` is integrable on the product and `K`
is bounded (`Gap212.Sieve.norm_pairKernel_le_tsum`) and continuous
(`Gap212.Sieve.continuous_pairKernel_comp`). This is what lets the product-measure integral be
written as an iterated one. -/
theorem integrable_pairKernel_mul {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) {x : ℝ}
    (hsum : Summable (weightMajorant c (1 / Real.log x))) :
    Integrable fun w : ℝ × ℝ ↦ profileFourier F w.1 * profileFourier G w.2 *
      pairKernel c (kernelArg x w.1) (kernelArg x w.2) := by
  rw [Measure.volume_eq_prod]
  exact ((integrable_profileFourier hF hFc).mul_prod (integrable_profileFourier hG hGc)).mul_bdd
    (continuous_pairKernel_comp hc hsum).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w ↦
      norm_pairKernel_le_tsum hc hsum (kernelArg_re x w.1) (kernelArg_re x w.2))

/-- **The interchange in the source's own shape**: an
iterated integral `∫ dξ ∫ dξ'`. Equal to `Gap212.Sieve.tsum_weightPairSum_eq_integral`'s
product-measure integral by Fubini, which applies because the integrand is integrable
(`Gap212.Sieve.integrable_pairKernel_mul`). -/
theorem tsum_weightPairSum_eq_integral_integral {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) {x : ℝ}
    (hx : 1 < x) (hsum : Summable (weightMajorant c (1 / Real.log x))) :
    ∑' p : ℕ × ℕ, c p * ((F (Notation.logx x p.1) : ℂ) * (G (Notation.logx x p.2) : ℂ))
      = ∫ ξ : ℝ, ∫ ξ' : ℝ, profileFourier F ξ * profileFourier G ξ' *
          pairKernel c (kernelArg x ξ) (kernelArg x ξ') := by
  rw [tsum_weightPairSum_eq_integral hc hF hFc hG hGc hx hsum, Measure.volume_eq_prod]
  refine (@MeasureTheory.integral_integral ℝ ℝ ℂ _ _ (volume : Measure ℝ) (volume : Measure ℝ)
    _ _ _ _ (fun ξ ξ' : ℝ ↦ profileFourier F ξ * profileFourier G ξ' *
      pairKernel c (kernelArg x ξ) (kernelArg x ξ')) ?_).symm
  have := integrable_pairKernel_mul hc hF hFc hG hGc hsum
  rwa [Measure.volume_eq_prod] at this

/-! ## The source's weight: the reciprocal kernel -/

/-- **The source's arithmetic weight**: `μ(d)μ(d')/[d,d']`. -/
noncomputable def recipPairWeight (p : ℕ × ℕ) : ℂ :=
  (μ p.1 : ℂ) * (μ p.2 : ℂ) / (Nat.lcm p.1 p.2 : ℂ)

/-- The source's weight vanishes on the degenerate pairs — `μ(0) = 0` — so summing over all of
`ℕ × ℕ` is the source's sum over positive `d, d'`. -/
theorem recipPairWeight_eq_zero : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → recipPairWeight p = 0 := by
  rintro ⟨d, d'⟩ (h | h) <;> simp only at h <;> subst h <;> simp [recipPairWeight]

/-- **The source's kernel `K(ξ,ξ')`**:
`K = ∑_{d,d'} μ(d)μ(d') / ([d,d'] d^s (d')^{s'})`. -/
noncomputable def recipKernel (s s' : ℂ) : ℂ := pairKernel recipPairWeight s s'

/-- **The source's majorant is the source's weight's majorant**: step 2's
`Gap212.Sieve.pairMajorant σ (d,d')` is `‖μ(d)μ(d')/[d,d']‖ d^{-σ}(d')^{-σ}`. This one computation
is the whole arithmetic content of instantiating the interchange at the reciprocal kernel. -/
theorem weightMajorant_recipPairWeight (σ : ℝ) (p : ℕ × ℕ) :
    weightMajorant recipPairWeight σ p = pairMajorant σ p := by
  obtain ⟨d, d'⟩ := p
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp [weightMajorant, recipPairWeight, pairMajorant]
  rcases Nat.eq_zero_or_pos d' with hd' | hd'
  · subst hd'; simp [weightMajorant, recipPairWeight, pairMajorant]
  have hlcm : (Nat.lcm d d' : ℝ) ≠ 0 := by
    have : Nat.lcm d d' ≠ 0 := Nat.lcm_ne_zero (by omega) (by omega)
    exact_mod_cast this
  have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdr' : (0 : ℝ) < (d' : ℝ) := by exact_mod_cast hd'
  have hp : ((d : ℝ) ^ σ) ≠ 0 := by positivity
  have hp' : ((d' : ℝ) ^ σ) ≠ 0 := by positivity
  rw [weightMajorant, recipPairWeight, pairMajorant, norm_div,
    Real.rpow_neg hdr.le, Real.rpow_neg hdr'.le]
  simp only [norm_mul, Complex.norm_intCast, Complex.norm_natCast]
  field_simp

/-- Step 2's summability, in the shape the generic interchange asks for. -/
theorem summable_weightMajorant_recipPairWeight {σ : ℝ} (hσ : 0 < σ) :
    Summable (weightMajorant recipPairWeight σ) := by
  simpa only [funext fun p ↦ weightMajorant_recipPairWeight σ p] using summable_pairMajorant hσ

/-- **The modulus of a kernel term is exactly step 2's majorant.** For exponents whose real parts
are both `σ`,

  `‖μ(d)μ(d')/([d,d'] d^s (d')^{s'})‖ = |μ(d)μ(d')| / ([d,d'] d^σ (d')^σ)`. -/
theorem norm_recipKernelTerm_of_re {s s' : ℂ} {σ : ℝ} (hs : s.re = σ) (hs' : s'.re = σ)
    (p : ℕ × ℕ) : ‖pairKernelTerm recipPairWeight s s' p‖ = pairMajorant σ p := by
  rw [norm_pairKernelTerm_of_re recipPairWeight_eq_zero hs hs', weightMajorant_recipPairWeight]

/-- **The source's kernel converges absolutely** wherever both exponents have real part `σ > 0`. -/
theorem summable_recipKernelTerm {s s' : ℂ} {σ : ℝ} (hσ : 0 < σ) (hs : s.re = σ)
    (hs' : s'.re = σ) : Summable fun p : ℕ × ℕ ↦ pairKernelTerm recipPairWeight s s' p :=
  summable_pairKernelTerm recipPairWeight_eq_zero
    (summable_weightMajorant_recipPairWeight hσ) hs hs'

/-- **The source's `K ≪ log³x`**, uniform in `ξ,ξ'`: if both exponents have real part
`σ > 0` then `‖K‖ ≤ Z(1+σ)³`. At `σ = 1/log x` this is the source's `ζ(1+1/log x)³`. -/
theorem norm_recipKernel_le {s s' : ℂ} {σ : ℝ} (hσ : 0 < σ) (hs : s.re = σ) (hs' : s'.re = σ) :
    ‖recipKernel s s'‖ ≤ zetaSeries (1 + σ) ^ 3 := by
  rw [recipKernel]
  refine (norm_pairKernel_le_tsum recipPairWeight_eq_zero
    (summable_weightMajorant_recipPairWeight hσ) hs hs').trans ?_
  rw [tsum_congr fun p ↦ weightMajorant_recipPairWeight σ p]
  exact tsum_pairMajorant_le hσ

/-- **The interchange at the source's kernel**: for smooth compactly
supported profiles `F, G` and `x > 1`,

  `∑_{d,d'} μ(d)μ(d')/[d,d'] · F(log_x d) · G(log_x d')`
  `  = ∫_{ℝ²} f(ξ) g(ξ') K(ξ,ξ') d(ξ,ξ')`.

The `d = 0` and `d' = 0` terms of the left-hand sum vanish, since `μ(0) = 0`, so the sum over all
of `ℕ × ℕ` is the source's sum over positive `d, d'`. -/
theorem tsum_recipPairSum_eq_integral {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) {x : ℝ}
    (hx : 1 < x) :
    ∑' p : ℕ × ℕ, (μ p.1 : ℂ) * (μ p.2 : ℂ) / (Nat.lcm p.1 p.2 : ℂ) *
        ((F (Notation.logx x p.1) : ℂ) * (G (Notation.logx x p.2) : ℂ))
      = ∫ w : ℝ × ℝ, profileFourier F w.1 * profileFourier G w.2 *
          recipKernel (kernelArg x w.1) (kernelArg x w.2) := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  exact tsum_weightPairSum_eq_integral recipPairWeight_eq_zero hF hFc hG hGc hx
    (summable_weightMajorant_recipPairWeight (by positivity))

/-- **The interchange at the source's kernel, in the source's iterated form** `∫ dξ ∫ dξ'`. -/
theorem tsum_recipPairSum_eq_integral_integral {F G : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) {x : ℝ}
    (hx : 1 < x) :
    ∑' p : ℕ × ℕ, (μ p.1 : ℂ) * (μ p.2 : ℂ) / (Nat.lcm p.1 p.2 : ℂ) *
        ((F (Notation.logx x p.1) : ℂ) * (G (Notation.logx x p.2) : ℂ))
      = ∫ ξ : ℝ, ∫ ξ' : ℝ, profileFourier F ξ * profileFourier G ξ' *
          recipKernel (kernelArg x ξ) (kernelArg x ξ') := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  exact tsum_weightPairSum_eq_integral_integral recipPairWeight_eq_zero hF hFc hG hGc hx
    (summable_weightMajorant_recipPairWeight (by positivity))

end Gap212.Sieve
