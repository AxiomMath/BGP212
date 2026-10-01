/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41Euler
public import Gap212.Sieve.Polymath41Fubini
public import Gap212.Sieve.Polymath41FubiniTotient

/-!
# The kernel of Polymath8b Lemma 4.1 *is* a Dirichlet series

`Gap212.Sieve.Polymath41Fubini` produces the source's kernel as a **pair** sum,

  `K(s,s') = ∑_{(d,d') ∈ ℕ × ℕ} c(d,d') d^{-s} (d')^{-s'}`,

and `Gap212.Sieve.Polymath41Kernel` produces the Dirichlet coefficient the source's Euler
factorisation is about,

  `a(n) = (1/n) ∑_{[d,d']=n} μ(d)μ(d') d^{-s} (d')^{-s'}`.

The first sums over pairs, the second over the *fibres* of `(d,d') ↦ [d,d']`, and this file
performs the regrouping. The fibre is `Gap212.Sieve.lcmFibre`, the licence is the absolute
convergence of step 2, and the vehicle is `HasSum.tsum_fiberwise`.

## The regrouping, and why it is not `Finset.sum_biUnion`

The pair sum is an infinite `tsum` over `ℕ × ℕ`, so the partition into fibres is not a finite
rearrangement. `HasSum.tsum_fiberwise` is the statement that a `HasSum` may be regrouped along an
*arbitrary* map, which is where step 2's summability is spent — it is what gives the `HasSum` in
the first place (`Gap212.Sieve.summable_pairKernelTerm`).

Two facts make the fibres finite sums rather than sub-`tsum`s:

* for `n ≠ 0` the preimage of `{n}` under `(d,d') ↦ [d,d']` is exactly the `Finset`
  `Gap212.Sieve.lcmFibre n` (`Gap212.Sieve.mem_lcmFibre`);
* the preimage of `{0}` is the set of degenerate pairs, on which every weight this development uses
  vanishes, so its contribution is `0` — matching `Gap212.Sieve.lcmFibre 0 = ∅`.

Both are packaged in `Gap212.Sieve.tsum_lcmPreimage_eq_sum_lcmFibre`, stated for an arbitrary
function vanishing on the degenerate pairs so that the *real* majorant and the *complex* kernel
term use one lemma.

## The generic layer, again

As in `Gap212.Sieve.Polymath41Fubini`, everything is proved for an arbitrary weight
`c : ℕ × ℕ → ℂ`: the regrouping does not know which kernel it is regrouping. The two kernels part
company only at the last step, where the fibre sum is identified with the *named* coefficient —
`Gap212.Sieve.kernelCoeff` for `1/[d,d']` and `Gap212.Sieve.kernelCoeffTotient` for `1/φ([d,d'])` —
and those two identifications are separate theorems whose proofs differ in exactly the denominator,
`n` against `φ(n)`.

## Main results

* `Gap212.Sieve.tsum_lcmPreimage_eq_sum_lcmFibre`: the fibre of `(d,d') ↦ [d,d']` is the `Finset`
  `Gap212.Sieve.lcmFibre`, including at `n = 0`.
* `Gap212.Sieve.hasSum_sum_lcmFibre_pairKernelTerm`: the regrouping of the kernel, at a general
  weight, as a `HasSum`; `Gap212.Sieve.pairKernel_eq_tsum_sum_lcmFibre` its `tsum` form.
* `Gap212.Sieve.hasSum_sum_lcmFibre_weightMajorant`: the same for the real majorant, which is what
  bounds the Dirichlet coefficient.
* `Gap212.Sieve.recipKernel_eq_tsum_kernelCoeff`,
  `Gap212.Sieve.totientKernel_eq_tsum_kernelCoeffTotient`: **the two identifications** — each kernel
  is the Dirichlet series of its own coefficient.
* `Gap212.Sieve.summable_norm_kernelCoeff`, `Gap212.Sieve.summable_norm_kernelCoeffTotient`: the
  summability that licenses the Euler product, which is step 2 collected by `n = [d,d']`.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset
open scoped ArithmeticFunction.Moebius

/-! ## The fibre of `(d,d') ↦ [d,d']` is `Gap212.Sieve.lcmFibre` -/

/-- **The sub-sum over one fibre of `(d,d') ↦ [d,d']` is a finite sum over
`Gap212.Sieve.lcmFibre`.** For `n ≠ 0` the preimage of `{n}` *is* that `Finset`
(`Gap212.Sieve.mem_lcmFibre`); for `n = 0` the preimage is the set of degenerate pairs, where the
hypothesis makes every term vanish, and `Gap212.Sieve.lcmFibre 0` is empty, so both sides are `0`.

Stated for an arbitrary target monoid because the two consumers are the complex kernel term and the
real majorant. -/
theorem tsum_lcmPreimage_eq_sum_lcmFibre {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    {f : ℕ × ℕ → M} (hf : ∀ q : ℕ × ℕ, q.1 = 0 ∨ q.2 = 0 → f q = 0) (n : ℕ) :
    ∑' q : ((fun q : ℕ × ℕ ↦ Nat.lcm q.1 q.2) ⁻¹' {n}), f ↑q = ∑ q ∈ lcmFibre n, f q := by
  rw [_root_.tsum_subtype]
  rcases eq_or_ne n 0 with rfl | hn
  · have hzero : ∀ q : ℕ × ℕ,
        ((fun q : ℕ × ℕ ↦ Nat.lcm q.1 q.2) ⁻¹' {0}).indicator f q = 0 := by
      intro q
      refine Set.indicator_apply_eq_zero.2 fun hq ↦ ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hq
      exact hf q (Nat.lcm_eq_zero_iff.1 hq)
    rw [tsum_congr hzero, tsum_zero]
    simp [lcmFibre]
  · refine (tsum_eq_sum (s := lcmFibre n) fun q hq ↦ ?_).trans (Finset.sum_congr rfl fun q hq ↦ ?_)
    · refine Set.indicator_apply_eq_zero.2 fun hmem ↦ ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hmem
      exact absurd (mem_lcmFibre.2 ⟨hn, hmem⟩) hq
    · exact Set.indicator_of_mem (by simpa using (mem_lcmFibre.1 hq).2) f

/-! ## The regrouping, at a general weight -/

/-- **A weight vanishing on the degenerate pairs makes its kernel term vanish there.** -/
theorem pairKernelTerm_eq_zero_of_weight {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) (s s' : ℂ) :
    ∀ q : ℕ × ℕ, q.1 = 0 ∨ q.2 = 0 → pairKernelTerm c s s' q = 0 := by
  intro q hq
  rw [pairKernelTerm, hc q hq, zero_mul, zero_mul]

/-- **The kernel, regrouped over the fibres of `(d,d') ↦ [d,d']`** — the step the source takes
between the pair sum and the Euler product. The regrouping of an infinite sum is licensed
by absolute convergence, which at exponents of real part `σ` is exactly step 2's summability of the
weight's majorant. -/
theorem hasSum_sum_lcmFibre_pairKernelTerm {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) {σ : ℝ}
    (hsum : Summable (weightMajorant c σ)) {s s' : ℂ} (hs : s.re = σ) (hs' : s'.re = σ) :
    HasSum (fun n : ℕ ↦ ∑ q ∈ lcmFibre n, pairKernelTerm c s s' q) (pairKernel c s s') := by
  have hS := (summable_pairKernelTerm hc hsum hs hs').hasSum
  have h := hS.tsum_fiberwise fun q : ℕ × ℕ ↦ Nat.lcm q.1 q.2
  rw [funext fun n ↦ tsum_lcmPreimage_eq_sum_lcmFibre
    (pairKernelTerm_eq_zero_of_weight hc s s') n] at h
  exact h

/-- The regrouping in `tsum` form: the kernel is the Dirichlet series whose `n`-th coefficient is
the fibre sum. -/
theorem pairKernel_eq_tsum_sum_lcmFibre {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) {σ : ℝ}
    (hsum : Summable (weightMajorant c σ)) {s s' : ℂ} (hs : s.re = σ) (hs' : s'.re = σ) :
    pairKernel c s s' = ∑' n : ℕ, ∑ q ∈ lcmFibre n, pairKernelTerm c s s' q :=
  (hasSum_sum_lcmFibre_pairKernelTerm hc hsum hs hs').tsum_eq.symm

/-- **The same regrouping for the real majorant.** This is what bounds the Dirichlet coefficient,
and hence what supplies the summability the Euler product needs — step 2 collected by
`n = [d,d']`, not a new estimate. -/
theorem hasSum_sum_lcmFibre_weightMajorant {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) {σ : ℝ}
    (hsum : Summable (weightMajorant c σ)) :
    HasSum (fun n : ℕ ↦ ∑ q ∈ lcmFibre n, weightMajorant c σ q)
      (∑' q : ℕ × ℕ, weightMajorant c σ q) := by
  have hzero : ∀ q : ℕ × ℕ, q.1 = 0 ∨ q.2 = 0 → weightMajorant c σ q = 0 := by
    intro q hq
    rw [weightMajorant, hc q hq, norm_zero, zero_mul, zero_mul]
  have h := hsum.hasSum.tsum_fiberwise fun q : ℕ × ℕ ↦ Nat.lcm q.1 q.2
  rw [funext fun n ↦ tsum_lcmPreimage_eq_sum_lcmFibre hzero n] at h
  exact h

/-- The fibre sums of the majorant are summable — the hypothesis of
`Gap212.Sieve.summable_norm_kernelCoeff`. -/
theorem summable_sum_lcmFibre_weightMajorant {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) {σ : ℝ}
    (hsum : Summable (weightMajorant c σ)) :
    Summable fun n : ℕ ↦ ∑ q ∈ lcmFibre n, weightMajorant c σ q :=
  (hasSum_sum_lcmFibre_weightMajorant hc hsum).summable

/-- **The fibre sum is dominated by the fibre sum of the majorant.** The triangle inequality on a
finite sum, with `Gap212.Sieve.norm_pairKernelTerm_of_re` making each bound an equality. -/
theorem norm_sum_lcmFibre_pairKernelTerm_le {c : ℕ × ℕ → ℂ}
    (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0) {σ : ℝ} {s s' : ℂ} (hs : s.re = σ)
    (hs' : s'.re = σ) (n : ℕ) :
    ‖∑ q ∈ lcmFibre n, pairKernelTerm c s s' q‖ ≤ ∑ q ∈ lcmFibre n, weightMajorant c σ q := by
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun q _ ↦ ?_))
  exact norm_pairKernelTerm_of_re hc hs hs' q

/-! ## The reciprocal kernel is the Dirichlet series of `Gap212.Sieve.kernelCoeff` -/

/-- **The fibre sum of the reciprocal weight is `Gap212.Sieve.kernelCoeff`.** On the fibre the
denominator `[d,d']` is the constant `n`, so it comes out of the sum — which is precisely why
`Gap212.Sieve.kernelCoeff` was defined with the `1/n` outside. -/
theorem sum_lcmFibre_pairKernelTerm_recip (s s' : ℂ) (n : ℕ) :
    ∑ q ∈ lcmFibre n, pairKernelTerm recipPairWeight s s' q = kernelCoeff s s' n := by
  rw [kernelCoeff, Finset.sum_div]
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  rw [pairKernelTerm, recipPairWeight, (mem_lcmFibre.1 hq).2]
  ring

/-- **The source's kernel `K` is the Dirichlet series `∑_n a(n)`**, at exponents of equal real part
`σ > 0`. It is what lets the Euler factorisation of `Gap212.Sieve.Polymath41Euler` speak about the
kernel of the interchange. -/
theorem recipKernel_eq_tsum_kernelCoeff {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ} (hs : s.re = σ)
    (hs' : s'.re = σ) : recipKernel s s' = ∑' n : ℕ, kernelCoeff s s' n := by
  rw [recipKernel, pairKernel_eq_tsum_sum_lcmFibre recipPairWeight_eq_zero
    (summable_weightMajorant_recipPairWeight hσ) hs hs']
  exact tsum_congr fun n ↦ sum_lcmFibre_pairKernelTerm_recip s s' n

/-- **`∑_n ‖a(n)‖ < ∞`**, the one hypothesis
`ArithmeticFunction.IsMultiplicative.eulerProduct_tprod` asks for beyond multiplicativity. It is
step 2's `Gap212.Sieve.summable_pairMajorant` collected by `n = [d,d']`. -/
theorem summable_norm_kernelCoeff {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ} (hs : s.re = σ)
    (hs' : s'.re = σ) : Summable fun n : ℕ ↦ ‖kernelCoeff s s' n‖ := by
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (summable_sum_lcmFibre_weightMajorant recipPairWeight_eq_zero
      (summable_weightMajorant_recipPairWeight hσ))
  rw [← sum_lcmFibre_pairKernelTerm_recip s s' n]
  exact norm_sum_lcmFibre_pairKernelTerm_le recipPairWeight_eq_zero hs hs' n

/-- `Gap212.Sieve.kernelCoeff` is summable — the Dirichlet series of the kernel converges. -/
theorem summable_kernelCoeff {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ} (hs : s.re = σ) (hs' : s'.re = σ) :
    Summable (kernelCoeff s s') :=
  Summable.of_norm (summable_norm_kernelCoeff hσ hs hs')

/-! ## The totient kernel is the Dirichlet series of `Gap212.Sieve.kernelCoeffTotient`

A **separate** derivation, not a rescaling: the fibre sum is the same but the constant coming out
of it is `φ(n)` rather than `n`, and `φ(2) = 1 ≠ 2`. -/

/-- **The fibre sum of the totient weight is `Gap212.Sieve.kernelCoeffTotient`.** On the fibre
`φ([d,d'])` is the constant `φ(n)`. -/
theorem sum_lcmFibre_pairKernelTerm_totient (s s' : ℂ) (n : ℕ) :
    ∑ q ∈ lcmFibre n, pairKernelTerm totientPairWeight s s' q = kernelCoeffTotient s s' n := by
  rw [kernelCoeffTotient, Finset.sum_div]
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  rw [pairKernelTerm, totientPairWeight, (mem_lcmFibre.1 hq).2]
  ring

/-- **The totient kernel is the Dirichlet series `∑_n a^φ(n)`** — the closing sentence of the
source's proof, at the level of the regrouping. Separate from
`Gap212.Sieve.recipKernel_eq_tsum_kernelCoeff` because the two kernels are separate assertions;
what is shared is the generic regrouping, not the identification. -/
theorem totientKernel_eq_tsum_kernelCoeffTotient {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ} (hs : s.re = σ)
    (hs' : s'.re = σ) : totientKernel s s' = ∑' n : ℕ, kernelCoeffTotient s s' n := by
  rw [totientKernel, pairKernel_eq_tsum_sum_lcmFibre totientPairWeight_eq_zero
    (summable_weightMajorant_totientPairWeight hσ) hs hs']
  exact tsum_congr fun n ↦ sum_lcmFibre_pairKernelTerm_totient s s' n

/-- **`∑_n ‖a^φ(n)‖ < ∞`**, from the totient majorant of
`Gap212.Sieve.Polymath41MajorantTotient`. The reciprocal kernel's majorant does **not** serve
here: `φ([d,d']) ≤ [d,d']` makes the totient terms larger. -/
theorem summable_norm_kernelCoeffTotient {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ} (hs : s.re = σ)
    (hs' : s'.re = σ) : Summable fun n : ℕ ↦ ‖kernelCoeffTotient s s' n‖ := by
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (summable_sum_lcmFibre_weightMajorant totientPairWeight_eq_zero
      (summable_weightMajorant_totientPairWeight hσ))
  rw [← sum_lcmFibre_pairKernelTerm_totient s s' n]
  exact norm_sum_lcmFibre_pairKernelTerm_le totientPairWeight_eq_zero hs hs' n

/-- `Gap212.Sieve.kernelCoeffTotient` is summable. -/
theorem summable_kernelCoeffTotient {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ} (hs : s.re = σ)
    (hs' : s'.re = σ) : Summable (kernelCoeffTotient s s') :=
  Summable.of_norm (summable_norm_kernelCoeffTotient hσ hs hs')

end Gap212.Sieve
