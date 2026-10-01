/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Step 2 of Polymath8b Lemma 4.1: the majorant that licenses Fubini

Having expanded the profiles (step 1, `Gap212.Sieve.Polymath41Fourier`), the source's proof
interchanges the `d,d'`-sum with the `ξ,ξ'`-integrals, and justifies the interchange with one bound:

> `∑_{d,d'} |μ(d)μ(d')| / ([d,d'] d^{1/log x} (d')^{1/log x})`
> `  = ∏_p (1 + 2/p^{1+1/log x} + 1/p^{1+2/log x}) ≤ ζ(1 + 1/log x)^3 ≪ log³x.`

`Gap212.Sieve.tsum_pairMajorant_le` is that bound, at a general `σ > 0` in place of `1/log x`, and
`Gap212.Sieve.summable_pairMajorant` is the summability it carries. Together they are exactly the
hypothesis Fubini needs on the arithmetic side.

## What is proved, and how it differs from the source's route

The source passes through the Euler product. This file does not: the Euler product is only the
source's *route* to the inequality, and the inequality is all that the Fubini step consumes. What is
proved instead is sharper than `ζ(1+σ)³`, namely
`∑_{d,d'} |μ(d)μ(d')| / ([d,d'] d^σ (d')^σ) ≤ Z(1+σ)² · Z(1+2σ)`

(`Gap212.Sieve.tsum_pairMajorant_le_mul`), which then gives `Z(1+σ)³` because `Z` is antitone
(`Gap212.Sieve.zetaSeries_antitone`). The mechanism is the substitution behind the source's Euler
factorisation, used directly on the pair rather than prime by prime: write `g = (d,d')`,
`d = g·a`, `d' = g·b`; then `[d,d'] = g·a·b` — with no squarefreeness needed, because
`Nat.gcd_mul_lcm` alone gives it — and the term becomes exactly
`1/(a^{1+σ} b^{1+σ} g^{1+2σ})`. The map `(d,d') ↦ (a,b,g)` is injective
(`Gap212.Sieve.gcdSplit_injective`), so the pair sum is dominated by a *product* of three
one-variable `p`-series, which is `Z(1+σ)²Z(1+2σ)`.

`Z` here is `Gap212.Sieve.zetaSeries`, the real Dirichlet series `∑_{n≥1} n^{-s}`, written without
`riemannZeta`: nothing downstream of this bound needs the analytic continuation, and identifying
`riemannZeta` with its Dirichlet series would add an obligation that buys nothing. `riemannZeta`
does enter Lemma 4.1's proof — at step 4, where the *pole* at `s = 1` is the whole point — but not
here.

## The totient kernel

This file is about `1/[d,d']` and says nothing about `1/φ([d,d'])`. The totient kernel needs its
own majorant, and it is **not** this one: `φ([d,d']) ≤ [d,d']`, so the totient terms are *larger*
and the bound does not transfer by monotonicity in the direction one wants. Nor does the
substitution transfer directly: `φ(gab) = φ(g)φ(a)φ(b)` needs `g, a, b` pairwise coprime, which
they are not in general here (`g` may share factors with `a`). The totient kernel's majorant is
`Gap212.Sieve.Polymath41MajorantTotient`.

## Main definitions

* `Gap212.Sieve.zetaSeries`: `Z(s) = ∑_{n≥1} n^{-s}`, the majorant's building block.
* `Gap212.Sieve.pairMajorant`: the source's summand `|μ(d)μ(d')|/([d,d'] d^σ (d')^σ)`.
* `Gap212.Sieve.gcdSplit`: `(d,d') ↦ (d/(d,d'), d'/(d,d'), (d,d'))`.

## Main results

* `Gap212.Sieve.summable_pairMajorant`: the double sum converges absolutely, for every `σ > 0`.
* `Gap212.Sieve.tsum_pairMajorant_le`: the source's `ζ(1+σ)³` bound.
-/

@[expose] public section

namespace Gap212.Sieve

open Real
open scoped ArithmeticFunction.Moebius

/-! ## The real Dirichlet series of `1` -/

/-- **`Z(s) = ∑_{n≥1} n^{-s}`**, the Riemann zeta function on the real half-line `s > 1` written as
its Dirichlet series. The `n = 0` term is `0 ^ (-s) = 0` for `s ≠ 0`, so summing over all of `ℕ`
costs nothing and saves shifting the index. -/
noncomputable def zetaSeries (s : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-s)

/-- The `p`-series test: `Gap212.Sieve.zetaSeries` converges for `s > 1`. -/
theorem summable_natRpow_neg {s : ℝ} (hs : 1 < s) : Summable fun n : ℕ ↦ (n : ℝ) ^ (-s) :=
  Real.summable_nat_rpow.2 (by linarith)

/-- Every term of `Gap212.Sieve.zetaSeries` is non-negative. -/
theorem natRpow_neg_nonneg (s : ℝ) (n : ℕ) : 0 ≤ (n : ℝ) ^ (-s) :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- The `p`-series test in the shape the product formula for double series asks for. -/
theorem summable_norm_natRpow_neg {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ ↦ ‖(n : ℝ) ^ (-s)‖ := by
  simpa only [Real.norm_eq_abs] using (summable_natRpow_neg hs).abs

/-- The same for the two-variable product `a^{-s}b^{-t}`. -/
theorem summable_norm_pairRpow {s t : ℝ} (hs : 1 < s) (ht : 1 < t) :
    Summable fun y : ℕ × ℕ ↦ ‖(y.1 : ℝ) ^ (-s) * (y.2 : ℝ) ^ (-t)‖ := by
  simpa only [Real.norm_eq_abs] using ((summable_natRpow_neg hs).mul_of_nonneg
    (summable_natRpow_neg ht) (natRpow_neg_nonneg _) (natRpow_neg_nonneg _)).abs

/-- **`Gap212.Sieve.zetaSeries` is antitone on `(1,∞)`**, term by term: `n^{-t} ≤ n^{-s}` when
`s ≤ t`, because `1 ≤ n` on every term that is not zero. This is what turns the sharp bound
`Z(1+σ)²Z(1+2σ)` of `Gap212.Sieve.tsum_pairMajorant_le_mul` into the source's `ζ(1+σ)³`. -/
theorem zetaSeries_antitone {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) : zetaSeries t ≤ zetaSeries s := by
  refine Summable.tsum_le_tsum (fun n ↦ ?_) (summable_natRpow_neg (lt_of_lt_of_le hs hst))
    (summable_natRpow_neg hs)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

/-! ## The two majorants and the injection between their index sets -/

/-- **The source's summand**: `|μ(d)μ(d')| / ([d,d'] d^σ (d')^σ)`, as a function of the
pair. At `σ = 1/log x` this is the modulus of the term the Fourier expansion of step 1 produces,
since `‖d^{-(1+2πiξ)/log x}‖ = d^{-1/log x}`
(`Gap212.Sieve.norm_natCast_cpow_profileExponent`). -/
noncomputable def pairMajorant (σ : ℝ) (p : ℕ × ℕ) : ℝ :=
  |(μ p.1 : ℝ)| * |(μ p.2 : ℝ)| /
    ((Nat.lcm p.1 p.2 : ℝ) * (p.1 : ℝ) ^ σ * (p.2 : ℝ) ^ σ)

/-- **The product majorant**: `a^{-(1+σ)} · b^{-(1+σ)} · g^{-(1+2σ)}`, a function on `ℕ³` that is a
product of three one-variable `p`-series terms and therefore sums to `Z(1+σ)²Z(1+2σ)`. -/
noncomputable def tripleMajorant (σ : ℝ) (q : ℕ × ℕ × ℕ) : ℝ :=
  (q.1 : ℝ) ^ (-(1 + σ)) * ((q.2.1 : ℝ) ^ (-(1 + σ)) * (q.2.2 : ℝ) ^ (-(1 + 2 * σ)))

/-- **The substitution behind the source's Euler factorisation**, as a map of index sets:
`(d,d') ↦ (d/(d,d'), d'/(d,d'), (d,d'))`. -/
def gcdSplit (p : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2, Nat.gcd p.1 p.2)

/-- **`Gap212.Sieve.gcdSplit` is injective.** The third coordinate recovers the gcd and the first
two are the cofactors, so `d = g·a` and `d' = g·b` reconstruct the pair (also when `g = 0`, since
then `d = d' = 0`). Injectivity, rather than bijectivity onto the pairwise-coprime triples, is all
the majorant needs. -/
theorem gcdSplit_injective : Function.Injective gcdSplit := by
  rintro ⟨d, d'⟩ ⟨e, e'⟩ h
  simp only [gcdSplit, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine Prod.ext ?_ ?_
  · rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_left d d'), h1, h3,
      Nat.mul_div_cancel' (Nat.gcd_dvd_left e e')]
  · rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_right d d'), h2, h3,
      Nat.mul_div_cancel' (Nat.gcd_dvd_right e e')]

/-! ## The pointwise comparison -/

/-- `Gap212.Sieve.pairMajorant` is non-negative. -/
theorem pairMajorant_nonneg (σ : ℝ) (p : ℕ × ℕ) : 0 ≤ pairMajorant σ p := by
  unfold pairMajorant
  positivity

/-- `Gap212.Sieve.tripleMajorant` is non-negative. -/
theorem tripleMajorant_nonneg (σ : ℝ) (q : ℕ × ℕ × ℕ) : 0 ≤ tripleMajorant σ q := by
  unfold tripleMajorant
  positivity

/-- **The identity that makes the substitution exact.** With `g = (d,d')`, `a = d/g`, `b = d'/g`
and `d, d' ≥ 1`,

  `[d,d'] · d^σ · (d')^σ = a^{1+σ} · b^{1+σ} · g^{1+2σ}`.

No squarefreeness is used: `[d,d'] = g·a·b` already follows from `Nat.gcd_mul_lcm`. This is the
pair-level form of the source's local factor `K_p`. -/
theorem lcm_mul_rpow_eq {d d' : ℕ} (hd : 1 ≤ d) (hd' : 1 ≤ d') (σ : ℝ) :
    (Nat.lcm d d' : ℝ) * (d : ℝ) ^ σ * (d' : ℝ) ^ σ
      = ((d / Nat.gcd d d' : ℕ) : ℝ) ^ (1 + σ) * ((d' / Nat.gcd d d' : ℕ) : ℝ) ^ (1 + σ) *
        ((Nat.gcd d d' : ℕ) : ℝ) ^ (1 + 2 * σ) := by
  set g := Nat.gcd d d' with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hd
  set a := d / g
  set b := d' / g
  have hda : d = g * a := (Nat.mul_div_cancel' (Nat.gcd_dvd_left d d')).symm
  have hdb : d' = g * b := (Nat.mul_div_cancel' (Nat.gcd_dvd_right d d')).symm
  have hlcm : Nat.lcm d d' = g * a * b := Nat.eq_of_mul_eq_mul_left hg <| by
    rw [hgdef, Nat.gcd_mul_lcm, ← hgdef, hda, hdb]; ring
  have hgR : (0 : ℝ) < (g : ℝ) := Nat.cast_pos.2 hg
  have haR : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.2 (Nat.div_pos (Nat.gcd_le_left _ hd) hg)
  have hbR : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.2 (Nat.div_pos (Nat.gcd_le_right _ hd') hg)
  rw [hlcm, hda, hdb]
  push_cast
  rw [Real.mul_rpow hgR.le haR.le, Real.mul_rpow hgR.le hbR.le,
    Real.rpow_add haR, Real.rpow_add hbR, Real.rpow_add hgR,
    Real.rpow_one, Real.rpow_one, Real.rpow_one,
    show (2 : ℝ) * σ = σ + σ from by ring, Real.rpow_add hgR]
  ring

/-- **The pointwise comparison.** Every term of `Gap212.Sieve.pairMajorant` is at most the term of
`Gap212.Sieve.tripleMajorant` at its `Gap212.Sieve.gcdSplit` image: the denominators agree exactly
(`Gap212.Sieve.lcm_mul_rpow_eq`) and the numerator `|μ(d)μ(d')|` is at most `1`
(`ArithmeticFunction.abs_moebius_le_one`). The degenerate cases `d = 0` and `d' = 0` are
`0 ≤ tripleMajorant`, since `μ 0 = 0`.

No hypothesis on `σ` is needed: the comparison is an identity of denominators plus `|μ| ≤ 1`, and
`σ > 0` enters only where the majorant has to be *summable*. -/
theorem pairMajorant_le_tripleMajorant (σ : ℝ) (p : ℕ × ℕ) :
    pairMajorant σ p ≤ tripleMajorant σ (gcdSplit p) := by
  obtain ⟨d, d'⟩ := p
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simpa [pairMajorant] using tripleMajorant_nonneg σ _
  rcases Nat.eq_zero_or_pos d' with hd' | hd'
  · subst hd'
    simpa [pairMajorant] using tripleMajorant_nonneg σ _
  have hμ (n : ℕ) : |(μ n : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one : |(μ n : ℤ)| ≤ 1)
  have hnum : |(μ d : ℝ)| * |(μ d' : ℝ)| ≤ 1 := mul_le_one₀ (hμ d) (abs_nonneg _) (hμ d')
  have hg : 0 < Nat.gcd d d' := Nat.gcd_pos_of_pos_left _ hd
  have haR : (0 : ℝ) < ((d / Nat.gcd d d' : ℕ) : ℝ) :=
    Nat.cast_pos.2 (Nat.div_pos (Nat.gcd_le_left _ hd) hg)
  have hbR : (0 : ℝ) < ((d' / Nat.gcd d d' : ℕ) : ℝ) :=
    Nat.cast_pos.2 (Nat.div_pos (Nat.gcd_le_right _ hd') hg)
  have hgR : (0 : ℝ) < ((Nat.gcd d d' : ℕ) : ℝ) := Nat.cast_pos.2 hg
  have htriple : tripleMajorant σ (gcdSplit (d, d')) = 1 /
      (((d / Nat.gcd d d' : ℕ) : ℝ) ^ (1 + σ) * ((d' / Nat.gcd d d' : ℕ) : ℝ) ^ (1 + σ) *
        ((Nat.gcd d d' : ℕ) : ℝ) ^ (1 + 2 * σ)) := by
    rw [tripleMajorant, gcdSplit, Real.rpow_neg haR.le, Real.rpow_neg hbR.le,
      Real.rpow_neg hgR.le, one_div, mul_inv, mul_inv, mul_assoc]
  rw [pairMajorant, htriple, lcm_mul_rpow_eq hd hd' σ]
  gcongr

/-! ## Summability and the bound -/

/-- `Gap212.Sieve.tripleMajorant` is summable over `ℕ³` for `σ > 0`, being a product of three
convergent `p`-series. -/
theorem summable_tripleMajorant {σ : ℝ} (hσ : 0 < σ) : Summable (tripleMajorant σ) := by
  have h1 : Summable fun n : ℕ ↦ (n : ℝ) ^ (-(1 + σ)) := summable_natRpow_neg (by linarith)
  exact h1.mul_of_nonneg (h1.mul_of_nonneg (summable_natRpow_neg (by linarith))
    (natRpow_neg_nonneg _) (natRpow_neg_nonneg _)) (natRpow_neg_nonneg _)
    fun _ ↦ mul_nonneg (natRpow_neg_nonneg _ _) (natRpow_neg_nonneg _ _)

/-- **`∑_{a,b,g} a^{-(1+σ)}b^{-(1+σ)}g^{-(1+2σ)} = Z(1+σ)²Z(1+2σ)`**, by two applications of the
product formula for absolutely convergent double series. -/
theorem tsum_tripleMajorant {σ : ℝ} (hσ : 0 < σ) :
    ∑' q, tripleMajorant σ q
      = zetaSeries (1 + σ) * (zetaSeries (1 + σ) * zetaSeries (1 + 2 * σ)) := by
  have e1 : (∑' n : ℕ, (n : ℝ) ^ (-(1 + σ))) * (∑' n : ℕ, (n : ℝ) ^ (-(1 + 2 * σ)))
      = ∑' y : ℕ × ℕ, (y.1 : ℝ) ^ (-(1 + σ)) * (y.2 : ℝ) ^ (-(1 + 2 * σ)) :=
    tsum_mul_tsum_of_summable_norm (summable_norm_natRpow_neg (by linarith))
      (summable_norm_natRpow_neg (by linarith))
  rw [zetaSeries, zetaSeries, e1]
  exact (tsum_mul_tsum_of_summable_norm (summable_norm_natRpow_neg (by linarith))
    (summable_norm_pairRpow (s := 1 + σ) (t := 1 + 2 * σ) (by linarith) (by linarith))).symm

/-- **The double sum converges absolutely**, for every `σ > 0`: the comparison
`Gap212.Sieve.pairMajorant_le_tripleMajorant` transported along the injection
`Gap212.Sieve.gcdSplit`. -/
theorem summable_pairMajorant {σ : ℝ} (hσ : 0 < σ) : Summable (pairMajorant σ) :=
  Summable.of_nonneg_of_le (pairMajorant_nonneg σ)
    (pairMajorant_le_tripleMajorant σ)
    ((summable_tripleMajorant hσ).comp_injective gcdSplit_injective)

/-- **The sharp form of the source's Fubini bound.**

  `∑_{d,d'} |μ(d)μ(d')| / ([d,d'] d^σ (d')^σ) ≤ Z(1+σ)² · Z(1+2σ)`.

The source states `ζ(1+σ)³`, which `Gap212.Sieve.tsum_pairMajorant_le` derives from this by
antitonicity of `Z`. -/
theorem tsum_pairMajorant_le_mul {σ : ℝ} (hσ : 0 < σ) :
    ∑' p, pairMajorant σ p
      ≤ zetaSeries (1 + σ) * (zetaSeries (1 + σ) * zetaSeries (1 + 2 * σ)) := by
  calc ∑' p, pairMajorant σ p
      ≤ ∑' p, tripleMajorant σ (gcdSplit p) :=
        Summable.tsum_le_tsum (pairMajorant_le_tripleMajorant σ)
          (summable_pairMajorant hσ)
          ((summable_tripleMajorant hσ).comp_injective gcdSplit_injective)
    _ ≤ ∑' q, tripleMajorant σ q :=
        tsum_comp_le_tsum_of_inj (summable_tripleMajorant hσ)
          (tripleMajorant_nonneg σ) gcdSplit_injective
    _ = _ := tsum_tripleMajorant hσ

/-- **The source's Fubini bound**: for every `σ > 0`,

  `∑_{d,d'} |μ(d)μ(d')| / ([d,d'] d^σ (d')^σ) ≤ Z(1+σ)³`,

with `Z(s) = ∑_{n≥1} n^{-s}`. At `σ = 1/log x` this is the source's `ζ(1+1/log x)³`, and with
`Z(1+σ) ≪ 1/σ` it is the source's `≪ log³x`. -/
theorem tsum_pairMajorant_le {σ : ℝ} (hσ : 0 < σ) :
    ∑' p, pairMajorant σ p ≤ zetaSeries (1 + σ) ^ 3 := by
  refine (tsum_pairMajorant_le_mul hσ).trans ?_
  have hz : 0 ≤ zetaSeries (1 + σ) := tsum_nonneg (natRpow_neg_nonneg _)
  calc zetaSeries (1 + σ) * (zetaSeries (1 + σ) * zetaSeries (1 + 2 * σ))
      ≤ zetaSeries (1 + σ) * (zetaSeries (1 + σ) * zetaSeries (1 + σ)) := by
        gcongr; exact zetaSeries_antitone (by linarith) (by linarith)
    _ = zetaSeries (1 + σ) ^ 3 := by ring

end Gap212.Sieve
