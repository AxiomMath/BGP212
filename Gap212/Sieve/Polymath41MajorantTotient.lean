/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41Majorant
public import PrimeGapsTheory.ArithmeticFunction.Estimates
public import PrimeGapsTheory.Analysis.Zeta

/-!
# The Fubini majorant of step 2 for the **totient** kernel

`Gap212.Sieve.tsum_pairMajorant_le` (`Gap212.Sieve.Polymath41Majorant`) bounds the reciprocal
kernel's pair sum `∑_{d,d'} |μ(d)μ(d')| / ([d,d'] d^σ (d')^σ)` by `Z(1+σ)³`. That bound is for
`1/[d,d']` **only**, and it does not transfer: `φ([d,d']) ≤ [d,d']`, so the totient terms are the
larger ones and monotonicity runs the wrong way. This file proves the totient kernel's own
majorant,

  `∑_{d,d'} |μ(d)μ(d')| / (φ([d,d']) d^σ (d')^σ) ≤ T(σ)² · T(2σ)`

(`Gap212.Sieve.tsum_pairTotientMajorant_le_mul`) for every `σ > 0`, where

  `T(σ) = ∑_{n≥1} |μ(n)| / (φ(n) n^σ)`

is `Gap212.Sieve.totientKernelSeries`, together with the summability that Fubini consumes
(`Gap212.Sieve.summable_pairTotientMajorant`) and a crude closed form in the reciprocal kernel's `Z`
(`Gap212.Sieve.tsum_pairTotientMajorant_le`, giving `Z(1+σ)⁶`).

## What survives from the reciprocal route, and what replaces the rest

The *substitution* survives: with `g = (d,d')`, `a = d/g`, `b = d'/g` one still has `[d,d'] = abg`
from `Nat.gcd_mul_lcm` alone, and `(d,d') ↦ (a,b,g)` is still injective, so the reused
`Gap212.Sieve.gcdSplit` and `Gap212.Sieve.gcdSplit_injective` do their work here unchanged.

What does **not** survive is the exact factorisation of the denominator. The reciprocal proof's
`Gap212.Sieve.lcm_mul_rpow_eq` is an *identity*, `[d,d'] d^σ (d')^σ = a^{1+σ}b^{1+σ}g^{1+2σ}`, and
its totient analogue `φ(abg) = φ(a)φ(b)φ(g)` is **false** in general, since `g` need not be coprime
to `a`. Two remedies are available and this file takes the second:

* *squarefreeness*: `|μ(d)μ(d')| ≠ 0` forces `d,d'` squarefree, whence `a,b,g` are pairwise coprime
  and `φ(abg) = φ(a)φ(b)φ(g)` after all. This gives an identity, but it pays for it with a
  squarefreeness hypothesis at every step of the algebra.
* *super-multiplicativity*: `φ(a)φ(b) ≤ φ(ab)` holds outright (`Nat.totient_super_multiplicative`),
  so `φ(a)φ(b)φ(g) ≤ φ(abg)` with **no** coprimality and no squarefreeness
  (`Gap212.Sieve.totient_mul_totient_mul_totient_le`). An *inequality* in the denominator is all a
  majorant ever needed, and it points the right way: it makes `1/φ([d,d'])` at most
  `1/(φ(a)φ(b)φ(g))`.

So the pair term is dominated by a product of three one-variable series, exactly as on the
reciprocal side — but the series is `T`, not `Z`, and the terms are `1/(φ(n)n^σ)` rather than
`n^{-(1+σ)}`. Squarefreeness is still used, but only to read `|μ(d)μ(d')| = 1` off as the numerator
`|μ(a)μ(b)μ(g)|` of the majorant, never inside the arithmetic.

## `T(σ) ≤ Z(1+σ)²`, and how much that loses

`T` is finite for every `σ > 0`, which is the substance here: the elementary `|μ(n)|/φ(n) ≤ 1` is
useless, because `∑ n^{-σ}` diverges at every `σ ≤ 1`. What makes it work is `n ≤ τ₂(n)φ(n)`
(`ArithmeticFunction.le_tau₂_mul_totient`, from `∑_{e ∣ n} φ(e) = n` with `φ(e) ∣ φ(n)`), which
turns the term into `τ₂(n)n^{-(1+σ)}`; that sums to `Z(1+σ)²` because `τ₂`'s Dirichlet series is
`ζ²` (`hasSum_tau_div_rpow`, transported to the real `Z` by
`Gap212.Sieve.riemannZeta_eq_ofReal_zetaSeries`).

Hence the closed form `Z(1+σ)⁶`, which is **weaker than the reciprocal kernel's `Z(1+σ)³` in the
rate, not merely in shape**: `Z(1+σ) ≍ 1/σ`, so the reciprocal bound is `≍ σ^{-3}` while this one
is `≍ σ^{-6}`; at `σ = 1/log x` that is `log⁶x` against the source's `log³x`. The loss is entirely
in `n ≤ τ₂(n)φ(n)`, which costs one extra `ζ` per variable — the truth is `T(σ) ≍ σ^{-1}`, since
`T(σ) = ∏_p (1 + 1/((p-1)p^σ))`, so `T(σ)²T(2σ) ≍ σ^{-3}` has the reciprocal rate. The sharp form
`Gap212.Sieve.tsum_pairTotientMajorant_le_mul` is `T`-valued and off by only `|μ| ≤ 1`.
`Gap212.Sieve.tsum_pairTotientMajorant_le` is enough for the interchange itself, which consumes
finiteness and not a rate.

The rate is recovered in `Gap212.Sieve.Polymath41MajorantTotientSharp`:
`Gap212.Sieve.totientKernelSeries_le_sharp` proves `T(σ) ≤ Z(1+σ)·Z(2)²` and
`Gap212.Sieve.tsum_pairTotientMajorant_le_sharp` proves `Z(2)⁶·Z(1+σ)³` for the pair sum, the
reciprocal kernel's rate with an absolute constant in place of the three extra `ζ`s.

## No oddness hypothesis
Totient-kernel arguments that pass through `(μ * φ)` need `2 ∣ W` and oddness, because the local
factor `p - 2` of `(μ * φ)` **vanishes at `p = 2`**, so a lower bound on `(μ * φ)(r)` is false
without excluding `r = 2`. Nothing here passes through `(μ * φ)`. The two arithmetic inputs are
`φ(a)φ(b) ≤ φ(ab)`, which has no local factor at all, and `n ≤ τ₂(n)φ(n)`, whose local factor at
`p = 2` reads `2 ≤ 2·1` — an *equality*, so `p = 2` is the extremal prime of the bound rather than a
degenerate one. No hypothesis of the form `2 ∣ W`, oddness, or coprimality to `W` is needed, and
none is assumed: the statements below quantify over all `d, d'`.

## Main definitions

* `Gap212.Sieve.totientKernelTerm`: `|μ(n)| / (φ(n) n^σ)`, the one-variable term.
* `Gap212.Sieve.totientKernelSeries`: `T(σ) = ∑_{n} |μ(n)|/(φ(n) n^σ)`.
* `Gap212.Sieve.pairTotientMajorant`: the summand `|μ(d)μ(d')|/(φ([d,d']) d^σ (d')^σ)`.
* `Gap212.Sieve.tripleTotientMajorant`: `T`'s term at `a`, at `b`, and at `g` with `σ` doubled.

## Main results

* `Gap212.Sieve.summable_pairTotientMajorant`: the double sum converges, for every `σ > 0`.
* `Gap212.Sieve.tsum_pairTotientMajorant_le_mul`: the sharp bound `T(σ)²T(2σ)`.
* `Gap212.Sieve.tsum_pairTotientMajorant_le`: the crude closed form `Z(1+σ)⁶`.
-/

@[expose] public section

namespace Gap212.Sieve

open Real
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ## The divisor function's Dirichlet series, in real form -/

/-- **`ζ(σ)` is the real series `Z(σ)`** for real `σ > 1`: both are the sum of the same real
`p`-series, the complex one being the image of the real one under `Real.toComplex`. This is
what reads `hasSum_tau_div_rpow` — whose value is `(ζ(σ)^r).re` — as a statement about
`Gap212.Sieve.zetaSeries`. -/
theorem riemannZeta_eq_ofReal_zetaSeries {σ : ℝ} (hσ : 1 < σ) :
    riemannZeta (σ : ℂ) = ((zetaSeries σ : ℝ) : ℂ) := by
  have hr : HasSum (fun n : ℕ ↦ ((((n : ℝ) ^ (-σ)) : ℝ) : ℂ)) ((zetaSeries σ : ℝ) : ℂ) := by
    simpa [zetaSeries, Function.comp_def] using
      (summable_natRpow_neg hσ).hasSum.map Complex.ofRealHom Complex.continuous_ofReal
  refine (hasSum_riemannZeta (s := (σ : ℂ)) (by simpa)).unique (hr.congr_fun fun n ↦ ?_)
  simp [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.cpow_neg]

/-- **`∑_{n≥1} τ₂(n) n^{-s} = Z(s)²`** for `s > 1`: the divisor function's Dirichlet series is
`ζ²`, here in real form. This is the whole of the quantitative input to
`Gap212.Sieve.totientKernelSeries_le`. -/
theorem tsum_tauTwo_div_rpow {s : ℝ} (hs : 1 < s) :
    ∑' n : ℕ, (τ₂ n : ℝ) / (n : ℝ) ^ s = zetaSeries s ^ 2 := by
  simpa [riemannZeta_eq_ofReal_zetaSeries hs, ← Complex.ofReal_pow] using
    (hasSum_tau_div_rpow (r := 2) hs).tsum_eq

/-- The same series is summable, which is what the comparison for
`Gap212.Sieve.summable_totientKernelTerm` needs. -/
theorem summable_tauTwo_div_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ ↦ (τ₂ n : ℝ) / (n : ℝ) ^ s :=
  (hasSum_tau_div_rpow (r := 2) hs).summable

/-! ## The one-variable totient kernel series `T` -/

/-- **The one-variable term** `|μ(n)| / (φ(n) n^σ)`. At `n = 0` the numerator and the denominator
both vanish, so the term is `0` and summing over all of `ℕ` costs nothing. -/
noncomputable def totientKernelTerm (σ : ℝ) (n : ℕ) : ℝ :=
  |(μ n : ℝ)| / ((n.totient : ℝ) * (n : ℝ) ^ σ)

/-- **`T(σ) = ∑_{n≥1} |μ(n)| / (φ(n) n^σ)`**, the totient kernel's one-variable series. It plays
here the role `Gap212.Sieve.zetaSeries` plays for the reciprocal kernel, and it is *not* comparable
to it term by term in the useful direction: `1/φ(n) ≥ 1/n`. -/
noncomputable def totientKernelSeries (σ : ℝ) : ℝ := ∑' n : ℕ, totientKernelTerm σ n

/-- Every term of `Gap212.Sieve.totientKernelTerm` is non-negative. -/
theorem totientKernelTerm_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ totientKernelTerm σ n :=
  div_nonneg (abs_nonneg _) (by positivity)

/-- **The pointwise bound that makes `T` finite**: `|μ(n)|/(φ(n)n^σ) ≤ τ₂(n) n^{-(1+σ)}`, from
`|μ(n)| ≤ 1` and `n ≤ τ₂(n)φ(n)` (`ArithmeticFunction.le_tau₂_mul_totient`). No hypothesis on `σ`,
and none on `n`: at `n = 0` both sides are `0`. -/
theorem totientKernelTerm_le_tauTwo (σ : ℝ) (n : ℕ) :
    totientKernelTerm σ n ≤ (τ₂ n : ℝ) / (n : ℝ) ^ (1 + σ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [totientKernelTerm]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmu : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have key : (n : ℝ) ≤ τ₂ n * n.totient := by
    exact_mod_cast ArithmeticFunction.le_tau₂_mul_totient (n := n)
  rw [totientKernelTerm, Real.rpow_add hn', Real.rpow_one,
    div_le_div_iff₀ (by positivity) (by positivity)]
  calc _ ≤ 1 * ((τ₂ n : ℝ) * n.totient * (n : ℝ) ^ σ) := by gcongr
    _ = _ := by ring

/-- **`T(σ)` converges for every `σ > 0`**, by comparison with the divisor series. -/
theorem summable_totientKernelTerm {σ : ℝ} (hσ : 0 < σ) : Summable (totientKernelTerm σ) :=
  Summable.of_nonneg_of_le (totientKernelTerm_nonneg σ) (totientKernelTerm_le_tauTwo σ)
    (summable_tauTwo_div_rpow (by linarith))

/-- `T(σ) ≥ 0`. -/
theorem totientKernelSeries_nonneg (σ : ℝ) : 0 ≤ totientKernelSeries σ :=
  tsum_nonneg (totientKernelTerm_nonneg σ)

/-- **`T(σ) ≤ Z(1+σ)²`** for `σ > 0`. This is the file's only lossy step: the truth is
`T(σ) ≍ 1/σ`, while `Z(1+σ)² ≍ 1/σ²`. -/
theorem totientKernelSeries_le {σ : ℝ} (hσ : 0 < σ) :
    totientKernelSeries σ ≤ zetaSeries (1 + σ) ^ 2 :=
  (Summable.tsum_le_tsum (totientKernelTerm_le_tauTwo σ) (summable_totientKernelTerm hσ)
    (summable_tauTwo_div_rpow (by linarith))).trans_eq (tsum_tauTwo_div_rpow (by linarith))

/-- The one-variable series in the shape the product formula for double series asks for. -/
theorem summable_norm_totientKernelTerm {σ : ℝ} (hσ : 0 < σ) :
    Summable fun n : ℕ ↦ ‖totientKernelTerm σ n‖ := by
  simpa only [Real.norm_eq_abs] using (summable_totientKernelTerm hσ).abs

/-- The same for the two-variable product `T`-term at exponents `s` and `t`. -/
theorem summable_norm_pairTotientKernelTerm {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Summable fun y : ℕ × ℕ ↦ ‖totientKernelTerm s y.1 * totientKernelTerm t y.2‖ := by
  simpa only [Real.norm_eq_abs] using ((summable_totientKernelTerm hs).mul_of_nonneg
    (summable_totientKernelTerm ht) (totientKernelTerm_nonneg s) (totientKernelTerm_nonneg t)).abs

/-! ## The two majorants -/

/-- **The totient kernel's summand**: `|μ(d)μ(d')| / (φ([d,d']) d^σ (d')^σ)`. This is the source's
majorant summand with `[d,d']` replaced by `φ([d,d'])`, which is the entry that the `k`-tuple
totient kernel `φ(W ∏_i [d_i,d_i'])` produces coordinatewise. -/
noncomputable def pairTotientMajorant (σ : ℝ) (p : ℕ × ℕ) : ℝ :=
  |(μ p.1 : ℝ)| * |(μ p.2 : ℝ)| /
    ((Nat.totient (Nat.lcm p.1 p.2) : ℝ) * (p.1 : ℝ) ^ σ * (p.2 : ℝ) ^ σ)

/-- **The product majorant**: `T`'s term at `a` and at `b` with exponent `σ`, and at `g` with
exponent `2σ` — the exponent `g` inherits from appearing in both `d = ga` and `d' = gb`. -/
noncomputable def tripleTotientMajorant (σ : ℝ) (q : ℕ × ℕ × ℕ) : ℝ :=
  totientKernelTerm σ q.1 * (totientKernelTerm σ q.2.1 * totientKernelTerm (2 * σ) q.2.2)

/-- `Gap212.Sieve.pairTotientMajorant` is non-negative. -/
theorem pairTotientMajorant_nonneg (σ : ℝ) (p : ℕ × ℕ) : 0 ≤ pairTotientMajorant σ p :=
  div_nonneg (by positivity) (by positivity)

/-- `Gap212.Sieve.tripleTotientMajorant` is non-negative. -/
theorem tripleTotientMajorant_nonneg (σ : ℝ) (q : ℕ × ℕ × ℕ) : 0 ≤ tripleTotientMajorant σ q :=
  mul_nonneg (totientKernelTerm_nonneg _ _)
    (mul_nonneg (totientKernelTerm_nonneg _ _) (totientKernelTerm_nonneg _ _))

/-! ## The splitting, and the inequality that replaces the reciprocal identity -/

/-- **`[d,d'] = a·b·g`** with `g = (d,d')`, `a = d/g`, `b = d'/g`, for `d, d' ≥ 1`. Only
`Nat.gcd_mul_lcm` is used; this is the `ℕ`-level content of the reciprocal kernel's
`Gap212.Sieve.lcm_mul_rpow_eq`, and it is the part of that route which *does* transfer. -/
theorem lcm_eq_div_gcd_mul {d d' g a b : ℕ} (hg : 0 < g) (hgg : Nat.gcd d d' = g)
    (hda : d = g * a) (hdb : d' = g * b) : Nat.lcm d d' = a * b * g := by
  refine Nat.eq_of_mul_eq_mul_left hg ?_
  rw [← hgg, Nat.gcd_mul_lcm, hgg, hda, hdb]
  ring

/-- **`φ(a)φ(b)φ(g) ≤ φ(abg)`**, with no coprimality and no squarefreeness: two applications of
`Nat.totient_super_multiplicative`. This inequality is what replaces the reciprocal kernel's exact
factorisation `[d,d'] d^σ (d')^σ = a^{1+σ}b^{1+σ}g^{1+2σ}`, whose totient analogue
`φ(abg) = φ(a)φ(b)φ(g)` is false. -/
theorem totient_mul_totient_mul_totient_le (a b g : ℕ) :
    a.totient * b.totient * g.totient ≤ (a * b * g).totient :=
  le_trans (Nat.mul_le_mul_right _ (Nat.totient_super_multiplicative a b))
    (Nat.totient_super_multiplicative (a * b) g)

/-- **The pointwise comparison.** Every term of `Gap212.Sieve.pairTotientMajorant` is at most the
term of `Gap212.Sieve.tripleTotientMajorant` at its `Gap212.Sieve.gcdSplit` image.

The two ingredients are disjoint: `Gap212.Sieve.totient_mul_totient_mul_totient_le` handles the
denominator and uses nothing about `μ`; squarefreeness — which `|μ(d)μ(d')| ≠ 0` supplies, the
alternative being `0 ≤ tripleTotientMajorant` — is used only to know that the numerators
`|μ(a)|`, `|μ(b)|`, `|μ(g)|` of the majorant are all `1`, since `a`, `b` and `g` each divide `d` or
`d'`.

No hypothesis on `σ` is needed. -/
theorem pairTotientMajorant_le_tripleTotientMajorant (σ : ℝ) (p : ℕ × ℕ) :
    pairTotientMajorant σ p ≤ tripleTotientMajorant σ (gcdSplit p) := by
  obtain ⟨d, d'⟩ := p
  by_cases h0 : μ d = 0 ∨ μ d' = 0
  · have : pairTotientMajorant σ (d, d') = 0 := by
      rcases h0 with h | h <;> simp [pairTotientMajorant, h]
    exact this ▸ tripleTotientMajorant_nonneg σ _
  push Not at h0
  have hsd : Squarefree d := ArithmeticFunction.moebius_ne_zero_iff_squarefree.1 h0.1
  have hsd' : Squarefree d' := ArithmeticFunction.moebius_ne_zero_iff_squarefree.1 h0.2
  set g := d.gcd d' with hgg
  obtain ⟨a, hda⟩ : g ∣ d := Nat.gcd_dvd_left d d'
  obtain ⟨b, hdb⟩ : g ∣ d' := Nat.gcd_dvd_right d d'
  -- `a`, `b` and `g` divide a squarefree number, hence are squarefree
  have hsa : Squarefree a := hsd.squarefree_of_dvd (Dvd.intro_left _ hda.symm)
  have hsb : Squarefree b := hsd'.squarefree_of_dvd (Dvd.intro_left _ hdb.symm)
  have hsg : Squarefree g := hsd.squarefree_of_dvd (Dvd.intro _ hda.symm)
  have ha := Nat.pos_of_ne_zero hsa.ne_zero
  have hb := Nat.pos_of_ne_zero hsb.ne_zero
  have hg := Nat.pos_of_ne_zero hsg.ne_zero
  have hga : d / g = a := by rw [hda, Nat.mul_div_cancel_left _ hg]
  have hgb : d' / g = b := by rw [hdb, Nat.mul_div_cancel_left _ hg]
  have hlcm : Nat.lcm d d' = a * b * g := lcm_eq_div_gcd_mul hg hgg.symm hda hdb
  have habs : ∀ {n : ℕ}, Squarefree n → |(μ n : ℝ)| = 1 := fun h ↦ by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree h
  have h2 : (g : ℝ) ^ (2 * σ) = (g : ℝ) ^ σ * (g : ℝ) ^ σ := by
    rw [two_mul, Real.rpow_add (by exact_mod_cast hg)]
  have hcd : (d : ℝ) ^ σ = (g : ℝ) ^ σ * (a : ℝ) ^ σ := by
    rw [hda, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  have hcd' : (d' : ℝ) ^ σ = (g : ℝ) ^ σ * (b : ℝ) ^ σ := by
    rw [hdb, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  simp only [pairTotientMajorant, tripleTotientMajorant, totientKernelTerm, gcdSplit, ← hgg,
    hga, hgb, hlcm, hcd, hcd', h2, habs hsd, habs hsd', habs hsa, habs hsb, habs hsg,
    one_mul]
  calc _ ≤ 1 / (((a.totient * b.totient * g.totient : ℕ) : ℝ) * ((g : ℝ) ^ σ * (a : ℝ) ^ σ) *
        ((g : ℝ) ^ σ * (b : ℝ) ^ σ)) := by
        gcongr
        exact totient_mul_totient_mul_totient_le a b g
    _ = _ := by push_cast; field_simp

/-! ## Summability and the bound -/

/-- `Gap212.Sieve.tripleTotientMajorant` is summable over `ℕ³` for `σ > 0`, being a product of
three convergent copies of `T`. -/
theorem summable_tripleTotientMajorant {σ : ℝ} (hσ : 0 < σ) :
    Summable (tripleTotientMajorant σ) :=
  (summable_totientKernelTerm hσ).mul_of_nonneg
    ((summable_totientKernelTerm hσ).mul_of_nonneg (summable_totientKernelTerm (by linarith))
      (totientKernelTerm_nonneg σ) (totientKernelTerm_nonneg (2 * σ)))
    (totientKernelTerm_nonneg σ)
    (fun q ↦ mul_nonneg (totientKernelTerm_nonneg _ _) (totientKernelTerm_nonneg _ _))

/-- **`∑_{a,b,g} T-term(a)·T-term(b)·T-term₂(g) = T(σ)²T(2σ)`**, by two applications of the product
formula for absolutely convergent double series. -/
theorem tsum_tripleTotientMajorant {σ : ℝ} (hσ : 0 < σ) :
    ∑' q, tripleTotientMajorant σ q
      = totientKernelSeries σ * (totientKernelSeries σ * totientKernelSeries (2 * σ)) := by
  simp only [totientKernelSeries, tripleTotientMajorant]
  rw [tsum_mul_tsum_of_summable_norm (summable_norm_totientKernelTerm hσ)
      (summable_norm_totientKernelTerm (by linarith)),
    tsum_mul_tsum_of_summable_norm (summable_norm_totientKernelTerm hσ)
      (summable_norm_pairTotientKernelTerm hσ (by linarith))]

/-- **The double sum converges absolutely**, for every `σ > 0`: the comparison
`Gap212.Sieve.pairTotientMajorant_le_tripleTotientMajorant` transported along the injection
`Gap212.Sieve.gcdSplit`. This is the arithmetic hypothesis Fubini needs on the totient side. -/
theorem summable_pairTotientMajorant {σ : ℝ} (hσ : 0 < σ) : Summable (pairTotientMajorant σ) :=
  Summable.of_nonneg_of_le (pairTotientMajorant_nonneg σ)
    (pairTotientMajorant_le_tripleTotientMajorant σ)
    ((summable_tripleTotientMajorant hσ).comp_injective gcdSplit_injective)

/-- **The sharp form of the totient kernel's Fubini bound.** For every `σ > 0`,

  `∑_{d,d'} |μ(d)μ(d')| / (φ([d,d']) d^σ (d')^σ) ≤ T(σ)² · T(2σ)`.

Only `|μ| ≤ 1` and `φ(a)φ(b)φ(g) ≤ φ(abg)` are lost, so this has the right order in `σ`, namely
`σ^{-3}`, matching the reciprocal kernel's `Z(1+σ)³`. -/
theorem tsum_pairTotientMajorant_le_mul {σ : ℝ} (hσ : 0 < σ) :
    ∑' p, pairTotientMajorant σ p
      ≤ totientKernelSeries σ * (totientKernelSeries σ * totientKernelSeries (2 * σ)) := by
  calc ∑' p, pairTotientMajorant σ p
      ≤ ∑' p, tripleTotientMajorant σ (gcdSplit p) :=
        Summable.tsum_le_tsum (pairTotientMajorant_le_tripleTotientMajorant σ)
          (summable_pairTotientMajorant hσ)
          ((summable_tripleTotientMajorant hσ).comp_injective gcdSplit_injective)
    _ ≤ ∑' q, tripleTotientMajorant σ q :=
        tsum_comp_le_tsum_of_inj (summable_tripleTotientMajorant hσ)
          (tripleTotientMajorant_nonneg σ) gcdSplit_injective
    _ = _ := tsum_tripleTotientMajorant hσ

/-- **The totient kernel's Fubini bound in terms of `Z`**: for every `σ > 0`,

  `∑_{d,d'} |μ(d)μ(d')| / (φ([d,d']) d^σ (d')^σ) ≤ Z(1+σ)⁶`.

The exponent is `6`, not the reciprocal kernel's `3`: each of the three `T`-factors is bounded by
`Z²` through `n ≤ τ₂(n)φ(n)`. At `σ = 1/log x` this reads `≪ log⁶x` where the source has `log³x`,
so the *rate* comes from `Gap212.Sieve.tsum_pairTotientMajorant_le_mul` with a sharper bound on
`T`, which is `Gap212.Sieve.tsum_pairTotientMajorant_le_sharp`; for the interchange, which consumes
finiteness, this suffices. -/
theorem tsum_pairTotientMajorant_le {σ : ℝ} (hσ : 0 < σ) :
    ∑' p, pairTotientMajorant σ p ≤ zetaSeries (1 + σ) ^ 6 := by
  refine (tsum_pairTotientMajorant_le_mul hσ).trans ?_
  have hT := totientKernelSeries_le hσ
  have hT2 : totientKernelSeries (2 * σ) ≤ zetaSeries (1 + σ) ^ 2 :=
    (totientKernelSeries_le (by linarith)).trans (pow_le_pow_left₀
      (tsum_nonneg fun n ↦ natRpow_neg_nonneg _ n) (zetaSeries_antitone (by linarith)
        (by linarith)) 2)
  have := totientKernelSeries_nonneg σ
  have := totientKernelSeries_nonneg (2 * σ)
  calc _ ≤ zetaSeries (1 + σ) ^ 2 * (zetaSeries (1 + σ) ^ 2 * zetaSeries (1 + σ) ^ 2) := by
        gcongr
    _ = _ := by ring

end Gap212.Sieve
