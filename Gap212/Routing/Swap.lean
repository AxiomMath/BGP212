/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.Patch
public meta import Gap212.Attr

/-!
# The `γ ↔ 1 - γ` swap, and why the scale can be replaced by an exact power

The source reduces Type II to `γ ≤ 1/2` in one sentence: "Interchanging the two convolution factors
replaces `γ` by `1-γ`, so it is enough to treat `γ ≤ 1/2`." Two things make that a step.

## The convolution is commutative

`Gap212.Routing.dconv_comm`, by the divisor involution `d ↦ n/d` — the two forms of
`Nat.sum_divisorsAntidiagonal`. This is where Type II's Siegel-Walfisz on **both** factors is
spent: after the swap the second factor is `α`, and the estimates require Siegel–Walfisz of
whichever sequence sits second. [2, Lemmas 3, 4 and 6] ask it of `β` only, so a class carrying it
on one side could not be swapped — which is exactly why `Harman.TypeIIFamily` asks for both.

## But the swapped scale is not an exact power

Here the one-sentence argument needs care. `Harman.TypeIIFamily` gives `N x =
x^{γ(x)}` **exactly**, while
the swapped scale is `M`, pinned only by `M N ≍ x` — so `M x ≍ x^{1-γ(x)}`, *not* equal to it. The
estimates' exponent condition demands an exact power, so `M` must be replaced by `x^{1-γ(x)}`, and
that replacement shown harmless.

It is, because both surviving hypotheses about a scale are invariant under `≍`:

* `Gap212.Routing.locatedAtScale_of_asympEq` — the support condition `c N x ≤ n ≤ C N x` absorbs
  the comparison constants into `c` and `C`;
* `Gap212.Routing.hasSiegelWalfisz_of_asympEq` — the scale appears as a factor on the right, so the
  comparison constant absorbs into the implied constant.

With these, the swap produces a genuine estimate input, and combining it with the localization of
`Gap212.Routing.Localize` and the patch of `Gap212.Routing.Patch` is what covers Type
II's whole `γ`-range.

## Main results

* `Gap212.Routing.dconv_comm`.
* `Gap212.Routing.locatedAtScale_of_asympEq`, `hasSiegelWalfisz_of_asympEq`.
-/

@[expose] public section

namespace Gap212.Routing

open Finset Real

/-- **Dirichlet convolution is commutative**, by the involution `d ↦ n/d` on divisors.

This is what the `γ ↔ 1-γ` reduction rests on, and it is why `Harman.TypeIIFamily`
requires Siegel–Walfisz
of *both* factors: after the swap the second factor is `α`, and the estimates ask it of whichever
sequence sits second. -/
theorem dconv_comm (α β : ℕ → ℝ → ℂ) : dconvFamily α β = dconvFamily β α := by
  funext n x
  rw [dconvFamily, dconvFamily, ← Nat.sum_divisorsAntidiagonal (fun a b ↦ α a x * β b x),
    ← Nat.sum_divisorsAntidiagonal' (fun a b ↦ β b x * α a x)]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- **`LocatedAtScaleFamily` only sees the scale up to `≍`.** The support condition is
`c N x ≤ n ≤ C N x`, so replacing `N` by a comparable `N'` just multiplies the two constants. -/
theorem locatedAtScale_of_asympEq {α : ℕ → ℝ → ℂ} {N N' : ℝ → ℝ}
    (h : LocatedAtScaleFamily α N) (hcmp : AsympEq N N') : LocatedAtScaleFamily α N' := by
  obtain ⟨c, C, hc, hcC, hbd⟩ := h
  obtain ⟨d, D, hd, hdD, hcmpbd⟩ := hcmp
  refine ⟨c * d, C * D, by positivity, mul_le_mul hcC hdD hd.le (hc.le.trans hcC),
    fun x hx n hne ↦ ?_⟩
  obtain ⟨hlo, hhi⟩ := hbd x hx n hne
  rw [mul_assoc, mul_assoc]
  exact ⟨(mul_le_mul_of_nonneg_left (hcmpbd x hx).1 hc.le).trans hlo,
    hhi.trans (mul_le_mul_of_nonneg_left (hcmpbd x hx).2 (hc.le.trans hcC))⟩

/-- **`HasSiegelWalfiszFamily` only sees the scale up to `≍`.** The scale appears as
a factor on the right
of the bound, so the comparison constant absorbs into the implied constant. -/
theorem hasSiegelWalfisz_of_asympEq {β : ℕ → ℝ → ℂ} {N N' : ℝ → ℝ}
    (h : HasSiegelWalfiszFamily β N) (hcmp : AsympEq N N') : HasSiegelWalfiszFamily β N' := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨d, D, hd, hdD, hcmpbd⟩ := hcmp
  refine ⟨k, fun A hA ↦ ?_⟩
  obtain ⟨c, hc, hbd⟩ := hk A hA
  have hD : (0 : ℝ) < D := lt_of_lt_of_le hd hdD
  refine ⟨c * D, by positivity, fun x hx q r hq hr a hcop ↦ ?_⟩
  refine (hbd x hx q r hq hr a hcop).trans ?_
  rw [div_le_div_iff_of_pos_right (Real.rpow_pos_of_pos (Real.log_pos hx) A)]
  calc c * ((q * r).divisors.card : ℝ) ^ k * N x
      ≤ c * ((q * r).divisors.card : ℝ) ^ k * (D * N' x) := by gcongr; exact (hcmpbd x hx).2
    _ = c * D * ((q * r).divisors.card : ℝ) ^ k * N' x := by ring

end Gap212.Routing
