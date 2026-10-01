/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41Majorant
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Step 4a of Polymath8b Lemma 4.1: the pole of `ζ` at `s = 1`, moved to the origin

Steps 1–3 of the proof of Polymath8b Lemma 4.1 expand the profiles
(`Gap212.Sieve.Polymath41Fourier`), license Fubini (`Gap212.Sieve.Polymath41Majorant`)
and compute the kernel's local factor (`Gap212.Sieve.Polymath41Kernel`). Step 4 then extracts
the asymptotic, and the mechanism is a single analytic fact: `ζ` has a simple pole of residue `1`
at `s = 1`, so with

  `s = (1 + iξ)/log x`

the factor `ζ(1 + s)` is `(1 + o(1))/s` as `log x → ∞`. Everything in the source's step 4 that is
not bookkeeping is this.

## Why the statements here are at the origin rather than at `1`

Mathlib's `riemannZeta_residue_one` is `(s - 1)·ζ(s) → 1` as `s → 1` within `{1}ᶜ`. Every consumer
in this proof meets the pole in the *shifted* variable, because the exponent it produces is
`1 + s` with `s = (1+iξ)/log x` small — never `s` near `1`. So the basic statement here is

  `Gap212.Sieve.tendsto_mul_riemannZeta_one_add_nhdsNE`: `s·ζ(1+s) → 1` as `s → 0` in `{0}ᶜ`,

together with the reciprocal `Gap212.Sieve.tendsto_inv_mul_riemannZeta_one_add_nhdsNE` (the kernel
carries `ζ` in a denominator as often as in a numerator), the `ε`-`δ` form
`Gap212.Sieve.exists_norm_mul_riemannZeta_one_add_sub_one_le` — which is what makes the estimate
*uniform* in `ξ`, since its bound depends on `s` only through `‖s‖` — and the specialisation to
`s = w/L` with `L → ∞` along the reals, `Gap212.Sieve.tendsto_mul_riemannZeta_one_add_div`, which
is the shape `L = log x` hands over. The `nhdsNE` suffix distinguishes these from
`Gap212.Sieve.tendsto_mul_riemannZeta_one_add` of `Gap212.Sieve.MoebiusReciprocalSeries`,
which is the same fact restricted to a real one-sided approach, `s ↓ 0` along `ℝ`; that one is a
corollary of this one, and the two files are independent.

## Reading step 2's majorant as `≪ log³x`

Step 2 bounds the Fubini majorant by `Z(1+σ)³` where `Z` is `Gap212.Sieve.zetaSeries`, the real
Dirichlet series, written without `riemannZeta` on purpose. The source's next sentence reads that
bound as `≪ log³x`, and *that* step needs the identification: `Z(σ) = ζ(σ)` for `σ > 1`
(`Gap212.Sieve.ofReal_zetaSeries_eq_riemannZeta`), whence `σ·Z(1+σ) → 1` as `σ ↓ 0`
(`Gap212.Sieve.tendsto_mul_zetaSeries_one_add`) and, at `σ = 1/L`,
`Z(1 + 1/L)/L → 1` (`Gap212.Sieve.tendsto_zetaSeries_one_add_inv_div`). So `Z(1+1/log x) ~ log x`
and the majorant is `~ log³x`, with no `≪` left implicit.

## The truncation and the `W`-product

The truncation of the `ξ`-integral to `|ξ| ≤ √(log x)` and the finite product over `p ∣ W` are
treated in `Gap212.Sieve.Polymath41PoleUniform` and `Gap212.Sieve.Polymath41PoleWProduct`, which
depend on nothing here beyond the `ε`-`δ` form.

## Main results

* `Gap212.Sieve.tendsto_mul_riemannZeta_one_add_nhdsNE`: `s·ζ(1+s) → 1` as `s → 0`, `s ≠ 0`.
* `Gap212.Sieve.tendsto_inv_mul_riemannZeta_one_add_nhdsNE`: the reciprocal of the same.
* `Gap212.Sieve.exists_norm_mul_riemannZeta_one_add_sub_one_le`: the `ε`-`δ` form, whose bound
  depends on `s` only through `‖s‖`.
* `Gap212.Sieve.tendsto_mul_riemannZeta_one_add_div`: the same at `s = w/L`, `L → ∞`.
* `Gap212.Sieve.ofReal_zetaSeries_eq_riemannZeta`: `Z(σ) = ζ(σ)` for `σ > 1`.
* `Gap212.Sieve.tendsto_zetaSeries_one_add_inv_div`: `Z(1 + 1/L)/L → 1`, so `Z(1+1/log x) ~ log x`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Topology

/-! ## The residue of `ζ` at `1`, in the shifted variable -/

/-- **The shift `s ↦ 1 + s` maps `𝓝[≠] 0` to `𝓝[≠] 1`.** The punctured neighbourhoods have to be
matched, not just the neighbourhoods: `riemannZeta_residue_one` is stated on `𝓝[≠] 1` because
`(s-1)·ζ(s)` is not even defined at `s = 1`. -/
theorem tendsto_one_add_nhdsWithin_ne :
    Tendsto (fun s : ℂ ↦ 1 + s) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun s : ℂ ↦ 1 + s) (𝓝 (0 : ℂ)) (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_id
    rw [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
    intro h
    exact hs (by simpa using h)

/-- **`ζ` has residue `1` at `1`, written at the origin**: `s·ζ(1+s) → 1` as `s → 0` through
`s ≠ 0`. This is `riemannZeta_residue_one` composed with `s ↦ 1 + s`, and it is the form every
consumer in Lemma 4.1 meets, because the exponent the sieve produces is `1 + (1+iξ)/log x`. -/
theorem tendsto_mul_riemannZeta_one_add_nhdsNE :
    Tendsto (fun s : ℂ ↦ s * riemannZeta (1 + s)) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
  refine (riemannZeta_residue_one.comp tendsto_one_add_nhdsWithin_ne).congr fun s ↦ ?_
  simp [Function.comp]

/-- **The reciprocal form**: `(s·ζ(1+s))⁻¹ → 1`. The kernel of Lemma 4.1 carries `ζ(1+s)` in a
denominator (through `∏_p (1 - p^{-1-s})`, which is `ζ(1+s)⁻¹` completed) as often as in a
numerator, and the limit is `1`, which is invertible, so no non-vanishing of `ζ` is needed. -/
theorem tendsto_inv_mul_riemannZeta_one_add_nhdsNE :
    Tendsto (fun s : ℂ ↦ (s * riemannZeta (1 + s))⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
  simpa using tendsto_mul_riemannZeta_one_add_nhdsNE.inv₀ one_ne_zero

/-- **The `ε`-`δ` form of `Gap212.Sieve.tendsto_mul_riemannZeta_one_add_nhdsNE`, and the reason step
4's estimate is uniform in `ξ`.** The hypothesis on `s` is `‖s‖ ≤ δ` — a bound on the *modulus*
only, so a single `δ` serves every direction of approach at once. Applied to `s = (1+2πiξ)/log x`,
whose modulus is at most `(1 + 2π|ξ|)/log x`, it gives an estimate depending on `ξ` through that
bound alone; see `Gap212.Sieve.Polymath41PoleUniform`. -/
theorem exists_norm_mul_riemannZeta_one_add_sub_one_le {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s : ℂ, s ≠ 0 → ‖s‖ ≤ δ → ‖s * riemannZeta (1 + s) - 1‖ ≤ ε := by
  have h := tendsto_mul_riemannZeta_one_add_nhdsNE
  rw [Metric.tendsto_nhdsWithin_nhds] at h
  obtain ⟨δ, hδ, hmain⟩ := h ε hε
  refine ⟨δ / 2, by positivity, fun s hs hsn ↦ ?_⟩
  have hmem : s ∈ ({(0 : ℂ)}ᶜ : Set ℂ) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
  have hd : dist s 0 < δ := by
    rw [dist_zero_right]
    linarith
  have := hmain hmem hd
  rw [dist_eq_norm] at this
  exact this.le

/-- **The pole at a reciprocal scale.** For any fixed `w ≠ 0`, `(w/L)·ζ(1 + w/L) → 1` as the real
`L → ∞`. With `w = 1 + 2πiξ` and `L = log x` this is the factor step 4 extracts; the `ξ`-dependence
is frozen into `w`, which is why the *uniform* statement needs the `ε`-`δ` form above rather than
this one. -/
theorem tendsto_div_atTop_nhdsWithin_ne {w : ℂ} (hw : w ≠ 0) :
    Tendsto (fun L : ℝ ↦ w / (L : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs]
    exact Tendsto.div_atTop tendsto_const_nhds tendsto_abs_atTop_atTop
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, div_eq_zero_iff, not_or]
    exact ⟨hw, by exact_mod_cast hL.ne'⟩

/-- `(w/L)·ζ(1 + w/L) → 1` as `L → ∞` along the reals, for fixed `w ≠ 0`. -/
theorem tendsto_mul_riemannZeta_one_add_div {w : ℂ} (hw : w ≠ 0) :
    Tendsto (fun L : ℝ ↦ (w / (L : ℂ)) * riemannZeta (1 + w / (L : ℂ))) atTop (𝓝 1) :=
  tendsto_mul_riemannZeta_one_add_nhdsNE.comp (tendsto_div_atTop_nhdsWithin_ne hw)

/-! ## Step 2's real Dirichlet series and `riemannZeta` -/

/-- **`Z(σ) = ζ(σ)` for real `σ > 1`.** `Gap212.Sieve.zetaSeries` is defined as `∑_{n} n^{-σ}` over
all of `ℕ`, the `n = 0` term vanishing; Mathlib's `zeta_eq_tsum_one_div_nat_cpow` is the same
series with a complex exponent and the same convention for `n = 0`. This identification is what
licenses reading step 2's `Z(1+σ)³` bound as the source's `≪ log³x`. -/
theorem ofReal_zetaSeries_eq_riemannZeta {σ : ℝ} (hσ : 1 < σ) :
    ((zetaSeries σ : ℝ) : ℂ) = riemannZeta (σ : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hσ), zetaSeries, Complex.ofReal_tsum]
  refine tsum_congr fun n ↦ ?_
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, Complex.ofReal_neg,
    Complex.cpow_neg, one_div]

/-- **The pole, on the real Dirichlet series**: `σ·Z(1+σ) → 1` as `σ ↓ 0`. Proved by transporting
`Gap212.Sieve.tendsto_mul_riemannZeta_one_add_nhdsNE` along
`Gap212.Sieve.ofReal_zetaSeries_eq_riemannZeta` and taking real parts, which is legitimate because
both sides are real. -/
theorem tendsto_mul_zetaSeries_one_add :
    Tendsto (fun σ : ℝ ↦ σ * zetaSeries (1 + σ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hcast : Tendsto (fun σ : ℝ ↦ ((σ : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun σ : ℝ ↦ ((σ : ℂ))) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.tendsto 0
      rw [Complex.ofReal_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      exact (Set.mem_Ioi.1 hσ).ne'
  have hcomp : Tendsto (fun σ : ℝ ↦ (σ : ℂ) * riemannZeta (1 + (σ : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    tendsto_mul_riemannZeta_one_add_nhdsNE.comp hcast
  have hre := (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomp
  rw [Complex.one_re] at hre
  refine hre.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have h1 : (1 : ℂ) + (σ : ℂ) = ((1 + σ : ℝ) : ℂ) := by push_cast; ring
  have h2 : (1 : ℝ) < 1 + σ := by have := Set.mem_Ioi.1 hσ; linarith
  simp only [Function.comp_apply, h1, ← ofReal_zetaSeries_eq_riemannZeta h2, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- **`Z(1 + 1/L) ~ L` as `L → ∞`**, stated as `Z(1 + 1/L)/L → 1`. At `L = log x` this is
`Z(1 + 1/log x) ~ log x`, so step 2's majorant `Z(1+1/log x)³` is `~ log³x` — the source's
`≪ log³x` with the constant named. -/
theorem tendsto_zetaSeries_one_add_inv_div :
    Tendsto (fun L : ℝ ↦ zetaSeries (1 + 1 / L) / L) atTop (𝓝 1) := by
  have hinv : Tendsto (fun L : ℝ ↦ 1 / L) atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa only [one_div] using tendsto_inv_atTop_zero (𝕜 := ℝ)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      exact Set.mem_Ioi.2 (by positivity)
  refine (tendsto_mul_zetaSeries_one_add.comp hinv).congr fun L ↦ ?_
  simp only [Function.comp_apply, div_eq_inv_mul, mul_one]

end Gap212.Sieve
