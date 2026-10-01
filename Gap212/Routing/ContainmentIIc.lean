/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.ContainmentsAtScale
public import Gap212.Routing.TypeIIcRoute
public meta import Gap212.Attr

/-!
# The Type IIc containment at a scale

`Gap212.Routing.ContainmentsAtScale` bridges four of the five modulus families from the
`γ`-shaped form to the `N`-shaped one; this module does the fifth, Type IIc. It is needed: after
the Type II reflection `γ` ranges over `[ξ₂ - ϵ, 1/2]`, while the Type IIb chamber only opens at
`γ ≥ 1/3 + 8ω + 7δ/3 + 3ϵ ≈ 0.4276`, so the window `γ ∈ [0.4, 0.4276]` is covered by Type IIc
alone, and this transport is what lets the Type II equidistribution estimate be stated at a
single `x`.

## The three windows

`Gap212.moduliIIc` is cut by three nested divisor conditions rather than one, which is what makes
it the most expensive of the five: `r ∣ d` in a window around `N`, then `u ∣ d / r` in a window
around `x / (N d)`, then `d₁ ∣ r` in a window around `r² x² / (N d⁴)`. The `γ`-shaped
family writes the same
three windows with `x^γ` in place of `N`, so at `N = x^γ` the two agree — the content of
`moduliIIcFamily_eq_moduliIIc` — and the three identities needed are
`(x^γ)⁻¹ x^a = x^{a-γ}` at `a = 1 - 6ε - δ`, `1 - 6ε`, and the two `52ε` variants.

## Main results

* `Gap212.Routing.moduliIIcFamily_eq_moduliIIc`: the two shapes agree at `N = x^γ`.
* `Gap212.Routing.mem_moduliIIc_route_atScale`: the Type IIc route, concluding at the scale.
-/

@[expose] public section

namespace Gap212.Routing

open Finset Real Gap212.PointA Gap212.Packing Gap212.Extraction

open Classical in
/-- **`D_{IIc}` in the two shapes.** The `γ`-shaped family and the `N`-shaped set agree at
`N = x ^ γ`: each of the three windows differs only by the identity `(x^γ)⁻¹ x^a = x^{a-γ}`, and
the divisibility clauses differ only in writing `r ∈ d.divisors` against `r ∣ d`, which agree on
the ambient range where `d ≠ 0`. -/
theorem moduliIIcFamily_eq_moduliIIc {x : ℝ} (hx : 0 < x) (ω γ δ ε : ℝ) :
    moduliIIcFamily x ω γ δ ε = moduliIIc x ω (x ^ γ) δ ε := by
  have e₁ : x ^ γ * x ^ (-3 * ε - δ) = x ^ (γ - 3 * ε - δ) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have e₂ : x ^ γ * x ^ (-3 * ε) = x ^ (γ - 3 * ε) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have e₃ : (x ^ γ)⁻¹ * x ^ (1 - 6 * ε - δ) = x ^ (1 - γ - 6 * ε - δ) := by
    rw [← Real.rpow_neg hx.le, ← Real.rpow_add hx]; congr 1; ring
  have e₄ : (x ^ γ)⁻¹ * x ^ (1 - 6 * ε) = x ^ (1 - γ - 6 * ε) := by
    rw [← Real.rpow_neg hx.le, ← Real.rpow_add hx]; congr 1; ring
  -- The `d₁` window carries a factor `r ^ 2` to the left of `N⁻¹`, so its identity is stated with
  -- that factor abstracted; `mul_assoc` is what reassociates it onto the two powers.
  have e₅ : ∀ c : ℝ, c * (x ^ γ)⁻¹ * x ^ (2 - 52 * ε - δ) = c * x ^ (2 - γ - 52 * ε - δ) := by
    intro c
    rw [mul_assoc, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
    congr 2; ring
  have e₆ : ∀ c : ℝ, c * (x ^ γ)⁻¹ * x ^ (2 - 52 * ε) = c * x ^ (2 - γ - 52 * ε) := by
    intro c
    rw [mul_assoc, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
    congr 2; ring
  rw [moduliIIc, moduliIIcFamily]
  simp only [e₁, e₂, e₃, e₄, e₅, e₆]
  ext d
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := Finset.mem_filter.1 h
    obtain ⟨r, hr, hr₁, hr₂, ⟨u, hu, hu₁, hu₂⟩, d₁, hd₁, hd₁₁, hd₁₂⟩ := h'.2
    exact Finset.mem_filter.2 ⟨h'.1, r, u, d₁, (Nat.mem_divisors.1 hr).1,
      (Nat.mem_divisors.1 hu).1, (Nat.mem_divisors.1 hd₁).1,
      hr₁, hr₂, hu₁, hu₂, hd₁₁, hd₁₂⟩
  · have h' := Finset.mem_filter.1 h
    have hd0 : d ≠ 0 := ne_zero_of_mem_moduliRange h'.1
    obtain ⟨r, u, d₁, hrd, hud, hd₁r, hr₁, hr₂, hu₁, hu₂, hdd₁, hdd₂⟩ := h'.2
    have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; exact hd0 (zero_dvd_iff.1 hrd))
    have hdr0 : d / r ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hrd) hr0).ne'
    exact Finset.mem_filter.2 ⟨h'.1, r, Nat.mem_divisors.2 ⟨hrd, hd0⟩, hr₁, hr₂,
      ⟨u, Nat.mem_divisors.2 ⟨hud, hdr0⟩, hu₁, hu₂⟩,
      d₁, Nat.mem_divisors.2 ⟨hd₁r, hr0.ne'⟩, hdd₁, hdd₂⟩

/-- **The Type IIc route, at the scale.** `Gap212.Routing.mem_moduliIIc_route` with its conclusion
transported to the `N`-shaped modulus set, for any `N` whose exponent at `x` is `γ`.

The scale enters as `logScale x N = γ` ("every `N` with `log_x N = γ`"), and `Gap212.rpow_logScale`
turns that back into `N = x ^ γ`. -/
theorem mem_moduliIIc_route_atScale {x ε₀ γ ε' ω₀ t wb N : ℝ}
    {j j' : Fin gap212ParamsPointA.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hN : 0 < N) (hγN : logScale x N = γ)
    (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hγlo : (2 / 5 : ℝ) - ((ϵ : ℚ) : ℝ) ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * ((ω : ℚ) : ℝ) + 7 * ((δ : ℚ) : ℝ) / 3 + 3 * ((ϵ : ℚ) : ℝ))
    (hω₀0 : 0 ≤ ω₀) (hω₀ : ω₀ ≤ ((ω : ℚ) : ℝ)) (hωt : t = 1 / 2 + 2 * ω₀)
    (hε'0 : 0 ≤ ε') (hε' : ε' ≤ ((ϵ : ℚ) : ℝ) / 100)
    (hwb0 : 0 ≤ wb) (hwb : wb ≤ ((ϵ : ℚ) : ℝ) / 32)
    (hqlo : x ^ (t - wb) ≤ (q : ℝ)) (hqhi : (q : ℝ) ≤ x ^ t)
    (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hq : q ∈ Qgen gap212ParamsPointA x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 + 2 * ω₀ - ε₀ * (1 / 2 + 2 * ω₀
      - (γ - 3 * ε' - widthIIc + (widthIIc - gap212ParamsPointA.δ) / 2 + gap212ParamsPointA.δ)
      - (1 - γ - 6 * ε' - widthIIc - (t - wb)
          + (widthIIc - gap212ParamsPointA.δ - wb) / 2))) ≤ (q : ℝ)) :
    q ∈ moduliIIc x (((ω : ℚ) : ℝ)) N widthIIc ε' := by
  have hxN : N = x ^ γ := by rw [← hγN, rpow_logScale hx hN]
  have hbase := mem_moduliIIc_route hx hε₀ hε₀1 hγlo hγhi hω₀0 hω₀ hωt hε'0 hε' hwb0 hwb
    hqlo hqhi hm hm' hq hqbig
  rw [hxN, ← moduliIIcFamily_eq_moduliIIc (lt_trans zero_lt_one hx)]
  exact hbase

end Gap212.Routing
