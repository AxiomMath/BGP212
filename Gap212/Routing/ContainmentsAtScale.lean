/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.Routes
public import Gap212.Equidistribution.Defs.FiveEstimates
public import Gap212.Parameters.Challenge
public meta import Gap212.Attr

/-!
# The five route containments, stated at the scale

`Gap212.Routing.TypeIIaRoute` and `Gap212.Routing.Routes` close four of the routes into
the `γ`-shaped families `Gap212.moduliIFamily`, `moduliIIaFamily`, `moduliIIbFamily` and
`moduliIIIFamily`, whose windows are displayed as powers of `x` alone. The five equidistribution
estimates read their moduli instead from `Gap212.moduliI`, `moduliIIa`, `moduliIIb` and
`moduliIII`, whose windows are placed relative to the real scale `N` of the convolution's second
factor. This module states each route at those families, which is the shape the estimates
consume.

## The two shapes are the same family at `N = x^γ`

A window `(N x^{-δ-3ε}, N x^{-3ε})` and a window `(x^{γ-δ-3ε}, x^{γ-3ε})` are the same window as
soon as `N = x^γ`, by `Real.rpow_add`; and for `1 < x` and `0 < N` that is exactly
`Gap212.logScale x N = γ`. The one branch point that has to move with it is `Gap212.moduliI`'s
trichotomy, stated in the scale as `N ≤ √x` and `N ≤ x^{1/2+2ω+ε}` where the `γ`-shaped family
states it as `γ ≤ 1/2` and `γ ≤ 1/2+2ω+ε`; `Real.rpow_le_rpow_left_iff` moves it. The remaining
difference is bookkeeping: the `γ`-shaped families cut by `Gap212.HasDivisorIn`'s
`∃ r ∈ d.divisors`, the scale-shaped ones by `r ∣ d`, and on the ambient range `Gap212.moduliRange`
every modulus is at least `1`, so the two agree. `Gap212.moduliIII`, whose window holds neither a
scale nor the analytic loss, agrees with `moduliIIIFamily` outright.

So each containment below is the corresponding `γ`-shaped route transported along one of the four
equalities of families, with no mathematics added.

## Main results

* `Gap212.Routing.moduliIFamily_eq_moduliI`, `moduliIIaFamily_eq_moduliIIa`,
  `moduliIIbFamily_eq_moduliIIb`, `moduliIIIFamily_eq_moduliIII`: the four equalities of families.
* `Gap212.Routing.mem_moduliI_route_le_half_atScale`, `mem_moduliI_route_gt_half_atScale`: Type I,
  both `γ`-regimes.
* `Gap212.Routing.mem_moduliIIa_route_atScale`, `mem_moduliIIb_route_atScale`: Types IIa and IIb.
* `Gap212.Routing.mem_moduliIII_route_atScale`: Type III, which reads no scale.
-/

@[expose] public section

namespace Gap212.Routing

open Gap212.PointA Gap212.Packing Gap212.Extraction

/-! ## The ambient range has no zero -/

/-- A modulus of the ambient range is nonzero: `Gap212.moduliRange` starts at `1`. This is what
makes `Gap212.HasDivisorIn`'s `r ∈ d.divisors` and the plain `r ∣ d` of the scale-shaped families
the same condition there. -/
theorem ne_zero_of_mem_moduliRange {x ω : ℝ} {d : ℕ} (hd : d ∈ moduliRange x ω) : d ≠ 0 := by
  rw [moduliRange, Finset.mem_Icc] at hd
  omega

/-- For a nonzero `d`, having a divisor in the open interval `(x^a, x^b)` is the same whether the
divisor is drawn from `d.divisors` or merely asked to divide `d`. -/
theorem hasDivisorIn_iff_exists_dvd {x a b : ℝ} {d : ℕ} (hd : d ≠ 0) :
    HasDivisorIn d x a b ↔ ∃ r : ℕ, r ∣ d ∧ x ^ a < (r : ℝ) ∧ (r : ℝ) < x ^ b := by
  constructor
  · rintro ⟨r, hr, h₁, h₂⟩
    exact ⟨r, (Nat.mem_divisors.1 hr).1, h₁, h₂⟩
  · rintro ⟨r, hr, h₁, h₂⟩
    exact ⟨r, Nat.mem_divisors.2 ⟨hr, hd⟩, h₁, h₂⟩

/-- The ambient range cut by one window, in the two spellings of "carries a divisor in it": the
`γ`-shaped families ask `Gap212.HasDivisorIn`, the scale-shaped ones ask `r ∣ d`. Both branches of
`Gap212.moduliI` that carry a window are an instance of this. -/
theorem filter_hasDivisorIn_eq_filter_dvd {x ω a b : ℝ}
    [DecidablePred fun d : ℕ => HasDivisorIn d x a b]
    [DecidablePred fun d : ℕ => ∃ r : ℕ, r ∣ d ∧ x ^ a < (r : ℝ) ∧ (r : ℝ) < x ^ b] :
    {d ∈ moduliRange x ω | HasDivisorIn d x a b}
      = {d ∈ moduliRange x ω | ∃ r : ℕ, r ∣ d ∧ x ^ a < (r : ℝ) ∧ (r : ℝ) < x ^ b} := by
  ext d
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := Finset.mem_filter.1 h
    exact Finset.mem_filter.2
      ⟨h'.1, (hasDivisorIn_iff_exists_dvd (ne_zero_of_mem_moduliRange h'.1)).1 h'.2⟩
  · have h' := Finset.mem_filter.1 h
    exact Finset.mem_filter.2
      ⟨h'.1, (hasDivisorIn_iff_exists_dvd (ne_zero_of_mem_moduliRange h'.1)).2 h'.2⟩

/-! ## The four equalities of families -/

open Classical in
/-- **`D_IIa` in the two shapes.** `Gap212.moduliIIaFamily x ω γ δ ε` is `Gap212.moduliIIa` at the
scale `N = x^γ`: the window `(x^{γ-3ε-δ}, x^{γ-3ε})` is `(N x^{-δ-3ε}, N x^{-3ε})`. -/
theorem moduliIIaFamily_eq_moduliIIa {x : ℝ} (hx : 0 < x) (ω γ δ ε : ℝ) :
    moduliIIaFamily x ω γ δ ε = moduliIIa x ω (x ^ γ) δ ε := by
  have e₁ : x ^ γ * x ^ (-δ - 3 * ε) = x ^ (γ - 3 * ε - δ) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have e₂ : x ^ γ * x ^ (-3 * ε) = x ^ (γ - 3 * ε) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  rw [moduliIIa, e₁, e₂, moduliIIaFamily]
  exact filter_hasDivisorIn_eq_filter_dvd

open Classical in
/-- **`D_I` in the two shapes.** Both the trichotomy and the two windows move: `γ ≤ 1/2` is
`x^γ ≤ √x` and `γ ≤ 1/2+2ω+ε` is `x^γ ≤ x^{1/2+2ω+ε}` for `1 < x`, the first window is the one of
`moduliIIaFamily_eq_moduliIIa`, and the second, `(x^{1-γ-δ-3ε}, x^{1-γ-3ε})`, is
`(N⁻¹ x^{1-δ-3ε}, N⁻¹ x^{1-3ε})` since `N⁻¹ = x^{-γ}`. The third branch carries no window. -/
theorem moduliIFamily_eq_moduliI {x : ℝ} (hx : 1 < x) (ω γ δ ε : ℝ) :
    moduliIFamily x ω γ δ ε = moduliI x ω (x ^ γ) δ ε := by
  have hx0 : (0 : ℝ) < x := by linarith
  have e₁ : x ^ γ * x ^ (-δ - 3 * ε) = x ^ (γ - δ - 3 * ε) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have e₂ : x ^ γ * x ^ (-3 * ε) = x ^ (γ - 3 * ε) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have e₃ : (x ^ γ)⁻¹ * x ^ (1 - δ - 3 * ε) = x ^ (1 - γ - δ - 3 * ε) := by
    rw [← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]; congr 1; ring
  have e₄ : (x ^ γ)⁻¹ * x ^ (1 - 3 * ε) = x ^ (1 - γ - 3 * ε) := by
    rw [← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]; congr 1; ring
  rw [moduliIFamily, moduliI]
  by_cases h₁ : γ ≤ 1 / 2
  · have h₁' : x ^ γ ≤ Real.sqrt x := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx.le h₁
    rw [if_pos h₁, if_pos h₁', e₁, e₂]
    exact filter_hasDivisorIn_eq_filter_dvd
  · have h₁' : ¬ x ^ γ ≤ Real.sqrt x := by
      rw [Real.sqrt_eq_rpow]
      exact fun h => h₁ ((Real.rpow_le_rpow_left_iff hx).1 h)
    rw [if_neg h₁, if_neg h₁']
    by_cases h₂ : γ ≤ 1 / 2 + 2 * ω + ε
    · have h₂' : x ^ γ ≤ x ^ (1 / 2 + 2 * ω + ε) :=
        Real.rpow_le_rpow_of_exponent_le hx.le h₂
      rw [if_pos h₂, if_pos h₂', e₃, e₄]
      exact filter_hasDivisorIn_eq_filter_dvd
    · have h₂' : ¬ x ^ γ ≤ x ^ (1 / 2 + 2 * ω + ε) :=
        fun h => h₂ ((Real.rpow_le_rpow_left_iff hx).1 h)
      rw [if_neg h₂, if_neg h₂']

open Classical in
/-- **`D_IIb` in the two shapes.** The outer window is `moduliIIaFamily_eq_moduliIIa`'s; the inner
one, on a divisor of `d / r`, is `(x^{1/2-γ-2ω-6ε-δ}, x^{1/2-γ-2ω-6ε})` against
`(N⁻¹ x^{1/2-2ω-6ε-δ}, N⁻¹ x^{1/2-2ω-6ε})`. Here both divisor conditions change spelling, and the
inner one needs `d / r ≠ 0`, which `r ∣ d` and `1 ≤ d` supply. -/
theorem moduliIIbFamily_eq_moduliIIb {x : ℝ} (hx : 0 < x) (ω γ δ ε : ℝ) :
    moduliIIbFamily x ω γ δ ε = moduliIIb x ω (x ^ γ) δ ε := by
  have e₁ : x ^ γ * x ^ (-3 * ε - δ) = x ^ (γ - 3 * ε - δ) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have e₂ : x ^ γ * x ^ (-3 * ε) = x ^ (γ - 3 * ε) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have e₃ : (x ^ γ)⁻¹ * x ^ (1 / 2 - 2 * ω - 6 * ε - δ)
      = x ^ (1 / 2 - γ - 2 * ω - 6 * ε - δ) := by
    rw [← Real.rpow_neg hx.le, ← Real.rpow_add hx]; congr 1; ring
  have e₄ : (x ^ γ)⁻¹ * x ^ (1 / 2 - 2 * ω - 6 * ε) = x ^ (1 / 2 - γ - 2 * ω - 6 * ε) := by
    rw [← Real.rpow_neg hx.le, ← Real.rpow_add hx]; congr 1; ring
  rw [moduliIIb, e₁, e₂, e₃, e₄, moduliIIbFamily]
  ext d
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := Finset.mem_filter.1 h
    obtain ⟨r, hr, hr₁, hr₂, u, hu, hu₁, hu₂⟩ := h'.2
    exact Finset.mem_filter.2 ⟨h'.1, r, u, (Nat.mem_divisors.1 hr).1,
      (Nat.mem_divisors.1 hu).1, hr₁, hr₂, hu₁, hu₂⟩
  · have h' := Finset.mem_filter.1 h
    have hd0 : d ≠ 0 := ne_zero_of_mem_moduliRange h'.1
    obtain ⟨r, u, hrd, hud, hr₁, hr₂, hu₁, hu₂⟩ := h'.2
    have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; exact hd0 (zero_dvd_iff.1 hrd))
    have hdr0 : d / r ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hrd) hr0).ne'
    exact Finset.mem_filter.2 ⟨h'.1, r, Nat.mem_divisors.2 ⟨hrd, hd0⟩, hr₁, hr₂, u,
      Nat.mem_divisors.2 ⟨hud, hdr0⟩, hu₁, hu₂⟩

open Classical in
/-- **`D_III` in the two shapes.** Its window is placed absolutely — no scale, no analytic loss —
so the `γ`-shaped family's two extra arguments are read by neither side.

The two differ only in how divisibility is written. The family cuts by `Gap212.HasDivisorIn`, whose
body is `∃ r ∈ d.divisors`, and `Gap212.moduliIII` by `∃ r, r ∣ d`, as `Gap212Challenge/Basic.lean`
spells it. `Nat.mem_divisors` is `r ∣ d ∧ d ≠ 0`, so the two agree exactly where `d ≠ 0`, which the
ambient range supplies: `moduliRange` starts at `1`. -/
theorem moduliIIIFamily_eq_moduliIII (x ω γ δ ε : ℝ) :
    moduliIIIFamily x ω γ δ ε = moduliIII x ω δ := by
  refine Finset.filter_congr fun d hd ↦ ?_
  have hd0 : d ≠ 0 := ne_zero_of_mem_moduliRange hd
  simp only [HasDivisorIn]
  constructor
  · rintro ⟨r, hr, hr₁, hr₂⟩
    exact ⟨r, (Nat.mem_divisors.1 hr).1, hr₁, hr₂⟩
  · rintro ⟨r, hrd, hr₁, hr₂⟩
    exact ⟨r, Nat.mem_divisors.2 ⟨hrd, hd0⟩, hr₁, hr₂⟩

/-! ## Type I at Point A, both regimes -/

/-- **The Type I route, low range, at the scale.** For a scale `N` with `log_x N = γ` in
`[ξ₁ - ϵ, 1/2]` and a retreat `ε' ≤ ϵ`, every generated modulus above `x^{1/2-ε₁}` lies in
`D_I(x, ω, N, δ*_{I,low}(γ), ε')`. The threshold is `ε₁ = ε₀(1/2 - a)` with `a` the window's lower
end, so it depends only on `ε₀` and the datum; `N ≤ √x` is the branch `γ ≤ 1/2` picks out.

This is `mem_moduliI_route_le_half` at `N = x^γ`. -/
theorem mem_moduliI_route_le_half_atScale {x ε₀ γ ε' N : ℝ}
    {j j' : Fin gap212ParamsPointA.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hN : 0 < N) (hγN : logScale x N = γ)
    (hγlo : gammaLoI ≤ γ) (hγhi : γ ≤ 1 / 2)
    (hε'0 : 0 ≤ ε') (hε' : ε' ≤ ((ϵ : ℚ) : ℝ))
    (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hq : q ∈ Qgen gap212ParamsPointA x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ * (1 / 2 - (γ - 3 * ε' - widthI₁
      + (widthI₁ - gap212ParamsPointA.δ) / 2))) ≤ (q : ℝ)) :
    q ∈ moduliI x (((ω : ℚ) : ℝ)) N widthI₁ ε' := by
  have hNx : N = x ^ γ := by rw [← hγN, rpow_logScale hx hN]
  rw [hNx, ← moduliIFamily_eq_moduliI hx]
  exact mem_moduliI_route_le_half hx hε₀ hε₀1 hγlo hγhi hε'0 hε' hm hm' hq hqbig

/-- **The Type I route, high range, at the scale.** For a scale `N` in `(√x, x^{1/2+2ω+ε'}]` — the
second branch of `D_I` — and a retreat `ε' ≤ ϵ`, every generated modulus above `x^{1/2-ε₁}` lies in
`D_I(x, ω, N, δ*_{I,high}, ε')`. The width is independent of `γ = log_x N`, but the window is not:
it sits near `x^{1-γ}`, which is what `N⁻¹` in the branch's endpoints says.

This is `mem_moduliI_route_gt_half` at `N = x^γ`, the two bounds on `N` read back as bounds on
`γ`. -/
theorem mem_moduliI_route_gt_half_atScale {x ε₀ γ ε' N : ℝ}
    {j j' : Fin gap212ParamsPointA.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hN : 0 < N) (hγN : logScale x N = γ)
    (hNlo : Real.sqrt x < N)
    (hNhi : N ≤ x ^ (1 / 2 + 2 * (((ω : ℚ) : ℝ)) + ε'))
    (hε'0 : 0 ≤ ε') (hε' : ε' ≤ ((ϵ : ℚ) : ℝ))
    (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hq : q ∈ Qgen gap212ParamsPointA x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ * (1 / 2 - (1 - γ - 3 * ε' - widthI₂
      + (widthI₂ - gap212ParamsPointA.δ) / 2))) ≤ (q : ℝ)) :
    q ∈ moduliI x (((ω : ℚ) : ℝ)) N widthI₂ ε' := by
  have hNx : N = x ^ γ := by rw [← hγN, rpow_logScale hx hN]
  have hγlo : ¬ γ ≤ 1 / 2 := by
    have h : x ^ (1 / 2 : ℝ) < x ^ γ := by rw [← Real.sqrt_eq_rpow, ← hNx]; exact hNlo
    exact not_le.2 ((Real.rpow_lt_rpow_left_iff hx).1 h)
  have hγhi : γ ≤ 1 / 2 + 2 * (((ω : ℚ) : ℝ)) + ε' :=
    (Real.rpow_le_rpow_left_iff hx).1 (by rw [← hNx]; exact hNhi)
  rw [hNx, ← moduliIFamily_eq_moduliI hx]
  exact mem_moduliI_route_gt_half hx hε₀ hε₀1 hγlo hγhi hε'0 hε' hm hm' hq hqbig

/-! ## Types IIa and IIb at Point A -/

/-- **The Type IIa route, at the scale.** For a scale `N` with
`log_x N = γ ∈ [2/5 + 24ω/5 + 7δ/5 + 2ϵ, 1/2]` and a retreat `ε' ≤ ϵ`, every generated modulus
above `x^{1/2-ε₁}` lies in `D_IIa(x, ω, N, δ*_IIa(γ), ε')` — at the route's fixed width
`widthIIa`, the value of `δ*_IIa` at the bottom of the range.

This is `mem_moduliIIa_route` at `N = x^γ`. -/
theorem mem_moduliIIa_route_atScale {x ε₀ γ ε' N : ℝ}
    {j j' : Fin gap212ParamsPointA.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hN : 0 < N) (hγN : logScale x N = γ)
    (hγlo : gammaLoIIa ≤ γ) (hγhi : γ ≤ 1 / 2)
    (hε'0 : 0 ≤ ε') (hε' : ε' ≤ ((ϵ : ℚ) : ℝ))
    (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hq : q ∈ Qgen gap212ParamsPointA x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ * (1 / 2 - (γ - 3 * ε' - widthIIa
      + (widthIIa - gap212ParamsPointA.δ) / 2))) ≤ (q : ℝ)) :
    q ∈ moduliIIa x (((ω : ℚ) : ℝ)) N widthIIa ε' := by
  have hNx : N = x ^ γ := by rw [← hγN, rpow_logScale hx hN]
  rw [hNx, ← moduliIIaFamily_eq_moduliIIa (by linarith : (0 : ℝ) < x)]
  exact mem_moduliIIa_route hx hε₀ hε₀1 hγlo hγhi hε'0 hε' hm hm' hq hqbig

/-- **The Type IIb route, at the scale.** For a scale `N` with `log_x N = γ` between the IIb and
IIa thresholds and a retreat `ε' ≤ ϵ`, every generated modulus above `x^{1/2-ε₁}` lies in
`D_IIb(x, ω, N, δ*_IIb(γ), ε')`, at the route's fixed width `widthIIb`. Two nested divisors are
asked for, and the threshold `ε₁` is read off the sum of the two windows' lower ends.

This is `mem_moduliIIb_route` at `N = x^γ`. -/
theorem mem_moduliIIb_route_atScale {x ε₀ γ ε' N : ℝ}
    {j j' : Fin gap212ParamsPointA.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hN : 0 < N) (hγN : logScale x N = γ)
    (hγlo : gammaLoIIb ≤ γ) (hγhi : γ ≤ gammaLoIIa)
    (hε'0 : 0 ≤ ε') (hε' : ε' ≤ ((ϵ : ℚ) : ℝ))
    (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hq : q ∈ Qgen gap212ParamsPointA x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ * (1 / 2
      - (γ - 3 * ε' - widthIIb + (widthIIb - gap212ParamsPointA.δ) / 2 + gap212ParamsPointA.δ)
      - (1 / 2 - γ - 2 * (((ω : ℚ) : ℝ)) - 6 * ε' - widthIIb
          + (widthIIb - gap212ParamsPointA.δ) / 2))) ≤ (q : ℝ)) :
    q ∈ moduliIIb x (((ω : ℚ) : ℝ)) N widthIIb ε' := by
  have hNx : N = x ^ γ := by rw [← hγN, rpow_logScale hx hN]
  rw [hNx, ← moduliIIbFamily_eq_moduliIIb (by linarith : (0 : ℝ) < x)]
  exact mem_moduliIIb_route hx hε₀ hε₀1 hγlo hγhi hε'0 hε' hm hm' hq hqbig

/-! ## Type III at Point A -/

/-- **The Type III route, at `D_III`.** Every generated modulus above `x^{1/2-ε₁}` lies in
`D_III(x, ω, δ*_III)`. There is no scale and no retreat to supply: the window is
`(x^{1/3+4δ*/3-4ω/3-δ*}, x^{1/3+4δ*/3-4ω/3})`, placed by the width and the level alone, and the
two window conditions the route assumes are the numeric facts `widthIII_gt_δ` and the
capacities `0.3563` and `0.1616` discharged inside `mem_moduliIII_route`.

This is `mem_moduliIII_route` with the `γ`-shaped family's two unread arguments erased. -/
theorem mem_moduliIII_route_atScale {x ε₀ : ℝ}
    {j j' : Fin gap212ParamsPointA.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hq : q ∈ Qgen gap212ParamsPointA x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ * (1 / 2 - (1 / 3 + 4 * widthIII / 3
      - 4 * (((ω : ℚ) : ℝ)) / 3 - widthIII + (widthIII - gap212ParamsPointA.δ) / 2)))
      ≤ (q : ℝ)) :
    q ∈ moduliIII x (((ω : ℚ) : ℝ)) widthIII := by
  rw [← moduliIIIFamily_eq_moduliIII x (((ω : ℚ) : ℝ)) 0 widthIII 0]
  exact mem_moduliIII_route hx hε₀ hε₀1 hm hm' hq hqbig

end Gap212.Routing
