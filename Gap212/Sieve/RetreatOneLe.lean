/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.AveragingFacts

/-!
# A retreated profile family vanishes from `1` on, unless one of its factors is null

The Gram-sum limits `Gap212.Sieve.LcmGramSumLimitOfSupport` and
`Gap212.Sieve.TotientGramSumLimitOfSupport` assume that each profile vanishes on `[β,∞)`; without
that hypothesis both limits are false (`Gap212.Sieve.not_lcmGramSumLimit`,
`Gap212.Sieve.not_totientGramSumLimit`), since the Gram sums read the profiles only on
`[0,\log_xB]`.

This file derives that hypothesis at `β = 1` from the retreat condition. The content is one
inequality: a point of `Gap212.GPY.retreatRegion` has **every** coordinate below `1/2`, because its
coordinates are nonnegative, they sum to less than `(1-ε₀)(A_{j+1}+ε)`, and
`A_{j+1}+ε ≤ A_n+ε < 1/2` is forced by `Gap212.SupportParams.A_last`.

So if every factor of a retreated family is non-zero *somewhere* on `[0,∞)`, moving one coordinate
to `t ≥ 1` keeps the product non-zero and puts the point in the retreat region, contradicting that
inequality — hence every factor vanishes from `1` on. The alternative is that some factor vanishes
identically on `[0,∞)`, and then the term it belongs to contributes nothing to either side of the
asymptotic; `Gap212.Sieve.prod_integral_eq_zero_of_null_left` is the right-hand half of that, the
left-hand half being the vanishing of the divisor weight, which is stated where each weight is.

The `Gap212.GPY.IsReducedRetreat` form of the hypothesis reads the profiles on the vector extended
by `0` at the removed coordinate, which changes nothing: the extension is still nonnegative and its
coordinate sum is the same, so the second corollary is the first with one `Fin.insertNth` unfolded.

`Gap212.Sieve.forall_eq_zero_of_one_le_or_null` is the same statement for a family indexed by an
extra parameter.

## Main results

* `Gap212.Sieve.coord_lt_half_of_mem_retreatRegion`: every coordinate of a retreated point is below
  `1/2`.
* `Gap212.Sieve.exists_null_or_forall_eq_zero_of_one_le`: a retreated family either has a factor
  vanishing on all of `[0,∞)`, or every factor vanishes from `1` on.
* `Gap212.Sieve.exists_null_or_forall_eq_zero_of_one_le_insertNth`: the same for the reduced
  retreat, whose region is read at the extended vector.
* `Gap212.Sieve.prod_integral_eq_zero_of_null_left`, `..._right`: a null factor kills the product
  of Gram integrals, which is the limit in the Gram-sum asymptotics.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY MeasureTheory

/-! ## Every coordinate of a retreated point is below `1/2` -/

/-- **A retreated point has every coordinate below `1/2`.** Its coordinates are nonnegative, so
each is at most their sum, which is less than `(1-ε₀)(A_{j+1}+ε) ≤ A_{j+1}+ε ≤ A_n+ε < 1/2` — the
last step being `Gap212.SupportParams.A_last`, and the first needing `ε₀ ≥ 0` together with
`A_{j+1}+ε > 0`, which holds because `A` is strictly increasing from `A_0 = -ε`.

Consequently a profile family supported in the retreat region cannot see an argument as large as
`1`. -/
theorem coord_lt_half_of_mem_retreatRegion {p : SupportParams} {k : ℕ} {j : Fin p.n} {ε₀ : ℝ}
    (hε₀ : 0 ≤ ε₀) {t : Fin k → ℝ} (ht : t ∈ retreatRegion p k j ε₀) (i : Fin k) :
    t i < 1 / 2 := by
  obtain ⟨hcube, hsum, -⟩ := ht
  have hle : t i ≤ ∑ i', t i' :=
    Finset.single_le_sum (fun i' _ ↦ (hcube i').1) (Finset.mem_univ i)
  have hmono : p.A j.succ ≤ p.A (Fin.last p.n) := p.A_mono.monotone (Fin.le_last _)
  have hlast := p.A_last
  have hApos : 0 < p.A j.succ + p.ε := by
    have h0 : -p.ε < p.A j.succ := by rw [← p.A_zero]; exact p.A_mono (Fin.succ_pos j)
    linarith
  have hcap : (1 - ε₀) * (p.A j.succ + p.ε) ≤ p.A j.succ + p.ε := by nlinarith
  linarith

/-! ## Retreated families vanish from `1` on -/

/-- **A retreated family's factors vanish from `1` on, unless one of them is null.** For a family
whose product is supported in `Gap212.GPY.retreatRegion` on the nonnegative orthant, either some
factor vanishes on all of `[0,∞)` — and then every term it multiplies is zero on both sides of the
asymptotic — or every factor vanishes from `1` on, which is exactly the hypothesis
of `Gap212.Sieve.LcmGramSumLimitOfSupport` and `Gap212.Sieve.TotientGramSumLimitOfSupport` at
`β = 1`.

If every factor is non-zero somewhere on `[0,∞)`, pick such a point in each coordinate and move the
`i`-th to `t`; the product stays non-zero, so the point is retreated, so
`Gap212.Sieve.coord_lt_half_of_mem_retreatRegion` bounds its `i`-th coordinate by `1/2` — and
`t ≥ 1` does not. -/
theorem exists_null_or_forall_eq_zero_of_one_le {p : SupportParams} {k : ℕ} {j : Fin p.n} {ε₀ : ℝ}
    (hε₀ : 0 ≤ ε₀) {F : Fin k → ℝ → ℝ}
    (hsupp : ∀ t : Fin k → ℝ, (∀ i, 0 ≤ t i) → (∏ i, F i (t i)) ≠ 0 →
      t ∈ retreatRegion p k j ε₀) :
    (∃ i₀, ∀ t : ℝ, 0 ≤ t → F i₀ t = 0) ∨ ∀ i, ∀ t : ℝ, 1 ≤ t → F i t = 0 := by
  by_cases hall : ∀ i, ∃ s : ℝ, 0 ≤ s ∧ F i s ≠ 0
  · refine Or.inr fun i t ht ↦ ?_
    choose s hs0 hsne using hall
    by_contra hne
    have hnn : ∀ i', 0 ≤ Function.update s i t i' := by
      intro i'
      by_cases hi : i' = i
      · subst hi; rw [Function.update_self]; linarith
      · rw [Function.update_of_ne hi]; exact hs0 i'
    have hmem := hsupp (Function.update s i t) hnn
      (Finset.prod_ne_zero_iff.mpr fun i' _ ↦ by
        by_cases hi : i' = i
        · subst hi; rwa [Function.update_self]
        · rw [Function.update_of_ne hi]; exact hsne i')
    have hlt := coord_lt_half_of_mem_retreatRegion hε₀ hmem i
    rw [Function.update_self] at hlt
    linarith
  · push Not at hall
    obtain ⟨i₀, hi₀⟩ := hall
    exact Or.inl ⟨i₀, fun t ht ↦ hi₀ t ht⟩

/-- **The same, for the reduced retreat.** `Gap212.GPY.IsReducedRetreat` reads the retreat region
at the vector extended by `0` at the removed coordinate; the extension is nonnegative wherever the
vector is and has the same coordinate sum, so
`Gap212.Sieve.coord_lt_half_of_mem_retreatRegion` applies at the index `i₀.succAbove i` and the
argument of `Gap212.Sieve.exists_null_or_forall_eq_zero_of_one_le` goes through verbatim. -/
theorem exists_null_or_forall_eq_zero_of_one_le_insertNth {p : SupportParams} {m : ℕ} {j : Fin p.n}
    {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) {i₀ : Fin (m + 1)} {F : Fin m → ℝ → ℝ}
    (hsupp : ∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∏ i, F i (t i)) ≠ 0 →
      i₀.insertNth 0 t ∈ retreatRegion p (m + 1) j ε₀) :
    (∃ i', ∀ t : ℝ, 0 ≤ t → F i' t = 0) ∨ ∀ i, ∀ t : ℝ, 1 ≤ t → F i t = 0 := by
  by_cases hall : ∀ i, ∃ s : ℝ, 0 ≤ s ∧ F i s ≠ 0
  · refine Or.inr fun i t ht ↦ ?_
    choose s hs0 hsne using hall
    by_contra hne
    have hnn : ∀ i', 0 ≤ Function.update s i t i' := by
      intro i'
      by_cases hi : i' = i
      · subst hi; rw [Function.update_self]; linarith
      · rw [Function.update_of_ne hi]; exact hs0 i'
    have hmem := hsupp (Function.update s i t) hnn
      (Finset.prod_ne_zero_iff.mpr fun i' _ ↦ by
        by_cases hi : i' = i
        · subst hi; rwa [Function.update_self]
        · rw [Function.update_of_ne hi]; exact hsne i')
    have hlt := coord_lt_half_of_mem_retreatRegion hε₀ hmem (i₀.succAbove i)
    rw [Fin.insertNth_apply_succAbove, Function.update_self] at hlt
    linarith
  · push Not at hall
    obtain ⟨i₀', hi₀⟩ := hall
    exact Or.inl ⟨i₀', fun t ht ↦ hi₀ t ht⟩

/-! ## A null factor kills the asserted limit -/

/-- **A factor vanishing on `[0,∞)` kills the Gram integral.** A function that is identically zero
on `[0,∞)` is locally constant at every point of `(0,∞)`, so its derivative vanishes there and the
set integral over `Set.Ioi 0` of either product is zero. Stated with the null factor on either
side. -/
theorem integral_deriv_mul_deriv_eq_zero_of_null {f g : ℝ → ℝ}
    (hnull : (∀ t : ℝ, 0 ≤ t → f t = 0) ∨ ∀ t : ℝ, 0 ≤ t → g t = 0) :
    (∫ t in Set.Ioi (0 : ℝ), deriv f t * deriv g t) = 0 := by
  have hz : ∀ t ∈ Set.Ioi (0 : ℝ), deriv f t * deriv g t = (0 : ℝ) := by
    intro t ht
    have key : ∀ h : ℝ → ℝ, (∀ u : ℝ, 0 ≤ u → h u = 0) → deriv h t = 0 := by
      intro h hh
      have hev : h =ᶠ[nhds t] fun _ ↦ (0 : ℝ) := by
        filter_upwards [eventually_gt_nhds ht] with u hu using hh u hu.le
      rw [hev.deriv_eq, deriv_const]
    rcases hnull with h | h
    · rw [key f h, zero_mul]
    · rw [key g h, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hz]
  simp

/-- **A null unprimed factor kills the product of Gram integrals**, which is the limit both
divisor-sum asymptotics assert. -/
theorem prod_integral_eq_zero_of_null_left {k : ℕ} {F G : Fin k → ℝ → ℝ} {i₀ : Fin k}
    (hnull : ∀ t : ℝ, 0 ≤ t → F i₀ t = 0) :
    (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t) = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i₀) (integral_deriv_mul_deriv_eq_zero_of_null (Or.inl hnull))

/-- **A null primed factor kills the product of Gram integrals**, the companion of
`Gap212.Sieve.prod_integral_eq_zero_of_null_left`. -/
theorem prod_integral_eq_zero_of_null_right {k : ℕ} {F G : Fin k → ℝ → ℝ} {i₀ : Fin k}
    (hnull : ∀ t : ℝ, 0 ≤ t → G i₀ t = 0) :
    (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t) = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i₀) (integral_deriv_mul_deriv_eq_zero_of_null (Or.inr hnull))

end Gap212.Sieve
