/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Auxiliary.Estimates
public meta import Gap212.Attr

/-!
# The transition window, and uniform subset-sums

## The transition window

`Gap212.Auxiliary.kappa_range_on_tr` bounds the deficiency on the transition range by
`C log log x / log x`. That is not yet what the transport argument needs, which is a bound by a
*fixed* multiple of `ϵ`: the transport radius is a fixed positive number, so the deficiency has to
be below it eventually rather than merely tending to zero. Composing the two gives the window.

The limit itself is `log y / y → 0` composed with `log x → ∞`, which is where Mathlib does the
work.

## Uniform subset-sums

`Gap212.Packing.exists_subset_sum_mem_Icc` hits one target window with a subset of the smooth
reservoir. The four-factor extraction at a `q`-scaled window needs more: the third window is pinned
to the full modulus rather than to the extracted factor `r`, so the *same* factorization has to
work for every `R` in the first window at once. That is the uniform statement: every target below
the total mass is met, not just one.

Greedy induction supplies it: take the element if it fits under the target, skip it otherwise, and
the two cases give the two bounds. The `- d` on the lower side is exactly the granularity of the
weights, which is why each one has to be at most `d`.

## Main results

* `Gap212.Transition.kappa_in_window`: the deficiency is eventually inside a fixed window.
* `Gap212.Extraction.subset_sum_uniform`: every target below the total mass is met to within `d`.
-/

@[expose] public section

namespace Gap212.Transition

open Real Filter Topology

/-- **`log log x / log x → 0`.** The limit behind the transition window, as the composition of
`log y / y → 0` with `log x → ∞`. -/
theorem tendsto_logLog_div_log :
    Tendsto (fun x : ℝ ↦ Real.log (Real.log x) / Real.log x) atTop (nhds 0) := by
  have hlogdiv : Tendsto (fun y : ℝ ↦ Real.log y / y) atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
    simpa using this
  have := hlogdiv.comp Real.tendsto_log_atTop
  simpa only [Function.comp_def] using this

/-- **The deficiency enters the transport window.** For fixed `C` and `ϵ > 0` there is an `x₀`
beyond which every modulus of the transition range at parameter `C` has deficiency between `0` and
`(11/80)ϵ`.

The two halves come from different places. That `κ > 0` is `Gap212.Auxiliary.kappa_range_on_tr`
applied pointwise — the transition range is below the half-level by definition. That `κ` is below
the *fixed* bound is the limit: `kappa_range_on_tr` gives only `κ < C log log x / log x`, which
shrinks but is not itself small, while the transport radius it has to fit inside does not.

`11/80` is the fraction of the slack the transport argument can afford at the four raw capacities;
see `Gap212.Transition.transitionRadius` and `Gap212.Transition.IIc.bin₄_binding`. -/
theorem kappa_in_window {C ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, exp 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ q : ℝ, 0 < q →
      x ^ ((1 : ℝ) / 2) / (log x) ^ C < q → q < x ^ ((1 : ℝ) / 2) →
      0 ≤ 1 / 2 - log q / log x ∧ 1 / 2 - log q / log x ≤ 11 / 80 * ε := by
  have hthr : 0 < 11 / 80 * ε := by positivity
  have hmul : Tendsto (fun x : ℝ ↦ C * (Real.log (Real.log x) / Real.log x)) atTop (nhds 0) := by
    have := tendsto_logLog_div_log.const_mul C
    simpa using this
  have heven : ∀ᶠ x : ℝ in atTop, C * (Real.log (Real.log x) / Real.log x) ≤ 11 / 80 * ε :=
    hmul.eventually_le_const hthr
  rw [eventually_atTop] at heven
  obtain ⟨a, ha⟩ := heven
  refine ⟨max a (exp 1 + 1), lt_of_lt_of_le (by linarith) (le_max_right a (exp 1 + 1)), ?_⟩
  intro x hx q hq hlo hhi
  have hxe : exp 1 < x := lt_of_lt_of_le (by linarith) (le_trans (le_max_right a (exp 1 + 1)) hx)
  obtain ⟨hpos, hlt⟩ := Gap212.Auxiliary.kappa_range_on_tr (C := C) hxe hq hlo hhi
  refine ⟨hpos.le, le_trans hlt.le ?_⟩
  rw [mul_div_assoc]
  exact ha x (le_trans (le_max_left a (exp 1 + 1)) hx)

end Gap212.Transition

namespace Gap212.Extraction

open Finset

/-- **Uniform subset-sums.** If every weight is at most `d`, then *every* target between `0` and
the total mass is met by some subset, to within `d` on the low side.

This is the uniform form of the window-hitting step. `Gap212.Packing.exists_subset_sum_mem_Icc`
hits one prescribed window; four-factor extraction at a `q`-scaled window needs one factorization
that works for every `R` in the first window simultaneously, and that is what quantifying the
target inside gives.

The proof is greedy: at each element, take it if it fits under the remaining target and skip it
otherwise. Taking it keeps the sum below the target by induction; skipping it can only happen when
the element alone exceeds the target, in which case the target is already below `d` and the empty
subset serves. That is where `w i ≤ d` is spent, and it is why the low-side slack is exactly
`d`. -/
theorem subset_sum_uniform {ι : Type*} (s : Finset ι) (w : ι → ℝ) (d : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ d) (hd : 0 ≤ d) :
    ∀ t : ℝ, 0 ≤ t → t ≤ ∑ i ∈ s, w i →
      ∃ u ⊆ s, t - d ≤ ∑ i ∈ u, w i ∧ ∑ i ∈ u, w i ≤ t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro t ht0 htle
    refine ⟨∅, by simp, ?_, ?_⟩
    · simp only [Finset.sum_empty] at htle ⊢
      linarith
    · simp only [Finset.sum_empty] at htle ⊢
      linarith
  | insert a s' ha ih =>
    intro t ht0 htle
    by_cases hcase : w a ≤ t
    · -- The element fits: spend it, and meet the remaining target `t - w a` on `s'`.
      have hsum : ∑ i ∈ insert a s', w i = w a + ∑ i ∈ s', w i := Finset.sum_insert ha
      have hw_s' : ∀ i ∈ s', 0 ≤ w i ∧ w i ≤ d := fun i hi ↦ hw i (Finset.mem_insert_of_mem hi)
      have ht0' : 0 ≤ t - w a := by linarith
      have htle' : t - w a ≤ ∑ i ∈ s', w i := by rw [hsum] at htle; linarith
      obtain ⟨u', hu'sub, hu'1, hu'2⟩ := ih hw_s' (t - w a) ht0' htle'
      have hau' : a ∉ u' := fun h ↦ ha (hu'sub h)
      refine ⟨insert a u', Finset.insert_subset_insert a hu'sub, ?_, ?_⟩
      · rw [Finset.sum_insert hau']; linarith
      · rw [Finset.sum_insert hau']; linarith
    · -- The element alone overshoots, so the target is below `d` and the empty subset serves.
      have hwa : 0 ≤ w a ∧ w a ≤ d := hw a (Finset.mem_insert_self a s')
      refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
      · simp only [Finset.sum_empty]; linarith [hwa.2]
      · simp only [Finset.sum_empty]; linarith

end Gap212.Extraction
