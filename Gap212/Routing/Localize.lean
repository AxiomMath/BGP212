/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.PointABridge
public meta import Gap212.Attr

/-!
# Localizing a convolution in the scale, and why the routing needs it

Why `Gap212.Harman.RoutingConclusionFamily` cannot be assembled with one width per estimate.

## The obstruction

`Gap212.HasEquidistributionFamily f D (triples ω δ G)` carries **one** width `δ`
and requires its walls
of **every** `g ∈ G`, where `G` must satisfy `∀ x > 1, ∃ g ∈ G, N x = x^g` — so `G` has to cover
every scale the sequence takes. The routing, by contrast, splits the Type II range into three
overlapping γ-ranges and applies a different estimate, with a different width, on each.

Those two cannot be reconciled by taking `G` to be the whole range and `δ` its worst width, because
no width works throughout. `Gap212.Routing.typeIIa_wall_unsatisfiable` is the proof: at the bottom
of the Type II class, `γ = ξ₂ - ϵ`, the first wall of the Type IIa estimate ([2, Lemma 3]) reads

    24ω_max + 7δ - 5(ξ₂ - ϵ) + ε₁ < -2,   i.e.   7δ + ε₁ < -0.156…,

which fails for every `δ ≥ 0`. So the estimate genuinely cannot be applied with a `G` reaching that
far down, and the three-range split is not a convenience.

## Localization, without touching the cited inputs

Restrict the *sequence* instead of the exponent set. For a set `S` of scales put
`Gap212.Routing.restrict S α n x = α n x` on `S` and `0` off it. Then:

* `restrict` preserves being a coefficient sequence, being located at a scale, and having
  Siegel–Walfisz — off `S` the sequence vanishes, so every condition is vacuous there;
* `dconvFamily (restrict S α) (restrict S β) = restrict S (dconvFamily α β)`, so a
  convolution localizes by
  localizing its factors, and the Harman-class shape survives;
* at a scale `x ∈ S`, the discrepancy of `restrict S f` *equals* that of `f`.

So the three routes are applied to three localized copies of `f`, each with its own `G` covering
only the scales where it is used, and `Gap212.Routing.hasEquidistributionOverQstar_of_cover`
reassembles them: the constants are finitely many, so their maximum serves.

What this costs is a scale-dependent `N`: the localized copy needs its scale function patched off
`S` so the exponent condition still holds there, harmless because the sequence is `0` there. That
patching is the one place the assembly does something the source does not mention.

## Main results

* `Gap212.Routing.typeIIa_wall_unsatisfiable`: the obstruction, as a theorem.
* `Gap212.Routing.restrict` and its closure lemmas.
* `Gap212.Routing.hasEquidistributionOverQstar_of_cover`: reassembly from a finite cover of scales.
-/

@[expose] public section

namespace Gap212.Routing

open Finset Real Gap212.PointA Gap212.Packing

/-! ## The obstruction -/

/-- **The first Type IIa wall is unsatisfiable at the bottom of the Type II range.** At `γ = ξ₂ - ϵ`
it demands `7δ + ε₁ < -0.156…`, impossible for `δ ≥ 0`.

So no single width lets the Type IIa estimate be applied with an exponent set reaching `ξ₂ - ϵ`,
and the routing must localize in the scale — see `Gap212.Routing.restrict`. -/
theorem typeIIa_wall_unsatisfiable {δstar ε₁ : ℝ} (hδ : 0 ≤ δstar) (hε₁ : 0 < ε₁) :
    ¬ (24 * ((ω : ℚ) : ℝ) + 7 * δstar - 5 * ((2 / 5 : ℝ) - ((ϵ : ℚ) : ℝ)) + ε₁ < -2) := by
  rw [cast_ω, cast_ϵ]
  norm_num
  linarith

/-! ## Localizing in the scale -/

open Classical in
/-- `restrict S α` agrees with `α` at scales in `S` and vanishes elsewhere. -/
noncomputable def restrict (S : Set ℝ) (α : ℕ → ℝ → ℂ) : ℕ → ℝ → ℂ :=
  fun n x ↦ if x ∈ S then α n x else 0

/-- At a scale `x ∈ S`, `restrict S α n x = α n x`. -/
theorem restrict_of_mem {S : Set ℝ} {α : ℕ → ℝ → ℂ} {n : ℕ} {x : ℝ} (hx : x ∈ S) :
    restrict S α n x = α n x := by
  simp [restrict, hx]

/-- At a scale `x ∉ S`, `restrict S α n x = 0`. -/
theorem restrict_of_notMem {S : Set ℝ} {α : ℕ → ℝ → ℂ} {n : ℕ} {x : ℝ} (hx : x ∉ S) :
    restrict S α n x = 0 := by
  simp [restrict, hx]

/-- Localizing preserves being a coefficient sequence. -/
theorem isCoefficientSequence_restrict {S : Set ℝ} {α : ℕ → ℝ → ℂ}
    (h : IsCoefficientSequenceFamily α) : IsCoefficientSequenceFamily (restrict S α) := by
  obtain ⟨C, k, l, hC, hbd⟩ := h
  refine ⟨C, k, l, hC, fun n x hx ↦ ?_⟩
  by_cases hm : x ∈ S
  · rw [restrict_of_mem hm]; exact hbd n x hx
  · rw [restrict_of_notMem hm, norm_zero]
    have hl : (0 : ℝ) ≤ log x := (Real.log_pos hx).le
    positivity

/-- Localizing preserves being located at a scale: off `S` the sequence vanishes, so the condition
is vacuous there. -/
theorem locatedAtScale_restrict {S : Set ℝ} {α : ℕ → ℝ → ℂ} {N : ℝ → ℝ}
    (h : LocatedAtScaleFamily α N) : LocatedAtScaleFamily (restrict S α) N := by
  obtain ⟨c, C, hc, hcC, hbd⟩ := h
  refine ⟨c, C, hc, hcC, fun x hx n hne ↦ ?_⟩
  by_cases hm : x ∈ S
  · exact hbd x hx n (by rwa [restrict_of_mem hm] at hne)
  · exact (hne (restrict_of_notMem hm)).elim

/-- **A convolution localizes by localizing its factors.** This is what keeps the Harman-class
shape intact under localization. -/
theorem dconv_restrict (S : Set ℝ) (α β : ℕ → ℝ → ℂ) :
    dconvFamily (restrict S α) (restrict S β) = restrict S (dconvFamily α β) := by
  funext n x
  by_cases hm : x ∈ S <;> simp [dconvFamily, restrict_of_mem, restrict_of_notMem, hm]

/-- **At a scale inside `S` the discrepancy is unchanged.** This is what lets a bound proved for
the localized copy be quoted for `f` itself. -/
theorem discrepancy_restrict_of_mem {f : ℕ → ℝ → ℂ} {S : Set ℝ} {x : ℝ} {a q : ℕ} (hx : x ∈ S) :
    discrepancy (restrict S f) x a q = discrepancy f x a q := by
  simp only [discrepancy, restrict_of_mem hx]

/-! ## Reassembly from a finite cover of scales -/

open Classical in
/-- **Reassembly.** If finitely many scale-sets cover `(1, ∞)` and `f` localized to each
equidistributes over the generated moduli, so does `f`. Their constants are finitely many, so the
maximum serves.

This is the step that lets the three Type II routes — which cannot share a width — be combined. -/
theorem hasEquidistributionOverQstar_of_cover {p : SupportParams} {f : ℕ → ℝ → ℂ}
    {ι : Type*} [Finite ι] [Nonempty ι] {S : ι → Set ℝ}
    (hcover : ∀ x : ℝ, 1 < x → ∃ i, x ∈ S i)
    (h : ∀ i, HasEquidistributionOverQstarFamily p (restrict (S i) f)) :
    HasEquidistributionOverQstarFamily p f := by
  classical
  have _inst : Fintype ι := Fintype.ofFinite ι
  intro ε₀ hε₀ A hA
  choose c hc hbd using fun i ↦ h i ε₀ hε₀ A hA
  refine ⟨Finset.univ.sup' Finset.univ_nonempty c, ?_, ?_⟩
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact lt_of_lt_of_le (hc i) (Finset.le_sup' c (Finset.mem_univ i))
  · intro x hx a ha
    obtain ⟨i, hi⟩ := hcover x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hlog : (0 : ℝ) < (log x) ^ A := Real.rpow_pos_of_pos (Real.log_pos hx) A
    calc ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ Squarefree q}, discrepancy f x a q
        = ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ Squarefree q},
            discrepancy (restrict (S i) f) x a q :=
          Finset.sum_congr rfl fun q _ ↦ (discrepancy_restrict_of_mem hi).symm
      _ ≤ c i * x / (log x) ^ A := hbd i x hx a ha
      _ ≤ Finset.univ.sup' Finset.univ_nonempty c * x / (log x) ^ A := by
          gcongr; exact Finset.le_sup' c (Finset.mem_univ i)

end Gap212.Routing
