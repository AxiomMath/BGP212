/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Defs
public import Gap212.Extraction.Setup
public meta import Gap212.Attr

/-!
# The unscaled rough profile, and the chamber cover

Two loose ends of the equidistribution layer.

## The profile, twice

The factor-extraction lemmas consume the pooled rough logarithms *rescaled* by `(1 - ε₀)⁻¹`,
because the packing conditions are stated against the support's own caps `B_{j,m}` rather than the
retreated ones. That is `Gap212.Extraction.xi_of_qgen`. But the routes that read a modulus's size
off its factorization want the logarithms themselves, against the retreated caps — the same tuple,
not divided.

Neither follows from the other, and the obstruction is the lower bound. `Ξ` records only `δ ≤ yᵢ`
for the rescaled tuple, so multiplying back by `1 - ε₀` yields `(1-ε₀)δ ≤ log_x fᵢ`, weaker than
the `δ ≤ log_x fᵢ` that `x^δ ≤ fᵢ` gives outright. So the unscaled form is proved
directly, from the same
three lines of `Qgen`.

## The chamber cover

A chamber is a compact region of `(ω₀, γ, δ)`-space on which one fixed estimate is invoked, and the
positive-level argument needs finitely many of them to cover every modulus's parameter point. The
covering is a product: the level runs over a compact interval `[0, ω]` (nonnegative because the
range is positive-level, bounded because `Gap212.Extraction.qgen_le` caps the modulus), the width
is the datum's fixed `δ`, and the exponent runs over the finitely many `γ`-ranges the routes carve
out.

So the content is that a product of a compact interval, a compact `γ`-piece and a point is a
chamber, and that finitely many of them cover when the `γ`-pieces do. Compactness is what
`Gap212.Auxiliary.uniform_margin_on_compact` then turns into a uniform margin.

## Main results

* `Gap212.Extraction.xi_of_qgen_unscaled`: the unscaled pooled profile lies in `Ξ` at the retreated
  caps.
* `Gap212.Defs.exists_chambers_cover`: finitely many chambers cover the positive-level parameter
  points.
-/

@[expose] public section

namespace Gap212.Extraction

open Finset Real Gap212.Packing

/-- **The unscaled rough profile lies in `Ξ` at the retreated caps.** A modulus generated at
`(j, j', m, m')` pools its rough factors into a tuple `F` of length `m + m'`, every entry at least
`x^δ`, whose logarithms `log_x F i` lie in `Ξ((1-ε₀)B_{j,m}, (1-ε₀)B_{j',m'}, m, m', δ)`.

Each of the three requirements is one line of `Qgen`: the roughness `x^δ ≤ fᵢ` gives the lower
bound, the two product caps give the two sums, and the upper bound `≤ 1` follows because a single
coordinate is at most the sum, which is at most `(1-ε₀)B ≤ 1`.

Compare `Gap212.Extraction.xi_of_qgen`, which divides through by `1 - ε₀` to reach the support's
own caps. That is what the packing conditions need; this is what the routes need. -/
@[gap212 "lem_rough_profile_in_xi_unscaled"]
theorem xi_of_qgen_unscaled {p : SupportParams} {x ε₀ : ℝ} {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hδ : 0 < p.δ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hq : q ∈ Qgen p x j j' m m' ε₀) :
    ∃ (F : Fin (m + m') → ℕ) (y : Fin (m + m') → ℝ),
      (∀ i, x ^ p.δ ≤ (F i : ℝ)) ∧
      (∀ i, y i = logb x (F i)) ∧
      y ∈ Xi ((1 - ε₀) * p.B j m) ((1 - ε₀) * p.B j' m') m m' p.δ := by
  classical
  obtain ⟨e, e', f, f', -, -, -, hfcap, hf'cap, -, -, -, hfr, hf'r⟩ := hq
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hone : (1 : ℝ) - ε₀ ≤ 1 := by linarith
  have hpos : (0 : ℝ) < 1 - ε₀ := by linarith
  -- Every rough factor exceeds `x^δ > 1`, hence is at least `1`.
  have hxδ1 : 1 < x ^ p.δ := (Real.one_lt_rpow_iff_of_pos hx0).mpr (Or.inl ⟨hx, hδ⟩)
  have hf1 : ∀ i, 1 ≤ f i := fun i ↦ by
    have h : (1 : ℝ) < (f i : ℝ) := lt_of_lt_of_le hxδ1 (hfr i)
    exact_mod_cast h.le
  have hf'1 : ∀ i, 1 ≤ f' i := fun i ↦ by
    have h : (1 : ℝ) < (f' i : ℝ) := lt_of_lt_of_le hxδ1 (hf'r i)
    exact_mod_cast h.le
  set u : Fin m → ℝ := fun i ↦ logb x (f i) with hu_def
  set v : Fin m' → ℝ := fun i ↦ logb x (f' i) with hv_def
  have hsumu : ∑ i, u i ≤ (1 - ε₀) * p.B j m :=
    sum_logb_le_of_prod_le hx univ f (fun i _ ↦ hf1 i) hfcap
  have hsumv : ∑ i, v i ≤ (1 - ε₀) * p.B j' m' :=
    sum_logb_le_of_prod_le hx univ f' (fun i _ ↦ hf'1 i) hf'cap
  have hu_lb : ∀ i, p.δ ≤ u i := fun i ↦ le_logb_of_rpow_le hx (hf1 i) (hfr i)
  have hv_lb : ∀ i, p.δ ≤ v i := fun i ↦ le_logb_of_rpow_le hx (hf'1 i) (hf'r i)
  have hcap : (1 - ε₀) * p.B j m ≤ 1 := by nlinarith
  have hcap' : (1 - ε₀) * p.B j' m' ≤ 1 := by nlinarith
  have hu_ub : ∀ i, u i ≤ 1 := fun i ↦ by
    have hnn : ∀ k, 0 ≤ u k := fun k ↦ le_trans hδ.le (hu_lb k)
    have := Finset.single_le_sum (f := u) (fun k _ ↦ hnn k) (Finset.mem_univ i)
    exact le_trans (le_trans this hsumu) hcap
  have hv_ub : ∀ i, v i ≤ 1 := fun i ↦ by
    have hnn : ∀ k, 0 ≤ v k := fun k ↦ le_trans hδ.le (hv_lb k)
    have := Finset.single_le_sum (f := v) (fun k _ ↦ hnn k) (Finset.mem_univ i)
    exact le_trans (le_trans this hsumv) hcap'
  refine ⟨Fin.append f f', Fin.append u v, ?_, ?_, ?_⟩
  · exact fun i ↦ append_mem_of_mem (S := {n : ℕ | x ^ p.δ ≤ (n : ℝ)}) f f' hfr hf'r i
  · intro i
    induction i using Fin.addCases with
    | left i => simp only [hu_def, Fin.append_left]
    | right i => simp only [hv_def, Fin.append_right]
  · exact mem_Xi_append u v (fun i ↦ ⟨hu_lb i, hu_ub i⟩) (fun i ↦ ⟨hv_lb i, hv_ub i⟩) hsumu hsumv

end Gap212.Extraction

namespace Gap212.Defs

open Finset Real

/-- **Finitely many chambers cover the positive-level parameter points.** Given a finite family of
compact `γ`-pieces covering the exponent range, the products `[0, ω] × Gᵢ × {δ}` are chambers, and
every parameter point with nonnegative level below `ω` and exponent in the range lies in one.

The three factors are what the argument has to hand: the level is nonnegative because the range is
the positive-level one and bounded above because `Gap212.Extraction.qgen_le` caps the modulus at
`x^{1/2 + 2ω}`; the width is the datum's fixed `δ`; and the exponent range is the union of the
finitely many `γ`-ranges the Type I, II and III routes carve out, each an interval, hence compact.

Compactness is the whole point of packaging them this way: it is what
`Gap212.Auxiliary.uniform_margin_on_compact` needs to turn each estimate's strict parameter
inequalities into a margin uniform over the chamber, and a margin uniform over finitely many
chambers is a margin, full stop. -/
theorem exists_chambers_cover {ω δ : ℝ} {r : ℕ} (G : Fin r → Set ℝ)
    (hGc : ∀ i, IsCompact (G i)) (Γ : Set ℝ) (hcov : Γ ⊆ ⋃ i, G i) :
    ∃ K : Fin r → PositiveLevelChamber,
      ∀ ω₀ ∈ Set.Icc (0 : ℝ) ω, ∀ γ ∈ Γ, ∃ i, (ω₀, γ, δ) ∈ (K i).carrier := by
  refine ⟨fun i ↦
    { carrier := Set.Icc (0 : ℝ) ω ×ˢ (G i ×ˢ ({δ} : Set ℝ))
      isCompact := (isCompact_Icc).prod ((hGc i).prod isCompact_singleton)
      nonneg := fun q hq ↦ hq.1.1 }, ?_⟩
  intro ω₀ hω₀ γ hγ
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hγ)
  exact ⟨i, ⟨hω₀, hi, rfl⟩⟩

end Gap212.Defs
