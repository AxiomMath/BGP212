/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCut

/-!
# The middle branch of a two-threshold cut

`Gap212.Packing.SortedCut` supplies the two one-sided readings of a cut on the second group's
largest coordinate: `Gap212.Packing.admitsPartition₄_of_rank_certificate_cut_low`, valid where
every coordinate of the group is at most `t` and every bin's affine constant `q k` is nonnegative,
and `..._cut_high`, valid where some coordinate is at least `t` and every `q k` is nonpositive. Two
applications of `Gap212.Packing.admitsPartition₄_of_cut`, at `t₁` then at `t₂`, split the profile
space into three branches instead of two, and the middle one

    t₁ ≤ y (e₂ 0) ≤ t₂

is served by **neither** of those lemmas at full strength. It is served by each of them at half
strength — `..._cut_low` at `t₂` uses only the upper bound, `..._cut_high` at `t₁` only the lower —
and that is strictly weaker than the branch allows, because the branch knows both.

## Why that gap is not cosmetic

Write `A = sup {t : the low reading closes this point}` and
`C = inf {t : the high reading closes it}`. The low reading's hypothesis strengthens as `t` falls
and the high reading's as `t` rises, so a *single* threshold closes the point exactly when `C ≤ A`.
Suppose `C > A`, which is the situation at the cells a single threshold cannot reach. Then a
three-way split at `t₁ ≤ t₂` needs `t₁ ≤ A` for its bottom branch and `t₂ ≥ C` for its top one; and
if the middle branch had to be read by `..._cut_low` at `t₂` it would need `t₂ ≤ A < C ≤ t₂`, while
reading it by `..._cut_high` at `t₁` would need `t₁ ≥ C > A ≥ t₁`. Both are contradictions. **So the
middle branch of a three-way split is not a combination of the two existing lemmas, and a
two-threshold split cannot be built from them alone.**

What the middle branch does give is one payment rule per bin rather than one for the certificate:
the `q` term of `Gap212.Packing.admitsPartition₄_of_rank_certificate_enum` is
`q k · (y (e₂ 0) - δ)`, and on the middle branch that is at most `q k · (t₂ - δ)` when `q k ≥ 0`
and at most `q k · (t₁ - δ)` when `q k ≤ 0`. Each bin picks the threshold its own sign wants, and
the signs may differ across the four bins — which is exactly what the one-sided lemmas forbid.

## What is here

* `Gap212.Packing.admitsPartition₄_of_rank_certificate_cut_mid`: the rank certificate on the middle
  branch, with a per-bin payment threshold `w k` constrained only by `hw` to be `t₂` where `q k` is
  nonnegative and `t₁` where it is nonpositive.

No new gluing lemma is needed: `Gap212.Packing.admitsPartition₄_of_cut` applied at `t₁`, and then
again at `t₂` inside its own high branch, produces the three branches with the middle one carrying
both hypotheses.
-/

@[expose] public section

namespace Gap212.Packing

open Finset

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **The rank certificate on the middle branch of a two-threshold cut.**

Every coordinate of the second group is at most `t₂`, some coordinate is at least `t₁`, and each
bin names the threshold it pays its `q` term at: `t₂` if its constant is nonnegative, `t₁` if
nonpositive. Nothing constrains the four signs to agree, which is the whole point — with all of
them nonnegative this is `Gap212.Packing.admitsPartition₄_of_rank_certificate_cut_low` at `t₂`,
with all of them nonpositive it is `..._cut_high` at `t₁`, and a mixed certificate is available to
neither.

`w` is a parameter rather than `if 0 ≤ q k then t₂ else t₁` so that a caller passes the four
thresholds as numerals and `hw` is four disjunctions `norm_num` settles. -/
theorem admitsPartition₄_of_rank_certificate_cut_mid {m₁ m₂ : ℕ} (hm₂ : 0 < m₂)
    {B₁ B₂ δ t₁ t₂ : 𝕜} {y : Fin (m₁ + m₂) → 𝕜} (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) (hδ : 0 ≤ δ)
    (hcutle : ∀ i : Fin (m₁ + m₂), m₁ ≤ (i : ℕ) → y i ≤ t₂)
    (hcutge : ∃ i : Fin (m₁ + m₂), m₁ ≤ (i : ℕ) ∧ t₁ ≤ y i)
    (T : Fin 4 → Finset (Fin m₁)) (U : Fin 4 → Finset (Fin m₂))
    (hTcover : ∀ j, ∃ k, j ∈ T k) (hTdisj : ∀ k l, k ≠ l → Disjoint (T k) (T l))
    (hUcover : ∀ j, ∃ k, j ∈ U k) (hUdisj : ∀ k l, k ≠ l → Disjoint (U k) (U l))
    (r s q w : Fin 4 → 𝕜) (hr0 : ∀ k, 0 ≤ r k) (hs0 : ∀ k, 0 ≤ s k)
    (hw : ∀ k, (0 ≤ q k ∧ w k = t₂) ∨ (q k ≤ 0 ∧ w k = t₁))
    (hr : ∀ k, ∀ j : ℕ, ((((T k).filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ r k * j)
    (hs : ∀ k, ∀ j : ℕ, 1 ≤ j → j ≤ m₂ →
      ((((U k).filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ s k * j + q k)
    (c : Fin 4 → 𝕜)
    (hcap : ∀ k, ((((T k).card : ℕ) : 𝕜) * δ + r k * (B₁ - (m₁ : 𝕜) * δ))
        + ((((U k).card : ℕ) : 𝕜) * δ + s k * (B₂ - (m₂ : 𝕜) * δ) + q k * (w k - δ)) ≤ c k) :
    AdmitsPartition₄ y (c 0) (c 1) (c 2) (c 3) := by
  classical
  obtain ⟨e₂, he₂, he₂G, he₂anti⟩ :=
    exists_antitone_enum (Finset.univ.filter (fun i : Fin (m₁ + m₂) ↦ ¬ ((i : ℕ) < m₁))) y
      (card_highGroup m₁ m₂)
  have hmem : e₂ ⟨0, hm₂⟩ ∈ Finset.univ.filter (fun i : Fin (m₁ + m₂) ↦ ¬ ((i : ℕ) < m₁)) := by
    rw [← he₂G]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hle : y (e₂ ⟨0, hm₂⟩) ≤ t₂ := hcutle _ (not_lt.1 (Finset.mem_filter.1 hmem).2)
  have hge : t₁ ≤ y (e₂ ⟨0, hm₂⟩) := by
    obtain ⟨i₀, hi₀, hti₀⟩ := hcutge
    have hmem₀ : i₀ ∈ Finset.image e₂ Finset.univ := by
      rw [he₂G]; exact Finset.mem_filter.2 ⟨Finset.mem_univ i₀, not_lt.2 hi₀⟩
    rw [Finset.mem_image] at hmem₀
    obtain ⟨j, -, rfl⟩ := hmem₀
    exact hti₀.trans (he₂anti (show (⟨0, hm₂⟩ : Fin m₂) ≤ j from Nat.zero_le _))
  refine admitsPartition₄_of_rank_certificate_enum hm₂ hy hδ he₂ he₂G he₂anti T U hTcover hTdisj
    hUcover hUdisj r s q hr0 hs0 hr hs c fun k ↦ ?_
  have hck := hcap k
  rcases hw k with ⟨hq, hwk⟩ | ⟨hq, hwk⟩
  · have hpay := mul_le_mul_of_nonneg_left (sub_le_sub_right hle δ) hq
    rw [hwk] at hck
    linarith
  · have hpay := mul_le_mul_of_nonpos_left (sub_le_sub_right hge δ) hq
    rw [hwk] at hck
    linarith

end Gap212.Packing
