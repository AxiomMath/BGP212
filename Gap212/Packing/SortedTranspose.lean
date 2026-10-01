/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCone
public import Gap212.Packing.SortedCellsUncut3
public import Gap212.Packing.SortedCellsRest

/-!
# Swapping the two groups of a cell

`Gap212.PackingCertificate` quantifies over **ordered** pairs `(m, m')`, while every rank
certificate is built for `m ≤ m'`, with the cut on the second group.
`Gap212.Packing.admitsPartition₄_of_comp_perm` transports along a permutation of *one* index type
and cannot pass between the two orders: `Fin (m₁ + m₂)` and `Fin (m₂ + m₁)` are not the same type,
so there is no `Equiv.Perm` to feed it.

This file supplies that transport. The content is that the whole four-block problem is
symmetric under exchanging the two groups, because `Ξ` caps the two groups separately and
`Gap212.Packing.AdmitsPartition₄` only ever sums over blocks of the index set:

* `Gap212.Packing.transposeEquiv` is the reindexing `Fin (m₂ + m₁) ≃ Fin (m₁ + m₂)` that sends the
  low group to the high one;
* `Gap212.Packing.xi_transpose` says it carries `Ξ B₁ B₂ m₁ m₂ δ` into `Ξ B₂ B₁ m₂ m₁ δ`;
* `Gap212.Packing.admitsPartition₄_of_comp_equiv` generalises `admitsPartition₄_of_comp_perm` to an
  equivalence between two `Fin` types, which is the one line the permutation version could not
  give;
* `Gap212.Packing.admitsPartition₄_transpose_of` puts the two together into the form a consumer
  wants: hand it any cell theorem for the pair `(m₂, m₁)`, curried over the profile, and get the
  conclusion for `(m₁, m₂)`.

So the 78 off-diagonal cells cost one `exact` each on top of the ordered cell, and the 13 diagonal
cells cost nothing at all — at `(m, m)` the two caps and the two group sizes agree, so the swap is
an automorphism of the problem and the ordered theorem already covers both readings.

## Main results

* `Gap212.Packing.admitsPartition₄_transpose_of`: the transport, in the shape a cell theorem plugs
  into.
* `Gap212.admitsPartition₄_cellTenSix_band`, `Gap212.admitsPartition₄_cellSevenFour_band`: the two
  worked examples, one over an uncut cell and one over a cut cell, showing the transport carries
  both instrument families.
-/

@[expose] public section

namespace Gap212.Packing

open Finset

/-! ## Reindexing the two groups -/

section Sums

variable {M : Type*} [AddCommMonoid M] {m₁ m₂ : ℕ}

/-- **The low group's sum, read on `Fin m₁`.** The filter `(i : ℕ) < m₁` picks out exactly the
image of `Fin.castAdd`, so its sum is a sum over the first group's own index type. -/
theorem sum_lowGroup_eq (y : Fin (m₁ + m₂) → M) :
    ∑ i ∈ univ.filter (fun i : Fin (m₁ + m₂) ↦ (i : ℕ) < m₁), y i =
      ∑ j : Fin m₁, y (Fin.castAdd m₂ j) := by
  classical
  rw [Finset.sum_filter, Fin.sum_univ_add]
  simp

/-- **The high group's sum, read on `Fin m₂`.** -/
theorem sum_highGroup_eq (y : Fin (m₁ + m₂) → M) :
    ∑ i ∈ univ.filter (fun i : Fin (m₁ + m₂) ↦ ¬ ((i : ℕ) < m₁)), y i =
      ∑ j : Fin m₂, y (Fin.natAdd m₁ j) := by
  classical
  rw [Finset.sum_filter, Fin.sum_univ_add]
  simp

end Sums

/-- **The index swap of a cell.** `Fin (m₂ + m₁) ≃ Fin (m₁ + m₂)`, sending the first `m₂` positions
to the last `m₂` and the last `m₁` to the first `m₁`: split both sides into a sum type and commute
the summands. -/
def transposeEquiv (m₁ m₂ : ℕ) : Fin (m₂ + m₁) ≃ Fin (m₁ + m₂) :=
  (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin m₂) (Fin m₁))).trans finSumFinEquiv

/-- **What the swap does to a profile**: it is `Fin.append` of the two groups in the other
order. -/
theorem comp_transposeEquiv {M : Type*} {m₁ m₂ : ℕ} (y : Fin (m₁ + m₂) → M) :
    y ∘ transposeEquiv m₁ m₂ =
      Fin.append (fun i : Fin m₂ ↦ y (Fin.natAdd m₁ i))
        (fun i : Fin m₁ ↦ y (Fin.castAdd m₂ i)) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [transposeEquiv]

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [IsStrictOrderedRing 𝕜] in
/-- **The check set is symmetric under the swap.** A profile capped by `B₁` on its first `m₁`
coordinates and by `B₂` on its last `m₂` becomes, after the swap, one capped by `B₂` on its first
`m₂` and by `B₁` on its last `m₁`. The box constraint is symmetric outright. -/
theorem xi_transpose {m₁ m₂ : ℕ} {B₁ B₂ δ : 𝕜} {y : Fin (m₁ + m₂) → 𝕜}
    (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) : y ∘ transposeEquiv m₁ m₂ ∈ Xi B₂ B₁ m₂ m₁ δ := by
  classical
  obtain ⟨hbox, hlow, hhigh⟩ := hy
  rw [sum_lowGroup_eq] at hlow
  rw [sum_highGroup_eq] at hhigh
  rw [comp_transposeEquiv]
  refine ⟨?_, ?_, ?_⟩
  · exact Fin.addCases (fun _ ↦ by simpa using hbox _) fun _ ↦ by simpa using hbox _
  · rw [sum_lowGroup_eq]; simpa using hhigh
  · rw [sum_highGroup_eq]; simpa using hlow

/-! ## Transport of the partition predicate -/

omit [IsStrictOrderedRing 𝕜] in
/-- **`AdmitsPartition₄` transports along an equivalence of index types.** The permutation version
`Gap212.Packing.admitsPartition₄_of_comp_perm` is the case `ℓ' = ℓ`, `σ : Equiv.Perm (Fin ℓ)`; the
proof is the same, since all it does is push the three named blocks forward along `σ` and observe
that the complement of the image is the image of the complement. Only the extra index gives the
group swap, where the two types are `Fin (m₂ + m₁)` and `Fin (m₁ + m₂)`. -/
theorem admitsPartition₄_of_comp_equiv {ℓ ℓ' : ℕ} (y : Fin ℓ → 𝕜) (σ : Fin ℓ' ≃ Fin ℓ)
    {b₁ b₂ b₃ b₄ : 𝕜} (h : AdmitsPartition₄ (y ∘ σ) b₁ b₂ b₃ b₄) :
    AdmitsPartition₄ y b₁ b₂ b₃ b₄ := by
  classical
  obtain ⟨I, J, K, hIJ, hIK, hJK, h1, h2, h3, h4⟩ := h
  have hsum (X : Finset (Fin ℓ')) : ∑ i ∈ X.map σ.toEmbedding, y i = ∑ i ∈ X, (y ∘ σ) i :=
    Finset.sum_map _ _ _
  have hcompl (X : Finset (Fin ℓ')) :
      Finset.univ \ X.map σ.toEmbedding = (Finset.univ \ X).map σ.toEmbedding := by
    rw [Finset.map_sdiff, Finset.map_univ_equiv]
  refine ⟨I.map σ.toEmbedding, J.map σ.toEmbedding, K.map σ.toEmbedding,
    Finset.disjoint_map _ |>.2 hIJ, Finset.disjoint_map _ |>.2 hIK,
    Finset.disjoint_map _ |>.2 hJK, ?_, ?_, ?_, ?_⟩
  · rwa [hsum]
  · rwa [hsum]
  · rwa [hsum]
  · rwa [← Finset.map_union, ← Finset.map_union, hcompl, hsum]

omit [IsStrictOrderedRing 𝕜] in
/-- **The transposed cell, discharged from the ordered one.**

`h` is any cell theorem for the pair `(m₂, m₁)`, curried over the profile — the shape every
`admitsPartition₄_cell*_band` theorem takes once its `γ` and `ω₀` hypotheses are supplied. The
conclusion is the same statement for `(m₁, m₂)`. This is the whole of what the ordered quantifier
in `Gap212.PackingCertificate` costs.

At a diagonal cell `m₁ = m₂` the two hypotheses coincide and this says nothing; it is the 78
off-diagonal cells that need it. -/
theorem admitsPartition₄_transpose_of {m₁ m₂ : ℕ} {B₁ B₂ δ : 𝕜} {c : Fin 4 → 𝕜}
    {y : Fin (m₁ + m₂) → 𝕜} (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ)
    (h : ∀ z ∈ Xi B₂ B₁ m₂ m₁ δ, AdmitsPartition₄ z (c 0) (c 1) (c 2) (c 3)) :
    AdmitsPartition₄ y (c 0) (c 1) (c 2) (c 3) :=
  admitsPartition₄_of_comp_equiv y (transposeEquiv m₁ m₂) (h _ (xi_transpose hy))

end Gap212.Packing

namespace Gap212

open Gap212.Packing

/-- **Cell `(10,6)`, the transpose of `(6,10)`.**

The worked example over an *uncut* cell, and the only one of the 62 whose ordered reading splits
the band: `Gap212.admitsPartition₄_cellSixTen_band` case-splits at `ω₀ = 27/4000` and then chains
rank certificates in `γ`. The transport is one application of
`Gap212.Packing.admitsPartition₄_transpose_of`; nothing about the certificates changes. -/
theorem admitsPartition₄_cellTenSix_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000) (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (10 + 6) → ℝ}
    (hy : y ∈ Xi (1081 / 5000 : ℝ) (983 / 5000) 10 6 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_transpose_of (c := fun k ↦ capD γ ω₀ k) hy
    fun _ hz ↦ admitsPartition₄_cellSixTen_band hωlo hωhi hγlo hγhi hz

/-- **Cell `(7,4)`, the transpose of `(4,7)`.**

The worked example over a *cut* cell: `Gap212.admitsPartition₄_cellFourSeven_band` closes `(4,7)`
by `Gap212.Packing.admitsPartition₄_of_cut` on the second group at `t = 1/20`, so here the cut
lands on the group of seven that is now *first*. The transport does not care — it swaps the index
type, and the cut hypothesis lives inside the ordered theorem. -/
theorem admitsPartition₄_cellSevenFour_band {γ ω₀ : ℝ} (hωlo : 4 / 625 < ω₀)
    (hωhi : ω₀ ≤ 7 / 1000) (hγlo : 2 / 5 - slack ≤ γ)
    (hγhi : γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * gap212Params.δ / 3 + 3 * slack)
    {y : Fin (7 + 4) → ℝ}
    (hy : y ∈ Xi (127 / 625 : ℝ) (917 / 5000) 7 4 (41 / 2500)) :
    AdmitsPartition₄ y (capD γ ω₀ 0) (capD γ ω₀ 1) (capD γ ω₀ 2) (capD γ ω₀ 3) :=
  admitsPartition₄_transpose_of (c := fun k ↦ capD γ ω₀ k) hy
    fun _ hz ↦ admitsPartition₄_cellFourSeven_band hωlo hωhi hγlo hγhi hz

end Gap212
