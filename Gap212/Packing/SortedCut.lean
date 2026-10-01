/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.SortedCone
public meta import Gap212.Attr

/-!
# The cut sorted cone, and the certificate that consumes both halves

`Gap212.Packing.SortedCone` bounds the mass a set of ranks carries by
`#S·δ + dens(S)·(B - mδ)`, and at some cells no single sorted assignment covers the whole
`γ`-range. This module supplies the instrument for those cells: a **cut** on the largest coordinate
of a group.

* `Gap212.Packing.sum_le_affine_sum_of_antitone` is the `Fin m` form of the affine prefix bound
  `Gap212.Packing.sum_mem_le_affine_of_antitone'` — a majorant `|S ∩ [0,j)| ≤ r·j + q` with `r` and
  `q` of *either* sign pays `r · ∑ x + q · x₀`.
* `Gap212.Packing.sum_image_le_of_ranks_affine` is the rank bound with that majorant: the block
  carries at most `#T·δ + r·(B - Nδ) + q·(y(e 0) - δ)`, where `e 0` is the group's largest
  coordinate.
* `Gap212.Packing.sum_image_le_of_ranks_cut_low` and `..._cut_high` pay the `q` term at a fixed
  threshold `t` instead: the first under `y i ≤ t` for every `i` of the group and `0 ≤ q`, the
  second under `t ≤ y i` for *some* `i` of the group and `q ≤ 0`. The sign of `q` reverses the
  comparison, so the two read identically.
* `Gap212.Packing.admitsPartition₄_of_rank_certificate_cut_low` and `..._cut_high` are the
  certificates: eight rank sets, eight prefix majorants, and one capacity check per bin, each half
  valid on its side of the cut.
* `Gap212.Packing.admitsPartition₄_of_cut` glues them: a case split on `le_or_gt` against the
  group's largest coordinate, so the conclusion is unconditional.

## Why the threshold is fixed first

`t` is a parameter of the *statement* of each half, quantified before `γ` and before the level
`ω₀`, and the glue lemma consumes the two halves at the same `t`. A statement reading
`∃ t, ∀ γ, …` would be useless to a consumer that must apply the cut at a `γ` it is given; the
order here is the one a consumer needs, and the certificates below fix `t = 1/25` as a numeral.

## What is cut

The cut is on the second group only, and that is not a loss at a diagonal cell: `Ξ` and
`Gap212.Packing.AdmitsPartition₄` are symmetric in the two groups, so at `m₁ = m₂` with equal caps
swapping the groups is a bijection of the whole problem and a first-group cut closes exactly what a
second-group cut closes. Off the diagonal the caps differ and the two are genuinely different
instruments; only the second is built here.
-/

@[expose] public section

namespace Gap212.Packing

open Finset

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ## The affine bound over `Fin m` -/

omit [IsStrictOrderedRing 𝕜] in
/-- The extension of a nonincreasing nonnegative `Fin m`-tuple by zero, together with the four
facts the `ℕ`-indexed prefix bounds are stated against. Factored out because the affine bound and
the `q = 0` bound of `Gap212.Packing.sum_le_mul_sum_of_antitone` both need it. -/
private theorem exists_extend_of_antitone {m : ℕ} (x : Fin m → 𝕜) (V : Finset (Fin m))
    (hx : ∀ i, 0 ≤ x i) (hanti : Antitone x) :
    ∃ x' : ℕ → 𝕜, (∀ i, 0 ≤ x' i) ∧ (∀ i j : ℕ, i ≤ j → x' j ≤ x' i) ∧
      (∀ i : Fin m, x' (i : ℕ) = x i) ∧
      (∑ j ∈ range m, if j ∈ V.map Fin.valEmbedding then x' j else 0) = ∑ i ∈ V, x i ∧
      (∑ j ∈ range m, x' j) = ∑ i, x i := by
  classical
  set x' : ℕ → 𝕜 := fun j ↦ if h : j < m then x ⟨j, h⟩ else 0 with hx'def
  have hx'nonneg : ∀ i, 0 ≤ x' i := by
    intro i; simp only [hx'def]; split_ifs with h
    · exact hx _
    · exact le_rfl
  have hx'anti : ∀ i j : ℕ, i ≤ j → x' j ≤ x' i := by
    intro i j hij
    simp only [hx'def]
    split_ifs with hj hi hi
    · exact hanti (show (⟨i, hi⟩ : Fin m) ≤ ⟨j, hj⟩ from hij)
    · exact absurd (lt_of_le_of_lt hij hj) hi
    · exact hx _
    · exact le_rfl
  have hval : ∀ i : Fin m, x' (i : ℕ) = x i := by
    intro i; simp only [hx'def, dif_pos i.isLt]
  refine ⟨x', hx'nonneg, hx'anti, hval, ?_, ?_⟩
  · rw [← Fin.sum_univ_eq_sum_range
      (fun j ↦ if j ∈ V.map Fin.valEmbedding then x' j else 0) m]
    have step : ∀ i : Fin m,
        (if (i : ℕ) ∈ V.map Fin.valEmbedding then x' (i : ℕ) else 0)
          = (if i ∈ V then x i else 0) := by
      intro i
      have hmem : ((i : ℕ) ∈ V.map Fin.valEmbedding) ↔ i ∈ V := by
        simp only [Finset.mem_map, Fin.valEmbedding_apply]
        exact ⟨fun ⟨a, ha, h⟩ ↦ by rwa [Fin.val_injective h] at ha, fun h ↦ ⟨i, h, rfl⟩⟩
      by_cases h : i ∈ V
      · rw [if_pos (hmem.2 h), if_pos h, hval]
      · rw [if_neg fun hh ↦ h (hmem.1 hh), if_neg h]
    rw [Finset.sum_congr rfl fun i _ ↦ step i, ← Finset.sum_filter]
    congr 1
    simp
  · rw [← Fin.sum_univ_eq_sum_range x' m]
    exact Finset.sum_congr rfl fun i _ ↦ hval i

/-- **The affine prefix bound, indexed by `Fin m`.**

For a nonincreasing nonnegative `x : Fin m → 𝕜` and a set `V` of positions whose prefix counts obey
`|{i ∈ V : i < j}| ≤ r·j + q` for `1 ≤ j ≤ m`, the mass on `V` is at most `r` times the total plus
`q` times the largest coordinate `x 0`. Neither `r` nor `q` need be nonnegative.

`0 < m` is load-bearing, and so is imposing the majorant only for `1 ≤ j`: at `m = 0` the claim
reads `0 ≤ q · x 0` and at `j = 0` the majorant reads `0 ≤ q`, either of which would rule the
negative-`q` case out by fiat. This is the `Fin m` form of
`Gap212.Packing.sum_mem_le_affine_of_antitone'` and the `q ≠ 0` companion of
`Gap212.Packing.sum_le_mul_sum_of_antitone`. -/
theorem sum_le_affine_sum_of_antitone {m : ℕ} (hm : 0 < m) (x : Fin m → 𝕜) (V : Finset (Fin m))
    (r q : 𝕜) (hx : ∀ i, 0 ≤ x i) (hanti : Antitone x)
    (hr : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      (((V.filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ r * j + q) :
    ∑ i ∈ V, x i ≤ r * (∑ i, x i) + q * x ⟨0, hm⟩ := by
  classical
  obtain ⟨x', h0, hanti', hval, e1, e2⟩ := exists_extend_of_antitone x V hx hanti
  have h := sum_mem_le_affine_of_antitone' (𝕜 := 𝕜) (n := m) hm x' (V.map Fin.valEmbedding) r q
    h0 hanti' fun j hj1 hj2 ↦ by
      rw [prefixCount_map_valEmbedding]; exact hr j hj1 hj2
  rw [e1, e2] at h
  have hzero : x' 0 = x ⟨0, hm⟩ := hval ⟨0, hm⟩
  rwa [hzero] at h

/-! ## The prefix majorant as a decidable check

With `r = p/d` and `q = a/d` the field inequality `|{i ∈ V : i < j}| ≤ r·j + q` is
`d·|{i ∈ V : i < j}| ≤ p·j + a` over `ℤ`, a bounded statement `decide` settles. The numerator of
`q` is an integer of either sign, which is why this is stated over `ℤ` and not over `ℕ` as
`Gap212.Packing.prefixDensity_of_nat` is. -/

/-- **The affine prefix check, reduced to a decidable statement about integers.** -/
theorem prefixAffine_of_int {N : ℕ} (V : Finset (Fin N)) (p a : ℤ) (d : ℕ) (hd : 0 < d)
    (h : ∀ j : ℕ, j ≤ N → 1 ≤ j →
      ((V.filter (fun i ↦ i.val < j)).card : ℤ) * (d : ℤ) ≤ p * j + a) :
    ∀ j : ℕ, 1 ≤ j → j ≤ N →
      (((V.filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜)
        ≤ ((p : 𝕜) / (d : 𝕜)) * j + (a : 𝕜) / (d : 𝕜) := by
  intro j hj1 hjN
  have hd' : (0 : 𝕜) < (d : 𝕜) := by exact_mod_cast hd
  rw [div_mul_eq_mul_div, ← add_div, le_div_iff₀ hd']
  exact_mod_cast h j hjN hj1

/-! ## The rank bound under a cut -/

/-- **The rank bound with an affine majorant.**

`G` is one group of a profile — every coordinate at least `δ`, total at most `B`, `N` of them,
enumerated in nonincreasing order by `e`. If the rank set `V` obeys `|V ∩ [0,j)| ≤ r·j + q` for
`1 ≤ j ≤ N`, the block carries at most `#V·δ + r·(B - Nδ) + q·(y(e 0) - δ)`.

The extra term is paid by the group's *largest* coordinate, which is what a cut controls. At
`q = 0` this is `Gap212.Packing.sum_image_le_of_ranks`. -/
@[gap212 "lem_rank_bound"]
theorem sum_image_le_of_ranks_affine {ι : Type*} [DecidableEq ι] {G : Finset ι} {y : ι → 𝕜}
    {δ B : 𝕜} {N : ℕ} (hN : 0 < N) (hδ : ∀ i ∈ G, δ ≤ y i) (hB : ∑ i ∈ G, y i ≤ B)
    {e : Fin N → ι} (he : Function.Injective e) (heG : Finset.image e Finset.univ = G)
    (hanti : Antitone fun j ↦ y (e j))
    (V : Finset (Fin N)) {r q : 𝕜} (hr0 : 0 ≤ r)
    (hr : ∀ j : ℕ, 1 ≤ j → j ≤ N →
      (((V.filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ r * j + q) :
    ∑ i ∈ V.image e, y i
      ≤ ((V.card : ℕ) : 𝕜) * δ + r * (B - (N : 𝕜) * δ) + q * (y (e ⟨0, hN⟩) - δ) := by
  classical
  have hmemG : ∀ j : Fin N, e j ∈ G := fun j ↦ by
    rw [← heG]; exact Finset.mem_image_of_mem e (Finset.mem_univ j)
  have hmain := sum_le_affine_sum_of_antitone hN (fun j ↦ y (e j) - δ) V r q
    (fun j ↦ sub_nonneg.2 (hδ _ (hmemG j))) (fun a b hab ↦ sub_le_sub_right (hanti hab) δ) hr
  have hsum : ∑ j : Fin N, y (e j) = ∑ i ∈ G, y i := by
    rw [← heG, Finset.sum_image (fun a _ b _ hab ↦ he hab)]
  have e2 : ∑ j : Fin N, (y (e j) - δ) ≤ B - (N : 𝕜) * δ := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hsum]
    linarith
  have e1 : ∑ i ∈ V, (y (e i) - δ) = (∑ i ∈ V.image e, y i) - ((V.card : ℕ) : 𝕜) * δ := by
    rw [Finset.sum_image (fun a _ b _ hab ↦ he hab), Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul]
  linarith [mul_le_mul_of_nonneg_left e2 hr0]

/-- **The low half of a cut, at the rank bound.** With every coordinate of the group at most `t`
and `0 ≤ q`, the `q` term costs `q · (t - δ)`. -/
theorem sum_image_le_of_ranks_cut_low {ι : Type*} [DecidableEq ι] {G : Finset ι} {y : ι → 𝕜}
    {δ B t : 𝕜} {N : ℕ} (hN : 0 < N) (hδ : ∀ i ∈ G, δ ≤ y i) (hB : ∑ i ∈ G, y i ≤ B)
    {e : Fin N → ι} (he : Function.Injective e) (heG : Finset.image e Finset.univ = G)
    (hanti : Antitone fun j ↦ y (e j))
    (V : Finset (Fin N)) {r q : 𝕜} (hr0 : 0 ≤ r) (hq : 0 ≤ q) (hcut : ∀ i ∈ G, y i ≤ t)
    (hr : ∀ j : ℕ, 1 ≤ j → j ≤ N →
      (((V.filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ r * j + q) :
    ∑ i ∈ V.image e, y i
      ≤ ((V.card : ℕ) : 𝕜) * δ + r * (B - (N : 𝕜) * δ) + q * (t - δ) := by
  have h := sum_image_le_of_ranks_affine hN hδ hB he heG hanti V hr0 hr
  have hle : y (e ⟨0, hN⟩) ≤ t := by
    refine hcut _ ?_
    rw [← heG]; exact Finset.mem_image_of_mem e (Finset.mem_univ _)
  have := mul_le_mul_of_nonneg_left (sub_le_sub_right hle δ) hq
  linarith

/-- **The high half of a cut, at the rank bound.** With *some* coordinate of the group at least `t`
and `q ≤ 0`, the `q` term costs `q · (t - δ)` again: the sign of `q` reverses the comparison, and
the group's largest coordinate is at least `t` as soon as one of them is. -/
theorem sum_image_le_of_ranks_cut_high {ι : Type*} [DecidableEq ι] {G : Finset ι} {y : ι → 𝕜}
    {δ B t : 𝕜} {N : ℕ} (hN : 0 < N) (hδ : ∀ i ∈ G, δ ≤ y i) (hB : ∑ i ∈ G, y i ≤ B)
    {e : Fin N → ι} (he : Function.Injective e) (heG : Finset.image e Finset.univ = G)
    (hanti : Antitone fun j ↦ y (e j))
    (V : Finset (Fin N)) {r q : 𝕜} (hr0 : 0 ≤ r) (hq : q ≤ 0) (hcut : ∃ i ∈ G, t ≤ y i)
    (hr : ∀ j : ℕ, 1 ≤ j → j ≤ N →
      (((V.filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ r * j + q) :
    ∑ i ∈ V.image e, y i
      ≤ ((V.card : ℕ) : 𝕜) * δ + r * (B - (N : 𝕜) * δ) + q * (t - δ) := by
  have h := sum_image_le_of_ranks_affine hN hδ hB he heG hanti V hr0 hr
  obtain ⟨i₀, hi₀, hti₀⟩ := hcut
  have hge : t ≤ y (e ⟨0, hN⟩) := by
    rw [← heG, Finset.mem_image] at hi₀
    obtain ⟨j, -, rfl⟩ := hi₀
    exact hti₀.trans (hanti (show (⟨0, hN⟩ : Fin N) ≤ j from Nat.zero_le _))
  have := mul_le_mul_of_nonpos_left (sub_le_sub_right hge δ) hq
  linarith

/-! ## The certificate, with the cut threaded through

`Gap212.Packing.admitsPartition₄_of_rank_certificate` is the `q = 0` case of the lemma below, and
allows an empty second group. The cut version needs `0 < m₂`, since the affine bound does. -/

/-- **The rank certificate at a *given* nonincreasing enumeration of the second group.**

Eight rank sets and their prefix majorants — the first group's by density `r k`, the second's
affine with slope `s k` and constant `q k` — discharge the four-block condition, the `q` term being
paid by the second group's largest coordinate `y (e₂ 0)`.

This is the form the two halves of a cut share: `e₂` is a parameter so that the halves can bound
`y (e₂ 0)` by the threshold from their own side. A caller with no cut wants
`Gap212.Packing.admitsPartition₄_of_rank_certificate` instead. -/
@[gap212 "lem_rank_certificate"]
theorem admitsPartition₄_of_rank_certificate_enum {m₁ m₂ : ℕ} (hm₂ : 0 < m₂) {B₁ B₂ δ : 𝕜}
    {y : Fin (m₁ + m₂) → 𝕜} (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) (hδ : 0 ≤ δ)
    {e₂ : Fin m₂ → Fin (m₁ + m₂)} (he₂ : Function.Injective e₂)
    (he₂G : Finset.image e₂ Finset.univ
      = Finset.univ.filter (fun i : Fin (m₁ + m₂) ↦ ¬ ((i : ℕ) < m₁)))
    (he₂anti : Antitone fun j ↦ y (e₂ j))
    (T : Fin 4 → Finset (Fin m₁)) (U : Fin 4 → Finset (Fin m₂))
    (hTcover : ∀ j, ∃ k, j ∈ T k) (hTdisj : ∀ k l, k ≠ l → Disjoint (T k) (T l))
    (hUcover : ∀ j, ∃ k, j ∈ U k) (hUdisj : ∀ k l, k ≠ l → Disjoint (U k) (U l))
    (r s q : Fin 4 → 𝕜) (hr0 : ∀ k, 0 ≤ r k) (hs0 : ∀ k, 0 ≤ s k)
    (hr : ∀ k, ∀ j : ℕ, ((((T k).filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ r k * j)
    (hs : ∀ k, ∀ j : ℕ, 1 ≤ j → j ≤ m₂ →
      ((((U k).filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ s k * j + q k)
    (c : Fin 4 → 𝕜)
    (hcap : ∀ k, ((((T k).card : ℕ) : 𝕜) * δ + r k * (B₁ - (m₁ : 𝕜) * δ))
        + ((((U k).card : ℕ) : 𝕜) * δ + s k * (B₂ - (m₂ : 𝕜) * δ)
          + q k * (y (e₂ ⟨0, hm₂⟩) - δ)) ≤ c k) :
    AdmitsPartition₄ y (c 0) (c 1) (c 2) (c 3) := by
  classical
  obtain ⟨hbox, hsum₁, hsum₂⟩ := hy
  have hy0 : ∀ i, 0 ≤ y i := fun i ↦ hδ.trans (hbox i).1
  set G₁ : Finset (Fin (m₁ + m₂)) := Finset.univ.filter (fun i ↦ (i : ℕ) < m₁) with hG₁
  set G₂ : Finset (Fin (m₁ + m₂)) := Finset.univ.filter (fun i ↦ ¬ ((i : ℕ) < m₁)) with hG₂
  have hGdisj : Disjoint G₁ G₂ := by
    rw [hG₁, hG₂]; exact Finset.disjoint_filter_filter_not _ _ _
  obtain ⟨e₁, he₁, he₁G, he₁anti⟩ := exists_antitone_enum G₁ y (card_lowGroup m₁ m₂)
  have hmem₁ : ∀ j, e₁ j ∈ G₁ := fun j ↦ by
    rw [← he₁G]; exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have hmem₂ : ∀ j, e₂ j ∈ G₂ := fun j ↦ by
    have hj : e₂ j ∈ Finset.image e₂ Finset.univ :=
      Finset.mem_image_of_mem _ (Finset.mem_univ j)
    rwa [he₂G] at hj
  set P : Fin 4 → Finset (Fin (m₁ + m₂)) :=
    fun k ↦ (T k).image e₁ ∪ (U k).image e₂ with hP
  have hsub₁ : ∀ V : Finset (Fin m₁), V.image e₁ ⊆ G₁ := by
    intro V i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi
    exact hmem₁ j
  have hsub₂ : ∀ V : Finset (Fin m₂), V.image e₂ ⊆ G₂ := by
    intro V i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi
    exact hmem₂ j
  have hmass : ∀ k, ∑ i ∈ P k, y i ≤ c k := by
    intro k
    have hdisjk : Disjoint ((T k).image e₁) ((U k).image e₂) :=
      Finset.disjoint_of_subset_left (hsub₁ _) (Finset.disjoint_of_subset_right (hsub₂ _) hGdisj)
    rw [hP, Finset.sum_union hdisjk]
    have b₁ := sum_image_le_of_ranks (G := G₁) (y := y) (δ := δ) (B := B₁)
      (fun i hi ↦ (hbox i).1) (by rw [hG₁]; exact hsum₁) he₁ he₁G he₁anti (T k) (hr0 k) (hr k)
    have b₂ := sum_image_le_of_ranks_affine (G := G₂) (y := y) (δ := δ) (B := B₂) hm₂
      (fun i hi ↦ (hbox i).1) hsum₂ he₂ he₂G he₂anti (U k) (hs0 k) (hs k)
    exact le_trans (add_le_add b₁ b₂) (hcap k)
  have hPdisj : ∀ k l, k ≠ l → Disjoint (P k) (P l) := by
    intro k l hkl
    rw [hP]
    refine Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2 ⟨?_, ?_⟩,
      Finset.disjoint_union_right.2 ⟨?_, ?_⟩⟩
    · rw [Finset.disjoint_image he₁]; exact hTdisj k l hkl
    · exact Finset.disjoint_of_subset_left (hsub₁ _)
        (Finset.disjoint_of_subset_right (hsub₂ _) hGdisj)
    · exact Finset.disjoint_of_subset_left (hsub₂ _)
        (Finset.disjoint_of_subset_right (hsub₁ _) hGdisj.symm)
    · rw [Finset.disjoint_image he₂]; exact hUdisj k l hkl
  have hcover : ∀ i, ∃ k, i ∈ P k := by
    intro i
    by_cases hi : (i : ℕ) < m₁
    · have hiG : i ∈ G₁ := by rw [hG₁]; simp [hi]
      rw [← he₁G, Finset.mem_image] at hiG
      obtain ⟨j, -, rfl⟩ := hiG
      obtain ⟨k, hk⟩ := hTcover j
      exact ⟨k, by rw [hP]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hk)⟩
    · have hiG : i ∈ Finset.image e₂ Finset.univ := by
        rw [he₂G]; exact Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩
      rw [Finset.mem_image] at hiG
      obtain ⟨j, -, rfl⟩ := hiG
      obtain ⟨k, hk⟩ := hUcover j
      exact ⟨k, by rw [hP]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)⟩
  refine ⟨P 0, P 1, P 2, hPdisj 0 1 (by decide), hPdisj 0 2 (by decide),
    hPdisj 1 2 (by decide), hmass 0, hmass 1, hmass 2, ?_⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ ↦ hy0 i) (hmass 3)
  intro i hi
  rw [Finset.mem_sdiff] at hi
  obtain ⟨k, hk⟩ := hcover i
  have h012 : i ∉ P 0 ∧ i ∉ P 1 ∧ i ∉ P 2 := by
    refine ⟨fun h ↦ hi.2 ?_, fun h ↦ hi.2 ?_, fun h ↦ hi.2 ?_⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
    · exact Finset.mem_union_right _ h
  match k with
  | 0 => exact absurd hk h012.1
  | 1 => exact absurd hk h012.2.1
  | 2 => exact absurd hk h012.2.2
  | 3 => exact hk

/-- **The rank certificate on the low half of a cut**: every coordinate of the second group at most
`t`, and `0 ≤ q k` for every bin, so the `q` term of each capacity check is paid at `t`. -/
@[gap212 "lem_rank_certificate"]
theorem admitsPartition₄_of_rank_certificate_cut_low {m₁ m₂ : ℕ} (hm₂ : 0 < m₂) {B₁ B₂ δ t : 𝕜}
    {y : Fin (m₁ + m₂) → 𝕜} (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) (hδ : 0 ≤ δ)
    (hcut : ∀ i : Fin (m₁ + m₂), m₁ ≤ (i : ℕ) → y i ≤ t)
    (T : Fin 4 → Finset (Fin m₁)) (U : Fin 4 → Finset (Fin m₂))
    (hTcover : ∀ j, ∃ k, j ∈ T k) (hTdisj : ∀ k l, k ≠ l → Disjoint (T k) (T l))
    (hUcover : ∀ j, ∃ k, j ∈ U k) (hUdisj : ∀ k l, k ≠ l → Disjoint (U k) (U l))
    (r s q : Fin 4 → 𝕜) (hr0 : ∀ k, 0 ≤ r k) (hs0 : ∀ k, 0 ≤ s k) (hq0 : ∀ k, 0 ≤ q k)
    (hr : ∀ k, ∀ j : ℕ, ((((T k).filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ r k * j)
    (hs : ∀ k, ∀ j : ℕ, 1 ≤ j → j ≤ m₂ →
      ((((U k).filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ s k * j + q k)
    (c : Fin 4 → 𝕜)
    (hcap : ∀ k, ((((T k).card : ℕ) : 𝕜) * δ + r k * (B₁ - (m₁ : 𝕜) * δ))
        + ((((U k).card : ℕ) : 𝕜) * δ + s k * (B₂ - (m₂ : 𝕜) * δ) + q k * (t - δ)) ≤ c k) :
    AdmitsPartition₄ y (c 0) (c 1) (c 2) (c 3) := by
  classical
  obtain ⟨e₂, he₂, he₂G, he₂anti⟩ :=
    exists_antitone_enum (Finset.univ.filter (fun i : Fin (m₁ + m₂) ↦ ¬ ((i : ℕ) < m₁))) y
      (card_highGroup m₁ m₂)
  have hmem : e₂ ⟨0, hm₂⟩ ∈ Finset.univ.filter (fun i : Fin (m₁ + m₂) ↦ ¬ ((i : ℕ) < m₁)) := by
    rw [← he₂G]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hle : y (e₂ ⟨0, hm₂⟩) ≤ t :=
    hcut _ (not_lt.1 (Finset.mem_filter.1 hmem).2)
  refine admitsPartition₄_of_rank_certificate_enum hm₂ hy hδ he₂ he₂G he₂anti T U hTcover hTdisj
    hUcover hUdisj r s q hr0 hs0 hr hs c fun k ↦ ?_
  have hqle := mul_le_mul_of_nonneg_left (sub_le_sub_right hle δ) (hq0 k)
  linarith [hcap k]

/-- **The rank certificate on the high half of a cut**: some coordinate of the second group at
least `t`, and `q k ≤ 0` for every bin, so the `q` term of each capacity check is again paid at
`t`. -/
@[gap212 "lem_rank_certificate"]
theorem admitsPartition₄_of_rank_certificate_cut_high {m₁ m₂ : ℕ} (hm₂ : 0 < m₂) {B₁ B₂ δ t : 𝕜}
    {y : Fin (m₁ + m₂) → 𝕜} (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) (hδ : 0 ≤ δ)
    (hcut : ∃ i : Fin (m₁ + m₂), m₁ ≤ (i : ℕ) ∧ t ≤ y i)
    (T : Fin 4 → Finset (Fin m₁)) (U : Fin 4 → Finset (Fin m₂))
    (hTcover : ∀ j, ∃ k, j ∈ T k) (hTdisj : ∀ k l, k ≠ l → Disjoint (T k) (T l))
    (hUcover : ∀ j, ∃ k, j ∈ U k) (hUdisj : ∀ k l, k ≠ l → Disjoint (U k) (U l))
    (r s q : Fin 4 → 𝕜) (hr0 : ∀ k, 0 ≤ r k) (hs0 : ∀ k, 0 ≤ s k) (hq0 : ∀ k, q k ≤ 0)
    (hr : ∀ k, ∀ j : ℕ, ((((T k).filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ r k * j)
    (hs : ∀ k, ∀ j : ℕ, 1 ≤ j → j ≤ m₂ →
      ((((U k).filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ s k * j + q k)
    (c : Fin 4 → 𝕜)
    (hcap : ∀ k, ((((T k).card : ℕ) : 𝕜) * δ + r k * (B₁ - (m₁ : 𝕜) * δ))
        + ((((U k).card : ℕ) : 𝕜) * δ + s k * (B₂ - (m₂ : 𝕜) * δ) + q k * (t - δ)) ≤ c k) :
    AdmitsPartition₄ y (c 0) (c 1) (c 2) (c 3) := by
  classical
  obtain ⟨e₂, he₂, he₂G, he₂anti⟩ :=
    exists_antitone_enum (Finset.univ.filter (fun i : Fin (m₁ + m₂) ↦ ¬ ((i : ℕ) < m₁))) y
      (card_highGroup m₁ m₂)
  obtain ⟨i₀, hi₀, hti₀⟩ := hcut
  have hge : t ≤ y (e₂ ⟨0, hm₂⟩) := by
    have hmem : i₀ ∈ Finset.image e₂ Finset.univ := by
      rw [he₂G]; exact Finset.mem_filter.2 ⟨Finset.mem_univ i₀, not_lt.2 hi₀⟩
    rw [Finset.mem_image] at hmem
    obtain ⟨j, -, rfl⟩ := hmem
    exact hti₀.trans (he₂anti (show (⟨0, hm₂⟩ : Fin m₂) ≤ j from Nat.zero_le _))
  refine admitsPartition₄_of_rank_certificate_enum hm₂ hy hδ he₂ he₂G he₂anti T U hTcover hTdisj
    hUcover hUdisj r s q hr0 hs0 hr hs c fun k ↦ ?_
  have hqle := mul_le_mul_of_nonpos_left (sub_le_sub_right hge δ) (hq0 k)
  linarith [hcap k]

/-! ## The glue

The two halves are the two sides of one comparison, so the disjunction is `le_or_gt` against the
second group's largest coordinate and nothing more. The threshold is the same `t` on both sides,
fixed before this lemma is applied. -/

omit [IsStrictOrderedRing 𝕜] in
/-- **A cut discharges the four-block condition unconditionally.**

Given the low half — valid when every coordinate of the second group is at most `t` — and the high
half — valid when some coordinate of the second group is at least `t` — the condition holds with no
hypothesis on the profile at all: take the largest coordinate of the second group and compare it
with `t`.

The second group must be nonempty, since otherwise neither half is about anything. -/
@[gap212 "lem_rank_certificate"]
theorem admitsPartition₄_of_cut {m₁ m₂ : ℕ} (hm₂ : 0 < m₂) {t : 𝕜} {y : Fin (m₁ + m₂) → 𝕜}
    {b₁ b₂ b₃ b₄ : 𝕜}
    (hlow : (∀ i : Fin (m₁ + m₂), m₁ ≤ (i : ℕ) → y i ≤ t) → AdmitsPartition₄ y b₁ b₂ b₃ b₄)
    (hhigh : (∃ i : Fin (m₁ + m₂), m₁ ≤ (i : ℕ) ∧ t ≤ y i) → AdmitsPartition₄ y b₁ b₂ b₃ b₄) :
    AdmitsPartition₄ y b₁ b₂ b₃ b₄ := by
  classical
  have hne : (Finset.univ.filter (fun i : Fin (m₁ + m₂) ↦ m₁ ≤ (i : ℕ))).Nonempty :=
    ⟨⟨m₁, by omega⟩, by simp⟩
  obtain ⟨i₀, hi₀, hmax⟩ :=
    (Finset.univ.filter (fun i : Fin (m₁ + m₂) ↦ m₁ ≤ (i : ℕ))).exists_max_image y hne
  rcases le_or_gt (y i₀) t with h | h
  · exact hlow fun i hi ↦ (hmax i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)).trans h
  · exact hhigh ⟨i₀, (Finset.mem_filter.1 hi₀).2, h.le⟩

end Gap212.Packing
