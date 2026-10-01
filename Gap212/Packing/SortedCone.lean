/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.Basic
public import Mathlib.Data.Fin.Tuple.Sort
public meta import Gap212.Attr

/-!
# The sorted cone, and block bounds by rank

The four-block conditions of Proposition 3 ask that every profile in the check set `Ξ` admit a
partition meeting the capacities. The arguments for `Gap212.conditionD_at_datum_low_level` and
its six companion bands build the partition from mass counts alone:
`Gap212.Packing.exists_small_coords` bounds the `(n+1)`-st smallest coordinate without sorting.
Such a reading only ever knows a coordinate to lie below a threshold, never that it is *the* `k`-th
largest, and that limits its reach.

This module supplies the sorted reading. Two facts:

* `Gap212.Packing.sum_mem_le_mul_sum_of_antitone`: for a nonincreasing nonnegative sequence, the
  mass carried by a set `S` of positions is at most `r` times the total, where `r` is any bound on
  the *prefix density* of `S` — `|S ∩ [0,j)| ≤ r·j` for every `j`. This is the sharp statement:
  with `r` the maximum prefix density it is an equality, attained on the profile that is flat down
  to the position realizing the maximum and at the floor below it. Only `≤` is used, and only `≤`
  is proved.
* `Gap212.Packing.exists_antitone_enum`: every finset can be enumerated so that a given weight is
  nonincreasing along it, by `Tuple.sort` applied to the negated weight.

Together these bound the mass at a set of *ranks*, which is what a certificate needs: a bin holding
ranks `S` of a group of `m` coordinates, each at least `δ` and summing to at most `B`, carries at
most `|S|·δ + r·(B - m·δ)`. That bound is strictly stronger than anything the sort-free reading can
give. For instance, at `m = 10`, `B = 1081/5000`, `δ = 41/2500` the sort-free bound on a single
coordinate is `B - 9δ = 343/5000` at *every* position, while the rank bound at position `i` is
`δ + (B - 10δ)/i`, which is `1081/50000` at `i = 10` — smaller by a factor of more than three.

## Why this is not a weakening

The reduction to the sorted cone costs nothing: `Ξ` is invariant under permuting coordinates within
either group, and `AdmitsPartition₄` transports along a permutation by carrying the three blocks
along with it. So a partition found for the sorted reindexing is a partition of the original tuple.
`Gap212.Packing.admitsPartition₄_of_comp_perm` is that transport.
-/

@[expose] public section

namespace Gap212.Packing

open Finset

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ## Prefix density bounds the mass of a rank set -/

/-- **The prefix count of a set of positions**: how many elements of `S` lie below `n`. The bound
a caller must supply is on this, divided by `n` — the *prefix density* of `S`. -/
@[gap212 "def_rank_bound"]
def prefixCount (S : Finset ℕ) (n : ℕ) : ℕ := ((range n).filter (· ∈ S)).card

/-- `prefixCount S 0 = 0`: no element of `S` lies below `0`. -/
@[simp] theorem prefixCount_zero (S : Finset ℕ) : prefixCount S 0 = 0 := by
  simp [prefixCount]

/-- `prefixCount S (n + 1)` is `prefixCount S n`, plus `1` if `n ∈ S`. -/
theorem prefixCount_succ (S : Finset ℕ) (n : ℕ) :
    prefixCount S (n + 1) = prefixCount S n + (if n ∈ S then 1 else 0) := by
  unfold prefixCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs <;> simp

/-! ### The telescoping identities

The affine prefix bound is proved from two telescoping identities, in which no sign enters: every
step is an identity, and the two inequalities used are termwise against `x k - x (k+1) ≥ 0` and
`x n ≥ 0`. So the bound needs no sign condition on `q`, which is what a cut certificate consumes:
the upper half `x 0 ≤ T` of a cut uses `q ≥ 0`, and the lower half `x 0 ≥ T` uses `q ≤ 0`. -/

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem sum_mem_eq_telescope (x : ℕ → 𝕜) (S : Finset ℕ) (n : ℕ) :
    (∑ i ∈ range n, if i ∈ S then x i else 0)
      = (∑ k ∈ range n, ((prefixCount S (k + 1) : ℕ) : 𝕜) * (x k - x (k + 1)))
        + ((prefixCount S n : ℕ) : 𝕜) * x n := by
  induction n with
  | zero => simp [prefixCount]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, prefixCount_succ]
    split_ifs <;> push_cast <;> ring

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem sum_eq_telescope (x : ℕ → 𝕜) (n : ℕ) :
    (∑ i ∈ range n, x i)
      = (∑ k ∈ range n, ((k + 1 : ℕ) : 𝕜) * (x k - x (k + 1))) + (n : 𝕜) * x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    push_cast
    ring

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem sum_telescope_diff (x : ℕ → 𝕜) (n : ℕ) :
    (∑ k ∈ range n, (x k - x (k + 1))) = x 0 - x n :=
  Finset.sum_range_sub' x n

/-- **The affine prefix bound, with no sign condition on either coefficient.**

If `|S ∩ [0,j)| ≤ r·j + q` for every `j` with `1 ≤ j ≤ n`, then

    ∑_{i ∈ S, i < n} x i  ≤  r · ∑_{i < n} x i  +  q · x 0 .

Neither `r` nor `q` need be nonnegative. This is the form both halves of a cut consume: the half
`x 0 ≤ T` uses `q ≥ 0`, paying `q·T`; the half `x 0 ≥ T` uses `q ≤ 0`, paying `q·T` again because
`q·x 0 ≤ q·T` when `q` is negative and `x 0 ≥ T`. The two are one statement.

`1 ≤ n` is needed and is not cosmetic: at `n = 0` the claim reads `0 ≤ q · x 0`, which is false for
negative `q`. The hypothesis is only imposed for `1 ≤ j`, since requiring it at `j = 0` would read
`0 ≤ q` and rule the negative case out by fiat. -/
theorem sum_mem_le_affine_of_antitone' {n : ℕ} (hn : 1 ≤ n) (x : ℕ → 𝕜) (S : Finset ℕ) (r q : 𝕜)
    (hx : ∀ i, 0 ≤ x i) (hanti : ∀ i j, i ≤ j → x j ≤ x i)
    (hr : ∀ j, 1 ≤ j → j ≤ n → ((prefixCount S j : ℕ) : 𝕜) ≤ r * j + q) :
    (∑ i ∈ range n, if i ∈ S then x i else 0) ≤ r * (∑ i ∈ range n, x i) + q * x 0 := by
  have hterm := Finset.sum_le_sum fun k hk ↦ mul_le_mul_of_nonneg_right
    (hr (k + 1) (Nat.le_add_left 1 k) (Finset.mem_range.1 hk))
    (sub_nonneg.2 (hanti k (k + 1) k.le_succ))
  have hsplit : (∑ k ∈ range n, (r * ((k + 1 : ℕ) : 𝕜) + q) * (x k - x (k + 1)))
      = r * (∑ k ∈ range n, ((k + 1 : ℕ) : 𝕜) * (x k - x (k + 1))) + q * (x 0 - x n) := by
    rw [← sum_telescope_diff x n, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [sum_mem_eq_telescope x S n, sum_eq_telescope x n]
  linarith [mul_le_mul_of_nonneg_right (hr n hn le_rfl) (hx n)]

/-- **A set of positions carries at most its affine prefix majorant.**

Let `x` be nonnegative and nonincreasing, and let `S` be a set of positions whose prefix counts
obey `|S ∩ [0,j)| ≤ r·j + q` for every `j`. Then the mass `x` puts on `S` within `[0,n)` is at most
`r` times the mass on all of `[0,n)` plus `q` times the *largest* coordinate.

Asking the hypothesis at `j = 0` reads `0 ≤ q`, so this form is the nonnegative-`q` one; it is the
`Gap212.Packing.sum_mem_le_affine_of_antitone'` case with that hypothesis, which is also what makes
`n = 0` harmless here.

This is the instrument for a **cut** sorted cone. Without a cut only `q = 0` is useful, since `x 0`
is bounded only by the total; with a cut `x 0 ≤ t` the `q` term costs `q·t`, and for a set of deep
ranks the least admissible `(r, q)` trades a much smaller `r` for a little `q`. -/
theorem sum_mem_le_affine_of_antitone {n : ℕ} (x : ℕ → 𝕜) (S : Finset ℕ) (r q : 𝕜)
    (hx : ∀ i, 0 ≤ x i) (hanti : ∀ i j, i ≤ j → x j ≤ x i)
    (hr : ∀ j : ℕ, ((prefixCount S j : ℕ) : 𝕜) ≤ r * j + q) :
    (∑ i ∈ range n, if i ∈ S then x i else 0) ≤ r * (∑ i ∈ range n, x i) + q * x 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using mul_nonneg (by simpa using hr 0) (hx 0)
  · exact sum_mem_le_affine_of_antitone' hn x S r q hx hanti fun j _ _ ↦ hr j

/-! ### The two halves of a cut

A cut on the largest coordinate splits the sorted cone into `x 0 ≤ T` and `x 0 ≥ T`, and both
halves consume the affine bound with the `q` term paid at `T`. They differ only in the sign of `q`:
on the low half `q ≥ 0` and `q · x 0 ≤ q · T` because `x 0 ≤ T`; on the high half `q ≤ 0` and the
same inequality holds because `x 0 ≥ T` reverses. That is why there is one lemma and not two. -/

/-- **The low half of a cut**: with `x 0 ≤ T` and `0 ≤ q`, the `q` term costs `q · T`. -/
theorem sum_mem_le_affine_of_le_top {n : ℕ} (hn : 1 ≤ n) (x : ℕ → 𝕜) (S : Finset ℕ) (r q T : 𝕜)
    (hx : ∀ i, 0 ≤ x i) (hanti : ∀ i j, i ≤ j → x j ≤ x i) (hq : 0 ≤ q) (hT : x 0 ≤ T)
    (hr : ∀ j, 1 ≤ j → j ≤ n → ((prefixCount S j : ℕ) : 𝕜) ≤ r * j + q) :
    (∑ i ∈ range n, if i ∈ S then x i else 0) ≤ r * (∑ i ∈ range n, x i) + q * T :=
  (sum_mem_le_affine_of_antitone' hn x S r q hx hanti hr).trans
    (by linarith [mul_le_mul_of_nonneg_left hT hq])

/-- **The high half of a cut**: with `T ≤ x 0` and `q ≤ 0`, the `q` term costs `q · T` again — the
sign of `q` reverses the comparison, so the two halves read identically. -/
theorem sum_mem_le_affine_of_top_le {n : ℕ} (hn : 1 ≤ n) (x : ℕ → 𝕜) (S : Finset ℕ) (r q T : 𝕜)
    (hx : ∀ i, 0 ≤ x i) (hanti : ∀ i j, i ≤ j → x j ≤ x i) (hq : q ≤ 0) (hT : T ≤ x 0)
    (hr : ∀ j, 1 ≤ j → j ≤ n → ((prefixCount S j : ℕ) : 𝕜) ≤ r * j + q) :
    (∑ i ∈ range n, if i ∈ S then x i else 0) ≤ r * (∑ i ∈ range n, x i) + q * T :=
  (sum_mem_le_affine_of_antitone' hn x S r q hx hanti hr).trans
    (by linarith [mul_le_mul_of_nonpos_left hT hq])

/-- **A set of positions carries at most its prefix density times the total.**

The `q = 0` case of `Gap212.Packing.sum_mem_le_affine_of_antitone`, and the one every
certificate here uses: `|S ∩ [0,j)| ≤ r·j` for every `j` gives `∑_S x ≤ r · ∑ x`.

The hypothesis is needed for every `j`, not only `j ≤ n`; a caller with `S ⊆ range n` and `0 ≤ r`
gets the rest from the case `j = n`. -/
theorem sum_mem_le_mul_sum_of_antitone {n : ℕ} (x : ℕ → 𝕜) (S : Finset ℕ) (r : 𝕜)
    (hx : ∀ i, 0 ≤ x i) (hanti : ∀ i j, i ≤ j → x j ≤ x i)
    (hr : ∀ j : ℕ, ((prefixCount S j : ℕ) : 𝕜) ≤ r * j) :
    (∑ i ∈ range n, if i ∈ S then x i else 0) ≤ r * ∑ i ∈ range n, x i := by
  simpa using sum_mem_le_affine_of_antitone (n := n) x S r 0 hx hanti (by simpa using hr)

/-- The prefix count of a `Finset (Fin m)` pushed to `ℕ` counts its elements below `j`. -/
theorem prefixCount_map_valEmbedding {m : ℕ} (T : Finset (Fin m)) (j : ℕ) :
    prefixCount (T.map Fin.valEmbedding) j = (T.filter (fun i ↦ i.val < j)).card := by
  rw [prefixCount, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Fin.valEmbedding_apply]
  grind

/-- **The rank-mass bound, indexed by `Fin m`.**

For a nonincreasing nonnegative `x : Fin m → 𝕜` and a set `T` of positions whose prefix counts
obey `|{i ∈ T : i < j}| ≤ r·j` for every `j`, the mass on `T` is at most `r` times the total. This
is the form a certificate uses: `T` is the set of ranks a bin receives, and `r` its prefix
density. -/
theorem sum_le_mul_sum_of_antitone {m : ℕ} (x : Fin m → 𝕜) (T : Finset (Fin m)) (r : 𝕜)
    (hx : ∀ i, 0 ≤ x i) (hanti : Antitone x)
    (hr : ∀ j : ℕ, (((T.filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ r * j) :
    ∑ i ∈ T, x i ≤ r * ∑ i, x i := by
  classical
  set x' : ℕ → 𝕜 := fun j ↦ if h : j < m then x ⟨j, h⟩ else 0
  have hval : ∀ i : Fin m, x' i = x i := fun i ↦ dif_pos i.isLt
  have hmain := sum_mem_le_mul_sum_of_antitone (n := m) x' (T.map Fin.valEmbedding) r
    (fun i ↦ by unfold x'; split_ifs; exacts [hx _, le_rfl])
    (fun i j hij ↦ by
      unfold x'
      split_ifs with hj hi hi
      exacts [hanti (show (⟨i, hi⟩ : Fin m) ≤ ⟨j, hj⟩ from hij), absurd (hij.trans_lt hj) hi,
        hx _, le_rfl])
    fun j ↦ by rw [prefixCount_map_valEmbedding]; exact hr j
  have hsub : T.map Fin.valEmbedding ⊆ range m := fun j hj ↦ by
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_range.mpr i.isLt
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub, Finset.sum_map,
    ← Fin.sum_univ_eq_sum_range] at hmain
  simpa only [Fin.valEmbedding_apply, hval] using hmain

/-- **The prefix-density hypothesis only has to be checked up to `N`.** Above `N` the filter is all
of `T`, so the count stops growing while `r·j` does not. This is what makes the hypothesis of
`Gap212.Packing.sum_le_mul_sum_of_antitone` a finite check for a concrete rank set. -/
theorem prefixDensity_of_le {N : ℕ} (T : Finset (Fin N)) (r : 𝕜) (hr0 : 0 ≤ r)
    (h : ∀ j, j ≤ N → (((T.filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ r * j) :
    ∀ j : ℕ, (((T.filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ r * j := by
  intro j
  rcases le_or_gt j N with hj | hj
  · exact h j hj
  · have hfil : T.filter (fun i ↦ i.val < j) = T.filter (fun i ↦ i.val < N) :=
      Finset.filter_congr fun i _ ↦ iff_of_true (i.isLt.trans hj) i.isLt
    rw [hfil]
    exact (h N le_rfl).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hj.le) hr0)

/-- **The prefix-density check, reduced to a decidable statement about naturals.**

With `r = p/q` the field inequality `|{i ∈ T : i < j}| ≤ r·j` is `q·|{i ∈ T : i < j}| ≤ p·j`, a
bounded statement about naturals that `decide` settles. Combined with
`Gap212.Packing.prefixDensity_of_le` this turns the hypothesis of the rank certificate into one
`decide` per bin. -/
theorem prefixDensity_of_nat {N : ℕ} (T : Finset (Fin N)) (p q : ℕ) (hq : 0 < q)
    (h : ∀ j, j ≤ N → q * (T.filter (fun i ↦ i.val < j)).card ≤ p * j) :
    ∀ j : ℕ, (((T.filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ ((p : 𝕜) / (q : 𝕜)) * j := by
  refine prefixDensity_of_le T _ (by positivity) fun j hj ↦ ?_
  rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast hq), mul_comm]
  exact_mod_cast h j hj

/-! ## Enumerating a group in nonincreasing order -/

/-- **Every finset can be enumerated so that a given weight is nonincreasing along it.**

`Tuple.sort` applied to the negated weight. This is the whole content of "reduce to the sorted
cone": the enumeration is a bijection onto `G`, so the blocks built from ranks are blocks of `G`,
and no coordinate leaves the group. -/
theorem exists_antitone_enum {ι : Type*} [DecidableEq ι] (G : Finset ι) (y : ι → 𝕜) {N : ℕ}
    (hN : G.card = N) :
    ∃ e : Fin N → ι, Function.Injective e ∧ Finset.image e Finset.univ = G ∧
      Antitone fun j ↦ y (e j) := by
  classical
  set e₀ : Fin N ≃ ↥G := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hN])).symm
  set σ : Equiv.Perm (Fin N) := Tuple.sort fun j ↦ -(y ((e₀ j) : ι))
  have hinj : Function.Injective fun j ↦ ((e₀ (σ j) : ↥G) : ι) := fun a b hab ↦
    σ.injective (e₀.injective (Subtype.ext hab))
  refine ⟨_, hinj, Finset.eq_of_subset_of_card_le ?_ ?_, fun a b hab ↦ by
    simpa using Tuple.monotone_sort (fun j ↦ -(y ((e₀ j) : ι))) hab⟩
  · exact Finset.image_subset_iff.mpr fun j _ ↦ (e₀ (σ j)).2
  · rw [hN, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- **The rank bound on a block of one group.**

`G` is one group of a profile: every coordinate at least `δ`, total mass at most `B`, and `N` of
them. `T` is the set of ranks — positions in nonincreasing order of mass — that one bin receives,
and `r` a bound on `T`'s prefix density. Then that bin carries at most `|T|·δ + r·(B - N·δ)`.

This is the instrument the sort-free reading cannot supply. Taking `T = {j}` a single rank, the
bound is `δ + r·(B - N·δ)` with `r = 1/(j+1)`, whereas the sort-free bound is `B - (N-1)·δ` at
every position. -/
@[gap212 "lem_rank_bound"]
theorem sum_image_le_of_ranks {ι : Type*} [DecidableEq ι] {G : Finset ι} {y : ι → 𝕜} {δ B : 𝕜}
    {N : ℕ} (hδ : ∀ i ∈ G, δ ≤ y i) (hB : ∑ i ∈ G, y i ≤ B)
    {e : Fin N → ι} (he : Function.Injective e) (heG : Finset.image e Finset.univ = G)
    (hanti : Antitone fun j ↦ y (e j))
    (T : Finset (Fin N)) {r : 𝕜} (hr0 : 0 ≤ r)
    (hr : ∀ j : ℕ, (((T.filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ r * j) :
    ∑ i ∈ T.image e, y i ≤ ((T.card : ℕ) : 𝕜) * δ + r * (B - (N : 𝕜) * δ) := by
  classical
  have hmemG : ∀ j, e j ∈ G := fun j ↦ heG ▸ Finset.mem_image_of_mem e (Finset.mem_univ j)
  set x : Fin N → 𝕜 := fun j ↦ y (e j) - δ
  have hxtot : ∑ j, x j = ∑ i ∈ G, y i - N * δ := by
    simp [x, Finset.sum_sub_distrib, ← heG, Finset.sum_image fun a _ b _ hab ↦ he hab]
  have hblock := (sum_le_mul_sum_of_antitone x T r (fun j ↦ sub_nonneg.2 (hδ _ (hmemG j)))
    (fun a b hab ↦ sub_le_sub_right (hanti hab) δ) hr).trans
    (mul_le_mul_of_nonneg_left (hxtot.trans_le (sub_le_sub_right hB _)) hr0)
  simp only [x, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hblock
  rw [Finset.sum_image fun a _ b _ hab ↦ he hab]
  linarith

/-! ## Transport along a permutation

`Ξ` is invariant under permuting coordinates within a group, and `AdmitsPartition₄` transports
along any permutation of the whole index type by carrying the three named blocks along with it.
Together these are what licenses reducing to a sorted profile: sorting is a permutation, and it
stays inside `Ξ` only when it does not move a coordinate between the two groups — which is why the
sorted reading below is applied to each group separately, never to the pooled tuple. -/

omit [IsStrictOrderedRing 𝕜] in
/-- **`AdmitsPartition₄` transports along a permutation.** If the reindexed tuple `y ∘ σ` admits a
partition meeting the capacities, so does `y`: push the three blocks forward along `σ`. -/
@[gap212 "lem_rank_bound"]
theorem admitsPartition₄_of_comp_perm {ℓ : ℕ} (y : Fin ℓ → 𝕜) (σ : Equiv.Perm (Fin ℓ))
    {b₁ b₂ b₃ b₄ : 𝕜} (h : AdmitsPartition₄ (y ∘ σ) b₁ b₂ b₃ b₄) :
    AdmitsPartition₄ y b₁ b₂ b₃ b₄ := by
  classical
  obtain ⟨I, J, K, hIJ, hIK, hJK, h1, h2, h3, h4⟩ := h
  have hsum : ∀ X : Finset (Fin ℓ), ∑ i ∈ X.map σ.toEmbedding, y i = ∑ i ∈ X, (y ∘ σ) i :=
    fun X ↦ Finset.sum_map _ _ _
  refine ⟨I.map σ.toEmbedding, J.map σ.toEmbedding, K.map σ.toEmbedding,
    Finset.disjoint_map _ |>.2 hIJ, Finset.disjoint_map _ |>.2 hIK,
    Finset.disjoint_map _ |>.2 hJK, (hsum I).trans_le h1, (hsum J).trans_le h2,
    (hsum K).trans_le h3, ?_⟩
  rwa [← Finset.map_union, ← Finset.map_union, ← Finset.map_univ_equiv σ, ← Finset.map_sdiff,
    hsum]

/-! ## The two groups, and the certificate that assembles them

`Ξ` caps the first `m₁` coordinates by `B₁` and the last `m₂` by `B₂`. The two groups are sorted
*separately* — a permutation mixing them would leave `Ξ`. So a certificate is eight rank sets: four
for each group, one per bin, each side partitioning its own positions.
-/

/-- The first group's index set inside `Fin (m₁ + m₂)`, and its size. -/
theorem card_lowGroup (m₁ m₂ : ℕ) :
    ((Finset.univ : Finset (Fin (m₁ + m₂))).filter (fun i ↦ i.val < m₁)).card = m₁ := by
  simp [Fin.card_filter_val_lt]

/-- The second group's size, by complementation. -/
theorem card_highGroup (m₁ m₂ : ℕ) :
    ((Finset.univ : Finset (Fin (m₁ + m₂))).filter (fun i ↦ ¬ (i.val < m₁))).card = m₂ := by
  classical
  have := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (m₁ + m₂)))) (p := fun i ↦ i.val < m₁)
  rw [card_lowGroup, Finset.card_univ, Fintype.card_fin] at this
  lia

/-- **The rank certificate discharges a four-block condition.**

Eight rank sets — `T k` for the low group, `U k` for the high group, `k` running over the four bins
— each side partitioning its own positions, together with prefix-density bounds `r k`, `s k` and a
capacity check, give `Gap212.Packing.AdmitsPartition₄` for every profile of `Ξ`.

This is where the sorted reading pays: the capacity check `hcap` is an inequality between exact
rationals, one per bin, and it is the *only* numeric content.

The fourth bin is the complement, so its rank sets are only used through `hcap 3`: the blocks for
bins one to three are named, and whatever they leave over is contained in the fourth block and
therefore no heavier. -/
@[gap212 "lem_rank_certificate"]
theorem admitsPartition₄_of_rank_certificate {m₁ m₂ : ℕ} {B₁ B₂ δ : 𝕜}
    {y : Fin (m₁ + m₂) → 𝕜} (hy : y ∈ Xi B₁ B₂ m₁ m₂ δ) (hδ : 0 ≤ δ)
    (T : Fin 4 → Finset (Fin m₁)) (U : Fin 4 → Finset (Fin m₂))
    (hTcover : ∀ j, ∃ k, j ∈ T k) (hTdisj : ∀ k l, k ≠ l → Disjoint (T k) (T l))
    (hUcover : ∀ j, ∃ k, j ∈ U k) (hUdisj : ∀ k l, k ≠ l → Disjoint (U k) (U l))
    (r s : Fin 4 → 𝕜) (hr0 : ∀ k, 0 ≤ r k) (hs0 : ∀ k, 0 ≤ s k)
    (hr : ∀ k, ∀ j : ℕ, ((((T k).filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ r k * j)
    (hs : ∀ k, ∀ j : ℕ, ((((U k).filter (fun i ↦ i.val < j)).card : ℕ) : 𝕜) ≤ s k * j)
    (c : Fin 4 → 𝕜)
    (hcap : ∀ k, ((((T k).card : ℕ) : 𝕜) * δ + r k * (B₁ - (m₁ : 𝕜) * δ))
        + ((((U k).card : ℕ) : 𝕜) * δ + s k * (B₂ - (m₂ : 𝕜) * δ)) ≤ c k) :
    AdmitsPartition₄ y (c 0) (c 1) (c 2) (c 3) := by
  classical
  obtain ⟨hbox, hsum₁, hsum₂⟩ := hy
  set G₁ : Finset (Fin (m₁ + m₂)) := Finset.univ.filter (fun i ↦ i.val < m₁)
  set G₂ : Finset (Fin (m₁ + m₂)) := Finset.univ.filter (fun i ↦ ¬ (i.val < m₁))
  have hGdisj : Disjoint G₁ G₂ := Finset.disjoint_filter_filter_not _ _ _
  obtain ⟨e₁, he₁, he₁G, he₁anti⟩ := exists_antitone_enum G₁ y (card_lowGroup m₁ m₂)
  obtain ⟨e₂, he₂, he₂G, he₂anti⟩ := exists_antitone_enum G₂ y (card_highGroup m₁ m₂)
  have hsub₁ : ∀ V : Finset (Fin m₁), V.image e₁ ⊆ G₁ := fun V ↦
    he₁G ▸ Finset.image_subset_image (Finset.subset_univ V)
  have hsub₂ : ∀ V : Finset (Fin m₂), V.image e₂ ⊆ G₂ := fun V ↦
    he₂G ▸ Finset.image_subset_image (Finset.subset_univ V)
  have hdisj : ∀ (V : Finset (Fin m₁)) (W : Finset (Fin m₂)),
      Disjoint (V.image e₁) (W.image e₂) := fun V W ↦
    Finset.disjoint_of_subset_left (hsub₁ V) (Finset.disjoint_of_subset_right (hsub₂ W) hGdisj)
  -- the four blocks
  set P : Fin 4 → Finset (Fin (m₁ + m₂)) := fun k ↦ (T k).image e₁ ∪ (U k).image e₂
  -- the mass bound on each block
  have hmass : ∀ k, ∑ i ∈ P k, y i ≤ c k := fun k ↦ by
    rw [Finset.sum_union (hdisj _ _)]
    exact (add_le_add
      (sum_image_le_of_ranks (fun i _ ↦ (hbox i).1) hsum₁ he₁ he₁G he₁anti (T k) (hr0 k) (hr k))
      (sum_image_le_of_ranks (fun i _ ↦ (hbox i).1) hsum₂ he₂ he₂G he₂anti (U k) (hs0 k) (hs k))
      ).trans (hcap k)
  -- pairwise disjointness
  have hPdisj : ∀ k l, k ≠ l → Disjoint (P k) (P l) := fun k l hkl ↦
    Finset.disjoint_union_left.2 ⟨Finset.disjoint_union_right.2
      ⟨(Finset.disjoint_image he₁).2 (hTdisj k l hkl), hdisj _ _⟩,
      Finset.disjoint_union_right.2
        ⟨(hdisj _ _).symm, (Finset.disjoint_image he₂).2 (hUdisj k l hkl)⟩⟩
  -- every index lies in some block
  have hcover : ∀ i, ∃ k, i ∈ P k := by
    intro i
    by_cases hi : i.val < m₁
    · have hi₁ : i ∈ G₁ := Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩
      rw [← he₁G, Finset.mem_image] at hi₁
      obtain ⟨j, -, rfl⟩ := hi₁
      obtain ⟨k, hk⟩ := hTcover j
      exact ⟨k, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hk)⟩
    · have hi₂ : i ∈ G₂ := Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩
      rw [← he₂G, Finset.mem_image] at hi₂
      obtain ⟨j, -, rfl⟩ := hi₂
      obtain ⟨k, hk⟩ := hUcover j
      exact ⟨k, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)⟩
  refine ⟨P 0, P 1, P 2, hPdisj 0 1 (by decide), hPdisj 0 2 (by decide),
    hPdisj 1 2 (by decide), hmass 0, hmass 1, hmass 2, (Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi ↦ ?_) fun i _ _ ↦ hδ.trans (hbox i).1).trans (hmass 3)⟩
  obtain ⟨k, hk⟩ := hcover i
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or] at hi
  match k with
  | 0 | 1 | 2 => tauto
  | 3 => exact hk

end Gap212.Packing
