/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.Monotone

/-!
# From one stratum pair to the whole generated family

The routing argument proves its discrepancy bound one `(j, j', m, m')` at a time — that is what the
source means by "it is enough to establish" the bound over `Q(x; …, j, j', m, m', ε₀)`. The moduli
the support generates are the union of those over all four indices, so the argument's last step is
a union bound.

That step is cheap but not free, and it is worth isolating for two reasons. The number of index
tuples is `n² (⌊1/δ⌋ + 1)²`, a constant depending only on the support and **not on `x`** — so it is
absorbed into the implied constant, which is what
`HasEquidistributionOverQstarFamily`'s `∃ c` is for.
This is the same manoeuvre the source performs for the `O((log x)^C)` decomposition pieces, except
that here the count really is `O(1)`, so nothing has to be spent on it.

## What the union bound needs

Only that the summand is nonnegative — it is a norm. `Gap212.Routing.sum_le_sum_of_cover` is the
general form: if every element of a `Finset` lies in at least one member of a family, the sum is at
most the sum of the members' sums. Mathlib has this for `ℝ≥0∞` (`ENNReal.tsum_biUnion_le`) but not
for an ordered field, so it is proved here from `Finset.sum_union_inter`.

## Splitting a modulus sum by size

The containments of `Gap212.Routing.Containment` all carry a hypothesis `x^{…} ≤ q`: the
factor-extraction lemmas only reach moduli above the retreated half-level. So a route cannot bound
the whole of `Q(j, j', m, m')` — it bounds the large part, and the small part is the business of
bilinear Bombieri–Vinogradov and endpoint transport. `Gap212.Routing.sum_split_at` is that split,
named because the four-range architecture of the routing is exactly this split applied at
`x^{1/2 - ε₁}`.

## Main results

* `Gap212.Routing.sum_union_le_of_nonneg`, `sum_biUnion_le_of_nonneg`, `sum_le_sum_of_cover`: the
  union bound for a nonnegative summand.
* `Gap212.Routing.qstarSum_le_of_forall_qgen`: the discrepancy over `Q*` from a uniform bound over
  each `Q(j, j', m, m')`, at the cost of the tuple count.
* `Gap212.Routing.sum_split_at`: a modulus sum split at a size threshold.
-/

@[expose] public section

namespace Gap212.Routing

open Finset

/-! ## The union bound for a nonnegative summand -/

/-- `∑_{A ∪ B} f ≤ ∑_A f + ∑_B f`, the overlap being counted twice on the right. -/
theorem sum_union_le_of_nonneg {κ : Type*} [DecidableEq κ] {f : κ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (A B : Finset κ) : ∑ k ∈ A ∪ B, f k ≤ ∑ k ∈ A, f k + ∑ k ∈ B, f k := by
  linarith [Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f),
    Finset.sum_nonneg fun k (_ : k ∈ A ∩ B) ↦ hf k]

/-- `∑_{⋃ i ∈ s, t i} f ≤ ∑_{i ∈ s} ∑_{t i} f`. -/
theorem sum_biUnion_le_of_nonneg {ι κ : Type*} [DecidableEq κ] {f : κ → ℝ} (hf : ∀ k, 0 ≤ f k)
    (s : Finset ι) (t : ι → Finset κ) :
    ∑ k ∈ s.biUnion t, f k ≤ ∑ i ∈ s, ∑ k ∈ t i, f k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      linarith [sum_union_le_of_nonneg hf (t a) (s.biUnion t)]

/-- **The union bound.** If every element of `L` lies in some `G i` with `i ∈ s`, the sum over `L`
is at most the sum of the sums over the `G i`. -/
theorem sum_le_sum_of_cover {ι κ : Type*} {f : κ → ℝ} (hf : ∀ k, 0 ≤ f k)
    {L : Finset κ} {s : Finset ι} {G : ι → Finset κ}
    (hcover : ∀ k ∈ L, ∃ i ∈ s, k ∈ G i) :
    ∑ k ∈ L, f k ≤ ∑ i ∈ s, ∑ k ∈ G i, f k := by
  classical
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (fun k hk ↦ Finset.mem_biUnion.mpr (hcover k hk)) fun k _ _ ↦ hf k)
    (sum_biUnion_le_of_nonneg hf s G)

open Classical in
/-- **A uniform bound over each index tuple gives one over `Q*`.** The cost is the number of
tuples, `n² (⌊1/δ⌋ + 1)²` — a constant depending on the support alone, so it is absorbed into the
implied constant of `HasEquidistributionOverQstarFamily` rather than competing with the
logarithmic saving. -/
theorem qstarSum_le_of_forall_qgen {f : ℕ → ℝ → ℂ} {p : SupportParams} {x ε₀ : ℝ} {a : ℕ} {c : ℝ}
    (hbound : ∀ (j j' : Fin p.n) (m m' : ℕ), m ≤ ⌊1 / p.δ⌋₊ → m' ≤ ⌊1 / p.δ⌋₊ →
      ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qgen p x j j' m m' ε₀ ∧ Squarefree q},
        discrepancy f x a q ≤ c) :
    ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ Squarefree q}, discrepancy f x a q
      ≤ (p.n * p.n * (⌊1 / p.δ⌋₊ + 1) * (⌊1 / p.δ⌋₊ + 1) : ℕ) * c := by
  classical
  set K : ℕ := ⌊1 / p.δ⌋₊ with hK
  -- The index set: both strata and both rough-factor counts.
  set S : Finset (Fin p.n × Fin p.n × ℕ × ℕ) :=
    (univ : Finset (Fin p.n)) ×ˢ (univ : Finset (Fin p.n)) ×ˢ Finset.Iic K ×ˢ Finset.Iic K with hS
  set G : Fin p.n × Fin p.n × ℕ × ℕ → Finset ℕ := fun t ↦
    {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qgen p x t.1 t.2.1 t.2.2.1 t.2.2.2 ε₀ ∧ Squarefree q} with hG
  -- Every squarefree generated modulus lies in one of them.
  have hcover : ∀ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ Squarefree q},
      ∃ t ∈ S, q ∈ G t := by
    intro q hq
    obtain ⟨hqIcc, hqQ, hqsf⟩ := Finset.mem_filter.mp hq
    simp only [Qstar, Set.mem_iUnion, exists_prop] at hqQ
    obtain ⟨j, j', m, hmK, m', hm'K, hm'⟩ := hqQ
    exact ⟨(j, j', m, m'), by
      simp only [hS, Finset.mem_product, Finset.mem_univ, true_and]; exact ⟨hmK, hm'K⟩,
      by simp [hG, hqIcc, hm', hqsf]⟩
  -- Bound the covering sum by the tuple count times `c`.
  refine (sum_le_sum_of_cover (fun q ↦ discrepancy_nonneg f x a q) hcover).trans
    ((Finset.sum_le_sum (g := fun _ ↦ c) fun t ht ↦ ?_).trans_eq ?_)
  · simp only [hS, Finset.mem_product, Finset.mem_univ, Finset.mem_Iic, true_and] at ht
    exact hbound t.1 t.2.1 t.2.2.1 t.2.2.2 ht.1 ht.2
  · simp [hS, mul_assoc]

/-! ## Splitting a modulus sum by size -/

open Classical in
/-- **A modulus sum splits at any size threshold.** The routing argument uses this at
`t = x^{1/2 - ε₁}`: above it the factor-extraction lemmas apply and the five Type estimates take
over, below it the sum is the business of bilinear Bombieri–Vinogradov and endpoint transport. -/
theorem sum_split_at {f : ℕ → ℝ → ℂ} {x : ℝ} {a : ℕ} (G : Finset ℕ) (t : ℝ) :
    ∑ q ∈ G, discrepancy f x a q
      = (∑ q ∈ G.filter (fun n : ℕ ↦ (n : ℝ) < t), discrepancy f x a q)
        + ∑ q ∈ G.filter (fun n : ℕ ↦ ¬ ((n : ℝ) < t)), discrepancy f x a q :=
  (Finset.sum_filter_add_sum_filter_not G _ _).symm

open Classical in
/-- The large half of the split, as the routing consumes it: a bound on each half gives a bound on
the whole. -/
theorem sum_le_of_split {f : ℕ → ℝ → ℂ} {x : ℝ} {a : ℕ} {G : Finset ℕ} {t c₁ c₂ : ℝ}
    (hsmall : ∑ q ∈ G.filter (fun n : ℕ ↦ (n : ℝ) < t), discrepancy f x a q ≤ c₁)
    (hlarge : ∑ q ∈ G.filter (fun n : ℕ ↦ ¬ ((n : ℝ) < t)), discrepancy f x a q ≤ c₂) :
    ∑ q ∈ G, discrepancy f x a q ≤ c₁ + c₂ := by
  rw [sum_split_at G t]
  linarith

end Gap212.Routing
