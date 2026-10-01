/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Harman.Challenge
public import Gap212.Routing.Union
public meta import Gap212.Attr

/-!
# The generated moduli are a finite union of bands

`Gap212.Qstar p x ε₀` is by definition the union of the bands `Gap212.Qgen p x j j' m m' ε₀` over
`j, j' : Fin p.n` and `m, m' ≤ ⌊1 / p.δ⌋`, so there are at most
`b = p.n ^ 2 * (⌊1 / p.δ⌋ + 1) ^ 2` of them — a number depending on the support datum alone and
**not on `x`**. Consequently a bound holding uniformly over each band gives one over `Qstar` at the
cost of the factor `b`, and because `b` does not grow with `x` that factor is absorbed into the
implied constant rather than competing with the logarithmic saving. This is the last step of the
routing argument, and the reason it may be run one index tuple `(j, j', m, m')` at a time.

## What the union bound needs

Only that the summand is nonnegative — it is a norm. So the argument is insensitive to *which*
discrepancy is summed, and the proof below is the one of
`Gap212.Routing.qstarSum_le_of_forall_qgen` transferred verbatim from the dyadic discrepancy
`Gap212.Routing.discrepancy` to the unrestricted `Gap212.sumError`, with `norm_nonneg` in place of
`discrepancy_nonneg`. The general form of the union bound, `Gap212.Routing.sum_le_sum_of_cover`, is
reused unchanged: Mathlib has it for `ℝ≥0∞` (`ENNReal.tsum_biUnion_le`) but not for an ordered
field.

The unrestricted discrepancy is the one the equidistribution estimates and `Gap212.TypeII` are
stated with, so it is this version that the routing's assembly consumes; the dyadic one is a
different quantity, with its own version `Gap212.Routing.qstarSum_le_of_forall_qgen`.

## Main results

* `Gap212.qstarSum_le_of_forall_qgen`: the unrestricted discrepancy summed over the squarefree
  moduli of `Qstar`, bounded by the band count times a uniform bound over each band.
* `Gap212.hasEquidistributionOverQstar_of_forall_qgen`: the same statement in the shape the routing
  quotes it, `Gap212.HasEquidistribution` on each band giving
  `Gap212.HasEquidistributionOverQstar` with the constant multiplied by the band count.
-/

@[expose] public section

namespace Gap212

open Finset

/-- The band count `b = n² (⌊1/δ⌋ + 1)²` of `Gap212.Qstar`: the number of index tuples
`(j, j', m, m')` with `j, j' : Fin p.n` and `m, m' ≤ ⌊1 / p.δ⌋`. It depends on the support datum
alone, which is why it costs nothing to a bound that has to be uniform in `x`. -/
noncomputable def bandCount (p : SupportParams) : ℕ :=
  p.n * p.n * (⌊1 / p.δ⌋₊ + 1) * (⌊1 / p.δ⌋₊ + 1)

open Classical in
/-- **A uniform bound over each band gives one over `Q*`.** `Qstar` is the union of the bands
`Qgen p x j j' m m' ε₀` over `j, j' : Fin p.n` and `m, m' ≤ ⌊1 / p.δ⌋`, so a sum of nonnegative
terms over it is at most the sum of the sums over the bands, of which there are `bandCount p`. The
cost is therefore that one factor, a constant depending on the support datum and not on `x`, so it
is absorbed into the implied constant instead of competing with the logarithmic saving.

The summand is `‖sumError f q a‖`, the unrestricted discrepancy the estimates are stated with; the
proof uses nothing about it beyond its nonnegativity. -/
@[gap212 "lem_finite_band_union"]
theorem qstarSum_le_of_forall_qgen {f : ℕ → ℂ} {p : SupportParams} {x ε₀ : ℝ} {a : ℕ} {c : ℝ}
    (hbound : ∀ (j j' : Fin p.n) (m m' : ℕ), m ≤ ⌊1 / p.δ⌋₊ → m' ≤ ⌊1 / p.δ⌋₊ →
      ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qgen p x j j' m m' ε₀ ∧ Squarefree q},
        ‖sumError f q a‖ ≤ c) :
    ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ Squarefree q}, ‖sumError f q a‖
      ≤ (bandCount p : ℝ) * c := by
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
    obtain ⟨hqIcc, hqQ, hqsf⟩ := mem_filter.mp hq
    simp only [Qstar, Set.mem_iUnion] at hqQ
    obtain ⟨j, j', m, hmK, m', hm'K, hm'⟩ := hqQ
    exact ⟨(j, j', m, m'), by simpa [hS] using ⟨mem_Iic.1 hmK, mem_Iic.1 hm'K⟩,
      by simp [hG, hqIcc, hm', hqsf]⟩
  -- Bound the covering sum by the band count times `c`.
  refine le_trans (Routing.sum_le_sum_of_cover (fun q ↦ norm_nonneg (sumError f q a)) hcover) ?_
  calc ∑ t ∈ S, ∑ q ∈ G t, ‖sumError f q a‖ ≤ ∑ _t ∈ S, c := sum_le_sum fun t ht ↦ by
        simp only [hS, mem_product, mem_univ, mem_Iic, true_and] at ht
        exact hbound _ _ _ _ ht.1 ht.2
    _ = (bandCount p : ℝ) * c := by simp [hS, bandCount, hK, mul_assoc]

open Classical in
/-- **The band union in the shape the routing quotes it.** If for each band the squarefree
discrepancy sum is at most `C₁ * x / (log x) ^ A`, then the sum over `Qstar` is at most
`bandCount p * C₁ * x / (log x) ^ A`: the saving `A` is untouched and only the constant moves.

This is how the assembly uses the union bound — the five Type estimates and the smooth-only band
are each applied at one index tuple, and their common constant is multiplied by the band count
once. -/
theorem hasEquidistributionOverQstar_of_forall_qgen {f : ℕ → ℂ} {p : SupportParams} {x ε₀ : ℝ}
    {a : ℕ} {A C₁ : ℝ}
    (hbound : ∀ (j j' : Fin p.n) (m m' : ℕ), m ≤ ⌊1 / p.δ⌋₊ → m' ≤ ⌊1 / p.δ⌋₊ →
      HasEquidistribution x {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qgen p x j j' m m' ε₀} f a A C₁) :
    HasEquidistributionOverQstar p x ε₀ f a A ((bandCount p : ℝ) * C₁) := by
  classical
  rw [HasEquidistributionOverQstar, HasEquidistribution, Finset.filter_filter]
  refine le_trans (qstarSum_le_of_forall_qgen (c := C₁ * x / (Real.log x) ^ A)
    fun j j' m m' hm hm' ↦ ?_) (le_of_eq (by ring))
  simpa only [HasEquidistribution, filter_filter] using hbound j j' m m' hm hm'

end Gap212
