/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.Basic
public import Mathlib.Tactic.Ring
public meta import Gap212.Attr

/-!
# Condition (D), the Type IIc packing condition

Condition (D) of Proposition 3 of Stadlmann's *Bounded gaps between primes* is the only
factor-packing condition that does not degenerate at Point A. Its four capacities are

    c₁ = γ - 2δ - 8ω₀ - ϵ,   c₂ = 1/2 - γ - 2ω₀ - ϵ,   c₃ = 4ω₀ + δ - ϵ,   c₄ = 8ω₀,

with `ω₀` ranging over `[0, ω]` and `γ` over `[ξ₂ - ϵ, 1/3 + 8ω + 7δ/3 + 3ϵ]`. Unlike (A), (B), (C)
and (E), the first capacity does *not* dominate the total rough mass `17/50`, so the trivial
partition fails and a greedy transfer is needed: the continuum-packing lemma.

## The greedy engine

`exists_subset_sum_mem_Icc` is the combinatorial core: if every element is at most `w` and the
total is at least `D`, then some subset has sum in `[D, D + w]`. The proof is not the incremental
greedy but its cleaner equivalent — take a subset of *minimal cardinality* whose sum reaches
`D`. Removing any one of its elements drops the sum below `D`, so the sum exceeds `D` by less than
that element, hence by at most `w`.

## The identity that drives the argument

The unused second-bin capacity after absorbing the deficit is exactly

    c₂ - D = 1/2 - Y - 2δ - 10ω₀ - 2ϵ = W,

which is `c₂_sub_D` — the `γ` cancels. So the greedy overshoot is affordable precisely when the
last transferred factor is at most `W`, and `conditionD_of_all_le_W` closes that branch. The
remaining branch, where some rough factor exceeds `W`, is where four exact rational inequalities
enter: `packing_ineq₁`–`packing_ineq₄`, each recorded with its exact slack.

## A defect in the printed condition

`no_partition₄_of_neg_capacity` records, as a theorem, that condition (D) as printed is
**unsatisfiable** whenever `ω₀ < 0`: the fourth capacity `8ω₀` is then negative, while the fourth
block's sum is a sum of nonnegative terms and so is at least `0`. The condition is stated for
`ω₀ ∈ [-ϵ, ω(j,j')]` but can only hold for `ω₀ ≥ 0`. Type IIc is therefore invoked only at
`ω₀ ≥ 0`, sub-half moduli being routed through Bombieri–Vinogradov and endpoint transport instead,
and everything below is stated at `ω₀ ≥ 0`.

## Main results

* `Gap212.Packing.exists_subset_sum_mem_Icc`: the greedy subset-sum engine.
* `Gap212.Packing.admitsPartition₄_of_partition₂`: a two-block partition serves as a four-block
  one.
* `Gap212.Packing.no_partition₄_of_neg_capacity`: the printed condition is unsatisfiable when
  `ω₀ < 0`.
* `Gap212.Packing.c₂_sub_D`: `c₂ - D = W`.
* `Gap212.Packing.reserve_pos`: the reserve is positive throughout the chamber.
* `Gap212.Packing.conditionD_of_D_nonpos`, `conditionD_of_all_le_W`: the two closable branches.
* `Gap212.Packing.packing_ineq₁`–`packing_ineq₄` and their slacks.
* `Gap212.Packing.conditionD_of_D_nonpos_real` and companions: the same at `ℝ`.

## The field the tuples live in

The rough-profile entries are `yᵢ = log_x(fᵢ)` and the chamber coordinates `γ`, `ω₀` are exponents,
so everything about a *tuple* is stated over an arbitrary linearly ordered field, and used at `ℝ`.
Only the fixed rational parameters — `capMin`, `reserveMin`, `packing_ineq₁`–`packing_ineq₄` — stay
in `ℚ`, where they belong and where `norm_num` decides them exactly.
-/

@[expose] public section

namespace Gap212.Packing

open Finset

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {ℓ : ℕ}

/-! ## The greedy subset-sum engine -/

/-- **The subset-sum filling lemma.** If every element is at most `w`, and the total is at least
`D ≥ 0`, then some subset has sum in `[D, D + w]`.

This is the engine behind the factor-extraction lemmas. Note that
nonnegativity of the entries is *not* needed: the minimal-cardinality argument only uses the upper
bound `w` on a single element. -/
@[gap212 "lem_subset_sum_window"]
theorem exists_subset_sum_mem_Icc (y : Fin ℓ → 𝕜) (w D : 𝕜)
    (hw : ∀ i, y i ≤ w) (hw0 : 0 ≤ w) (hD : 0 ≤ D)
    (htot : D ≤ ∑ i, y i) :
    ∃ I : Finset (Fin ℓ), D ≤ ∑ i ∈ I, y i ∧ ∑ i ∈ I, y i ≤ D + w := by
  classical
  set S : Finset (Finset (Fin ℓ)) :=
    (univ : Finset (Fin ℓ)).powerset.filter (fun I ↦ D ≤ ∑ i ∈ I, y i) with hSdef
  have hSne : S.Nonempty := ⟨univ, by simp [hSdef, htot]⟩
  obtain ⟨I, hIS, hImin⟩ := S.exists_min_image Finset.card hSne
  have hID : D ≤ ∑ i ∈ I, y i := by
    have : I ∈ (univ : Finset (Fin ℓ)).powerset.filter (fun I ↦ D ≤ ∑ i ∈ I, y i) := hIS
    exact (mem_filter.mp this).2
  refine ⟨I, hID, ?_⟩
  rcases I.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · -- The empty subset already reaches `D`, so `D ≤ 0`; with `hD` the sum is `0`.
    simp only [sum_empty] at hID ⊢
    linarith
  · -- Deleting `i` must drop the sum below `D`, by minimality of the cardinality.
    have hcard : (I.erase i).card < I.card := card_erase_lt_of_mem hi
    have hlt : ∑ j ∈ I.erase i, y j < D := by
      by_contra hcon
      have hmem : I.erase i ∈ S :=
        mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), not_lt.mp hcon⟩
      have hge := hImin _ hmem
      omega
    have hsplit : ∑ j ∈ I, y j = y i + ∑ j ∈ I.erase i, y j := (add_sum_erase _ _ hi).symm
    have hwi := hw i
    linarith

/-! ## Reducing four blocks to two -/

omit [IsStrictOrderedRing 𝕜] in
/-- A two-block partition serves as a four-block one when the last two capacities are nonnegative:
put the complement's mass in block two and leave blocks three and four empty. -/
theorem admitsPartition₄_of_partition₂ {y : Fin ℓ → 𝕜} {b₁ b₂ b₃ b₄ : 𝕜}
    (h : AdmitsPartition₂ y b₁ b₂) (hb₃ : 0 ≤ b₃) (hb₄ : 0 ≤ b₄) :
    AdmitsPartition₄ y b₁ b₂ b₃ b₄ := by
  classical
  obtain ⟨I, hI₁, hI₂⟩ := h
  refine ⟨I, univ \ I, ∅, Finset.disjoint_sdiff, disjoint_empty_right _,
    disjoint_empty_right _, hI₁, hI₂, by simpa using hb₃, ?_⟩
  have hcover : I ∪ (univ \ I) ∪ ∅ = univ := by
    rw [union_empty, Finset.union_sdiff_of_subset (subset_univ I)]
  rw [hcover, sdiff_self]
  simpa using hb₄

/-! ## The printed condition is unsatisfiable at a negative fourth capacity -/

/-- **The defect.** If the fourth capacity is negative and the entries are nonnegative, no
four-block partition exists: the fourth block's sum is a sum of nonnegative terms, hence at least
`0 > b₄`.

Condition (D) is printed for `ω₀ ∈ [-ϵ, ω(j,j')]` with fourth capacity `8ω₀`, so for `ω₀ < 0` it
cannot hold for any tuple whatsoever. Type IIc must therefore be invoked only at `ω₀ ≥ 0`. -/
theorem no_partition₄_of_neg_capacity {y : Fin ℓ → 𝕜} {b₁ b₂ b₃ b₄ : 𝕜}
    (hy : ∀ i, 0 ≤ y i) (hb₄ : b₄ < 0) : ¬ AdmitsPartition₄ y b₁ b₂ b₃ b₄ := by
  rintro ⟨I, J, K, -, -, -, -, -, -, h₄⟩
  have : (0 : 𝕜) ≤ ∑ i ∈ univ \ (I ∪ J ∪ K), y i := sum_nonneg fun i _ ↦ hy i
  linarith

/-! ## The Type IIc capacities -/

open Gap212.PointA

/-- The first Type IIc capacity, `c₁ = γ - 2δ - 8ω₀ - ϵ`. -/
def cap₁ (γ ω₀ : 𝕜) : 𝕜 := γ - 2 * (δ : 𝕜) - 8 * ω₀ - (ϵ : 𝕜)

/-- The second Type IIc capacity, `c₂ = 1/2 - γ - 2ω₀ - ϵ`. -/
def cap₂ (γ ω₀ : 𝕜) : 𝕜 := 1 / 2 - γ - 2 * ω₀ - (ϵ : 𝕜)

/-- The third Type IIc capacity, `c₃ = 4ω₀ + δ - ϵ`. -/
def cap₃ (ω₀ : 𝕜) : 𝕜 := 4 * ω₀ + (δ : 𝕜) - (ϵ : 𝕜)

/-- The fourth Type IIc capacity, `c₄ = 8ω₀`. Zero at the endpoint `ω₀ = 0`, where the fourth
block must be empty. -/
def cap₄ (ω₀ : 𝕜) : 𝕜 := 8 * ω₀

/-- The deficit `D = Y - c₁`: the mass that must be moved out of the first block. -/
def deficit (Y γ ω₀ : 𝕜) : 𝕜 := Y - cap₁ γ ω₀

/-- The reserve `W = 1/2 - Y - 2δ - 10ω₀ - 2ϵ`: the second block's unused capacity after the
deficit has been absorbed. -/
def reserve (Y ω₀ : 𝕜) : 𝕜 := 1 / 2 - Y - 2 * (δ : 𝕜) - 10 * ω₀ - 2 * (ϵ : 𝕜)

/-- **The identity driving the greedy argument**: the second block's capacity, less the deficit it
must absorb, is exactly the reserve. Note the `γ` cancels. -/
theorem c₂_sub_D (Y γ ω₀ : 𝕜) : cap₂ γ ω₀ - deficit Y γ ω₀ = reserve Y ω₀ := by
  unfold cap₂ deficit cap₁ reserve; ring

/-- The reserve at the endpoint `ω₀ = 0` with maximal mass `Y = 17/50` is `621/5000 - 2ϵ`. -/
theorem reserve_endpoint : reserve (17 / 50 : 𝕜) 0 = 621 / 5000 - 2 * (ϵ : 𝕜) := by
  unfold reserve
  rw [cast_δ]
  ring

/-- The reserve is minimized over the chamber at `ω₀ = ω`, `Y = 17/50`, where it is
`74/1250 - 2ϵ`. -/
theorem reserve_min : reserve (17 / 50 : 𝕜) (ω : 𝕜) = 74 / 1250 - 2 * (ϵ : 𝕜) := by
  unfold reserve
  rw [cast_δ, cast_ω]
  ring

/-- **The reserve is positive throughout the chamber** `ω₀ ∈ [0, ω]`, `Y ≤ 17/50`. This is what
makes the greedy transfer affordable at all. Only the upper bound on `ω₀` is needed. -/
theorem reserve_pos {Y ω₀ : 𝕜} (hY : Y ≤ 17 / 50) (hω₀' : ω₀ ≤ (ω : 𝕜)) :
    0 < reserve Y ω₀ := by
  rw [cast_ω] at hω₀'
  unfold reserve
  rw [cast_δ, cast_ϵ]
  norm_num
  linarith

/-! ## The two closable branches of the continuum-packing lemma -/

/-- **Branch 1: no deficit.** If the whole rough mass already fits in the first capacity, put
everything there and leave the other three blocks empty. -/
theorem conditionD_of_D_nonpos {y : Fin ℓ → 𝕜} {γ ω₀ : 𝕜}
    (htot : ∑ i, y i ≤ cap₁ γ ω₀) (h₂ : 0 ≤ cap₂ γ ω₀) (hω₀ : 0 ≤ ω₀)
    (h₃ : 0 ≤ cap₃ ω₀) :
    AdmitsPartition₄ y (cap₁ γ ω₀) (cap₂ γ ω₀) (cap₃ ω₀) (cap₄ ω₀) :=
  admitsPartition₄_of_total_le htot h₂ h₃ (by unfold cap₄; linarith)

/-- **Branch 2: every rough factor fits in the reserve.** Then the greedy transfer works: some
subset has mass in `[D, D + W]`, and `D + W = c₂` by `c₂_sub_D`, so that subset fits in the second
block while the untransferred remainder — of mass `Y - D = c₁` — fits in the first.

Blocks three and four are left empty, which is why `0 ≤ cap₃ ω₀` and `0 ≤ ω₀` are needed. -/
theorem conditionD_of_all_le_W {y : Fin ℓ → 𝕜} {γ ω₀ : 𝕜}
    (hle : ∀ i, y i ≤ reserve (∑ i, y i) ω₀)
    (hW0 : 0 ≤ reserve (∑ i, y i) ω₀)
    (hD0 : 0 ≤ deficit (∑ i, y i) γ ω₀)
    (hc₁ : 0 ≤ cap₁ γ ω₀)
    (hω₀ : 0 ≤ ω₀) (h₃ : 0 ≤ cap₃ ω₀) :
    AdmitsPartition₄ y (cap₁ γ ω₀) (cap₂ γ ω₀) (cap₃ ω₀) (cap₄ ω₀) := by
  classical
  have hdef : deficit (∑ i, y i) γ ω₀ = (∑ i, y i) - cap₁ γ ω₀ := rfl
  -- The deficit does not exceed the total, since the first capacity is nonnegative.
  have htotD : deficit (∑ i, y i) γ ω₀ ≤ ∑ i, y i := by rw [hdef]; linarith
  obtain ⟨J, hJlow, hJhigh⟩ :=
    exists_subset_sum_mem_Icc y (reserve (∑ i, y i) ω₀) (deficit (∑ i, y i) γ ω₀)
      hle hW0 hD0 htotD
  refine admitsPartition₄_of_partition₂ ⟨univ \ J, ?_, ?_⟩ h₃ (by unfold cap₄; linarith)
  · -- The untransferred mass is `Y - ∑_J y ≤ Y - D = c₁`.
    have hsplit : ∑ i ∈ univ \ J, y i + ∑ i ∈ J, y i = ∑ i, y i := sum_sdiff (subset_univ J)
    rw [hdef] at hJlow
    linarith
  · -- The transferred mass is at most `D + W = c₂`.
    rw [Finset.sdiff_sdiff_eq_self (subset_univ J)]
    have hid := c₂_sub_D (∑ i, y i) γ ω₀
    linarith

/-! ## The four exact rational inequalities

These are the comparisons the remaining branch of the continuum-packing lemma rests on — the case
where some rough factor exceeds the reserve. Each is recorded together with its exact slack. -/

/-- `c₁ᵐⁱⁿ = 2/5 - 2δ - 8ω - ϵ = 3121999999/10¹⁰`, the least first capacity over the chamber. -/
def capMin : ℚ := 2 / 5 - 2 * δ - 8 * ω - ϵ

/-- `c₁ᵐⁱⁿ = 3121999999/10¹⁰`. -/
theorem capMin_eq : capMin = 3121999999 / 10 ^ 10 := by norm_num [capMin, δ, ω, ϵ]

/-- `Wᵐⁱⁿ = 74/1250 - 2ϵ`, the least reserve over the chamber. -/
def reserveMin : ℚ := 74 / 1250 - 2 * ϵ

/-- **Packing inequality 1**: `17/50 - c₁ᵐⁱⁿ < 2δ`. This bounds the deficit below `2δ`, so any
two factors, each of mass at least `δ`, carry it. -/
theorem packing_ineq₁ : 17 / 50 - capMin < 2 * δ := by norm_num [capMin, δ, ω, ϵ]

/-- Its exact slack. -/
theorem packing_ineq₁_slack : 2 * δ - (17 / 50 - capMin) = 79999999 / 10 ^ 10 := by
  norm_num [capMin, δ, ω, ϵ]

/-- **Packing inequality 2**: `3Wᵐⁱⁿ > 17/100`. Three factors each exceeding the reserve would
overflow the rough cap `B₃ = 17/100`, so at most two can. -/
theorem packing_ineq₂ : 17 / 100 < 3 * reserveMin := by norm_num [reserveMin, ϵ]

/-- Its exact slack. -/
theorem packing_ineq₂_slack : 3 * reserveMin - 17 / 100 = 37999997 / (5 * 10 ^ 9) := by
  norm_num [reserveMin, ϵ]

/-- **Packing inequality 3**: `2B₁,₂ ≤ c₁ᵐⁱⁿ`. If neither side carries more than two factors,
the whole mass fits in the first block. -/
theorem packing_ineq₃ : 2 * B₁ ≤ capMin := by norm_num [capMin, B₁, δ, ω, ϵ]

/-- Its exact slack. -/
theorem packing_ineq₃_slack : capMin - 2 * B₁ = 21999999 / 10 ^ 10 := by
  norm_num [capMin, B₁, δ, ω, ϵ]

/-- **Packing inequality 4**: `B₁,₃ + B₁,₂ - c₁ᵐⁱⁿ < δ`. If one side carries at most two factors,
the deficit falls below `δ`, so any single factor, of mass at least `δ`, carries it. -/
theorem packing_ineq₄ : B₃ + B₁ - capMin < δ := by norm_num [capMin, B₁, B₃, δ, ω, ϵ]

/-- Its exact slack. -/
theorem packing_ineq₄_slack : δ - (B₃ + B₁ - capMin) = 50999999 / 10 ^ 10 := by
  norm_num [capMin, B₁, B₃, δ, ω, ϵ]

/-- The four exact inequalities of the continuum-packing lemma, together. -/
theorem packing_inequalities :
    17 / 50 - capMin < 2 * δ ∧ 17 / 100 < 3 * reserveMin ∧ 2 * B₁ ≤ capMin ∧
      B₃ + B₁ - capMin < δ :=
  ⟨packing_ineq₁, packing_ineq₂, packing_ineq₃, packing_ineq₄⟩

/-! ## Instantiation at `ℝ`

The rough-profile tuples are `yᵢ = log_x(fᵢ)` and the chamber coordinates `γ`, `ω₀` are exponents,
so `ℝ` is the field condition (D) is actually used over — `Gap212.Extraction.four_factor` consumes
`AdmitsPartition₄` at `ℝ`. The capacities and the two closable branches above are stated over any
linearly ordered field precisely so that this instantiation exists; the exact rational facts stay
in `ℚ`, which is where the fixed parameters belong and where `norm_num` can decide them. -/

/-- **Branch 1 at `ℝ`.** -/
theorem conditionD_of_D_nonpos_real {y : Fin ℓ → ℝ} {γ ω₀ : ℝ}
    (htot : ∑ i, y i ≤ cap₁ γ ω₀) (h₂ : 0 ≤ cap₂ γ ω₀) (hω₀ : 0 ≤ ω₀)
    (h₃ : 0 ≤ cap₃ ω₀) :
    AdmitsPartition₄ y (cap₁ γ ω₀) (cap₂ γ ω₀) (cap₃ ω₀) (cap₄ ω₀) :=
  conditionD_of_D_nonpos htot h₂ hω₀ h₃

/-- **Branch 2 at `ℝ`.** -/
theorem conditionD_of_all_le_W_real {y : Fin ℓ → ℝ} {γ ω₀ : ℝ}
    (hle : ∀ i, y i ≤ reserve (∑ i, y i) ω₀)
    (hW0 : 0 ≤ reserve (∑ i, y i) ω₀)
    (hD0 : 0 ≤ deficit (∑ i, y i) γ ω₀)
    (hc₁ : 0 ≤ cap₁ γ ω₀)
    (hω₀ : 0 ≤ ω₀) (h₃ : 0 ≤ cap₃ ω₀) :
    AdmitsPartition₄ y (cap₁ γ ω₀) (cap₂ γ ω₀) (cap₃ ω₀) (cap₄ ω₀) :=
  conditionD_of_all_le_W hle hW0 hD0 hc₁ hω₀ h₃

/-- **The defect at `ℝ`**: condition (D) as printed is unsatisfiable for `ω₀ < 0`, over the field
the tuples actually live in. -/
theorem no_partition₄_of_neg_capacity_real {y : Fin ℓ → ℝ} {b₁ b₂ b₃ b₄ : ℝ}
    (hy : ∀ i, 0 ≤ y i) (hb₄ : b₄ < 0) : ¬ AdmitsPartition₄ y b₁ b₂ b₃ b₄ :=
  no_partition₄_of_neg_capacity hy hb₄

end Gap212.Packing
