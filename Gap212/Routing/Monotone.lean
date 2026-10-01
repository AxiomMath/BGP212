/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Equidistribution.Basic
public import Gap212.Main
public meta import Gap212.Attr

/-!
# Equidistribution is monotone in the set of moduli

Each of the five estimates concludes equidistribution over *its own* moduli set `D_type`, while the
routing argument needs it over the moduli the support actually generates. The containments of
`Gap212.Routing.Containment` give `Q ⊆ D_type`, and this module supplies the other half: an
equidistribution bound over a set transfers to any subset.

The reason is that the quantity summed is a **norm**, hence nonnegative, so shrinking the index set
can only shrink the sum. That is the whole content — but it is worth isolating, because it is what
makes the containments useful, and because the direction matters: equidistribution says a sum is
*small*, so it flows from larger index sets to smaller ones, opposite to the direction in which the
containments are stated.

## The discrepancy, named

Every equidistribution statement in the development sums the same quantity, and it appears inline
in each definition. `Gap212.Routing.discrepancy` names it, so the monotonicity argument can be
stated about a sum of nonnegative reals rather than about an expression that happens to be a norm.

## Main results

* `Gap212.Routing.discrepancy_nonneg`: the summand is nonnegative.
* `Gap212.Routing.hasEquidistribution_mono`: equidistribution transfers to a smaller moduli family.
* `Gap212.Routing.discrepancySum_le_of_subset`: the corresponding bound on a single sum.
-/

@[expose] public section

namespace Gap212.Routing

open Finset Real

/-- The discrepancy of `f` at modulus `q` and scale `x`, relative to the primitive class `a`: the
difference between the count over `[x, 2x]` in that class and its expected value. This is the
quantity every equidistribution statement sums. -/
@[gap212 "def_discrepancy"]
noncomputable def discrepancy (f : ℕ → ℝ → ℂ) (x : ℝ) (a q : ℕ) : ℝ :=
  ‖(∑ n ∈ dyadic x with n ≡ a [MOD q], f n x) -
    (1 / (Nat.totient q : ℂ)) * ∑ n ∈ dyadic x with Nat.Coprime n q, f n x‖

/-- The discrepancy is nonnegative, being a norm. This is the only property of it the monotonicity
argument uses. -/
theorem discrepancy_nonneg (f : ℕ → ℝ → ℂ) (x : ℝ) (a q : ℕ) : 0 ≤ discrepancy f x a q :=
  norm_nonneg _

/-- Shrinking the set of moduli shrinks the discrepancy sum. -/
theorem discrepancySum_le_of_subset {f : ℕ → ℝ → ℂ} {x : ℝ} {a : ℕ} {D' D : Finset ℕ}
    (hsub : D' ⊆ D) :
    ∑ q ∈ D', discrepancy f x a q ≤ ∑ q ∈ D, discrepancy f x a q :=
  Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ ↦ discrepancy_nonneg f x a q

/-- **Equidistribution is monotone in the moduli family.** If `D'` is contained in `D` at every
choice of parameters, then equidistribution over `D` gives equidistribution over `D'`.

Note the direction: equidistribution says a sum is *small*, so it flows from the larger family to
the smaller one — opposite to the direction in which the containments `Q ⊆ D_type` run. That is
exactly why the two compose. The witnesses `ε₀` and `c` are reused unchanged; only the sum is
weakened. -/
theorem hasEquidistribution_mono {f : ℕ → ℝ → ℂ}
    {D D' : ℝ → ℝ → ℝ → ℝ → ℝ → Finset ℕ} {S : Set (ℝ × ℝ × ℝ)}
    (hsub : ∀ x ω γ δ ε, D' x ω γ δ ε ⊆ D x ω γ δ ε)
    (h : HasEquidistributionFamily f D S) : HasEquidistributionFamily f D' S := by
  classical
  obtain ⟨ε₀, hε₀pos, hmain⟩ := h
  refine ⟨ε₀, hε₀pos, fun ε hε A hA ↦ ?_⟩
  obtain ⟨c, hcpos, hbound⟩ := hmain ε hε A hA
  refine ⟨c, hcpos, fun pr hpr x hx a ha ↦ ?_⟩
  refine le_trans ?_ (hbound pr hpr x hx a ha)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ (hsub x pr.1 pr.2.1 pr.2.2 ε))
    fun q _ _ ↦ norm_nonneg _

open Classical in
/-- The same statement for the support-generated family: if the moduli a support generates are
contained in a family over which `f` equidistributes, the discrepancy sum over the generated moduli
obeys the same bound.

This is the form the routing argument consumes at each `(j, j', m, m')`. -/
theorem qstarSum_le_of_subset {f : ℕ → ℝ → ℂ} {p : SupportParams} {x ε₀ : ℝ} {a : ℕ}
    {D : Finset ℕ}
    (hsub : ∀ q : ℕ, q ∈ Finset.Icc 1 ⌊x⌋₊ → q ∈ Qstar p x ε₀ → Squarefree q → q ∈ D) :
    ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ Squarefree q}, discrepancy f x a q
      ≤ ∑ q ∈ {q ∈ D | Squarefree q}, discrepancy f x a q := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ ↦ discrepancy_nonneg f x a q
  intro q hq
  simp only [Finset.mem_filter] at hq ⊢
  exact ⟨hsub q hq.1 hq.2.1 hq.2.2, hq.2.2⟩

end Gap212.Routing
