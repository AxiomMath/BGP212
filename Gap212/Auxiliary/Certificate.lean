/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Certificate
public import Gap212.Parameters.PointA
public import Gap212.Sieve.GPYDefs
public meta import Gap212.Attr

/-!
# The certificate bridge, the datum's conditions, and the positivity chain

Three short pieces the assembly needs between the numerical certificate and the sieve criterion,
and between the datum's rational checks and the abstract conditions that consume them.

## Main results

* `Gap212.Auxiliary.certificate_implies_hypothesis`: at `c₁ = c₂ = 0` the certificate inequality is
  exactly the sieve criterion's variational hypothesis.
* `Gap212.Auxiliary.scalar_conditions_at_pointA`: the four scalar conditions hold at Point A. For
  the datum of the main theorems see `Gap212.scalar_conditions_at_datum`.
* `Gap212.Auxiliary.datum_constraints`: Point A's parameters satisfy the support-datum
  constraints, with the step bound the binding one.
* `Gap212.Auxiliary.infinitely_many_of_unbounded`: an unbounded set of naturals is infinite, which
  is how "positive for arbitrarily large `x`" becomes "infinitely many `n`".
-/

@[expose] public section

namespace Gap212.Auxiliary

open Finset Gap212.PointA

/-- **The certificate gives the sieve criterion's hypothesis.** With `c₁ = c₂ = 0` the certificate
inequality `I < k(1-c₁)J - k c₂ K` collapses to `I < k J`, which is the variational hypothesis
verbatim. The `K`-term disappears because it is multiplied by `c₂`, and `(1 - c₁) = 1`.

The certificate is stated in the physical scale, so no rescaling is needed. -/
@[gap212 "lem_certificate_implies_hypothesis"]
theorem certificate_implies_hypothesis {I J K : ℝ} {k : ℝ}
    (h : I < k * (1 - 0) * J - k * 0 * K) : I < k * J := by
  simpa using h

/-- **The four scalar conditions hold at Point A.** Each is a comparison between explicit
rationals, already discharged individually in `Gap212.Parameters.PointA`; this is their
conjunction.

Point A differs from the datum `p_⋆` of the main theorems: `p_⋆` has `A₁ = 257/1000`,
`δ = 41/2500`, `ξ₁ = 19/50`, where this theorem is at `A₁ = 513/2000`, `δ = 179/10000`,
`ξ₁ = 23317/60000`. The four conditions at `p_⋆` are `Gap212.scalar_conditions_at_datum`.

The second condition is stated below in the form with `- 15 * ϵ`, which holds at Point A with a
slack of `66599997/2000000000`. -/
theorem scalar_conditions_at_pointA :
    δ < min (ξ₁ - 4 * A₁ + 2 / 3) (9 / 7 - (34 / 7) * A₁) - 2 * ϵ ∧
      0 ≤ 19 / 2 - 36 * A₁ - 13 * δ - 15 * ϵ ∧
      δ ≤ min (ξ₂ / 10 - 32 * A₁ / 10 + 8 / 10) (ξ₂ / 4 + 11 / 16 - 3 * A₁) - 2 * ϵ ∧
      δ < 11 / 8 - (7 / 2) * A₁ - (9 / 8) * ξ₃ - 2 * ϵ :=
  ⟨typeI_condition, typeII_condition_a, typeII_condition_b, typeIII_condition⟩

/-- **Point A satisfies the support-datum constraints**: `0 < δ`, `0 < ϵ`, `A₁ < 1/2 - ϵ`, and the
cap row's step is at most `δ`.

The binding one is the step: the row jumps from `31/200` to `17/100`, a step of `3/200`, against
`δ = 179/10000`. Since `3/200 = 150/10000`, the slack is `29/10000`. -/
@[gap212 "lem_datum_admissible"]
theorem datum_constraints :
    (0 : ℚ) < δ ∧ (0 : ℚ) < ϵ ∧ A₁ < 1 / 2 - ϵ ∧ B₃ - B₁ ≤ δ := by
  refine ⟨by norm_num [δ], by norm_num [ϵ], by norm_num [A₁, ϵ], by norm_num [B₁, B₃, δ]⟩

/-- **Unboundedness gives infinitude.** A set of naturals containing an element beyond every bound
is infinite. This is the step from "the GPY sum is positive for arbitrarily large `x`" to
"infinitely many `n` have two prime translates". -/
@[gap212 "lem_positivity_dhl"]
theorem infinitely_many_of_unbounded {S : Set ℕ} (h : ∀ N : ℕ, ∃ n ∈ S, N ≤ n) : S.Infinite := by
  rw [Set.infinite_coe_iff.symm.trans Set.infinite_coe_iff]
  refine Set.infinite_of_not_bddAbove ?_
  intro hbdd
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨n, hnS, hn⟩ := h (M + 1)
  exact absurd (hM hnS) (by omega)

/-- **A quotient above one gives strict inequality.** If a quotient of positive quantities exceeds
`1`, the numerator exceeds the denominator.

**This is not the sieve's central comparison.** That comparison — for all large `x` the weighted
count of prime translates exceeds the total weight, quantified over the support datum, the tensor
datum and the minorant — is `Gap212.Sieve.ratio_exceeds_one`, which `Gap212.Sieve.dhl_of_tensorData`
consumes. What is below is a division manipulation over the reals: no sums, no `ν`, no `ρ`, no
datum, no asymptotic input. -/
theorem ratio_exceeds_one {num den : ℝ} (hden : 0 < den) (h : 1 < num / den) : den < num := by
  rwa [lt_div_iff₀ hden, one_mul] at h

end Gap212.Auxiliary
