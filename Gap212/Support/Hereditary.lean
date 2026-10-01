/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Support
public import Mathlib.Tactic.Ring
public meta import Gap212.Attr

/-!
# The hereditary rough-mass bound

The support `T_k(δ, A, B, ε)` caps the mass carried by the *rough* coordinates — those exceeding
`δ` — at `B_{j,m}`, where `m` is how many of them there are. This cap is inherited by every
subset of the rough coordinates:

    I' ⊆ I = {i : tᵢ > δ}  ⟹  ∑_{i ∈ I'} tᵢ ≤ B_{j,|I'|}.

[2] calls the monotonicity condition `δ < B_{j,m} ≤ B_{j,m+1} ≤ B_{j,m} + δ` that makes this
work "quite important", and uses the consequence repeatedly — in the sieve realization, in
identifying which divisor coordinates can contribute, and in placing the generated moduli in `Q*`.

## Why it is true

Dropping a rough coordinate loses *more* than `δ` from the sum (each is `> δ` by definition of
rough) but *at most* `δ` from the bound (that is the `B_{j,m+1} ≤ B_{j,m} + δ` half of the
condition). So the bound degrades no faster than the mass does. Formally, deleting `m - r`
coordinates loses at least `(m - r)δ` of mass, while `B_step_iterate` gives
`B_{j,m} ≤ B_{j,r} + (m - r)δ`; subtracting the two gives the claim.

## The empty subset

The lemma is stated for `1 ≤ |I'|`. `SupportParams` constrains `B j m` only for `m ≥ 1`, so `B j 0`
is unconstrained and could be negative — the `|I'| = 0` case would need `0 ≤ B_{j,0}` as an extra
hypothesis. Every use is at a nonempty subset, so requiring `1 ≤ |I'|` loses nothing.

## Main results

* `Gap212.SupportParams.B_step_iterate`: `B_{j,r+d} ≤ B_{j,r} + d·δ`.
* `Gap212.SupportParams.sum_le_B_of_subset_large`: the hereditary bound, on a stratum.
* `Gap212.mem_large_iff`: unfolding of the rough-coordinate set.
-/

@[expose] public section

namespace Gap212

open Finset

/-- A coordinate is rough exactly when it exceeds `δ`. -/
theorem mem_large_iff {p : SupportParams} {k : ℕ} {t : Fin k → ℝ} {i : Fin k} :
    i ∈ p.large k t ↔ p.δ < t i := by
  simp [SupportParams.large]

namespace SupportParams

variable {p : SupportParams}

/-- **Iterating the step condition.** `B_{j,m+1} ≤ B_{j,m} + δ` compounds: raising the index by `d`
raises the cap by at most `d·δ`. Requires `1 ≤ r`, which is where `B` is constrained. -/
@[gap212 "lem_brow_step"]
theorem B_step_iterate (j : Fin p.n) {r : ℕ} (hr : 1 ≤ r) (d : ℕ) :
    p.B j (r + d) ≤ p.B j r + d * p.δ := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [← add_assoc]
      push_cast
      linarith [p.B_step j (r + d) (by omega)]

/-- **The hereditary rough-mass bound.** If `t` lies in the `j`-th stratum and `I'` is a nonempty
set of rough coordinates of `t`, then the mass of `I'` is capped by `B_{j,|I'|}`.

This bound is the reason the monotonicity condition on `B` is imposed. -/
theorem sum_le_B_of_subset_large {k : ℕ} {j : Fin p.n} {t : Fin k → ℝ}
    (ht : t ∈ p.stratum k j) {I' : Finset (Fin k)} (hsub : I' ⊆ p.large k t)
    (hne : 1 ≤ I'.card) :
    ∑ i ∈ I', t i ≤ p.B j I'.card := by
  classical
  set I := p.large k t with hI
  set r := I'.card with hr
  -- The number of dropped coordinates. Working with `d` rather than `m - r` avoids
  -- truncated subtraction throughout.
  set d := (I \ I').card with hd
  -- The stratum's own cap, on the full rough set.
  have hcap : ∑ i ∈ I, t i ≤ p.B j I.card := ht.2.2
  -- Split the rough mass into `I'` and the coordinates dropped.
  have hsplit : ∑ i ∈ I \ I', t i + ∑ i ∈ I', t i = ∑ i ∈ I, t i := sum_sdiff hsub
  -- The same split for cardinalities.
  have hcard : d + r = I.card := card_sdiff_add_card_eq_card hsub
  -- Every dropped coordinate is rough, so the dropped mass is at least `d·δ`.
  have hdrop : (d : ℝ) * p.δ ≤ ∑ i ∈ I \ I', t i := by
    simpa [nsmul_eq_mul] using
      card_nsmul_le_sum _ _ _ fun i hi ↦ (mem_large_iff.mp (mem_sdiff.mp hi).1).le
  -- The cap degrades by at most `d·δ` when the index drops from `I.card` to `r`.
  have hchain : p.B j I.card ≤ p.B j r + (d : ℝ) * p.δ := by
    rw [← hcard, add_comm d r]
    exact B_step_iterate j hne d
  linarith

end SupportParams

/-- The hereditary bound as it is used downstream: a nonempty subset of the rough coordinates of a
point of the support `T` satisfies the cap at its own cardinality, for the stratum containing
it. -/
theorem sum_le_B_of_mem_T {p : SupportParams} {k : ℕ} {t : Fin k → ℝ} (ht : t ∈ T p k)
    {I' : Finset (Fin k)} (hsub : I' ⊆ p.large k t) (hne : 1 ≤ I'.card) :
    ∃ j : Fin p.n, ∑ i ∈ I', t i ≤ p.B j I'.card := by
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
  exact ⟨j, SupportParams.sum_le_B_of_subset_large hj hsub hne⟩

end Gap212
