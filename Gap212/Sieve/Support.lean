/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Definitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Interval.Finset.Nat

/-!
# The stratified support `T_k(δ, A, B, ε)`

Definition 1 ("Simplex subset") of Stadlmann, *Bounded gaps between primes* (§2.1). This region
replaces Polymath's `ε`-enlarged simplex as the support of the functions in the GPY optimization
problem, and enlarging it is what buys `H₁ ≤ 212`.

A point `t ∈ [0,1]^k` lies in `T_k` when, for some stratum `j`, the coordinate sum `∑ tᵢ` falls in
the window `[A_{j-1} + ε, A_j + ε)` *and* the sum of the coordinates exceeding `δ` is at most
`B_{j,m}`, where `m` counts those large coordinates.

## The role of the monotonicity condition on `B`

`SupportParams.B_lt`, `B_mono` and `B_step` encode `δ < B_{j,m} ≤ B_{j,m+1} ≤ B_{j,m} + δ`. The
paper calls this "quite important" and uses it repeatedly: it is what makes
`∑_{i ∈ I} tᵢ ≤ B_{j,|I|}` for `I = {i : tᵢ > δ}` imply `∑_{i ∈ I'} tᵢ ≤ B_{j,|I'|}` for every
`I' ⊆ I` — dropping a coordinate loses at least `δ` from the sum but at most `δ` from the bound.

## Main definitions

Declared in `Gap212.Definitions`.

* `Gap212.SupportParams`: admissible `(δ, ε, n, A, B)` per Definition 1.
* `Gap212.T`: the support itself.
-/

@[expose] public section

namespace Gap212

open Real

namespace SupportParams

variable (p : SupportParams)

open Classical in
/-- The set `I = {i : tᵢ ≥ δ}` of rough coordinates, as a `Finset`.

The non-strict sibling of `Gap212.SupportParams.large`. A stratum constrains the coordinates
*exceeding* `δ`; the moduli a support generates constrain the rough factors, which are the ones of
size *at least* `x^δ`. Anything transporting the second constraint reads this set, not `large`. -/
noncomputable def roughIdx (k : ℕ) (t : Fin k → ℝ) : Finset (Fin k) :=
  {i ∈ Finset.univ | p.δ ≤ t i}

end SupportParams

/-- Every point of the support lies in the unit cube. -/
theorem mem_unitCube_of_mem_T {p : SupportParams} {k : ℕ} {t : Fin k → ℝ} (ht : t ∈ T p k)
    (i : Fin k) : t i ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
  exact hj.1 i

end Gap212
