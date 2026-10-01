/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Definitions
public import Gap212.Sieve.Integrals

/-!
# The numerical certificate

Inequality (2.1) of Proposition 1 in Stadlmann, *Bounded gaps between primes* (§2.2): the existence
of a symmetric, square-integrable `F` supported on `T_k(δ, A, B, ε)` with

`(k(1-c₁) J(F) - k c₂ K(F)) / I(F) > 1`.

The library takes this inequality as a hypothesis: it is not proved here. The paper obtains such
an `F` by computing exact rational matrices `M₁`, `M₂` over the relevant support and extracting an
eigenvector.

## Why the ratio is stated as a product

Writing the conclusion as `I F ≠ 0 ∧ ... > I F` rather than as a quotient `> 1` avoids the
division, which in Lean is total and returns `0` at `I F = 0`. As a quotient the inequality is
*false* when `I F = 0` rather than meaningless; stated multiplicatively, the non-degeneracy
`0 < I F` is explicit. `0 < I F` also rules out the
degenerate `F = 0`, for which the paper's ratio is `0/0`.

## Main definitions

Declared in `Gap212.Definitions`:

* `Gap212.Symmetric`: invariance of `F` under permutations of its coordinates.
* `Gap212.Certificate`: inequality (2.1), for general parameters and `c₁`, `c₂`.
* `Gap212.gap212Params`: the support datum of the main theorem, in Stadlmann's physical scale.
* `Gap212.Gap212Certificate`: the certificate at those parameters, `k = 45`, `c₁ = c₂ = 0`.

Declared here:

* `Gap212.gap212ParamsPointA`: the Point A datum, a different support.
-/

@[expose] public section

namespace Gap212

open MeasureTheory

/-- **The Point A datum**, the support at which the packing conditions are stated: `ε = 0.0085`,
`δ = 0.0179`, one stratum with `A = (-ε, 0.2565)`, and `B₁,₁ = B₁,₂ = 0.155` with `B₁,ₘ = 0.17`
for `m ≥ 3`.

It is a different support from `Gap212.gap212Params`, the datum of the main theorem;
`Gap212.Routing.PointABridge` identifies its fields with the exact rationals of `Gap212.PointA`. -/
noncomputable def gap212ParamsPointA : SupportParams where
  δ := 0.0179
  ε := 0.0085
  n := 1
  A := fun i ↦ (i.val : ℝ) * 0.265 - 0.0085
  B := fun _ m ↦ if m = 0 then 0 else if m ≤ 2 then 0.155 else 0.17
  δ_pos := by norm_num
  ε_pos := by norm_num
  n_pos := by norm_num
  A_zero := by norm_num
  A_mono := by
    intro i j hij
    have : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    simp only
    linarith
  A_last := by norm_num [Fin.last]
  B_zero := fun _ ↦ by norm_num
  B_lt := by
    intro j m hm
    have h0 : ¬ m = 0 := by omega
    simp only [if_neg h0]
    split_ifs <;> norm_num
  B_mono := by
    intro j m hm
    have h0 : ¬ m = 0 := by omega
    have h1 : ¬ m + 1 = 0 := by omega
    simp only [if_neg h0, if_neg h1]
    split_ifs <;> first | omega | norm_num
  B_step := by
    intro j m hm
    have h0 : ¬ m = 0 := by omega
    have h1 : ¬ m + 1 = 0 := by omega
    simp only [if_neg h0, if_neg h1]
    split_ifs <;> first | omega | norm_num

end Gap212
