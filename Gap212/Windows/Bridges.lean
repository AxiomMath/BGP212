/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Equidistribution.Basic
public import Gap212.Sieve.Support
public import Gap212.Tuple.H45
public import Gap212.Support.Hereditary
public meta import Gap212.Attr

/-!
# Small bridges the assembly needs

Short results sitting between pieces already formalized: the level of a band pair, the `B`-row
bound from its first entry, additivity of the discrepancy numerator, and the two halves of the
`H₄₅` admissibility argument.

## Main results

* `Gap212.Bridges.omegaMax`: the level `ω(j,j')` of a band pair.
* `Gap212.Bridges.brow_from_first`: `B_{j,m} ≤ B_{j,1} + (m-1)δ`.
* `Gap212.Bridges.discrepancy_numerator_additive`: the discrepancy is additive in the sequence.
* `Gap212.Bridges.h45_small_primes`, `h45_large_primes`: the two halves of admissibility, the
  first a finite check per prime up to 43, the second pigeonhole.
-/

@[expose] public section

namespace Gap212.Bridges

open Finset

/-- **The level of a band pair**, `ω(j,j') = (A_j + A_{j'})/2 - 1/4`. It is the exponent placing a
modulus generated at `(j,j')` inside `[1, x^{1/2 + 2ω}]`. -/
@[gap212 "def_omega_max"]
noncomputable def omegaMax (p : SupportParams) (j j' : Fin p.n) : ℝ :=
  (p.A j.succ + p.A j'.succ) / 2 - 1 / 4

/-- **The `B`-row from its first entry**: `B_{j,1+d} ≤ B_{j,1} + dδ`, the `r = 1` case of the row's
step bound. Stated in the `1 + d` form the iteration produces, which is how consumers index it. -/
theorem brow_from_first (p : SupportParams) (j : Fin p.n) (d : ℕ) :
    p.B j (1 + d) ≤ p.B j 1 + d * p.δ :=
  p.B_step_iterate j le_rfl d

/-- **The discrepancy numerator is additive in the sequence.** Both sums are linear in `f`, and so
is multiplication by `1/φ(q)`; the discrepancy itself is the norm of this difference, so the
triangle inequality applies to it through this identity. -/
theorem discrepancy_numerator_additive (f g : ℕ → ℝ → ℂ) (x : ℝ) (a q : ℕ) :
    ((∑ n ∈ dyadic x with n ≡ a [MOD q], (f n x + g n x)) -
        (1 / (Nat.totient q : ℂ)) * ∑ n ∈ dyadic x with Nat.Coprime n q, (f n x + g n x)) =
      ((∑ n ∈ dyadic x with n ≡ a [MOD q], f n x) -
          (1 / (Nat.totient q : ℂ)) * ∑ n ∈ dyadic x with Nat.Coprime n q, f n x) +
        ((∑ n ∈ dyadic x with n ≡ a [MOD q], g n x) -
          (1 / (Nat.totient q : ℂ)) * ∑ n ∈ dyadic x with Nat.Coprime n q, g n x) := by
  simp only [Finset.sum_add_distrib]
  ring

/-- **No prime obstructs `H₄₅`, for the small primes.** For each prime the reductions of the 45
elements omit a class; `Gap212.admissible_H45` is the finite verification, and for `p ≤ 43` that
verification is the content, since the pigeonhole bound does not reach those primes. -/
@[gap212 "lem_h45_small_primes"]
theorem h45_small_primes {p : ℕ} (hp : p.Prime) :
    ∃ a < p, ∀ h ∈ H45, ¬ (h ≡ a [MOD p]) :=
  Gap212.admissible_H45.exists_lt_forall_not_modEq hp

/-- **No prime above 45 obstructs `H₄₅`.** Its image modulo `p` has at most `#H₄₅ = 45` elements,
so for `p > 45` some residue class is missed. This is pigeonhole and needs no computation, which is
why the finite check only has to run over the primes up to 43. -/
@[gap212 "lem_h45_large_primes"]
theorem h45_large_primes {p : ℕ} (hp : H45.card < p) :
    ∃ a < p, ∀ h ∈ H45, h % p ≠ a :=
  Finset.exists_lt_forall_mod_ne_of_card_lt hp

end Gap212.Bridges
