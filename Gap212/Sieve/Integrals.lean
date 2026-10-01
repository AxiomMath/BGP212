/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Definitions
public import Gap212.Sieve.Support
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The key integrals `I`, `J`, `K`

Definition 6 of Stadlmann, *Bounded gaps between primes* (§2.1). These are the three functionals
whose ratio the numerical certificate must push above `1`, per inequality (2.1) of Proposition 1.

Throughout, the ambient dimension is written `m + 1` rather than `k`, because `J` and `K` split off
the last coordinate: `J`'s integrand pairs `F(t₁,…,t_m, t_k)` against `F(t₁,…,t_m, t'_k)` with two
*separate* last coordinates, so its natural domain is `(Fin m → ℝ) × ℝ × ℝ`. The certificate
`Gap212.Gap212Certificate` is at `k = 45`, i.e. `m = 44`.

## An ill-formedness in the paper's `K`

Definition 6's display for `K` carries three constraints — including one on `t'_k` — but its
integrand is `F(t₁,…,t_k)²` and its measure is `dt₁ ⋯ dt_k`. So `t'_k` is constrained without ever
being integrated, and the display does not define a number. The same defect is repeated in the
`M₂` display of §5.

We take the reading forced by the paper's *proof*, where `K` is unambiguous: `K_i(F, G; B)` in the
proof of Lemma 2.2 integrates over `{∑_{s ≠ i} t_s > B}` against `F·G` with measure `dt₁ ⋯ dt_k`
and no `t'_k` at all. So `Kregion` drops the `t'_k` constraint.

The reading of `K` does not affect `H₁ ≤ 212`: at `ξ₂ = 2/5` the minorant degenerates to `1_ℙ`
and `c₂ = 0`, and `K` enters inequality (2.1) only through the term `-k c₂ K`.

## Main definitions

Declared in `Gap212.Definitions`:

* `Gap212.Iint`: `I(F) = ∫_{T_k} F²`.
* `Gap212.Jint`: `J(F)`, the double-last-coordinate functional.
* `Gap212.Kint`: `K(F)`, on the reading above.
-/

@[expose] public section

namespace Gap212

open MeasureTheory

variable (p : SupportParams)

end Gap212
