/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Gap212.Attr
public import Gap212.Definitions
public import Gap212.Routing.Consequences
public import Gap212.Routing.Defs.Equidistribution

/-!
# The prime indicator on the dyadic block

The prime indicator `1_ℙ : ℕ → ℂ`, worth `1` at a prime natural number and `0` elsewhere, has
infinite support, so at `1_ℙ` the two sums of the unrestricted discrepancy
`Δ(f; d, a) = ∑ᶠ_{n ≡ a (d)} f n - φ(d)⁻¹ * ∑ᶠ_{(n, d) = 1} f n`
are not finite sums and carry no information: an unrestricted sum of a family that is not finitely
supported takes a default value, so an estimate stated at `1_ℙ` would appear to typecheck while
asserting nothing. Cutting the indicator down to the dyadic block
`𝒟(x) = {n : ⌈x⌉ ≤ n ≤ ⌊2x⌋}` repairs this: the restricted sequence `1_ℙ^{(x)}` agrees with `1_ℙ`
on `𝒟(x)` and vanishes off it, so its support is contained in a finite set and both sums are
finite.

The dyadic discrepancy `Δ_𝒟(f; x, d, a) = Gap212.sumErrorDyadic x f d a` instead cuts both of
its sums to the block, so it is a difference of finite sums for every sequence. The two quantities
differ in general, but `Δ(f; d, a) = Δ_𝒟(g; x, d, a)` as soon as `f` is supported in the block and
`g` agrees with `f` there, because a sum of `f` over a set of indices is then the sum over the
indices of the block lying in that set, and the cutting conditions `n ≡ a (d)` and `(n, d) = 1` and
the factor `φ(d)⁻¹` are the same on the two sides. At `f = 1_ℙ^{(x)}` and `g = 1_ℙ` the identity
reads `Δ(1_ℙ^{(x)}; d, a) = Δ_𝒟(1_ℙ; x, d, a)`, so it identifies the unrestricted discrepancy that
the assumed Harman reduction bounds, summed over a family of moduli, with the discrepancy of the
primes of `[x, 2x]` in residue classes that the sieve counts.

## Main definitions

Declared in `Gap212.Definitions`, which carries the challenge file's own text.

* `Gap212.primeInterval`: the prime indicator restricted to the dyadic block, `1_ℙ^{(x)}`.

## Main results

* `Gap212.sumError_eq_sumErrorDyadic_of_support_subset`: the unrestricted
  discrepancy of a sequence supported in the dyadic block is the dyadic discrepancy of any sequence
  agreeing with it there.
* `Gap212.sumError_primeInterval_eq_sumErrorDyadic`: its instance
  at `1_ℙ^{(x)}`, `Δ(1_ℙ^{(x)}; d, a) = Δ_𝒟(1_ℙ; x, d, a)`.

## Implementation notes

The restriction is `Set.indicator` at the coercion of `Gap212.dyadic x`, which makes the two
clauses of the source's definition, `primeInterval_of_mem` and `primeInterval_of_notMem`, and
the support inclusion `support_primeInterval_subset` that the identity below asks for,
one-line consequences of the Mathlib API rather than unfoldings; a definition by
`if n ∈ dyadic x then _ else 0` would state the same function and carry none of that. The prime
indicator itself is written inline as `if n.Prime then 1 else 0`, there being nothing to say about
it that `Nat.Prime` does not already say; Mathlib has no indicator of the primes, and
`Nat.primeCounting` counts them instead. The codomain is `ℂ` rather than an arbitrary semiring,
since the discrepancy and the equidistribution estimates all fix `ℕ → ℂ`, and the scale comes
first, so that `primeInterval x` is the sequence.

The support hypothesis is stated as `Function.support f ⊆ ↑(dyadic x)`, a coercion of a `Finset`
rather than `⊆ dyadic x`, because that is the shape in which
`Gap212.support_subset_Icc_and_finsum_mem_eq_sum_filter_of_located` and
`support_primeInterval_subset` deliver it. The other hypothesis of that upstream lemma is
`hf0 : f 0 = 0`, and `primeInterval_zero` is exactly it for `1_ℙ^{(x)}` at a positive scale,
read at `c₀ = 1`, `c₁ = 2`, `N = x`, where the lemma's range `Finset.Icc ⌈1 * x⌉₊ ⌊2 * x⌋₊` is
`dyadic x` up to `one_mul`.

One statement covers both displays of the source. The general identity
`Δ(f; d, a) = Δ_𝒟(f; x, d, a)` is the case `g = f`, whose agreement hypothesis is `fun _ _ ↦ rfl`;
the prime-indicator identity is the case `f = primeInterval x`, `g = 1_ℙ`. Separating the two
functions is what makes the second an instance rather than a corollary: the restriction changes the
sequence only outside the block, where the dyadic discrepancy does not look, so no sum needs to be
re-cut for it.

Neither `x ≥ 3` nor `d ≥ 1` is asked of the identity, though the source has both. The rôle of
`x ≥ 3` is to put `0` outside the block, which `x > 0` already does, and the index `0` needs no
exclusion here in any case, being treated alike on the two sides; the rôle of `d ≥ 1` is to make
`φ(d)` nonzero, and the factor `φ(d)⁻¹` is carried untouched from one side of the equation to the
other. So the identity holds at `d = 0`, at `d = 1`, and at the degenerate scales `x ≤ 0`, where
the truncated block is `𝒟(x) = {0}`.

## References

* [1, (1.1)], for the unrestricted discrepancy.
* [2, Definition 3] and the conclusion of [2, Proposition 2], where the discrepancy bounded is the
  one at the primes of `[x, 2x]`.
-/

@[expose] public section

namespace Gap212

attribute [gap212 "not_prime_indicator"] primeIndicator
attribute [gap212 "def_prime_interval"] primeInterval

/-- On the dyadic block, `1_ℙ^{(x)}` is the prime indicator. -/
theorem primeInterval_of_mem {x : ℝ} {n : ℕ} (hn : n ∈ dyadic x) :
    primeInterval x n = primeIndicator n :=
  if_pos hn

/-- Off the dyadic block, `1_ℙ^{(x)}` vanishes. -/
theorem primeInterval_of_notMem {x : ℝ} {n : ℕ} (hn : n ∉ dyadic x) :
    primeInterval x n = 0 :=
  if_neg hn

/-- At a positive scale `1_ℙ^{(x)}` vanishes at `0`: the block `𝒟(x)` then starts at `⌈x⌉ ≥ 1`. -/
theorem primeInterval_zero {x : ℝ} (hx : 0 < x) : primeInterval x 0 = 0 :=
  primeInterval_of_notMem <| by simp [dyadic, Nat.ceil_eq_zero, hx.not_ge]

/-- `1_ℙ^{(x)}` is supported in the dyadic block. -/
theorem support_primeInterval_subset (x : ℝ) :
    Function.support (primeInterval x) ⊆ ↑(dyadic x) := by
  intro n hn
  by_contra h
  exact hn (primeInterval_of_notMem h)

/-- **On the dyadic block the two discrepancies agree.** Let `f` be supported in the dyadic block
`𝒟(x)` and let `g` agree with `f` there. Then the unrestricted discrepancy of `f` at the modulus
`d` and the class `a` is the dyadic discrepancy of `g`.

At `g = f` this is `Δ(f; d, a) = Δ_𝒟(f; x, d, a)` for a sequence vanishing off the block; at
`f = primeInterval x` and `g = primeIndicator` it is `Δ(1_ℙ^{(x)}; d, a) = Δ_𝒟(1_ℙ; x, d, a)`.
The general form is the one the sieve consumes, for an arbitrary minorant supported in the block.
Neither `x ≥ 3` nor `d ≥ 1` is needed. -/
@[gap212 "lem_prime_interval_discrepancy"]
theorem sumError_eq_sumErrorDyadic_of_support_subset {f g : ℕ → ℂ}
    {x : ℝ} (hf : Function.support f ⊆ ↑(dyadic x)) (hfg : Set.EqOn f g ↑(dyadic x)) (d a : ℕ) :
    sumError f d a = sumErrorDyadic x g d a := by
  rw [sumError, sumErrorDyadic,
    finsum_mem_setOf_eq_sum_filter_of_support_subset hf hfg (· ≡ a [MOD d]),
    finsum_mem_setOf_eq_sum_filter_of_support_subset hf hfg (Nat.Coprime · d)]

/-- **The prime discrepancy on `[x, 2x]`.** The unrestricted discrepancy of the restricted prime
indicator is the dyadic discrepancy of the prime indicator:
`Δ(1_ℙ^{(x)}; d, a) = Δ_𝒟(1_ℙ; x, d, a)`. This is what the Harman reduction's conclusion gives the
sieve. -/
theorem sumError_primeInterval_eq_sumErrorDyadic (x : ℝ) (d a : ℕ) :
    sumError (primeInterval x) d a = sumErrorDyadic x primeIndicator d a :=
  sumError_eq_sumErrorDyadic_of_support_subset
    (support_primeInterval_subset x) (fun _ ↦ primeInterval_of_mem) d a

end Gap212
