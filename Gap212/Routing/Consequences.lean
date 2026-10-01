/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Gap212.Attr
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# A located sequence has a finite discrepancy

A sequence `f : ℕ → M` is *located at the scale `N`* between the endpoints `c₀` and `c₁` when every
nonzero term of positive index satisfies `c₀ * N ≤ n ≤ c₁ * N`. Such a sequence, if it vanishes at
`0` as well, is supported in the finite range `Finset.Icc ⌈c₀ * N⌉₊ ⌊c₁ * N⌋₊`, and consequently an
unrestricted sum of `f` over a set of indices is the finite sum over that range cut by the same
condition.

Applied to the two conditions `n ≡ a [MOD d]` and `Nat.Coprime n d` and subtracted, this turns the
discrepancy
`Δ(f; d, a) = ∑_{n ≡ a (d)} f n - φ(d)⁻¹ * ∑_{(n, d) = 1} f n`,
whose two sums are unrestricted sums over `ℕ`, into
`∑_{c₀N ≤ n ≤ c₁N, n ≡ a (d)} f n - φ(d)⁻¹ * ∑_{c₀N ≤ n ≤ c₁N, (n, d) = 1} f n`,
a difference of two finite sums. An unrestricted sum of a family that is not finitely supported is
`0` by default, so this is what makes `Δ(f; d, a)` the quantity it is meant to be rather than that
default value, and no estimate stated with `Δ` can do without it. Neither hypothesis costs anything
where the discrepancy is used: there `f` is a Dirichlet convolution of sequences located at scales,
hence located at the product scale and zero at `0`.

## Main results

* `Gap212.finsum_mem_setOf_eq_sum_filter_of_support_subset`: an unrestricted sum of a function
  supported in a `Finset` `s` over the indices satisfying a decidable condition is the finite sum
  over `s` cut by that condition, of any function agreeing with it on `s`.
* `Gap212.support_subset_Icc_and_finsum_mem_eq_sum_filter_of_located`: the support inclusion, and
  the identity it forces between an unrestricted sum of `f` over a set of indices and the finite
  sum over `Finset.Icc ⌈c₀ * N⌉₊ ⌊c₁ * N⌋₊` cut by the same condition.

## Implementation notes

The range is the `Finset.Icc ⌈c₀ * N⌉₊ ⌊c₁ * N⌋₊` of naturals rather than the set
`{n | c₀ * N ≤ n ∧ n ≤ c₁ * N}` it transcribes: a sum runs over a `Finset`, and for `n ≠ 0` the
two memberships agree, by `Nat.ceil_le` and `Nat.le_floor_iff'`. At `n = 0` the range can miss the
index the set contains: `Nat.ceil_le` reads `⌈c₀ * N⌉₊ ≤ 0 ↔ c₀ * N ≤ 0`, so as soon as
`0 < c₀ * N` — the source's own regime, `0 < c₀` and `1 ≤ N` — the index `0` is outside the range
while `hloc`, which speaks only at positive indices, says nothing about it; the inclusion is then
false for `f = 1_{n = 0}`. That is why `f 0 = 0` is a hypothesis and not a convenience. The
opposite difference is free: the floor endpoint never excludes `0`, so when `c₀ * N ≤ 0` and
`c₁ * N < 0` the index `0` lies in the range but outside the set, and a range larger than the set
it transcribes only makes an inclusion easier.

The second conclusion is stated for an arbitrary decidable condition on the index rather than for
the two conditions `n ≡ a [MOD d]` and `Nat.Coprime n d` separately: neither the subtraction nor
the factor `φ(d)⁻¹` of the discrepancy plays any part in restricting the summation range, and the
source's `d ≥ 1` — which only makes `φ(d) ≠ 0` — is not needed for that restriction.

The source's `0 < c₀` and `1 ≤ N` are not hypotheses here: they make the range nonempty and bounded
away from `0`, and neither conclusion needs that, since a `Finset.Icc` of naturals is finite
whatever its endpoints and the index `0` is excluded by `f 0 = 0` rather than by positivity of
`c₀ * N`. The codomain is an arbitrary additive commutative monoid, which covers the source's `ℂ`:
the subtraction and the factor `φ(d)⁻¹` belong to the discrepancy, not to either of its two sums.
Where the source only says that `f` vanishes outside some range, the statement pins that range and
states the sum identity over it.

## References

* [1, (1.1)] and [1, Definition 2.5 (i)].
* [2, Definition 6 (i)].
-/

namespace Gap212

/-- A function on `ℕ` vanishing at `0` whose nonzero values at positive indices `n` satisfy
`a ≤ n ≤ b` is supported in `Finset.Icc ⌈a⌉₊ ⌊b⌋₊`. The index `0` is the one the location
hypothesis says nothing about, and `hf0` is what excludes it. -/
private lemma support_subset_Icc_ceil_floor {M : Type*} [Zero M] {f : ℕ → M} {a b : ℝ}
    (hloc : ∀ n ≥ (1 : ℕ), f n ≠ 0 → a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b) (hf0 : f 0 = 0) :
    Function.support f ⊆ ↑(Finset.Icc ⌈a⌉₊ ⌊b⌋₊) := fun n hn ↦
  have ⟨h₀, h₁⟩ := hloc n (Nat.one_le_iff_ne_zero.2 fun h ↦ hn (h ▸ hf0)) hn
  Finset.mem_Icc.2 ⟨Nat.ceil_le.2 h₀, Nat.le_floor h₁⟩

/-- A function `f` supported in a `Finset` `s` sums over the indices satisfying a decidable
predicate `p` to the finite sum over `s` filtered by `p` of any `g` agreeing with `f` on `s`:
outside `s` there is nothing to add, inside `s` the two summations run over the same indices, and
there `f` and `g` have the same values. The one-function case is `hfg := fun _ _ ↦ rfl`; allowing
`g ≠ f` off `s` is what lets a sum of `f` be read as a sum of a function defined only on `s`.

Mathlib has the engine `finsum_mem_eq_sum_of_subset` but neither form of this consequence. It is
the `Function.support f ⊆ ↑s` companion of `finsum_mem_eq_sum_filter`, which instead filters the
support itself. -/
public lemma finsum_mem_setOf_eq_sum_filter_of_support_subset {α M : Type*} [AddCommMonoid M]
    {f g : α → M} {s : Finset α} (hf : Function.support f ⊆ ↑s) (hfg : Set.EqOn f g ↑s)
    (p : α → Prop) [DecidablePred p] :
    ∑ᶠ i ∈ {i | p i}, f i = ∑ i ∈ s with p i, g i :=
  (finsum_mem_eq_sum_of_subset f
        (fun _ hi ↦ Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hf hi.2, hi.1⟩))
        fun _ hi ↦ (Finset.mem_filter.1 hi).2).trans <|
    Finset.sum_congr rfl fun _ hi ↦ hfg (Finset.mem_filter.1 hi).1

/-- **A located sequence has a finite discrepancy.** Let `f` be located at the scale `N` between
the endpoints `c₀` and `c₁` — every nonzero term of positive index has `c₀ * N ≤ n ≤ c₁ * N` — and
let `f 0 = 0`. Then `f` is supported in the finite range `Finset.Icc ⌈c₀ * N⌉₊ ⌊c₁ * N⌋₊`, and
hence, for every decidable condition on the index, the unrestricted sum of `f` over the indices
satisfying it is the finite sum over that range of those satisfying it.

Taking the condition to be `n ≡ a [MOD d]` and then `Nat.Coprime n d`, and subtracting `φ(d)⁻¹`
times the second identity from the first, expresses the discrepancy of `f` at the modulus `d` and
the class `a` as a difference of two sums over `c₀ * N ≤ n ≤ c₁ * N`. -/
@[gap212 "lem_finite_support_discrepancy"]
public theorem support_subset_Icc_and_finsum_mem_eq_sum_filter_of_located
    {M : Type*} [AddCommMonoid M] {f : ℕ → M} {c₀ c₁ N : ℝ}
    (hloc : ∀ n ≥ (1 : ℕ), f n ≠ 0 → c₀ * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ c₁ * N) (hf0 : f 0 = 0) :
    Function.support f ⊆ ↑(Finset.Icc ⌈c₀ * N⌉₊ ⌊c₁ * N⌋₊) ∧
      ∀ (p : ℕ → Prop) [DecidablePred p],
        ∑ᶠ n ∈ {n | p n}, f n = ∑ n ∈ Finset.Icc ⌈c₀ * N⌉₊ ⌊c₁ * N⌋₊ with p n, f n :=
  have hsupp := support_subset_Icc_ceil_floor hloc hf0
  ⟨hsupp, fun p _ ↦ finsum_mem_setOf_eq_sum_filter_of_support_subset hsupp (fun _ _ ↦ rfl) p⟩

end Gap212
