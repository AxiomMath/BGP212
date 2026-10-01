/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.GPYDefs
public import Mathlib.NumberTheory.Divisors
public meta import Gap212.Attr

/-!
# The divisor sums: the normalization, the reduced supports, and the residue averaging

The vocabulary of the two divisor-sum evaluations the sieve's numerator and denominator reduce to:
the common normalization `𝓒_x` both asymptotics are stated against, the support condition on a pair
of divisor-weight families with one coordinate removed, and the two arithmetic weights the
common-residue averaging pays — how many divisor tuples generate a given modulus, and how rare the
residue class each of them needs is.

## The removed coordinate

The prime numerator drops one coordinate: the shift `n + h_{i₀}` is the one asked to be prime, so
its divisor sum collapses and the remaining `k - 1` coordinates carry the divisor weights. Those
coordinates are indexed by `Fin m` at `k = m + 1`, read through `Fin.succAbove i₀`, and a vector of
them is extended back to `ℝ^k` by `Fin.insertNth i₀ 0` — putting `0` in the removed slot, which is
the value the collapsed coordinate contributes to every support condition.

## Main definitions

* `Gap212.GPY.calC`: the normalization `𝓒_x`.
* `Gap212.GPY.IsReducedRetreat`: the asymmetric support condition on a reduced pair of families.
* `Gap212.GPY.residueWeight`: the combined multiplicity-and-rarity weight `v(q)`.
* `Gap212.GPY.IsTupleResidue`: the congruences cutting out a divisor tuple's residue.
-/

@[expose] public section

namespace Gap212.GPY

open Finset

/-- **The sieve normalization** `𝓒_x = x W(x)^{k-1} / (φ(W(x))^k (log x)^k)`, written at
`k = m + 1` so that the exponent `k - 1` is the literal `m`.

Both divisor-sum asymptotics are stated against this one quantity: the denominator's `k` sieve
factors give `B_x^{-k} = (W/φ(W))^k (log x)^{-k}` against a density `x/W`, and in the numerator the
prime density `x/log x` and the factor `1/φ(W)` combine with the remaining `k - 1` sieve factors to
the same thing. That is why no extra `log x`, no `W/φ(W)` and no factor `k` survives in the
ratio. -/
@[gap212 "def_calC"]
noncomputable def calC (m : ℕ) (x : ℝ) : ℝ :=
  x * (W x : ℝ) ^ m / (((W x).totient : ℝ) ^ (m + 1) * Real.log x ^ (m + 1))

/-- **A reduced retreated pair**: two families of profiles on the coordinates other than `i₀`, the
unprimed one confined to the retreat region *and* to the marginal region, the primed one only to
the retreat region — each read on the vector extended by `0` at the removed coordinate `i₀`.

The asymmetry is the asymmetry of the generated moduli: the unprimed side is held to the node
`A_j - ε` and the primed side only to `A_{j'} + ε`. It is what removing one coordinate buys, and it
is the reason both mixed bounds of `Qgen` can be met at once. -/
@[gap212 "def_reduced_retreat"]
def IsReducedRetreat (p : SupportParams) (m : ℕ) (j j' : Fin p.n) (ε₀ : ℝ) (i₀ : Fin (m + 1))
    (F G : Fin m → ℝ → ℝ) : Prop :=
  ∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) →
    ((∏ i, F i (t i)) ≠ 0 →
      i₀.insertNth 0 t ∈ retreatRegion p (m + 1) j ε₀ ∧ t ∈ marginalRegion p m j ε₀) ∧
    ((∏ i, G i (t i)) ≠ 0 → i₀.insertNth 0 t ∈ retreatRegion p (m + 1) j' ε₀)

/-- **The residue weight** `v(q) = 5808^{ω(q/W(x))}`, where `ω` counts distinct prime factors.

The base is `3(k-1)·(k-1) = 132·44` at `k = 45`: the first factor bounds how many divisor tuples
generate a given modulus, the second is the reciprocal probability that a CRT sample lands in the
class such a tuple needs. It is below `8192 = 2^13`, which is what keeps the combined weight a
*fixed* power of the divisor function on squarefree moduli. -/
@[gap212 "def_residue_weight"]
noncomputable def residueWeight (x : ℝ) (q : ℕ) : ℕ := 5808 ^ (q / W x).primeFactors.card

/-- **The residue of a divisor tuple**: `a` is a tuple residue when it is `b + h_{i₀}` modulo the
pre-sieving modulus and `h_{i₀} - h_i` modulo `[d_i, d'_i]` for every remaining coordinate.

These are the congruences an `n` with `n ≡ b (W)` and `d_i, d'_i ∣ n + h_i` forces on `n + h_{i₀}`,
which is the integer the prime discrepancy is taken at. The tuple residue is the unique class
modulo `q = W(x)∏[d_i,d'_i]`; uniqueness (and existence) is the Chinese remainder theorem under the
pairwise coprimality assumed here, so it is a companion lemma and not part of this definition,
which states only the congruences that characterize the class. -/
@[gap212 "def_tuple_residue"]
def IsTupleResidue {m : ℕ} (x : ℝ) (b : ℕ) (h : Fin (m + 1) → ℕ) (i₀ : Fin (m + 1))
    (d d' : Fin m → ℕ) (a : ℕ) : Prop :=
  a ≡ b + h i₀ [MOD W x] ∧
    ∀ i : Fin m, (a : ℤ) ≡ (h i₀ : ℤ) - (h (i₀.succAbove i) : ℤ) [ZMOD ((d i).lcm (d' i) : ℕ)]

end Gap212.GPY
