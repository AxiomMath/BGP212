/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Gap212.Attr
public import Mathlib.Tactic.NormNum.Ineq

/-!
# The scalar conditions on the Harman parameters

Factor extraction reaches every generated modulus above `x^(1/2 - ε₁)`, and the bilinear input
reaches every modulus up to `x^(1/2) (log x)^(-B)`; for large `x` the two ranges overlap, so
together they carry the equidistribution that the assumed reduction of `1_ℙ` to the class
`ℋ(ξ₁, ξ₂, ξ₃)` demands. That reduction is available only at an admissible triple, and this file
supplies the admissibility of the chosen triple.

[2, Proposition 2] asks of `(ξ₁, ξ₂, ξ₃)`, beyond `ξᵢ ∈ (0, 1)`, five scalar inequalities,

`2ξ₁ + 3ξ₂ < 2`,  `ξ₂ ≤ ξ₃`,  `ξ₁ + 9ξ₂ < 4`,  `2ξ₁ + ξ₂ > 1`,  `17ξ₂ < 7`,

each of which its proof introduces at a named step of the numerical argument it generalises — the
one of Baker–Irving and of the author's earlier paper, whose explicit exponents it replaces
throughout by the three variables. The first is the Buchstab-decomposition assumption
`2(1 - ξ₁ - ξ₂) > ξ₂`, which makes the cofactor of the first decomposition sum prime, and which the
proof re-uses under the two further spellings `1 - ξ₁ - ξ₂/2 > ξ₂` and `ξ₂/2 < 1 - ξ₁ - ξ₂`. The
second is what lets the Type III estimate be applied inside the treatment of that sum. The third
rearranges `1 - 4(1 - 2ξ₂) < 1 - ξ₁ - ξ₂`, bounding the mass the small exponents carry there. The
fourth rearranges `(1 - ξ₂)/2 > 1 - ξ₁ - ξ₂`, which drops the ordering condition `α₂ < α₁` in the
treatment of the third sum. The fifth rearranges `2(8ξ₂ - 3) < 1 - ξ₂`, the last requirement of
that treatment, and it is the strongest member of the chain
`17ξ₂ < 7 → 12ξ₂ < 5 → 7ξ₂ < 3 → 16ξ₂ < 7`, whose three weaker links the same proof also invokes
separately; that is why the list of five is complete.

At `(ξ₁, ξ₂, ξ₃) = (19/50, 2/5, 2/5)` all five hold: `2ξ₁ + 3ξ₂ = 49/25`, `ξ₁ + 9ξ₂ = 199/50`,
`2ξ₁ + ξ₂ = 29/25` and `17ξ₂ = 34/5`, with slacks `1/25`, `0`, `1/50`, `4/25` and `1/5`. Two are
worth naming. The second is attained, `2/5` being the least `ξ₃` admissible at this `ξ₂`. And
`ξ₂ = 2/5` is the endpoint at which the minorant of that proposition degenerates to the prime
indicator: `1 - 2ξ₂ ≥ 1/5` there, so every exponent in either exceptional Buchstab sum exceeds
`1/5`, while each of those sums also confines a pair of its exponents to a sum below `ξ₂`; at
`ξ₂ = 2/5` that pair would have to satisfy both `α, α' > 1/5` and `α + α' < 2/5`. Both sums are
therefore empty, `ρ(·; x) = 1_ℙ`, and neither a density loss nor a pointwise penalty is incurred:
the certificate may be taken with `c₁ = c₂ = 0`.

## Main results

* `Gap212.harman_scalar_conditions_at_datum`: the five inequalities hold at `(19/50, 2/5, 2/5)`.

## Implementation notes

The triple enters as three equations on variables rather than as literals substituted into the
conclusion. The two forms are interderivable, and the equational one keeps the three roles legible:
read at the literals, `ξ₂ ≤ ξ₃` is `2/5 ≤ 2/5`, in which nothing records that the two sides are the
Type II and Type III parameters and that the inequality is the one binding them.

The inequalities are stated over an arbitrary linearly ordered field rather than over `ℝ` alone.
The `ξᵢ` of [2] are exponents of `x` and so real, and the reduction they license,
`Gap212.HarmanReduction`, takes them real; but nothing in these five comparisons of numerals uses
more than a characteristic-zero order, and the project carries the same triple twice — as reals in
the reduction, and as exact rationals in the arithmetic bookkeeping of the chosen datum. One
statement serves both, `ℝ` and `ℚ` being instances.

The standing `ξ₁, ξ₂, ξ₃ ∈ (0, 1)` of [2] is not conjoined: it holds at the triple, but
`Gap212.HarmanReduction` imposes no range condition, so it is no part of what admissibility is
here. Nor does the support datum appear, these five constraining the triple alone; datum and triple
meet only in `Gap212.Gap212HarmanReduction`, the specialization these conditions license, which
fixes both.

## References

* [2, Proposition 2], for the five inequalities and the minorant they license, and its proof for
  the step each one serves.
* [1, Theorem 2.8 (v)], of which the Type III estimate admitted by the second inequality is a
  variant.
-/

public section

namespace Gap212

/-- **The Harman parameters are admissible.** At `(ξ₁, ξ₂, ξ₃) = (19/50, 2/5, 2/5)` the five scalar
inequalities [2, Proposition 2] asks of the triple all hold: `2ξ₁ + 3ξ₂ < 2`, `ξ₂ ≤ ξ₃`,
`ξ₁ + 9ξ₂ < 4`, `2ξ₁ + ξ₂ > 1` and `17ξ₂ < 7`, with slacks `1/25`, `0`, `1/50`, `4/25` and `1/5` —
the second attained, `2/5` being the least `ξ₃` admissible at this `ξ₂`.

Stated over any linearly ordered field: `Gap212.HarmanReduction`, the reduction these conditions
license, reads the triple in `ℝ`, while the chosen datum's arithmetic reads it in `ℚ`. -/
@[gap212 "lem_harman_scalar_at_datum"]
theorem harman_scalar_conditions_at_datum {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {ξ₁ ξ₂ ξ₃ : 𝕜}
    (hξ₁ : ξ₁ = 19 / 50) (hξ₂ : ξ₂ = 2 / 5) (hξ₃ : ξ₃ = 2 / 5) :
    2 * ξ₁ + 3 * ξ₂ < 2 ∧ ξ₂ ≤ ξ₃ ∧ ξ₁ + 9 * ξ₂ < 4 ∧ 1 < 2 * ξ₁ + ξ₂ ∧ 17 * ξ₂ < 7 := by
  norm_num [hξ₁, hξ₂, hξ₃]

end Gap212
