/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Gap212.Attr
public import Gap212.Definitions
public import Gap212.Equidistribution.Basic

/-!
# Coefficient sequences and equidistribution

The source states its estimates with implied constants: a coefficient sequence satisfies
`|α(n;x)| ≪ τ(n)^{O(1)} log(x)^{O(1)}`, is located at a scale with `1 ≪ c ≪ C ≪ 1`, has a smooth
profile with `|ψ^{(j)}(t)| ≪_j log(x)^{O_j(1)}`, and has the Siegel–Walfisz property with a bound
`≪_A τ(qr)^{O(1)} N/log(x)^A`. None of those constants may depend on the integer variable, on the
scale, or on the sequence's position in a family, and in the equidistribution estimates all of them
are fixed before the sequences, their scales and the width. They are therefore named once and
collected into a single record, a *constant bundle*
`K = (C, k, l; c₋, c₊; a₋, a₊; (bⱼ), (wⱼ); S, E)`, whose only conditions are `0 < c₋ < c₊` and
`0 < a₋ < a₊`; in particular no positivity is asked of `C`, of the `bⱼ` or of `S`. Four of the
eleven are functions, in two pairs, and that is the content of the source's subscripted `≪`: the
Siegel–Walfisz constant `S` and divisor exponent `E` are functions of the saving asked of the bound
— the `A` of the source's `≪_A`, written `B` below — and not of a modulus, a scale or a residue
class, while the derivative bound `bⱼ` and its logarithmic exponent `wⱼ` are functions of the order
`j` of the derivative alone.

The logarithms the three bounds are stated in are this development's, not the source's `log x`: the
coefficient bound is in `1 + log n`, which has no `x` to take a logarithm of and is meaningful at
`n = 1`; the derivative bounds are in `log N`, the logarithm of the scale; and the Siegel–Walfisz
saving is `(1 + Real.log N) ^ B`, where the source saves `(Real.log x) ^ A`. The scales are of
polynomial size in `x`, so each difference is absorbed by the exponent.

*Commensurability at the bundle* is the comparison the third pair of constants is there for: for
reals `z` and `y`, `z ≍_K y` is the conjunction of `a₋ * y ≤ z` and `z ≤ a₊ * y`. It is the
source's `≍` with its constants named — the hypothesis that the product of the scales of a
convolution is of the size of the main scale reads `a₋ * x ≤ M * N ≤ a₊ * x`, never `M * N = x` —
and it is pointwise, between two reals whose constants are fixed in advance: nothing here tends to
infinity and no constant is quantified, because in each equidistribution estimate the bundle, hence
`a₋` and `a₊`, is fixed before the sequences, their scales and the main scale. Since `0 < a₋` it
forces `0 < z` when `0 < y`, and since `a₋ < a₊` the admissible ratios `z / y` fill a genuine
interval. It is neither symmetric nor transitive: both inequalities put `y` on the right, so
`z ≍_K y` compares `z` against the reference quantity `y`, and the exchanged relation would ask for
the constants `a₊⁻¹, a₋⁻¹`, which the bundle does not carry. The relation between *functions*, with
the constants existentially bound, is a different notion: `Gap212.AsympEq` asks for some
`0 < c ≤ C` with `c * g t ≤ f t ≤ C * g t` for all `t > 1`, and is what a bare `≍` between
functions of `x` abbreviates.

Three growth and support conditions cut a sequence `α : ℕ → ℂ` down to the ones the estimates are
about: the coefficient bound `‖α n‖ ≤ C τ(n)^k (1 + log n)^l`, location at a scale `N`, which
confines the support to `[c₋ N, c₊ N]` and is what makes the unrestricted sums below finite, and
smoothness at `N`, which asks that `α n = ψ (n / N)` for a smooth profile `ψ` supported in
`[c₋, c₊]` with `‖ψ^{(j)}‖ ≤ bⱼ (log N)^wⱼ`. Each is stated at `n ≥ 1`, leaving `α 0` free, save
smoothness, which is an identity at every `n`. The Siegel–Walfisz property is the fourth, and
unlike the other three it is an estimate rather than a pointwise bound: the discrepancy of `α` in a
class `a mod q`, with a coprimality condition modulo a second modulus `r`, saves an arbitrary power
of the logarithm of the scale.

The *discrepancy* of a sequence `f : ℕ → ℂ` at a modulus `d` and a residue `a` is the sum of `f`
over the class `a mod d`, minus the expected value of that sum, namely `1 / φ(d)` times the sum of
`f` over the integers coprime to `d`. It comes in two forms, which are different quantities. The
*dyadic* one cuts both sums to the dyadic block `𝒟(x) = {n : ⌈x⌉ ≤ n ≤ ⌊2x⌋}` of `Gap212.dyadic`,
`Δ_𝒟(f; x, d, a) = ∑_{n ∈ 𝒟(x), n ≡ a (d)} f n - φ(d)⁻¹ ∑_{n ∈ 𝒟(x), (n, d) = 1} f n`;
both ranges are `Finset`s, so this is a finite sum for every `f`, whatever its support, and is
total in all four arguments. The *unrestricted* one takes both sums over all of `ℕ`, so its
summation range is the support of `f` and it says something only where that support is finite —
which is what location at a scale provides. It is the unrestricted discrepancy that the
equidistribution estimates sum: `∑_{d ∈ D, d squarefree} |Δ(f; d, a)| ≪ x / (log x)^A` over a
finite family `D` of moduli.

## Main definitions

Declared in `Gap212.Definitions`, which carries the challenge file's own text.

* `Gap212.ConstantBundle`: the eleven constants controlling coefficient growth, support, scale
  commensurability, smoothness and Siegel–Walfisz bounds, with four conditions on the support and
  commensurability endpoints — positivity of `c₋` and of `a₋`, and the strict orders `c₋ < c₊` and
  `a₋ < a₊`.
* `Gap212.ConstantBundle.asympEq`: the commensurability `z ≍_K y`.
* `Gap212.IsCoefficientSequence`: the coefficient bound `‖α n‖ ≤ C τ(n)^k (1 + log n)^l`.
* `Gap212.LocatedAtScale`: support in `[c₀ N, c₁ N]`.
* `Gap212.IsSmoothAtScale`: `α n = ψ (n / N)` for a smooth profile `ψ` supported in `[c, C]` whose
  derivatives obey `‖ψ^{(j)}‖ ≤ b j * (log N) ^ m j`.
* `Gap212.dconv`: the Dirichlet convolution in the arithmetic variable.
* `Gap212.HasSiegelWalfisz`: the Siegel–Walfisz bound at every saving.
* `Gap212.ConstantBundle.IsCoefficientSequence`, `Gap212.ConstantBundle.LocatedAtScale`,
  `Gap212.ConstantBundle.IsSmoothAtScale`, `Gap212.ConstantBundle.HasSiegelWalfisz`: those four
  conditions with their constants read off a bundle.
* `Gap212.sumErrorDyadic`: the dyadic discrepancy `Δ_𝒟(f; x, d, a)`.
* `Gap212.sumError`: the unrestricted discrepancy `Δ(f; d, a)`, which the equidistribution
  estimates are stated with.
* `Gap212.HasEquidistribution`: the bound `∑_{d ∈ D, d squarefree} ‖Δ(f; d, a)‖ ≤ C x / (log x)^A`.

## Main results

* `Gap212.ConstantBundle.scaleHi_pos`, `Gap212.ConstantBundle.asympHi_pos`: the upper endpoints
  `c₊` and `a₊` are positive, completing the chains `0 < c₋ < c₊` and `0 < a₋ < a₊` that the fields
  state in halves.
* `Gap212.ConstantBundle.asympEq_iff`: commensurability at `K` is the conjunction of the two
  inequalities `a₋ * y ≤ z` and `z ≤ a₊ * y`.
* `Gap212.ConstantBundle.nonneg_of_asympEq`: `z ≍_K y` forces `0 ≤ y`.
* `Gap212.pos_of_locatedAtScale`: a sequence located at `N` with a nonzero term forces `0 < N`.

## Implementation notes

The constants are data rather than an existential claim. "∃ constants such that …" would let each
estimate choose its own, and the estimates are applied to convolutions whose scale exponent varies
with `x`; the bundle pins one choice, quantified before the sequences and their scales, so that the
constant of an estimate is uniform over them. Depending on the saving and on the order of the
derivative alone is likewise what lets `S`, `E`, `bⱼ` and `wⱼ` be fixed before the scale; the
alternative reading, bounds re-chosen at each `x`, is vacuous, since at a fixed `x` a smooth
function on a compact set has all of its derivatives bounded. A `structure` rather than a `class`:
the estimates quantify over two bundles at once and pass them explicitly, so there is no bundle for
instance resolution to find. The pair `scaleLo`, `scaleHi` serves twice, as the endpoints of the
support of a located sequence and as the interval off which a smooth profile vanishes. The two
positivity conditions and the two strict orders are separate fields, not a conjunction, and carry
`by norm_num` as their default value, so a bundle with numeric endpoints is written by listing its
eleven constants with `where` or `{ … }`; the anonymous constructor fires no defaults and asks for
all fifteen fields.

Commensurability is pinned as the conjunction of exactly those two non-strict inequalities in that
orientation, rather than characterised up to the existence of constants: with the bundle fixed in
advance the constants are the content, and "some pair of constants works" is both weaker and
unusable. It is defined at every pair of reals with no side condition — at `y = 0` it says
`0 ≤ z ≤ 0`, that is `z = 0` — and the hypotheses that make a comparison meaningful belong to the
statements that use it. Neither side of `asympEq_iff` is degenerate: at `a₋ = 1/2`, `a₊ = 2` one
has `z ≍_K z` for every `0 ≤ z`, while `0 ≍_K 1` fails at every bundle, since `0 < a₋`.

Each of the four conditions on a sequence takes its constants as explicit arguments, and the
version reading them off a bundle is a separate definition: the estimates hold a single bundle and
vary the sequence, while a proof about one condition alone — smoothness implies Siegel–Walfisz, say
— needs only the constants that condition mentions, and stating it at a bundle would tie it to the
other seven. Smoothness quantifies the profile after the scale and the sequence but its bounds `b`
and `m` before both, which is the source's dependence of the implied constant on the order of the
derivative alone.

The discrepancies are `ℂ`-valued and the norm is *not* taken: the source writes the quantity inside
absolute values, and the norm is taken where the quantity is summed, in `HasEquidistribution`. A
real-valued sequence — the sieve's minorant `ρ(·; x) : ℕ → ℝ` — enters through the coercion
`fun n ↦ (ρ n x : ℂ)`; the codomain is not abstracted over a division ring, since each consumer
fixes it to `ℂ`.

Neither positivity of `d` nor coprimality of `a` is required of either discrepancy; the hypotheses
that make the quantity meaningful belong to the statements that use it. At `d = 0` one has
`φ(0) = 0`, so the subtracted term vanishes, and `n ≡ a [MOD 0]` is `n = a`, leaving `f a` for
`a ∈ 𝒟(x)` and `0` otherwise; at `d = 1` both ranges are the whole block and the value is `0`.
Since `n ≡ a (d)` depends on `a` only modulo `d`, so does `Δ_𝒟(f; x, d, a)`. In `x` the dyadic
discrepancy is total but meaningful only for `1 ≤ x`: the truncated `⌈·⌉₊` and `⌊·⌋₊` give
`𝒟(x) = {0}` for `x ≤ 0`, so the value there is built from `f 0`.

## References

* [1, Definition 2.5], for the bundled constants; [1, Definition 1.2], where `X ≍ Y` abbreviates
  `Y ≪ X ≪ Y`, and [1, Definition 2.6 (i)], whose `M N ≍ x` between a product of scales and the
  main scale this is with the constants named.
* [2, Definition 6] for the constants and the equidistribution of [2] for the quantity summed
  there, written over `n ∈ [x, 2x]` inside absolute values; [2, Lemmas 3–7], whose scale
  hypothesis is `M(x) N(x) ≍ x` (`M(x) N₁(x) N₂(x) N₃(x) ≍ x` in the trilinear one).
-/

@[expose] public section

namespace Gap212

attribute [gap212 "def_constant_bundle"] ConstantBundle
attribute [gap212 "def_asymp_eq"] ConstantBundle.asympEq
attribute [gap212 "def_coeff_sequence"] IsCoefficientSequence
attribute [gap212 "def_located_at_scale"] LocatedAtScale
attribute [gap212 "def_smooth_at_scale"] IsSmoothAtScale
attribute [gap212 "def_dconv"] dconv
attribute [gap212 "def_siegel_walfisz"] HasSiegelWalfisz
attribute [gap212 "def_discrepancy_dyadic"] sumErrorDyadic
attribute [gap212 "def_has_equidistribution"] HasEquidistribution

/-! ## Constant bundles -/

namespace ConstantBundle

variable (K : ConstantBundle)

/-- The right support endpoint is positive: `0 < c₋ < c₊` gives `0 < c₊`. -/
theorem scaleHi_pos : 0 < K.scaleHi := K.scaleLo_pos.trans K.scaleLo_lt_scaleHi

/-- The upper commensurability constant is positive: `0 < a₋ < a₊` gives `0 < a₊`. -/
theorem asympHi_pos : 0 < K.asympHi := K.asympLo_pos.trans K.asympLo_lt_asympHi

/-- **Commensurability at a bundle**, unfolded: `z ≍_K y` is the conjunction of
`K.asympLo * y ≤ z` and `z ≤ K.asympHi * y`. -/
theorem asympEq_iff {K : ConstantBundle} {z y : ℝ} :
    K.asympEq z y ↔ K.asympLo * y ≤ z ∧ z ≤ K.asympHi * y := Iff.rfl

/-- **The reference quantity of a commensurability is non-negative**: `a₋ * y ≤ z ≤ a₊ * y` with
`a₋ < a₊` is `0 ≤ (a₊ - a₋) * y`. Only the strict order of the two constants is used, not `0 < a₋`,
so this holds at the bundles with `1 < a₋` too. It is the sign a consumer that moves `a₋` or `a₊`
needs, and the reason such a move asks no positivity of `y`. -/
theorem nonneg_of_asympEq {K : ConstantBundle} {z y : ℝ} (h : K.asympEq z y) : 0 ≤ y := by
  nlinarith [h.1.trans h.2, K.asympLo_lt_asympHi]

end ConstantBundle

/-! ## Sequences at a single scale

Every constant is an explicit argument, and no positivity is imposed on `C`, on `b` or on `S`. -/

/-- **A scale carrying a nonzero term is positive**: a term `α n ≠ 0` with `n ≥ 1` located in
`[c₀ * N, c₁ * N]` gives `1 ≤ n ≤ c₁ * N` with `0 < c₁`, hence `0 < N`. At a nonpositive scale the
condition has no nonzero term to constrain, so it is vacuous there. It is the sign a consumer that
moves `c₀` or `c₁` needs, and the reason such a move asks no positivity of `N`. -/
theorem pos_of_locatedAtScale {c₀ c₁ : ℝ} {α : ℕ → ℂ} {N : ℝ} (hc₁ : 0 < c₁)
    (h : LocatedAtScale c₀ c₁ α N) {n : ℕ} (hn : 1 ≤ n) (hne : α n ≠ 0) : 0 < N := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [(h n hn hne).2]

end Gap212
