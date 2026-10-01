/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Gap212.Attr
public import Gap212.Routing.Defs.Equidistribution

/-!
# Normalizing a constant bundle

Every constant bundle can be replaced by one whose support and commensurability endpoints straddle
`1` and whose coefficient constant is at least `1`, without losing any clause a datum satisfies.

The construction widens the two intervals and enlarges the coefficient constant:
`c₋ ↦ min c₋ 1`, `c₊ ↦ max c₊ 1`, `a₋ ↦ min a₋ 1`, `a₊ ↦ max a₊ 1`, `C ↦ max C 1`, with every other
component unchanged. Each of the five clauses is monotone in exactly the components it reads, and
they read disjoint groups: the coefficient bound reads `(C, k, l)`, location reads `(c₋, c₊)`,
smoothness reads `(c₋, c₊, b, w)`, Siegel–Walfisz reads `(S, E)`, and commensurability reads
`(a₋, a₊)`. So a datum satisfying several clauses at `K` satisfies all of them at `K♭`, and no join
of bundles is ever needed.

`C ↦ max C 1` is the part that is easy to omit and load-bearing: without `1 ≤ C` the step
`C ≤ C ^ 2` fails, and `Gap212.isCoefficientSequence_and_locatedAtScale_dconv` does not give that
a `K`-coefficient sequence is a `Ψ(K)`-one.

Widening an interval weakens `c₋ * N ≤ n ≤ c₊ * N` only for `0 ≤ N`, and `a₋ * y ≤ z ≤ a₊ * y` only
for `0 ≤ y`; neither transfer has to assume that sign, because the hypothesis being transferred
supplies it. A nonzero term `α n ≠ 0` with `n ≥ 1` located in `[c₋ N, c₊ N]` gives `1 ≤ n ≤ c₊ * N`
with `0 < c₊`, hence `0 < N`; and `a₋ * y ≤ z ≤ a₊ * y` with `a₋ < a₊` gives `0 ≤ (a₊ - a₋) * y`,
hence `0 ≤ y`. Below those thresholds the transferred hypothesis is itself vacuous rather than the
conclusion false, so both transfers hold at every real scale and at every pair of reals, using only
the strict-order fields the structure already carries.

## Main definitions

* `Gap212.ConstantBundle.flat`: the normalization `K♭` of a bundle.

## Main results

* `Gap212.constantBundle_flat_transfer`: `K♭` is normalized, and every clause a datum satisfies at
  `K` it satisfies at `K♭`.
-/

@[expose] public section

namespace Gap212

open Real

namespace ConstantBundle

/-- **The normalization of a bundle**: the support and commensurability intervals widened to
straddle `1`, and the coefficient constant raised to at least `1`. -/
noncomputable def flat (K : ConstantBundle) : ConstantBundle where
  coeffConst := max K.coeffConst 1
  coeffFstPow := K.coeffFstPow
  coeffSndPow := K.coeffSndPow
  scaleLo := min K.scaleLo 1
  scaleHi := max K.scaleHi 1
  asympLo := min K.asympLo 1
  asympHi := max K.asympHi 1
  smoothConst := K.smoothConst
  smoothPow := K.smoothPow
  siegelWalfiszConst := K.siegelWalfiszConst
  siegelWalfiszPow := K.siegelWalfiszPow
  scaleLo_pos := lt_min K.scaleLo_pos zero_lt_one
  scaleLo_lt_scaleHi :=
    lt_of_le_of_lt (min_le_left _ _) (lt_of_lt_of_le K.scaleLo_lt_scaleHi (le_max_left _ _))
  asympLo_pos := lt_min K.asympLo_pos zero_lt_one
  asympLo_lt_asympHi :=
    lt_of_le_of_lt (min_le_left _ _) (lt_of_lt_of_le K.asympLo_lt_asympHi (le_max_left _ _))

/-- The `scaleLo` field of `K.flat` is `min K.scaleLo 1`. -/
@[simp] theorem flat_scaleLo (K : ConstantBundle) : K.flat.scaleLo = min K.scaleLo 1 := rfl
/-- The `scaleHi` field of `K.flat` is `max K.scaleHi 1`. -/
@[simp] theorem flat_scaleHi (K : ConstantBundle) : K.flat.scaleHi = max K.scaleHi 1 := rfl
/-- The `asympLo` field of `K.flat` is `min K.asympLo 1`. -/
@[simp] theorem flat_asympLo (K : ConstantBundle) : K.flat.asympLo = min K.asympLo 1 := rfl
/-- The `asympHi` field of `K.flat` is `max K.asympHi 1`. -/
@[simp] theorem flat_asympHi (K : ConstantBundle) : K.flat.asympHi = max K.asympHi 1 := rfl

/-- The normalized support interval straddles `1`. -/
theorem flat_scaleLo_le_one (K : ConstantBundle) : K.flat.scaleLo ≤ 1 := min_le_right _ _

/-- `1 ≤ K.flat.scaleHi`. -/
theorem one_le_flat_scaleHi (K : ConstantBundle) : 1 ≤ K.flat.scaleHi := le_max_right _ _

/-- The normalized commensurability interval straddles `1`. -/
theorem flat_asympLo_le_one (K : ConstantBundle) : K.flat.asympLo ≤ 1 := min_le_right _ _

/-- `1 ≤ K.flat.asympHi`. -/
theorem one_le_flat_asympHi (K : ConstantBundle) : 1 ≤ K.flat.asympHi := le_max_right _ _

/-- **The coefficient constant is at least `1`**, which is what makes `C ≤ C ^ 2` available. -/
theorem one_le_flat_coeffConst (K : ConstantBundle) : 1 ≤ K.flat.coeffConst := le_max_right _ _

end ConstantBundle

/-- **Bundle normalization.** Every clause a datum satisfies at `K` it satisfies at `K.flat`, and
`K.flat` has both intervals straddling `1` and `1 ≤ coeffConst`.

The location and commensurability transfers hold at every real scale and every pair of reals: the
sign their widened interval needs comes from the hypothesis being transferred, which is vacuous
where that sign fails. -/
@[gap212 "lem_bundle_normalization"]
theorem constantBundle_flat_transfer (K : ConstantBundle) :
    K.flat.scaleLo ≤ 1 ∧ 1 ≤ K.flat.scaleHi ∧
    K.flat.asympLo ≤ 1 ∧ 1 ≤ K.flat.asympHi ∧
    1 ≤ K.flat.coeffConst ∧
    (∀ α : ℕ → ℂ, K.IsCoefficientSequence α → K.flat.IsCoefficientSequence α) ∧
    (∀ (α : ℕ → ℂ) (N : ℝ), K.LocatedAtScale α N → K.flat.LocatedAtScale α N) ∧
    (∀ (α : ℕ → ℂ) (N : ℝ), K.IsSmoothAtScale α N → K.flat.IsSmoothAtScale α N) ∧
    (∀ (α : ℕ → ℂ) (N : ℝ), K.HasSiegelWalfisz α N → K.flat.HasSiegelWalfisz α N) ∧
    (∀ z y : ℝ, K.asympEq z y → K.flat.asympEq z y) := by
  refine ⟨K.flat_scaleLo_le_one, K.one_le_flat_scaleHi, K.flat_asympLo_le_one,
    K.one_le_flat_asympHi, K.one_le_flat_coeffConst, ?_, ?_, ?_, ?_, ?_⟩
  · -- the coefficient bound reads `(C, k, l)`, and only `C` moved, upwards
    intro α hα n hn
    refine (hα n hn).trans ?_
    have hτ : (0 : ℝ) ≤ (n.divisors.card : ℝ) ^ K.coeffFstPow := by positivity
    have hlog : (0 : ℝ) ≤ (1 + log n) ^ K.coeffSndPow := by
      have : (0 : ℝ) ≤ log n := Real.log_natCast_nonneg n
      positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hτ) hlog
  · -- location reads `(c₋, c₊)`, and the interval only widened, at a scale the nonzero term
    -- forces to be positive
    intro α N hα n hn hne
    have hN : (0 : ℝ) ≤ N := (pos_of_locatedAtScale K.scaleHi_pos hα hn hne).le
    obtain ⟨hlo, hhi⟩ := hα n hn hne
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hN).trans hlo,
      hhi.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hN)⟩
  · -- smoothness reads `(c₋, c₊, b, w)`; the derivative data is unchanged
    intro α N hα
    obtain ⟨ψ, hψ, hsupp, hderiv, heq⟩ := hα
    refine ⟨ψ, hψ, fun t ht ↦ ?_, hderiv, heq⟩
    obtain ⟨h1, h2⟩ := hsupp t ht
    exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_left _ _)⟩
  · -- Siegel–Walfisz reads `(S, E)`, both unchanged, so this is the same statement
    exact fun _ _ hα ↦ hα
  · -- commensurability reads `(a₋, a₊)`, and that interval only widened, at a `y` the comparison
    -- forces to be non-negative
    intro z y hzy
    have hy : (0 : ℝ) ≤ y := ConstantBundle.nonneg_of_asympEq hzy
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hy).trans hzy.1,
      hzy.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hy)⟩

end Gap212
