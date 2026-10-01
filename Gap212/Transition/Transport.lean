/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Packing.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public meta import Gap212.Attr

/-!
# Transport of the endpoint factorization below the half-level

The extraction lemmas are run at a modulus level `θ = log_x q`, and the packing conditions that
feed them are verified once, at the endpoint `θ = 1/2`. The dyadic decomposition however produces
blocks at `θ` slightly *below* `1/2`, and the question is whether the endpoint partition survives
there.

It does, and for a reason with nothing analytic in it: every bin capacity is an **affine** function
of `θ`, so moving `θ` by `u` moves each capacity by at most `L|u|` for `L` the largest slope. If
the endpoint partition was verified with reserve `η > 0` to spare, it therefore remains valid on
`|θ - 1/2| < η/L`. That is `Gap212.Transition.transport₂` and its companions, the endpoint
transport argument of [2], which is where the transition range gets its width.

## The fourth bin is why this cannot be done by substitution

The natural-looking route is to keep the Type IIc capacities as functions of `ω₀` (where
`θ = 1/2 + 2ω₀`, so `ω₀ = -κ/2` at `θ = 1/2 - κ`) and simply evaluate them at a negative `ω₀`. That
route is not merely lossy, it is **unavailable**: the fourth capacity is `8ω₀`, which is strictly
negative for `κ > 0`, and `Gap212.Packing.no_partition₄_of_neg_capacity` shows no partition can
then exist at all — a block's `y`-sum is a sum of nonnegative terms.

[2] instead keeps the *raw* capacities, the ones the extraction windows actually
produce before the final uniform weakening. The fourth of those is `-4κ + 55εt`, which is
nonnegative exactly on `κ ≤ 11εₐ/80`, and that is where the transition range's radius comes from —
`Gap212.Transition.IIc.cap₄_eq_zero_at_radius` shows the constraint is tight, the capacity hitting
`0` precisely at the endpoint of the range.

So the four-range formulation is not a presentational choice. It is what keeps the fourth bin's
capacity nonnegative, and it resolves the sign of the fourth capacity in the statement of
[2, Proposition 3 (D)].

## An unused bin still needs a nonnegative capacity

The transport lemma of [2] adds "bins whose endpoint capacity is zero remain unused", and its proof
glosses this as: an unused zero-capacity bin receives no rough factor, so its sign away from the
endpoint is irrelevant. The second half does not survive formalization — an unused block has `y`-sum
`0`, so its capacity must still be `≥ 0`, and a negative one is fatal rather than irrelevant. The
conclusion of [2] stands, because the transition range it fixes enforces the nonnegativity anyway;
but the reason is the table, not the bin being unused.

## Main results

* `Gap212.Transition.affine_ge_of_dist_lt`: the scalar core — an affine capacity loses less than
  the reserve inside the radius.
* `Gap212.Transition.transport₂`, `transport₃`, `transport₄`: the transport lemma at each leaf.
* `Gap212.Transition.IIc.cap₁_eq` … `cap₄_eq`: the four term-by-term substitutions.
* `Gap212.Transition.IIc.admitsPartition₄_transport`: the endpoint partition transported across the
  transition range.
* `Gap212.Transition.IIc.cap₄_eq_zero_at_radius`: the range's radius is exactly bin 4's wall.
-/

@[expose] public section

namespace Gap212.Transition

open Gap212.Packing

/-! ## The affine core -/

/-- **An affine capacity loses less than the reserve.** The multiplicative form, which is what the
argument actually uses: if the slope is at most `L` and `L|θ - 1/2| < η`, then the capacity
`c + s(θ - 1/2)` at level `θ` still dominates the retreated endpoint capacity `c - η`.

This is the whole content of the transport lemma; everything below is instantiation. -/
theorem affine_ge_of_mul_lt {s θ η L : ℝ} (hs : |s| ≤ L) (hlt : L * |θ - 1 / 2| < η) (c : ℝ) :
    c - η ≤ c + s * (θ - 1 / 2) := by
  linarith [neg_abs_le (s * (θ - 1 / 2)), abs_mul s (θ - 1 / 2),
    mul_le_mul_of_nonneg_right hs (abs_nonneg (θ - 1 / 2))]

/-- The same, in the division form `|θ - 1/2| < η/L`. -/
theorem affine_ge_of_dist_lt {s θ η L : ℝ} (hL : 0 < L) (hs : |s| ≤ L)
    (hθ : |θ - 1 / 2| < η / L) (c : ℝ) :
    c - η ≤ c + s * (θ - 1 / 2) :=
  affine_ge_of_mul_lt hs ((lt_div_iff₀' hL).1 hθ) c

/-- **Transport at a two-factor leaf.** An endpoint two-block partition with reserve `η` in both
bins remains valid at every level within `η/L` of the half-level. -/
theorem transport₂ {ℓ : ℕ} {y : Fin ℓ → ℝ} {c₁ c₂ s₁ s₂ θ η L : ℝ}
    (hL : 0 < L) (hs₁ : |s₁| ≤ L) (hs₂ : |s₂| ≤ L)
    (hθ : |θ - 1 / 2| < η / L)
    (h : AdmitsPartition₂ y (c₁ - η) (c₂ - η)) :
    AdmitsPartition₂ y (c₁ + s₁ * (θ - 1 / 2)) (c₂ + s₂ * (θ - 1 / 2)) :=
  h.mono (affine_ge_of_dist_lt hL hs₁ hθ c₁) (affine_ge_of_dist_lt hL hs₂ hθ c₂)

/-- **Transport at a three-factor leaf.** -/
theorem transport₃ {ℓ : ℕ} {y : Fin ℓ → ℝ} {c₁ c₂ c₃ s₁ s₂ s₃ θ η L : ℝ}
    (hL : 0 < L) (hs₁ : |s₁| ≤ L) (hs₂ : |s₂| ≤ L) (hs₃ : |s₃| ≤ L)
    (hθ : |θ - 1 / 2| < η / L)
    (h : AdmitsPartition₃ y (c₁ - η) (c₂ - η) (c₃ - η)) :
    AdmitsPartition₃ y (c₁ + s₁ * (θ - 1 / 2)) (c₂ + s₂ * (θ - 1 / 2))
      (c₃ + s₃ * (θ - 1 / 2)) :=
  h.mono (affine_ge_of_dist_lt hL hs₁ hθ c₁) (affine_ge_of_dist_lt hL hs₂ hθ c₂)
    (affine_ge_of_dist_lt hL hs₃ hθ c₃)

/-- **Transport at a four-factor leaf**, whose fourth bin has endpoint capacity `0`.

The fourth bin gets an explicit hypothesis rather than a reserve, and this is the one place the
statement departs from that of [2]. A bin with endpoint capacity `0` has no reserve to spend, so
`affine_ge_of_dist_lt` says nothing about it; and it cannot simply be ignored, since an unused
block still has `y`-sum `0` and so still needs a nonnegative capacity. The hypothesis
`0 ≤ s₄ * (θ - 1/2)` is exactly what must be checked, and for Type IIc the capacity table checks
it. -/
theorem transport₄ {ℓ : ℕ} {y : Fin ℓ → ℝ} {c₁ c₂ c₃ s₁ s₂ s₃ s₄ θ η L : ℝ}
    (hL : 0 < L) (hs₁ : |s₁| ≤ L) (hs₂ : |s₂| ≤ L) (hs₃ : |s₃| ≤ L)
    (hθ : |θ - 1 / 2| < η / L)
    (h₄ : 0 ≤ s₄ * (θ - 1 / 2))
    (h : AdmitsPartition₄ y (c₁ - η) (c₂ - η) (c₃ - η) 0) :
    AdmitsPartition₄ y (c₁ + s₁ * (θ - 1 / 2)) (c₂ + s₂ * (θ - 1 / 2))
      (c₃ + s₃ * (θ - 1 / 2)) (s₄ * (θ - 1 / 2)) :=
  h.mono (affine_ge_of_dist_lt hL hs₁ hθ c₁) (affine_ge_of_dist_lt hL hs₂ hθ c₂)
    (affine_ge_of_dist_lt hL hs₃ hθ c₃) h₄

/-! ## The Type IIc capacity table

[2] computes the four raw capacities at `θ = 1/2 - κ` term by term and tabulates their
differences from the endpoint capacities. Both halves are below: the substitutions as identities,
then the differences as inequalities. -/

namespace IIc

variable (γ εt d θ : ℝ)

/-- The lower end of the first Type IIc window, `a₁ = γ - 3εt - d`, before the final uniform
weakening. -/
def a₁ : ℝ := γ - 3 * εt - d

/-- The upper end of the first window, `b₁ = γ - 3εt`. -/
def b₁ : ℝ := γ - 3 * εt

/-- The lower end of the second window, `a₂ = 1 - γ - 6εt - θ - d`. It depends on the modulus
level `θ`, which is why the extraction is stated on a dyadic block. -/
def a₂ : ℝ := 1 - γ - 6 * εt - θ - d

/-- The upper end of the second window, `b₂ = 1 - γ - 6εt - θ`. -/
def b₂ : ℝ := 1 - γ - 6 * εt - θ

/-- The lower end of the third window, `a₃ = 2 - γ - 52εt - d - 4θ`. The coefficient `4` on `θ` is
the `d⁻⁴` of the Type IIc moduli set. -/
def a₃ : ℝ := 2 - γ - 52 * εt - d - 4 * θ

/-- The upper end of the third window, `b₃ = 2 - γ - 52εt - 4θ`. -/
def b₃ : ℝ := 2 - γ - 52 * εt - 4 * θ

/-! ### The four substitutions -/

/-- Bin 1's capacity `2a₁ + b₃` at `θ = 1/2 - κ` is `γ - 2d + 4κ - 58εt`. -/
theorem cap₁_eq (γ εt d κ : ℝ) :
    2 * a₁ γ εt d + b₃ γ εt (1 / 2 - κ) = γ - 2 * d + 4 * κ - 58 * εt := by
  unfold a₁ b₃; ring

/-- Bin 2's capacity `b₂` at `θ = 1/2 - κ` is `1/2 - γ + κ - 6εt`. -/
theorem cap₂_eq (γ εt κ : ℝ) :
    b₂ γ εt (1 / 2 - κ) = 1 / 2 - γ + κ - 6 * εt := by
  unfold b₂; ring

/-- Bin 3's capacity `θ - b₁ - a₂` at `θ = 1/2 - κ` is `d - 2κ + 9εt`. -/
theorem cap₃_eq (γ εt d κ : ℝ) :
    1 / 2 - κ - b₁ γ εt - a₂ γ εt d (1 / 2 - κ) = d - 2 * κ + 9 * εt := by
  unfold b₁ a₂; ring

/-- Bin 4's capacity `a₁ - 2b₁ - a₃` at `θ = 1/2 - κ` is `-4κ + 55εt`. Note that `γ` and `d` both
cancel: the fourth capacity depends only on the retreat and the distance below the half-level. -/
theorem cap₄_eq (γ εt d κ : ℝ) :
    a₁ γ εt d - 2 * b₁ γ εt - a₃ γ εt d (1 / 2 - κ) = -(4 * κ) + 55 * εt := by
  unfold a₁ b₁ a₃; ring

/-- The level `θ` of the four-factor extraction is `1/2 + 2ω₀`, so a level `1/2 - κ` below the
half-level is `ω₀ = -κ/2`. -/
@[gap212 "lem_theta_kappa_omega"]
theorem theta_of_kappa (κ : ℝ) : 1 / 2 + 2 * (-(κ / 2)) = 1 / 2 - κ := by ring

/-! ### The four differences

Each raw capacity dominates its endpoint capacity throughout `0 ≤ κ ≤ 11εₐ/80`, at the retreat
`εt = εₐ/100`. Bins 1 and 2 hold for any `κ ≥ 0`; bins 3 and 4 are where the range comes from. -/

/-- Bin 1: the difference is `4κ + 42εₐ/100`, nonnegative for any `κ ≥ 0`. -/
@[gap212 "lem_capacity_difference_1"]
theorem endpoint_le_cap₁ {γ d κ εa : ℝ} (hκ : 0 ≤ κ) (hεa : 0 ≤ εa) :
    γ - 2 * d - εa ≤ γ - 2 * d + 4 * κ - 58 * (εa / 100) := by linarith

/-- Bin 2: the difference is `κ + 94εₐ/100`, nonnegative for any `κ ≥ 0`. -/
@[gap212 "lem_capacity_difference_2"]
theorem endpoint_le_cap₂ {γ κ εa : ℝ} (hκ : 0 ≤ κ) (hεa : 0 ≤ εa) :
    1 / 2 - γ - εa ≤ 1 / 2 - γ + κ - 6 * (εa / 100) := by linarith

/-- Bin 3: the difference is `109εₐ/100 - 2κ`, so this bin alone would allow `κ ≤ 109εₐ/200`. -/
@[gap212 "lem_capacity_difference_3"]
theorem endpoint_le_cap₃ {d κ εa : ℝ} (hκ : κ ≤ 11 * εa / 80) (hεa : 0 ≤ εa) :
    d - εa ≤ d - 2 * κ + 9 * (εa / 100) := by linarith

/-- Bin 4: the difference is `55εₐ/100 - 4κ`. This is the binding constraint, and it is what fixes
the transition range at `κ ≤ 11εₐ/80`. -/
@[gap212 "lem_capacity_difference_4"]
theorem endpoint_le_cap₄ {κ εa : ℝ} (hκ : κ ≤ 11 * εa / 80) :
    (0 : ℝ) ≤ -(4 * κ) + 55 * (εa / 100) := by linarith

/-- **Bin 4 is the binding constraint**: its wall `11εₐ/80` is strictly inside bin 3's
`109εₐ/200`. -/
@[gap212 "lem_transition_capacities_nonneg"]
theorem bin₄_binding {εa : ℝ} (hεa : 0 < εa) : 11 * εa / 80 < 109 * εa / 200 := by linarith

/-- **The radius is exactly bin 4's wall**: at `κ = 11εₐ/80` the fourth capacity is `0`, not merely
small. So the transition range cannot be widened without the fourth block going negative, which
`Gap212.Packing.no_partition₄_of_neg_capacity` rules out entirely. -/
theorem cap₄_eq_zero_at_radius (εa : ℝ) :
    -(4 * (11 * εa / 80)) + 55 * (εa / 100) = 0 := by ring

/-- **Why substitution is not an option.** At a level below the half-level the Type IIc fourth
capacity written as a function of `ω₀` is `8ω₀ = -4κ`, strictly negative. Together with
`Gap212.Packing.no_partition₄_of_neg_capacity` this says the `ω₀`-substituted partition does not
exist, so the transport must be run on the raw capacities of `cap₄_eq` instead. -/
theorem substituted_cap₄_neg {κ : ℝ} (hκ : 0 < κ) : 8 * (-(κ / 2)) < 0 := by linarith

/-! ### The transport -/

/-- **The Type IIc endpoint partition, transported.** If the four-block condition holds at the
endpoint capacities `(γ - 2d - εₐ, 1/2 - γ - εₐ, d - εₐ, 0)`, then it holds at the raw capacities
the extraction windows produce at every level `θ = 1/2 - κ` with `0 ≤ κ ≤ 11εₐ/80`.

This is the form `Gap212.Extraction.four_factor` consumes throughout the transition range. -/
theorem admitsPartition₄_transport {ℓ : ℕ} {y : Fin ℓ → ℝ} {γ d κ εa : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 11 * εa / 80) (hεa : 0 ≤ εa)
    (h : AdmitsPartition₄ y (γ - 2 * d - εa) (1 / 2 - γ - εa) (d - εa) 0) :
    AdmitsPartition₄ y
      (2 * a₁ γ (εa / 100) d + b₃ γ (εa / 100) (1 / 2 - κ))
      (b₂ γ (εa / 100) (1 / 2 - κ))
      (1 / 2 - κ - b₁ γ (εa / 100) - a₂ γ (εa / 100) d (1 / 2 - κ))
      (a₁ γ (εa / 100) d - 2 * b₁ γ (εa / 100) - a₃ γ (εa / 100) d (1 / 2 - κ)) := by
  rw [cap₁_eq, cap₂_eq, cap₃_eq, cap₄_eq]
  exact h.mono (endpoint_le_cap₁ hκ0 hεa) (endpoint_le_cap₂ hκ0 hεa)
    (endpoint_le_cap₃ hκ hεa) (endpoint_le_cap₄ hκ)

end IIc

/-! ## The radius at the fixed slack -/

/-- The transition range's radius, `11εₐ/80`. -/
noncomputable def transitionRadius (εa : ℝ) : ℝ := 11 * εa / 80

/-- At the fixed slack `εₐ = 10⁻¹⁰` the radius is `11/(8·10¹¹)`. Small, but a fixed positive
constant, which is all the argument needs: the dyadic blocks of the transition range have
`κ = O(log log x / log x) = o(1)`, so they fall inside it for `x` large. -/
theorem transitionRadius_pointA : transitionRadius (1 / 10 ^ 10) = 11 / (8 * 10 ^ 11) := by
  norm_num [transitionRadius]

/-- The radius is positive whenever the slack is. -/
theorem transitionRadius_pos {εa : ℝ} (hεa : 0 < εa) : 0 < transitionRadius εa := by
  unfold transitionRadius; linarith

end Gap212.Transition
