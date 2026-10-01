/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.GPYDefs
public import Gap212.Sieve.Integrals
public import Mathlib.Analysis.Convolution
public meta import Gap212.Attr

/-!
# The sieve endgame: the retreat, the variational gap, and the tensor mesh

The vocabulary in which the Maynard–Tao sieve is run over a stratified support once the variational
certificate is in hand: the buffered region the approximating functions are confined to, the
restricted marginal form the certificate's `J` becomes at a one-band datum, the three operations
that turn an `L²` certificate into a fixed smooth one (shrink-and-translate, the numerical retreat
data, mollification), and the tensor data the smooth function is finally approximated by.

## Two coordinates, and how they are written

`J` and everything downstream single out one coordinate, so the ambient dimension is written
`m + 1` and the remaining coordinates are indexed by `Fin m`, exactly as in
`Gap212.Sieve.Integrals`. A point of `ℝ^k` split as `(u, t)` is `Fin.snoc u t`; a family
`(a_s)_{s ≠ i}` is a function on `Fin m` read through `Fin.succAbove i`, the order embedding that
skips `i`.

The one-variable functions are taken on all of `ℝ` rather than on `[0,∞)`, the convention fixed by
`Gap212.GPY.lambdaF`, which evaluates its profile at `log_x d` for arbitrary `d`. Every clause about
their support is therefore relativised to the orthant. The `g`'s are compactly supported inside
`(0,∞)`, but the tails `f = 𝒯g`, which the tensor datum is about, are not: `(𝒯g)(t) = ∫_t^∞ g` is
the total mass at every `t` below `supp g`, so a non-zero tail has no compact support on `ℝ`.
Compact support on `ℝ`, or vanishing of the product off the retreat region, would force
`f l i 0 = 0`, and with it `𝓙ᵢ = 0`, since both groups of `Gap212.Defs.formJMarginal` carry these
boundary values. See `TensorDatum` below.

## Main definitions

* `Gap212.GPY.roughAt`: the coordinates reaching a threshold.
* `Gap212.GPY.bufferedRegion`: the retreat region with room in the inequalities and at the
  threshold.
* `Gap212.GPY.TensorDatum`: finitely many coefficients and smooth tensor factors supported in the
  retreat region.
* `Gap212.GPY.marginalForm`: the restricted marginal form `J̃_c`.
* `Gap212.GPY.HasVariationalGap`: `0 < I_T(G)` and `I_T(G) < k J̃_c(G)`.
* `Gap212.GPY.shrinkTranslate`, `retreatData`, `mollify`: the retreat.
* `Gap212.GPY.tailTransform`: `(𝒯g)(t) = ∫_t^∞ g`.
* `Gap212.GPY.tensorMarginal`, `tensorMarginalHigh`: the `i`-th marginal of a tensor sum, and the
  part of it carried by the high indices.
-/

@[expose] public section

namespace Gap212.GPY

open Finset MeasureTheory Convolution

open Classical in
/-- **The coordinates reaching a threshold**, `{i : θ ≤ tᵢ}` as a `Finset`.

`SupportParams.large` is the *strict* set `{i : δ < tᵢ}` at the *fixed* threshold `δ`, and neither
choice serves here: the buffered region has to see a coordinate sitting anywhere above `δ - ζ₁`,
since a perturbation of size `ζ₁` can push such a coordinate into the rough set and bring its mass
into a cap that did not previously count it. -/
noncomputable def roughAt {k : ℕ} (θ : ℝ) (t : Fin k → ℝ) : Finset (Fin k) :=
  {i ∈ Finset.univ | θ ≤ t i}

/-- **The buffered retreat region** `R⁺⁺_k(j, ε₀, ζ₁, κ)`: the coordinates lie in `[ζ₁, 1 - κ]`,
the total mass is `κ` below the retreated node `(1 - ε₀)(A_j + ε)`, and — when the set of
coordinates reaching `δ - ζ₁` is non-empty — its mass is `κ` below the retreated cap.

The two buffers do different work. `κ` is room in the two inequalities; `ζ₁` is room at the rough
threshold. The cap clause is asked only of a non-empty rough set, exactly as `SupportParams` guards
its own chain at `m ≥ 1`: at the empty set it would read `0 ≤ -κ` and the region would be empty. -/
@[gap212 "def_buffered_region"]
noncomputable def bufferedRegion (p : SupportParams) (k : ℕ) (j : Fin p.n) (ε₀ ζ₁ κ : ℝ) :
    Set (Fin k → ℝ) :=
  {t | (∀ i, t i ∈ Set.Icc ζ₁ (1 - κ)) ∧
    (∑ i, t i) ≤ (1 - ε₀) * (p.A j.succ + p.ε) - κ ∧
    ((roughAt (p.δ - ζ₁) t).Nonempty →
      ∑ i ∈ roughAt (p.δ - ζ₁) t, t i ≤ (1 - ε₀) * p.B j (roughAt (p.δ - ζ₁) t).card - κ)}

/-- **A tensor datum at level `ε₀`**: a length `L`, coefficients `cₗ`, and smooth compactly
supported one-variable factors `f_{l,i}` whose product over the `k` coordinates is supported in the
retreat region `R⁺_k(j, ε₀)`.

The support clause is the whole point of the datum: it is what keeps the moduli the sieve weights
generate inside `Q⋆`, and it is asked of the *product* — an individual factor may well be supported
outside the region, since the region constrains the coordinates jointly. -/
@[gap212 "def_tensor_datum"]
structure TensorDatum (p : SupportParams) (k : ℕ) (j : Fin p.n) (ε₀ : ℝ) where
  /-- How many tensor terms. -/
  L : ℕ
  /-- The coefficient of each term; no sign is asked here. -/
  c : Fin L → ℝ
  /-- The one-variable factors, `f l i` being the `i`-th factor of the `l`-th term. -/
  f : Fin L → Fin k → ℝ → ℝ
  /-- Every factor is smooth, i.e. `C^∞`, with exponent `(⊤ : ℕ∞)`. (In `WithTop ℕ∞`, `⊤` is
  analyticity, and an analytic function on `ℝ` vanishing on a half-line is identically zero.) -/
  smooth : ∀ l i, ContDiff ℝ (⊤ : ℕ∞) (f l i)
  /-- Every factor vanishes beyond a common bound: compact support on `[0,∞)`, not on `ℝ`.

  The factors are tails `f = 𝒯g`, and `(𝒯g)(t) = ∫_t^∞ g` equals the total mass at every `t` below
  `supp g`, so a tail has no compact support on `ℝ` unless `f l i 0 = ∫_0^∞ g = 0`. -/
  compactSupport : ∃ B : ℝ, ∀ l i t, B < t → f l i t = 0
  /-- Each term's product is supported in the retreat region, among the points of the orthant.

  The factors are functions on `[0,∞)` in the source: on `[0,∞)` the tail of a `g` supported in
  `[α,β] ⊆ (0,∞)` is supported in `[0,β]`, with the product in the downward box
  `{t ∈ [0,∞)^k : tᵢ ≤ β_{l,i}}`, as `Gap212.GPY.retreatRegion_downward_closed` uses. Since
  `retreatRegion` lies in `[0,1]^k`, the clause without the orthant restriction would force the
  product to vanish wherever a coordinate is negative. -/
  supp_subset : ∀ l, ∀ t : Fin k → ℝ, (∀ i, 0 ≤ t i) → (∏ i, f l i (t i)) ≠ 0 →
    t ∈ retreatRegion p k j ε₀

/-- **The restricted marginal form** `J̃_c(G)`: the last coordinate is integrated out over
`[0, ∞)`, the result squared, and the square integrated over the part of the orthant
`[0,∞)^{k-1}` where the remaining coordinates sum to at most `c`.

At a one-band datum this is what the certificate's `J_T` becomes, and it is the only form of `J`
under which replacing `G` by `|G|` cannot decrease the numerator — a restricted square of a
marginal, not a marginal of a square. The cutoff is non-strict, and the cutoff hyperplane is
Lebesgue-null, so moving the cutoff inward converges. -/
@[gap212 "def_marginal_form"]
noncomputable def marginalForm {m : ℕ} (c : ℝ) (G : (Fin (m + 1) → ℝ) → ℝ) : ℝ :=
  ∫ u in {u : Fin m → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c},
    (∫ t in Set.Ioi (0 : ℝ), G (Fin.snoc u t)) ^ 2

/-- **The variational gap at cutoff `c`**: `0 < I_T(G)` and `I_T(G) < k J̃_c(G)`, at `k = m + 1`.

Square-integrability of `G` and its vanishing off `T_k(p)` are *not* part of this predicate: they
are carried as hypotheses of every statement about the gap, and they are what make the two
quantities finite rather than what the gap asserts. -/
@[gap212 "def_variational_gap"]
def HasVariationalGap (p : SupportParams) (m : ℕ) (c : ℝ) (G : (Fin (m + 1) → ℝ) → ℝ) : Prop :=
  0 < Iint p (m + 1) G ∧ Iint p (m + 1) G < ((m + 1 : ℕ) : ℝ) * marginalForm c G

/-- **The shrink-and-translate map** `(Σ_{a,b₀}G)(t) = G((t - b₀·1)/(1 - a))`: the support of `G`
is shrunk by `1 - a` and pushed off every coordinate hyperplane by `b₀`.

Shrinking retreats the caps and the total mass; translating is what puts a fixed positive distance
between the support and the boundary of the orthant, which is what the rough-threshold buffer and
the later downward boxes need. -/
@[gap212 "def_shrink_translate"]
noncomputable def shrinkTranslate {k : ℕ} (a b₀ : ℝ) (G : (Fin k → ℝ) → ℝ) :
    (Fin k → ℝ) → ℝ := fun t ↦ G (fun i ↦ (t i - b₀) / (1 - a))

/-- **The retreat data at `a`**, the quadruple `(b₀, ε₀, ζ, ϱ)` of translation, retreat, threshold
buffer and mollifier radius:
`(aδ/(100k), a/100, aδ/2, aδ/(1000k))`.

Every entry is `a` times a rational multiple of `δ` or of `1`, so each of the two margins the
retreat has to clear is `a` times a fixed positive rational — which is what makes them checkable
once and for all rather than at each `a`. -/
@[gap212 "def_retreat_data"]
noncomputable def retreatData (p : SupportParams) (k : ℕ) (a : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (a * p.δ / (100 * k), a / 100, a * p.δ / 2, a * p.δ / (1000 * k))

/-- **Mollification** at radius `ϱ` against a kernel `φ`:
`(M_{φ,ϱ}G)(t) = ∫ G(t - y) ϱ^{-k} φ(y/ϱ) dy`.

Written as Mathlib's `convolution` of the rescaled kernel with `G` — the two are the same integral
by definition — so that the support and `L²`-convergence lemmas of `Mathlib.Analysis.Convolution`
apply to it directly. The hypotheses on `φ` (non-negative, smooth, supported in the unit ball,
total mass one) are carried by the statements that use this, not by the operation. -/
@[gap212 "def_mollification"]
noncomputable def mollify {k : ℕ} (φ : (Fin k → ℝ) → ℝ) (ϱ : ℝ) (G : (Fin k → ℝ) → ℝ) :
    (Fin k → ℝ) → ℝ :=
  (fun y ↦ (ϱ ^ k)⁻¹ * φ (ϱ⁻¹ • y)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G

/-- **The tail transform** `(𝒯g)(t) = ∫_t^∞ g(s) ds`.

It is the primitive that runs the tensor construction backwards: a product of tails is supported on
a *downward* box, which is the shape the support region can contain, while its mixed derivative
recovers the product of the `g`'s up to one common sign. -/
@[gap212 "def_tail_transform"]
noncomputable def tailTransform (g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in Set.Ioi t, g s

/-- **The `i`-th tensor marginal** `Γᵢ(u) = ∑_l cₗ (∫_0^∞ g_{l,i}) ∏_{s ≠ i} g_{l,s}(u_s)`, for a
tensor datum whose factors are the tails of the `g_{l,i}`.

Integrating the `i`-th coordinate of `∑_l cₗ ∏_i g_{l,i}` out over `[0,∞)` factors through each
term, because each term is a product: the `i`-th factor contributes its total mass and the others
are untouched. -/
@[gap212 "def_tensor_marginal"]
noncomputable def tensorMarginal {L m : ℕ} (c : Fin L → ℝ) (g : Fin L → Fin (m + 1) → ℝ → ℝ)
    (i : Fin (m + 1)) (u : Fin m → ℝ) : ℝ :=
  ∑ l : Fin L, c l * (∫ t in Set.Ioi (0 : ℝ), g l i t) * ∏ s : Fin m, g l (i.succAbove s) (u s)

/-- **The high part of the `i`-th tensor marginal**: the same sum restricted to the high index set
`𝒰(i)`, the terms whose other factors are not confined to the marginal region.

The computable numerator is `∫ (Γᵢ² - Γ_{i,𝒰}²)`, so this is exactly the part that has to be shown
negligible as the mesh shrinks — and it is, because below the cutoff it can only be non-zero inside
a strip whose width is a fixed multiple of the mesh. -/
@[gap212 "def_tensor_marginal_high"]
noncomputable def tensorMarginalHigh {L m : ℕ} (c : Fin L → ℝ) (g : Fin L → Fin (m + 1) → ℝ → ℝ)
    (𝓤 : Finset (Fin L)) (i : Fin (m + 1)) (u : Fin m → ℝ) : ℝ :=
  ∑ l ∈ 𝓤, c l * (∫ t in Set.Ioi (0 : ℝ), g l i t) * ∏ s : Fin m, g l (i.succAbove s) (u s)

end Gap212.GPY
