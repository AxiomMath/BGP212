/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Defs
public import Gap212.Consequences.BundleNormalization
public import Gap212.Equidistribution.Estimates.Assumed
public import Gap212.Packing.TypeI
public import Gap212.Routing.BandUnionAtScale
public import Gap212.Routing.ContainmentsAtScale
public import Gap212.Routing.Retreat
public import Gap212.Routing.Widths
public import Gap212.Windows.Bridges
public meta import Gap212.Attr

/-!
# The routes composed at one `x`, general in the support

The three per-type equidistribution lemmas, stated in their natural generality: at an arbitrary
support datum `p`, an arbitrary band `(j, j', m, m')`, with the packing
Conditions as **hypotheses** rather than facts about a chosen datum. Nothing here mentions
`Gap212.gap212Params` or `Gap212.gap212ParamsPointA`; the level is `Gap212.Bridges.omegaMax p j j'`
throughout.

## What makes the bare capacities reachable

`Gap212.Routing.hasDivisorIn_of_qgen_strict` concludes `Gap212.HasDivisorIn q x a b` — an **open**
window — from the two-block packing condition at the **bare** capacities `b` and `1/2 - a`. The two
strictnesses come from the retreat `1 - ε₀` at the top and from the threshold `ε₁` at the bottom,
so no inward inset is charged to the Conditions. That is what lets Condition A and Condition E,
whose capacities are exhausted, be consumed as stated. The threshold is `ε₁ = ε₀ δ / 2`, the same
number on every branch, which is why one `ε₁` serves the whole statement.

## The width is chosen per `x`

Each of the four bilinear estimates quantifies its width `δ` *after* its constant `C`, so the width
may be read off the exponent `γ = log_x N` of the member at hand. Type I uses this: below the
half-power the width is `Gap212.Packing.deltaStarI₁ γ ω ϵ`, above it the constant
`deltaStarI₂ ω ϵ`, and above `1/2 + 2ω + ε'` the modulus family carries no window at all and the
datum's own `δ` serves. Type III does not need it — `Gap212.moduliIII` reads no scale, so its width
is the constant `Gap212.Routing.deltaStarIII'`.

## What is here

Type I and Type III are assembled here. Type II needs all three of the IIa, IIb and IIc routes; its
IIa containment is here, and the assembly is `Gap212.typeII_equidistribution`, with the IIb and
IIc containments `Gap212.mem_moduliIIb_of_conditionC` and `Gap212.mem_moduliIIc_of_conditionD`.

## Main results

* `Gap212.typeI_equidistribution`: Type I equidistribution over the generated moduli.
* `Gap212.typeIII_equidistribution`: Type III equidistribution over the generated moduli.
* `Gap212.mem_moduliI_low_of_conditionA`, `mem_moduliI_high_of_conditionAHigh`,
  `mem_moduliIII_of_conditionE`, `mem_moduliIIa_of_conditionB`: the four route containments the
  bare-capacity window serves, each at an arbitrary support and from its Condition alone.
* `Gap212.hasEquidistribution_of_subset`, `Gap212.qstarAboveSum_le_of_forall_qgen`: the two
  bookkeeping steps the composition needs — restricting a bound to a subfamily, and pooling the
  bands of `Gap212.Qstar` while the threshold restriction is carried along.
* `Gap212.omegaMax_le_last`, `Gap212.pos_sub_eps_of_omegaMax_pos`: the facts about `ω(j,j')` that
  the scalar conditions are converted through.
-/

@[expose] public section

namespace Gap212

open Finset Real Gap212.Bridges Gap212.Packing

/-! ## Bookkeeping -/

/-- **Equidistribution restricts to a subfamily.** The summand is a norm, so dropping moduli can
only shrink the sum and the same constant serves. -/
theorem hasEquidistribution_of_subset {x : ℝ} {D' D : Finset ℕ} {f : ℕ → ℂ} {a : ℕ} {A C : ℝ}
    (hD : D' ⊆ D) (h : HasEquidistribution x D f a A C) : HasEquidistribution x D' f a A C := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ norm_nonneg _) h
  exact Finset.filter_subset_filter _ hD

open Classical in
/-- **The band union, with the threshold carried along.** `Gap212.qstarSum_le_of_forall_qgen`
pools the bands of `Gap212.Qstar`; the per-type lemmas bound only the moduli above
`x^{1/2-ε₁}`, and their assembly pools exactly those. The argument is the same union bound over the
same `bandCount p` index tuples — only the sets being covered carry one extra conjunct. -/
theorem qstarAboveSum_le_of_forall_qgen {f : ℕ → ℂ} {p : SupportParams} {x ε₀ ε₁ : ℝ} {a : ℕ}
    {c : ℝ}
    (hbound : ∀ (j j' : Fin p.n) (m m' : ℕ), m ≤ ⌊1 / p.δ⌋₊ → m' ≤ ⌊1 / p.δ⌋₊ →
      ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ |
          (q ∈ Qgen p x j j' m m' ε₀ ∧ x ^ (1 / 2 - ε₁) < (q : ℝ)) ∧ Squarefree q},
        ‖sumError f q a‖ ≤ c) :
    ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ |
        (q ∈ Qstar p x ε₀ ∧ x ^ (1 / 2 - ε₁) < (q : ℝ)) ∧ Squarefree q},
      ‖sumError f q a‖ ≤ (bandCount p : ℝ) * c := by
  set S : Finset (Fin p.n × Fin p.n × ℕ × ℕ) :=
    univ ×ˢ univ ×ˢ Finset.Iic ⌊1 / p.δ⌋₊ ×ˢ Finset.Iic ⌊1 / p.δ⌋₊
  set G : Fin p.n × Fin p.n × ℕ × ℕ → Finset ℕ := fun t ↦
    {q ∈ Finset.Icc 1 ⌊x⌋₊ |
      (q ∈ Qgen p x t.1 t.2.1 t.2.2.1 t.2.2.2 ε₀ ∧ x ^ (1 / 2 - ε₁) < (q : ℝ)) ∧ Squarefree q}
  have hcover : ∀ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ |
      (q ∈ Qstar p x ε₀ ∧ x ^ (1 / 2 - ε₁) < (q : ℝ)) ∧ Squarefree q}, ∃ t ∈ S, q ∈ G t := by
    intro q hq
    simp only [Finset.mem_filter, Qstar, Set.mem_iUnion, exists_prop] at hq
    obtain ⟨hqIcc, ⟨⟨j, j', m, hmK, m', hm'K, hm'⟩, hqbig⟩, hqsf⟩ := hq
    exact ⟨(j, j', m, m'), Finset.mem_product.2 ⟨mem_univ _, mem_product.2 ⟨mem_univ _,
      mem_product.2 ⟨hmK, hm'K⟩⟩⟩, Finset.mem_filter.2 ⟨hqIcc, ⟨hm', hqbig⟩, hqsf⟩⟩
  refine (Routing.sum_le_sum_of_cover (fun q ↦ norm_nonneg (sumError f q a)) hcover).trans ?_
  calc ∑ t ∈ S, ∑ q ∈ G t, ‖sumError f q a‖
      ≤ ∑ _t ∈ S, c := Finset.sum_le_sum fun t ht ↦ by
        simp only [S, Finset.mem_product, Finset.mem_univ, Finset.mem_Iic, true_and] at ht
        exact hbound _ _ _ _ ht.1 ht.2
    _ = (bandCount p : ℝ) * c := by simp [S, bandCount, mul_assoc]

/-! ## The level and the caps -/

/-- **The level is bounded by the top node**, `ω(j,j') ≤ A_n - 1/4`: `A` is strictly monotone, so
both `A_{j+1}` and `A_{j'+1}` are at most `A_n`. This is how the scalar conditions — stated at
`A_n` — are converted into bounds on the widths, which are stated at `ω(j,j')`. -/
theorem A_succ_le_last (p : SupportParams) (k : Fin p.n) : p.A k.succ ≤ p.A (Fin.last p.n) :=
  p.A_mono.monotone (Fin.le_last _)

/-- The level `ω(j,j')` is at most `A_n - 1/4`. -/
theorem omegaMax_le_last (p : SupportParams) (j j' : Fin p.n) :
    omegaMax p j j' ≤ p.A (Fin.last p.n) - 1 / 4 := by
  unfold omegaMax
  linarith [A_succ_le_last p j, A_succ_le_last p j']

/-- **A positive level forces both mixed caps positive.** `ω(j,j') > 0` says
`A_{j+1} + A_{j'+1} > 1/2`, and `A_{j'+1} ≤ A_n < 1/2 - ε`, so `A_{j+1} > ε`; the other side is
`A_{j'+1} > A_0 = -ε` outright. These are what `Gap212.Routing.qgen_antitone` asks of the caps, and
they are what lets the conclusion be asserted at *every* `ε₀ > 0` rather than only at small
ones. -/
theorem pos_sub_eps_of_omegaMax_pos {p : SupportParams} {j j' : Fin p.n}
    (hω : 0 < omegaMax p j j') : 0 ≤ p.A j.succ - p.ε ∧ 0 ≤ p.A j'.succ + p.ε := by
  have hzero : p.A 0 < p.A j'.succ := p.A_mono (Fin.succ_pos _)
  unfold omegaMax at hω
  exact ⟨by linarith [A_succ_le_last p j', p.A_last], by linarith [p.A_zero]⟩

/-- **Every rung of a `B`-row is nonnegative**: it is `0` at `m = 0` and exceeds `δ > 0` after. -/
theorem brow_nonneg (p : SupportParams) (j : Fin p.n) (m : ℕ) : 0 ≤ p.B j m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact (p.B_zero j).ge
  · exact (p.δ_pos.trans (p.B_lt j m hm)).le

/-- The slack `ϵ = 10⁻¹⁰` is positive and small. -/
private theorem slack_pos_lt : 0 < slack ∧ slack < 1 / 1000 := by
  unfold slack; norm_num

/-- A generated modulus at a positive level lies in the ambient range at that level. -/
private theorem mem_moduliRange_of_omegaMax_pos {p : SupportParams} {x ε₀ : ℝ} {j j' : Fin p.n}
    {m m' q : ℕ} (hx : 1 < x) (hε₀ : 0 < ε₀) (hω : 0 < omegaMax p j j')
    (hq : q ∈ Qgen p x j j' m m' ε₀) : q ∈ moduliRange x (omegaMax p j j') :=
  Routing.mem_moduliRange_of_qgen hx hε₀ (by unfold omegaMax at hω; linarith) hq

/-- The threshold `ε₁ ≤ ε₀ δ / 2` is strictly below `ε₀ c` for any capacity `c ≥ δ`. -/
private theorem thr_lt_of_le {ε₀ ε₁ δ c : ℝ} (hε₀ : 0 < ε₀) (hδ : 0 < δ)
    (hε₁ : ε₁ ≤ ε₀ * δ / 2) (hc : δ ≤ c) : ε₁ < ε₀ * c := by
  nlinarith

/-! ## The extraction threshold

All three routes reach the same moduli, and the value below is what each of them produces: the
`min ε₀ (1/2)` is the retreat the extraction needs (`Gap212.Routing.qgen_antitone` carries the
conclusion back up to every `ε₀ > 0`), the `δ/2` makes `ε₁ = ε₀δ/2`, and the `ϵ/16` is
the Type IIc level bound. Naming it is what lets the bands of `Gap212.Qstar` be pooled: a threshold
existentially quantified per band could not be minimised over them. -/

/-- **The extraction threshold** `ε₁ = min(min(ε₀, 1/2) · δ / 2, ϵ/16)`, the same for every band
and every route. -/
noncomputable def extractionThreshold (p : SupportParams) (ε₀ : ℝ) : ℝ :=
  min (min ε₀ (1 / 2) * p.δ / 2) (slack / 16)

/-- The extraction threshold is positive whenever `ε₀ > 0`. -/
theorem extractionThreshold_pos {p : SupportParams} {ε₀ : ℝ} (h : 0 < ε₀) :
    0 < extractionThreshold p ε₀ := by
  have := mul_pos (lt_min h one_half_pos) p.δ_pos
  exact lt_min (by linarith) (by linarith [slack_pos_lt.1])

/-- The extraction threshold is at most `min(ε₀, 1/2) · δ / 2`. -/
theorem extractionThreshold_le_retreat (p : SupportParams) (ε₀ : ℝ) :
    extractionThreshold p ε₀ ≤ min ε₀ (1 / 2) * p.δ / 2 := min_le_left _ _

/-- The extraction threshold is at most `ϵ/16`. -/
theorem extractionThreshold_le_slack (p : SupportParams) (ε₀ : ℝ) :
    extractionThreshold p ε₀ ≤ slack / 16 := min_le_right _ _

/-! ## The commensurability constant as an exponent

`Gap212.ConstantBundle.asympEq` compares `M * N` with `x` up to the constants `a_∓`, so the second
scale of a Type I or Type II member obeys `N ≤ a_+ x` and no better. The Baker–Irving estimate
wants an *exponent* bound `N ≤ x^{γ₂}`, and `γ₂ = 1 + log a_+ / log 3` supplies it at every
`x ≥ 3`. -/

/-- **A constant is an exponent from `x = 3` on.** For `1 ≤ c` and `3 ≤ x`,
`c ≤ x^{log c / log 3}`. -/
theorem le_rpow_log_div_log_three {c x : ℝ} (hc : 1 ≤ c) (hx : 3 ≤ x) :
    c ≤ x ^ (Real.log c / Real.log 3) := by
  rw [Real.rpow_def_of_pos (by linarith), mul_comm, ← Real.log_le_iff_le_exp (by linarith),
    div_mul_eq_mul_div, le_div_iff₀ (Real.log_pos (by norm_num))]
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hx) (Real.log_nonneg hc)

/-! ## Type III

`Gap212.moduliIII` reads neither a scale nor the analytic loss, so the Type III route has one
window at one width — the constant `Gap212.Routing.deltaStarIII'` — and the only thing the member
contributes is its four scales. -/

/-- **The Type III window's two capacities.** With `b = 1/3 + 4δ*/3 - 4ω/3` the window's top and
`a = b - δ*` its bottom, `b = 1 - 6ω - (3/2)ξ₃ - (8/3)ϵ` and
`1/2 - a = (5/2)ω + (3/8)ξ₃ + (2/3)ϵ`. The first is Condition E's first capacity **exactly**, which
is why that condition carries `(8/3)ϵ` rather than the `2ϵ` of [2, Proposition 3]. -/
theorem typeIII_window_caps (ω ξ₃ : ℝ) :
    1 / 3 + 4 * Routing.deltaStarIII' ω ξ₃ slack / 3 - 4 * ω / 3
        = 1 - 6 * ω - 3 / 2 * ξ₃ - 8 / 3 * slack ∧
      1 / 2 - (1 / 3 + 4 * Routing.deltaStarIII' ω ξ₃ slack / 3 - 4 * ω / 3
          - Routing.deltaStarIII' ω ξ₃ slack)
        = 5 / 2 * ω + 3 / 8 * ξ₃ + 2 / 3 * slack := by
  unfold Routing.deltaStarIII'
  constructor <;> ring

/-- **`Q ⊆ D_III`, from Condition E alone**, at an arbitrary support. Every generated modulus above
`x^{1/2-ε₁}` carries a divisor in the Type III window, with `ε₁ = ε₀ δ / 2` and **no inward inset
on either capacity** — the strictness comes from the retreat and from `ε₁`, through
`Gap212.Routing.hasDivisorIn_of_qgen_strict`.

The two window conditions the route assumes appear as `hwin₂` (`1/2 - a ≥ δ`) and, through
`hω`/`hξ₃`, the positivity of the window's lower end. -/
@[gap212 "lem_typeIII_containment"]
theorem mem_moduliIII_of_conditionE {p : SupportParams} {ξ₃ x ε₀ ε₁ : ℝ}
    {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₁ : ε₁ ≤ ε₀ * p.δ / 2)
    (hscalarIII : p.δ < 11 / 8 - 7 / 2 * p.A (Fin.last p.n) - 9 / 8 * ξ₃ - 2 * slack)
    (hE : Defs.ConditionE (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (1 - 6 * omegaMax p j j' - 3 / 2 * ξ₃ - 8 / 3 * slack)
      (5 / 2 * omegaMax p j j' + 3 / 8 * ξ₃ - 2 * slack))
    (hω : omegaMax p j j' ∈ Set.Ioo (0 : ℝ) (1 / 12)) (hξ₃ : ξ₃ < 1 / 2)
    (hwin₂ : p.δ ≤ 5 / 2 * omegaMax p j j' + 3 / 8 * ξ₃ + 2 / 3 * slack)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hq : q ∈ Qgen p x j j' m m' ε₀) (hqbig : x ^ (1 / 2 - ε₁) ≤ (q : ℝ)) :
    q ∈ moduliIII x (omegaMax p j j') (Routing.deltaStarIII' (omegaMax p j j') ξ₃ slack) := by
  classical
  obtain ⟨hcap₁, hcap₂⟩ := typeIII_window_caps (omegaMax p j j') ξ₃
  have hs := slack_pos_lt
  have hδs : p.δ < Routing.deltaStarIII' (omegaMax p j j') ξ₃ slack := by
    rw [Routing.deltaStarIII']; linarith [omegaMax_le_last p j j']
  rw [← Routing.moduliIIIFamily_eq_moduliIII x (omegaMax p j j') 0 _ 0, moduliIIIFamily,
    Finset.mem_filter]
  -- the window's lower end is positive: `1/2 - a = (5/2)ω + (3/8)ξ₃ + (2/3)ϵ < 1/2`
  refine ⟨mem_moduliRange_of_omegaMax_pos hx hε₀ hω.1 hq,
    Routing.hasDivisorIn_of_qgen_strict hx p.δ_pos hε₀ hε₀1 (by linarith [hω.2]) (by linarith)
      (thr_lt_of_le hε₀ p.δ_pos hε₁ (hwin₂.trans hcap₂.ge)) hB hB'
      (fun y hy ↦ (hE y hy).mono hcap₁.ge (by linarith)) hq hqbig⟩

open Classical in
/-- **Type III equidistribution over the generated moduli.**
Assume the scalar Type III condition and Condition E at the band,
and suppose `ω(j,j') ∈ (0, 1/12)`, `ξ₃ + ϵ < 1/2` and `0 < δ*_III < 1/4 + ω(j,j')`. Then for every
bundle `K` and every `ε₀ > 0` there is an `ε₁ > 0` such that for every `A > 0` there is a `C` with:
for every `x ≥ 3`, every `f` of Type III at `(K, x)` for `ξ₃` and every `a` coprime below `x`, the
squarefree generated moduli above `x^{1/2-ε₁}` carry `∑ |Δ(f;q,a)| ≤ C x (log x)^{-A}`.

`ε₁ = min(ε₀, 1/2) · δ / 2`, which depends only on `ε₀` and the datum, as the extraction lemma
requires; the `min` is what extends the conclusion from the small retreats the extraction needs to
every `ε₀ > 0`, through `Gap212.Routing.qgen_antitone`.

The width is the constant `δ*_III` at every `x`: `Gap212.moduliIII` reads no scale, so unlike the
four bilinear estimates nothing here has to be chosen per `x`. The four scale hypotheses of
`Gap212.TypeIIIPolymath` hold at `κ = ξ₃ + ϵ` with constant `1`, which is where the bundle
normalization is spent, and the wall reads `4 - 4ϵ ≤ 4`. -/
theorem typeIII_bound (h₅ : TypeIIIPolymath)
    {p : SupportParams} {ξ₃ : ℝ} {j j' : Fin p.n} {m m' : ℕ}
    (hscalarIII : p.δ < 11 / 8 - 7 / 2 * p.A (Fin.last p.n) - 9 / 8 * ξ₃ - 2 * slack)
    (hE : Defs.ConditionE (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (1 - 6 * omegaMax p j j' - 3 / 2 * ξ₃ - 8 / 3 * slack)
      (5 / 2 * omegaMax p j j' + 3 / 8 * ξ₃ - 2 * slack))
    (hω : omegaMax p j j' ∈ Set.Ioo (0 : ℝ) (1 / 12))
    (hξ₃ : 0 < ξ₃) (hκ : ξ₃ + slack < 1 / 2)
    (hδstar : 0 < Routing.deltaStarIII' (omegaMax p j j') ξ₃ slack)
    (hδstarhi : Routing.deltaStarIII' (omegaMax p j j') ξ₃ slack < 1 / 4 + omegaMax p j j')
    (hwin₂ : p.δ ≤ 5 / 2 * omegaMax p j j' + 3 / 8 * ξ₃ + 2 / 3 * slack)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1) (K : ConstantBundle) :
    ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ,
      ∀ x ≥ (3 : ℝ), ∀ f : ℕ → ℂ, ∀ a : ℕ, TypeIII K x ξ₃ f → CoprimeBelow a x →
        HasEquidistribution x
          {q ∈ Finset.Icc 1 ⌊x⌋₊ |
            q ∈ Qgen p x j j' m m' ε₀ ∧ x ^ (1 / 2 - extractionThreshold p ε₀) < (q : ℝ)}
          f a A C := by
  intro ε₀ hε₀ A hA
  have hs := slack_pos_lt
  have hδpos := p.δ_pos
  -- the estimate, at the level, `κ = ξ₃ + ϵ`, the constant width and the slack `θ = 3ϵ`
  obtain ⟨eps, heps, hmain⟩ := h₅ K.flat (omegaMax p j j') hω (ξ₃ + slack) ⟨by linarith, hκ⟩
    (Routing.deltaStarIII' (omegaMax p j j') ξ₃ slack) ⟨hδstar, hδstarhi⟩ (3 * slack) (by linarith)
  obtain ⟨C, hC⟩ := hmain (eps / 2) ⟨by linarith, by linarith⟩ A hA
  refine ⟨C, fun x hx f a hf ha ↦ ?_⟩
  have hx1 : (1 : ℝ) < x := by linarith
  obtain ⟨-, -, halo, hahi, -, hcoeff, hloc, hsmooth, -, hasymp⟩ := constantBundle_flat_transfer K
  obtain ⟨α, ψ₁, ψ₂, ψ₃, M, hM, N₁, hN₁, N₂, hN₂, N₃, hN₃, hfeq, hα, hp₁, hp₂, hp₃, hαM,
    hs₁, hs₂, hs₃, hprod, hN₁lo, hN₁hi, hN₂lo, hN₂hi, hN₃lo, hN₃hi, h₁₂, h₁₃, h₂₃⟩ := hf
  -- the pairwise and individual scale bounds, at `κ` and with constant `1`
  have hpair : ∀ z : ℝ, x ^ (1 - ξ₃ - slack) ≤ z → K.flat.asympLo * x ^ (1 - (ξ₃ + slack)) ≤ z :=
    fun z hz ↦ (mul_le_of_le_one_left (by positivity) halo).trans (by rwa [← sub_sub])
  have hsingle : ∀ z : ℝ, x ^ (1 - 2 * ξ₃ - slack) ≤ z →
      K.flat.asympLo * x ^ (1 - 2 * (ξ₃ + slack)) ≤ z := fun z hz ↦
    (mul_le_of_le_one_left (by positivity) halo).trans
      ((Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)).trans hz)
  have hupper : ∀ z : ℝ, z ≤ x ^ (ξ₃ + slack) → z ≤ K.flat.asympHi * x ^ (ξ₃ + slack) :=
    fun z hz ↦ hz.trans (le_mul_of_one_le_left (by positivity) hahi)
  have hEq := hC x hx α ψ₁ ψ₂ ψ₃ M hM N₁ hN₁ N₂ hN₂ N₃ hN₃ a
    (hcoeff α hα) (hcoeff ψ₁ hp₁) (hcoeff ψ₂ hp₂) (hcoeff ψ₃ hp₃) (hloc α M hαM)
    (hsmooth ψ₁ N₁ hs₁) (hsmooth ψ₂ N₂ hs₂) (hsmooth ψ₃ N₃ hs₃) (hasymp _ _ hprod)
    (hpair _ h₁₂) (hpair _ h₁₃) (hpair _ h₂₃)
    (hsingle _ hN₁lo) (hupper _ hN₁hi) (hsingle _ hN₂lo) (hupper _ hN₂hi)
    (hsingle _ hN₃lo) (hupper _ hN₃hi)
    (by rw [Routing.deltaStarIII']; linarith) ha
  rw [← hfeq] at hEq
  -- the containment, on the moduli the threshold reaches
  refine hasEquidistribution_of_subset (fun q hq ↦ ?_) hEq
  obtain ⟨-, hqQ, hqbig⟩ := Finset.mem_filter.1 hq
  obtain ⟨hAj, hAj'⟩ := pos_sub_eps_of_omegaMax_pos hω.1
  exact mem_moduliIII_of_conditionE hx1 (lt_min hε₀ one_half_pos)
    (min_lt_of_right_lt one_half_lt_one) (extractionThreshold_le_retreat p ε₀) hscalarIII hE hω
    (by linarith) hwin₂ hB hB' (Routing.qgen_antitone hx1 (min_le_left _ _) (brow_nonneg p j m)
      (brow_nonneg p j' m') hAj hAj' hqQ) hqbig.le

/-! ## Type I

Two windows and one threshold. Below the half-power the width is `δ*_{I,low}(γ)`, which makes the
estimate's wall an identity; above it the constant `δ*_{I,high}`, which makes it `1 - 14ϵ`; and
above `1/2 + 2ω + ε'` the family is the whole ambient range and neither the wall nor a window is
asked for. Both windows are consumed at their bare capacities, so Condition A and Condition A′ are
quoted as stated. -/

/-- **`Q ⊆ D_I`, low range, from Condition A**, at an arbitrary support. The window is
`(γ - δ* - 3ε', γ - 3ε')` at `δ* = δ*_{I,low}(γ)`, so its capacities are `γ - 3ε'` and
`1/6 - 4ω - ϵ + 3ε'` — Condition A's `ξ₁ - 2ϵ` and `1/6 - 4ω - 2ϵ` clear both once `3ε' ≤ ϵ`. -/
@[gap212 "lem_typeI_low_containment"]
theorem mem_moduliI_low_of_conditionA {p : SupportParams} {ξ₁ x ε₀ ε₁ ε' γ ω : ℝ}
    {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₁ : ε₁ ≤ ε₀ * p.δ / 2)
    (hε'0 : 0 ≤ ε') (hε' : 3 * ε' ≤ slack)
    (hscalarI : p.δ < ξ₁ - 4 * p.A (Fin.last p.n) + 2 / 3 - 2 * slack) (hξ₁ : ξ₁ ≤ 1 / 2)
    (hωeq : ω = omegaMax p j j') (hω : 0 < ω)
    (hA : Defs.ConditionA (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (ξ₁ - 2 * slack) (1 / 6 - 4 * ω - 2 * slack))
    (hγlo : ξ₁ - slack ≤ γ) (hγhi : γ ≤ 1 / 2)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hq : q ∈ Qgen p x j j' m m' ε₀) (hqbig : x ^ (1 / 2 - ε₁) ≤ (q : ℝ)) :
    q ∈ moduliIFamily x ω γ (deltaStarI₁ γ ω slack) ε' := by
  classical
  subst hωeq
  have hs := slack_pos_lt
  have hlast := omegaMax_le_last p j j'
  rw [moduliIFamily, if_pos hγhi, Finset.mem_filter]
  refine ⟨mem_moduliRange_of_omegaMax_pos hx hε₀ hω hq,
    Routing.hasDivisorIn_of_qgen_strict hx p.δ_pos hε₀ hε₀1 ?_ ?_ (thr_lt_of_le hε₀ p.δ_pos hε₁ ?_)
      hB hB' (fun y hy ↦ (hA y hy).mono (by linarith) ?_) hq hqbig⟩ <;>
  · rw [deltaStarI₁]; linarith

/-- **`Q ⊆ D_I`, high range, from Condition A′**, at an arbitrary support. Here the window sits
near `x^{1-γ}`: its capacities are `1 - γ - 3ε'` and `γ - 1/2 + δ*_{I,high} + 3ε'`, and Condition
A′'s `1/2 - 2ω - 2ϵ` and `1/14 - (68/14)ω - 2ϵ` clear both, the second because `γ > 1/2` on this
range. -/
@[gap212 "lem_typeI_high_containment"]
theorem mem_moduliI_high_of_conditionAHigh {p : SupportParams} {x ε₀ ε₁ ε' γ ω : ℝ}
    {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₁ : ε₁ ≤ ε₀ * p.δ / 2)
    (hε'0 : 0 ≤ ε') (hε' : 3 * ε' ≤ slack)
    (hscalarI : p.δ < 9 / 7 - 34 / 7 * p.A (Fin.last p.n) - 2 * slack)
    (hωeq : ω = omegaMax p j j') (hω : 0 < ω)
    (hA' : Defs.ConditionAHigh (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (1 / 2 - 2 * ω - 2 * slack) (1 / 14 - 68 * ω / 14 - 2 * slack))
    (hγlo : ¬ (γ ≤ 1 / 2)) (hγhi : γ ≤ 1 / 2 + 2 * ω + ε')
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hq : q ∈ Qgen p x j j' m m' ε₀) (hqbig : x ^ (1 / 2 - ε₁) ≤ (q : ℝ)) :
    q ∈ moduliIFamily x ω γ (deltaStarI₂ ω slack) ε' := by
  classical
  subst hωeq
  have hs := slack_pos_lt
  have hγ : 1 / 2 < γ := not_le.mp hγlo
  have hlast := omegaMax_le_last p j j'
  rw [moduliIFamily, if_neg hγlo, if_pos hγhi, Finset.mem_filter]
  refine ⟨mem_moduliRange_of_omegaMax_pos hx hε₀ hω hq,
    Routing.hasDivisorIn_of_qgen_strict hx p.δ_pos hε₀ hε₀1 ?_ ?_ (thr_lt_of_le hε₀ p.δ_pos hε₁ ?_)
      hB hB' (fun y hy ↦ (hA' y hy).mono (by linarith) ?_) hq hqbig⟩ <;>
  · rw [deltaStarI₂]; linarith

open Classical in
/-- **Type I equidistribution over the generated moduli.**
Assume the scalar Type I condition, Condition A and Condition A′ at
the band, and suppose `ω(j,j') ∈ (0, 1/4)`. Then for every bundle `K` and every `ε₀ > 0` there is
an `ε₁ > 0` such that for every `A > 0` there is a `C` with: for every `x ≥ 3`, every `f` of Type I
at `(K, x)` for `ξ₁` and every `a` coprime below `x`, the squarefree generated moduli above
`x^{1/2-ε₁}` carry `∑ |Δ(f;q,a)| ≤ C x (log x)^{-A}`.

Three branches, one threshold `ε₁ = min(ε₀, 1/2) · δ / 2`. The exponent window handed to
`Gap212.TypeIBakerIrving` is `[ξ₁ - ϵ, 1 + log a₊ / log 3]`: the lower end is the class's own scale
bound, and the upper end turns the commensurability constant `a₊` into an exponent at every
`x ≥ 3`, which is what `Gap212.le_rpow_log_div_log_three` supplies. The width is then read off the
branch the exponent `γ = log_x N` falls in, legitimately because the estimate quantifies `δ` after
`C`: in the first branch the wall is the identity `1 + θ = 1 + θ`, in the second it is
`1 - 14ϵ ≤ 1 - θ`, and in the third both of its antecedents are false and the datum's own `δ`
serves. -/
theorem typeI_bound (h₃ : TypeIBakerIrving)
    {p : SupportParams} {ξ₁ : ℝ} {j j' : Fin p.n} {m m' : ℕ}
    (hscalarI : p.δ < min (ξ₁ - 4 * p.A (Fin.last p.n) + 2 / 3)
      (9 / 7 - 34 / 7 * p.A (Fin.last p.n)) - 2 * slack)
    (hA : Defs.ConditionA (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (ξ₁ - 2 * slack) (1 / 6 - 4 * omegaMax p j j' - 2 * slack))
    (hA' : Defs.ConditionAHigh (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (1 / 2 - 2 * omegaMax p j j' - 2 * slack)
      (1 / 14 - 68 * omegaMax p j j' / 14 - 2 * slack))
    (hω : omegaMax p j j' ∈ Set.Ioo (0 : ℝ) (1 / 4)) (hξ₁ : ξ₁ ≤ 1 / 2)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1) (K : ConstantBundle) :
    ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ,
      ∀ x ≥ (3 : ℝ), ∀ f : ℕ → ℂ, ∀ a : ℕ, TypeI K x ξ₁ f → CoprimeBelow a x →
        HasEquidistribution x
          {q ∈ Finset.Icc 1 ⌊x⌋₊ |
            q ∈ Qgen p x j j' m m' ε₀ ∧ x ^ (1 / 2 - extractionThreshold p ε₀) < (q : ℝ)}
          f a A C := by
  intro ε₀ hε₀ A hA₀
  have hs := slack_pos_lt
  have hδpos := p.δ_pos
  -- the two branches of the scalar condition
  rw [lt_sub_iff_add_lt, lt_min_iff] at hscalarI
  obtain ⟨hsc₁, hsc₂⟩ := hscalarI
  have hlast := omegaMax_le_last p j j'
  have he0 : 0 < min ε₀ (1 / 2) := lt_min hε₀ one_half_pos
  have he1 : min ε₀ (1 / 2) < 1 := min_lt_of_right_lt one_half_lt_one
  have hthr := extractionThreshold_le_retreat p ε₀
  obtain ⟨hAj, hAj'⟩ := pos_sub_eps_of_omegaMax_pos hω.1
  have hahi : 1 ≤ K.flat.asympHi := K.one_le_flat_asympHi
  have hL : 0 ≤ Real.log K.flat.asympHi / Real.log 3 :=
    div_nonneg (Real.log_nonneg hahi) (Real.log_nonneg (by norm_num))
  obtain ⟨eps, heps, hmain⟩ := h₃ K.flat (omegaMax p j j') hω (3 * slack) (by linarith)
    (ξ₁ - slack) (1 + Real.log K.flat.asympHi / Real.log 3) (by linarith [hω.1]) (by linarith)
  set ε' : ℝ := min (eps / 2) (slack / 3)
  have hε'pos : 0 < ε' := lt_min (by linarith) (by linarith)
  have hε'slack : 3 * ε' ≤ slack := by linarith [min_le_right (eps / 2) (slack / 3)]
  obtain ⟨C, hC⟩ := hmain ε' ⟨hε'pos, (min_le_left _ _).trans_lt (by linarith)⟩ A hA₀
  refine ⟨C, fun x hx f a hf ha ↦ ?_⟩
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  obtain ⟨-, -, -, -, -, hcoeff, hloc, hsmooth, -, hasymp⟩ := constantBundle_flat_transfer K
  obtain ⟨α, β, M, hM, N, hN, hfeq, hα, hβ, hαM, hβN, hprod, hsβ, hNlo⟩ := hf
  -- the exponent of the second scale, as an opaque number at this `x`
  obtain ⟨γ, hγL⟩ : ∃ γ : ℝ, Real.log N / Real.log x = γ := ⟨_, rfl⟩
  have hNx : N = x ^ γ := by rw [← hγL]; exact (rpow_logScale hx1 (by linarith)).symm
  have hγlo : ξ₁ - slack ≤ γ := hγL ▸ le_logScale_of_rpow_le hx1 hNlo
  have hsqrt : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
  -- the second scale is below `x^{γ₂}`, `γ₂ = 1 + log a₊ / log 3`
  have hNub : N ≤ x ^ (1 + Real.log K.flat.asympHi / Real.log 3) := by
    rw [Real.rpow_add hx0, Real.rpow_one]
    linarith [(hasymp _ _ hprod).2, le_mul_of_one_le_left (by linarith : (0 : ℝ) ≤ N) hM,
      mul_le_mul_of_nonneg_right (le_rpow_log_div_log_three hahi hx) hx0.le]
  -- the estimate, at a width the branch supplies, on `D_I` in its `γ`-shape
  have hest : ∀ δ : ℝ, 0 < δ →
      (N ≤ Real.sqrt x → 3 * γ - 12 * omegaMax p j j' - 3 * δ ≥ 1 + 3 * slack) →
      (Real.sqrt x < N → N ≤ x ^ (1 / 2 + 2 * omegaMax p j j' + ε') →
        68 * omegaMax p j j' + 14 * δ ≤ 1 - 3 * slack) →
      HasEquidistribution x (moduliIFamily x (omegaMax p j j') γ δ ε') f a A C := by
    intro δ hδ hw₁ hw₂
    rw [Routing.moduliIFamily_eq_moduliI hx1, ← hNx, hfeq]
    exact hC δ hδ x hx α β M hM N hN a (hcoeff α hα) (hcoeff β hβ) (hloc α M hαM)
      (hloc β N hβN) (hasymp _ _ hprod) (hsmooth β N hsβ) hNlo hNub (hγL ▸ hw₁) hw₂ ha
  have hqgen : Qgen p x j j' m m' ε₀ ⊆ Qgen p x j j' m m' (min ε₀ (1 / 2)) :=
    Routing.qgen_antitone hx1 (min_le_left _ _) (brow_nonneg p j m) (brow_nonneg p j' m') hAj hAj'
  by_cases hγ1 : γ ≤ 1 / 2
  · -- the low range: the width is `δ*_{I,low}(γ)` and the wall is an identity
    have hNle : N ≤ Real.sqrt x := by
      rw [hsqrt, hNx]; exact Real.rpow_le_rpow_of_exponent_le hx1.le hγ1
    refine hasEquidistribution_of_subset (fun q hq ↦ ?_)
      (hest (deltaStarI₁ γ (omegaMax p j j') slack) (by rw [deltaStarI₁]; linarith)
      (fun _ ↦ by linarith [typeI_analytic₁ (𝕜 := ℝ) γ (omegaMax p j j') slack])
      fun hlt _ ↦ absurd hlt hNle.not_gt)
    obtain ⟨-, hqQ, hqbig⟩ := Finset.mem_filter.1 hq
    exact mem_moduliI_low_of_conditionA hx1 he0 he1 hthr hε'pos.le hε'slack
      (by linarith) hξ₁ rfl hω.1 hA hγlo hγ1 hB hB' (hqgen hqQ) hqbig.le
  have hNgt : Real.sqrt x < N := by
    rw [hsqrt, hNx]; exact (Real.rpow_lt_rpow_left_iff hx1).mpr (not_le.mp hγ1)
  by_cases hγ2 : γ ≤ 1 / 2 + 2 * omegaMax p j j' + ε'
  · -- the high range: the width is the constant `δ*_{I,high}`
    refine hasEquidistribution_of_subset (fun q hq ↦ ?_)
      (hest (deltaStarI₂ (omegaMax p j j') slack) (by rw [deltaStarI₂]; linarith)
      (fun hle ↦ absurd hNgt hle.not_gt)
      fun _ _ ↦ by linarith [typeI_analytic₂ (𝕜 := ℝ) (omegaMax p j j') slack])
    obtain ⟨-, hqQ, hqbig⟩ := Finset.mem_filter.1 hq
    exact mem_moduliI_high_of_conditionAHigh hx1 he0 he1 hthr hε'pos.le hε'slack
      (by linarith) rfl hω.1 hA' hγ1 hγ2 hB hB' (hqgen hqQ) hqbig.le
  -- the unconstrained range: `D_I` is the ambient range and no wall is asked for
  refine hasEquidistribution_of_subset (fun q hq ↦ ?_) (hest p.δ hδpos
    (fun hle ↦ absurd hNgt hle.not_gt)
    fun _ hle ↦ absurd ((Real.rpow_le_rpow_left_iff hx1).1 (by rwa [hNx] at hle)) hγ2)
  rw [moduliIFamily, if_neg hγ1, if_neg hγ2]
  exact mem_moduliRange_of_omegaMax_pos hx1 hε₀ hω.1 (Finset.mem_filter.1 hq).2.1

/-! ## Type IIa

The third of the five routes cut by a single window, and the third that the bare-capacity window
serves. The other two Type II ranges ask more: `Gap212.moduliIIb` asks two nested divisors, served
by `Gap212.Extraction.three_factor_strict`, and `Gap212.moduliIIc` three, served by
`Gap212.Extraction.four_factor`. -/

/-- **`Q ⊆ D_IIa`, from Condition B**, at an arbitrary support. The window is
`(γ - 3ε' - δ*, γ - 3ε')` at `δ* = δ*_IIa(γ)`, whose capacities are `γ - 3ε'` and
`1/2 - γ + 3ε' + δ*`; Condition B's `2/5 + (24/5)ω + (7/5)δ - 2ϵ` and `1/14 - (24/7)ω - 2ϵ` clear
both on the range `[2/5 + (24/5)ω + (7/5)δ + (7/5)ϵ, 1/2]`, whose left endpoint is exactly where
`δ*_IIa(γ) ≥ δ` begins. -/
@[gap212 "lem_typeIIa_containment"]
theorem mem_moduliIIa_of_conditionB {p : SupportParams} {x ε₀ ε₁ ε' γ ω : ℝ}
    {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) (hε₁ : ε₁ ≤ ε₀ * p.δ / 2)
    (hε'0 : 0 ≤ ε') (hε' : 3 * ε' ≤ slack)
    (hωeq : ω = omegaMax p j j') (hω : 0 < ω)
    (hBcond : Defs.ConditionB (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (2 / 5 + 24 * ω / 5 + 7 * p.δ / 5 - 2 * slack) (1 / 14 - 24 * ω / 7 - 2 * slack))
    (hγlo : 2 / 5 + 24 * ω / 5 + 7 * p.δ / 5 + 7 * slack / 5 ≤ γ) (hγhi : γ ≤ 1 / 2)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hq : q ∈ Qgen p x j j' m m' ε₀) (hqbig : x ^ (1 / 2 - ε₁) ≤ (q : ℝ)) :
    q ∈ moduliIIaFamily x ω γ (Routing.deltaStarIIa γ ω slack) ε' := by
  classical
  subst hωeq
  have hs := slack_pos_lt
  have hδ := p.δ_pos
  rw [moduliIIaFamily, Finset.mem_filter]
  refine ⟨mem_moduliRange_of_omegaMax_pos hx hε₀ hω hq,
    Routing.hasDivisorIn_of_qgen_strict hx p.δ_pos hε₀ hε₀1 ?_ ?_ (thr_lt_of_le hε₀ p.δ_pos hε₁ ?_)
      hB hB' (fun y hy ↦ (hBcond y hy).mono (by linarith) ?_) hq hqbig⟩ <;>
  · rw [Routing.deltaStarIIa]; linarith

/-! ## The two equidistribution statements

Each is its explicit-threshold form with `ε₁` produced. The threshold is
`Gap212.extractionThreshold p ε₀`, so these two and the Type II statement all reach the same moduli
— which is what lets the assembly over the Harman class pool the bands. -/

open Classical in
/-- **Type I equidistribution over the generated moduli.** Assume the scalar Type I condition,
Condition A and Condition A′ at the band, `ω(j,j') ∈ (0,1/4)`, `ξ₁ ≤ 1/2` and
`B_{j,m}, B_{j',m'} ≤ 1`. Then for every bundle `K` and every `ε₀ > 0` there is an `ε₁ > 0` such
that for every `A > 0` there is a `C` with: for every `x ≥ 3`, every `f` of Type I at `(K,x)` for
`ξ₁` and every `a` coprime below `x`, the squarefree generated moduli above `x^{1/2-ε₁}` carry
`∑ |Δ(f;q,a)| ≤ C x (log x)^{-A}`. -/
@[gap212 "lem_typeI_equidistribution"]
theorem typeI_equidistribution (h₃ : TypeIBakerIrving)
    {p : SupportParams} {ξ₁ : ℝ} {j j' : Fin p.n} {m m' : ℕ}
    (hscalarI : p.δ < min (ξ₁ - 4 * p.A (Fin.last p.n) + 2 / 3)
      (9 / 7 - 34 / 7 * p.A (Fin.last p.n)) - 2 * slack)
    (hA : Defs.ConditionA (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (ξ₁ - 2 * slack) (1 / 6 - 4 * omegaMax p j j' - 2 * slack))
    (hA' : Defs.ConditionAHigh (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (1 / 2 - 2 * omegaMax p j j' - 2 * slack)
      (1 / 14 - 68 * omegaMax p j j' / 14 - 2 * slack))
    (hω : omegaMax p j j' ∈ Set.Ioo (0 : ℝ) (1 / 4)) (hξ₁ : ξ₁ ≤ 1 / 2)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1) (K : ConstantBundle) :
    ∀ ε₀ > (0 : ℝ), ∃ ε₁ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ,
      ∀ x ≥ (3 : ℝ), ∀ f : ℕ → ℂ, ∀ a : ℕ, TypeI K x ξ₁ f → CoprimeBelow a x →
        HasEquidistribution x
          {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qgen p x j j' m m' ε₀ ∧ x ^ (1 / 2 - ε₁) < (q : ℝ)}
          f a A C :=
  fun ε₀ hε₀ ↦ ⟨extractionThreshold p ε₀, extractionThreshold_pos hε₀,
    typeI_bound h₃ hscalarI hA hA' hω hξ₁ hB hB' K ε₀ hε₀⟩

open Classical in
/-- **Type III equidistribution over the generated moduli.** Assume the scalar Type III condition
and Condition E at the band, and suppose `ω(j,j') ∈ (0, 1/12)`, `0 < ξ₃`, `ξ₃ + ϵ < 1/2`,
`0 < δ*_III < 1/4 + ω(j,j')`, `δ ≤ (5/2)ω + (3/8)ξ₃ + (2/3)ϵ` and `B_{j,m}, B_{j',m'} ≤ 1`. Then
for every bundle `K` and every `ε₀ > 0` there is an `ε₁ > 0` such that for every `A > 0` there is a
`C` with: for every `x ≥ 3`, every `f` of Type III at `(K,x)` for `ξ₃` and every `a` coprime below
`x`, the squarefree generated moduli above `x^{1/2-ε₁}` carry `∑ |Δ(f;q,a)| ≤ C x (log x)^{-A}`. -/
@[gap212 "lem_typeIII_equidistribution"]
theorem typeIII_equidistribution (h₅ : TypeIIIPolymath)
    {p : SupportParams} {ξ₃ : ℝ} {j j' : Fin p.n} {m m' : ℕ}
    (hscalarIII : p.δ < 11 / 8 - 7 / 2 * p.A (Fin.last p.n) - 9 / 8 * ξ₃ - 2 * slack)
    (hE : Defs.ConditionE (Xi (p.B j m) (p.B j' m') m m' p.δ)
      (1 - 6 * omegaMax p j j' - 3 / 2 * ξ₃ - 8 / 3 * slack)
      (5 / 2 * omegaMax p j j' + 3 / 8 * ξ₃ - 2 * slack))
    (hω : omegaMax p j j' ∈ Set.Ioo (0 : ℝ) (1 / 12))
    (hξ₃ : 0 < ξ₃) (hκ : ξ₃ + slack < 1 / 2)
    (hδstar : 0 < Routing.deltaStarIII' (omegaMax p j j') ξ₃ slack)
    (hδstarhi : Routing.deltaStarIII' (omegaMax p j j') ξ₃ slack < 1 / 4 + omegaMax p j j')
    (hwin₂ : p.δ ≤ 5 / 2 * omegaMax p j j' + 3 / 8 * ξ₃ + 2 / 3 * slack)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1) (K : ConstantBundle) :
    ∀ ε₀ > (0 : ℝ), ∃ ε₁ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ,
      ∀ x ≥ (3 : ℝ), ∀ f : ℕ → ℂ, ∀ a : ℕ, TypeIII K x ξ₃ f → CoprimeBelow a x →
        HasEquidistribution x
          {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qgen p x j j' m m' ε₀ ∧ x ^ (1 / 2 - ε₁) < (q : ℝ)}
          f a A C :=
  fun ε₀ hε₀ ↦ ⟨extractionThreshold p ε₀, extractionThreshold_pos hε₀,
    typeIII_bound h₅ hscalarIII hE hω hξ₃ hκ hδstar hδstarhi hwin₂ hB hB' K ε₀ hε₀⟩

end Gap212
