/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.EndgameDefs
public import Gap212.Sieve.Certificate
public import Gap212.Support.Hereditary
public meta import Gap212.Attr

/-!
# The support geometry of the retreat

The retreat region `R⁺_k(j, ε₀)` is the stratum with both of its inequalities pulled in by the
factor `1 - ε₀` and its rough set taken at the *non-strict* threshold `δ ≤ tᵢ`, because the
constraint it transports is the one the moduli a support generates carry: a rough factor is one of
size *at least* `x^δ`. This file proves what the sieve endgame needs of that region, and that the
shrink-translate-mollify retreat lands inside its buffered version.

## The shape of the argument

Everything about the caps goes through one lemma, `SupportParams.sum_le_B_of_subset_rough`: if the
coordinates of `I` all reach `δ` and their mass is at most `c·B_{j,#I}`, then every subset inherits
the bound at its own cardinality. Dropping a coordinate loses at least `δ` from the mass and, by
`SupportParams.B_step`, at most `δ` from the cap, so the cap degrades no faster than the mass. The
scale factor `c ≤ 1` is what lets the same lemma serve the stratum (`c = 1`, threshold read through
`SupportParams.large`) and the retreat region (`c = 1 - ε₀`, threshold read through
`SupportParams.roughIdx`).

## The two certified margins

`retreat_cap_margin` and `retreat_total_margin` are the only numerical facts the retreat needs, and
both are *equalities* at the extreme index — the constants `2163403/14062500` and `20482/78125` are
exactly the room the chosen datum leaves, not under-estimates. The total-mass one is tight outright,
which is why it needs no hypothesis on `𝖺` at all: after the substitutions the two sides are the
same affine function of `𝖺`.

## Main results

* `Gap212.SupportParams.sum_le_B_of_subset_rough`: the hereditary bound at a scale factor.
* `Gap212.GPY.retreatRegion_downward_closed`: the retreat region is downward closed.
* `Gap212.GPY.retreatRegion_subset_T`: the bottom-band retreat region sits inside the support.
* `Gap212.GPY.lt_B_one_of_mem_retreatRegion`: each coordinate is below `B_{j,1}`.
* `Gap212.GPY.retreat_cap_margin`, `Gap212.GPY.retreat_total_margin`: the two certified margins.
* `Gap212.GPY.delta_lt_of_shrink_rough`: the shrink map clears the rough threshold.
* `Gap212.GPY.mollify_shrinkTranslate_support_subset`: the retreated mollification lands in the
  buffered region.
-/

@[expose] public section

namespace Gap212

open Finset

namespace SupportParams

variable {p : SupportParams}

/-- The cap row is non-negative: at `m = 0` it vanishes and beyond that it exceeds `δ > 0`. -/
theorem B_nonneg (j : Fin p.n) (m : ℕ) : 0 ≤ p.B j m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact (p.B_zero j).ge
  · exact (p.δ_pos.trans (p.B_lt j m hm)).le

/-- A coordinate is rough exactly when it reaches `δ`. The non-strict sibling of
`Gap212.mem_large_iff`. -/
theorem mem_roughIdx_iff {k : ℕ} {t : Fin k → ℝ} {i : Fin k} :
    i ∈ p.roughIdx k t ↔ p.δ ≤ t i := by
  simp [SupportParams.roughIdx]

/-- Every large coordinate is rough: `δ < tᵢ` implies `δ ≤ tᵢ`. -/
theorem large_subset_roughIdx {k : ℕ} (t : Fin k → ℝ) : p.large k t ⊆ p.roughIdx k t :=
  fun _ hi ↦ mem_roughIdx_iff.mpr (mem_large_iff.mp hi).le

/-- **The hereditary rough-mass bound, at a scale factor.** If every coordinate of `I` reaches `δ`
and the mass of `I` is at most `c·B_{j,#I}` for some `c ∈ [0,1]`, then every subset `I' ⊆ I`
satisfies the same bound at its own cardinality.

Both the factor `c` and the non-strict threshold are used downstream. A point of the `j`-th stratum
satisfies the hypothesis at `c = 1` with `I` its set of large coordinates, where `δ < tᵢ`; a point
of the retreat region satisfies it at `c = 1 - ε₀` with `I` its set of *rough* coordinates, where
only `δ ≤ tᵢ` is available — and it has to be that set, because the moduli a support generates are
constrained at rough factors of size at least `x^δ`.

The empty subset is not excluded: there the claim is `0 ≤ c·B_{j,0}`, which is `B_zero`. It has to
be taken separately, because `B_step_iterate` is guarded at `r ≥ 1` and its `r = 0` instance is
false — it would read `B_{j,m} ≤ m·δ`, already failing at `m = 1`. -/
@[gap212 "lem_hereditary"]
theorem sum_le_B_of_subset_rough {k : ℕ} {j : Fin p.n} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {t : Fin k → ℝ} {I I' : Finset (Fin k)} (hrough : ∀ i ∈ I, p.δ ≤ t i)
    (hcap : ∑ i ∈ I, t i ≤ c * p.B j I.card) (hsub : I' ⊆ I) :
    ∑ i ∈ I', t i ≤ c * p.B j I'.card := by
  rcases Nat.eq_zero_or_pos I'.card with hr | hr
  · simp [Finset.card_eq_zero.mp hr, p.B_zero j]
  -- Each dropped coordinate carries at least `δ`, so the drop costs at least `d·δ`.
  have hdrop : ((I \ I').card : ℝ) * p.δ ≤ ∑ i ∈ I \ I', t i := by
    simpa using Finset.card_nsmul_le_sum _ _ _ fun i hi ↦ hrough i (Finset.mem_sdiff.mp hi).1
  -- The cap degrades by at most `d·δ` over the same drop.
  have hchain := B_step_iterate j hr (I \ I').card
  rw [add_comm, Finset.card_sdiff_add_card_eq_card hsub] at hchain
  linarith [Finset.sum_sdiff hsub (f := t), mul_le_mul_of_nonneg_left hchain hc0,
    mul_nonneg (sub_nonneg.2 hc1) (mul_nonneg (Nat.cast_nonneg (I \ I').card) p.δ_pos.le)]

end SupportParams

namespace GPY

open MeasureTheory

/-! ### The retreat region -/

/-- The hereditary bound at `c = 1 - ε₀`, on subsets of the rough set of a retreat-region point. -/
private theorem sum_le_of_subset_roughIdx {p : SupportParams} {k : ℕ} {j : Fin p.n} {ε₀ : ℝ}
    (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ ≤ 1) {t : Fin k → ℝ} {I : Finset (Fin k)}
    (hcap : ∑ i ∈ p.roughIdx k t, t i ≤ (1 - ε₀) * p.B j (p.roughIdx k t).card)
    (hsub : I ⊆ p.roughIdx k t) : ∑ i ∈ I, t i ≤ (1 - ε₀) * p.B j I.card :=
  SupportParams.sum_le_B_of_subset_rough (by linarith) (by linarith)
    (fun _ ↦ SupportParams.mem_roughIdx_iff.mp) hcap hsub

/-- **The retreat region is downward closed.** Lowering a coordinate cannot leave the region: the
total mass only drops, and for the cap the rough set can only shrink, so the hereditary bound at
`c = 1 - ε₀` transports the cap to the smaller rough set.

This is what allows the tensor construction's downward boxes: a product of tails is supported on a
box hanging below a point of the region, and the whole box has to lie in the region too. -/
@[gap212 "lem_retreat_downward_closed"]
theorem retreatRegion_downward_closed {p : SupportParams} {k : ℕ} {j : Fin p.n} {ε₀ : ℝ}
    (hε₀ : 0 ≤ ε₀) (hε₀' : ε₀ ≤ 1) {t s : Fin k → ℝ} (ht : t ∈ retreatRegion p k j ε₀)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ t i) : s ∈ retreatRegion p k j ε₀ := by
  obtain ⟨hcube, htot, hcap⟩ := ht
  refine ⟨fun i ↦ ⟨(hs i).1, (hs i).2.trans (hcube i).2⟩, ?_, ?_⟩
  · exact (Finset.sum_le_sum fun i _ ↦ (hs i).2).trans_lt htot
  · exact (Finset.sum_le_sum fun i _ ↦ (hs i).2).trans <| sum_le_of_subset_roughIdx hε₀ hε₀' hcap
      fun i hi ↦ SupportParams.mem_roughIdx_iff.mpr
        ((SupportParams.mem_roughIdx_iff.mp hi).trans (hs i).2)

/-- **The retreat region sits inside the support.** At the bottom band the retreat region is
contained in the first stratum, hence in `T_k(p)`.

The band matters: the lower end of the first stratum's total-mass window is `A₀ + ε = 0`, which
every point of the region clears because its coordinates are non-negative. No one-band hypothesis
on the datum is needed, since the bottom band is available at every `n ≥ 1`. -/
@[gap212 "lem_retreat_in_support"]
theorem retreatRegion_subset_T {p : SupportParams} {k : ℕ} {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀)
    (hε₀' : ε₀ ≤ 1) : retreatRegion p k ⟨0, p.n_pos⟩ ε₀ ⊆ T p k := by
  rintro t ⟨hcube, htot, hcap⟩
  have hcs : (⟨0, p.n_pos⟩ : Fin p.n).castSucc = 0 := rfl
  have hmono := p.A_mono (show (⟨0, p.n_pos⟩ : Fin p.n).castSucc < (⟨0, p.n_pos⟩ : Fin p.n).succ
    by simp [Fin.lt_def])
  rw [hcs, p.A_zero] at hmono
  refine Set.mem_iUnion.mpr ⟨⟨0, p.n_pos⟩, hcube, ⟨?_, ?_⟩, ?_⟩
  · rw [hcs, p.A_zero, neg_add_cancel]
    exact Finset.sum_nonneg fun i _ ↦ (hcube i).1
  · nlinarith
  · nlinarith [sum_le_of_subset_roughIdx hε₀ hε₀' hcap (p.large_subset_roughIdx t),
      p.B_nonneg (⟨0, p.n_pos⟩ : Fin p.n) (p.large k t).card]

/-- **A single coordinate of the retreat region is small**: every coordinate is strictly below the
first rung `B_{j,1}` of the cap row.

This is the `dₖ = d'ₖ = 1` forcing of the sieve realization: the retreated cap on a *single* rough
coordinate is already below the wall, so no sieve divisor can carry that much of the support
exponent. Below `δ` the bound is `δ < B_{j,1}`; at or above `δ` it is the hereditary bound at the
singleton, and the factor `1 - ε₀ < 1` makes it strict. -/
@[gap212 "lem_retreat_coordinate_bound"]
theorem lt_B_one_of_mem_retreatRegion {p : SupportParams} {k : ℕ} {j : Fin p.n} {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀' : ε₀ ≤ 1) {t : Fin k → ℝ} (ht : t ∈ retreatRegion p k j ε₀)
    (i : Fin k) : t i < p.B j 1 := by
  obtain ⟨-, -, hcap⟩ := ht
  have hB1 : p.δ < p.B j 1 := p.B_lt j 1 le_rfl
  by_cases hi : p.δ ≤ t i
  · have h := sum_le_of_subset_roughIdx hε₀.le hε₀' hcap
      (Finset.singleton_subset_iff.mpr (SupportParams.mem_roughIdx_iff.mpr hi))
    rw [Finset.sum_singleton, Finset.card_singleton] at h
    nlinarith [p.δ_pos]
  · linarith [not_le.mp hi]

/-! ### The two certified margins of the retreat data -/

/-- The chosen datum has one band, so any two band indices agree. -/
private theorem gap212Params_fin_eq (i j : Fin gap212Params.n) : i = j :=
  Fin.ext ((Nat.lt_one_iff.mp i.isLt).trans (Nat.lt_one_iff.mp j.isLt).symm)

/-- The retreat data of the chosen datum at `k = 45`, in numerals. -/
private theorem retreatData_gap212 (a : ℝ) : retreatData gap212Params 45 a =
    (a * (41 / 2500) / 4500, a / 100, a * (41 / 2500) / 2, a * (41 / 2500) / 45000) := by
  simp only [retreatData, Prod.mk.injEq]
  norm_num [show gap212Params.δ = 41 / 2500 from rfl]

/-- The chosen datum has one band, so its only total-mass node is `A₁ + ε = 53/200`. -/
theorem gap212Params_A_succ (j : Fin gap212Params.n) :
    gap212Params.A j.succ + gap212Params.ε = 53 / 200 := by
  have h1 : gap212Params.A j.succ = ((j.succ.val : ℝ)) * (53 / 200) - 1 / 125 := rfl
  have h2 : gap212Params.ε = (1 : ℝ) / 125 := rfl
  rw [h1, h2, Fin.val_succ, Nat.lt_one_iff.mp j.isLt]
  norm_num

/-- The rational inequality behind `retreat_cap_margin`, with the factor `𝖺` divided out: the
`m`-th translation-plus-mollification cost plus the certified margin fits under the retreated cap.

The cost per rough coordinate is `δ/(100k) + δ/(1000k) = 11δ/45000 = 451/112500000` at `k = 45`.
The inequality is an *equality* at `m = 1`, so `2163403/14062500` is exactly the smallest of the
forty-five margins. From `m = 10` on the cap row is constant while the cost grows linearly, which
is why the range has to be bounded at all; at `m = 45` the slack is still `133661/625000`. -/
theorem gap212Cap_margin {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 45) :
    (m : ℝ) * ((41 / 2500) / 4500 + (41 / 2500) / 45000) + 2163403 / 14062500
      ≤ 99 / 100 * gap212Cap m := by
  by_cases h : 10 ≤ m
  · rw [gap212Cap_of_ten_le h]
    have hm45 : (m : ℝ) ≤ 45 := by exact_mod_cast hm
    linarith
  · have h' : m < 10 := by omega
    interval_cases m <;> norm_num [gap212Cap]

/-- **The cap margin of the retreat data.** Shrinking by `1 - 𝖺`, translating by `b₀` and
mollifying at radius `ϱ` costs `m(b₀ + ϱ)` on a rough set of size `m`, and that cost plus a fixed
positive margin `𝖺·2163403/14062500` still fits under the retreated cap `(1 - ε₀)B_{1,m}`, for
every `1 ≤ m ≤ 45`.

Every term is `𝖺` times a rational depending only on `m`, so the inequality is checked once for the
chosen datum rather than at each `𝖺`. The margin is *tight*: at `m = 1` the two sides are
equal. Only `0 < 𝖺` is needed, not `𝖺 < 1/2`. -/
@[gap212 "lem_retreat_cap_margin"]
theorem retreat_cap_margin {a b₀ ε₀ ζ ϱ : ℝ} (ha : 0 < a)
    (hdata : retreatData gap212Params 45 a = (b₀, ε₀, ζ, ϱ)) (j : Fin gap212Params.n)
    {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 45) :
    (1 - a) * gap212Params.B j m + m * (b₀ + ϱ)
      ≤ (1 - ε₀) * gap212Params.B j m - a * (2163403 / 14062500) := by
  simp only [retreatData_gap212, Prod.mk.injEq] at hdata
  obtain ⟨rfl, rfl, -, rfl⟩ := hdata
  rw [show gap212Params.B j m = gap212Cap m from rfl]
  linarith [mul_le_mul_of_nonneg_left (gap212Cap_margin hm1 hm) ha.le]

/-- **The total-mass margin of the retreat data.** The same computation for the total mass: the
shrunk node `(1 - 𝖺)(A₁ + ε)` plus the full translation-and-mollification cost `k(b₀ + ϱ)` stays
below the retreated node by at least `𝖺·20482/78125`.

Tight outright — over the denominator `2500000` the two sides are equal — so `20482/78125` is
exactly the available room, not an under-estimate. Tightness is also why no hypothesis on `𝖺`
appears: the two sides are the same affine function of `𝖺` once the retreat data is substituted. -/
@[gap212 "lem_retreat_total_margin"]
theorem retreat_total_margin {a b₀ ε₀ ζ ϱ : ℝ}
    (hdata : retreatData gap212Params 45 a = (b₀, ε₀, ζ, ϱ)) (j : Fin gap212Params.n) :
    (1 - a) * (gap212Params.A j.succ + gap212Params.ε) + 45 * (b₀ + ϱ)
      ≤ (1 - ε₀) * (gap212Params.A j.succ + gap212Params.ε) - a * (20482 / 78125) := by
  simp only [retreatData_gap212, Prod.mk.injEq] at hdata
  obtain ⟨rfl, rfl, -, rfl⟩ := hdata
  rw [gap212Params_A_succ j]
  linarith

/-! ### The shrink map at the rough threshold -/

/-- **The shrink map clears the rough threshold.** If the shrunk-and-translated coordinate
`tᵢ = (1 - 𝖺)sᵢ + b₀` reaches `δ - ζ`, then the original coordinate `sᵢ` was *strictly* above `δ`.

This is what covers the equality case of the non-strict rough threshold, and a whole neighbourhood
of it: the buffer `ζ = 𝖺δ/2` together with the translation `b₀ = 𝖺δ/(100k)` satisfies
`ζ + b₀ < 𝖺δ`, which is `1/2 + 1/(100k) < 1` — true for every `k ≥ 1`. So a coordinate of `t` that
is merely close to `δ` from below still comes from a large coordinate of `s`. -/
@[gap212 "lem_shrink_threshold"]
theorem delta_lt_of_shrink_rough {p : SupportParams} {k : ℕ} (hk : 1 ≤ k) {a b₀ ε₀ ζ ϱ : ℝ}
    (ha : 0 < a) (ha' : a < 1 / 2) (hdata : retreatData p k a = (b₀, ε₀, ζ, ϱ))
    {s : Fin k → ℝ} {i : Fin k} (hi : p.δ - ζ ≤ (1 - a) * s i + b₀) : p.δ < s i := by
  simp only [retreatData, Prod.mk.injEq] at hdata
  obtain ⟨rfl, -, rfl, -⟩ := hdata
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have haδ : 0 < a * p.δ := mul_pos ha p.δ_pos
  -- `b₀ ≤ 𝖺δ/100`, because `100 ≤ 100k`; hence `ζ + b₀ < 𝖺δ`, which makes the shrink strict.
  have hbk : a * p.δ / (100 * (k : ℝ)) ≤ a * p.δ / 100 :=
    div_le_div_of_nonneg_left haδ.le (by norm_num) (by linarith)
  exact lt_of_mul_lt_mul_left (by linarith) (by linarith : (0 : ℝ) ≤ 1 - a)

/-! ### The retreated mollification -/

/-- The support of a rescaled mollifier kernel: if `φ` vanishes off the unit ball then
`y ↦ c·φ(ϱ⁻¹ • y)` vanishes off the ball of radius `ϱ`. -/
theorem support_scaled_kernel_subset {k : ℕ} {φ : (Fin k → ℝ) → ℝ} {ϱ c : ℝ} (hϱ : 0 < ϱ)
    (hφ : Function.support φ ⊆ Metric.closedBall 0 1) :
    Function.support (fun y : Fin k → ℝ ↦ c * φ (ϱ⁻¹ • y)) ⊆ Metric.closedBall 0 ϱ := by
  intro y hy
  have hmem := @hφ (ϱ⁻¹ • y) fun h ↦ hy (by simp [h])
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hϱ,
    inv_mul_le_iff₀ hϱ, mul_one] at hmem
  rwa [mem_closedBall_zero_iff]

/-- **The retreated mollification lands in the buffered retreat region.** For the chosen datum at
`k = 45`, if `G` vanishes off `T₄₅(p⋆)` then mollifying its shrink-translate at radius `ϱ`
produces a function supported inside `R⁺⁺₄₅(1, ε₀, ζ₁, κ)`.

The three clauses of the buffered region come from three different places. The coordinate window
`[ζ₁, 1 - κ]` is the translation `b₀` pushing the support off the boundary of the orthant, with
`ϱ ≤ b₀/2 = κ` leaving room at the bottom. The total mass is `retreat_total_margin`, the certified
margin `𝖺·20482/78125` absorbing `κ`. The cap is `delta_lt_of_shrink_rough` — which turns a
coordinate of `v` reaching `δ - ζ₁` into a *large* coordinate of `s` — followed by the hereditary
bound at `c = 1` on the stratum and then `retreat_cap_margin`.

Only the support hypothesis on the mollifier `φ` is used; non-negativity, smoothness and unit total
mass are what the *other* clauses of the retreat need, not this one. The ambient norm on `ℝ⁴⁵` is
the supremum norm, so `Metric.closedBall 0 1` is the unit cube and the coordinatewise bound
`|yᵢ| ≤ ϱ` — all this proof uses of the kernel's support — is immediate. -/
@[gap212 "lem_retreat_mollify_support"]
theorem mollify_shrinkTranslate_support_subset {a b₀ ε₀ ζ ϱ κ ζ₁ : ℝ} (ha : 0 < a)
    (ha' : a < 1 / 2) (hdata : retreatData gap212Params 45 a = (b₀, ε₀, ζ, ϱ))
    (hκ : κ = a * gap212Params.δ / (200 * 45)) (hζ₁ : ζ₁ = κ / (2 * 45))
    {φ : (Fin 45 → ℝ) → ℝ} (hφ : Function.support φ ⊆ Metric.closedBall 0 1)
    {G : (Fin 45 → ℝ) → ℝ} (hG : ∀ t, t ∉ T gap212Params 45 → G t = 0)
    (j : Fin gap212Params.n) :
    Function.support (mollify φ ϱ (shrinkTranslate a b₀ G))
      ⊆ bufferedRegion gap212Params 45 j ε₀ ζ₁ κ := by
  -- The numerals of the retreat data at the chosen datum.
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  have h := hdata
  simp only [retreatData_gap212, Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl, rfl⟩ := h
  rw [hδ] at hκ
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hA := gap212Params_A_succ j
  -- Split a point of the support as kernel point plus shrink-translate point.
  intro v hv
  obtain ⟨y, hy, t, htsupp, hvt⟩ := Set.mem_add.mp (MeasureTheory.support_convolution_subset
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure (Fin 45 → ℝ))) hv)
  have hyball := support_scaled_kernel_subset (by positivity) hφ hy
  rw [mem_closedBall_zero_iff] at hyball
  have hy : ∀ i, -(a * (41 / 2500) / 45000) ≤ y i ∧ y i ≤ a * (41 / 2500) / 45000 :=
    fun i ↦ abs_le.mp ((norm_le_pi_norm y i).trans hyball)
  have hvi : ∀ i, v i = y i + t i := fun i ↦ by rw [← hvt]; rfl
  -- The preimage point `s` lies in the support, hence in the single stratum.
  set s : Fin 45 → ℝ := fun i ↦ (t i - a * (41 / 2500) / 4500) / (1 - a) with hsdef
  have hts : ∀ i, t i = (1 - a) * s i + a * (41 / 2500) / 4500 := fun i ↦ by
    simp only [hsdef, mul_div_cancel₀ _ h1a.ne']
    ring
  obtain ⟨j', hj'⟩ := Set.mem_iUnion.mp (of_not_not fun h ↦ htsupp (hG s h))
  obtain ⟨hcube, hwin, hcap⟩ := gap212Params_fin_eq j' j ▸ hj'
  have hsum : ∑ i, s i ≤ 53 / 200 := by linarith [hwin.2]
  -- Two transport identities, used at `Finset.univ` for the mass and at the rough set for the cap.
  have hsumv : ∀ I : Finset (Fin 45),
      ∑ i ∈ I, v i ≤ ∑ i ∈ I, t i + I.card * (a * (41 / 2500) / 45000) := fun I ↦ by
    rw [Finset.sum_congr rfl fun i _ ↦ hvi i, Finset.sum_add_distrib, add_comm]
    gcongr
    simpa using Finset.sum_le_card_nsmul I y _ fun i _ ↦ (hy i).2
  have hsumt : ∀ I : Finset (Fin 45),
      ∑ i ∈ I, t i = (1 - a) * ∑ i ∈ I, s i + I.card * (a * (41 / 2500) / 4500) := fun I ↦ by
    rw [Finset.sum_congr rfl fun i _ ↦ hts i, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
  -- The three clauses of the buffered region.
  refine ⟨fun i ↦ ⟨?_, ?_⟩, ?_, ?_⟩
  · linarith [mul_nonneg h1a.le (hcube i).1, (hy i).1, hvi i, hts i]
  · have hsi : s i ≤ 53 / 200 :=
      (Finset.single_le_sum (fun i' _ ↦ (hcube i').1) (Finset.mem_univ i)).trans hsum
    linarith [mul_le_mul_of_nonneg_left hsi h1a.le, (hy i).2, hvi i, hts i]
  · -- Total mass, through `retreat_total_margin`.
    have h1 := hsumv Finset.univ
    have h2 := hsumt Finset.univ
    have hmargin := retreat_total_margin hdata j
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at h1 h2
    rw [hA] at hmargin ⊢
    linarith [mul_le_mul_of_nonneg_left hsum h1a.le]
  · -- The cap, through `delta_lt_of_shrink_rough`, the hereditary bound and `retreat_cap_margin`.
    intro hne
    set I := roughAt (gap212Params.δ - ζ₁) v with hIdef
    have hIlarge : I ⊆ gap212Params.large 45 s := fun i hi ↦ by
      have hvi' : gap212Params.δ - ζ₁ ≤ v i := by simpa [hIdef, roughAt] using hi
      refine mem_large_iff.mpr (delta_lt_of_shrink_rough (by norm_num) ha ha' hdata ?_)
      linarith [(hy i).2, hvi i, hts i]
    have hscap : ∑ i ∈ I, s i ≤ gap212Params.B j I.card := by
      simpa using SupportParams.sum_le_B_of_subset_rough (c := 1) zero_le_one le_rfl
        (fun i hi ↦ (mem_large_iff.mp hi).le) (by rwa [one_mul]) hIlarge
    linarith [hsumv I, hsumt I, mul_le_mul_of_nonneg_left hscap h1a.le,
      retreat_cap_margin ha hdata j (Finset.card_pos.mpr hne)
        ((Finset.card_le_univ I).trans_eq (Fintype.card_fin 45))]

end GPY

end Gap212
