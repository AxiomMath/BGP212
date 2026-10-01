/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public meta import Gap212.Attr

/-!
# The tensor mesh: approximating a smooth bump by a non-negative tensor sum

A smooth, non-negative `G : ℝ^k → ℝ` compactly supported in
the open orthant `(0,∞)^k` is approximated uniformly, to any accuracy `ε₃`, by a finite sum
`∑_{l ≤ L} c_l ∏_{i ≤ k} g_{l,i}` in which

* every coefficient `c_l` is non-negative,
* every factor `g_{l,i}` is non-negative and smooth,
* every factor is supported in an interval `[α_{l,i}, β_{l,i}] ⊆ (0,∞)` of length at most `ε₃`,
* every box `∏_i [α_{l,i}, β_{l,i}]` meets `supp G` and lies in its `ε₃`-neighbourhood.

## The construction

The natural ingredient is a smooth `χ ≥ 0` supported in `(-1,1)` with `∑_{m ∈ ℤ} χ(τ - m) = 1`.
Mathlib has no such periodic partition of unity: its
`SmoothPartitionOfUnity` is indexed by an abstract cover of a manifold and carries no translation
structure, and `ContDiffBump` gives a single bump with no summation identity. So `χ` is built here,
and the construction is chosen to make the partition identity a *telescoping sum* rather than a
locally finite one:

`Gap212.Sieve.meshBump τ = σ(τ + 1) - σ(τ)`, with `σ = Real.smoothTransition`.

Because `σ` is monotone, smooth, `0` on `(-∞,0]` and `1` on `[1,∞)`, this `χ` is non-negative,
smooth, and vanishes off `(-1,1)`; and
`∑_{m < n} χ(τ - m) = σ(τ + 1) - σ(τ - n + 1)` by telescoping, which is `1` as soon as
`0 ≤ τ ≤ n - 1`. That is all the partition-of-unity content the proof uses, and it needs no
infinite sum: the grid is truncated to `{0, …, n-1}^k` with `n` large enough to cover `supp G`, and
the truncated sum is still identically `1` there while staying in `[0,1]` everywhere.

The multi-indices are then thinned to those `m` with `G(hm) ≠ 0` — which is what puts every
retained box inside the orthant and inside the `ε₃`-neighbourhood of `supp G` — and discarding the
rest changes nothing, the discarded coefficients being `0`.

## Main definitions

* `Gap212.Sieve.meshBump`: the elementary bump `σ(τ+1) - σ(τ)`.
* `Gap212.Sieve.meshFactor`: its rescaling `τ ↦ meshBump (τ/w - m)`, supported in
  `[mw - w, mw + w]`.
* `Gap212.Sieve.meshPartialSum`: the truncated partition sum `∑_{m < n} meshFactor w m`.
* `Gap212.Sieve.meshPoint`: the grid point `w·m` of a multi-index.

## Main results

* `Gap212.Sieve.sum_meshBump_range`: the telescoping partition identity.
* `Gap212.Sieve.meshPartialSum_eq_one`: the truncated sum is `1` on the covered range.
* `Gap212.Sieve.exists_tensor_partition_approx`: a smooth non-negative `G` compactly supported in
  the open orthant is uniformly `ε₃`-approximated by non-negative combinations of tensor products
  of smooth bumps on short intervals.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset

/-! ## The elementary bump -/

/-- **The mesh bump** `χ(τ) = σ(τ + 1) - σ(τ)`, with `σ = Real.smoothTransition`.

Non-negative because `σ` is monotone, smooth because `σ` is, and vanishing off `(-1,1)` because `σ`
is `0` on `(-∞,0]` and `1` on `[1,∞)`. Its translates telescope: see `sum_meshBump_range`. -/
noncomputable def meshBump (τ : ℝ) : ℝ :=
  Real.smoothTransition (τ + 1) - Real.smoothTransition τ

/-- The mesh bump is non-negative. -/
lemma meshBump_nonneg (τ : ℝ) : 0 ≤ meshBump τ :=
  sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))

/-- The mesh bump is smooth. -/
lemma contDiff_meshBump : ContDiff ℝ (⊤ : ℕ∞) meshBump :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

/-- The mesh bump vanishes on `(-∞, -1]`. -/
lemma meshBump_of_le_neg_one {τ : ℝ} (h : τ ≤ -1) : meshBump τ = 0 := by
  rw [meshBump, Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

/-- The mesh bump vanishes on `[1, ∞)`. -/
lemma meshBump_of_one_le {τ : ℝ} (h : 1 ≤ τ) : meshBump τ = 0 := by
  rw [meshBump, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le h, sub_self]

/-- If `meshBump τ ≠ 0` then `|τ| < 1`. -/
lemma abs_lt_one_of_meshBump_ne_zero {τ : ℝ} (h : meshBump τ ≠ 0) : |τ| < 1 :=
  abs_lt.2 ⟨lt_of_not_ge fun hc ↦ h (meshBump_of_le_neg_one hc),
    lt_of_not_ge fun hc ↦ h (meshBump_of_one_le hc)⟩

/-- **The partition identity**, as a telescoping sum: `∑_{m < n} χ(τ - m) = σ(τ+1) - σ(τ-n+1)`.

This is the finite substitute for `∑_{m ∈ ℤ} χ(τ - m) = 1`; the right-hand side is
`1` precisely when `0 ≤ τ ≤ n - 1`, and lies in `[0,1]` always. -/
lemma sum_meshBump_range (n : ℕ) (τ : ℝ) :
    ∑ m ∈ range n, meshBump (τ - m) =
      Real.smoothTransition (τ + 1) - Real.smoothTransition (τ - n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, meshBump,
      show τ - ((n + 1 : ℕ) : ℝ) + 1 = τ - n by push_cast; ring]
    ring

/-! ## The rescaled bumps and their truncated partition sum -/

/-- **The mesh factor** of width `w` at index `m`: the bump `χ` rescaled to sit on the interval
`[mw - w, mw + w]`, of length `2w`. -/
noncomputable def meshFactor (w : ℝ) (m : ℕ) (τ : ℝ) : ℝ := meshBump (τ / w - m)

/-- The mesh factor is non-negative. -/
lemma meshFactor_nonneg (w : ℝ) (m : ℕ) (τ : ℝ) : 0 ≤ meshFactor w m τ := meshBump_nonneg _

/-- The mesh factor is smooth. -/
lemma contDiff_meshFactor (w : ℝ) (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (meshFactor w m) :=
  contDiff_meshBump.comp ((contDiff_id.div_const w).sub contDiff_const)

/-- For `0 < w`, the mesh factor `meshFactor w m` is supported in `[mw - w, mw + w]`. -/
lemma meshFactor_support {w : ℝ} (hw : 0 < w) (m : ℕ) :
    Function.support (meshFactor w m) ⊆ Set.Icc ((m : ℝ) * w - w) ((m : ℝ) * w + w) := by
  intro τ hτ
  obtain ⟨h1, h2⟩ := abs_lt.1 (abs_lt_one_of_meshBump_ne_zero (Function.mem_support.1 hτ))
  rw [neg_lt_sub_iff_lt_add, ← sub_lt_iff_lt_add', lt_div_iff₀ hw] at h1
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hw] at h2
  exact ⟨by linarith, by linarith⟩

/-- **The truncated partition sum** `∑_{m < n} meshFactor w m`. -/
noncomputable def meshPartialSum (w : ℝ) (n : ℕ) (τ : ℝ) : ℝ :=
  ∑ m ∈ range n, meshFactor w m τ

/-- The truncated partition sum equals `σ(τ/w + 1) - σ(τ/w - n + 1)`, with
`σ = Real.smoothTransition`. -/
lemma meshPartialSum_eq (w : ℝ) (n : ℕ) (τ : ℝ) :
    meshPartialSum w n τ =
      Real.smoothTransition (τ / w + 1) - Real.smoothTransition (τ / w - n + 1) :=
  sum_meshBump_range n (τ / w)

/-- The truncated partition sum is non-negative. -/
lemma meshPartialSum_nonneg (w : ℝ) (n : ℕ) (τ : ℝ) : 0 ≤ meshPartialSum w n τ :=
  Finset.sum_nonneg fun _ _ => meshFactor_nonneg _ _ _

/-- The truncated partition sum is at most `1`. -/
lemma meshPartialSum_le_one (w : ℝ) (n : ℕ) (τ : ℝ) : meshPartialSum w n τ ≤ 1 := by
  rw [meshPartialSum_eq]
  linarith [Real.smoothTransition.le_one (τ / w + 1), Real.smoothTransition.nonneg (τ / w - n + 1)]

/-- The truncated partition sum `meshPartialSum w n τ` equals `1` when `0 ≤ τ / w ≤ n - 1`. -/
lemma meshPartialSum_eq_one {w : ℝ} {n : ℕ} {τ : ℝ} (h0 : 0 ≤ τ / w)
    (h1 : τ / w ≤ (n : ℝ) - 1) : meshPartialSum w n τ = 1 := by
  rw [meshPartialSum_eq, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

/-- **The grid point** `w·m` attached to a multi-index `m`. -/
noncomputable def meshPoint {k n : ℕ} (w : ℝ) (m : Fin k → Fin n) : Fin k → ℝ :=
  fun i => ((m i : ℕ) : ℝ) * w

/-- The `i`-th coordinate of `meshPoint w m` is `(m i : ℝ) * w`. -/
@[simp] lemma meshPoint_apply {k n : ℕ} (w : ℝ) (m : Fin k → Fin n) (i : Fin k) :
    meshPoint w m i = ((m i : ℕ) : ℝ) * w := rfl

/-! ## The approximation theorem -/

/-- **Tensor approximation by a non-negative partition of unity.**

Let `G : ℝ^k → ℝ` be smooth, non-negative and compactly supported in `(0,∞)^k` — the last read as
`tsupport G` being compact and contained in the open orthant — and let
`ε₃ > 0`. Then there are `L`, coefficients `c_l ≥ 0`, non-negative smooth factors `g_{l,i}` and
intervals `[α_{l,i}, β_{l,i}]` such that

* `Function.support (g l i) ⊆ [α l i, β l i]` and `β l i - α l i ≤ ε₃` (each factor sits on an
  interval of length at most `ε₃`);
* `0 < α l i`, so that interval is contained in `(0,∞)`;
* the box `∏_i [α l i, β l i]` contains a point of `supp G` — hence meets the `ε₃`-neighbourhood —
  and every one of its points is within `ε₃` of `supp G` in every coordinate, so the box is
  contained in that neighbourhood;
* `|G t - ∑_l c_l ∏_i g_{l,i}(t_i)| ≤ ε₃` for every `t`, i.e. the sup-norm bound.

The two support clauses use `Function.support G`, not `tsupport G`, as in
`Gap212.Sieve.TensorDensity`. -/
@[gap212 "lem_tensor_density"]
theorem exists_tensor_partition_approx {k : ℕ} (hk : 1 ≤ k) {G : (Fin k → ℝ) → ℝ}
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) G) (hnonneg : ∀ t, 0 ≤ G t) (hcs : HasCompactSupport G)
    (horth : tsupport G ⊆ {t : Fin k → ℝ | ∀ i, 0 < t i}) {ε₃ : ℝ} (hε₃ : 0 < ε₃) :
    ∃ (L : ℕ) (c : Fin L → ℝ) (g : Fin L → Fin k → ℝ → ℝ) (α β : Fin L → Fin k → ℝ),
      (∀ l, 0 ≤ c l) ∧
      (∀ l i t, 0 ≤ g l i t) ∧
      (∀ l i, ContDiff ℝ (⊤ : ℕ∞) (g l i)) ∧
      (∀ l i, Function.support (g l i) ⊆ Set.Icc (α l i) (β l i)) ∧
      (∀ l i, β l i - α l i ≤ ε₃) ∧
      (∀ l i, 0 < α l i) ∧
      (∀ l, ∃ s ∈ Function.support G, ∀ i, s i ∈ Set.Icc (α l i) (β l i)) ∧
      (∀ l, ∀ t : Fin k → ℝ, (∀ i, t i ∈ Set.Icc (α l i) (β l i)) →
        ∃ s ∈ Function.support G, ∀ i, |t i - s i| ≤ ε₃) ∧
      (∀ t : Fin k → ℝ, |G t - ∑ l, c l * ∏ i, g l i (t i)| ≤ ε₃) := by
  classical
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  -- The degenerate case `G ≡ 0`: no terms at all.
  by_cases hG0 : ∀ t, G t = 0
  · exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, by simp [hG0, hε₃.le]⟩
  obtain ⟨t₀, ht₀⟩ := not_forall.1 hG0
  have hK : IsCompact (tsupport G) := hcs
  have hKne : (tsupport G).Nonempty := ⟨t₀, subset_tsupport G ht₀⟩
  -- A box `[a₀, R]^k` around the support, with `a₀ > 0`.
  have key : ∀ i : Fin k, ∃ a b : ℝ, 0 < a ∧ ∀ t ∈ tsupport G, a ≤ t i ∧ t i ≤ b := by
    intro i
    obtain ⟨x, hx, hxm⟩ := hK.exists_isMinOn hKne (continuous_apply i).continuousOn
    obtain ⟨y, hy, hym⟩ := hK.exists_isMaxOn hKne (continuous_apply i).continuousOn
    exact ⟨x i, y i, horth hx i,
      fun t ht => ⟨isMinOn_iff.1 hxm t ht, isMaxOn_iff.1 hym t ht⟩⟩
  choose A B hA0 hAB using key
  obtain ⟨a₀, ha₀pos, ha₀le⟩ : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ i, a₀ ≤ A i :=
    ⟨univ.inf' univ_nonempty A, (Finset.lt_inf'_iff _).2 fun i _ => hA0 i,
      fun i => Finset.inf'_le _ (mem_univ i)⟩
  obtain ⟨R, hRpos, hBle⟩ : ∃ R : ℝ, 0 < R ∧ ∀ i, B i ≤ R :=
    ⟨max 1 (univ.sup' univ_nonempty B), lt_of_lt_of_le one_pos (le_max_left _ _),
      fun i => le_trans (Finset.le_sup' B (mem_univ i)) (le_max_right _ _)⟩
  -- Uniform continuity supplies the modulus the oscillation bound is read off.
  have huc : UniformContinuous G := hcs.uniformContinuous_of_continuous hsmooth.continuous
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.1 huc ε₃ hε₃
  -- The mesh width.
  obtain ⟨w, hw0, hwa, hwδ, hwε⟩ : ∃ w : ℝ, 0 < w ∧ w < a₀ ∧ w < δ ∧ w ≤ ε₃ / 2 :=
    ⟨min (a₀ / 2) (min (δ / 2) (ε₃ / 2)),
      lt_min (by linarith) (lt_min (by linarith) (by linarith)),
      lt_of_le_of_lt (min_le_left _ _) (by linarith),
      lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith),
      le_trans (min_le_right _ _) (min_le_right _ _)⟩
  -- The number of grid steps needed to cover `[0, R]`.
  obtain ⟨n, hnR⟩ : ∃ n : ℕ, R < ((n : ℝ) - 1) * w := by
    refine ⟨⌈R / w⌉₊ + 2, ?_⟩
    have := (div_le_iff₀ hw0).1 (Nat.le_ceil (R / w))
    push_cast
    linarith
  -- Dividing by `w` sends `[0, R]` into `[0, n - 1]`.
  have hdivle : ∀ x : ℝ, x ≤ R → x / w ≤ (n : ℝ) - 1 := fun x hx ↦ by
    rw [div_le_iff₀ hw0]
    linarith
  -- The retained multi-indices, enumerated by a `Fin`.
  set S : Finset (Fin k → Fin n) := univ.filter (fun m => G (meshPoint w m) ≠ 0) with hS
  obtain ⟨L, idx, hidxS, hsumidx⟩ : ∃ (L : ℕ) (idx : Fin L → (Fin k → Fin n)),
      (∀ l, idx l ∈ S) ∧ ∀ F : (Fin k → Fin n) → ℝ, ∑ l, F (idx l) = ∑ m ∈ S, F m :=
    ⟨#S, fun l => ((S.equivFin.symm l : S) : Fin k → Fin n), fun l => (S.equivFin.symm l).2,
      fun F => (Equiv.sum_comp S.equivFin.symm (fun x : S => F ↑x)).trans (sum_coe_sort S F)⟩
  have hidxsupp : ∀ l, meshPoint w (idx l) ∈ Function.support G := fun l =>
    (mem_filter.1 (hidxS l)).2
  have hidxbox : ∀ l i, a₀ ≤ ((idx l i : ℕ) : ℝ) * w := fun l i =>
    (ha₀le i).trans (by simpa using (hAB i _ (subset_tsupport G (hidxsupp l))).1)
  refine ⟨L, fun l => G (meshPoint w (idx l)), fun l i => meshFactor w (idx l i),
    fun l i => ((idx l i : ℕ) : ℝ) * w - w, fun l i => ((idx l i : ℕ) : ℝ) * w + w,
    fun l => hnonneg _, fun l i t => meshFactor_nonneg _ _ _,
    fun l i => contDiff_meshFactor _ _, fun l i => meshFactor_support hw0 _,
    fun l i => by linarith, fun l i => by linarith [hidxbox l i],
    -- The box contains the grid point, which lies in `supp G`.
    fun l => ⟨meshPoint w (idx l), hidxsupp l, fun i => ⟨by simp; linarith, by simp; linarith⟩⟩,
    -- Every point of the box is within `ε₃` of that grid point, hence of `supp G`.
    fun l t ht => ⟨meshPoint w (idx l), hidxsupp l, fun i => ?_⟩, fun t => ?_⟩
  · rw [meshPoint_apply, abs_le]
    constructor <;> linarith [(ht i).1, (ht i).2]
  -- The sup-norm estimate.
  set P : (Fin k → Fin n) → ℝ := fun m => ∏ i, meshFactor w (m i) (t i) with hP
  have hPnonneg : ∀ m, 0 ≤ P m := fun m => Finset.prod_nonneg fun _ _ => meshFactor_nonneg _ _ _
  set Tot : ℝ := ∏ i, meshPartialSum w n (t i) with hTotDef
  have hTot1 : Tot ≤ 1 :=
    Finset.prod_le_one (fun _ _ => meshPartialSum_nonneg _ _ _)
      (fun _ _ => meshPartialSum_le_one _ _ _)
  -- The full grid sum of the products is the product of the truncated partition sums.
  have hsumP : ∑ m : (Fin k → Fin n), P m = Tot := by
    simp only [hP, hTotDef, meshPartialSum, ← Fin.sum_univ_eq_sum_range, Fintype.prod_sum]
  -- Only grid points within `w` of `t` contribute, and there `G` varies by at most `ε₃`.
  have hclose : ∀ m : (Fin k → Fin n), P m ≠ 0 → |G t - G (meshPoint w m)| ≤ ε₃ := by
    intro m hm
    refine (hδ (lt_of_le_of_lt ((dist_pi_le_iff hw0.le).2 fun i => ?_) hwδ)).le
    have h := Set.mem_Icc.1 (meshFactor_support hw0 (m i)
      (Function.mem_support.2 fun h => hm (Finset.prod_eq_zero (mem_univ i) h)))
    rw [Real.dist_eq, meshPoint_apply, abs_le]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  -- Where `G` does not vanish, the truncated partition sum is exactly `1`.
  have hone : G t ≠ 0 → Tot = 1 := fun h0 => Finset.prod_eq_one fun i _ => by
    have hts : t ∈ tsupport G := subset_tsupport G h0
    exact meshPartialSum_eq_one (div_nonneg (by linarith [(hAB i t hts).1, ha₀le i]) hw0.le)
      (hdivle _ (by linarith [(hAB i t hts).2, hBle i]))
  -- The two sums agree: the discarded coefficients are zero.
  have hreindex :
      ∑ l, G (meshPoint w (idx l)) * P (idx l)
        = ∑ m : (Fin k → Fin n), G (meshPoint w m) * P m := by
    rw [hsumidx (fun m => G (meshPoint w m) * P m)]
    exact Finset.sum_subset (Finset.subset_univ S) fun m _ hm => by simp_all
  -- The decomposition and the bound.
  have hdecomp : G t - ∑ l, G (meshPoint w (idx l)) * P (idx l)
      = G t * (1 - Tot) + ∑ m : (Fin k → Fin n), (G t - G (meshPoint w m)) * P m := by
    rw [hreindex]
    simp only [sub_mul, sum_sub_distrib, ← mul_sum, hsumP]
    ring
  have hb1 : |∑ m : (Fin k → Fin n), (G t - G (meshPoint w m)) * P m| ≤ ε₃ * Tot := by
    rw [← hsumP, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => ?_)
    rcases eq_or_ne (P m) 0 with h | h
    · simp [h]
    · rw [abs_mul, abs_of_nonneg (hPnonneg m)]
      exact mul_le_mul_of_nonneg_right (hclose m h) (hPnonneg m)
  have hzero : G t * (1 - Tot) = 0 := by
    rcases eq_or_ne (G t) 0 with h0 | h0 <;> simp [h0, hone]
  rw [hdecomp, hzero, zero_add]
  exact hb1.trans (mul_le_of_le_one_right hε₃.le hTot1)

end Gap212.Sieve
