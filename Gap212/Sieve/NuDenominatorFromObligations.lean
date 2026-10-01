/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.NuDenominatorBridge
public import Gap212.Sieve.SelbergAssembly
public import Gap212.Sieve.SmoothMoebiusInner

/-!
# The denominator asymptotic, from the Selberg progression sum

`Gap212.Sieve.selberg_progression_sum` evaluates the inner sum of a *pair* of profile families. The
denominator quantity `∑ν` is a *square* of a combination of `L` families, so it expands into `L²`
such pair sums (`Gap212.Sieve.sum_nu_dyadic_eq_sum_pairs`), and the main terms assemble into
`Gap212.Defs.formI c (gramInner F)` (`Gap212.Sieve.formI_gramInner_eq`). This file combines the
pair asymptotics by an `ε`-budget split over the `L²` pairs, taking `η` at
`ε/(1 + ∑|c_l c_{l'}|)` in each and the largest of the finitely many thresholds
(`Gap212.Sieve.nuDenominator_of_pairSums`).

## The hypotheses

`Gap212.Sieve.selberg_progression_sum` assumes `Gap212.Sieve.LcmGramSumLimitOfSupport` and
`Gap212.Sieve.SelbergSievingError`. The second is proved at every `m` by
`Gap212.Sieve.selbergSievingError`, so `Gap212.Sieve.nuDenominator_of_lcmGramSumLimitOfSupport`
derives `Gap212.Sieve.NuDenominator (m+1)` from `Gap212.Sieve.LcmGramSumLimitOfSupport` alone; that
in turn follows from `Gap212.Sieve.polymath41Recip` by
`Gap212.Sieve.lcmGramSumLimitOfSupport_iff_polymath41Recip`.

`Gap212.Sieve.LcmGramSumLimitOfSupport` assumes that each profile vanishes from `β` on; without
this clause the Gram limit is false (`Gap212.Sieve.not_lcmGramSumLimit`), since it would quantify
the profiles and the truncation `B ≥ x^β` independently while the Gram sum reads the profiles only
on `[0, log_x B]`. At a tensor datum the clause holds at `β = 1` by
`Gap212.Sieve.forall_eq_zero_of_one_le_or_null`, unless some factor vanishes identically on
`[0,∞)`, in which case its term vanishes on both sides (`Gap212.Sieve.prod_lambdaF_eq_zero_of_null`,
`Gap212.Sieve.prod_gramInner_eq_zero_of_null`).

The regularity hypotheses of `Gap212.Sieve.NuDenominator` are needed: the unrestricted form
`Gap212.Sieve.NuDenominatorUnrestricted`, which quantifies over profiles with no regularity, is
refuted by `Gap212.Sieve.not_nuDenominatorUnrestricted` at the indicator of `{0}`.

## The compact-support crossing

`Gap212.GPY.TensorDatum` does **not** give `HasCompactSupport (f l i)` — its
`compactSupport` field is one-sided, `∃ B, ∀ l i t, B < t → f l i t = 0`, because the factors are
tails `𝒯g` and a tail with compact support on `ℝ` is identically zero. The Selberg progression sum
wants compact support on `ℝ`. `Gap212.Sieve.exists_truncation` crosses this: multiplying by a bump
that is `1` on a neighbourhood of
`[0, B]` changes nothing on `[0,∞)`, and `λ_F` samples `F` only at the nonnegative points
`log_x d` while `gramInner` sees it only on `(0,∞)` (`Gap212.Sieve.lambdaF_congr_nonneg`,
`Gap212.Sieve.gramInner_congr_nonneg`).

## Main results

* `Gap212.Sieve.nuDenominator_of_pairSums`: the denominator asymptotic from the pair asymptotics.
* `Gap212.Sieve.forall_eq_zero_of_one_le_or_null`: the support clause of
  `Gap212.Sieve.LcmGramSumLimitOfSupport` holds at a retreated family.
* `Gap212.Sieve.nuDenominator_of_obligations`, `Gap212.Sieve.nuDenominator_of_tensorDatum`,
  `Gap212.Sieve.nuDenominator_of_gramObligations`: the denominator asymptotic from
  `LcmGramSumLimitOfSupport` and `SelbergSievingError`, through
  `Gap212.Sieve.selberg_progression_sum`.
* `Gap212.Sieve.nuDenominator_of_lcmGramSumLimitOfSupport`: the denominator asymptotic from
  `LcmGramSumLimitOfSupport` alone.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset Filter Gap212.Defs Gap212.GPY MeasureTheory

/-! ## Agreement on the nonnegative axis is all the two sides see -/

private theorem logx_nonneg_of_mem_divisors {x : ℝ} (hx : 1 < x) {d n : ℕ} (hd : d ∈ n.divisors) :
    (0 : ℝ) ≤ Gap212.Notation.logx x d :=
  div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr (Nat.pos_of_mem_divisors hd)))
    (Real.log_nonneg hx.le)

/-- **`λ_F` samples `F` only at nonnegative points.** The arguments are `log_x d` for `d ∣ n`, so
`d ≥ 1` and `x > 1` put every one of them in `[0,∞)`: two profiles agreeing there have the same
divisor weight. -/
theorem lambdaF_congr_nonneg {F G : ℝ → ℝ} {x : ℝ} (hx : 1 < x)
    (hFG : ∀ t : ℝ, 0 ≤ t → F t = G t) (n : ℕ) : lambdaF F x n = lambdaF G x n := by
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [hFG _ (logx_nonneg_of_mem_divisors hx hd)]

/-- **`ν` samples the profiles only at nonnegative points**, being built from `λ`. -/
theorem nu_congr_nonneg {k L : ℕ} {c : Fin L → ℝ} {F G : Fin L → Fin k → ℝ → ℝ} {x : ℝ} (hx : 1 < x)
    (hFG : ∀ l i, ∀ t : ℝ, 0 ≤ t → F l i t = G l i t) (h : Fin k → ℕ) (n : ℕ) :
    nu L c F h x n = nu L c G h x n := by
  simp only [nu, lambdaF_congr_nonneg hx (hFG _ _)]

/-- **The Gram data see the profiles only on `(0,∞)`.** The integral runs over `Set.Ioi 0`, and the
derivative at a positive point is determined by the values at nearby positive points. -/
theorem gramInner_congr_nonneg {k L : ℕ} {F G : Fin L → Fin k → ℝ → ℝ}
    (hFG : ∀ l i, ∀ t : ℝ, 0 ≤ t → F l i t = G l i t) : gramInner F = gramInner G := by
  funext l l' s
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  have hnhds : ∀ H H' : ℝ → ℝ, (∀ u : ℝ, 0 ≤ u → H u = H' u) → deriv H t = deriv H' t := by
    intro H H' hHH'
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [eventually_gt_nhds ht] with u hu using hHH' u hu.le
  rw [hnhds _ _ (hFG l s), hnhds _ _ (hFG l' s)]

/-! ## Truncating a one-sided support to a compact one -/

/-- **A profile vanishing beyond `B` agrees on `[0,∞)` with one of compact support.** Multiplying
by a bump equal to `1` on `[-(|B|+2), |B|+2]` leaves the nonnegative axis untouched — above `|B|+2`
the profile already vanishes — and makes the support compact.

`Gap212.GPY.TensorDatum`'s `compactSupport` field is one-sided, while
`Gap212.Sieve.selberg_progression_sum` asks for `HasCompactSupport` on all of `ℝ`, which no tail
has.

The truncation is `G = F·χ` with `χ` a `ContDiffBump`,
which is `C^∞`, so `G` is exactly as smooth as `F` is and the statement is polymorphic in the index
`n : ℕ∞`. The index cannot be taken in `WithTop ℕ∞`: at `ω` the claim is false, a non-zero analytic
function on `ℝ` having no compact support. -/
theorem exists_truncation {n : ℕ∞} {F : ℝ → ℝ} {B : ℝ} (hF : ContDiff ℝ (n : WithTop ℕ∞) F)
    (hB : ∀ t : ℝ, B < t → F t = 0) :
    ∃ G : ℝ → ℝ, ContDiff ℝ (n : WithTop ℕ∞) G ∧ HasCompactSupport G ∧
      ∀ t : ℝ, 0 ≤ t → F t = G t := by
  set χ : ContDiffBump (0 : ℝ) :=
    { rIn := |B| + 2, rOut := |B| + 3, rIn_pos := by positivity,
      rIn_lt_rOut := by linarith } with hχ
  refine ⟨fun t ↦ F t * χ t, hF.mul χ.contDiff, χ.hasCompactSupport.mul_left, fun t ht ↦ ?_⟩
  rcases le_or_gt t (|B| + 2) with hle | hgt
  · simp [χ.one_of_mem_closedBall (x := t) (by simpa [Real.dist_eq, abs_of_nonneg ht, hχ])]
  · simp [hB t (by linarith [le_abs_self B])]

/-! ## The `ε`-budget split over the `L²` pairs -/

/-- **The denominator asymptotic from the pair sums, by an `ε`-budget split.** Given the pair
asymptotic `|∑_{n ≡ b} (∏ᵢλ_{F l i})(∏ᵢλ_{F l' i}) - (∏ᵢ∫F'_{l,i}F'_{l',i})·𝓒_x| ≤ η·𝓒_x` for every
ordered pair `(l, l')` of tensor indices, the tensor weight `ν` — which is the square of the
`c`-combination — satisfies `|∑_{n ≡ b} ν(n) - 𝓘·𝓒_x| ≤ η·𝓒_x`. The hypothesis is the conclusion
of `Gap212.Sieve.selberg_progression_sum`.

The proof is the expansion of the square into `L²` pair sums
(`Gap212.Sieve.sum_nu_dyadic_eq_sum_pairs`) and a budget split: each pair is taken at
`η/(1 + ∑_{l,l'}|c_l c_{l'}|)` and the threshold is the largest of the finitely many. The main
terms are exactly the summands of `Gap212.Defs.formI c (gramInner F)` by
`Gap212.Sieve.formI_gramInner_eq`. -/
theorem nuDenominator_of_pairSums {k L : ℕ} (c : Fin L → ℝ) (F : Fin L → Fin k → ℝ → ℝ)
    (h : Fin k → ℕ)
    (hpair : ∀ l l' : Fin L, ∀ η > (0 : ℝ), ∃ X : ℝ, ∀ x > X, ∀ b : ℕ,
      Defs.IsPreSieved b (W x) h →
        |(∑ n ∈ dyadic x with n % W x = b % W x,
              (∏ i, lambdaF (F l i) x (n + h i)) * ∏ i, lambdaF (F l' i) x (n + h i)) -
            (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F l i) t * deriv (F l' i) t) * scale k x|
          ≤ η * scale k x) :
    ∀ η > (0 : ℝ), ∃ X : ℝ, ∀ x > X, ∀ b : ℕ, Defs.IsPreSieved b (W x) h →
      |(∑ n ∈ dyadic x with n % W x = b % W x, nu L c F h x n) -
        formI c (gramInner F) * scale k x| ≤ η * scale k x := by
  intro η hη
  -- The budget: one `η'` for each of the `L²` pairs, weighted by `|c_l c_{l'}|`.
  set w : Fin L × Fin L → ℝ := fun q ↦ c q.1 * c q.2
  set T : ℝ := 1 + ∑ q : Fin L × Fin L, |w q| with hT
  have hTpos : 0 < T := by positivity
  have hη' : 0 < η / T := div_pos hη hTpos
  choose Xf hXf using fun q : Fin L × Fin L ↦ hpair q.1 q.2 _ hη'
  obtain ⟨X, hX⟩ := Finite.exists_le Xf
  refine ⟨max X 1, fun x hx b hb ↦ ?_⟩
  have hxX : ∀ q, x > Xf q := fun q ↦ ((hX q).trans (le_max_left X 1)).trans_lt hx
  have hSnn : 0 ≤ scale k x := (scale_pos ((le_max_right X 1).trans_lt hx) (primorial_pos _)).le
  -- Both sides as one sum over the pairs.
  rw [sum_nu_dyadic_eq_sum_pairs, formI_gramInner_eq,
    ← Fintype.sum_prod_type (f := fun q : Fin L × Fin L ↦ w q *
      ∑ n ∈ dyadic x with n % W x = b % W x,
        (∏ i, lambdaF (F q.1 i) x (n + h i)) * ∏ i, lambdaF (F q.2 i) x (n + h i)),
    ← Fintype.sum_prod_type (f := fun q : Fin L × Fin L ↦ w q *
      ∏ s, ∫ t in Set.Ioi (0 : ℝ), deriv (F q.1 s) t * deriv (F q.2 s) t),
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  -- Each pair is within its share of the budget.
  calc |∑ q : Fin L × Fin L, (w q * ∑ n ∈ dyadic x with n % W x = b % W x,
            (∏ i, lambdaF (F q.1 i) x (n + h i)) * ∏ i, lambdaF (F q.2 i) x (n + h i) -
          w q * (∏ s, ∫ t in Set.Ioi (0 : ℝ), deriv (F q.1 s) t * deriv (F q.2 s) t) *
            scale k x)|
      ≤ ∑ q : Fin L × Fin L, |w q| * (η / T * scale k x) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ ↦ ?_)
        refine (le_of_eq ?_).trans (mul_le_mul_of_nonneg_left (hXf q x (hxX q) b hb) (abs_nonneg _))
        rw [← abs_mul]; ring_nf
    _ = (∑ q : Fin L × Fin L, |w q|) * (η / T) * scale k x := by
        rw [← Finset.sum_mul]; ring
    _ ≤ η * scale k x := by
        refine mul_le_mul_of_nonneg_right ?_ hSnn
        grw [show ∑ q, |w q| ≤ T by linarith]
        rw [mul_div_cancel₀ _ hTpos.ne']

/-! ## Retreated families satisfy the support clause of the Gram limit -/

/-- **A retreated family's factors vanish from `1` on, unless the term is null.** This is the
hypothesis of `Gap212.Sieve.LcmGramSumLimitOfSupport` at `β = 1`, derived from the retreat clause
of a tensor datum.

If every factor of the `l`-th term is non-zero *somewhere* on `[0,∞)`, pick such a point in each
coordinate and move the `i`-th to `t`; the product is then non-zero, so the point is retreated, so
its coordinates sum to less than `(1 - ε₀)(A_{j+1} + ε) < 1/2` — and a single coordinate equal to
`t ≥ 1` already exceeds that. The alternative is that some factor vanishes identically on `[0,∞)`,
and then the whole `l`-th term contributes nothing to either side
(`Gap212.Sieve.prod_lambdaF_eq_zero_of_null`, `Gap212.Sieve.prod_gramInner_eq_zero_of_null`). -/
theorem forall_eq_zero_of_one_le_or_null (p : SupportParams) {k L : ℕ} {j : Fin p.n} {ε₀ : ℝ}
    (hε₀ : 0 ≤ ε₀) {F : Fin L → Fin k → ℝ → ℝ}
    (hsupp : ∀ l, ∀ t : Fin k → ℝ, (∀ i, 0 ≤ t i) → (∏ i, F l i (t i)) ≠ 0 →
      t ∈ retreatRegion p k j ε₀) (l : Fin L) :
    (∃ i₀, ∀ t : ℝ, 0 ≤ t → F l i₀ t = 0) ∨ ∀ i, ∀ t : ℝ, 1 ≤ t → F l i t = 0 := by
  by_cases hall : ∀ i, ∃ s : ℝ, 0 ≤ s ∧ F l i s ≠ 0
  · refine Or.inr fun i t ht ↦ ?_
    choose s hs0 hsne using hall
    by_contra hne
    have hnn : ∀ i', 0 ≤ Function.update s i t i' := fun i' ↦ by
      rcases eq_or_ne i' i with rfl | hi
      · rw [Function.update_self]; linarith
      · rw [Function.update_of_ne hi]; exact hs0 i'
    obtain ⟨-, hsum, -⟩ := hsupp l _ hnn (Finset.prod_ne_zero_iff.mpr fun i' _ ↦ by
      rcases eq_or_ne i' i with rfl | hi
      · rwa [Function.update_self]
      · rw [Function.update_of_ne hi]; exact hsne i')
    -- One coordinate of size `t ≥ 1` already exceeds the retreated total mass.
    have hle := Finset.single_le_sum (fun i' _ ↦ hnn i') (Finset.mem_univ i)
    rw [Function.update_self] at hle
    have hA := p.A_mono.monotone (Fin.le_last j.succ)
    have hA₀ := p.A_mono (Fin.succ_pos j)
    rw [p.A_zero] at hA₀
    nlinarith [p.A_last]
  · push Not at hall
    exact Or.inl hall

/-- **A null factor kills the term's divisor-weight product.** If `F l i₀` vanishes on `[0,∞)` then
`λ_{F l i₀}` vanishes, since `λ` reads the profile only at the nonnegative points `log_x d`. -/
theorem prod_lambdaF_eq_zero_of_null {k L : ℕ} {F : Fin L → Fin k → ℝ → ℝ} {l : Fin L} {i₀ : Fin k}
    (hnull : ∀ t : ℝ, 0 ≤ t → F l i₀ t = 0) {x : ℝ} (hx : 1 < x) (h : Fin k → ℕ) (n : ℕ) :
    ∏ i, lambdaF (F l i) x (n + h i) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i₀) (Finset.sum_eq_zero fun d hd ↦ ?_)
  rw [hnull _ (logx_nonneg_of_mem_divisors hx hd), mul_zero]

/-- **A null factor kills the term's Gram product**, the coordinate `i₀` contributing
`∫_{t>0} 0·(F l' i₀)' = 0` because a function vanishing on `[0,∞)` has vanishing derivative on
`(0,∞)`. -/
theorem prod_gramInner_eq_zero_of_null {k L : ℕ} {F : Fin L → Fin k → ℝ → ℝ} {l : Fin L}
    {i₀ : Fin k} (hnull : ∀ t : ℝ, 0 ≤ t → F l i₀ t = 0) (l' : Fin L) :
    ∏ s, gramInner F l l' s = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
  have hz : ∀ t ∈ Set.Ioi (0 : ℝ), deriv (F l i₀) t * deriv (F l' i₀) t = (0 : ℝ) := by
    intro t ht
    have hev : F l i₀ =ᶠ[nhds t] fun _ ↦ (0 : ℝ) := by
      filter_upwards [eventually_gt_nhds ht] with u hu using hnull u hu.le
    simp [hev.deriv_eq]
  simp [gramInner, setIntegral_congr_fun measurableSet_Ioi hz]

/-! ## The same, through the Selberg progression sum -/

/-- **The denominator asymptotic from the Selberg progression sum's two hypotheses.**

`Gap212.Sieve.selberg_progression_sum` gives the pair asymptotic consumed by
`Gap212.Sieve.nuDenominator_of_pairSums`, at `j' = j` with both families retreated at the same
band, with `𝓒_x` identified with the scale by `Gap212.Sieve.calC_eq_scale_succ`. Both hypotheses
hold: `Gap212.Sieve.SelbergSievingError` is `Gap212.Sieve.selbergSievingError`, and
`Gap212.Sieve.LcmGramSumLimitOfSupport` follows from `Gap212.Sieve.polymath41Recip`; see
`Gap212.Sieve.nuDenominator_of_lcmGramSumLimitOfSupport`. The support clause of `hgram` holds at
the profiles by `Gap212.Sieve.forall_eq_zero_of_one_le_or_null`. The profiles are `C^∞`, as
`hgram` asks. -/
theorem nuDenominator_of_obligations (hgram : LcmGramSumLimitOfSupport) {m : ℕ}
    (hsieve : SelbergSievingError m) (p : SupportParams) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1)
    (j : Fin p.n) {L : ℕ} (c : Fin L → ℝ) (F : Fin L → Fin (m + 1) → ℝ → ℝ)
    (hF : ∀ l i, ContDiff ℝ (⊤ : ℕ∞) (F l i)) (hFc : ∀ l i, HasCompactSupport (F l i))
    {h : Fin (m + 1) → ℕ} (hmono : StrictMono h)
    (hsupp : ∀ l, ∀ t : Fin (m + 1) → ℝ, (∀ i, 0 ≤ t i) → (∏ i, F l i (t i)) ≠ 0 →
      t ∈ retreatRegion p (m + 1) j ε₀) :
    ∀ η > (0 : ℝ), ∃ X : ℝ, ∀ x > X, ∀ b : ℕ, Defs.IsPreSieved b (W x) h →
      |(∑ n ∈ dyadic x with n % W x = b % W x, nu L c F h x n) -
        formI c (gramInner F) * scale (m + 1) x| ≤ η * scale (m + 1) x := by
  refine nuDenominator_of_pairSums c F h fun l l' η hη ↦ ?_
  obtain ⟨X, hX⟩ := selberg_progression_sum hgram hsieve p hε₀ hε₀' j j hmono (F l) (F l')
    (fun i ↦ hF l i) (fun i ↦ hFc l i) (fun i ↦ hF l' i) (fun i ↦ hFc l' i)
    (fun t ht ↦ ⟨hsupp l t ht, hsupp l' t ht⟩) η hη
  refine ⟨X, fun x hx b hb ↦ ?_⟩
  rw [← calC_eq_scale_succ]
  simpa only [Finset.prod_mul_distrib] using hX x hx b hb

/-! ## At a tensor datum -/

/-- **The denominator asymptotic at a tensor datum.** The same conclusion at the data
`Gap212.Sieve.sieveWeights` produces, which is where `Gap212.Sieve.gpySieve_of_obligations` applies
it: `Gap212.GPY.TensorDatum` supplies the smoothness and the support clause,
`ε₀ ∈ (0,1)` comes from `Gap212.Sieve.sieveWeights` and `StrictMono h` from `Gap212.DHL`'s own
binder, so every hypothesis of `Gap212.Sieve.nuDenominator_of_obligations` is discharged there.

The datum's one-sided `compactSupport` is handled by `Gap212.Sieve.exists_truncation`: the
truncated profiles are `C^∞` and agree with the datum's on `[0,∞)`, which is all that `ν` and
`gramInner` see. So the conclusion is stated at `D.f` itself, not at the truncation. -/
theorem nuDenominator_of_tensorDatum (hgram : LcmGramSumLimitOfSupport) {m : ℕ}
    (hsieve : SelbergSievingError m) (p : SupportParams) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1)
    {j : Fin p.n} (D : TensorDatum p (m + 1) j ε₀) {h : Fin (m + 1) → ℕ} (hmono : StrictMono h) :
    ∀ η > (0 : ℝ), ∃ X : ℝ, ∀ x > X, ∀ b : ℕ, Defs.IsPreSieved b (W x) h →
      |(∑ n ∈ dyadic x with n % W x = b % W x, nu D.L D.c D.f h x n) -
        formI D.c (gramInner D.f) * scale (m + 1) x| ≤ η * scale (m + 1) x := by
  intro η hη
  obtain ⟨B, hB⟩ := D.compactSupport
  choose G hG hGc hGeq using fun l i ↦ exists_truncation (n := ⊤) (D.smooth l i) (hB l i)
  -- The truncation inherits the support clause, agreeing with the datum on the orthant.
  obtain ⟨X, hX⟩ := nuDenominator_of_obligations hgram hsieve p hε₀ hε₀' j D.c G hG hGc hmono
    (fun l t ht hne ↦ D.supp_subset l t ht
      (by rwa [Finset.prod_congr rfl fun i _ ↦ hGeq l i (t i) (ht i)])) η hη
  refine ⟨max X 1, fun x hx b hb ↦ ?_⟩
  rw [gramInner_congr_nonneg hGeq,
    Finset.sum_congr rfl fun n _ ↦ nu_congr_nonneg ((le_max_right X 1).trans_lt hx) hGeq h n]
  exact hX x ((le_max_left X 1).trans_lt hx) b hb

/-- **`Gap212.Sieve.NuDenominator (m+1)` from the Selberg progression sum's two hypotheses.** This
is `Gap212.Sieve.nuDenominator_of_tensorDatum` read as a `Prop`: `Gap212.Sieve.NuDenominator` asks
for exactly the data that theorem takes. -/
theorem nuDenominator_of_gramObligations (hgram : LcmGramSumLimitOfSupport) {m : ℕ}
    (hsieve : SelbergSievingError m) : NuDenominator (m + 1) :=
  fun p _ε₀ hε₀ hε₀' _j D _h hmono ↦
    nuDenominator_of_tensorDatum hgram hsieve p hε₀ hε₀' D hmono

/-! ## The denominator asymptotic from the Gram limit -/

/-- **The denominator asymptotic from the Gram limit alone.**
`Gap212.Sieve.nuDenominator_of_gramObligations` with its second hypothesis discharged by
`Gap212.Sieve.selbergSievingError`. The remaining hypothesis
`Gap212.Sieve.LcmGramSumLimitOfSupport` follows from `Gap212.Sieve.polymath41Recip` by
`Gap212.Sieve.lcmGramSumLimitOfSupport_iff_polymath41Recip`. -/
theorem nuDenominator_of_lcmGramSumLimitOfSupport (hgram : LcmGramSumLimitOfSupport) (m : ℕ) :
    NuDenominator (m + 1) :=
  nuDenominator_of_gramObligations hgram (selbergSievingError m)

end Gap212.Sieve
