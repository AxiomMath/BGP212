/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.UniformModulusInput
public import Gap212.Sieve.MertensMoebiusSq
public import Gap212.Sieve.WSieve

/-!
# The reciprocal Gram-sum limit, reduced to one analytic statement about the inner sums

`Gap212.Sieve.lcmGramSumLimitOfSupport_iff` shows the reciprocal Gram-sum limit
`Gap212.Sieve.LcmGramSumLimitOfSupport` equivalent to a Riemann sum,

  `(φ(W)/W)\log x·𝓖_x(F,G) = κ_x·∑_{e≤B,(e,W)=1}(μ²(e)/φ(e))·r_F(e)r_G(e)`,
  `κ_x = (W/φ(W))/\log x`,  `r_F(e) = \log x·Z_F(e)·φ(eW)/(eW)`,

which combines two inputs: the Mertens asymptotic for the weight `μ²/φ`, a theorem
(`Gap212.Sieve.sum_moebiusSq_div_totient_coprime`), and the evaluation `r_F(e) → -F'(\log_xe)`.
This file uses the first to restate the Gram-sum limit as a statement about the second.

## The measure

`Gap212.Sieve.tendsto_mertensKappa_mul_weightedSum`: for `H` continuous and vanishing on `[β,∞)`
and any truncation `B(x) ≥ x^β`,

  `κ_x·∑_{e≤B(x),(e,W)=1}(μ²(e)/φ(e))·H(\log_xe) ⟶ ∫_0^∞H`.

The normalized `μ²/φ` weight is Lebesgue measure in the variable `\log_xe`. The proof is a Riemann
sum against the counting function: the `e`-range `[1,x^β]` is cut at `⌊x^{jβ/n}⌋`, the Mertens
asymptotic evaluates the normalized mass of each block as `β/n + o(1)`, and `H`, uniformly
continuous on `[0,β]`, is constant to within `ε` on each block. Only continuity of `H` is assumed,
since `H = F'G'` with `F` and `G` only `C¹`.

The errors of the asymptotic vanish by three facts about the pre-sieving modulus:
`W(x) ≤ \log x/\log\log x` (`Gap212.Sieve.W_le_log_div_log_log`), hence `κ_x → 0`;
`τ(W(x)) ≤ W(x) ≤ \log x`, negligible against the cut `⌊x^{jβ/n}⌋`; and `ellV(W(x)) ≤ \log\log x`
(`Gap212.Sieve.ellV_le_log`).

## The defect statement

`Gap212.Sieve.GramRatioDefectVanishes` says that the defect between the summand and its predicted
value has vanishing normalized weighted sum,

  `κ_x·∑_{e≤B,(e,W)=1}(μ²(e)/φ(e))·(r_F(e)r_G(e) - F'(\log_xe)G'(\log_xe)) ⟶ 0`,

and `Gap212.Sieve.lcmGramSumLimitOfSupport_iff_gramRatioDefectVanishes` proves it equivalent to the
Gram-sum limit. `Gap212.Sieve.NormalizedInnerRatioL1`, with absolute values inside the sum, is a
stronger sufficient condition.

## The top of the `e`-range

`r_F(e) → -F'(\log_xe)` fails uniformly in `e`. `W(x)` is the primorial of
`z = ⌊\log\log\log x⌋`, so every prime not dividing `eW(x)` exceeds `z`, and
`Gap212.Sieve.innerRecip_eq_of_primes_dvd` collapses the inner sum to the single term `F(\log_xe)`
for every `e ∈ (B/(z+1),B]`. There `r_F(e) = \log x·F(\log_xe)·φ(eW)/(eW)` is of size
`\log(z+1)`, against a prediction `F'(\log_xe)` near `F'(β) = 0`. Since `F` vanishes from `β` on
and `B ≥ x^β`, `|F(\log_xe)| ≤ ‖F'‖_∞·\log(z+1)/\log x` there, and the block's normalized weight is
`O(\log(z+1)/\log x)` by the same Mertens asymptotic.

The averages over `e` are therefore not affected by
`Gap212.Sieve.not_uniformMoebiusPartialSumDecay`, which refutes the modulus-free Möbius bound in
that thin top range. The modulus-aware bound `|S_q(w)| ≤ C(q/φ(q))/(1+\log w)`, whose right-hand
side is `≍ e^γ\log z/\log w` at `q = P(z)`, is satisfied there.

## Main definitions

* `Gap212.Sieve.mertensKappa`: the normalization `κ_x = (W/φ(W))/\log x`.
* `Gap212.Sieve.mertensWeight`, `Gap212.Sieve.mertensWeightCut`: the `μ²/φ` weight switched off
  outside the coprimality class, and its counting function below `x^s`.
* `Gap212.Sieve.GramRatioDefectVanishes`: the defect statement.
* `Gap212.Sieve.NormalizedInnerRatioL1`: its weighted-`ℓ¹` strengthening.

## Main results

* `Gap212.Sieve.W_le_log_div_log_log`, `Gap212.Sieve.tendsto_mertensKappa`: the normalization
  vanishes.
* `Gap212.Sieve.tendsto_mertensKappa_mul_weightCut`: the normalized weighted count below `x^s`
  converges to `s`.
* `Gap212.Sieve.tendsto_mertensKappa_mul_weightedSum`: the Riemann sum against a continuous
  profile, and `Gap212.Sieve.tendsto_mertensKappa_mul_weightedSum_gramCex` an instance with a
  positive limit.
* `Gap212.Sieve.lcmGramSumLimitOfSupport_iff_gramRatioDefectVanishes`: the Gram-sum limit is
  equivalent to the defect statement.
* `Gap212.Sieve.lcmGramSumLimitOfSupport_of_normalizedInnerRatioL1`: and follows from the `ℓ¹`
  form.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY
open scoped ArithmeticFunction.Moebius

/-! ## The size of the pre-sieving modulus, one notch sharper -/

/-- **`W(x) ≤ log x / log log x` for large `x`.** `Gap212.Sieve.W_le_log` with the little-`o` run
at the constant `1/(1 + log 4)` instead of `1/log 4`: `W(x) ≤ 4^{log u} = exp((log 4)(log u))` with
`u = log log x`, and `exp((log 4)(log u)) ≤ exp(u - log u) = (log x)/u` as soon as
`(1 + log 4)(log u) ≤ u`. -/
theorem W_le_log_div_log_log :
    ∀ᶠ x : ℝ in atTop, (W x : ℝ) ≤ Real.log x / Real.log (Real.log x) := by
  have hl4 : (0 : ℝ) < 1 + Real.log 4 := by positivity
  have key : ∀ᶠ u : ℝ in atTop, (1 + Real.log 4) * Real.log u ≤ u ∧ 1 ≤ u := by
    have hb := Real.isLittleO_log_id_atTop.bound (c := 1 / (1 + Real.log 4)) (by positivity)
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with u hu hu1
    refine ⟨?_, hu1⟩
    simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u),
      abs_of_nonneg (Real.log_nonneg hu1)] at hu
    rwa [one_div_mul_eq_div, le_div_iff₀' hl4] at hu
  have hcomp : ∀ᶠ x : ℝ in atTop, (1 + Real.log 4) * Real.log (Real.log (Real.log x))
      ≤ Real.log (Real.log x) ∧ 1 ≤ Real.log (Real.log x) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually key
  filter_upwards [hcomp, eventually_gt_atTop (1 : ℝ)] with x ⟨hkey, hu1⟩ hx1
  set u := Real.log (Real.log x) with hu
  calc (W x : ℝ) ≤ ((4 : ℕ) ^ (⌊Real.log u⌋₊ : ℕ) : ℕ) := by
        exact_mod_cast primorial_le_four_pow _
    _ = (4 : ℝ) ^ ((⌊Real.log u⌋₊ : ℕ) : ℝ) := by push_cast [Real.rpow_natCast]; ring
    _ ≤ (4 : ℝ) ^ Real.log u :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le (Real.log_nonneg hu1))
    _ = Real.exp (Real.log u * Real.log 4) := by
        rw [Real.rpow_def_of_pos (by norm_num)]
        ring_nf
    _ ≤ Real.exp (u - Real.log u) := Real.exp_le_exp.mpr (by nlinarith)
    _ = Real.log x / u := by
        rw [Real.exp_sub, Real.exp_log (by linarith : (0 : ℝ) < u), hu,
          Real.exp_log (Real.log_pos hx1)]

/-- **The normalization of the Gram sum's Riemann form**, `κ_x = (W/φ(W))/log x`. It tends to `0`
(`Gap212.Sieve.tendsto_mertensKappa`), which is what makes the isolated `e = 1` term of the
weighted sum harmless. -/
noncomputable def mertensKappa (x : ℝ) : ℝ :=
  (W x : ℝ) / ((W x).totient : ℝ) / Real.log x

/-- `κ_x` written out, for refolding the normalization of
`Gap212.Sieve.MertensWeightedGramLimit`. -/
theorem mertensKappa_eq (x : ℝ) :
    (W x : ℝ) / ((W x).totient : ℝ) / Real.log x = mertensKappa x := rfl

/-- `κ_x ≥ 0` for `x ≥ 1`. -/
theorem mertensKappa_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ mertensKappa x := by
  have := Real.log_nonneg hx
  rw [mertensKappa]
  positivity

/-- **`κ_x → 0`.** `W/φ(W) ≤ W ≤ log x / log log x` (`Gap212.Sieve.W_le_log_div_log_log`), so
`κ_x ≤ 1/log log x`. -/
theorem tendsto_mertensKappa : Tendsto mertensKappa atTop (nhds 0) := by
  have hll : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  refine squeeze_zero' ?_ ?_ hll.inv_tendsto_atTop
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact mertensKappa_nonneg hx
  · filter_upwards [W_le_log_div_log_log, hll.eventually_gt_atTop 0,
      eventually_gt_atTop (1 : ℝ)] with x hW hu hx1
    have hphi : (1 : ℝ) ≤ ((W x).totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (primorial_pos _)
    rw [mertensKappa, div_le_iff₀ (Real.log_pos hx1), Pi.inv_apply, inv_mul_eq_div]
    exact (div_le_self (Nat.cast_nonneg _) hphi).trans hW


/-! ## The weighted counting function at a power cutoff -/

/-- **The `μ²/φ` weight summed over the coprimality class below `x^s`**, the counting function
whose normalized increments are the Riemann-sum measure of
`Gap212.Sieve.MertensWeightedGramLimit`. -/
noncomputable def mertensWeightCut (x s : ℝ) : ℝ :=
  ∑ e ∈ Icc 1 ⌊x ^ s⌋₊ with Nat.Coprime (W x) e, ((μ e : ℝ) ^ 2 / (e.totient : ℝ))

/-- At `s = 0` the cutoff is `1` and the only term is `e = 1`. -/
theorem mertensWeightCut_zero {x : ℝ} : mertensWeightCut x 0 = 1 := by
  simp [mertensWeightCut, Finset.filter_singleton]

/-- The cut weight sum `mertensWeightCut x s` is nonnegative. -/
theorem mertensWeightCut_nonneg (x s : ℝ) : 0 ≤ mertensWeightCut x s :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The floor of `x^s` is within a factor `2` of `x^s`, and at least `1`, for large `x`. -/
theorem eventually_floor_rpow {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, (2 : ℝ) ≤ x ^ s ∧ x ^ s / 2 ≤ (⌊x ^ s⌋₊ : ℝ)
      ∧ ((⌊x ^ s⌋₊ : ℕ) : ℝ) ≤ x ^ s ∧ 1 ≤ ⌊x ^ s⌋₊ := by
  filter_upwards [(tendsto_rpow_atTop hs).eventually_ge_atTop (2 : ℝ)] with x hx
  have hnn : (0 : ℝ) ≤ x ^ s := by linarith
  refine ⟨hx, ?_, Nat.floor_le hnn, Nat.le_floor (by exact_mod_cast (by linarith : (1:ℝ) ≤ x ^ s))⟩
  have := Nat.sub_one_lt_floor (x ^ s)
  linarith

/-- `log ⌊x^s⌋₊` is within `log 2` of `s log x` once `x^s / 2 ≤ ⌊x^s⌋₊`. -/
theorem abs_log_floor_rpow_sub_le {x s : ℝ} (hx : 0 < x) (h2 : 2 ≤ x ^ s)
    (hlo : x ^ s / 2 ≤ (⌊x ^ s⌋₊ : ℝ)) (hhi : ((⌊x ^ s⌋₊ : ℕ) : ℝ) ≤ x ^ s) :
    |Real.log ((⌊x ^ s⌋₊ : ℕ) : ℝ) - s * Real.log x| ≤ Real.log 2 := by
  have h1 := Real.log_le_log (by linarith) hlo
  rw [Real.log_div (by positivity) (by norm_num)] at h1
  rw [abs_le, ← Real.log_rpow hx]
  constructor
  · linarith
  · linarith [Real.log_le_log (by linarith) hhi, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

/-- The divisor count of `V ≤ log x` is at most `N` once `log x / y < 1 / 2 ≤ N / y`. -/
theorem card_divisors_div_le_one {V N : ℕ} {x y : ℝ} (hV : (V : ℝ) ≤ Real.log x) (hy : 0 < y)
    (hsmall : Real.log x / y < 1 / 2) (hN : y / 2 ≤ N) : ((#V.divisors : ℕ) : ℝ) / N ≤ 1 := by
  have : ((#V.divisors : ℕ) : ℝ) ≤ V := by exact_mod_cast Nat.card_divisors_le_self _
  rw [div_lt_iff₀ hy] at hsmall
  rw [div_le_one (by linarith)]
  linarith

/-- `(|γ| + log log x) / log x → 0`. -/
theorem tendsto_abs_eulerMascheroni_add_log_log_div_log : Tendsto (fun x : ℝ ↦
    (|Real.eulerMascheroniConstant| + Real.log (Real.log x)) / Real.log x) atTop (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ ↦ |Real.eulerMascheroniConstant| / Real.log x) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop
  have h2 : Tendsto (fun x : ℝ ↦ Real.log (Real.log x) / Real.log x) atTop (nhds 0) := by
    simpa [Function.comp_def] using (Real.isLittleO_log_id_atTop.comp_tendsto
      Real.tendsto_log_atTop).tendsto_div_nhds_zero
  simpa [add_div] using h1.add h2

/-- **The normalized weighted count below `x^s` converges to `s`.** This is the Mertens asymptotic
`Gap212.Sieve.sum_moebiusSq_div_totient_coprime` read at `N = ⌊x^s⌋`, divided by its own prefactor:
`κ_x·A_W(⌊x^s⌋) = (log⌊x^s⌋ + γ + ellV W)/log x + κ_x·E`, and all three corrections vanish —
`log⌊x^s⌋ = s log x + O(1)`, `ellV (W x) ≤ log log x`, and `κ_x·E ≪ κ_x → 0` because
`τ(W x) ≤ W x ≤ log x` is negligible against `⌊x^s⌋`. -/
theorem tendsto_mertensKappa_mul_weightCut {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ ↦ mertensKappa x * mertensWeightCut x s) atTop (nhds s) := by
  obtain ⟨C, hC, hasym⟩ := sum_moebiusSq_div_totient_coprime
  have hlogdiv : Tendsto (fun x : ℝ ↦ Real.log x / x ^ s) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero
  have hkap : Tendsto (fun x : ℝ ↦ 2 * C * mertensKappa x) atTop (nhds 0) := by
    simpa using tendsto_mertensKappa.const_mul (2 * C)
  have hlog2 : Tendsto (fun x : ℝ ↦ Real.log 2 / Real.log x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  rw [Metric.tendsto_nhds]
  intro η hη
  have hη3 : (0 : ℝ) < η / 3 := by linarith
  filter_upwards [eventually_floor_rpow hs, W_le_log, eventually_gt_atTop (1 : ℝ),
    hlogdiv.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2)),
    hkap.eventually (gt_mem_nhds hη3),
    tendsto_abs_eulerMascheroni_add_log_log_div_log.eventually (gt_mem_nhds hη3),
    hlog2.eventually (gt_mem_nhds hη3)]
    with x ⟨h2le, hlo, hhi, hN1⟩ hWlog hx1 hsmall hkx hgx h2x
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hxpos : (0 : ℝ) < x := by linarith
  have hW1 : 1 ≤ W x := primorial_pos _
  have hkpos : 0 ≤ mertensKappa x := mertensKappa_nonneg (by linarith)
  -- the divisor count of `W x` is below the cutoff, so the error term is `≤ 2C`
  have htauN : ((#(W x).divisors : ℕ) : ℝ) / ((⌊x ^ s⌋₊ : ℕ) : ℝ) ≤ 1 :=
    card_divisors_div_le_one hWlog (by linarith) hsmall hlo
  -- the constant `ellV` is between `0` and `log log x`
  -- assemble
  set D : ℝ := (mertensWeightCut x s) - ((W x).totient : ℝ) / (W x : ℝ)
      * (Real.log ((⌊x ^ s⌋₊ : ℕ) : ℝ) + Real.eulerMascheroniConstant + PrimeGaps.ellV (W x))
    with hD
  have hDbd : |D| ≤ 2 * C :=
    (hasym (W x) hW1 (squarefree_primorial _) ⌊x ^ s⌋₊ hN1).trans (by nlinarith [hC.le])
  have hsplit : mertensKappa x * mertensWeightCut x s - s
      = mertensKappa x * D
        + (Real.log ((⌊x ^ s⌋₊ : ℕ) : ℝ) - s * Real.log x) / Real.log x
        + (Real.eulerMascheroniConstant + PrimeGaps.ellV (W x)) / Real.log x := by
    rw [hD, mertensKappa]
    field_simp
    ring
  have b1 : |mertensKappa x * D| ≤ 2 * C * mertensKappa x := by
    rw [abs_mul, abs_of_nonneg hkpos]
    nlinarith [abs_nonneg D]
  have b2 : |(Real.log ((⌊x ^ s⌋₊ : ℕ) : ℝ) - s * Real.log x) / Real.log x|
      ≤ Real.log 2 / Real.log x := by
    rw [abs_div, abs_of_pos hL, div_le_div_iff_of_pos_right hL]
    exact abs_log_floor_rpow_sub_le hxpos h2le hlo hhi
  have b3 : |(Real.eulerMascheroniConstant + PrimeGaps.ellV (W x)) / Real.log x|
      ≤ (|Real.eulerMascheroniConstant| + Real.log (Real.log x)) / Real.log x := by
    rw [abs_div, abs_of_pos hL, div_le_div_iff_of_pos_right hL]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_of_nonneg (PrimeGaps.ellV_nonneg _)]
    linarith [(ellV_le_log hW1).trans (Real.log_le_log (by exact_mod_cast hW1) hWlog)]
  rw [Real.dist_eq, hsplit]
  exact (abs_add_three _ _ _).trans_lt (by linarith)


/-! ## The Riemann sum against a continuous profile -/

/-- **The `μ²/φ` weight switched off outside the coprimality class**, so that the filtered sums of
the Gram sum are plain sums over an interval, which `Gap212.Sieve.sum_Ioc_chain` chops at the
partition points. -/
noncomputable def mertensWeight (x : ℝ) (e : ℕ) : ℝ :=
  if Nat.Coprime (W x) e then (μ e : ℝ) ^ 2 / (e.totient : ℝ) else 0

/-- The weight `mertensWeight x e` is nonnegative. -/
theorem mertensWeight_nonneg (x : ℝ) (e : ℕ) : 0 ≤ mertensWeight x e := by
  rw [mertensWeight]
  split_ifs <;> positivity

/-- `mertensWeightCut x t` is the plain sum of `mertensWeight x e` over `1 ≤ e ≤ ⌊x^t⌋`. -/
theorem mertensWeightCut_eq_sum (x t : ℝ) :
    mertensWeightCut x t = ∑ e ∈ Finset.Icc 1 ⌊x ^ t⌋₊, mertensWeight x e := by
  rw [mertensWeightCut, Finset.sum_filter]
  rfl

/-- Chopping a sum over `(M 0, M n]` at the partition points `M 1, …, M (n-1)`. -/
theorem sum_Ioc_chain {M : ℕ → ℕ} (hM : ∀ j, M j ≤ M (j + 1)) (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, ∑ e ∈ Finset.Ioc (M j) (M (j + 1)), f e
      = ∑ e ∈ Finset.Ioc (M 0) (M n), f e := by
  have hmono : Monotone M := monotone_nat_of_le_succ hM
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, ← Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl),
      Finset.Ioc_union_Ioc_eq_Ioc (hmono (Nat.zero_le n)) (hM n)]

/-- **A nonnegatively weighted sum is within `ε` of the constant it is compared against**, for an
abstract weight and profile. -/
theorem abs_sum_sub_const_mul_le {S : Finset ℕ} {w g : ℕ → ℝ} {c ε : ℝ}
    (hw : ∀ e ∈ S, 0 ≤ w e) (hg : ∀ e ∈ S, |g e - c| ≤ ε) :
    |∑ e ∈ S, w e * g e - c * ∑ e ∈ S, w e| ≤ ε * ∑ e ∈ S, w e := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun e he => ?_)
  rw [show w e * g e - c * w e = w e * (g e - c) by ring, abs_mul, abs_of_nonneg (hw e he),
    mul_comm ε (w e)]
  exact mul_le_mul_of_nonneg_left (hg e he) (hw e he)

/-- The normalized weighted count below `x^s` converges to `s` for every `s ≥ 0`: at `s = 0` the
count is the single term `e = 1` and the normalization itself tends to `0`. -/
theorem tendsto_mertensKappa_mul_weightCut_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun x : ℝ ↦ mertensKappa x * mertensWeightCut x s) atTop (nhds s) := by
  obtain rfl | h := hs.eq_or_lt
  · simpa [mertensWeightCut_zero] using tendsto_mertensKappa
  · exact tendsto_mertensKappa_mul_weightCut h

/-- **The normalized `μ²/φ` weight is Lebesgue measure in `log_x e`.** For `H` continuous and
vanishing on `[β,∞)` and any truncation `B(x) ≥ x^β`,

  `(W/φ(W))/log x · ∑_{e ≤ B(x), (W,e)=1}(μ²(e)/φ(e))·H(log_x e) ⟶ ∫_0^∞ H`.

The only arithmetic input is the Mertens asymptotic
`Gap212.Sieve.sum_moebiusSq_div_totient_coprime`, read at the partition points `⌊x^{jβ/n}⌋`.
Above `⌊x^β⌋` every term vanishes, so the `e`-range is `[1, x^β]` and its normalized mass converges
to `β`. -/
theorem tendsto_mertensKappa_mul_weightedSum {H : ℝ → ℝ} (hH : Continuous H) {β : ℝ}
    (hβ : 0 < β) (hHv : ∀ t, β ≤ t → H t = 0) (B : ℝ → ℕ)
    (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦ mertensKappa x *
        ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) * H (Notation.logx x e))
      atTop (nhds (∫ t in Set.Ioi (0 : ℝ), H t)) := by
  classical
  have hIeq : (∫ t in Set.Ioi (0 : ℝ), H t) = ∫ t in (0 : ℝ)..β, H t := by
    rw [intervalIntegral.integral_of_le hβ.le]
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self ?_
    intro t ht
    simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_Ioc, not_and, not_le] at ht
    exact hHv t (ht.2 ht.1).le
  rw [hIeq, Metric.tendsto_nhds]
  intro η hη
  have hβ1 : (0 : ℝ) < β + 1 := by linarith
  set ε : ℝ := η / (4 * (β + 1)) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  obtain ⟨δ, hδ, hδH⟩ := (Metric.uniformContinuousOn_iff_le.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := β)).uniformContinuousOn_of_continuous
      hH.continuousOn)) ε hε
  obtain ⟨n, hnlt⟩ := exists_nat_gt (β / δ)
  have hnR : (0 : ℝ) < (n : ℝ) := lt_trans (by positivity) hnlt
  have hmesh : β / (n : ℝ) ≤ δ :=
    (div_le_iff₀ hnR).2 (by rw [div_lt_iff₀ hδ] at hnlt; linarith)
  set s : ℕ → ℝ := fun j ↦ (j : ℝ) * β / (n : ℝ) with hsdef
  have hs0 : s 0 = 0 := by simp [hsdef]
  have hsn : s n = β := by rw [hsdef]; field_simp
  have hsdiff : ∀ j, s (j + 1) - s j = β / (n : ℝ) := fun j => by
    rw [hsdef]; push_cast; ring
  have hsmono : ∀ j, s j ≤ s (j + 1) := fun j => by
    linarith [hsdiff j, (by positivity : (0 : ℝ) ≤ β / (n : ℝ))]
  have hsnn : ∀ j, 0 ≤ s j := fun j => by rw [hsdef]; positivity
  have hsle : ∀ j, j ≤ n → s j ≤ β := by
    intro j hj
    rw [hsdef, div_le_iff₀ hnR]
    nlinarith [(by exact_mod_cast hj : (j : ℝ) ≤ (n : ℝ))]
  have hsmem : ∀ j, j ≤ n → s j ∈ Set.Icc (0 : ℝ) β := fun j hj => ⟨hsnn j, hsle j hj⟩
  -- the Riemann sum of `H` at the right endpoints is within `ε β` of the integral
  have hRint : |(∑ j ∈ Finset.range n, H (s (j + 1)) * (s (j + 1) - s j))
      - ∫ t in (0 : ℝ)..β, H t| ≤ ε * β := by
    have hsplit : (∫ t in (0 : ℝ)..β, H t)
        = ∑ k ∈ Finset.range n, ∫ t in (s k)..(s (k + 1)), H t := by
      rw [intervalIntegral.sum_integral_adjacent_intervals
        (fun k _ => hH.intervalIntegrable _ _), hs0, hsn]
    have hterm : ∀ k ∈ Finset.range n,
        |H (s (k + 1)) * (s (k + 1) - s k) - ∫ t in (s k)..(s (k + 1)), H t|
          ≤ ε * (s (k + 1) - s k) := by
      intro k hk
      have hkn : k + 1 ≤ n := Finset.mem_range.mp hk
      have hle : s k ≤ s (k + 1) := hsmono k
      have hrw : H (s (k + 1)) * (s (k + 1) - s k) - ∫ t in (s k)..(s (k + 1)), H t
          = ∫ t in (s k)..(s (k + 1)), (H (s (k + 1)) - H t) := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const
          (hH.intervalIntegrable _ _), intervalIntegral.integral_const, smul_eq_mul]
        ring
      rw [hrw]
      have hbd : ∀ t ∈ Set.uIoc (s k) (s (k + 1)), ‖H (s (k + 1)) - H t‖ ≤ ε := by
        intro t ht
        rw [Set.uIoc_of_le hle] at ht
        have htmem : t ∈ Set.Icc (0 : ℝ) β :=
          ⟨le_trans (hsnn k) ht.1.le, le_trans ht.2 (hsle _ hkn)⟩
        rw [← dist_eq_norm]
        refine hδH _ (hsmem _ hkn) t htmem ?_
        rw [Real.dist_eq, abs_of_nonneg (by linarith [ht.2] : (0 : ℝ) ≤ s (k + 1) - t)]
        linarith [hsdiff k, ht.1]
      simpa [abs_of_nonneg (sub_nonneg.2 hle)] using
        intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [hsplit, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_range_sub s, hs0, hsn, sub_zero]
  -- the three limits
  have hG : Tendsto (fun x : ℝ ↦ ∑ j ∈ Finset.range n, H (s (j + 1)) *
        (mertensKappa x * (mertensWeightCut x (s (j + 1)) - mertensWeightCut x (s j))))
      atTop (nhds (∑ j ∈ Finset.range n, H (s (j + 1)) * (s (j + 1) - s j))) := by
    refine tendsto_finsetSum _ fun j _ => Tendsto.const_mul _ ?_
    simpa [mul_sub] using (tendsto_mertensKappa_mul_weightCut_of_nonneg (hsnn (j + 1))).sub
      (tendsto_mertensKappa_mul_weightCut_of_nonneg (hsnn j))
  have hK0 : Tendsto (fun x : ℝ ↦ mertensKappa x * |H 0|) atTop (nhds 0) := by
    simpa using tendsto_mertensKappa.mul_const |H 0|
  filter_upwards [hB, eventually_gt_atTop (1 : ℝ),
    Metric.tendsto_nhds.1 hG (η / 8) (by linarith),
    Metric.tendsto_nhds.1 (tendsto_mertensKappa_mul_weightCut hβ) 1 one_pos,
    Metric.tendsto_nhds.1 hK0 (η / 8) (by linarith)] with x hBx hx1 hGx hAx hKx
  have hxpos : (0 : ℝ) < x := by linarith
  have hLx : 0 < Real.log x := Real.log_pos hx1
  have hkpos : 0 ≤ mertensKappa x := mertensKappa_nonneg hx1.le
  -- the partition points
  have hMmono : ∀ j, ⌊x ^ s j⌋₊ ≤ ⌊x ^ s (j + 1)⌋₊ := fun j =>
    Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hx1.le (hsmono j))
  have hM0 : ⌊x ^ s 0⌋₊ = 1 := by rw [hs0, Real.rpow_zero, Nat.floor_one]
  have hMn : ⌊x ^ s n⌋₊ = ⌊x ^ β⌋₊ := by rw [hsn]
  -- `log_x e` at the partition points
  have hlogxlo : ∀ (j : ℕ) (e : ℕ), ⌊x ^ s j⌋₊ < e → s j < Notation.logx x e := by
    intro j e he
    have h := Real.log_lt_log (by positivity) ((Nat.floor_lt (by positivity)).1 he)
    rw [Real.log_rpow hxpos] at h
    rw [Notation.logx, lt_div_iff₀ hLx]
    linarith
  have hlogxhi : ∀ (j : ℕ) (e : ℕ), 1 ≤ e → e ≤ ⌊x ^ s j⌋₊ → Notation.logx x e ≤ s j := by
    intro j e he1 he
    have h := Real.log_le_log (by exact_mod_cast he1) ((Nat.le_floor_iff (by positivity)).1 he)
    rw [Real.log_rpow hxpos] at h
    rw [Notation.logx, div_le_iff₀ hLx]
    linarith
  -- rewrite the sum as a plain sum of `mertensWeight`
  have step1 : (∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
        ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) * H (Notation.logx x e))
      = ∑ e ∈ Finset.Icc 1 (B x), mertensWeight x e * H (Notation.logx x e) := by
    simp only [Finset.sum_filter, mertensWeight, ite_mul, zero_mul]
  have hfloorB : ⌊x ^ β⌋₊ ≤ B x := by simpa using Nat.floor_le_floor hBx
  have step2 : (∑ e ∈ Finset.Icc 1 (B x), mertensWeight x e * H (Notation.logx x e))
      = ∑ e ∈ Finset.Icc 1 ⌊x ^ β⌋₊, mertensWeight x e * H (Notation.logx x e) := by
    refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hfloorB) ?_).symm
    intro e he hne
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hgt : ⌊x ^ β⌋₊ < e := lt_of_not_ge fun hc => hne (Finset.mem_Icc.mpr ⟨he1, hc⟩)
    have : β < Notation.logx x e := by
      have := hlogxlo n e (by rwa [hMn])
      rwa [hsn] at this
    rw [hHv _ this.le, mul_zero]
  have hM1 : ∀ j : ℕ, 1 ≤ ⌊x ^ s j⌋₊ := fun j =>
    hM0 ▸ monotone_nat_of_le_succ hMmono (Nat.zero_le j)
  have hIccsplit : ∀ a b : ℕ, 1 ≤ a → a ≤ b →
      Finset.Icc 1 b = Finset.Icc 1 a ∪ Finset.Ioc a b := by
    intro a b h1 hab
    ext e
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisjIcc : ∀ a b : ℕ, Disjoint (Finset.Icc 1 a) (Finset.Ioc a b) := fun a b =>
    Finset.disjoint_left.2 fun e he he' => by
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at he he'
      omega
  have step3 : (∑ e ∈ Finset.Icc 1 ⌊x ^ β⌋₊, mertensWeight x e * H (Notation.logx x e))
      = H 0 + ∑ j ∈ Finset.range n,
          ∑ e ∈ Finset.Ioc ⌊x ^ s j⌋₊ ⌊x ^ s (j + 1)⌋₊,
            mertensWeight x e * H (Notation.logx x e) := by
    rw [sum_Ioc_chain hMmono, hM0, hMn, hIccsplit 1 _ le_rfl (hMn ▸ hM1 n),
      Finset.sum_union (hdisjIcc _ _), Finset.Icc_self, Finset.sum_singleton]
    simp [mertensWeight, Notation.logx]
  -- the normalized mass of each block
  have hWtblk : ∀ j : ℕ, (∑ e ∈ Finset.Ioc ⌊x ^ s j⌋₊ ⌊x ^ s (j + 1)⌋₊, mertensWeight x e)
      = mertensWeightCut x (s (j + 1)) - mertensWeightCut x (s j) := by
    intro j
    rw [mertensWeightCut_eq_sum, mertensWeightCut_eq_sum,
      hIccsplit _ _ (hM1 j) (hMmono j), Finset.sum_union (hdisjIcc _ _)]
    ring
  -- the block estimate
  have hblk : ∀ j ∈ Finset.range n,
      |(∑ e ∈ Finset.Ioc ⌊x ^ s j⌋₊ ⌊x ^ s (j + 1)⌋₊, mertensWeight x e * H (Notation.logx x e))
          - H (s (j + 1)) * (mertensWeightCut x (s (j + 1)) - mertensWeightCut x (s j))|
        ≤ ε * (mertensWeightCut x (s (j + 1)) - mertensWeightCut x (s j)) := by
    intro j hj
    have hjn : j + 1 ≤ n := Finset.mem_range.mp hj
    have hgb : ∀ e ∈ Finset.Ioc ⌊x ^ s j⌋₊ ⌊x ^ s (j + 1)⌋₊,
        |H (Notation.logx x e) - H (s (j + 1))| ≤ ε := by
      intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_Ioc.mp he
      have he1' : 1 ≤ e := le_trans (hM1 j) he1.le
      have hlo := hlogxlo j e he1
      have hhi := hlogxhi (j + 1) e he1' he2
      have hmem : Notation.logx x e ∈ Set.Icc (0 : ℝ) β :=
        ⟨le_trans (hsnn j) hlo.le, le_trans hhi (hsle _ hjn)⟩
      rw [← Real.dist_eq]
      refine hδH _ hmem _ (hsmem _ hjn) ?_
      rw [Real.dist_eq, abs_of_nonpos (by linarith : Notation.logx x e - s (j + 1) ≤ 0)]
      linarith [hsdiff j]
    have hmain := abs_sum_sub_const_mul_le (w := mertensWeight x)
      (g := fun e ↦ H (Notation.logx x e)) (c := H (s (j + 1))) (ε := ε)
      (fun e _ ↦ mertensWeight_nonneg x e) hgb
    rwa [hWtblk j] at hmain
  have hblksum : |(∑ j ∈ Finset.range n, ∑ e ∈ Finset.Ioc ⌊x ^ s j⌋₊ ⌊x ^ s (j + 1)⌋₊,
          mertensWeight x e * H (Notation.logx x e))
        - ∑ j ∈ Finset.range n, H (s (j + 1)) *
            (mertensWeightCut x (s (j + 1)) - mertensWeightCut x (s j))|
      ≤ ε * (mertensWeightCut x β - 1) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hblk).trans_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun j ↦ mertensWeightCut x (s j)), hs0, hsn,
      mertensWeightCut_zero]
  -- assemble
  have hQ : mertensKappa x * (∑ j ∈ Finset.range n, H (s (j + 1)) *
        (mertensWeightCut x (s (j + 1)) - mertensWeightCut x (s j)))
      = ∑ j ∈ Finset.range n, H (s (j + 1)) *
        (mertensKappa x * (mertensWeightCut x (s (j + 1)) - mertensWeightCut x (s j))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hSid : mertensKappa x * (∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
        ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) * H (Notation.logx x e))
      = mertensKappa x * H 0 + mertensKappa x *
          ∑ j ∈ Finset.range n, ∑ e ∈ Finset.Ioc ⌊x ^ s j⌋₊ ⌊x ^ s (j + 1)⌋₊,
            mertensWeight x e * H (Notation.logx x e) := by
    rw [step1, step2, step3, mul_add]
  -- the numerical bounds
  rw [Real.dist_eq] at hGx hAx hKx
  set P : ℝ := ∑ j ∈ Finset.range n, ∑ e ∈ Finset.Ioc ⌊x ^ s j⌋₊ ⌊x ^ s (j + 1)⌋₊,
    mertensWeight x e * H (Notation.logx x e) with hPdef
  set Q : ℝ := ∑ j ∈ Finset.range n, H (s (j + 1)) *
    (mertensWeightCut x (s (j + 1)) - mertensWeightCut x (s j)) with hQdef
  set Gv : ℝ := ∑ j ∈ Finset.range n, H (s (j + 1)) *
    (mertensKappa x * (mertensWeightCut x (s (j + 1)) - mertensWeightCut x (s j))) with hGvdef
  set R : ℝ := ∑ j ∈ Finset.range n, H (s (j + 1)) * (s (j + 1) - s j) with hRdef
  set I : ℝ := ∫ t in (0 : ℝ)..β, H t with hIdef
  have hεβ : ε * (β + 1) = η / 4 := by rw [hεdef]; field_simp
  have hcutnn : 0 ≤ mertensWeightCut x β := mertensWeightCut_nonneg x β
  have hAlt : mertensKappa x * mertensWeightCut x β < β + 1 := by linarith [(abs_lt.1 hAx).2]
  have hb1 : |mertensKappa x * H 0| < η / 8 := by
    rw [abs_mul, abs_of_nonneg hkpos]
    linarith [(abs_lt.1 hKx).2]
  have hb2 : |mertensKappa x * P - Gv| ≤ η / 4 := by
    rw [← hQ, ← mul_sub, abs_mul, abs_of_nonneg hkpos]
    calc mertensKappa x * |P - Q|
        ≤ mertensKappa x * (ε * (mertensWeightCut x β - 1)) :=
          mul_le_mul_of_nonneg_left hblksum hkpos
      _ ≤ ε * (β + 1) := by nlinarith [hε.le, hkpos, hAlt]
      _ = η / 4 := hεβ
  have hb4 : |R - I| ≤ η / 4 := hRint.trans (by nlinarith [hε.le, hβ.le])
  rw [hSid, Real.dist_eq, show mertensKappa x * H 0 + mertensKappa x * P - I
      = mertensKappa x * H 0 + (mertensKappa x * P - Gv) + (Gv - R) + (R - I) from by ring]
  exact (abs_add_le _ _).trans_lt
    (by linarith [abs_add_three (mertensKappa x * H 0) (mertensKappa x * P - Gv) (Gv - R)])


/-! ## The defect statement, and its weighted-`ℓ¹` form -/

/-- **A `C¹` profile vanishing from `β` on has vanishing derivative from `β` on.** Above `β` the
function is locally zero, so the derivative is; at `β` itself the derivative is the limit of its
values to the right, `deriv F` being continuous. This is why the support hypothesis of
`Gap212.Sieve.LcmGramSumLimitOfSupport` controls the predicted value `-F'(log_x e)` at the top of
the `e`-range. -/
theorem deriv_eq_zero_of_eventually_zero {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) {β : ℝ}
    (hFv : ∀ t, β ≤ t → F t = 0) : ∀ t, β ≤ t → deriv F t = 0 := by
  have hgt : ∀ t, β < t → deriv F t = 0 := fun t ht => by
    rw [Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (0 : ℝ))
      ((lt_mem_nhds ht).mono fun u hu => hFv u hu.le), deriv_const]
  intro t ht
  obtain rfl | h := ht.eq_or_lt
  · refine tendsto_nhds_unique
      (hF.continuous_deriv_one.continuousWithinAt (s := Set.Ioi β)).tendsto
      (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with u hu using (hgt u hu).symm
  · exact hgt t h

/-- **An instance of `Gap212.Sieve.tendsto_mertensKappa_mul_weightedSum` with a positive limit.**
`H = (F')²` at the `C^∞` bump `F = Gap212.Sieve.gramCexProfile`, with `tsupport F = [2,4]`, is
continuous and vanishes on `[5,∞)`; with `β = 5` and `B(x) = ⌊x^5⌋+1 ≥ x^5` the limit is
`∫_0^∞(F')²`, which is positive (`Gap212.Sieve.integral_deriv_gramCexProfile_sq_pos`). -/
theorem tendsto_mertensKappa_mul_weightedSum_gramCex :
    (0 < ∫ t in Set.Ioi (0 : ℝ), deriv gramCexProfile t * deriv gramCexProfile t)
      ∧ Tendsto (fun x : ℝ ↦ mertensKappa x *
          ∑ e ∈ Icc 1 (⌊x ^ (5 : ℝ)⌋₊ + 1) with Nat.Coprime (W x) e,
            ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
              (deriv gramCexProfile (Notation.logx x e) * deriv gramCexProfile (Notation.logx x e)))
        atTop (nhds (∫ t in Set.Ioi (0 : ℝ), deriv gramCexProfile t * deriv gramCexProfile t)) := by
  have hvan : ∀ t : ℝ, (5 : ℝ) ≤ t → gramCexProfile t = 0 := by
    intro t ht
    refine image_eq_zero_of_notMem_tsupport ?_
    rw [gramCexProfile_tsupport, Metric.mem_closedBall, Real.dist_eq]
    intro hc
    linarith [(abs_le.mp hc).2]
  have hcont : Continuous fun t : ℝ ↦ deriv gramCexProfile t * deriv gramCexProfile t :=
    gramCexProfile_contDiff_one.continuous_deriv_one.mul
      gramCexProfile_contDiff_one.continuous_deriv_one
  refine ⟨integral_deriv_gramCexProfile_sq_pos,
    tendsto_mertensKappa_mul_weightedSum (β := 5) hcont (by norm_num) (fun t ht ↦ ?_) _ ?_⟩
  · rw [deriv_eq_zero_of_eventually_zero gramCexProfile_contDiff_one hvan t ht, zero_mul]
  · filter_upwards with x
    have h := Nat.lt_floor_add_one (x ^ (5 : ℝ))
    push_cast
    linarith

/-- Pulling the normalization through a difference of weighted sums. -/
theorem mertensKappa_mul_sum_sub (x : ℝ) (N : ℕ) (a b : ℕ → ℝ) :
    mertensKappa x * ∑ e ∈ Icc 1 N with Nat.Coprime (W x) e,
        ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) * (a e - b e)
      = (mertensKappa x * ∑ e ∈ Icc 1 N with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) * a e)
        - mertensKappa x * ∑ e ∈ Icc 1 N with Nat.Coprime (W x) e,
          ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) * b e := by
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun e _ ↦ by ring)

/-- **The reciprocal Gram-sum limit, as a defect statement.** With
`r_F(e) = log x·Z_F(e)·φ(eW)/(eW)` the normalized inner sum (`Gap212.Sieve.innerRecipRatio`) and
`κ_x = (W/φ(W))/log x`, the defect between the summand and its predicted value has vanishing
normalized weighted sum:

  `κ_x·∑_{e≤B,(e,W)=1}(μ²(e)/φ(e))·(r_F(e)r_G(e) − F'(log_x e)G'(log_x e)) ⟶ 0`,

for `C^∞` compactly supported profiles vanishing from `β` on and truncations `B ≥ x^β`.

It is equivalent to `Gap212.Sieve.LcmGramSumLimitOfSupport`
(`Gap212.Sieve.lcmGramSumLimitOfSupport_iff_gramRatioDefectVanishes`):
`Gap212.Sieve.tendsto_mertensKappa_mul_weightedSum` evaluates the same normalized sum with the
predicted summand as `∫_0^∞F'G'`. A sufficient form is `Gap212.Sieve.NormalizedInnerRatioL1`.

At the top of the range, `e ∈ (B/(z+1), B]` with `z = ⌊log log log x⌋`, the inner sum collapses to
the single term `F(log_x e)` (`Gap212.Sieve.innerRecip_eq_of_primes_dvd`), so `r_F(e)` does not
converge to `-F'(log_x e)` uniformly in `e`; the support hypothesis bounds
`|F(log_x e)| ≤ ‖F'‖_∞·log(z+1)/log x` there. -/
def GramRatioDefectVanishes : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → ContDiff ℝ (⊤ : ℕ∞) G →
    HasCompactSupport G →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) → (∀ t, β ≤ t → G t = 0) →
      ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
        Filter.Tendsto (fun x : ℝ ↦ mertensKappa x *
            ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
              ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
                (innerRecipRatio (W x) e F x (B x) * innerRecipRatio (W x) e G x (B x)
                  - deriv F (Notation.logx x e) * deriv G (Notation.logx x e)))
          Filter.atTop (nhds 0)

/-- **`Gap212.Sieve.MertensWeightedGramLimit` is equivalent to the defect statement.** The
predicted summand's normalized weighted sum converges to `∫_0^∞F'G'`
(`Gap212.Sieve.tendsto_mertensKappa_mul_weightedSum` at `H = F'G'`, continuous and vanishing on
`[β,∞)` by `Gap212.Sieve.deriv_eq_zero_of_eventually_zero`); subtracting it gives one direction and
adding it back the other. -/
theorem mertensWeightedGramLimit_iff_gramRatioDefectVanishes :
    MertensWeightedGramLimit ↔ GramRatioDefectVanishes := by
  have hmeas : ∀ (F G : ℝ → ℝ), ContDiff ℝ 1 F → ContDiff ℝ 1 G → ∀ β : ℝ, 0 < β →
      (∀ t, β ≤ t → F t = 0) → ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
      Tendsto (fun x : ℝ ↦ mertensKappa x *
          ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
            ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
              (deriv F (Notation.logx x e) * deriv G (Notation.logx x e)))
        atTop (nhds (∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t)) := by
    intro F G hF hG β hβ hFv B hB
    have hcont : Continuous fun t : ℝ ↦ deriv F t * deriv G t :=
      hF.continuous_deriv_one.mul hG.continuous_deriv_one
    refine tendsto_mertensKappa_mul_weightedSum hcont hβ (fun t ht ↦ ?_) B hB
    rw [deriv_eq_zero_of_eventually_zero hF hFv t ht, zero_mul]
  -- `hmeas` is stated for `C¹` profiles; the `C^∞` profiles here are `C¹`.
  have hdown : ∀ H : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) H → ContDiff ℝ 1 H :=
    fun _ hH ↦ hH.of_le (by exact_mod_cast le_top)
  refine ⟨fun h F G hF hFc hG hGc β hβ hFv hGv B hB ↦ ?_,
    fun h F G hF hFc hG hGc β hβ hFv hGv B hB ↦ ?_⟩
  · have h1 := h F G hF hFc hG hGc β hβ hFv hGv B hB
    simp only [mertensKappa_eq] at h1
    simpa only [mertensKappa_mul_sum_sub, sub_self] using
      h1.sub (hmeas F G (hdown F hF) (hdown G hG) β hβ hFv B hB)
  · have h1 := h F G hF hFc hG hGc β hβ hFv hGv B hB
    simp only [mertensKappa_mul_sum_sub] at h1
    simpa only [zero_add, sub_add_cancel, mertensKappa] using
      h1.add (hmeas F G (hdown F hF) (hdown G hG) β hβ hFv B hB)

/-- **`Gap212.Sieve.LcmGramSumLimitOfSupport` is equivalent to the defect statement.** The
composite of `Gap212.Sieve.lcmGramSumLimitOfSupport_iff` and
`Gap212.Sieve.mertensWeightedGramLimit_iff_gramRatioDefectVanishes`. -/
theorem lcmGramSumLimitOfSupport_iff_gramRatioDefectVanishes :
    LcmGramSumLimitOfSupport ↔ GramRatioDefectVanishes :=
  lcmGramSumLimitOfSupport_iff.trans mertensWeightedGramLimit_iff_gramRatioDefectVanishes

/-- **The weighted-`ℓ¹` form of the defect statement**: the absolute defect has vanishing
normalized weighted sum,

  `κ_x·∑_{e≤B,(e,W)=1}(μ²(e)/φ(e))·|r_F(e)r_G(e) − F'(log_x e)G'(log_x e)| ⟶ 0`,

for `C¹` profiles. It implies `Gap212.Sieve.LcmGramSumLimitOfSupport`
(`Gap212.Sieve.lcmGramSumLimitOfSupport_of_normalizedInnerRatioL1`) and is stronger than the
equivalent `Gap212.Sieve.GramRatioDefectVanishes`, since it forbids cancellation between the
`e`'s. -/
def NormalizedInnerRatioL1 : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F → ContDiff ℝ 1 G → HasCompactSupport G →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) → (∀ t, β ≤ t → G t = 0) →
      ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
        Filter.Tendsto (fun x : ℝ ↦ mertensKappa x *
            ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
              ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
                |innerRecipRatio (W x) e F x (B x) * innerRecipRatio (W x) e G x (B x)
                  - deriv F (Notation.logx x e) * deriv G (Notation.logx x e)|)
          Filter.atTop (nhds 0)

/-- The `ℓ¹` form implies the defect form: a sum is at most the sum of the absolute values. -/
theorem gramRatioDefectVanishes_of_normalizedInnerRatioL1 (h : NormalizedInnerRatioL1) :
    GramRatioDefectVanishes := by
  intro F G hF hFc hG hGc β hβ hFv hGv B hB
  replace hF : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast le_top)
  replace hG : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast le_top)
  refine squeeze_zero_norm' ?_ (h F G hF hFc hG hGc β hβ hFv hGv B hB)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mertensKappa_nonneg hx)]
  refine mul_le_mul_of_nonneg_left ?_ (mertensKappa_nonneg hx)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun e _ ↦ ?_)
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (μ e : ℝ) ^ 2 / (e.totient : ℝ))]

/-- **`Gap212.Sieve.LcmGramSumLimitOfSupport` from the weighted-`ℓ¹` form.** -/
theorem lcmGramSumLimitOfSupport_of_normalizedInnerRatioL1 (h : NormalizedInnerRatioL1) :
    LcmGramSumLimitOfSupport :=
  lcmGramSumLimitOfSupport_iff_gramRatioDefectVanishes.2
    (gramRatioDefectVanishes_of_normalizedInnerRatioL1 h)

end Gap212.Sieve
