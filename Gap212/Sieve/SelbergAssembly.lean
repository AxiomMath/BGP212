/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.RetreatOneLe
public import Gap212.Sieve.SelbergErrorTerm
public import Gap212.Sieve.SelbergMainTerm

/-!
# The denominator divisor sum: the assembly

The evaluation of the denominator divisor sum, assembled from four pieces. The fourth, the
sieving error, is stated here as `Gap212.Sieve.SelbergSievingError` and proved as
`Gap212.Sieve.selbergSievingError` in `Gap212.Sieve.SmoothMoebiusInner`.

## The four pieces

* **The elementary reduction** (`Gap212.Sieve.SelbergProgressionSum`). The `2k` divisor
  weights are expanded, the `n`-sum is moved inside, and what is left of each divisor pair is the
  number of block members it divides. A pair divides nothing unless its least common multiples are
  pairwise coprime and coprime to `W(x)`, and then the Chinese remainder theorem collapses the
  conditions to one class modulo `q = W(x)∏ᵢ[dᵢ,d'ᵢ]`.
* **The per-pair count** (`Gap212.Sieve.abs_card_dyadic_filter_modEq_sub_le`): that class has
  `x/q + O(1)` members, with the constant `2`.
* **The error term** (`Gap212.Sieve.card_contributing_isLittleO_calC`): the pairs contributing at
  all number `o(𝓒_x)`, so the accumulated `O(1)` is `o(𝓒_x)`.
* **The main term** (`Gap212.Sieve.tendsto_prod_pairSumRecip_of_support`): granting
  `Gap212.Sieve.LcmGramSumLimitOfSupport`, `B_x^k` times the pair sum over the **full** box of
  divisors coprime to `W(x)` tends to `∏ᵢ∫₀^∞F'ᵢG'ᵢ`. (Without the support hypothesis the Gram
  limit `Gap212.Sieve.LcmGramSumLimit` is false, by `Gap212.Sieve.not_lcmGramSumLimit`.) The
  support clause — each profile vanishes from `β` on — is supplied by the retreat hypothesis at
  `β = 1`, in `Gap212.Sieve.tendsto_boxPairSum_of_retreated`.

## The sieving error

The main term needed here is over the tuples whose least common multiples are **pairwise
coprime**; what `Gap212.Sieve.tendsto_prod_pairSumRecip` evaluates is the sum over the **full** box
of tuples coprime to `W(x)`. The difference — the tuples where two lcms share a prime — is
`Gap212.Sieve.SelbergSievingError`. It is a hypothesis of the declarations in this file and is
proved in `Gap212.Sieve.SmoothMoebiusInner` (`Gap212.Sieve.selbergSievingError`), at every `m`.

The target is `o(B_x^{-k})`, i.e. smaller than the main term, which is itself `≍(\log x)^{-k}`; a
bound taking absolute values inside any coordinate replaces that coordinate's `≍1/\log x` by
`≍(\log x)^3` and so overshoots by `(\log x)^4` per coordinate. The saving is arithmetic: a prime
shared by two lcms of a tuple coprime to `W(x)` exceeds `\log\log\log x`, and `∑_{p>z}p^{-2}\to0`.
Using it needs, for each `e`, the one-coordinate pair sum restricted to `e ∣ [d,d']` bounded by
`O(1/(e^s B_x))` **uniformly in `e`** — Möbius cancellation uniform in a growing modulus.
`Gap212.Sieve.SmoothMoebiusInner` obtains it by removing the modulus *before* the `v`-integration
of the summation by parts, so the profile is summed against the Möbius weight at the modulus-free
scale and no `\log\log x` is lost. The union over the pairs `(i,j)` and the shared divisors is
affordable, because the coprimality indicator can be Möbius-inverted rather than bounded, which
expands the restriction *exactly* into products of one-coordinate sums
(`Gap212.Sieve.sum_coprime_pairs_eq_sum_moebius`) and leaves the triangle inequality to be taken
once at the end, over the Möbius variables, where `∑_{e>z}e^{-2}≍1/z` pays for it; see
`Gap212.Sieve.SievingErrorTails`.

The statement is made for truncations `B ≥ x^β` with `β ≥ 1`: the one-coordinate estimate is fed
the profiles' support clause, which the retreat condition supplies only from `1` on, and
`Gap212.Sieve.selberg_progression_sum` below truncates at `B = ⌊2x⌋ + H` with `H` the largest
shift, i.e. at `β = 1`.

## Main results

* `Gap212.Sieve.IsRetreatedPair`: the support hypothesis on the two profile families.
* `Gap212.Sieve.boxPairSum`, `sievedPairSum`: the main-term sum over the full coprime-to-`W(x)`
  box, and its restriction to the tuples with pairwise coprime lcms.
* `Gap212.Sieve.SelbergSievingError`: the difference of those two is `o(B_x^{-k})`, for every
  truncation `B ≥ x^β` with `β ≥ 1`; proved, at every `m`, by `Gap212.Sieve.selbergSievingError`.
* `Gap212.Sieve.coeffProd_eq_zero_of_null`, `Gap212.Sieve.boxPairSum_eq_zero_of_null`: a profile
  vanishing on all of `[0,∞)` kills the box sum, which is the degenerate branch of the support
  dispatch.
* `Gap212.Sieve.tendsto_boxPairSum_of_retreated`: the full-box main term from
  `Gap212.Sieve.LcmGramSumLimitOfSupport` alone, its support clause discharged from the retreat
  hypothesis.
* `Gap212.Sieve.tendsto_sievedPairSum`: the restricted main term, granting the Gram limit and the
  sieving error.
* `Gap212.Sieve.lt_rpow_half_of_coeffProd_ne_zero`: a contributing tuple has every coordinate below
  `x^{1/2}`, whatever the truncation.
* `Gap212.Sieve.selbergSievingError_of_subsingleton`, `..._zero`: the sieving error where there is
  nothing to sieve — special cases of `Gap212.Sieve.selbergSievingError`, proved without the Möbius
  machinery.
* `Gap212.Sieve.abs_dyadic_sum_sub_main_le`: the elementary reduction and the error term in one
  inequality, with every constant explicit.
* `Gap212.Sieve.selberg_progression_sum`: the asymptotic for the denominator divisor sum.
-/

@[expose] public section

namespace Gap212.Sieve

open Asymptotics Filter Finset Gap212.Defs Gap212.GPY
open scoped ArithmeticFunction.Moebius

/-! ## The coefficient of a divisor tuple -/

/-- **The Möbius coefficient of a divisor tuple**, `∏ᵢμ(dᵢ)Fᵢ(log_x dᵢ)`: the weight the divisor
expansion of `Gap212.Sieve.prod_lambdaF_eq_sum` attaches to the tuple `d`. -/
noncomputable def coeffProd {k : ℕ} (x : ℝ) (F : Fin k → ℝ → ℝ) (d : Fin k → ℕ) : ℝ :=
  ∏ i, (μ (d i) : ℝ) * F i (Notation.logx x (d i))

/-- **A coefficient is bounded by a bound on the profiles.** `|μ| ≤ 1` and `|Fᵢ| ≤ C` give
`|∏ᵢμ(dᵢ)Fᵢ(log_x dᵢ)| ≤ C^k`. -/
theorem abs_coeffProd_le {k : ℕ} {x : ℝ} {F : Fin k → ℝ → ℝ} {C : ℝ}
    (hFC : ∀ i t, |F i t| ≤ C) (d : Fin k → ℕ) : |coeffProd x F d| ≤ C ^ k := by
  rw [coeffProd, abs_prod]
  calc _ ≤ ∏ _i : Fin k, C := Finset.prod_le_prod (fun i _ ↦ abs_nonneg _) fun i _ ↦ by
        rw [abs_mul]
        refine (mul_le_of_le_one_left (abs_nonneg _) ?_).trans (hFC _ _)
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = C ^ k := by simp

/-- `log_x d ≥ 0` for a positive integer `d` and `x > 1`. -/
private theorem logx_nat_nonneg {x : ℝ} (hx : 1 < x) {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ Notation.logx x d :=
  div_nonneg (Real.log_nonneg (by exact_mod_cast hd)) (Real.log_nonneg hx.le)

/-- A non-zero coefficient has a non-zero profile product. -/
private theorem prod_ne_zero_of_coeffProd_ne_zero {k : ℕ} {x : ℝ} {F : Fin k → ℝ → ℝ}
    {d : Fin k → ℕ} (h : coeffProd x F d ≠ 0) : (∏ i, F i (Notation.logx x (d i))) ≠ 0 :=
  right_ne_zero_of_mul (by rwa [coeffProd, Finset.prod_mul_distrib] at h)

/-! ## The support hypothesis -/

/-- **A retreated pair of profile families**: the hypothesis
`supp ∏ᵢFᵢ ⊆ R⁺_k(j,ε₀)` and `supp ∏ᵢGᵢ ⊆ R⁺_k(j',ε₀)`, read on the nonnegative orthant — which is
where the arguments `log_x dᵢ` of a tuple of divisors `dᵢ ≥ 1` of `x > 1` live.

The symmetric companion of `Gap212.GPY.IsReducedRetreat`, which states the same thing for a pair of
families with one coordinate removed and with the unprimed side additionally confined to the
marginal region. -/
def IsRetreatedPair (p : SupportParams) (k : ℕ) (j j' : Fin p.n) (ε₀ : ℝ)
    (F G : Fin k → ℝ → ℝ) : Prop :=
  ∀ t : Fin k → ℝ, (∀ i, 0 ≤ t i) →
    ((∏ i, F i (t i)) ≠ 0 → t ∈ retreatRegion p k j ε₀) ∧
    ((∏ i, G i (t i)) ≠ 0 → t ∈ retreatRegion p k j' ε₀)

/-! ## The two main-term sums -/

/-- **The main-term pair sum over the full box** of divisors up to `B` coprime to `W(x)`: the
quantity `Gap212.Sieve.tendsto_prod_pairSumRecip` evaluates. -/
noncomputable def boxPairSum {k : ℕ} (x : ℝ) (B : ℕ) (F G : Fin k → ℝ → ℝ) : ℝ :=
  ∑ d ∈ Fintype.piFinset fun _ : Fin k ↦ {d ∈ Icc 1 B | Nat.Coprime (W x) d},
    ∑ d' ∈ Fintype.piFinset fun _ : Fin k ↦ {d ∈ Icc 1 B | Nat.Coprime (W x) d},
      coeffProd x F d * coeffProd x G d' / ∏ i, ((d i).lcm (d' i) : ℝ)

/-- **The main-term pair sum needed here**: the same sum restricted to the tuples whose least
common multiples `[dᵢ,d'ᵢ]` are pairwise coprime. These are the only tuples that divide anything in
the pre-sieved class (`Gap212.Sieve.coprime_of_forall_dvd`), so this — not
`Gap212.Sieve.boxPairSum` — is what the reduction produces. -/
noncomputable def sievedPairSum {k : ℕ} (x : ℝ) (B : ℕ) (F G : Fin k → ℝ → ℝ) : ℝ :=
  ∑ d ∈ Fintype.piFinset fun _ : Fin k ↦ {d ∈ Icc 1 B | Nat.Coprime (W x) d},
    ∑ d' ∈ Fintype.piFinset fun _ : Fin k ↦ {d ∈ Icc 1 B | Nat.Coprime (W x) d},
      if ∀ i i' : Fin k, i ≠ i' → Nat.Coprime ((d i).lcm (d' i)) ((d i').lcm (d' i')) then
        coeffProd x F d * coeffProd x G d' / ∏ i, ((d i).lcm (d' i) : ℝ)
      else 0

/-- **The full-box main term, granting `Gap212.Sieve.LcmGramSumLimitOfSupport`.** This is
`Gap212.Sieve.tendsto_prod_pairSumRecip_of_support` read at `Gap212.Sieve.boxPairSum`, under the
hypothesis that each profile vanishes from `β` on; `Gap212.Sieve.tendsto_boxPairSum_of_retreated`
derives that hypothesis from the retreat condition. The profiles are `C^∞`, as
`Gap212.Sieve.LcmGramSumLimitOfSupport` asks. -/
theorem tendsto_boxPairSum (hlim : LcmGramSumLimitOfSupport) {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    {β : ℝ} (hβ : 0 < β) (hFβ : ∀ i, ∀ t, β ≤ t → F i t = 0)
    (hGβ : ∀ i, ∀ t, β ≤ t → G i t = 0)
    (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦ (((W x).totient : ℝ) / (W x : ℝ) * Real.log x) ^ k *
        boxPairSum x (B x) F G) atTop
      (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) := by
  simp only [boxPairSum, coeffProd]
  exact tendsto_prod_pairSumRecip_of_support hlim F G hF hFc hG hGc hβ hFβ hGβ B hB

/-! ## The support clause of the Gram limit holds at a retreated pair -/

/-- **A null factor kills the Möbius coefficient of every tuple in the box.** The coefficient reads
`F i₀` at `log_x (d i₀)`, which is nonnegative for `d i₀ ≥ 1` and `x > 1`, so a profile vanishing
on all of `[0,∞)` zeroes the whole product. -/
theorem coeffProd_eq_zero_of_null {k : ℕ} {F : Fin k → ℝ → ℝ} {i₀ : Fin k}
    (hnull : ∀ t : ℝ, 0 ≤ t → F i₀ t = 0) {x : ℝ} (hx : 1 < x) {d : Fin k → ℕ}
    (hd : ∀ i, 1 ≤ d i) : coeffProd x F d = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
  rw [hnull _ (logx_nat_nonneg hx (hd i₀)), mul_zero]

/-- **A null factor on either side kills the full-box pair sum.** Every tuple of the box has all
coordinates at least `1`, so `Gap212.Sieve.coeffProd_eq_zero_of_null` applies to each term. -/
theorem boxPairSum_eq_zero_of_null {k : ℕ} {F G : Fin k → ℝ → ℝ} {i₀ : Fin k}
    (hnull : (∀ t : ℝ, 0 ≤ t → F i₀ t = 0) ∨ ∀ t : ℝ, 0 ≤ t → G i₀ t = 0) {x : ℝ} (hx : 1 < x)
    (B : ℕ) : boxPairSum x B F G = 0 := by
  refine Finset.sum_eq_zero fun d hd ↦ Finset.sum_eq_zero fun d' hd' ↦ ?_
  simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_Icc] at hd hd'
  rcases hnull with h | h
  · rw [coeffProd_eq_zero_of_null h hx fun i ↦ (hd i).1.1, zero_mul, zero_div]
  · rw [coeffProd_eq_zero_of_null h hx fun i ↦ (hd' i).1.1, mul_zero, zero_div]

/-- **The full-box main term at a retreated pair, granting `Gap212.Sieve.LcmGramSumLimitOfSupport`
alone.** The same conclusion as `Gap212.Sieve.tendsto_boxPairSum` at `β = 1`, with the support
hypothesis discharged from `Gap212.Sieve.IsRetreatedPair` instead of assumed.

`Gap212.Sieve.exists_null_or_forall_eq_zero_of_one_le` splits each family: either every factor
vanishes from `1` on — the support clause at `β = 1` — or some factor vanishes on all of `[0,∞)`,
and then both sides are identically zero (`Gap212.Sieve.boxPairSum_eq_zero_of_null`,
`Gap212.Sieve.prod_integral_eq_zero_of_null_left`). The retreat condition confines every coordinate
below `1/2`. -/
theorem tendsto_boxPairSum_of_retreated (hlim : LcmGramSumLimitOfSupport) (p : SupportParams)
    {k : ℕ} {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) {j j' : Fin p.n} (F G : Fin k → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    (hsupp : IsRetreatedPair p k j j' ε₀ F G)
    (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ (1 : ℝ) ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦ (((W x).totient : ℝ) / (W x : ℝ) * Real.log x) ^ k *
        boxPairSum x (B x) F G) atTop
      (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) := by
  -- In the null cases both sides vanish identically; otherwise the Gram limit applies.
  have hnull : ∀ i₀ : Fin k, (∀ t : ℝ, 0 ≤ t → F i₀ t = 0) ∨ (∀ t : ℝ, 0 ≤ t → G i₀ t = 0) →
      Tendsto (fun x : ℝ ↦ (((W x).totient : ℝ) / (W x : ℝ) * Real.log x) ^ k *
          boxPairSum x (B x) F G) atTop
        (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) := fun i₀ h ↦ by
    rw [h.elim prod_integral_eq_zero_of_null_left prod_integral_eq_zero_of_null_right]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [boxPairSum_eq_zero_of_null h hx, mul_zero]
  obtain ⟨i₀, hnF⟩ | hF1 := exists_null_or_forall_eq_zero_of_one_le hε₀ fun t ht ↦ (hsupp t ht).1
  · exact hnull i₀ (.inl hnF)
  obtain ⟨i₀, hnG⟩ | hG1 := exists_null_or_forall_eq_zero_of_one_le hε₀ fun t ht ↦ (hsupp t ht).2
  · exact hnull i₀ (.inr hnG)
  exact tendsto_boxPairSum hlim F G hF hFc hG hGc one_pos hF1 hG1 B hB

/-! ## The sieving error -/

/-- **The sieving error.** For a retreated pair of profile families and a truncation `B ≥ x^β` with
`β ≥ 1`,

  `B_x^k·(∑_{full box} - ∑_{pairwise coprime lcms}) ⟶ 0`,  `B_x = (φ(W)/W)\log x`,

the two sums being `Gap212.Sieve.boxPairSum` and `Gap212.Sieve.sievedPairSum`. It holds at every
`m`: `Gap212.Sieve.selbergSievingError`, in `Gap212.Sieve.SmoothMoebiusInner`.

`Gap212.Sieve.tendsto_sievedPairSum` uses it: the reduction of the denominator divisor sum produces
the restricted sum, while `Gap212.Sieve.tendsto_prod_pairSumRecip` evaluates the full one, and this
is exactly the difference.

The coordinates of the full box separate because `1/∏ᵢ[dᵢ,d'ᵢ]` is a product; the
pairwise-coprimality restriction couples them. The target is `o(B_x^{-k})`, and the main term is
itself of that size, so the estimate has to keep the Möbius cancellation in **every** coordinate:
taking absolute values in one coordinate costs `(\log x)^4` against a target with no room at all.
The saving is that a prime shared between two lcms of a tuple coprime to `W(x)` exceeds
`\log\log\log x`, so its reciprocal square is summably small; exploiting it needs the
one-coordinate pair sum restricted to `e ∣ [d,d']` bounded by `O(1/(e^sB_x))` **uniformly in `e`**.
`Gap212.Sieve.SmoothMoebiusInner` obtains this by removing the modulus before the `v`-integration
of the summation by parts (`Gap212.Sieve.moebiusReciprocalBelow_eq_sum_smoothDivWeight`).

The coprimality indicator is Möbius-inverted instead of bounded, and
`Gap212.Sieve.sum_coprime_pairs_eq_sum_moebius` expands the restriction exactly into products of
one-coordinate sums, with `Gap212.Sieve.exists_threshold_abs_sub_sum_coprime_pairs_le` paying for
the resulting `∑_{e>z}e^{-2}`; see `Gap212.Sieve.SievingErrorTails`. At `k` coordinates the
expansion is in `Gap212.Sieve.PairwiseCoprimeMoebius`: the edge-by-edge accounting that pays for
two coordinates is **false from `k = 4` on** (`Gap212.Sieve.prod_incLcm_lt_prod_edges_four`), and
the bound is prime-wise, `Gap212.Sieve.sq_configLcm_dvd_prod_incLcm`.

The one-coordinate statement used carries three conditions. The exponent of `e` is
`s ∈ (1/2,1)`: the shape `O(1/(E·B_x))` is false, since two large primes whose product exceeds `B`
leave the one-coordinate sum two terms. The truncation satisfies `B ≥ x^β`: without it the
estimate is false at every exponent (`Gap212.Sieve.not_oneCoordLcmDecay`), because at `B = 1` the
box is a single point and the sum is the uncancelled `F(0)G(0)`. And the profiles vanish from `β`
on: without it the estimate is false (`Gap212.Sieve.not_oneCoordLcmDecayAtLevel`). The statement
with all three is `Gap212.Sieve.OneCoordLcmDecayAtLevelOfSupport`, proved at `s = 3/4` by
`Gap212.Sieve.oneCoordLcmDecayAtLevelOfSupport_three_quarters`; see
`Gap212.Sieve.SievingErrorReduction` and `Gap212.Sieve.OneCoordLcmSelberg`.

The range `β ≥ 1` comes from the last condition: the retreat condition supplies "each profile
vanishes from `β` on" only from `β = 1` on. -/
@[gap212 "lem_selberg_sieving_error"]
def SelbergSievingError (m : ℕ) : Prop :=
  ∀ (p : SupportParams) (ε₀ : ℝ), 0 < ε₀ → ε₀ < 1 → ∀ (j j' : Fin p.n)
      (F G : Fin (m + 1) → ℝ → ℝ),
    (∀ i, ContDiff ℝ 1 (F i)) → (∀ i, HasCompactSupport (F i)) →
    (∀ i, ContDiff ℝ 1 (G i)) → (∀ i, HasCompactSupport (G i)) →
    IsRetreatedPair p (m + 1) j j' ε₀ F G →
    ∀ β : ℝ, 1 ≤ β → ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
      Tendsto (fun x : ℝ ↦ (((W x).totient : ℝ) / (W x : ℝ) * Real.log x) ^ (m + 1) *
          (boxPairSum x (B x) F G - sievedPairSum x (B x) F G)) atTop (nhds 0)

/-! ## The truncation and the sieving error

The Gram limits `Gap212.Sieve.LcmGramSumLimit` and `Gap212.Sieve.TotientGramSumLimit` are false
because they quantify over the profiles and the truncation `B ≥ x^β` independently, so a profile
supported above `\log_xB` makes the sum vanish while the asserted target does not
(`Gap212.Sieve.not_lcmGramSumLimit`, `Gap212.Sieve.not_totientGramSumLimit`). This does not apply
to `Gap212.Sieve.SelbergSievingError`, for two reasons.

**The target is `0`, and the two sums are the same summand over nested index sets.** Any degeneracy
that kills terms kills them on *both* sides, so the difference stays `0`; the witness against a
Gram limit — a bump supported outside `[0,\log_xB]` — makes both sums identically zero here, and
`0` is what is asserted.

**The retreat hypothesis makes `B` irrelevant beyond `x^{1/2}`.**
`Gap212.Sieve.lt_rpow_half_of_coeffProd_ne_zero` below: every tuple with a non-zero coefficient has
every coordinate below `x^{1/2}`, whatever `B` is, because `Gap212.Sieve.IsRetreatedPair` confines
`\log_xdᵢ` to the retreat region and every coordinate there is below `1/2`
(`Gap212.Sieve.coord_lt_half_of_mem_retreatRegion`).

`Gap212.Sieve.selbergSievingError_zero` and `Gap212.Sieve.selbergSievingError_of_subsingleton` are
the elementary cases, independent of the Möbius argument.
-/

/-- **A retreated tuple's coordinates are below `x^{1/2}`, whatever the truncation.** A non-zero
Möbius coefficient forces `\log_xdᵢ` into the retreat region, where every coordinate is below `1/2`
(`Gap212.Sieve.coord_lt_half_of_mem_retreatRegion`).

Hence the box beyond `x^{1/2}` contributes nothing to either of the two sums
`Gap212.Sieve.SelbergSievingError` compares. -/
theorem logx_lt_half_of_coeffProd_ne_zero {p : SupportParams} {k : ℕ} {j : Fin p.n} {ε₀ : ℝ}
    (hε₀ : 0 ≤ ε₀) {F : Fin k → ℝ → ℝ}
    (hsupp : ∀ t : Fin k → ℝ, (∀ i, 0 ≤ t i) → (∏ i, F i (t i)) ≠ 0 →
      t ∈ retreatRegion p k j ε₀)
    {x : ℝ} (hx : 1 < x) {d : Fin k → ℕ} (hd : ∀ i, 1 ≤ d i) (h : coeffProd x F d ≠ 0)
    (i : Fin k) : Notation.logx x (d i) < 1 / 2 :=
  coord_lt_half_of_mem_retreatRegion hε₀
    (hsupp _ (fun i' ↦ logx_nat_nonneg hx (hd i')) (prod_ne_zero_of_coeffProd_ne_zero h)) i

/-- **The same bound in multiplicative form**: `dᵢ < x^{1/2}`. -/
theorem lt_rpow_half_of_coeffProd_ne_zero {p : SupportParams} {k : ℕ} {j : Fin p.n} {ε₀ : ℝ}
    (hε₀ : 0 ≤ ε₀) {F : Fin k → ℝ → ℝ}
    (hsupp : ∀ t : Fin k → ℝ, (∀ i, 0 ≤ t i) → (∏ i, F i (t i)) ≠ 0 →
      t ∈ retreatRegion p k j ε₀)
    {x : ℝ} (hx : 1 < x) {d : Fin k → ℕ} (hd : ∀ i, 1 ≤ d i) (h : coeffProd x F d ≠ 0)
    (i : Fin k) : (d i : ℝ) < x ^ (1 / 2 : ℝ) := by
  have hlt := logx_lt_half_of_coeffProd_ne_zero hε₀ hsupp hx hd h i
  have hx0 : 0 < x := by linarith
  rw [Notation.logx, div_lt_iff₀ (Real.log_pos hx)] at hlt
  rw [← Real.log_lt_log_iff (Nat.cast_pos.mpr (hd i)) (Real.rpow_pos_of_pos hx0 _),
    Real.log_rpow hx0]
  linarith

/-- **With one coordinate there is nothing to sieve.** The pairwise-coprimality restriction is a
condition on *distinct* coordinates, so on a subsingleton index type it is vacuous and the
restricted sum is the full one. -/
theorem sievedPairSum_eq_boxPairSum_of_subsingleton {k : ℕ} (hk : ∀ i i' : Fin k, i = i') (x : ℝ)
    (B : ℕ) (F G : Fin k → ℝ → ℝ) : sievedPairSum x B F G = boxPairSum x B F G :=
  Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    if_pos fun i i' hne ↦ absurd (hk i i') hne

/-- **The sieving error holds outright when there is only one coordinate**, both sums being equal
by `Gap212.Sieve.sievedPairSum_eq_boxPairSum_of_subsingleton`. Subsumed by
`Gap212.Sieve.selbergSievingError`, which holds at every `m`. -/
theorem selbergSievingError_of_subsingleton {m : ℕ} (hk : ∀ i i' : Fin (m + 1), i = i') :
    SelbergSievingError m := by
  intro p ε₀ _ _ j j' F G _ _ _ _ _ β _ B _
  simp [sievedPairSum_eq_boxPairSum_of_subsingleton hk]

/-- **`Gap212.Sieve.SelbergSievingError 0`**, costing nothing because there are no two distinct
coordinates to share a prime. The general case is `Gap212.Sieve.selbergSievingError`. -/
theorem selbergSievingError_zero : SelbergSievingError 0 :=
  selbergSievingError_of_subsingleton fun i i' ↦ by lia

/-- **The main term, granting the Gram limit and the sieving error.** `B_x^k` times
the pair sum over the tuples with pairwise coprime least common multiples tends to `∏ᵢ∫₀^∞F'ᵢG'ᵢ`:
the full-box limit of `Gap212.Sieve.tendsto_boxPairSum_of_retreated` minus the sieving error.

`hsieve` holds by `Gap212.Sieve.selbergSievingError`. The Gram limit is
`Gap212.Sieve.LcmGramSumLimitOfSupport`, at the truncation `β = 1`, where its support clause
follows from `hsupp`. The profiles are `C^∞` because `hgram` asks for that, while
`Gap212.Sieve.SelbergSievingError` is stated for `C¹` profiles. -/
theorem tendsto_sievedPairSum (hlim : LcmGramSumLimitOfSupport) {m : ℕ}
    (hsieve : SelbergSievingError m)
    (p : SupportParams) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) (j j' : Fin p.n)
    (F G : Fin (m + 1) → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    (hsupp : IsRetreatedPair p (m + 1) j j' ε₀ F G)
    (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ (1 : ℝ) ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦ (((W x).totient : ℝ) / (W x : ℝ) * Real.log x) ^ (m + 1) *
        sievedPairSum x (B x) F G) atTop
      (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) := by
  have h := (tendsto_boxPairSum_of_retreated hlim p hε₀.le F G hF hFc hG hGc hsupp B hB).sub
    (hsieve p ε₀ hε₀ hε₀' j j' F G (fun i ↦ (hF i).of_le (by exact_mod_cast le_top)) hFc
      (fun i ↦ (hG i).of_le (by exact_mod_cast le_top)) hGc hsupp 1 le_rfl B hB)
  rw [sub_zero] at h
  exact h.congr fun x ↦ by ring

/-! ## The elementary reduction, with every constant explicit

What is left is elementary bookkeeping: the expansion of the `2k` divisor weights, the
discarding of the tuples that divide nothing, and the replacement of each surviving count by `x/q`.
-/

/-- **The number of block members of the pre-sieved class a divisor pair divides.** This is the
factor `Gap212.Sieve.sum_prod_lambdaF_dyadic` leaves attached to each pair of divisor tuples. -/
noncomputable def pairCount {k : ℕ} (x : ℝ) (b : ℕ) (h d d' : Fin k → ℕ) : ℕ :=
  #(Finset.filter (fun n ↦ (∀ i, d i ∣ n + h i) ∧ (∀ i, d' i ∣ n + h i))
      {n ∈ dyadic x | n % W x = b % W x})

/-- **A divisor pair whose lcms are not pairwise coprime, or not coprime to `W(x)`, divides nothing
in the pre-sieved class.** "A tuple contributes only if the `[dᵢ,d'ᵢ]` are pairwise coprime and
coprime to `W`", contrapositively; `Gap212.Sieve.coprime_of_forall_dvd` is the content
and this is the count form. -/
theorem pairCount_eq_zero_of_not_sieved {k : ℕ} {x : ℝ} {b : ℕ} {h : Fin k → ℕ}
    (hmono : StrictMono h)
    (hD : ∀ q : ℕ, q.Prime → q ≤ (Finset.image h Finset.univ).diameter → q ∣ W x)
    (hb : IsPreSieved b (W x) h) {d d' : Fin k → ℕ}
    (hns : ¬ ((∀ i, Nat.Coprime (W x) (d i)) ∧ (∀ i, Nat.Coprime (W x) (d' i)) ∧
      ∀ i i' : Fin k, i ≠ i' → Nat.Coprime ((d i).lcm (d' i)) ((d i').lcm (d' i')))) :
    pairCount x b h d d' = 0 := by
  rw [pairCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro n hn
  simp only [Finset.mem_filter] at hn
  obtain ⟨hpw, hcopW⟩ :=
    coprime_of_forall_dvd hmono hD hb hn.1.2 (forall_dvd_iff_forall_lcm_dvd.mp hn.2)
  exact hns ⟨fun i ↦ (hcopW i).coprime_dvd_right (Nat.dvd_lcm_left _ _),
    fun i ↦ (hcopW i).coprime_dvd_right (Nat.dvd_lcm_right _ _), hpw⟩

/-- **The two-sided count of one divisor pair.** At a pair whose least common multiples are
pairwise coprime and coprime to `W(x)`, the number of block members of the pre-sieved class that
the pair divides is `x/q + O(1)` with `q = W(x)∏ᵢ[dᵢ,d'ᵢ]` and the constant `2`.

The Chinese remainder step is `Gap212.Sieve.exists_crt_class`; the count of one class in the block
is `Gap212.Sieve.abs_card_dyadic_filter_modEq_sub_le`. This is the two-sided companion of
`Gap212.Sieve.card_pair_le`, which bounds the same count above. -/
theorem abs_pairCount_sub_le {k : ℕ} {x : ℝ} (hx : 1 ≤ x) {b : ℕ} (h : Fin k → ℕ)
    {d d' : Fin k → ℕ} (hd : ∀ i, 0 < d i) (hd' : ∀ i, 0 < d' i)
    (hcopW : ∀ i, Nat.Coprime (W x) ((d i).lcm (d' i)))
    (hpw : ∀ i i' : Fin k, i ≠ i' → Nat.Coprime ((d i).lcm (d' i)) ((d i').lcm (d' i'))) :
    |(pairCount x b h d d' : ℝ) - x / ((W x : ℝ) * ∏ i, ((d i).lcm (d' i) : ℝ))| ≤ 2 := by
  rw [pairCount]
  have hmpos : ∀ i, 0 < (d i).lcm (d' i) := fun i ↦ Nat.lcm_pos (hd i) (hd' i)
  have hqpos : 0 < W x * ∏ i, (d i).lcm (d' i) :=
    Nat.mul_pos (primorial_pos _) (Finset.prod_pos fun i _ ↦ hmpos i)
  obtain ⟨a, ha⟩ := exists_crt_class (W := W x) (b := b) h hmpos hcopW hpw
  have hset : Finset.filter (fun n ↦ (∀ i, d i ∣ n + h i) ∧ (∀ i, d' i ∣ n + h i))
      {n ∈ dyadic x | n % W x = b % W x}
        = {n ∈ dyadic x | n ≡ a [MOD W x * ∏ i, (d i).lcm (d' i)]} := by
    ext n
    simp only [Finset.mem_filter, and_assoc, forall_dvd_iff_forall_lcm_dvd]
    exact and_congr_right fun _ ↦ ha n
  rw [hset]
  exact_mod_cast abs_card_dyadic_filter_modEq_sub_le hx hqpos

open Classical in
/-- **The tuples that contribute**: those in the box whose Möbius coefficient is non-zero. The
error term of `Gap212.Sieve.card_contributing_isLittleO_calC` counts pairs of these. -/
noncomputable def contribBox {k : ℕ} (x : ℝ) (B : ℕ) (F : Fin k → ℝ → ℝ) : Finset (Fin k → ℕ) :=
  {d ∈ Fintype.piFinset fun _ : Fin k ↦ Icc 1 B | coeffProd x F d ≠ 0}

/-- **The expansion, in the notation of `Gap212.Sieve.coeffProd` and `Gap212.Sieve.pairCount`.**
`Gap212.Sieve.sum_prod_lambdaF_dyadic` verbatim, with the two abbreviations folded in. -/
theorem sum_prod_lambdaF_dyadic_coeff {k : ℕ} {x : ℝ} (hx : 0 < x) (b H : ℕ) (h : Fin k → ℕ)
    (hH : ∀ i, h i ≤ H) (F G : Fin k → ℝ → ℝ) :
    (∑ n ∈ dyadic x with n % W x = b % W x,
        ∏ i, lambdaF (F i) x (n + h i) * lambdaF (G i) x (n + h i))
      = ∑ d ∈ Fintype.piFinset fun _ : Fin k ↦ Icc 1 (⌊2 * x⌋₊ + H),
          ∑ d' ∈ Fintype.piFinset fun _ : Fin k ↦ Icc 1 (⌊2 * x⌋₊ + H),
            coeffProd x F d * coeffProd x G d' * (pairCount x b h d d' : ℝ) :=
  sum_prod_lambdaF_dyadic hx b H h hH F G

/-- **The elementary reduction, as one inequality.** The weighted sum over the block differs from
`(x/W(x))` times the restricted main-term sum by at most `2C^{2k}` times the number of *pairs* of
contributing tuples:

  `|∑_{x≤n≤2x, n≡b(W)}∏ᵢλ_{Fᵢ}(n+hᵢ)λ_{Gᵢ}(n+hᵢ) - (x/W)·∑_{sieved}| ≤ 2C^{2k}·#T_F·#T_G`.

Three of the five steps, with nothing left implicit. The `2k` weights are expanded and
the `n`-sum moved inside (`Gap212.Sieve.sum_prod_lambdaF_dyadic`); the tuples not coprime to `W(x)`
and those with a shared prime among their lcms divide nothing
(`Gap212.Sieve.pairCount_eq_zero_of_not_sieved`), so dropping them changes neither side; and each
surviving count is `x/q + O(1)` with constant `2` (`Gap212.Sieve.abs_pairCount_sub_le`). Only the
pairs with a non-zero coefficient survive the estimate, and those are exactly the pairs
`Gap212.Sieve.card_contributing_isLittleO_calC` counts. -/
theorem abs_dyadic_sum_sub_main_le {m : ℕ} {x : ℝ} (hx : 1 < x) {b H : ℕ} {h : Fin (m + 1) → ℕ}
    (hmono : StrictMono h) (hH : ∀ i, h i ≤ H)
    (hD : ∀ q : ℕ, q.Prime → q ≤ (Finset.image h Finset.univ).diameter → q ∣ W x)
    (hb : IsPreSieved b (W x) h) (F G : Fin (m + 1) → ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hFC : ∀ i t, |F i t| ≤ C) (hGC : ∀ i t, |G i t| ≤ C) :
    |(∑ n ∈ dyadic x with n % W x = b % W x,
          ∏ i, lambdaF (F i) x (n + h i) * lambdaF (G i) x (n + h i))
        - x / (W x : ℝ) * sievedPairSum x (⌊2 * x⌋₊ + H) F G|
      ≤ 2 * (C ^ (m + 1) * C ^ (m + 1)) *
          ((#(contribBox x (⌊2 * x⌋₊ + H) F) : ℝ) *
            (#(contribBox x (⌊2 * x⌋₊ + H) G) : ℝ)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  set B := ⌊2 * x⌋₊ + H
  set box : Finset (Fin (m + 1) → ℕ) :=
    Fintype.piFinset fun _ : Fin (m + 1) ↦ Icc 1 B with hboxdef
  set boxW : Finset (Fin (m + 1) → ℕ) :=
    Fintype.piFinset fun _ : Fin (m + 1) ↦ {d ∈ Icc 1 B | Nat.Coprime (W x) d} with hboxWdef
  -- The pairwise-coprimality predicate, and the per-pair term of the difference.
  set pw : (Fin (m + 1) → ℕ) → (Fin (m + 1) → ℕ) → Prop := fun d d' ↦
    ∀ i i' : Fin (m + 1), i ≠ i' → Nat.Coprime ((d i).lcm (d' i)) ((d i').lcm (d' i'))
  set T : (Fin (m + 1) → ℕ) → (Fin (m + 1) → ℕ) → ℝ := fun d d' ↦
    coeffProd x F d * coeffProd x G d' * (pairCount x b h d d' : ℝ) -
      (if pw d d' then coeffProd x F d * coeffProd x G d' *
        (x / ((W x : ℝ) * ∏ i, ((d i).lcm (d' i) : ℝ))) else 0) with hTdef
  -- `boxW ⊆ box`, and membership facts.
  have hmemboxW : ∀ d : Fin (m + 1) → ℕ,
      d ∈ boxW ↔ ∀ i, (1 ≤ d i ∧ d i ≤ B) ∧ Nat.Coprime (W x) (d i) := fun d ↦ by
    simp [boxW, Fintype.mem_piFinset]
  have hmembox : ∀ d : Fin (m + 1) → ℕ, d ∈ box ↔ ∀ i, 1 ≤ d i ∧ d i ≤ B := fun d ↦ by
    simp [box, Fintype.mem_piFinset]
  have hsub : boxW ⊆ box := Fintype.piFinset_subset _ _ fun _ ↦ Finset.filter_subset _ _
  -- Step one: the expansion, restricted to the tuples coprime to `W(x)`.
  have hexp : (∑ n ∈ dyadic x with n % W x = b % W x,
        ∏ i, lambdaF (F i) x (n + h i) * lambdaF (G i) x (n + h i))
      = ∑ d ∈ boxW, ∑ d' ∈ boxW,
          coeffProd x F d * coeffProd x G d' * (pairCount x b h d d' : ℝ) := by
    rw [sum_prod_lambdaF_dyadic_coeff hx0 b H h hH F G, ← hboxdef, ← Finset.sum_product',
      ← Finset.sum_product']
    refine (Finset.sum_subset (Finset.product_subset_product hsub hsub) fun p hp hpW ↦ ?_).symm
    rw [Finset.mem_product] at hp hpW
    rw [pairCount_eq_zero_of_not_sieved hmono hD hb fun hg ↦ hpW
      ⟨(hmemboxW _).mpr fun i ↦ ⟨(hmembox _).mp hp.1 i, hg.1 i⟩,
        (hmemboxW _).mpr fun i ↦ ⟨(hmembox _).mp hp.2 i, hg.2.1 i⟩⟩, Nat.cast_zero, mul_zero]
  -- Step two: the main term, written over the same range.
  have hmain : x / (W x : ℝ) * sievedPairSum x B F G
      = ∑ d ∈ boxW, ∑ d' ∈ boxW, if pw d d' then coeffProd x F d * coeffProd x G d' *
          (x / ((W x : ℝ) * ∏ i, ((d i).lcm (d' i) : ℝ))) else 0 := by
    simp_rw [sievedPairSum, ← hboxWdef, Finset.mul_sum, mul_ite, mul_zero]
    exact Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun d' _ ↦
      if_congr Iff.rfl (by ring) rfl
  -- The difference is the sum of the per-pair terms.
  have hdiff : (∑ n ∈ dyadic x with n % W x = b % W x,
        ∏ i, lambdaF (F i) x (n + h i) * lambdaF (G i) x (n + h i))
        - x / (W x : ℝ) * sievedPairSum x B F G
      = ∑ d ∈ boxW, ∑ d' ∈ boxW, T d d' := by
    rw [hexp, hmain, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ ↦ (Finset.sum_sub_distrib _ _).symm
  -- Each per-pair term is bounded by `2C^{2k}`, and vanishes off the contributing pairs.
  have hTbound : ∀ d ∈ boxW, ∀ d' ∈ boxW, |T d d'| ≤ 2 * (C ^ (m + 1) * C ^ (m + 1)) := by
    intro d hd d' hd'
    have hdpos : ∀ i, 0 < d i := fun i ↦ ((hmemboxW d).mp hd i).1.1
    have hd'pos : ∀ i, 0 < d' i := fun i ↦ ((hmemboxW d').mp hd' i).1.1
    have hFb := abs_coeffProd_le (x := x) (F := F) hFC d
    have hGb := abs_coeffProd_le (x := x) (F := G) hGC d'
    by_cases hp : pw d d'
    · have hcop : ∀ i, Nat.Coprime (W x) ((d i).lcm (d' i)) := fun i ↦
        Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul _ _)
          (Nat.Coprime.mul_right ((hmemboxW d).mp hd i).2 ((hmemboxW d').mp hd' i).2)
      have hcount := abs_pairCount_sub_le (b := b) hx.le h hdpos hd'pos hcop hp
      have hTeq : T d d' = coeffProd x F d * coeffProd x G d' *
          ((pairCount x b h d d' : ℝ) - x / ((W x : ℝ) * ∏ i, ((d i).lcm (d' i) : ℝ))) := by
        simp only [hTdef, if_pos hp]
        ring
      rw [hTeq, abs_mul, abs_mul, mul_comm 2]
      exact mul_le_mul (mul_le_mul hFb hGb (abs_nonneg _) (pow_nonneg hC _)) hcount (abs_nonneg _)
        (by positivity)
    · have hzero : pairCount x b h d d' = 0 :=
        pairCount_eq_zero_of_not_sieved hmono hD hb fun hgood ↦ hp hgood.2.2
      rw [show T d d' = 0 by simp [hTdef, hp, hzero], abs_zero]
      positivity
  -- Restrict to the contributing pairs and count them.
  rw [hdiff, ← Finset.sum_product', ← Finset.sum_filter_ne_zero]
  have hS : {p ∈ boxW ×ˢ boxW | T p.1 p.2 ≠ 0} ⊆ contribBox x B F ×ˢ contribBox x B G :=
    fun p hp ↦ by
      simp only [contribBox, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hsub hp.1.1, fun h ↦ hp.2 (by simp [hTdef, h])⟩,
        hsub hp.1.2, fun h ↦ hp.2 (by simp [hTdef, h])⟩
  calc _ ≤ ∑ p ∈ boxW ×ˢ boxW with T p.1 p.2 ≠ 0, |T p.1 p.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ #{p ∈ boxW ×ˢ boxW | T p.1 p.2 ≠ 0} • (2 * (C ^ (m + 1) * C ^ (m + 1))) :=
      Finset.sum_le_card_nsmul _ _ _ fun p hp ↦ by
        simp only [Finset.mem_filter, Finset.mem_product] at hp
        exact hTbound _ hp.1.1 _ hp.1.2
    _ ≤ _ := by
      rw [nsmul_eq_mul, mul_comm]
      gcongr
      exact_mod_cast (Finset.card_le_card hS).trans_eq (Finset.card_product _ _)

/-! ## The normalization -/

/-- **`𝓒_x` is `x/W(x)` against `B_x^{-k}`.** `calC m x·B_x^{m+1} = x/W(x)` with
`B_x = (φ(W)/W)\log x`: the identity that turns the main term `(x/W)∑` into `𝓒_x` times the
normalized sum the Gram-sum limit evaluates, i.e.
`(x/W)·B_x^{-k}(∏ᵢ∫F'ᵢG'ᵢ + o(1)) = (∏ᵢ∫F'ᵢG'ᵢ + o(1))𝓒_x`. -/
theorem calC_mul_pow_normalization {x : ℝ} (hx : 1 < x) (m : ℕ) :
    calC m x * (((W x).totient : ℝ) / (W x : ℝ) * Real.log x) ^ (m + 1) = x / (W x : ℝ) := by
  have hW : (0 : ℝ) < W x := by exact_mod_cast primorial_pos _
  have hφ : (0 : ℝ) < (W x).totient := by exact_mod_cast Nat.totient_pos.mpr (primorial_pos _)
  have hL := Real.log_pos hx
  rw [calC, mul_pow, div_pow]
  field_simp
  ring

/-! ## The denominator divisor sum -/

/-- **The denominator divisor sum.** For a support datum `p`, `ε₀ ∈ (0,1)`, bands `j, j'`, a
strictly increasing shift tuple `h`, and profile families `Fᵢ, Gᵢ` of class `C¹` with compact
support whose products are supported in the two retreat regions,

  `∑_{x≤n≤2x, n≡b (W(x))}∏ᵢλ_{Fᵢ}(n+hᵢ)λ_{Gᵢ}(n+hᵢ) = (∏ᵢ∫₀^∞F'ᵢG'ᵢ + o(1))·𝓒_x`,

uniformly over the pre-sieved residues `b`, which sits inside the `∃ X`, as in
`Gap212.Sieve.NuDenominator`.

The `ε`-form is the `+o(1)`, and `𝓒_x` is `Gap212.GPY.calC`, which
`Gap212.Sieve.calC_eq_scale_succ` identifies with `Gap212.Sieve.scale (m+1)` for the consumers
stated there.

**The two hypotheses.** `Gap212.Sieve.LcmGramSumLimitOfSupport` follows from
`Gap212.Sieve.polymath41Recip` by `Gap212.Sieve.lcmGramSumLimitOfSupport_iff_polymath41Recip`, and
`Gap212.Sieve.SelbergSievingError` is `Gap212.Sieve.selbergSievingError`;
`Gap212.Sieve.nuDenominator_of_lcmGramSumLimitOfSupport` is the same route with the latter
discharged. The support clause of the Gram limit — each profile vanishes from `β` on — follows
from the retreat hypothesis `hsupp`, which confines every coordinate of a point where `∏ᵢFᵢ` or
`∏ᵢGᵢ` is non-zero below `1/2` (`Gap212.Sieve.coord_lt_half_of_mem_retreatRegion`): at `β = 1` the
clause holds unless some factor vanishes on all of `[0,∞)`, in which case both sides are
identically zero (`Gap212.Sieve.tendsto_boxPairSum_of_retreated`).

The other ingredients:

* the expansion and the interchange, `Gap212.Sieve.sum_prod_lambdaF_dyadic`;
* that only the tuples with pairwise coprime lcms coprime to `W(x)` contribute,
  `Gap212.Sieve.coprime_of_forall_dvd` through `Gap212.Sieve.pairCount_eq_zero_of_not_sieved`;
* the Chinese remainder collapse and the count of one class, `Gap212.Sieve.abs_pairCount_sub_le`;
* the error term, `Gap212.Sieve.card_contributing_isLittleO_calC` against
  `Gap212.Sieve.calC_lower_bound`;
* the main term, `Gap212.Sieve.tendsto_prod_pairSumRecip_of_support`, and the normalization
  `Gap212.Sieve.calC_mul_pow_normalization`.

Admissibility of `ℋ` is not among the hypotheses. What the reduction uses of the tuple is that it
is strictly increasing and that every prime up to its diameter divides `W(x)` — the second holds
for all large `x` by `Gap212.Sieve.eventually_dvd_W_of_prime_le`, and is supplied inside the proof.

The truncation is `B = ⌊2x⌋ + H` with `H` the largest shift, which is every divisor any `n + hᵢ` in
the block can have; so no divisor is lost and the hypotheses are used at `β = 1`. -/
@[gap212 "lem_selberg_progression_sum"]
theorem selberg_progression_sum (hgram : LcmGramSumLimitOfSupport) {m : ℕ}
    (hsieve : SelbergSievingError m) (p : SupportParams) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1)
    (j j' : Fin p.n) {h : Fin (m + 1) → ℕ} (hmono : StrictMono h) (F G : Fin (m + 1) → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    (hsupp : IsRetreatedPair p (m + 1) j j' ε₀ F G) :
    ∀ η > (0 : ℝ), ∃ X : ℝ, ∀ x > X, ∀ b : ℕ, IsPreSieved b (W x) h →
      |(∑ n ∈ dyadic x with n % W x = b % W x,
            ∏ i, lambdaF (F i) x (n + h i) * lambdaF (G i) x (n + h i)) -
          (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t) * calC m x|
        ≤ η * calC m x := by
  -- The truncation: every divisor of a shift of a block member is at most `⌊2x⌋ + H`.
  set H := Finset.univ.sup h
  have hH : ∀ i, h i ≤ H := fun i ↦ Finset.le_sup (Finset.mem_univ i)
  set B : ℝ → ℕ := fun y ↦ ⌊2 * y⌋₊ + H with hBdef
  have hB : ∀ᶠ y : ℝ in atTop, y ^ (1 : ℝ) ≤ (B y : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy1
    simp only [Real.rpow_one, hBdef, Nat.cast_add]
    linarith [Nat.sub_one_lt_floor (2 * y), Nat.cast_nonneg (α := ℝ) H]
  -- The restricted main term, granting the two hypotheses.
  have hlim := tendsto_sievedPairSum hgram hsieve p hε₀ hε₀' j j' F G hF hFc hG hGc hsupp B hB
  set L := ∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t
  -- A single bound for all `2k` profiles.
  obtain ⟨C, hC0, hFC, hGC⟩ : ∃ C, 0 ≤ C ∧ (∀ i t, |F i t| ≤ C) ∧ ∀ i t, |G i t| ≤ C := by
    choose cF hcF using fun i ↦ (hFc i).exists_bound_of_continuous (hF i).continuous
    choose cG hcG using fun i ↦ (hGc i).exists_bound_of_continuous (hG i).continuous
    have hsF : (0 : ℝ) ≤ ∑ i, |cF i| := by positivity
    have hsG : (0 : ℝ) ≤ ∑ i, |cG i| := by positivity
    refine ⟨(∑ i, |cF i|) + ∑ i, |cG i|, by positivity, fun i t ↦ ?_, fun i t ↦ ?_⟩
    · linarith [(Real.norm_eq_abs _).symm.trans_le (hcF i t), le_abs_self (cF i),
        Finset.single_le_sum (fun i _ ↦ abs_nonneg (cF i)) (Finset.mem_univ i)]
    · linarith [(Real.norm_eq_abs _).symm.trans_le (hcG i t), le_abs_self (cG i),
        Finset.single_le_sum (fun i _ ↦ abs_nonneg (cG i)) (Finset.mem_univ i)]
  set K := 2 * (C ^ (m + 1) * C ^ (m + 1)) with hKdef
  have hK0 : 0 ≤ K := by positivity
  -- The error term: the pairs of contributing tuples are `o(𝓒_x)`.
  have herr : (fun y : ℝ ↦ (#(contribBox y (B y) F ×ˢ contribBox y (B y) G) : ℝ))
      =o[atTop] fun y : ℝ ↦ calC m y := by
    refine card_contributing_isLittleO_calC p m hε₀ hε₀' j j'
      (fun y ↦ contribBox y (B y) F ×ˢ contribBox y (B y) G) ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy1 dd hdd
    simp only [Finset.mem_product, contribBox, Finset.mem_filter, Fintype.mem_piFinset,
      Finset.mem_Icc] at hdd
    obtain ⟨⟨hd1, hc1⟩, hd2, hc2⟩ := hdd
    exact ⟨fun i ↦ (hd1 i).1, fun i ↦ (hd2 i).1,
      (hsupp _ fun i ↦ logx_nat_nonneg hy1 (hd1 i).1).1 (prod_ne_zero_of_coeffProd_ne_zero hc1),
      (hsupp _ fun i ↦ logx_nat_nonneg hy1 (hd2 i).1).2 (prod_ne_zero_of_coeffProd_ne_zero hc2)⟩
  -- The `ε`-form.
  intro η hη
  have hmainev : ∀ᶠ y : ℝ in atTop,
      |(((W y).totient : ℝ) / (W y : ℝ) * Real.log y) ^ (m + 1) *
        sievedPairSum y (B y) F G - L| ≤ η / 2 :=
    (Metric.tendsto_nhds.mp hlim (η / 2) (half_pos hη)).mono fun _ hy ↦ hy.le
  have herrev : ∀ᶠ y : ℝ in atTop,
      K * ((#(contribBox y (B y) F) : ℝ) * (#(contribBox y (B y) G) : ℝ)) ≤ η / 2 * calC m y := by
    have hc : (0 : ℝ) < η / (2 * (K + 1)) := by positivity
    filter_upwards [herr.bound hc, calC_lower_bound m] with y hy hlow
    have hcalC : 0 ≤ calC m y := hlow.2.le.trans hlow.1
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hcalC,
      Finset.card_product, Nat.cast_mul] at hy
    have hfrac : K * (η / (2 * (K + 1))) ≤ η / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
      nlinarith
    calc _ ≤ K * (η / (2 * (K + 1)) * calC m y) := mul_le_mul_of_nonneg_left hy hK0
      _ ≤ η / 2 * calC m y := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hfrac hcalC
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hmainev.and (herrev.and
    ((eventually_gt_atTop (1 : ℝ)).and ((calC_lower_bound m).and
      (eventually_dvd_W_of_prime_le (Finset.image h Finset.univ).diameter)))))
  refine ⟨X, fun y hy b hb ↦ ?_⟩
  obtain ⟨hmy, herry, hy1, hlow, hDy⟩ := hX y hy.le
  have hcalC : 0 ≤ calC m y := hlow.2.le.trans hlow.1
  -- The reduction, and the normalization.
  have hred := abs_dyadic_sum_sub_main_le (x := y) hy1 hmono hH hDy hb F G hC0 hFC hGC
  rw [← hKdef] at hred
  have hsecond : |y / (W y : ℝ) * sievedPairSum y (B y) F G - L * calC m y|
      ≤ η / 2 * calC m y := by
    rw [← calC_mul_pow_normalization hy1 m, mul_assoc, mul_comm L, ← mul_sub, abs_mul,
      abs_of_nonneg hcalC, mul_comm (calC m y)]
    exact mul_le_mul_of_nonneg_right hmy hcalC
  refine (abs_sub_le _ (y / (W y : ℝ) * sievedPairSum y (B y) F G) _).trans ?_
  linarith [hred.trans herry]

end Gap212.Sieve
