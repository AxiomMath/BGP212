/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.OneCoordLcmRefutation
public import Gap212.Sieve.MertensMoebiusSq

/-!
# Selberg diagonalisation of the one-coordinate estimate for supported profiles

`Gap212.Sieve.OneCoordLcmDecayAtLevelOfSupport` has no slack: the one-coordinate pair sum is
`≍1/B_x` already at `e = 1`, the diagonal `d = d'` alone is `≍B_x`, and the absolute pair sum is
`≍B_x^3`. So no term-by-term bound can prove it. What *can*: the Selberg change of variables
`Gap212.Sieve.sum_pairs_div_lcm_eq_sum_totient_mul`, which replaces the pair sum by

  `∑_{r ≤ B} φ(r)·y_r·y'_r`,  `y_r = ∑_{d ∈ [1,B], (d,W)=1, r ∣ d} μ(d)F(\log_xd)/d`,

after which *absolute values are no longer lossy*: the whole cancellation of the original sum is
carried by the single one-variable quantity `y_r`, and the two-variable estimate follows from a
pointwise bound on it. This file proves that implication at `e = 1`.

## The one-variable input

`Gap212.Sieve.SmoothMoebiusInnerBound` asks exactly

  `|y_r| ≤ C·(W/φ(W))/(φ(r)\log x)`,  uniformly in `r ≥ 1` and in the truncation `B ≥ x^β`.

Its shape is that of the main term. Writing `d = rm` and `u = \log_xr`,
`y_r = (μ(r)/r)∑_{(m,rW)=1}μ(m)F(u + \log_xm)/m`, whose main term is
`(μ(r)/r)(rW/φ(rW))(-F'(u))/\log x = μ(r)(W/φ(W))(-F'(u))/(φ(r)\log x)` — the asserted bound with
`C = \|F'\|_∞`, attained at `r = 1`. Three checks:
at `r = 1` it is the classical smoothed Möbius bound `≍1/\log x` (times `W/φ(W)`, the local
correction of the coprimality class); at `r > x^β` the left side is *zero*, since the support
clause kills every `d ≥ x^β`; and at `r ∈ (x^β/2, x^β)` the left side is the single term
`|F(\log_xr)|/r ≤ \|F'\|_∞\log2/(r\log x)`, which the right side dominates because `φ(r) ≤ r`. The
denominator is `φ(r)`, not `r`: `r/φ(r)` is unbounded on the moduli coprime to `W(x)`, and it is
`φ(r)` that makes `∑_rφ(r)y_r^2` come out at `(W/φ(W))/\log x` against
`Gap212.Sieve.sum_moebiusSq_div_totient_coprime`.

## Main results

`Gap212.Sieve.oneCoordLcmDecayAtLevelOfSupport_of_smoothMoebiusInnerBound`:
`Gap212.Sieve.OneCoordLcmDecayAtLevelOfSupport (3/4)` **in full**, at every modulus `e`, from the
one-variable input alone — and `1/2 < 3/4`, so
`Gap212.Sieve.tendsto_boxPairSum_sub_sievedPairSum_of_smoothMoebiusInnerBound` chains it into the
sieving error. The one-variable bound is therefore the *only* input. (Without the support clause,
the two-variable estimate is false: `Gap212.Sieve.not_oneCoordLcmDecay`,
`Gap212.Sieve.not_oneCoordLcmDecayAtLevel`.)

**And the one-variable input is a theorem**, `Gap212.Sieve.smoothMoebiusInnerBound`
(`Gap212.Sieve.SmoothMoebiusInner`), so both implications below are unconditional:
`Gap212.Sieve.oneCoordLcmDecayAtLevelOfSupport_three_quarters` and
`Gap212.Sieve.tendsto_boxPairSum_sub_sievedPairSum` state them with no hypothesis. What the
`log log x` obstruction needs is not a sharper partial-sum bound but the smooth-number
decomposition of the coprimality-restricted Möbius weight, which removes the modulus *before* the
Abel integration.

All three hypotheses are used. The truncation `x^β ≤ B` is what the pointwise input is quantified
over; the support clause makes `y_r` vanish for `r > x^β`
(`Gap212.Sieve.innerMoebiusSum_eq_zero_of_rpow_lt`), so the modulus sum has length `β\log x` rather
than `\log B`; without it the input itself is false, at exactly the moduli `r ≍ x^β` where the
refutation lives. And `s < 1` is what pays for the divisor factors: for squarefree `e` coprime to
`W(x)` the whole `e`-dependence comes out as `128^{ω(e)}/e`, and `128^{ω(e)} ≤ e^{1/4}` only because
every prime factor of `e` exceeds `2^{28}` (`Gap212.Sieve.pow_card_primeFactors_le_self`) — at
`s = 1` there is nothing to pay with.

The modulus-restricted half runs as follows. Only squarefree `e` coprime to `W(x)` have any pair to
sum over (`Gap212.Sieve.restrictedSum_pairWeight_eq_zero_of_not_squarefree`,
`Gap212.Sieve.restrictedSum_pairWeight_eq_zero_of_not_coprime`). For those, the pairs with
`e ∣ [d,d']` are partitioned by `a = (e,d)`, which forces `e/a ∣ d'`
(`Gap212.Sieve.dvd_lcm_iff_div_gcd_dvd`); each class diagonalises, its `d`-side factor is
`∑_{c ∣ e/a}μ(c)y_{[[r,a],c]}` (`Gap212.Sieve.sum_filter_gcd_eq_sum_divisors_moebius_mul`), and
then `φ([r,m])(r,m) ≥ φ(r)φ(m)` (`Gap212.Sieve.totient_mul_totient_le_gcd_mul_totient_lcm`) turns
the pointwise input into `(r,ce)c/(φ(r)φ(e)φ(c))`, whose modulus sum is the `e = 1` Mertens sum
again (`Gap212.Sieve.sum_gcd_div_totient_le` — no estimate at a moving modulus is needed anywhere).
-/

@[expose] public section

namespace Gap212.Sieve

open Asymptotics Filter Finset Gap212.Defs Gap212.GPY
open scoped ArithmeticFunction.Moebius

/-! ## The bilinear Selberg diagonalisation -/

/-- **The Selberg diagonalisation of a pair sum, bilinear form.** For weights `l`, `l'` on a finset
`D ⊆ [1,B]`,

  `∑_{d,d' ∈ D} l(d)l'(d')/[d,d'] = ∑_{r ≤ B} φ(r)·(∑_{d ∈ D, r ∣ d} l(d)/d)(∑_{d' ∈ D, r ∣ d'}
  l'(d')/d')`.

`Gap212.Sieve.sum_pairs_div_lcm_eq_sum_totient_mul_sq` is the case `l = l'`; the proof is the same
`1/[d,d'] = (d,d')/(dd')`, `∑_{r ∣ n}φ(r) = n` and one exchange of summation. The bilinear form is
what a pair sum with *two* profiles needs, and unlike the square it is not sign-definite — but the
point of the identity is unchanged: each factor is a one-variable sum, so bounding the two factors
separately loses nothing. -/
theorem sum_pairs_div_lcm_eq_sum_totient_mul (B : ℕ) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ B) (l l' : ℕ → ℝ) :
    ∑ d ∈ D, ∑ d' ∈ D, l d * l' d' / (Nat.lcm d d' : ℝ)
      = ∑ r ∈ Icc 1 B, (r.totient : ℝ) * ((∑ d ∈ D with r ∣ d, l d / (d : ℝ))
          * ∑ d' ∈ D with r ∣ d', l' d' / (d' : ℝ)) := by
  simp_rw [Finset.sum_filter, Finset.sum_mul_sum, Finset.mul_sum, ite_zero_mul_ite_zero,
    mul_ite, mul_zero]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d' hd' ↦ ?_
  obtain ⟨hd1, hdB⟩ := hD d hd
  have hd'1 := (hD d' hd').1
  rw [← Finset.sum_filter, ← Finset.sum_mul, sum_filter_Icc_totient_eq_gcd hd1 hdB]
  have hg : (Nat.gcd d d' : ℝ) * Nat.lcm d d' = d * d' := by exact_mod_cast Nat.gcd_mul_lcm d d'
  have hl : (Nat.lcm d d' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lcm_ne_zero (by omega) (by omega))
  field_simp
  linear_combination l d * l' d' * hg

/-! ## The one-variable sum the diagonalisation produces -/

/-- **The inner Möbius sum of the Selberg diagonalisation**,
`y_r = ∑_{d ∈ [1,B], (d,W(x))=1, r ∣ d} μ(d)F(\log_xd)/d` — the one-variable quantity that carries
all of the cancellation in the one-coordinate pair sum. -/
noncomputable def innerMoebiusSum (x : ℝ) (F : ℝ → ℝ) (B r : ℕ) : ℝ :=
  ∑ d ∈ wBox x B with r ∣ d, (μ d : ℝ) * F (Notation.logx x d) / (d : ℝ)

/-- **Above the support the inner sum is empty of content.** If `F` vanishes from `β` on and
`x^β < r`, every `d` counted by `y_r` is `≥ r > x^β`, so `\log_xd > β` and the profile kills it.
This is what makes the `r`-sum of the diagonalisation finite in the only sense that matters: it
runs over `r ≤ x^β`, *not* over `r ≤ B`, so the unbounded truncation `B` contributes nothing. -/
theorem innerMoebiusSum_eq_zero_of_rpow_lt {x : ℝ} (hx : 1 < x) {β : ℝ} {F : ℝ → ℝ}
    (hFβ : ∀ t : ℝ, β ≤ t → F t = 0) {B r : ℕ} (hr : x ^ β < (r : ℝ)) :
    innerMoebiusSum x F B r = 0 := by
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  obtain ⟨hdB, hrd⟩ := Finset.mem_filter.mp hd
  have hrd' : (r : ℝ) ≤ d := by exact_mod_cast Nat.le_of_dvd (mem_wBox.mp hdB).1.1 hrd
  have h1 : Real.log (x ^ β) < Real.log d := Real.log_lt_log (by positivity) (hr.trans_le hrd')
  rw [Real.log_rpow (by linarith)] at h1
  rw [hFβ _ (by rw [Notation.logx, le_div_iff₀ (Real.log_pos hx)]; linarith), mul_zero, zero_div]

/-- **A modulus sharing a factor with `W(x)` sees nothing.** The box consists of integers coprime
to `W(x)`, so no multiple of such a modulus is in it. -/
theorem innerMoebiusSum_eq_zero_of_not_coprime {x : ℝ} {F : ℝ → ℝ} {B r : ℕ}
    (hr : ¬ Nat.Coprime (W x) r) : innerMoebiusSum x F B r = 0 := by
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  obtain ⟨hdB, hrd⟩ := Finset.mem_filter.mp hd
  exact absurd ((mem_wBox.mp hdB).2.coprime_dvd_right hrd) hr

/-- **A non-squarefree modulus sees only Möbius zeros.** Every multiple of a non-squarefree `r` is
non-squarefree, so `μ` annihilates the whole inner sum. Together with
`Gap212.Sieve.innerMoebiusSum_eq_zero_of_not_coprime` and
`Gap212.Sieve.innerMoebiusSum_eq_zero_of_rpow_lt` this restricts the diagonalisation's `r`-sum to
the squarefree moduli below `x^β` coprime to `W(x)` — exactly the support of the weight `μ²/φ` in
`Gap212.Sieve.sum_moebiusSq_div_totient_coprime`. -/
theorem innerMoebiusSum_eq_zero_of_not_squarefree {x : ℝ} {F : ℝ → ℝ} {B r : ℕ}
    (hr : ¬ Squarefree r) : innerMoebiusSum x F B r = 0 := by
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    fun h ↦ hr (h.squarefree_of_dvd (Finset.mem_filter.mp hd).2)]

/-! ## The one-variable input -/

/-- **The pointwise bound on the inner Möbius sum** — the one-variable input the Selberg
diagonalisation reduces the two-variable estimate to. For every profile vanishing from `β` on there
is a constant `C` with

  `|y_r| = |∑_{d ≤ B, (d,W)=1, r ∣ d} μ(d)F(\log_xd)/d| ≤ C·(W/φ(W))/(φ(r)\log x)`

for every large `x`, every truncation `B ≥ x^β` and every modulus `r ≥ 1`.

**Proved**: `Gap212.Sieve.smoothMoebiusInnerBound`, with `C = C₀‖F'‖_∞`.

This is the size of the main term: with `d = rm` and `u = \log_xr`,
`y_r = (μ(r)/r)∑_{(m,rW)=1}μ(m)F(u+\log_xm)/m`, and the Mellin main term of the inner sum is
`(rW/φ(rW))(-F'(u))/\log x`, i.e. `y_r ≈ μ(r)(W/φ(W))(-F'(u))/(φ(r)\log x)`. At `r = 1` the
statement *is* the classical smoothed Möbius bound and the constant is attained, so the exponent of
`\log x` cannot be improved; at `r > x^β` the left side is zero
(`Gap212.Sieve.innerMoebiusSum_eq_zero_of_rpow_lt`), which is what makes the unbounded truncation
harmless; and at `r` within a constant factor of `x^β` the left side is the single term
`|F(\log_xr)|/r`, dominated because `F` vanishes at `β` and `φ(r) ≤ r`.

**The primorial witness.** What kills a uniform
constant in `Gap212.Sieve.moebiusPartialSumDecay` is a sieve-saturated modulus — at `q` the
primorial of `⌊w⌋` the partial sum is exactly `1`, which is
`Gap212.Sieve.not_uniformMoebiusPartialSumDecay`. Here the analogue is admissible: take
`r = ∏_{v<p≤z}p` with `v = \log\log\log x`, so `r` is coprime to `W(x)` and the statement is not
vacuous at it, and `z` with `r ≍ x^β/z`, so `m = 1` is the only survivor and
`y_r = μ(r)F(\log_xr)/r` with `|F(\log_xr)| ≍ \|F'\|\log z/\log x`. The asserted bound then reads
`\|F'\|_∞\log z·(φ(r)/r) ≤ C(W/φ(W))`, and `φ(r)/r = ∏_{v<p≤z}(1-1/p) ≍ \log v/\log z`, so both
sides are `≍\log\log\log\log x` and it survives on the constant. With `r` in place of `φ(r)` the
same witness **refutes** it, by the whole factor `\log z/\log v`. -/
def SmoothMoebiusInnerBound : Prop :=
  ∀ β : ℝ, 0 < β → ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F →
    (∀ t : ℝ, β ≤ t → F t = 0) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, ∀ B r : ℕ, x ^ β ≤ (B : ℝ) → 1 ≤ r →
        |innerMoebiusSum x F B r|
          ≤ C * ((W x : ℝ) / ((W x).totient : ℝ)) / ((r.totient : ℝ) * Real.log x)

/-! ## Facts about the pre-sieving modulus -/

/-- Facts about `W(x)`, in one `eventually`: `1 ≤ φ(W) ≤ W`,
`W^2 ≤ \log x`, `τ(W) ≤ W`, `ℓ_W ≤ W`, and `1 ≤ \log x`. -/
theorem eventually_W_facts : ∀ᶠ x : ℝ in atTop,
    (1 : ℝ) ≤ Real.log x ∧ (1 : ℝ) ≤ ((W x).totient : ℝ)
      ∧ ((W x).totient : ℝ) ≤ (W x : ℝ) ∧ ((W x : ℝ)) ^ 2 ≤ Real.log x
      ∧ (#(W x).divisors : ℝ) ≤ (W x : ℝ) ∧ PrimeGaps.ellV (W x) ≤ (W x : ℝ) := by
  filter_upwards [W_sq_le_log, Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hWsq hL
  have hW0 : 0 < W x := primorial_pos _
  have hW1 : (1 : ℝ) ≤ (W x : ℝ) := by exact_mod_cast hW0
  refine ⟨hL, by exact_mod_cast Nat.totient_pos.mpr hW0, ?_, hWsq, ?_, ?_⟩
  · exact_mod_cast Nat.totient_le _
  · exact_mod_cast Nat.card_divisors_le_self _
  · exact (ellV_le_log hW0).trans (Real.log_le_self (by linarith))

/-- The Mertens sum of `μ^2/φ` over `r ≤ x^β` coprime to `W(x)`, with the `O_W(1)` of
`Gap212.Sieve.sum_moebiusSq_div_totient_coprime` discharged by the facts of
`Gap212.Sieve.eventually_W_facts`. -/
private theorem sum_moebiusSq_div_totient_le_of_W_facts {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hmert : ∀ W : ℕ, 1 ≤ W → Squarefree W → ∀ N : ℕ, 1 ≤ N →
      |(∑ e ∈ Finset.Icc 1 N with Nat.Coprime W e, ((μ e : ℝ) ^ 2 / (e.totient : ℝ)))
          - (W.totient : ℝ) / (W : ℝ)
            * (Real.log N + Real.eulerMascheroniConstant + PrimeGaps.ellV W)|
        ≤ C₀ * (1 + (#W.divisors : ℝ) / N))
    {x β : ℝ} (hx1 : 1 < x) (hβ : 0 < β) (hL1 : 1 ≤ Real.log x)
    (hφ1 : 1 ≤ ((W x).totient : ℝ)) (hφW : ((W x).totient : ℝ) ≤ W x)
    (hWsq : (W x : ℝ) ^ 2 ≤ Real.log x) (hτW : (#(W x).divisors : ℝ) ≤ W x)
    (hℓW : PrimeGaps.ellV (W x) ≤ W x) :
    ∑ r ∈ Icc 1 ⌊x ^ β⌋₊ with Nat.Coprime (W x) r, ((μ r : ℝ) ^ 2 / (r.totient : ℝ))
      ≤ (β + (2 + 2 * C₀)) * ((((W x).totient : ℝ) / (W x : ℝ)) * Real.log x) := by
  set L : ℝ := Real.log x
  set Wr : ℝ := (W x : ℝ)
  set φW : ℝ := ((W x).totient : ℝ)
  have hW0 : 0 < Wr := by linarith
  set N₀ : ℕ := ⌊x ^ β⌋₊
  have hN₀1 : 1 ≤ N₀ := Nat.le_floor (by exact_mod_cast Real.one_le_rpow hx1.le hβ.le)
  have hN₀R : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀1
  have habs := (abs_le.mp (hmert (W x) (primorial_pos _) (squarefree_primorial _) N₀ hN₀1)).2
  have hlogN₀ : Real.log N₀ ≤ β * L := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log (by linarith) (Nat.floor_le (by positivity))
  have hγ : Real.eulerMascheroniConstant ≤ 1 :=
    (Real.eulerMascheroniConstant_lt_two_thirds.trans (by norm_num)).le
  have h1 : (φW / Wr) * (Real.log N₀ + Real.eulerMascheroniConstant + PrimeGaps.ellV (W x))
      ≤ (φW / Wr) * (β * L + 1 + Wr) := by gcongr
  have h2 : C₀ * (1 + (#(W x).divisors : ℝ) / N₀) ≤ C₀ * (1 + Wr) := by
    gcongr
    exact (div_le_self (Nat.cast_nonneg _) hN₀R).trans hτW
  -- `(φ(W)/W)\log x ≥ W`, from `W^2 ≤ \log x` and `φ(W) ≥ 1`
  have hu1 : φW / Wr ≤ 1 := (div_le_one hW0).mpr hφW
  have huL : Wr ≤ (φW / Wr) * L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hW0]
    nlinarith
  nlinarith

/-! ## The reduction at `e = 1` -/

/-- **The one-coordinate estimate at `e = 1`, from the one-variable input.** This is the bound
`Gap212.Sieve.OneCoordLcmDecayAtLevelOfSupport s` asserts at `e = 1` — where `e^s = 1`, so the
statement is the target's `e = 1` instance verbatim, for every `s` at once — derived from
`Gap212.Sieve.SmoothMoebiusInnerBound` alone.

The proof is the Selberg change of variables and nothing else. By
`Gap212.Sieve.sum_pairs_div_lcm_eq_sum_totient_mul` the pair sum is `∑_{r ≤ B}φ(r)y_ry'_r`; the
moduli `r` that are non-squarefree, that share a factor with `W(x)`, or that exceed `x^β`
contribute zero (the three `Gap212.Sieve.innerMoebiusSum_eq_zero_of_*` lemmas — the last uses the
support clause, and makes the unbounded truncation `B` harmless); on what is left, the input gives
`φ(r)|y_r||y'_r| ≤ C_FC_G(W/φ(W))^2/(φ(r)\log^2x)`, and
`Gap212.Sieve.sum_moebiusSq_div_totient_coprime` sums `μ^2(r)/φ(r)` over the moduli `≤ x^β` coprime
to `W` to `(φ(W)/W)(β\log x + O_W(1))`. The two `W/φ(W)` factors cancel one of the `φ(W)/W`, and
what is left is `C_FC_G(β + O(1))·(W/φ(W))/\log x = K/B_x`. Note where the sharpness went: the
`\log^{-2}x` from the two inner bounds is only turned into `\log^{-1}x` by the *length* `β\log x`
of the modulus sum, so a bound on `y_r` weaker by any power of `\log x` would not close, and one
with `r` in place of `φ(r)` would not either. -/
theorem abs_restrictedSum_one_le_of_smoothMoebiusInnerBound (hin : SmoothMoebiusInnerBound)
    {β : ℝ} (hβ : 0 < β) (F G : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G) (hFβ : ∀ t : ℝ, β ≤ t → F t = 0)
    (hGβ : ∀ t : ℝ, β ≤ t → G t = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop, ∀ B : ℕ, x ^ β ≤ (B : ℝ) →
      |restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeight x F G) 1|
        ≤ K / ((((W x).totient : ℝ) / (W x : ℝ)) * Real.log x) := by
  obtain ⟨CF, hCF, hevF⟩ := hin β hβ F hF hFc hFβ
  obtain ⟨CG, hCG, hevG⟩ := hin β hβ G hG hGc hGβ
  obtain ⟨C₀, hC₀, hmert⟩ := sum_moebiusSq_div_totient_coprime
  refine ⟨CF * CG * (β + 2 + 2 * C₀), by positivity, ?_⟩
  filter_upwards [hevF, hevG, eventually_W_facts, eventually_gt_atTop (1 : ℝ)]
    with x hxF hxG ⟨hL1, hφ1, hφW, hWsq, hτW, hℓW⟩ hx1 B hB
  -- the Mertens sum of `μ²/φ` over the class
  have hMle := sum_moebiusSq_div_totient_le_of_W_facts hC₀ hmert hx1 hβ hL1 hφ1 hφW hWsq hτW hℓW
  set L : ℝ := Real.log x
  set Wr : ℝ := (W x : ℝ)
  set φW : ℝ := ((W x).totient : ℝ)
  have hL0 : 0 < L := by linarith
  have hφ0 : 0 < φW := by linarith
  have hW0 : 0 < Wr := by linarith
  -- the diagonalisation
  set N₀ : ℕ := ⌊x ^ β⌋₊
  have hN₀B : N₀ ≤ B := Nat.floor_le_of_le hB
  have hdiag : restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeight x F G) 1
      = ∑ r ∈ Icc 1 B, (r.totient : ℝ)
          * (innerMoebiusSum x F B r * innerMoebiusSum x G B r) := by
    rw [restrictedSum_one, Finset.sum_product]
    exact sum_pairs_div_lcm_eq_sum_totient_mul B (wBox x B) (fun d hd ↦ (mem_wBox.mp hd).1)
      (fun d ↦ (μ d : ℝ) * F (Notation.logx x d)) (fun d ↦ (μ d : ℝ) * G (Notation.logx x d))
  -- restrict the modulus sum to the squarefree moduli below `x^β` coprime to `W(x)`
  set S : Finset ℕ := {e ∈ Finset.Icc 1 N₀ | Nat.Coprime (W x) e}
  have hSsub : S ⊆ Icc 1 B := fun r hr ↦ by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
    exact Finset.mem_Icc.mpr ⟨h1, h2.trans hN₀B⟩
  have hzero : ∀ r ∈ Icc 1 B, r ∉ S →
      (r.totient : ℝ) * (innerMoebiusSum x F B r * innerMoebiusSum x G B r) = 0 := by
    intro r hr hrS
    by_cases hcop : Nat.Coprime (W x) r
    · have hgt : x ^ β < (r : ℝ) := Nat.lt_of_floor_lt (lt_of_not_ge fun h ↦ hrS
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, h⟩, hcop⟩))
      rw [innerMoebiusSum_eq_zero_of_rpow_lt hx1 hFβ hgt, zero_mul, mul_zero]
    · rw [innerMoebiusSum_eq_zero_of_not_coprime hcop, zero_mul, mul_zero]
  have hterm : ∀ r ∈ S,
      |(r.totient : ℝ) * (innerMoebiusSum x F B r * innerMoebiusSum x G B r)|
        ≤ (CF * CG * (Wr / φW) ^ 2 / L ^ 2) * ((μ r : ℝ) ^ 2 / (r.totient : ℝ)) := by
    intro r hr
    have hr1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
    by_cases hsf : Squarefree r
    · have hφr : (0 : ℝ) < (r.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hr1
      have hmu : ((μ r : ℤ) : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
      rw [abs_mul, abs_of_nonneg hφr.le, abs_mul, hmu]
      calc (r.totient : ℝ) * (|innerMoebiusSum x F B r| * |innerMoebiusSum x G B r|)
          ≤ (r.totient : ℝ)
              * ((CF * (Wr / φW) / ((r.totient : ℝ) * L))
                  * (CG * (Wr / φW) / ((r.totient : ℝ) * L))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hxF B r hB hr1) (hxG B r hB hr1)
              (abs_nonneg _) (by positivity)) hφr.le
        _ = (CF * CG * (Wr / φW) ^ 2 / L ^ 2) * (1 / (r.totient : ℝ)) := by
            field_simp
    · rw [innerMoebiusSum_eq_zero_of_not_squarefree hsf, zero_mul, mul_zero, abs_zero,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
      positivity
  -- assembly
  rw [hdiag, ← Finset.sum_subset hSsub hzero]
  refine (Finset.abs_sum_le_sum_abs _ _).trans <| (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left hMle (by positivity)).trans_eq ?_
  field_simp
  ring

/-! ## Totient arithmetic for the modulus-restricted diagonalisation -/

/-- **`φ(g·l) = g·φ(l)` when `g ∣ l`.** The primes of `g·l` are exactly the primes of `l`, so the
Euler product gains the factor `g` and nothing else. -/
theorem totient_mul_of_dvd : ∀ {g l : ℕ}, g ∣ l → (g * l).totient = g * l.totient := by
  intro g l hgl
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  have h := Nat.totient_gcd_mul_totient_mul g l
  rw [Nat.gcd_eq_left hgl] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr hg) (h.trans (by ring))

/-- **`φ(r)φ(m) ≤ (r,m)·φ([r,m])`** — with equality, but only the inequality is needed. This is
what makes the modulus-restricted diagonalisation summable: it converts a bound at the modulus
`[r,m]` into `(r,m)/(φ(r)φ(m))`, where the `1/φ(r)` is what the Mertens sum integrates and the
`(r,m)` is what the divisor bookkeeping absorbs. From `Nat.totient_gcd_mul_totient_mul` and
`Gap212.Sieve.totient_mul_of_dvd` at `g = (r,m) ∣ [r,m]`. -/
theorem totient_mul_totient_le_gcd_mul_totient_lcm (r m : ℕ) :
    r.totient * m.totient ≤ Nat.gcd r m * (Nat.lcm r m).totient := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have h1 := Nat.totient_gcd_mul_totient_mul r m
  rw [← Nat.gcd_mul_lcm r m,
    totient_mul_of_dvd ((Nat.gcd_dvd_left r m).trans (Nat.dvd_lcm_left r m))] at h1
  have key : (Nat.gcd r m).totient * (Nat.lcm r m).totient = r.totient * m.totient :=
    Nat.eq_of_mul_eq_mul_right (Nat.gcd_pos_of_pos_left _ hr) (by rw [← h1]; ring)
  rw [← key]
  exact Nat.mul_le_mul_right _ (Nat.totient_le _)

/-- **`(k,m)(k,n) ∣ k·(m,n)`.** The product divides both `k·n` and `k·m`, hence their gcd. -/
theorem gcd_mul_gcd_dvd_mul_gcd (k m n : ℕ) :
    Nat.gcd k m * Nat.gcd k n ∣ k * Nat.gcd m n := by
  have h := Nat.dvd_gcd (mul_dvd_mul (Nat.gcd_dvd_left k m) (Nat.gcd_dvd_right k n))
    ((mul_dvd_mul (Nat.gcd_dvd_right k m) (Nat.gcd_dvd_left k n)).trans (mul_comm m k).dvd)
  rwa [Nat.gcd_mul_left, Nat.gcd_comm n m] at h

/-- **`k ≤ 2^{ω(k)}φ(k)`**: `k/φ(k) = ∏_{p ∣ k}p/(p-1)` and each factor is at most `2`. -/
theorem self_le_two_pow_card_primeFactors_mul_totient (k : ℕ) :
    k ≤ 2 ^ #k.primeFactors * k.totient := by
  have hprod : ∏ p ∈ k.primeFactors, p ≤ 2 ^ #k.primeFactors * ∏ p ∈ k.primeFactors, (p - 1) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun p hp ↦ ?_
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  rw [Nat.totient_eq_div_primeFactors_mul]
  calc k = k / (∏ p ∈ k.primeFactors, p) * ∏ p ∈ k.primeFactors, p :=
        (Nat.div_mul_cancel (Nat.prod_primeFactors_dvd k)).symm
    _ ≤ k / (∏ p ∈ k.primeFactors, p) * (2 ^ #k.primeFactors * ∏ p ∈ k.primeFactors, (p - 1)) :=
        Nat.mul_le_mul_left _ hprod
    _ = _ := by ring

/-! ## The modulus sum with a gcd weight -/

/-- **The gcd-weighted Mertens sum.** For every `Q ≠ 0`,

  `∑_{r ≤ N, (r,W)=1, r squarefree} (r,Q)/φ(r) ≤ (∑_{k ∣ Q}k/φ(k))·∑_{r ≤ N, (r,W)=1} μ^2(r)/φ(r)`,

by fibering the moduli over `k = (r,Q)`: the fibre is contained in the multiples of `k`, and
`r ↦ kr` maps the whole range into itself with `φ(kr) ≥ φ(k)φ(r)`
(`Nat.totient_super_multiplicative`). This is what keeps the modulus-restricted diagonalisation
tied to the *same* Mertens sum the `e = 1` case uses — no Mertens estimate at a moving modulus is
needed. -/
theorem sum_gcd_div_totient_le (W N Q : ℕ) (hQ : Q ≠ 0) :
    ∑ r ∈ Icc 1 N with (Nat.Coprime W r ∧ Squarefree r), (Nat.gcd r Q : ℝ) / (r.totient : ℝ)
      ≤ (∑ k ∈ Q.divisors, (k : ℝ) / (k.totient : ℝ))
        * ∑ r ∈ Icc 1 N with (Nat.Coprime W r ∧ Squarefree r), (1 : ℝ) / (r.totient : ℝ) := by
  set T : Finset ℕ := {r ∈ Icc 1 N | Nat.Coprime W r ∧ Squarefree r}
  have hφT : ∀ r ∈ T, (0 : ℝ) < r.totient := fun r hr ↦ by
    exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
  rw [← Finset.sum_fiberwise_of_maps_to (g := (Nat.gcd · Q))
    fun r _ ↦ Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right r Q, hQ⟩, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk ↦ ?_
  have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
  have hφk : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk0
  have hsub : {r ∈ T | Nat.gcd r Q = k} ⊆ T.image (k * ·) := by
    intro r hr
    obtain ⟨hrT, hgcd⟩ := Finset.mem_filter.mp hr
    obtain ⟨r', rfl⟩ := hgcd ▸ Nat.gcd_dvd_left r Q
    obtain ⟨hmem, hcop, hsf⟩ := Finset.mem_filter.mp hrT
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hmem
    have hr'0 : 0 < r' := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
    exact Finset.mem_image.mpr ⟨r', Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hr'0, (Nat.le_mul_of_pos_left _ hk0).trans h2⟩, hcop.coprime_dvd_right (dvd_mul_left r' k),
      hsf.squarefree_of_dvd (dvd_mul_left r' k)⟩, rfl⟩
  calc ∑ r ∈ T with Nat.gcd r Q = k, (Nat.gcd r Q : ℝ) / (r.totient : ℝ)
      = k * ∑ r ∈ T with Nat.gcd r Q = k, (1 : ℝ) / (r.totient : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r hr ↦ by rw [(Finset.mem_filter.mp hr).2]; ring
    _ ≤ k * ∑ r ∈ T.image (k * ·), (1 : ℝ) / (r.totient : ℝ) := by gcongr
    _ = k * ∑ r' ∈ T, (1 : ℝ) / (((k * r').totient : ℕ) : ℝ) := by
        rw [Finset.sum_image fun a _ b _ h ↦ Nat.eq_of_mul_eq_mul_left hk0 h]
    _ ≤ k * ∑ r' ∈ T, (1 / (k.totient : ℝ)) * ((1 : ℝ) / (r'.totient : ℝ)) := by
        gcongr with r' hr'
        rw [one_div_mul_one_div]
        exact one_div_le_one_div_of_le (mul_pos hφk (hφT r' hr'))
          (by exact_mod_cast Nat.totient_super_multiplicative k r')
    _ = (k : ℝ) / (k.totient : ℝ) * ∑ r ∈ T, (1 : ℝ) / (r.totient : ℝ) := by
        rw [← Finset.mul_sum]; ring

/-! ## The modulus, split between the two coordinates -/

/-- **`e ∣ [d,d']` splits the modulus at `a = (e,d)`**: for squarefree `e` the complement `e/a`
must divide the *other* coordinate, and conversely. This is the partition the modulus-restricted
diagonalisation runs over — `a` is determined by `d`, so the classes are disjoint, and no
inclusion-exclusion is needed to cover them. -/
theorem dvd_lcm_iff_div_gcd_dvd {e d d' : ℕ} (hesf : Squarefree e) :
    e ∣ Nat.lcm d d' ↔ (e / Nat.gcd e d) ∣ d' := by
  have hae : Nat.gcd e d ∣ e := Nat.gcd_dvd_left e d
  have hmul : Nat.gcd e d * (e / Nat.gcd e d) = e := Nat.mul_div_cancel' hae
  have hcop := (Nat.squarefree_mul_iff.mp (hmul ▸ hesf)).1
  have hcd : Nat.Coprime (e / Nat.gcd e d) d := Nat.eq_one_of_dvd_coprimes hcop
    (Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.div_dvd_of_dvd hae)) (Nat.gcd_dvd_right _ _))
    (Nat.gcd_dvd_left _ _)
  refine ⟨fun h ↦ hcd.dvd_of_dvd_mul_left
      ((Nat.div_dvd_of_dvd hae).trans (h.trans (Nat.lcm_dvd_mul d d'))), fun h ↦ ?_⟩
  rw [← hmul]
  exact hcop.mul_dvd_of_dvd_of_dvd ((Nat.gcd_dvd_right e d).trans (Nat.dvd_lcm_left d d'))
    (h.trans (Nat.dvd_lcm_right d d'))

/-- **The exact-gcd condition, read on the complement.** For squarefree `e` and `a ∣ e` with
`a ∣ d`: `(e,d) = a` exactly when `d` is coprime to `e/a`. -/
theorem gcd_eq_iff_coprime_div {e a d : ℕ} (hesf : Squarefree e) (hae : a ∣ e) (had : a ∣ d) :
    Nat.gcd e d = a ↔ Nat.gcd (e / a) d = 1 := by
  have hmul : a * (e / a) = e := Nat.mul_div_cancel' hae
  have hcop := (Nat.squarefree_mul_iff.mp (hmul ▸ hesf)).1
  refine ⟨fun h ↦ Nat.eq_one_of_dvd_coprimes hcop ((Nat.dvd_gcd
      ((Nat.gcd_dvd_left (e / a) d).trans (Nat.div_dvd_of_dvd hae))
        (Nat.gcd_dvd_right (e / a) d)).trans h.dvd) (Nat.gcd_dvd_left _ _), fun h ↦ ?_⟩
  rw [← hmul, Nat.Coprime.gcd_mul_right_cancel a h]
  exact Nat.gcd_eq_left had

/-- **The divisors of `n` that divide `d` are the divisors of `(n,d)`.** -/
theorem filter_dvd_divisors_eq_divisors_gcd {n d : ℕ} (hn : n ≠ 0) :
    {c ∈ n.divisors | c ∣ d} = (Nat.gcd n d).divisors := by
  ext c
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  exact ⟨fun ⟨⟨hcn, _⟩, hcd⟩ ↦ ⟨⟨hcn, hcd⟩, Nat.gcd_ne_zero_left hn⟩,
    fun ⟨⟨hcn, hcd⟩, _⟩ ↦ ⟨⟨hcn, hn⟩, hcd⟩⟩

/-- **The inner sum over one class of the partition, expanded by Möbius.** For squarefree `e` and
`a ∣ e`,

  `∑_{d ∈ [1,B], (d,W)=1, r ∣ d, (e,d)=a} μ(d)F(\log_xd)/d
      = ∑_{c ∣ e/a} μ(c)·y_{[[r,a],c]}`,

the coprimality `(d, e/a) = 1` that the exact-gcd condition amounts to
(`Gap212.Sieve.gcd_eq_iff_coprime_div`) being detected by `∑_{c ∣ (e/a,d)}μ(c)`. So the one class
of the partition is a signed combination of at most `τ(e/a)` inner Möbius sums, and the pointwise
input bounds each of them. -/
theorem sum_filter_gcd_eq_sum_divisors_moebius_mul {x : ℝ} (F : ℝ → ℝ) (B : ℕ) {e a : ℕ}
    (hesf : Squarefree e) (hae : a ∣ e) (r : ℕ) :
    ∑ d ∈ wBox x B with (r ∣ d ∧ Nat.gcd e d = a), (μ d : ℝ) * F (Notation.logx x d) / (d : ℝ)
      = ∑ c ∈ (e / a).divisors, (μ c : ℝ) * innerMoebiusSum x F B (Nat.lcm (Nat.lcm r a) c) := by
  have hb0 : e / a ≠ 0 := fun h ↦ hesf.ne_zero (by rw [← Nat.mul_div_cancel' hae, h, mul_zero])
  have hRHS : ∑ c ∈ (e / a).divisors, (μ c : ℝ) * innerMoebiusSum x F B (Nat.lcm (Nat.lcm r a) c)
      = ∑ d ∈ wBox x B, ∑ c ∈ (e / a).divisors,
          (if Nat.lcm (Nat.lcm r a) c ∣ d then
            (μ c : ℝ) * ((μ d : ℝ) * F (Notation.logx x d) / (d : ℝ)) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [innerMoebiusSum, Finset.mul_sum, Finset.sum_filter]
  rw [hRHS, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  set w : ℝ := (μ d : ℝ) * F (Notation.logx x d) / (d : ℝ)
  by_cases hra : r ∣ d ∧ a ∣ d
  · have hstep : ∑ c ∈ (e / a).divisors,
        (if Nat.lcm (Nat.lcm r a) c ∣ d then (μ c : ℝ) * w else 0)
        = (∑ c ∈ (e / a).divisors with c ∣ d, (μ c : ℝ)) * w := by
      rw [Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      simp only [Nat.lcm_dvd_iff, hra, true_and, ite_mul, zero_mul]
    rw [hstep, filter_dvd_divisors_eq_divisors_gcd hb0, sum_divisors_moebius_real]
    simp [gcd_eq_iff_coprime_div hesf hae hra.2, hra.1]
  · rw [if_neg fun ⟨hr, hg⟩ ↦ hra ⟨hr, hg ▸ Nat.gcd_dvd_right e d⟩]
    refine (Finset.sum_eq_zero fun c _ ↦ if_neg fun hdvd ↦ hra ?_).symm
    rw [Nat.lcm_dvd_iff, Nat.lcm_dvd_iff] at hdvd
    exact hdvd.1

/-- **The inner sum at an lcm modulus is the doubly-divisible sum.** -/
theorem innerMoebiusSum_lcm (x : ℝ) (F : ℝ → ℝ) (B r m : ℕ) :
    innerMoebiusSum x F B (Nat.lcm r m)
      = ∑ d ∈ wBox x B with (r ∣ d ∧ m ∣ d), (μ d : ℝ) * F (Notation.logx x d) / (d : ℝ) := by
  simp only [innerMoebiusSum, Nat.lcm_dvd_iff]

/-- **The modulus-restricted pair sum, partitioned and diagonalised.** For squarefree `e`,

  `|T_e| ≤ ∑_{a ∣ e}∑_{c ∣ e/a}∑_{r ≤ B} φ(r)·|y_F([[r,a],c])|·|y_G([r,e/a])|`.

Three exact steps and one triangle inequality, in that order: the pairs with `e ∣ [d,d']` are
partitioned by `a = (e,d)`, which forces `e/a ∣ d'` (`Gap212.Sieve.dvd_lcm_iff_div_gcd_dvd`); each
class is a pair sum with the two coordinates restricted independently, so
`Gap212.Sieve.sum_pairs_div_lcm_eq_sum_totient_mul` diagonalises it; the `d`-side factor is a
signed combination of `τ(e/a)` inner Möbius sums
(`Gap212.Sieve.sum_filter_gcd_eq_sum_divisors_moebius_mul`) and the `d'`-side factor is one of
them. **Only now are absolute values taken**, and by then every factor is a one-variable sum with
no cancellation left inside it — which is why this does not lose the `B_x^4` that a term-by-term
bound on the original sum loses. -/
theorem abs_restrictedSum_le_sum_divisors {x : ℝ} (F G : ℝ → ℝ) (B : ℕ) {e : ℕ}
    (hesf : Squarefree e) :
    |restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeight x F G) e|
      ≤ ∑ a ∈ e.divisors, ∑ c ∈ (e / a).divisors, ∑ r ∈ Icc 1 B,
          (r.totient : ℝ) * (|innerMoebiusSum x F B (Nat.lcm (Nat.lcm r a) c)|
            * |innerMoebiusSum x G B (Nat.lcm r (e / a))|) := by
  have hpart : restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeight x F G) e
      = ∑ a ∈ e.divisors, ∑ d ∈ wBox x B with Nat.gcd e d = a,
          ∑ d' ∈ wBox x B with (e / a) ∣ d', pairWeight x F G (d, d') := by
    rw [restrictedSum, ← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ ↦ Nat.gcd e p.1)
      (f := pairWeight x F G)
      fun p _ ↦ Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left e p.1, hesf.ne_zero⟩]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hset : {p ∈ {p ∈ wBox x B ×ˢ wBox x B | e ∣ lcmPair p} | Nat.gcd e p.1 = a}
        = {d ∈ wBox x B | Nat.gcd e d = a} ×ˢ {d' ∈ wBox x B | (e / a) ∣ d'} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨fun ⟨⟨⟨h1, h2⟩, hdvd⟩, h⟩ ↦ ⟨⟨h1, h⟩, h2, h ▸ (dvd_lcm_iff_div_gcd_dvd hesf).mp hdvd⟩,
        fun ⟨⟨h1, h⟩, h2, hb⟩ ↦ ⟨⟨⟨h1, h2⟩, (dvd_lcm_iff_div_gcd_dvd hesf).mpr (h ▸ hb)⟩, h⟩⟩
    rw [hset, Finset.sum_product]
  rw [hpart]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a ha ↦ ?_)
  obtain ⟨hae, -⟩ := Nat.mem_divisors.mp ha
  set L : ℕ → ℝ := fun d ↦ if Nat.gcd e d = a then (μ d : ℝ) * F (Notation.logx x d) else 0
    with hLdef
  set M : ℕ → ℝ := fun d ↦ if (e / a) ∣ d then (μ d : ℝ) * G (Notation.logx x d) else 0 with hMdef
  have hinner : ∑ d ∈ wBox x B with Nat.gcd e d = a,
        ∑ d' ∈ wBox x B with (e / a) ∣ d', pairWeight x F G (d, d')
      = ∑ d ∈ wBox x B, ∑ d' ∈ wBox x B, L d * M d' / (Nat.lcm d d' : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [Finset.sum_filter]
    by_cases hP : Nat.gcd e d = a
    · refine (if_pos hP).trans (Finset.sum_congr rfl fun d' _ ↦ ?_)
      by_cases hQ : e / a ∣ d' <;> simp [hLdef, hMdef, hP, hQ, pairWeight, lcmPair]
    · simp [hLdef, hP]
  rw [hinner, sum_pairs_div_lcm_eq_sum_totient_mul B (wBox x B) (fun d hd ↦ (mem_wBox.mp hd).1)]
  have hA : ∀ r : ℕ, ∑ d ∈ wBox x B with r ∣ d, L d / (d : ℝ)
      = ∑ c ∈ (e / a).divisors, (μ c : ℝ) * innerMoebiusSum x F B (Nat.lcm (Nat.lcm r a) c) := by
    intro r
    rw [← sum_filter_gcd_eq_sum_divisors_moebius_mul F B hesf hae r, Finset.sum_filter,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    by_cases h1 : r ∣ d <;> by_cases h2 : Nat.gcd e d = a <;> simp [hLdef, h1, h2]
  have hB : ∀ r : ℕ, ∑ d' ∈ wBox x B with r ∣ d', M d' / (d' : ℝ)
      = innerMoebiusSum x G B (Nat.lcm r (e / a)) := by
    intro r
    rw [innerMoebiusSum_lcm, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    by_cases h1 : r ∣ d <;> by_cases h2 : e / a ∣ d <;> simp [hMdef, h1, h2]
  refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ ↦ ?_)).trans_eq
    Finset.sum_comm
  rw [hA r, hB r, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_mul, ← Finset.mul_sum,
    ← Finset.sum_mul]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_real_le_one c)

/-! ## The arithmetic of one class of the partition -/

/-- `((r,Q),A) = (r,A)` when `A ∣ Q`. -/
theorem gcd_gcd_of_dvd {r Q A : ℕ} (h : A ∣ Q) : Nat.gcd (Nat.gcd r Q) A = Nat.gcd r A := by
  rw [Nat.gcd_assoc, Nat.gcd_eq_right h]

/-- **The two moduli of one partition class, in one inequality.** For squarefree `e`, `a ∣ e` and
`c ∣ e/a`, writing `m = [[r,a],c]` and `n = [r,e/a]`,

  `φ(r)^2φ(e)φ(c) ≤ (r,ce)·c·φ(m)φ(n)`.

Everything in the modulus-restricted bound is here: `φ(r)φ(ac) ≤ (r,ac)φ(m)` and
`φ(r)φ(e/a) ≤ (r,e/a)φ(n)` (`Gap212.Sieve.totient_mul_totient_le_gcd_mul_totient_lcm`), the two
gcds collapse to `(r,ce)·(ac,e/a) = (r,ce)·c`
(`Gap212.Sieve.gcd_mul_gcd_dvd_mul_gcd`), and `φ(ac)φ(e/a) = φ(e)φ(c)` because `a`, `c`, `e/a` are
pairwise coprime except for `c ∣ e/a`. -/
theorem totient_sq_mul_le_gcd_mul_totient_lcm_mul (e a c r : ℕ) (hesf : Squarefree e)
    (hae : a ∣ e) (hc : c ∣ e / a) :
    r.totient * r.totient * (e.totient * c.totient)
      ≤ Nat.gcd r (c * e) * c
        * ((Nat.lcm (Nat.lcm r a) c).totient * (Nat.lcm r (e / a)).totient) := by
  set b : ℕ := e / a
  have hmul : a * b = e := Nat.mul_div_cancel' hae
  have hsf : Squarefree (a * b) := by rw [hmul]; exact hesf
  have hcopab : Nat.Coprime a b := (Nat.squarefree_mul_iff.mp hsf).1
  have hcopac : Nat.Coprime a c := hcopab.coprime_dvd_right hc
  rw [Nat.lcm_assoc, hcopac.lcm_eq_mul]
  have hQ : a * c * b = c * e := by rw [← hmul]; ring
  -- the two totient/lcm inequalities
  have h1 := totient_mul_totient_le_gcd_mul_totient_lcm r (a * c)
  have h2 := totient_mul_totient_le_gcd_mul_totient_lcm r b
  -- the gcds collapse
  have hAQ : a * c ∣ c * e := ⟨b, hQ.symm⟩
  have hbQ : b ∣ c * e := ⟨a * c, hQ.symm.trans (mul_comm _ _)⟩
  have hgcdAb : Nat.gcd (a * c) b = c := by
    rw [hcopab.gcd_mul_left_cancel c]
    exact Nat.gcd_eq_left hc
  have hcollapse : Nat.gcd r (a * c) * Nat.gcd r b ∣ Nat.gcd r (c * e) * c := by
    have h := gcd_mul_gcd_dvd_mul_gcd (Nat.gcd r (c * e)) (a * c) b
    rwa [gcd_gcd_of_dvd hAQ, gcd_gcd_of_dvd hbQ, hgcdAb] at h
  have he0 : 0 < e := Nat.pos_of_ne_zero hesf.ne_zero
  have hb0 : 0 < b := Nat.pos_of_ne_zero fun h ↦ hesf.ne_zero (by rw [← hmul, h, mul_zero])
  have hc0 : 0 < c := Nat.pos_of_dvd_of_pos hc hb0
  -- the totients factor
  calc r.totient * r.totient * (e.totient * c.totient)
      = (r.totient * (a * c).totient) * (r.totient * b.totient) := by
        rw [Nat.totient_mul hcopac, ← hmul, Nat.totient_mul hcopab]; ring
    _ ≤ (Nat.gcd r (a * c) * (Nat.lcm r (a * c)).totient) * (Nat.gcd r b * (Nat.lcm r b).totient) :=
        Nat.mul_le_mul h1 h2
    _ = (Nat.gcd r (a * c) * Nat.gcd r b)
          * ((Nat.lcm r (a * c)).totient * (Nat.lcm r b).totient) := by ring
    _ ≤ Nat.gcd r (c * e) * c
          * ((Nat.lcm r (a * c)).totient * (Nat.lcm r b).totient) :=
        Nat.mul_le_mul_right _ <| Nat.le_of_dvd
          (Nat.mul_pos (Nat.gcd_pos_of_pos_right r (Nat.mul_pos hc0 he0)) hc0) hcollapse

/-! ## Divisor factors, absorbed by the large prime factors of the modulus -/

/-- `k/φ(k) ≤ 2^{ω(N)}` for every divisor `k` of `N`. -/
theorem self_div_totient_le_two_pow_card_primeFactors {N k : ℕ} (hN : N ≠ 0) (hk : k ∣ N)
    (hk0 : k ≠ 0) : (k : ℝ) / (k.totient : ℝ) ≤ 2 ^ #N.primeFactors := by
  have hφ : (0 : ℝ) < (k.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hk0)
  rw [div_le_iff₀ hφ]
  have h1 : (k : ℝ) ≤ 2 ^ #k.primeFactors * (k.totient : ℝ) := by
    exact_mod_cast self_le_two_pow_card_primeFactors_mul_totient k
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ hφ.le)
  exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_card (Nat.primeFactors_mono hk hN))

/-- **The divisor sum of `k/φ(k)` over the divisors of `Q ∣ e^2` is at most `8^{ω(e)}`**: at most
`4^{ω(e)}` divisors, each with `k/φ(k) ≤ 2^{ω(e)}`. Every factor the modulus-restricted
diagonalisation produces is of this shape, and this is why they are all absorbed: the prime factors
of `e` exceed `\log\log\log x`, so `2^{ω(e)}` is a vanishing power of `e`. -/
theorem sum_divisors_self_div_totient_le {Q e : ℕ} (he : Squarefree e) (hQ : Q ∣ e * e)
    (hQ0 : Q ≠ 0) : ∑ k ∈ Q.divisors, (k : ℝ) / (k.totient : ℝ) ≤ 8 ^ #e.primeFactors := by
  have he0 : e ≠ 0 := he.ne_zero
  have hee : e * e ≠ 0 := mul_ne_zero he0 he0
  have hpfee : (e * e).primeFactors = e.primeFactors := by
    rw [Nat.primeFactors_mul he0 he0, Finset.union_self]
  have hcard : #Q.divisors ≤ 4 ^ #e.primeFactors := by
    rw [Nat.card_divisors hQ0]
    calc Q.primeFactors.prod (Q.factorization · + 1)
        ≤ ∏ _p ∈ Q.primeFactors, 4 := Finset.prod_le_prod' fun p _ ↦ by
          have h1 := (Nat.factorization_le_iff_dvd hQ0 hee).mpr hQ p
          rw [Nat.factorization_mul he0 he0, Finsupp.add_apply] at h1
          have := he.natFactorization_le_one p
          omega
      _ = 4 ^ #Q.primeFactors := Finset.prod_const _
      _ ≤ 4 ^ #e.primeFactors := Nat.pow_le_pow_right (by norm_num)
          (Finset.card_le_card (hpfee ▸ Nat.primeFactors_mono hQ hee))
  have hterm : ∀ k ∈ Q.divisors, (k : ℝ) / (k.totient : ℝ) ≤ 2 ^ #e.primeFactors := fun k hk ↦ by
    simpa [hpfee] using self_div_totient_le_two_pow_card_primeFactors hee
      ((Nat.dvd_of_mem_divisors hk).trans hQ) (Nat.pos_of_mem_divisors hk).ne'
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul, show (8 : ℝ) = 4 * 2 by norm_num, mul_pow]
  gcongr
  exact_mod_cast hcard

/-- **`2^{ω(e)}` is a small power of `e` when the prime factors of `e` are large.** For squarefree
`e` all of whose prime factors exceed `D`, `D^{ω(e)} ≤ e`. At `D = 2^{28}` this gives
`(128^{ω(e)})^4 ≤ e`, which is what turns every divisor factor of the modulus-restricted bound into
`e^{1/4}` — the whole slack of the exponent `s = 3/4`. The hypothesis holds whenever `e` is
coprime to `W(x)`, since `W(x)` collects every prime up to `\log\log\log x`. -/
theorem pow_card_primeFactors_le_self {e D : ℕ} (he : Squarefree e)
    (hD : ∀ p ∈ e.primeFactors, D ≤ p) : D ^ #e.primeFactors ≤ e := by
  calc D ^ #e.primeFactors = ∏ _p ∈ e.primeFactors, D := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ e.primeFactors, p := Finset.prod_le_prod' hD
    _ = e := Nat.prod_primeFactors_of_squarefree he

/-! ## The Mertens sum over the moduli the support clause leaves -/

/-- **The modulus sum of the diagonalisation, bounded once and for all.** For every large `x` and
every `β > 0`,

  `∑_{r ≤ x^β, (r,W)=1} μ^2(r)/φ(r) ≤ (β + C)·(φ(W)/W)\log x`

with an absolute `C`. This is `Gap212.Sieve.sum_moebiusSq_div_totient_coprime` with its `O_W(1)`
discharged: `\log⌊x^β⌋ ≤ β\log x`, `γ ≤ 1`, `ℓ_W ≤ \log W ≤ W` and `τ(W) ≤ W`, all `≤ \log x` since
`W(x)^2 ≤ \log x` (`Gap212.Sieve.W_sq_le_log`). The prefactor `φ(W)/W` is what the two `W/φ(W)` of
the inner bounds cancel against, and the length `β\log x` is what turns `\log^{-2}x` into
`\log^{-1}x`. -/
theorem eventually_sum_moebiusSq_div_totient_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ β : ℝ, 0 < β →
      ∑ r ∈ Icc 1 ⌊x ^ β⌋₊ with Nat.Coprime (W x) r, ((μ r : ℝ) ^ 2 / (r.totient : ℝ))
        ≤ (β + C) * ((((W x).totient : ℝ) / (W x : ℝ)) * Real.log x) := by
  obtain ⟨C₀, hC₀, hmert⟩ := sum_moebiusSq_div_totient_coprime
  refine ⟨2 + 2 * C₀, by positivity, ?_⟩
  filter_upwards [eventually_W_facts, eventually_gt_atTop (1 : ℝ)]
    with x ⟨hL1, hφ1, hφW, hWsq, hτW, hℓW⟩ hx1 β hβ
  exact sum_moebiusSq_div_totient_le_of_W_facts hC₀ hmert hx1 hβ hL1 hφ1 hφW hWsq hτW hℓW

/-! ## The moduli that see no pair at all -/

/-- **A non-squarefree modulus contributes nothing.** `e ∣ [d,d']` forces `[d,d']` non-squarefree,
hence one of `d`, `d'` non-squarefree, and `μ` kills the term. -/
theorem restrictedSum_pairWeight_eq_zero_of_not_squarefree (x : ℝ) (F G : ℝ → ℝ) (B : ℕ) {e : ℕ}
    (he : ¬ Squarefree e) :
    restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeight x F G) e = 0 := by
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  have hdvd := (Finset.mem_filter.mp hp).2
  by_cases hd : Squarefree p.1
  · by_cases hd' : Squarefree p.2
    · exact absurd ((squarefree_lcm hd hd').squarefree_of_dvd hdvd) he
    · simp [pairWeight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd']
  · simp [pairWeight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]

/-- **A modulus sharing a factor with `W(x)` contributes nothing**: the whole box is coprime to
`W(x)`, hence so is `[d,d']`, hence so is every divisor of it. -/
theorem restrictedSum_pairWeight_eq_zero_of_not_coprime (x : ℝ) (F G : ℝ → ℝ) (B : ℕ) {e : ℕ}
    (he : ¬ Nat.Coprime (W x) e) :
    restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeight x F G) e = 0 := by
  refine Finset.sum_eq_zero fun p hp ↦ absurd ?_ he
  obtain ⟨hmem, hdvd⟩ := Finset.mem_filter.mp hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
  exact (((mem_wBox.mp h1).2.mul_right (mem_wBox.mp h2).2).coprime_dvd_right
    (Nat.lcm_dvd_mul p.1 p.2)).coprime_dvd_right hdvd

/-! ## The one-coordinate estimate for supported profiles, from the one-variable input -/

/-- **`Gap212.Sieve.OneCoordLcmDecayAtLevelOfSupport (3/4)` holds, given the one-variable Möbius
bound `Gap212.Sieve.SmoothMoebiusInnerBound`.** Since `1/2 < 3/4`, this is exactly what
`Gap212.Sieve.tendsto_boxPairSum_sub_sievedPairSum_of_support` consumes, so on this one input the
sieving error closes.

The proof is Selberg's change of variables and then only inequalities. The moduli `e` that are not
squarefree or not coprime to `W(x)` have no pair to sum over at all
(`Gap212.Sieve.restrictedSum_pairWeight_eq_zero_of_not_squarefree`,
`Gap212.Sieve.restrictedSum_pairWeight_eq_zero_of_not_coprime`). For the rest,
`Gap212.Sieve.abs_restrictedSum_le_sum_divisors` partitions the pairs by `a = (e,d)` and
diagonalises each class, leaving `∑_{a ∣ e}∑_{c ∣ e/a}∑_rφ(r)|y_F([[r,a],c])||y_G([r,e/a])|` — at
which point the input bounds each factor and nothing further cancels.

Two mechanisms carry the estimate. The support clause
makes every `y` vanish at moduli above `x^β`, so the modulus sum runs over `r ≤ x^β` however large
the truncation `B` is, and `Gap212.Sieve.eventually_sum_moebiusSq_div_totient_le` bounds it by
`(β + C)(φ(W)/W)\log x`; against the `(W/φ(W))^2/\log^2x` of the two inner bounds this is exactly
`K/B_x`, with no slack. The exponent `3/4 < 1` pays for the divisor factors: the `e`-dependence
is all `128^{ω(e)}/e` (`Gap212.Sieve.sum_divisors_self_div_totient_le` and
`Gap212.Sieve.totient_sq_mul_le_gcd_mul_totient_lcm_mul`), and `e` is coprime to `W(x)`, so every
prime factor of `e` exceeds `2^{28}` and `128^{ω(e)} ≤ e^{1/4}`
(`Gap212.Sieve.pow_card_primeFactors_le_self`). At `s = 1` that last step is unavailable. -/
theorem oneCoordLcmDecayAtLevelOfSupport_of_smoothMoebiusInnerBound
    (hin : SmoothMoebiusInnerBound) : OneCoordLcmDecayAtLevelOfSupport (3 / 4) := by
  intro β hβ F G hF hFc hG hGc hFβ hGβ
  obtain ⟨CF, hCF, hevF⟩ := hin β hβ F hF hFc hFβ
  obtain ⟨CG, hCG, hevG⟩ := hin β hβ G hG hGc hGβ
  obtain ⟨C₀, hC₀, hmert⟩ := eventually_sum_moebiusSq_div_totient_le
  refine ⟨CF * CG * (β + C₀), by positivity, ?_⟩
  filter_upwards [hevF, hevG, eventually_W_facts, eventually_gt_atTop (1 : ℝ), hmert,
    eventually_dvd_W_of_prime_le (2 ^ 28)]
    with x hxF hxG ⟨hL1, hφ1, hφW, _⟩ hx1 hxM hxP B e hB he
  set L : ℝ := Real.log x
  set Wr : ℝ := (W x : ℝ)
  set φW : ℝ := ((W x).totient : ℝ)
  have hL0 : 0 < L := by linarith
  have hφ0 : 0 < φW := by linarith
  have hW0 : 0 < Wr := by linarith
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hrpow : (0 : ℝ) < (e : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos heR _
  have hnn : 0 ≤ CF * CG * (β + C₀) / (φW / Wr * L * (e : ℝ) ^ (3 / 4 : ℝ)) := by positivity
  obtain hesf | hesf := em' (Squarefree e)
  · rw [restrictedSum_pairWeight_eq_zero_of_not_squarefree x F G B hesf, abs_zero]
    exact hnn
  obtain hecop | hecop := em' (Nat.Coprime (W x) e)
  · rw [restrictedSum_pairWeight_eq_zero_of_not_coprime x F G B hecop, abs_zero]
    exact hnn
  -- the main case
  set w : ℕ := #e.primeFactors
  set N₀ : ℕ := ⌊x ^ β⌋₊
  set S' : Finset ℕ := {r ∈ Icc 1 N₀ | Nat.Coprime (W x) r ∧ Squarefree r} with hS'def
  have he0 : e ≠ 0 := hesf.ne_zero
  have hN₀B : N₀ ≤ B := Nat.floor_le_of_le hB
  set Ms : ℝ := ∑ r ∈ S', (1 : ℝ) / (r.totient : ℝ) with hMsdef
  set K₁ : ℝ := CF * CG * (Wr / φW) ^ 2 / L ^ 2 with hK₁def
  have hMs0 : (0 : ℝ) ≤ Ms := Finset.sum_nonneg fun r _ ↦ by positivity
  have hK₁0 : (0 : ℝ) ≤ K₁ := by positivity
  -- the Mertens bound, on the squarefree part of the range
  have hMs : Ms ≤ (β + C₀) * (φW / Wr * L) := by
    refine le_trans ?_ (hxM β hβ)
    calc Ms = ∑ r ∈ S', ((μ r : ℝ) ^ 2 / (r.totient : ℝ)) :=
          Finset.sum_congr rfl fun r hr ↦ by
            rw [show ((μ r : ℤ) : ℝ) ^ 2 = 1 by exact_mod_cast
              ArithmeticFunction.moebius_sq_eq_one_of_squarefree (Finset.mem_filter.mp hr).2.2]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (fun r hr ↦ Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2.1⟩) fun i _ _ ↦ by positivity
  -- every prime factor of `e` is large, so every divisor factor is a small power of `e`
  have hDp : ∀ p ∈ e.primeFactors, 2 ^ 28 ≤ p := fun p hp ↦ by
    by_contra hcon
    have hpp := Nat.prime_of_mem_primeFactors hp
    exact hpp.ne_one (Nat.eq_one_of_dvd_coprimes hecop (hxP p hpp (by omega))
      (Nat.dvd_of_mem_primeFactors hp))
  have h128 : (128 : ℝ) ^ w ≤ (e : ℝ) ^ (1 / 4 : ℝ) := by
    have hR : ((128 : ℝ) ^ w) ^ (4 : ℕ) ≤ (e : ℝ) := by
      calc ((128 : ℝ) ^ w) ^ (4 : ℕ) = ((2 ^ 28 : ℕ) : ℝ) ^ w := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ (e : ℝ) := by exact_mod_cast pow_card_primeFactors_le_self hesf hDp
    have h4 : ((e : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = (e : ℝ) := by
      rw [← Real.rpow_natCast ((e : ℝ) ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul heR.le]
      norm_num
    refine (pow_le_pow_iff_left₀ (n := 4) (by positivity) (by positivity) (by norm_num)).mp ?_
    rwa [h4]
  -- the bound for one class of the partition
  have hrm : ∀ r a c : ℕ, r ∣ Nat.lcm (Nat.lcm r a) c :=
    fun r a c ↦ (Nat.dvd_lcm_left r a).trans (Nat.dvd_lcm_left _ c)
  have hsub : S' ⊆ Icc 1 B := fun r hr ↦ by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
    exact Finset.mem_Icc.mpr ⟨h1, h2.trans hN₀B⟩
  have hkey : ∀ a ∈ e.divisors, ∀ c ∈ (e / a).divisors,
      ∑ r ∈ Icc 1 B, (r.totient : ℝ) * (|innerMoebiusSum x F B (Nat.lcm (Nat.lcm r a) c)|
          * |innerMoebiusSum x G B (Nat.lcm r (e / a))|)
        ≤ K₁ * ((32 : ℝ) ^ w / (e : ℝ)) * Ms := by
    intro a ha c hc
    obtain ⟨hae, -⟩ := Nat.mem_divisors.mp ha
    obtain ⟨hcb, hb0⟩ := Nat.mem_divisors.mp hc
    have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
    have hc0 : 0 < c := Nat.pos_of_mem_divisors hc
    have hce : c ∣ e := hcb.trans (Nat.div_dvd_of_dvd hae)
    have hzero : ∀ r ∈ Icc 1 B, r ∉ S' →
        (r.totient : ℝ) * (|innerMoebiusSum x F B (Nat.lcm (Nat.lcm r a) c)|
          * |innerMoebiusSum x G B (Nat.lcm r (e / a))|) = 0 := by
      intro r hr hrS
      have hr1 := (Finset.mem_Icc.mp hr).1
      suffices innerMoebiusSum x F B (Nat.lcm (Nat.lcm r a) c) = 0 by simp [this]
      by_cases hcop : Nat.Coprime (W x) r
      · by_cases hsfr : Squarefree r
        · refine innerMoebiusSum_eq_zero_of_rpow_lt hx1 hFβ ((Nat.lt_of_floor_lt
            (lt_of_not_ge fun h ↦ hrS (Finset.mem_filter.mpr
              ⟨Finset.mem_Icc.mpr ⟨hr1, h⟩, hcop, hsfr⟩))).trans_le ?_)
          exact_mod_cast Nat.le_of_dvd (Nat.lcm_pos (Nat.lcm_pos hr1 ha0) hc0) (hrm r a c)
        · exact innerMoebiusSum_eq_zero_of_not_squarefree
            fun hsf ↦ hsfr (hsf.squarefree_of_dvd (hrm r a c))
      · exact innerMoebiusSum_eq_zero_of_not_coprime
          fun hcp ↦ hcop (hcp.coprime_dvd_right (hrm r a c))
    rw [← Finset.sum_subset hsub hzero]
    have hφe : (0 : ℝ) < (e.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero he0)
    have hφc : (0 : ℝ) < (c.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hc0
    have hterm : ∀ r ∈ S', (r.totient : ℝ)
        * (|innerMoebiusSum x F B (Nat.lcm (Nat.lcm r a) c)|
          * |innerMoebiusSum x G B (Nat.lcm r (e / a))|)
        ≤ K₁ * ((Nat.gcd r (c * e) : ℝ) * (c : ℝ)
            / ((r.totient : ℝ) * (e.totient : ℝ) * (c.totient : ℝ))) := by
      intro r hr
      have hr1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
      have hm1 : 1 ≤ Nat.lcm (Nat.lcm r a) c := Nat.lcm_pos (Nat.lcm_pos hr1 ha0) hc0
      have hn1 : 1 ≤ Nat.lcm r (e / a) := Nat.lcm_pos hr1 (Nat.pos_of_ne_zero hb0)
      have hφm : (0 : ℝ) < ((Nat.lcm (Nat.lcm r a) c).totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hm1
      have hφn : (0 : ℝ) < ((Nat.lcm r (e / a)).totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hn1
      have hφr : (0 : ℝ) < (r.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hr1
      have hcast : (r.totient : ℝ) * (r.totient : ℝ) * ((e.totient : ℝ) * (c.totient : ℝ))
          ≤ (Nat.gcd r (c * e) : ℝ) * (c : ℝ)
            * (((Nat.lcm (Nat.lcm r a) c).totient : ℝ) * ((Nat.lcm r (e / a)).totient : ℝ)) := by
        exact_mod_cast totient_sq_mul_le_gcd_mul_totient_lcm_mul e a c r hesf hae hcb
      calc (r.totient : ℝ) * (|innerMoebiusSum x F B (Nat.lcm (Nat.lcm r a) c)|
            * |innerMoebiusSum x G B (Nat.lcm r (e / a))|)
          ≤ (r.totient : ℝ) * ((CF * (Wr / φW) / (((Nat.lcm (Nat.lcm r a) c).totient : ℝ) * L))
            * (CG * (Wr / φW) / (((Nat.lcm r (e / a)).totient : ℝ) * L))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hxF B _ hB hm1) (hxG B _ hB hn1)
              (abs_nonneg _) (by positivity)) hφr.le
        _ = K₁ * ((r.totient : ℝ)
              / (((Nat.lcm (Nat.lcm r a) c).totient : ℝ) * ((Nat.lcm r (e / a)).totient : ℝ))) := by
            rw [hK₁def]; field_simp
        _ ≤ K₁ * ((Nat.gcd r (c * e) : ℝ) * (c : ℝ)
              / ((r.totient : ℝ) * (e.totient : ℝ) * (c.totient : ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_ hK₁0
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hcast]
    -- the three divisor factors
    have hfac1 : (c : ℝ) / (c.totient : ℝ) ≤ 2 ^ w :=
      self_div_totient_le_two_pow_card_primeFactors he0 hce hc0.ne'
    have hfac2 : (1 : ℝ) / (e.totient : ℝ) ≤ 2 ^ w / (e : ℝ) := by
      rw [div_le_div_iff₀ hφe heR]
      have := self_div_totient_le_two_pow_card_primeFactors he0 dvd_rfl he0
      rw [div_le_iff₀ hφe] at this
      linarith
    have hfac3 : ∑ k ∈ (c * e).divisors, (k : ℝ) / (k.totient : ℝ) ≤ 8 ^ w :=
      sum_divisors_self_div_totient_le hesf (mul_dvd_mul hce dvd_rfl) (Nat.mul_ne_zero hc0.ne' he0)
    have hgcdsum := sum_gcd_div_totient_le (W x) N₀ (c * e) (Nat.mul_ne_zero hc0.ne' he0)
    rw [← hS'def, ← hMsdef] at hgcdsum
    have hcc : (c : ℝ) / ((e.totient : ℝ) * (c.totient : ℝ))
        * ∑ k ∈ (c * e).divisors, (k : ℝ) / (k.totient : ℝ) ≤ (32 : ℝ) ^ w / (e : ℝ) := by
      calc (c : ℝ) / ((e.totient : ℝ) * (c.totient : ℝ))
            * ∑ k ∈ (c * e).divisors, (k : ℝ) / (k.totient : ℝ)
          = (c : ℝ) / (c.totient : ℝ) * ((1 : ℝ) / (e.totient : ℝ))
            * ∑ k ∈ (c * e).divisors, (k : ℝ) / (k.totient : ℝ) := by ring
        _ ≤ 2 ^ w * (2 ^ w / (e : ℝ)) * 8 ^ w := mul_le_mul
            (mul_le_mul hfac1 hfac2 (by positivity) (by positivity)) hfac3
            (Finset.sum_nonneg fun k _ ↦ by positivity) (by positivity)
        _ = (32 : ℝ) ^ w / (e : ℝ) := by
            rw [show (32 : ℝ) = 2 * 2 * 8 by norm_num, mul_pow, mul_pow]; ring
    calc ∑ r ∈ S', (r.totient : ℝ) * (|innerMoebiusSum x F B (Nat.lcm (Nat.lcm r a) c)|
          * |innerMoebiusSum x G B (Nat.lcm r (e / a))|)
        ≤ ∑ r ∈ S', K₁ * ((Nat.gcd r (c * e) : ℝ) * (c : ℝ)
            / ((r.totient : ℝ) * (e.totient : ℝ) * (c.totient : ℝ))) := Finset.sum_le_sum hterm
      _ = K₁ * ((c : ℝ) / ((e.totient : ℝ) * (c.totient : ℝ)))
            * ∑ r ∈ S', (Nat.gcd r (c * e) : ℝ) / (r.totient : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun r _ ↦ by ring
      _ ≤ K₁ * ((c : ℝ) / ((e.totient : ℝ) * (c.totient : ℝ)))
            * ((∑ k ∈ (c * e).divisors, (k : ℝ) / (k.totient : ℝ)) * Ms) := by gcongr
      _ = K₁ * ((c : ℝ) / ((e.totient : ℝ) * (c.totient : ℝ))
            * ∑ k ∈ (c * e).divisors, (k : ℝ) / (k.totient : ℝ)) * Ms := by ring
      _ ≤ K₁ * ((32 : ℝ) ^ w / (e : ℝ)) * Ms :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcc hK₁0) hMs0
  -- sum the classes
  have hdivcard : ∀ n : ℕ, n ∣ e → (#n.divisors : ℝ) ≤ (2 : ℝ) ^ w := fun n hn ↦ by
    have h1 := Finset.card_le_card (Nat.divisors_subset_of_dvd he0 hn)
    rw [card_divisors_of_squarefree hesf] at h1
    exact_mod_cast h1
  have h32 : 0 ≤ K₁ * ((32 : ℝ) ^ w / (e : ℝ)) := mul_nonneg hK₁0 (by positivity)
  refine (abs_restrictedSum_le_sum_divisors F G B hesf).trans ?_
  calc ∑ a ∈ e.divisors, ∑ c ∈ (e / a).divisors, ∑ r ∈ Icc 1 B, (r.totient : ℝ)
          * (|innerMoebiusSum x F B (Nat.lcm (Nat.lcm r a) c)|
            * |innerMoebiusSum x G B (Nat.lcm r (e / a))|)
      ≤ ∑ a ∈ e.divisors, ∑ _c ∈ (e / a).divisors, K₁ * ((32 : ℝ) ^ w / (e : ℝ)) * Ms :=
        Finset.sum_le_sum fun a ha ↦ Finset.sum_le_sum (hkey a ha)
    _ ≤ ∑ _a ∈ e.divisors, (2 : ℝ) ^ w * (K₁ * ((32 : ℝ) ^ w / (e : ℝ)) * Ms) :=
        Finset.sum_le_sum fun a ha ↦ by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right
            (hdivcard _ (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors ha))) (mul_nonneg h32 hMs0)
    _ ≤ (2 : ℝ) ^ w * ((2 : ℝ) ^ w * (K₁ * ((32 : ℝ) ^ w / (e : ℝ)) * Ms)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hdivcard e dvd_rfl)
          (mul_nonneg (by positivity) (mul_nonneg h32 hMs0))
    _ ≤ (2 : ℝ) ^ w * ((2 : ℝ) ^ w
          * (K₁ * ((32 : ℝ) ^ w / (e : ℝ)) * ((β + C₀) * (φW / Wr * L)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hMs h32) (by positivity)) (by positivity)
    _ = CF * CG * (β + C₀) * (Wr / φW) / L * ((128 : ℝ) ^ w / (e : ℝ)) := by
        rw [hK₁def, show (128 : ℝ) = 2 * 2 * 32 by norm_num, mul_pow, mul_pow]
        field_simp
    _ ≤ CF * CG * (β + C₀) * (Wr / φW) / L * (1 / (e : ℝ) ^ (3 / 4 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_div_iff₀ heR hrpow, one_mul]
        calc (128 : ℝ) ^ w * (e : ℝ) ^ (3 / 4 : ℝ)
            ≤ (e : ℝ) ^ (1 / 4 : ℝ) * (e : ℝ) ^ (3 / 4 : ℝ) := by gcongr
          _ = (e : ℝ) := by rw [← Real.rpow_add heR]; norm_num
    _ = CF * CG * (β + C₀) / (φW / Wr * L * (e : ℝ) ^ (3 / 4 : ℝ)) := by field_simp

/-- **The sieving error, from the one-variable Möbius bound.** This is
`Gap212.Sieve.oneCoordLcmDecayAtLevelOfSupport_of_smoothMoebiusInnerBound` fed to
`Gap212.Sieve.tendsto_boxPairSum_sub_sievedPairSum_of_support` at `s = 3/4`, which is admissible
because `1/2 < 3/4`: the conclusion is the content of `Gap212.Sieve.SelbergSievingError m`, which
is stated at `β ≥ 1`. So `Gap212.Sieve.SmoothMoebiusInnerBound` — a bound on a *one-variable*
Möbius sum — is the single input for the Selberg sieving error. That input is proved, so
`Gap212.Sieve.tendsto_boxPairSum_sub_sievedPairSum` is this statement with the hypothesis
discharged, and `Gap212.Sieve.selbergSievingError` follows. -/
theorem tendsto_boxPairSum_sub_sievedPairSum_of_smoothMoebiusInnerBound
    (hin : SmoothMoebiusInnerBound) (p : SupportParams) {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) {m : ℕ}
    {j j' : Fin p.n} (F G : Fin (m + 1) → ℝ → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    (hFc : ∀ i, HasCompactSupport (F i)) (hG : ∀ i, ContDiff ℝ 1 (G i))
    (hGc : ∀ i, HasCompactSupport (G i)) (hsupp : IsRetreatedPair p (m + 1) j j' ε₀ F G)
    {β : ℝ} (hβ1 : 1 ≤ β) (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦ (((W x).totient : ℝ) / (W x : ℝ) * Real.log x) ^ (m + 1) *
        (boxPairSum x (B x) F G - sievedPairSum x (B x) F G)) atTop (nhds 0) :=
  tendsto_boxPairSum_sub_sievedPairSum_of_support (by norm_num)
    (oneCoordLcmDecayAtLevelOfSupport_of_smoothMoebiusInnerBound hin) p hε₀ F G hF hFc hG hGc
    hsupp hβ1 B hB

end Gap212.Sieve
