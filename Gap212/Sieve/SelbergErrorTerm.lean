/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.DivisorMoment
public import Gap212.Sieve.SelbergProgressionSum

/-!
# The denominator divisor sum: the error term

The last step in the evaluation of the denominator divisor sum, in full. The error
left by replacing each divisor pair's count by `x/q` is `O(1)` per pair
(`Gap212.Sieve.card_pair_le` and its companion lower bound), so the whole error is `O` of the
number of pairs that contribute at all. A pair contributes only if both its logarithmic size
vectors lie in their retreat regions, and then

* `∏ᵢ dᵢd'ᵢ ≤ x^{(1-ε₀)S}` with `S = (A_j+ε) + (A_{j'}+ε) < 1`
  (`Gap212.Sieve.prod_pair_le_rpow_of_mem_retreatRegion`);
* the pairs of `k`-tuples of positive integers with `∏ᵢ dᵢd'ᵢ ≤ N` number at most
  `N(1+\log N)^{2k-1}` (`Gap212.Sieve.card_pairs_le_of_prod_le`, the divisor-moment bound
  `∑_{m≤N}τ_{2k}(m)` in the form `Gap212.Sieve.card_finMulAntidiagLE_le` proves);
* `x^σ(1+σ\log x)^{r}` is `o(x/(\log x)^{m})` for every `σ < 1` and every `r, m`
  (`Gap212.Sieve.rpow_mul_one_add_mul_log_isLittleO`), and `𝓒_x ≥ x/(\log x)^{k+1}` by
  `Gap212.Sieve.calC_lower_bound`.

So the count of contributing pairs is `o(𝓒_x)`, which is the error term.

## What is `S` here, and why the exponent is `(1-ε₀)S` rather than `S`

The natural way to run the count is at `q ≤ x^S`, which is what
`Gap212.Sieve.denominator_modulus_exponent` delivers for the modulus `W(x)∏ᵢ[dᵢ,d'ᵢ]`. The count
below is of tuples, not of moduli, so what it needs is a bound on `∏ᵢ dᵢd'ᵢ`, and for that the
retreat regions give the sharper `(1-ε₀)S` directly — the `ε₀` of
`Gap212.Sieve.denominator_modulus_exponent` is spent on absorbing `W(x)`, which does not appear
here. Both exponents are below `1`, which is all the error term uses.

## Main results

* `Gap212.Sieve.card_pairs_le_of_prod_le`: the divisor-moment count of pairs.
* `Gap212.Sieve.rpow_mul_one_add_mul_log_isLittleO`: the analytic estimate `σ < 1` buys.
* `Gap212.Sieve.card_contributing_isLittleO_calC`: the error term — the number of contributing
  divisor pairs is `o(𝓒_x)`.
* `Gap212.Sieve.abs_card_dyadic_filter_modEq_sub_le`: the two-sided per-pair count,
  `|N_q - x/q| ≤ 2`.
-/

@[expose] public section

namespace Gap212.Sieve

open Asymptotics Filter Finset Gap212.Defs Gap212.GPY

/-! ## Counting pairs of divisor tuples of bounded product -/

/-- **The divisor-moment count, in pair form.** Any finite collection of pairs of `k`-tuples of
positive integers with `∏ᵢ dᵢd'ᵢ ≤ N` has at most `N(1 + \log N)^{2k-1}` members.

This is the divisor-moment bound `∑_{m ≤ N}τ_{2k}(m) ≪ N(\log N)^{2k-1}`: concatenating the two
`k`-tuples into one `2k`-tuple is an injection into `Nat.finMulAntidiagLE (Fin 2k) N`, whose
cardinality `Gap212.Sieve.card_finMulAntidiagLE_le` bounds with constant `1`. -/
theorem card_pairs_le_of_prod_le {k : ℕ} (hk : 1 ≤ k) {N : ℕ}
    (T : Finset ((Fin k → ℕ) × (Fin k → ℕ)))
    (hT : ∀ dd ∈ T, (∀ i, 0 < dd.1 i) ∧ (∀ i, 0 < dd.2 i) ∧
      (∏ i, dd.1 i) * (∏ i, dd.2 i) ≤ N) :
    (#T : ℝ) ≤ (N : ℝ) * (1 + Real.log N) ^ (2 * k - 1) := by
  classical
  have hkk : k + k = (2 * k - 1) + 1 := by omega
  -- Concatenation is an injection into the tuples of product at most `N`.
  have hcard : #T ≤ #(Nat.finMulAntidiagLE (Fin (k + k)) N) := by
    refine Finset.card_le_card_of_injOn (fun dd ↦ Fin.append dd.1 dd.2) ?_ ?_
    · intro dd hdd
      obtain ⟨h1, h2, h3⟩ := hT dd hdd
      refine Nat.mem_finMulAntidiagLE_iff.mpr ⟨?_, ?_⟩
      · rw [Fin.prod_univ_add]
        simpa only [Fin.append_left, Fin.append_right] using h3
      · refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_)
        · simpa only [Fin.append_left] using (h1 i).ne'
        · simpa only [Fin.append_right] using (h2 i).ne'
    · intro dd _ ee _ heq
      exact Prod.ext
        (funext fun i ↦ by simpa only [Fin.append_left] using congrFun heq (Fin.castAdd k i))
        (funext fun i ↦ by simpa only [Fin.append_right] using congrFun heq (Fin.natAdd k i))
  exact (Nat.cast_le.2 hcard).trans (hkk ▸ card_finMulAntidiagLE_le (2 * k - 1) N)

/-! ## The analytic estimate `σ < 1` buys -/

/-- A power of `\log x` is `o(x^δ)` for every `δ > 0`. Mathlib's
`Real.isLittleO_log_rpow_rpow_atTop` with the real exponent read as a natural one. -/
theorem log_pow_isLittleO_rpow {δ : ℝ} (hδ : 0 < δ) (P : ℕ) :
    (fun x : ℝ ↦ Real.log x ^ P) =o[atTop] (fun x : ℝ ↦ x ^ δ) :=
  (isLittleO_log_rpow_rpow_atTop (P : ℝ) hδ).congr_left fun x ↦
    Real.rpow_natCast (Real.log x) P

/-- **The estimate the exponent `σ < 1` buys**: `x^σ(1 + c\log x)^r = o(x/(\log x)^m)` for every
`σ ∈ [0,1)`, every `c ≥ 0` and all natural `r, m`.

The saving is the whole power `x^{1-σ}`, against which the `r + m` accumulated powers of `\log x`
are negligible. This is the step where `S < 1` is spent, and it is the only place
the error term needs analysis rather than counting. -/
theorem rpow_mul_one_add_mul_log_isLittleO {σ c : ℝ} (hσ1 : σ < 1) (hc : 0 ≤ c) (r m : ℕ) :
    (fun x : ℝ ↦ x ^ σ * (1 + c * Real.log x) ^ r) =o[atTop]
      (fun x : ℝ ↦ x / Real.log x ^ m) := by
  have hδ : 0 < 1 - σ := by linarith
  have hK : (0 : ℝ) < (1 + c) ^ r := by positivity
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [(log_pow_isLittleO_rpow hδ (r + m)).bound (c := ε / (1 + c) ^ r) (by positivity),
    eventually_ge_atTop (Real.exp 1)] with x hx hxe
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxe
  have hL1 : 1 ≤ Real.log x := by simpa using Real.log_le_log (Real.exp_pos 1) hxe
  set L := Real.log x
  have hLm : 0 < L ^ m := by positivity
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hx
  -- The `(1 + cL)^r` factor is at most `(1+c)^r L^r`.
  have hstep : (1 + c * L) ^ r ≤ (1 + c) ^ r * L ^ r := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) r
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), mul_div_assoc',
    le_div_iff₀ hLm]
  calc x ^ σ * (1 + c * L) ^ r * L ^ m
      ≤ x ^ σ * ((1 + c) ^ r * L ^ r) * L ^ m := by gcongr
    _ = x ^ σ * ((1 + c) ^ r * L ^ (r + m)) := by ring
    _ ≤ x ^ σ * ((1 + c) ^ r * (ε / (1 + c) ^ r * x ^ (1 - σ))) := by gcongr
    _ = ε * (x ^ σ * x ^ (1 - σ)) := by field_simp
    _ = ε * x := by rw [← Real.rpow_add hx0]; simp

/-! ## The product of a pair confined to the retreat regions -/

/-- **A tuple confined to a retreat region has small product**: if every `logScale x (dᵢ)` vector
of a positive tuple lies in `R⁺_k(j,ε₀)`, then `∏ᵢdᵢ ≤ x^{(1-ε₀)(A_j+ε)}`.

The region's total-mass clause is exactly this bound after `dᵢ = x^{\log_x dᵢ}`. -/
theorem prod_le_rpow_of_mem_retreatRegion {p : SupportParams} {k : ℕ} {j : Fin p.n} {ε₀ x : ℝ}
    (hx : 1 < x) {d : Fin k → ℕ} (hd : ∀ i, 0 < d i)
    (hmem : (fun i ↦ logScale x (d i)) ∈ retreatRegion p k j ε₀) :
    (∏ i, (d i : ℝ)) ≤ x ^ ((1 - ε₀) * (p.A j.succ + p.ε)) := by
  rw [prod_cast_eq_rpow_sum hx hd Finset.univ]
  exact Real.rpow_le_rpow_of_exponent_le hx.le hmem.2.1.le

/-- **A contributing pair has small product.** With the two tuples confined to the retreat regions
of bands `j` and `j'`, `∏ᵢdᵢd'ᵢ ≤ x^{(1-ε₀)S}` at `S = (A_j+ε) + (A_{j'}+ε)`.

This is the tuple-side companion of `Gap212.Sieve.denominator_modulus_exponent`, which bounds the
*modulus* `W(x)∏ᵢ[dᵢ,d'ᵢ]` by `x^S`. The exponent here is the sharper `(1-ε₀)S`, because no `W(x)`
has to be absorbed. -/
theorem prod_pair_le_rpow_of_mem_retreatRegion {p : SupportParams} {k : ℕ} {j j' : Fin p.n}
    {ε₀ x : ℝ} (hx : 1 < x) {d d' : Fin k → ℕ} (hd : ∀ i, 0 < d i) (hd' : ∀ i, 0 < d' i)
    (hmem : (fun i ↦ logScale x (d i)) ∈ retreatRegion p k j ε₀)
    (hmem' : (fun i ↦ logScale x (d' i)) ∈ retreatRegion p k j' ε₀) :
    (∏ i, (d i : ℝ)) * (∏ i, (d' i : ℝ))
      ≤ x ^ ((1 - ε₀) * ((p.A j.succ + p.ε) + (p.A j'.succ + p.ε))) := by
  rw [mul_add, Real.rpow_add (by linarith)]
  exact mul_le_mul (prod_le_rpow_of_mem_retreatRegion hx hd hmem)
    (prod_le_rpow_of_mem_retreatRegion hx hd' hmem') (by positivity) (by positivity)

/-! ## The error term -/

/-- **The error term of the denominator divisor sum.** Let `p` be a support datum, `ε₀ ∈ (0,1)` and
`j, j'` two bands, and let `T x` be *any* finite collection of pairs of positive `k`-tuples
(`k = m + 1`) whose logarithmic size vectors lie in the two retreat regions. Then

  `#(T x) = o(𝓒_x)`.

The pairs are counted by the divisor-moment bound
`Gap212.Sieve.card_pairs_le_of_prod_le` at `N = ⌊x^σ⌋` with `σ = (1-ε₀)S < 1`
(`Gap212.Sieve.prod_pair_le_rpow_of_mem_retreatRegion`), which gives
`#(T x) ≤ x^σ(1+σ\log x)^{2k-1}`; that is `o(x/(\log x)^{k+1})` by
`Gap212.Sieve.rpow_mul_one_add_mul_log_isLittleO`, and `𝓒_x` is at least `x/(\log x)^{k+1}` by
`Gap212.Sieve.calC_lower_bound`.

Since the count a single pair contributes differs from `x/q` by at most `2`
(`Gap212.Sieve.abs_card_dyadic_filter_modEq_sub_le`) and the Möbius coefficients are bounded, the
whole error is a fixed constant times this count — `Asymptotics.IsLittleO.const_mul_left` — so this
is the error term itself and not merely a count.

The hypothesis is eventual in `x`, which is what the support clauses supply. -/
theorem card_contributing_isLittleO_calC (p : SupportParams) (m : ℕ) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) (j j' : Fin p.n)
    (T : ℝ → Finset ((Fin (m + 1) → ℕ) × (Fin (m + 1) → ℕ)))
    (hT : ∀ᶠ x : ℝ in atTop, ∀ dd ∈ T x, (∀ i, 0 < dd.1 i) ∧ (∀ i, 0 < dd.2 i) ∧
      (fun i ↦ logScale x (dd.1 i)) ∈ retreatRegion p (m + 1) j ε₀ ∧
      (fun i ↦ logScale x (dd.2 i)) ∈ retreatRegion p (m + 1) j' ε₀) :
    (fun x : ℝ ↦ (#(T x) : ℝ)) =o[atTop] (fun x : ℝ ↦ calC m x) := by
  classical
  -- Each band's node, shifted by `ε`, is positive and below `1/2`; so `0 < S < 1`.
  have node : ∀ b : Fin p.n, 0 < p.A b.succ + p.ε ∧ p.A b.succ + p.ε < 1 / 2 := fun b ↦ by
    constructor <;> linarith [p.A_zero, p.A_last, p.A_mono (Fin.succ_pos b),
      p.A_mono.monotone (Fin.le_last b.succ)]
  set S := (p.A j.succ + p.ε) + (p.A j'.succ + p.ε)
  have hS0 : 0 < S := by linarith [(node j).1, (node j').1]
  have hS1 : S < 1 := by linarith [(node j).2, (node j').2]
  set σ := (1 - ε₀) * S
  have hσ0 : 0 ≤ σ := mul_nonneg (by linarith) hS0.le
  have hσ1 : σ < 1 := (mul_lt_of_lt_one_left hS0 (by linarith)).trans hS1
  set r := 2 * (m + 1) - 1
  -- The count is at most `x^σ (1 + σ log x)^r`.
  have hcount : ∀ᶠ x : ℝ in atTop,
      ‖(#(T x) : ℝ)‖ ≤ 1 * ‖x ^ σ * (1 + σ * Real.log x) ^ r‖ := by
    filter_upwards [hT, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hx0 : (0 : ℝ) < x := by linarith
    set N := ⌊x ^ σ⌋₊
    have hN1 : 1 ≤ N := Nat.le_floor (by simpa using Real.one_le_rpow hx1.le hσ0)
    have hNle : (N : ℝ) ≤ x ^ σ := Nat.floor_le (by positivity)
    -- The divisor-moment bound at `N`.
    have hbound : (#(T x) : ℝ) ≤ (N : ℝ) * (1 + Real.log N) ^ r := by
      refine card_pairs_le_of_prod_le (k := m + 1) (Nat.le_add_left 1 m) (T x) fun dd hdd ↦ ?_
      obtain ⟨h1, h2, h3, h4⟩ := hx dd hdd
      exact ⟨h1, h2, Nat.le_floor <| by
        exact_mod_cast prod_pair_le_rpow_of_mem_retreatRegion hx1 h1 h2 h3 h4⟩
    -- `log N ≤ σ log x`.
    have hlogN : Real.log N ≤ σ * Real.log x :=
      (Real.log_le_log (by exact_mod_cast hN1) hNle).trans_eq (Real.log_rpow hx0 _)
    have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
    have hpow0 : (0 : ℝ) ≤ (1 + σ * Real.log x) ^ r := pow_nonneg (by linarith) r
    rw [one_mul, Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (mul_nonneg (by positivity) hpow0)]
    exact hbound.trans (by gcongr)
  -- `x/(log x)^{m+2}` is at most `𝓒_x`.
  have hcalC : ∀ᶠ x : ℝ in atTop,
      ‖x / Real.log x ^ (m + 2)‖ ≤ 1 * ‖calC m x‖ := by
    filter_upwards [calC_lower_bound m] with x hx
    rw [one_mul, Real.norm_of_nonneg hx.2.le,
      Real.norm_of_nonneg (le_trans hx.2.le hx.1)]
    exact hx.1
  exact ((Asymptotics.IsBigO.of_bound 1 hcount).trans_isLittleO
    (rpow_mul_one_add_mul_log_isLittleO hσ1 hσ0 r (m + 2))).trans_isBigO
      (Asymptotics.IsBigO.of_bound 1 hcalC)

/-! ## The per-pair error is `O(1)` -/

/-- **The two-sided count of one class in the dyadic block**: for `x ≥ 1` and `q ≥ 1`,

  `|#{n ∈ [x,2x] : n ≡ a (q)} - x/q| ≤ 2`.

The upper half is `Gap212.Sieve.card_dyadic_filter_modEq_le`; the lower half is
`Gap212.Sieve.card_filter_modEq_ge`, whose natural-number division costs one more unit. This is the
usual "the number of `n ∈ [x,2x]` in one class modulo `q` is `x/q + O(1)`", with the constant
made explicit — and it is what makes the error a fixed multiple of the number of contributing
pairs. -/
theorem abs_card_dyadic_filter_modEq_sub_le {x : ℝ} (hx : 1 ≤ x) {q a : ℕ} (hq : 0 < q) :
    |(#{n ∈ dyadic x | n ≡ a [MOD q]} : ℝ) - x / q| ≤ 2 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hupper : (#{n ∈ dyadic x | n ≡ a [MOD q]} : ℝ) ≤ x / q + 1 :=
    card_dyadic_filter_modEq_le (by linarith) hq
  -- The lower bound, through the sharp count of one class in a block.
  have hce : (⌈x⌉₊ : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hfl : 2 * x - 1 ≤ (⌊2 * x⌋₊ : ℝ) := (Nat.sub_one_lt_floor (2 * x)).le
  have hMcast : (x : ℝ) - 1 ≤ ((⌊2 * x⌋₊ + 1 - ⌈x⌉₊ : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by exact_mod_cast (by linarith : (⌈x⌉₊ : ℝ) ≤ ⌊2 * x⌋₊ + 1))]
    push_cast
    linarith
  set M := ⌊2 * x⌋₊ + 1 - ⌈x⌉₊
  have hdiv : (M : ℝ) / q - 1 ≤ ((M / q : ℕ) : ℝ) :=
    Nat.floor_div_eq_div (K := ℝ) M q ▸ (Nat.sub_one_lt_floor _).le
  have hlow : ((M / q : ℕ) : ℝ) ≤ (#{n ∈ dyadic x | n ≡ a [MOD q]} : ℝ) := by
    rw [Gap212.dyadic]
    exact_mod_cast card_filter_modEq_ge (A := ⌈x⌉₊) (B := ⌊2 * x⌋₊) (a := a) hq
  have hxq : x / q - 1 / q ≤ (M : ℝ) / q := sub_div x 1 q ▸ div_le_div_of_nonneg_right hMcast hq'.le
  have h1q : (1 : ℝ) / q ≤ 1 := div_le_one_of_le₀ hq1 hq'.le
  exact abs_le.2 ⟨by linarith, by linarith⟩

end Gap212.Sieve
