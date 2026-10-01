/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.DivisorSumAssembly
public import Gap212.Sieve.NuDenominatorFromObligations
public import Gap212.Sieve.NumeratorFromObligations
public import Gap212.Sieve.ScaleCalC
public import Gap212.Sieve.SelbergErrorTerm
public import Gap212.Sieve.SmoothTotientInner
public import Gap212.Sieve.WeightedError
public meta import Gap212.Attr

/-!
# The sieve asymptotic, from the divisor sum over `Q⋆` and the weighted error

`Gap212.Sieve.SieveAsymptotic` is the asymptotic for the sieve sum weighted by `ρ(n + h_{i₀})`.
This module proves it, at `k = 45`, from `Gap212.Sieve.divisor_sum_over_qstar` and
`Gap212.Sieve.weighted_error_negligible`.

## Main results

* `Gap212.Sieve.sieveAsymptotic_of_obligations`: `SieveAsymptotic 44`, granting the two hypotheses
  `Gap212.Sieve.TotientGramSumLimitOfSupport` and `Gap212.Sieve.TotientSievingError 44` of
  `Gap212.Sieve.divisor_sum_over_qstar`.
* `Gap212.Sieve.sieveAsymptotic_of_totientGramSumLimitOfSupport`,
  `Gap212.Sieve.numeratorAsymptotic_of_totientGramSumLimitOfSupport`: the same, on the first of
  those two alone, the second being `Gap212.Sieve.totientSievingError`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Real Gap212.Defs Gap212.GPY MeasureTheory
open scoped ArithmeticFunction.Moebius

/-! ## The weighted divisor expansion

`Gap212.Sieve.sum_prod_lambdaF_pair` interchanges the `n`-sum with the divisor expansion for the
*unweighted* block sum, leaving a cardinality. The numerator carries the weight `ρ(n + h_{i₀};x)`,
so what is left of a divisor pair is a weighted count rather than a count. -/

/-- **The interchange, with a weight.** For any weight `w` and any finite set `S` of integers whose
shifts are positive and bounded by `B`, the weighted sum over `S` of the `2k`-fold divisor weight
is a sum over *pairs* of divisor tuples in `[1,B]^k` of the Möbius coefficient against the weight
of the members of `S` the pair divides.

This is `Gap212.Sieve.sum_prod_lambdaF_pair` with `Finset.card` replaced by `∑ w`; at `w = 1` the
two agree. -/
theorem sum_weighted_prod_lambdaF_pair {k : ℕ} {x : ℝ} {B : ℕ} (S : Finset ℕ) (w : ℕ → ℝ)
    (h : Fin k → ℕ) (F G : Fin k → ℝ → ℝ) (hN : ∀ n ∈ S, ∀ i, 0 < n + h i)
    (hB : ∀ n ∈ S, ∀ i, n + h i ≤ B) :
    ∑ n ∈ S, w n * ∏ i, lambdaF (F i) x (n + h i) * lambdaF (G i) x (n + h i)
      = ∑ d ∈ Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 B),
          ∑ d' ∈ Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 B),
            (∏ i, (μ (d i) : ℝ) * F i (Gap212.Notation.logx x (d i))) *
              (∏ i, (μ (d' i) : ℝ) * G i (Gap212.Notation.logx x (d' i))) *
              (∑ n ∈ S with (∀ i, d i ∣ n + h i) ∧ (∀ i, d' i ∣ n + h i), w n) := by
  classical
  set box := Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 B) with hbox
  set A : (Fin k → ℕ) → ℝ := fun d ↦
    ∏ i, (μ (d i) : ℝ) * F i (Gap212.Notation.logx x (d i)) with hA
  set A' : (Fin k → ℕ) → ℝ := fun d ↦
    ∏ i, (μ (d i) : ℝ) * G i (Gap212.Notation.logx x (d i)) with hA'
  have step : ∀ n ∈ S, w n * ∏ i, lambdaF (F i) x (n + h i) * lambdaF (G i) x (n + h i)
      = ∑ d ∈ box, ∑ d' ∈ box,
          if (∀ i, d i ∣ n + h i) ∧ (∀ i, d' i ∣ n + h i) then A d * A' d' * w n else 0 := by
    intro n hn
    rw [prod_mul_distrib, prod_lambdaF_eq_box F x (hN n hn) (hB n hn),
      prod_lambdaF_eq_box G x (hN n hn) (hB n hn), sum_mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun d _ ↦ ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun d' _ ↦ ?_
    split_ifs <;> simp_all [mul_comm]
  rw [sum_congr rfl step, sum_comm]
  refine sum_congr rfl fun d _ ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun d' _ ↦ ?_
  rw [← sum_filter, ← Finset.mul_sum]

/-! ## The divisor weight at a prime -/

/-- **At a prime shift the divisor weight is the boundary value.** If `N` is prime and at least
`x`, and `F` vanishes from `1` on, then `λ_F(N) = F(0)`: the divisors of `N` are `1` and `N`, and
`log_x N ≥ 1` kills the second. -/
theorem lambdaF_of_prime {F : ℝ → ℝ} {x : ℝ} (hx : 1 < x) {N : ℕ} (hN : N.Prime)
    (hxN : x ≤ (N : ℝ)) (hF1 : ∀ t : ℝ, 1 ≤ t → F t = 0) :
    lambdaF F x N = F 0 := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hbig : (1 : ℝ) ≤ Gap212.Notation.logx x (N : ℕ) := by
    rw [Gap212.Notation.logx, le_div_iff₀ hlogx, one_mul]
    exact Real.log_le_log (lt_trans zero_lt_one hx) hxN
  rw [lambdaF, hN.divisors, Finset.sum_pair hN.one_lt.ne, hF1 _ hbig]
  simp [Gap212.Notation.logx, ArithmeticFunction.moebius_apply_prime hN]

/-! ## The identity joining the two normalizations

The divisor sum over `Q⋆` is normalized by `Gap212.Sieve.divisorSumNorm`, and the prime density
supplies `x/\log x`; their product is `𝓒_x`. That is the arithmetic behind
"`(1+o(1))(x/\log x)·(∏+o(1))W^{k-1}/(φ(W)^k(\log x)^{k-1}) = (∏+o(1))𝓒_x`". -/

/-- **The prime density times the divisor-sum normalization is `𝓒_x`.** -/
theorem density_mul_divisorSumNorm (m : ℕ) {x : ℝ} (hx : 1 < x) :
    x / Real.log x * divisorSumNorm m x = calC m x := by
  have hφ : (0 : ℝ) < ((W x).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (primorial_pos _)
  have hL : (0 : ℝ) < Real.log x := Real.log_pos hx
  rw [divisorSumNorm, calC]
  field_simp
  ring

/-! ## Splitting a class sum into its average and the dyadic discrepancy

`Gap212.sumErrorDyadic` subtracts `1/φ(q)` times the sum over the integers of the block
**coprime to `q`**, while the split used here subtracts `1/φ(q)` times the sum over all of
`𝓓(x)`. The two agree here because the weight's own support makes the coprimality automatic, which
the hypothesis `hcop` records. -/

/-- **The class sum is its average plus the discrepancy.** For a positive modulus `q` at which
every member of the block the weight does not annihilate is coprime, the sum of `ρ(·;x)` over a
class modulo `q` is `1/φ(q)` times its sum over the whole block, plus the real part of the dyadic
discrepancy of `Gap212.sumErrorDyadic`. -/
theorem sum_class_eq_average_add_discrepancy {x : ℝ} {ρ : ℕ → ℝ → ℝ} {q a : ℕ}
    (hcop : ∀ M ∈ dyadic x, ρ M x ≠ 0 → Nat.Coprime M q) :
    ∑ M ∈ dyadic x with M ≡ a [MOD q], ρ M x
      = (1 / (Nat.totient q : ℝ)) * ∑ M ∈ dyadic x, ρ M x
        + (sumErrorDyadic x (fun n ↦ ((ρ n x : ℝ) : ℂ)) q a).re := by
  classical
  have hcopsum : ∑ M ∈ dyadic x with Nat.Coprime M q, ρ M x = ∑ M ∈ dyadic x, ρ M x :=
    Finset.sum_filter_of_ne hcop
  have hcast : sumErrorDyadic x (fun n ↦ ((ρ n x : ℝ) : ℂ)) q a
      = (((∑ M ∈ dyadic x with M ≡ a [MOD q], ρ M x)
          - (1 / (Nat.totient q : ℝ)) * ∑ M ∈ dyadic x with Nat.Coprime M q, ρ M x : ℝ) : ℂ) := by
    rw [sumErrorDyadic]
    push_cast
    ring
  rw [hcast, Complex.ofReal_re, hcopsum]
  ring

/-! ## The edge the shift leaves

The inner sum runs over `m = n + h_{i₀}` for `n` in the block, hence over
`[⌈x⌉ + h_{i₀}, ⌊2x⌋ + h_{i₀}]`, while `Gap212.sumErrorDyadic` evaluates over the block itself.
The ranges differ in at most `h_{i₀}` integers at the lower end — the upper end costs nothing,
`ρ(·;x)` vanishing off the block — and `0 ≤ ρ ≤ 1` there. -/

/-- **The shift costs at most `H`.** The weighted class sum read at the shifted argument differs
from the class sum over the block by at most `H`. -/
theorem abs_shifted_class_sum_sub_le {x : ℝ} {ρ : ℕ → ℝ → ℝ}
    (hsupp : ∀ n : ℕ, n ∉ dyadic x → ρ n x = 0)
    (hmin : ∀ n ∈ dyadic x, 0 ≤ ρ n x ∧ ρ n x ≤ 1) (q a₀ H : ℕ) :
    |(∑ n ∈ dyadic x with n ≡ a₀ [MOD q], ρ (n + H) x)
        - ∑ M ∈ dyadic x with M ≡ a₀ + H [MOD q], ρ M x| ≤ (H : ℝ) := by
  classical
  set c := ⌈x⌉₊ with hc
  set d := ⌊2 * x⌋₊ with hd
  set f : ℕ → ℝ := fun M ↦ if M ≡ a₀ + H [MOD q] then ρ M x else 0 with hf
  have hf0 : ∀ M : ℕ, M ∉ dyadic x → f M = 0 := fun M hM ↦ by simp [hf, hsupp M hM]
  have hfabs : ∀ M : ℕ, |f M| ≤ 1 := by
    intro M
    by_cases hM : M ∈ dyadic x
    · obtain ⟨h1, h2⟩ := hmin M hM
      simp only [hf]
      split_ifs <;> simp [abs_of_nonneg h1, h2]
    · simp [hf0 M hM]
  have hdy : dyadic x = Finset.Icc c d := rfl
  -- The shifted sum, re-indexed.
  have h1 : (∑ n ∈ dyadic x with n ≡ a₀ [MOD q], ρ (n + H) x)
      = ∑ M ∈ Finset.Icc (c + H) (d + H), f M := by
    rw [hdy, Finset.sum_filter, ← Finset.map_add_right_Icc, Finset.sum_map]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    simp only [hf, addRightEmbedding_apply]
    refine if_congr ⟨fun hn ↦ hn.add_right H, fun hn ↦ Nat.ModEq.add_right_cancel' H hn⟩ rfl rfl
  -- Its upper edge costs nothing: the weight vanishes above the block.
  have h2 : ∑ M ∈ Finset.Icc (c + H) (d + H), f M = ∑ M ∈ Finset.Icc (c + H) d, f M := by
    refine (Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega)) fun M hM hnot ↦ ?_).symm
    refine hf0 M fun hMd ↦ hnot ?_
    simp only [hdy, Finset.mem_Icc] at hMd hM ⊢
    omega
  have h3 : (∑ M ∈ dyadic x with M ≡ a₀ + H [MOD q], ρ M x) = ∑ M ∈ Finset.Icc c d, f M := by
    rw [hdy, Finset.sum_filter]
  -- What is left is the lower edge, of at most `H` integers.
  have hsub : Finset.Icc (c + H) d ⊆ Finset.Icc c d := Finset.Icc_subset_Icc (by omega) le_rfl
  have h4 : (∑ M ∈ Finset.Icc c d, f M) - ∑ M ∈ Finset.Icc (c + H) d, f M
      = ∑ M ∈ Finset.Icc c d \ Finset.Icc (c + H) d, f M := (Finset.sum_sdiff_eq_sub hsub).symm
  have hsub2 : Finset.Icc c d \ Finset.Icc (c + H) d ⊆ Finset.Ico c (c + H) := by
    intro M hM
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ico] at hM ⊢
    omega
  have hcard : #(Finset.Icc c d \ Finset.Icc (c + H) d) ≤ H :=
    (Finset.card_le_card hsub2).trans (by simp)
  rw [h1, h2, h3, abs_sub_comm, h4]
  refine (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_card_nsmul _ _ 1 fun M _ ↦ hfabs M).trans ?_)
  rw [nsmul_eq_mul, mul_one]
  exact_mod_cast hcard

/-! ## The degenerate branch: a factor vanishing on `[0,∞)`

`Gap212.Sieve.exists_null_or_forall_eq_zero_of_one_le` splits a retreated family into the case
where some factor vanishes on the whole nonnegative axis — where both sides of the asymptotic are
identically zero — and the case where every factor vanishes from `1` on, which is what the prime
collapse consumes. -/

/-- **A null profile kills its divisor weight.** `λ_F` samples `F` only at the nonnegative points
`log_x d`. -/
theorem lambdaF_eq_zero_of_null {F : ℝ → ℝ} {x : ℝ} (hx : 1 < x)
    (hF : ∀ t : ℝ, 0 ≤ t → F t = 0) (N : ℕ) : lambdaF F x N = 0 := by
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
  have hnn : (0 : ℝ) ≤ Gap212.Notation.logx x d :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hd1)) (Real.log_nonneg hx.le)
  rw [hF _ hnn, mul_zero]

/-- **Two pairs of profiles agreeing on `[0,∞)` have the same Gram integral.** The derivative at a
positive point is determined by the values at nearby positive points. -/
theorem setIntegral_deriv_congr_nonneg {F₁ F₂ G₁ G₂ : ℝ → ℝ}
    (hF : ∀ t : ℝ, 0 ≤ t → F₁ t = F₂ t) (hG : ∀ t : ℝ, 0 ≤ t → G₁ t = G₂ t) :
    ∫ t in Set.Ioi (0 : ℝ), deriv F₁ t * deriv G₁ t
      = ∫ t in Set.Ioi (0 : ℝ), deriv F₂ t * deriv G₂ t := by
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  have hnhds : ∀ H H' : ℝ → ℝ, (∀ u : ℝ, 0 ≤ u → H u = H' u) → deriv H t = deriv H' t := by
    intro H H' hHH'
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [eventually_gt_nhds ht] with u hu using hHH' u hu.le
  rw [hnhds _ _ hF, hnhds _ _ hG]

/-- **A null profile kills its Gram integral.** -/
theorem setIntegral_deriv_eq_zero_of_null {F G : ℝ → ℝ} (hF : ∀ t : ℝ, 0 ≤ t → F t = 0) :
    ∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t = 0 := by
  rw [setIntegral_deriv_congr_nonneg (F₂ := fun _ ↦ (0 : ℝ)) (G₂ := G) hF fun _ _ ↦ rfl]
  simp

/-! ## The prime collapse

One route to `d_{i₀} = d'_{i₀} = 1` is the roughness of `ρ` against the retreat coordinate bound.
The minorant clause alone suffices, and more directly: a shift the
weight does not annihilate is **prime**, so its divisors are `1` and itself, and a retreated
profile vanishes at `\log_x` of the second, which is at least `1`. -/

/-- **The removed coordinate's two divisor weights are the boundary values.** For `n` in the block
and profiles vanishing from `1` on, the weighted product factors as `F_{i₀}(0)G_{i₀}(0)` times the
product over the remaining coordinates.

Either `ρ(n + h_{i₀};x) = 0` and both sides vanish, or `n + h_{i₀}` is prime by the minorant clause
of `Gap212.Defs.RhoHypotheses` — and at least `x` — so
`Gap212.Sieve.lambdaF_of_prime` evaluates its divisor weights. -/
theorem rho_mul_prod_lambdaF_eq {m : ℕ} {x : ℝ} (hx : 1 < x) {p : SupportParams} {ρ : ℕ → ℝ → ℝ}
    {β : ℝ} (hρ : RhoHypotheses p ρ β) {h : Fin (m + 1) → ℕ} (i₀ : Fin (m + 1))
    {F G : Fin (m + 1) → ℝ → ℝ} (hF1 : ∀ i, ∀ t : ℝ, 1 ≤ t → F i t = 0)
    (hG1 : ∀ i, ∀ t : ℝ, 1 ≤ t → G i t = 0) {n : ℕ} (hn : n ∈ dyadic x) :
    ρ (n + h i₀) x * ∏ i, lambdaF (F i) x (n + h i) * lambdaF (G i) x (n + h i)
      = F i₀ 0 * G i₀ 0 *
        (ρ (n + h i₀) x * ∏ s : Fin m, lambdaF (F (i₀.succAbove s)) x (n + h (i₀.succAbove s)) *
          lambdaF (G (i₀.succAbove s)) x (n + h (i₀.succAbove s))) := by
  rw [Fin.prod_univ_succAbove (fun i ↦ lambdaF (F i) x (n + h i) * lambdaF (G i) x (n + h i)) i₀]
  rcases eq_or_ne (ρ (n + h i₀) x) 0 with h0 | h0
  · rw [h0]; ring
  have hmem : n + h i₀ ∈ dyadic x := by_contra fun hc ↦ h0 (hρ.support x _ hc)
  have hprime : (n + h i₀).Prime := by
    obtain ⟨hlow, hhigh⟩ := hρ.minorant x hx _ hmem
    by_contra hnp
    rw [if_neg hnp] at hhigh
    exact h0 (le_antisymm hhigh hlow)
  have hge : x ≤ ((n + h i₀ : ℕ) : ℝ) := (Nat.le_ceil x).trans
    (by exact_mod_cast (Finset.mem_Icc.mp hn).1.trans (Nat.le_add_right n (h i₀)))
  rw [lambdaF_of_prime hx hprime hge (hF1 i₀), lambdaF_of_prime hx hprime hge (hG1 i₀)]
  ring

/-! ## The reduced retreat, from the support hypotheses of the sieve asymptotic -/

/-- **The `i₀`-removed families are `i₀`-retreated.** `Gap212.GPY.IsReducedRetreat` reads the two
products on the vector extended by `0` at `i₀`, and
`Gap212.Sieve.SieveAsymptotic`'s clauses are about the full products; the extension's `i₀`-th
factor is `F_{i₀}(0)`, so the crossing costs exactly the non-vanishing of the two boundary values —
and where one of them vanishes both sides of the asymptotic are zero anyway. -/
theorem isReducedRetreat_of_retreat {p : SupportParams} {m : ℕ} {j j' : Fin p.n} {ε₀ : ℝ}
    (i₀ : Fin (m + 1)) {F G : Fin (m + 1) → ℝ → ℝ} (hF0 : F i₀ 0 ≠ 0) (hG0 : G i₀ 0 ≠ 0)
    (hFsupp : ∀ t : Fin (m + 1) → ℝ, (∀ i, 0 ≤ t i) → (∏ i, F i (t i)) ≠ 0 →
      t ∈ retreatRegion p (m + 1) j ε₀)
    (hGsupp : ∀ t : Fin (m + 1) → ℝ, (∀ i, 0 ≤ t i) → (∏ i, G i (t i)) ≠ 0 →
      t ∈ retreatRegion p (m + 1) j' ε₀)
    (hmarg : ∀ t : Fin m → ℝ, (∀ s, 0 ≤ t s) → (∏ s, F (i₀.succAbove s) (t s)) ≠ 0 →
      t ∈ marginalRegion p m j ε₀) :
    IsReducedRetreat p m j j' ε₀ i₀ (fun s ↦ F (i₀.succAbove s)) (fun s ↦ G (i₀.succAbove s)) := by
  have hnn : ∀ t : Fin m → ℝ, (∀ s, 0 ≤ t s) →
      ∀ i, 0 ≤ (i₀.insertNth (0 : ℝ) t : Fin (m + 1) → ℝ) i := by
    intro t ht i
    induction i using Fin.succAboveCases i₀ <;> simp [ht]
  have hsplit : ∀ (H : Fin (m + 1) → ℝ → ℝ) (t : Fin m → ℝ),
      ∏ i, H i ((i₀.insertNth (0 : ℝ) t : Fin (m + 1) → ℝ) i)
        = H i₀ 0 * ∏ s, H (i₀.succAbove s) (t s) := by
    intro H t
    rw [Fin.prod_univ_succAbove
      (fun i ↦ H i ((i₀.insertNth (0 : ℝ) t : Fin (m + 1) → ℝ) i)) i₀]
    simp
  intro t ht
  exact ⟨fun hprod ↦ ⟨hFsupp _ (hnn t ht) (hsplit F t ▸ mul_ne_zero hF0 hprod),
    hmarg t ht hprod⟩, fun hprod ↦ hGsupp _ (hnn t ht) (hsplit G t ▸ mul_ne_zero hG0 hprod)⟩

/-- **The reduced retreat only sees the nonnegative axis**, so it transfers to any pair of families
agreeing there — which is what the truncation of `Gap212.Sieve.exists_truncation` changes. -/
theorem isReducedRetreat_congr_nonneg {p : SupportParams} {m : ℕ} {j j' : Fin p.n} {ε₀ : ℝ}
    {i₀ : Fin (m + 1)} {F G F₂ G₂ : Fin m → ℝ → ℝ}
    (hF : ∀ s, ∀ t : ℝ, 0 ≤ t → F s t = F₂ s t) (hG : ∀ s, ∀ t : ℝ, 0 ≤ t → G s t = G₂ s t)
    (hred : IsReducedRetreat p m j j' ε₀ i₀ F G) : IsReducedRetreat p m j j' ε₀ i₀ F₂ G₂ := by
  intro t ht
  have hFe : ∏ s, F₂ s (t s) = ∏ s, F s (t s) :=
    Finset.prod_congr rfl fun s _ ↦ (hF s (t s) (ht s)).symm
  have hGe : ∏ s, G₂ s (t s) = ∏ s, G s (t s) :=
    Finset.prod_congr rfl fun s _ ↦ (hG s (t s) (ht s)).symm
  rw [hFe, hGe]
  exact hred t ht

/-! ## Bookkeeping for the divisor numerator -/

/-- **The Möbius function is bounded by one.** -/
theorem abs_moebius_cast_le_one (n : ℕ) : |((μ n : ℤ) : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- **The numerator is dominated by the bare product of profile values**, the weight
`Gap212.Sieve.weighted_error_negligible` sums against. -/
theorem abs_divisorNumerator_le {m : ℕ} (x : ℝ) (F G : Fin m → ℝ → ℝ)
    (dd : (Fin m → ℕ) × (Fin m → ℕ)) :
    |divisorNumerator x F G dd|
      ≤ |∏ i, F i (Gap212.logScale x (dd.1 i)) * G i (Gap212.logScale x (dd.2 i))| := by
  rw [divisorNumerator, Finset.abs_prod, Finset.abs_prod]
  refine Finset.prod_le_prod (fun i _ ↦ abs_nonneg _) fun i _ ↦ ?_
  rw [abs_mul, abs_mul, abs_mul, abs_mul]
  exact mul_le_mul (mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_cast_le_one _))
    (mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_cast_le_one _)) (by positivity)
    (abs_nonneg _)

/-- **The numerator only sees the nonnegative axis.** -/
theorem divisorNumerator_congr_nonneg {m : ℕ} {x : ℝ} (hx : 1 < x) {F G F₂ G₂ : Fin m → ℝ → ℝ}
    (hF : ∀ s, ∀ t : ℝ, 0 ≤ t → F s t = F₂ s t) (hG : ∀ s, ∀ t : ℝ, 0 ≤ t → G s t = G₂ s t)
    {dd : (Fin m → ℕ) × (Fin m → ℕ)} (hd1 : ∀ s, 0 < dd.1 s) (hd2 : ∀ s, 0 < dd.2 s) :
    divisorNumerator x F G dd = divisorNumerator x F₂ G₂ dd := by
  have hnn : ∀ d : ℕ, 0 < d → (0 : ℝ) ≤ Gap212.Notation.logx x d := fun d hd ↦
    div_nonneg (Real.log_nonneg (by exact_mod_cast hd)) (Real.log_nonneg hx.le)
  refine Finset.prod_congr rfl fun s _ ↦ ?_
  rw [hF s _ (hnn _ (hd1 s)), hG s _ (hnn _ (hd2 s))]

/-- Each factor of a non-zero numerator is non-zero. -/
private theorem factor_ne_zero_of_divisorNumerator_ne_zero {m : ℕ} {x : ℝ} {F G : Fin m → ℝ → ℝ}
    {dd : (Fin m → ℕ) × (Fin m → ℕ)} (hne : divisorNumerator x F G dd ≠ 0) (s : Fin m) :
    (μ (dd.1 s) : ℝ) * F s (Gap212.Notation.logx x (dd.1 s)) *
      ((μ (dd.2 s) : ℝ) * G s (Gap212.Notation.logx x (dd.2 s))) ≠ 0 :=
  Finset.prod_ne_zero_iff.mp hne s (Finset.mem_univ s)

/-- **A non-zero numerator has positive coordinates**, `μ(0) = 0` being what forces it. -/
theorem pos_of_divisorNumerator_ne_zero {m : ℕ} {x : ℝ} {F G : Fin m → ℝ → ℝ}
    {dd : (Fin m → ℕ) × (Fin m → ℕ)} (hne : divisorNumerator x F G dd ≠ 0) :
    (∀ s, 0 < dd.1 s) ∧ (∀ s, 0 < dd.2 s) := by
  have hfac := factor_ne_zero_of_divisorNumerator_ne_zero hne
  exact ⟨fun s ↦ Nat.pos_of_ne_zero fun h0 ↦ hfac s (by simp [h0]),
    fun s ↦ Nat.pos_of_ne_zero fun h0 ↦ hfac s (by simp [h0])⟩

/-- **A non-zero numerator has non-zero profile products**, which is what the retreat clauses of
`Gap212.GPY.IsReducedRetreat` are read at. -/
theorem prod_ne_zero_of_divisorNumerator_ne_zero {m : ℕ} {x : ℝ} {F G : Fin m → ℝ → ℝ}
    {dd : (Fin m → ℕ) × (Fin m → ℕ)} (hne : divisorNumerator x F G dd ≠ 0) :
    (∏ s, F s (Gap212.Notation.logx x (dd.1 s))) ≠ 0 ∧
      (∏ s, G s (Gap212.Notation.logx x (dd.2 s))) ≠ 0 := by
  have hfac := factor_ne_zero_of_divisorNumerator_ne_zero hne
  exact ⟨Finset.prod_ne_zero_iff.mpr fun s _ h0 ↦ hfac s (by simp [h0]),
    Finset.prod_ne_zero_iff.mpr fun s _ h0 ↦ hfac s (by simp [h0])⟩

/-- **The index set of `Gap212.Sieve.divisor_sum_over_qstar` sits in any box containing
`[1,⌊x⌋₊]`.** -/
theorem mem_box_of_mem_qstarPairs {p : SupportParams} {m : ℕ} {x ε₀ : ℝ} {B : ℕ}
    (hB : ⌊x⌋₊ ≤ B) {dd : (Fin m → ℕ) × (Fin m → ℕ)} (hdd : dd ∈ qstarPairs p m x ε₀) :
    dd ∈ (Fintype.piFinset fun _ : Fin m ↦ Finset.Icc 1 B) ×ˢ
      Fintype.piFinset fun _ : Fin m ↦ Finset.Icc 1 B := by
  classical
  simp only [qstarPairs, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset,
    Finset.mem_Icc] at hdd ⊢
  exact ⟨fun i ↦ ⟨(hdd.1.1 i).1, (hdd.1.1 i).2.trans hB⟩,
    fun i ↦ ⟨(hdd.1.2 i).1, (hdd.1.2 i).2.trans hB⟩⟩

/-! ## The error term of the shift, counted on the reduced coordinates

`Gap212.Sieve.card_contributing_isLittleO_calC` counts pairs of `k`-tuples. The numerator's tuples
live on the `k - 1` coordinates other than `i₀`; extending each by `1` there — which is extending
its logarithmic size vector by `0` — puts them in range of that count, injectively. -/

/-- **The contributing reduced pairs are `o(𝓒_x)`.** -/
theorem card_reduced_contributing_isLittleO_calC (p : SupportParams) (m : ℕ) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) (j j' : Fin p.n) (i₀ : Fin (m + 1))
    (T : ℝ → Finset ((Fin m → ℕ) × (Fin m → ℕ)))
    (hT : ∀ᶠ x : ℝ in atTop, ∀ dd ∈ T x, (∀ s, 0 < dd.1 s) ∧ (∀ s, 0 < dd.2 s) ∧
      (i₀.insertNth (0 : ℝ) (fun s ↦ Gap212.logScale x (dd.1 s)) : Fin (m + 1) → ℝ)
          ∈ retreatRegion p (m + 1) j ε₀ ∧
      (i₀.insertNth (0 : ℝ) (fun s ↦ Gap212.logScale x (dd.2 s)) : Fin (m + 1) → ℝ)
          ∈ retreatRegion p (m + 1) j' ε₀) :
    (fun x : ℝ ↦ (#(T x) : ℝ)) =o[atTop] (fun x : ℝ ↦ calC m x) := by
  classical
  set lift : ((Fin m → ℕ) × (Fin m → ℕ)) → ((Fin (m + 1) → ℕ) × (Fin (m + 1) → ℕ)) :=
    fun dd ↦ (i₀.insertNth 1 dd.1, i₀.insertNth 1 dd.2) with hliftdef
  have hinj : Function.Injective lift := by
    intro dd ee hde
    simp only [hliftdef, Prod.mk.injEq] at hde
    exact Prod.ext (funext fun s ↦ by simpa using congrFun hde.1 (i₀.succAbove s))
      (funext fun s ↦ by simpa using congrFun hde.2 (i₀.succAbove s))
  have hlog : ∀ (x : ℝ) (d : Fin m → ℕ),
      (fun i ↦ Gap212.logScale x ((i₀.insertNth 1 d : Fin (m + 1) → ℕ) i))
        = (i₀.insertNth (0 : ℝ) (fun s ↦ Gap212.logScale x (d s)) : Fin (m + 1) → ℝ) := by
    intro x d
    funext i
    induction i using Fin.succAboveCases i₀ <;> simp [Gap212.logScale]
  refine (card_contributing_isLittleO_calC p m hε₀ hε₀' j j'
      (fun x ↦ (T x).image lift) ?_).congr' ?_ (EventuallyEq.refl _ _)
  · filter_upwards [hT] with x hx dd' hdd'
    obtain ⟨dd, hdd, rfl⟩ := Finset.mem_image.mp hdd'
    obtain ⟨hp1, hp2, hm1, hm2⟩ := hx dd hdd
    refine ⟨fun i ↦ ?_, fun i ↦ ?_, hlog x dd.1 ▸ hm1, hlog x dd.2 ▸ hm2⟩ <;>
      induction i using Fin.succAboveCases i₀ <;> simp [hliftdef, hp1, hp2]
  · filter_upwards with x
    rw [Finset.card_image_of_injective _ hinj]

/-- **A non-zero numerator has squarefree coordinates**, which is what
`Gap212.Sieve.weighted_error_negligible` asks of the tuples it sums over. -/
theorem squarefree_of_divisorNumerator_ne_zero {m : ℕ} {x : ℝ} {F G : Fin m → ℝ → ℝ}
    {dd : (Fin m → ℕ) × (Fin m → ℕ)} (hne : divisorNumerator x F G dd ≠ 0) :
    (∀ s, Squarefree (dd.1 s)) ∧ (∀ s, Squarefree (dd.2 s)) := by
  have hfac := factor_ne_zero_of_divisorNumerator_ne_zero hne
  refine ⟨fun s ↦ ?_, fun s ↦ ?_⟩ <;>
    exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp fun h0 ↦ hfac s (by simp [h0])

/-! ## The asymptotic, assembled

The proof has five steps: the removed coordinate's divisor weights come
out as `F_{i₀}(0)G_{i₀}(0)`, the remaining `2(k-1)` weights are expanded and the `n`-sum moved
inside, the congruences collapse by the Chinese remainder theorem, the inner sum splits into its
average and the dyadic discrepancy, and the two halves are the divisor sum over `Q⋆` against the
mean-value clause and the weighted-error estimate. -/

set_option maxHeartbeats 4000000 in
-- All five steps sit in this one declaration: the expansion, the Chinese
-- remainder collapse, the average/discrepancy split, the main term against the divisor sum over
-- `Q⋆` and the error against the weighted-error estimate. Splitting it
-- would mean naming a dozen intermediate quantities that depend on the whole hypothesis block; the
-- cost is elaboration time, not search.
/-- **The sieve asymptotic at a non-degenerate pair of profile families.** The main case of
`Gap212.Sieve.sieveAsymptotic_of_obligations`: every factor vanishes from `1` on, and the two
boundary values at the removed coordinate are non-zero.

The profiles are `C^∞`, as `hgram` and `Gap212.Sieve.divisor_sum_over_qstar` ask; the truncations
`Ft`, `Gt` inherit whatever `hFC`, `hGC` give, `Gap212.Sieve.exists_truncation` being polymorphic
in the index. -/
theorem sieveAsymptotic_core (hgram : TotientGramSumLimitOfSupport)
    (hsieve : TotientSievingError 44) (p : SupportParams) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1)
    (j j' : Fin p.n) (hA : p.ε < p.A j.succ) {ρ : ℕ → ℝ → ℝ} {β : ℝ} (hρ : RhoHypotheses p ρ β)
    (heq : HasEquidistributionOverQstarFamily p fun n x ↦ ((ρ n x : ℝ) : ℂ))
    {hh : Fin (44 + 1) → ℕ} (hmono : StrictMono hh) (i₀ : Fin (44 + 1))
    {F G : Fin (44 + 1) → ℝ → ℝ} (hFC : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (hGC : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i))
    (hFB : ∃ B : ℝ, ∀ i, ∀ t : ℝ, B < t → F i t = 0)
    (hGB : ∃ B : ℝ, ∀ i, ∀ t : ℝ, B < t → G i t = 0)
    (hFsupp : ∀ t : Fin (44 + 1) → ℝ, (∀ i, 0 ≤ t i) → (∏ i, F i (t i)) ≠ 0 →
      t ∈ retreatRegion p (44 + 1) j ε₀)
    (hGsupp : ∀ t : Fin (44 + 1) → ℝ, (∀ i, 0 ≤ t i) → (∏ i, G i (t i)) ≠ 0 →
      t ∈ retreatRegion p (44 + 1) j' ε₀)
    (hmarg : ∀ t : Fin 44 → ℝ, (∀ s, 0 ≤ t s) → (∏ s, F (i₀.succAbove s) (t s)) ≠ 0 →
      t ∈ marginalRegion p 44 j ε₀)
    (hF1 : ∀ i, ∀ t : ℝ, 1 ≤ t → F i t = 0) (hG1 : ∀ i, ∀ t : ℝ, 1 ≤ t → G i t = 0)
    (hF00 : F i₀ 0 ≠ 0) (hG00 : G i₀ 0 ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ X : ℝ, ∀ x > X, ∀ b : ℕ, IsPreSieved b (W x) hh →
      |(∑ n ∈ dyadic x with n % W x = b % W x,
            ρ (n + hh i₀) x * ∏ i, lambdaF (F i) x (n + hh i) * lambdaF (G i) x (n + hh i)) -
          (F i₀ 0 * G i₀ 0 * ∏ s : Fin 44, ∫ t in Set.Ioi (0 : ℝ),
              deriv (F (i₀.succAbove s)) t * deriv (G (i₀.succAbove s)) t) * scale (44 + 1) x|
        ≤ η * scale (44 + 1) x := by
  classical
  -- The reduced families, and compactly supported versions of them.
  have hred : IsReducedRetreat p 44 j j' ε₀ i₀ (fun s ↦ F (i₀.succAbove s))
      (fun s ↦ G (i₀.succAbove s)) := isReducedRetreat_of_retreat i₀ hF00 hG00 hFsupp hGsupp hmarg
  obtain ⟨BF, hBF⟩ := hFB
  obtain ⟨BG, hBG⟩ := hGB
  choose Ft hFtd hFtc hFte using fun s : Fin 44 ↦
    exists_truncation (hFC (i₀.succAbove s)) (fun t ht ↦ hBF (i₀.succAbove s) t ht)
  choose Gt hGtd hGtc hGte using fun s : Fin 44 ↦
    exists_truncation (hGC (i₀.succAbove s)) (fun t ht ↦ hBG (i₀.succAbove s) t ht)
  have hredt : IsReducedRetreat p 44 j j' ε₀ i₀ Ft Gt :=
    isReducedRetreat_congr_nonneg hFte hGte hred
  set Pit : ℝ := ∏ s : Fin 44, ∫ t in Set.Ioi (0 : ℝ), deriv (Ft s) t * deriv (Gt s) t with hPitdef
  have hPi : (∏ s : Fin 44, ∫ t in Set.Ioi (0 : ℝ),
      deriv (F (i₀.succAbove s)) t * deriv (G (i₀.succAbove s)) t) = Pit :=
    Finset.prod_congr rfl fun s _ ↦ setIntegral_deriv_congr_nonneg (hFte s) (hGte s)
  rw [hPi]
  -- A single bound for the truncated profiles.
  choose cF hcF using fun s : Fin 44 ↦ (hFtc s).exists_bound_of_continuous (hFtd s).continuous
  choose cG hcG using fun s : Fin 44 ↦ (hGtc s).exists_bound_of_continuous (hGtd s).continuous
  set Mb : ℝ := (∑ s, |cF s|) + ∑ s, |cG s| with hMbdef
  have hsF : (0 : ℝ) ≤ ∑ s, |cF s| := Finset.sum_nonneg fun s _ ↦ abs_nonneg _
  have hsG : (0 : ℝ) ≤ ∑ s, |cG s| := Finset.sum_nonneg fun s _ ↦ abs_nonneg _
  have hMb0 : (0 : ℝ) ≤ Mb := add_nonneg hsF hsG
  have hFtM : ∀ s t, |Ft s t| ≤ Mb := fun s t ↦ by
    linarith [(Real.norm_eq_abs _).symm.trans_le (hcF s t), le_abs_self (cF s),
      Finset.single_le_sum (fun s _ ↦ abs_nonneg (cF s)) (Finset.mem_univ s)]
  have hGtM : ∀ s t, |Gt s t| ≤ Mb := fun s t ↦ by
    linarith [(Real.norm_eq_abs _).symm.trans_le (hcG s t), le_abs_self (cG s),
      Finset.single_le_sum (fun s _ ↦ abs_nonneg (cG s)) (Finset.mem_univ s)]
  obtain ⟨Mp, hMpdef⟩ : ∃ z : ℝ, z = Mb ^ 88 := ⟨_, rfl⟩
  have hMp0 : (0 : ℝ) ≤ Mp := by rw [hMpdef]; positivity
  have hnumbnd : ∀ (y : ℝ) (dd : (Fin 44 → ℕ) × (Fin 44 → ℕ)),
      |divisorNumerator y Ft Gt dd| ≤ Mp := by
    intro y dd
    rw [hMpdef]
    refine le_trans (abs_divisorNumerator_le y Ft Gt dd) ?_
    rw [Finset.abs_prod]
    calc ∏ s : Fin 44, |Ft s (Gap212.logScale y (dd.1 s)) * Gt s (Gap212.logScale y (dd.2 s))|
        ≤ ∏ _s : Fin 44, Mb * Mb := by
          refine Finset.prod_le_prod (fun s _ ↦ abs_nonneg _) fun s _ ↦ ?_
          rw [abs_mul]
          exact mul_le_mul (hFtM _ _) (hGtM _ _) (abs_nonneg _) hMb0
      _ = Mb ^ 88 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← sq, ← pow_mul]
  -- The budget.
  set K₀ : ℝ := |F i₀ 0 * G i₀ 0| with hK₀def
  have hK₀0 : (0 : ℝ) ≤ K₀ := abs_nonneg _
  set δ : ℝ := η / (3 * (K₀ + 1)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  set ε₂ : ℝ := min (1 / 2) (δ / (2 * (|Pit| + 1))) with hε₂def
  have hε₂pos : 0 < ε₂ := lt_min (by norm_num) (div_pos hδpos (by positivity))
  have hε₂half : ε₂ ≤ 1 / 2 := min_le_left _ _
  have hε₂Pi : ε₂ * |Pit| ≤ δ / 2 := by
    calc ε₂ * |Pit| ≤ δ / (2 * (|Pit| + 1)) * |Pit| :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)
      _ ≤ δ / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
          nlinarith [abs_nonneg Pit, hδpos.le]
  set ε₃ : ℝ := δ / 4 with hε₃def
  have hε₃pos : 0 < ε₃ := div_pos hδpos four_pos
  -- The contributing tuples, and their count.
  set contr : ℝ → Finset ((Fin 44 → ℕ) × (Fin 44 → ℕ)) := fun y ↦
    {dd ∈ qstarPairs p 44 y ε₀ | divisorNumerator y Ft Gt dd ≠ 0} with hcontrdef
  have hcontrmem : ∀ (y : ℝ) (dd : (Fin 44 → ℕ) × (Fin 44 → ℕ)),
      dd ∈ contr y ↔ dd ∈ qstarPairs p 44 y ε₀ ∧ divisorNumerator y Ft Gt dd ≠ 0 :=
    fun _ _ ↦ Finset.mem_filter
  have hmemret : ∀ (y : ℝ), 1 < y → ∀ dd : (Fin 44 → ℕ) × (Fin 44 → ℕ),
      divisorNumerator y Ft Gt dd ≠ 0 →
      ((i₀.insertNth (0 : ℝ) (fun s ↦ Gap212.logScale y (dd.1 s)) : Fin (44 + 1) → ℝ)
          ∈ retreatRegion p (44 + 1) j ε₀ ∧
        (i₀.insertNth (0 : ℝ) (fun s ↦ Gap212.logScale y (dd.2 s)) : Fin (44 + 1) → ℝ)
          ∈ retreatRegion p (44 + 1) j' ε₀) := by
    intro y hy dd hne
    obtain ⟨hp1, hp2⟩ := pos_of_divisorNumerator_ne_zero hne
    obtain ⟨hq1, hq2⟩ := prod_ne_zero_of_divisorNumerator_ne_zero hne
    have hnn : ∀ d : ℕ, 0 < d → (0 : ℝ) ≤ Gap212.logScale y d := fun d hd ↦
      div_nonneg (Real.log_nonneg (by exact_mod_cast hd)) (Real.log_nonneg hy.le)
    exact ⟨((hredt _ fun s ↦ hnn _ (hp1 s)).1 hq1).1, (hredt _ fun s ↦ hnn _ (hp2 s)).2 hq2⟩
  have hcount : (fun y : ℝ ↦ (#(contr y) : ℝ)) =o[atTop] fun y ↦ calC 44 y := by
    refine card_reduced_contributing_isLittleO_calC p 44 hε₀ hε₀' j j' i₀ contr ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy dd hdd
    obtain ⟨-, hne⟩ := (hcontrmem y dd).mp hdd
    obtain ⟨hp1, hp2⟩ := pos_of_divisorNumerator_ne_zero hne
    exact ⟨hp1, hp2, hmemret y hy dd hne⟩
  -- The two inputs, and the eventual facts.
  have hnode := divisor_sum_over_qstar hgram hsieve p hε₀ hε₀' j j' hA i₀ Ft Gt hFtd hFtc
    hGtd hGtc hredt
  have hwe := weighted_error_negligible (m := 44) rfl p hε₀ hε₀' j j' hA i₀ hmono hρ heq
    hFtM hGtM hredt hδpos
  have hdens : ∀ᶠ y : ℝ in atTop,
      |(∑ n ∈ dyadic y, ρ n y) - y / Real.log y| ≤ ε₂ * y / Real.log y := by
    obtain ⟨X₀, hX₀⟩ := hρ.density ε₂ hε₂pos
    exact (eventually_gt_atTop X₀).mono hX₀
  have hzeta : ∀ᶠ y : ℝ in atTop,
      |(∑ dd ∈ qstarPairs p 44 y ε₀, divisorNumerator y Ft Gt dd /
          (Nat.totient (W y * ∏ i, (dd.1 i).lcm (dd.2 i)) : ℝ)) / divisorSumNorm 44 y - Pit|
        ≤ ε₃ := by
    filter_upwards [Metric.tendsto_nhds.mp hnode ε₃ hε₃pos] with y hy
    exact (Real.dist_eq _ _ ▸ hy).le
  have hHnn : (0 : ℝ) ≤ (hh i₀ : ℝ) := Nat.cast_nonneg _
  have hedgeo : ∀ᶠ y : ℝ in atTop,
      (hh i₀ : ℝ) * (Mp * (#(contr y) : ℝ)) ≤ δ * calC 44 y := by
    set cc : ℝ := δ / (((hh i₀ : ℝ) + 1) * (Mp + 1)) with hccdef
    have hden : (0 : ℝ) < ((hh i₀ : ℝ) + 1) * (Mp + 1) :=
      mul_pos (by linarith) (by linarith)
    have hcc : 0 < cc := div_pos hδpos hden
    filter_upwards [hcount.bound hcc, calC_lower_bound 44] with y hy hlow
    have hcalC : (0 : ℝ) ≤ calC 44 y := le_trans hlow.2.le hlow.1
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hcalC] at hy
    calc (hh i₀ : ℝ) * (Mp * (#(contr y) : ℝ))
        ≤ (hh i₀ : ℝ) * (Mp * (cc * calC 44 y)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy hMp0) hHnn
      _ = (hh i₀ : ℝ) * Mp * cc * calC 44 y := by ring
      _ ≤ δ * calC 44 y := by
        refine mul_le_mul_of_nonneg_right ?_ hcalC
        rw [hccdef, ← mul_div_assoc, div_le_iff₀ hden]
        nlinarith [mul_nonneg hδpos.le (by linarith : (0 : ℝ) ≤ (hh i₀ : ℝ) + Mp + 1)]
  set Sexp : ℝ := (p.A j.succ + p.ε) + (p.A j'.succ + p.ε) with hSexpdef
  have hS1 : Sexp < 1 := (denominator_modulus_exponent p (44 + 1) hε₀ hε₀' j j').1
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hwe.and (hdens.and (hzeta.and (hedgeo.and
    ((eventually_gt_atTop (1 : ℝ)).and ((calC_lower_bound 44).and
      ((eventually_dvd_W_of_prime_le (Finset.image hh Finset.univ).diameter).and
        ((generated_modulus_le_rpow p hε₀ hε₀' j j' i₀).and
          (mem_Qstar_of_divisorNumerator_ne_zero p hε₀ hε₀' j j' hA i₀ hredt)))))))))
  refine ⟨X, fun y hy b hb ↦ ?_⟩
  obtain ⟨hwey, hdensy, hzetay, hedgey, hy1, hlowy, hDy, hQsizey, hQy⟩ := hX y hy.le
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos hy1
  have hWpos : 0 < W y := primorial_pos _
  have hcalC : (0 : ℝ) ≤ calC 44 y := le_trans hlowy.2.le hlowy.1
  rw [scale_succ_eq_calC]
  have hminy : ∀ n ∈ dyadic y, 0 ≤ ρ n y ∧ ρ n y ≤ 1 := fun n hn ↦ by
    obtain ⟨h1, h2⟩ := hρ.minorant y hy1 n hn
    exact ⟨h1, h2.trans (by split_ifs <;> norm_num)⟩
  -- Abbreviations at this `y`.
  set Hsup := Finset.univ.sup hh with hHsupdef
  have hHle : ∀ i, hh i ≤ Hsup := fun i ↦ Finset.le_sup (Finset.mem_univ i)
  set Bx := ⌊2 * y⌋₊ + Hsup with hBxdef
  set Sy : Finset ℕ := {n ∈ dyadic y | n % W y = b % W y} with hSydef
  set Pblk : ℝ := ∑ M ∈ dyadic y, ρ M y with hPblkdef
  set qm : (Fin 44 → ℕ) × (Fin 44 → ℕ) → ℕ := fun dd ↦ W y * ∏ s, (dd.1 s).lcm (dd.2 s) with hqmdef
  obtain ⟨Tsum, hTsum⟩ : ∃ f : (Fin 44 → ℕ) × (Fin 44 → ℕ) → ℝ, ∀ dd, f dd =
      ∑ n ∈ Sy with (∀ s, dd.1 s ∣ n + hh (i₀.succAbove s)) ∧
        (∀ s, dd.2 s ∣ n + hh (i₀.succAbove s)), ρ (n + hh i₀) y := ⟨_, fun _ ↦ rfl⟩
  have hnpos : ∀ n ∈ Sy, ∀ s : Fin 44, 0 < n + hh (i₀.succAbove s) := fun n hn s ↦ by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have := Nat.one_le_ceil_iff.mpr hy0
    lia
  have hnle : ∀ n ∈ Sy, ∀ s : Fin 44, n + hh (i₀.succAbove s) ≤ Bx := fun n hn s ↦
    Nat.add_le_add (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2 (hHle _)
  -- Step one: the removed coordinate's weights come out, and the rest is retruncated.
  have hstep1 : (∑ n ∈ Sy, ρ (n + hh i₀) y * ∏ i, lambdaF (F i) y (n + hh i) *
        lambdaF (G i) y (n + hh i))
      = F i₀ 0 * G i₀ 0 * ∑ n ∈ Sy, ρ (n + hh i₀) y *
          ∏ s : Fin 44, lambdaF (Ft s) y (n + hh (i₀.succAbove s)) *
            lambdaF (Gt s) y (n + hh (i₀.succAbove s)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hpr : (∏ s : Fin 44, lambdaF (F (i₀.succAbove s)) y (n + hh (i₀.succAbove s)) *
          lambdaF (G (i₀.succAbove s)) y (n + hh (i₀.succAbove s)))
        = ∏ s : Fin 44, lambdaF (Ft s) y (n + hh (i₀.succAbove s)) *
          lambdaF (Gt s) y (n + hh (i₀.succAbove s)) :=
      Finset.prod_congr rfl fun s _ ↦ by
        rw [lambdaF_congr_nonneg hy1 (hFte s), lambdaF_congr_nonneg hy1 (hGte s)]
    rw [rho_mul_prod_lambdaF_eq hy1 hρ i₀ hF1 hG1 (Finset.mem_filter.mp hn).1, hpr]
  -- Step two: the divisor expansion and the interchange.
  have hstep2 : (∑ n ∈ Sy, ρ (n + hh i₀) y *
        ∏ s : Fin 44, lambdaF (Ft s) y (n + hh (i₀.succAbove s)) *
          lambdaF (Gt s) y (n + hh (i₀.succAbove s)))
      = ∑ dd ∈ (Fintype.piFinset fun _ : Fin 44 ↦ Finset.Icc 1 Bx) ×ˢ
            Fintype.piFinset fun _ : Fin 44 ↦ Finset.Icc 1 Bx,
          divisorNumerator y Ft Gt dd * Tsum dd := by
    rw [sum_weighted_prod_lambdaF_pair Sy (fun n ↦ ρ (n + hh i₀) y)
      (fun s ↦ hh (i₀.succAbove s)) Ft Gt hnpos hnle, Finset.sum_product]
    refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun d' _ ↦ ?_
    rw [hTsum, divisorNumerator, ← Finset.prod_mul_distrib]
  -- Step three: only the index set of `divisor_sum_over_qstar` contributes.
  have hstep3 : (∑ dd ∈ (Fintype.piFinset fun _ : Fin 44 ↦ Finset.Icc 1 Bx) ×ˢ
        Fintype.piFinset fun _ : Fin 44 ↦ Finset.Icc 1 Bx,
        divisorNumerator y Ft Gt dd * Tsum dd)
      = ∑ dd ∈ contr y, divisorNumerator y Ft Gt dd * Tsum dd := by
    have hfl : ⌊y⌋₊ ≤ Bx := (Nat.floor_le_floor (by linarith)).trans (Nat.le_add_right _ _)
    refine (Finset.sum_subset (fun dd hdd ↦ mem_box_of_mem_qstarPairs hfl
      ((hcontrmem y dd).mp hdd).1) fun dd _ hnot ↦ ?_).symm
    rcases eq_or_ne (divisorNumerator y Ft Gt dd) 0 with h0 | h0
    · rw [h0, zero_mul]
    have hnq : dd ∉ qstarPairs p 44 y ε₀ := fun hc ↦ hnot ((hcontrmem y dd).mpr ⟨hc, h0⟩)
    have hT0 : Tsum dd = 0 := by
      rw [hTsum]
      refine Finset.sum_eq_zero fun n hn ↦ absurd ?_ hnq
      obtain ⟨hnSy, hdvd⟩ := Finset.mem_filter.mp hn
      have hnb : n ≡ b [MOD W y] := (Finset.mem_filter.mp hnSy).2
      have hlcmdvd : ∀ s, ((dd.1 s).lcm (dd.2 s)) ∣ n + hh (i₀.succAbove s) := fun s ↦
        Nat.lcm_dvd (hdvd.1 s) (hdvd.2 s)
      refine (mem_qstarPairs_iff p dd).mpr ⟨fun s ↦ ?_, fun s s' hss ↦ ?_, hQy dd h0⟩
      · exact (Nat.Coprime.coprime_dvd_left (hlcmdvd s)
          (coprime_W_of_modEq hb hnb (i₀.succAbove s))).symm
      · exact Nat.Coprime.coprime_dvd_right (hlcmdvd s')
          (Nat.Coprime.coprime_dvd_left (hlcmdvd s)
            (coprime_shifts_of_modEq hmono hDy hb hnb
              (fun hc ↦ hss (Fin.succAbove_right_injective hc))))
    rw [hT0, mul_zero]
  -- The Chinese remainder residues.
  have hexA : ∀ dd : (Fin 44 → ℕ) × (Fin 44 → ℕ), ∃ a : ℕ, dd ∈ contr y → ∀ n : ℕ,
      ((n ≡ b [MOD W y] ∧ ∀ s, ((dd.1 s).lcm (dd.2 s)) ∣ n + hh (i₀.succAbove s))
        ↔ n ≡ a [MOD W y * ∏ s, (dd.1 s).lcm (dd.2 s)]) := by
    intro dd
    by_cases hdd : dd ∈ contr y
    · obtain ⟨hq, -⟩ := (hcontrmem y dd).mp hdd
      obtain ⟨hcopW, hpw, -⟩ := (mem_qstarPairs_iff p dd).mp hq
      obtain ⟨a, ha⟩ := exists_crt_class (W := W y) (b := b)
        (m := fun s ↦ (dd.1 s).lcm (dd.2 s)) (fun s ↦ hh (i₀.succAbove s))
        (fun s ↦ lcm_pos_of_mem_qstarPairs hq s) hcopW hpw
      exact ⟨a, fun _ ↦ ha⟩
    · exact ⟨0, fun hc ↦ absurd hc hdd⟩
  choose ares hares using hexA
  have hTclass : ∀ dd ∈ contr y, Tsum dd
      = ∑ n ∈ dyadic y with n ≡ ares dd [MOD qm dd], ρ (n + hh i₀) y := by
    intro dd hdd
    rw [hTsum]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext n
    simp only [hSydef, Finset.mem_filter, and_assoc]
    refine ⟨fun hn ↦ ⟨hn.1, (hares dd hdd n).mp ⟨hn.2.1, fun s ↦
        Nat.lcm_dvd (hn.2.2.1 s) (hn.2.2.2 s)⟩⟩, fun hn ↦ ?_⟩
    obtain ⟨hnb, hdvd⟩ := (hares dd hdd n).mpr hn.2
    exact ⟨hn.1, hnb, fun s ↦ (Nat.dvd_lcm_left _ _).trans (hdvd s),
      fun s ↦ (Nat.dvd_lcm_right _ _).trans (hdvd s)⟩
  have hcopq : ∀ dd ∈ contr y, ∀ M ∈ dyadic y, ρ M y ≠ 0 → Nat.Coprime M (qm dd) := by
    intro dd hdd M hM hne
    obtain ⟨hq, hn0⟩ := (hcontrmem y dd).mp hdd
    obtain ⟨hp1, hp2⟩ := pos_of_divisorNumerator_ne_zero hn0
    obtain ⟨hm1, hm2⟩ := hmemret y hy1 dd hn0
    obtain ⟨hlow, hhigh⟩ := hρ.minorant y hy1 M hM
    have hMp : M.Prime := by
      by_contra hnp
      rw [if_neg hnp] at hhigh
      exact hne (le_antisymm hhigh hlow)
    have hMge : y ≤ (M : ℝ) := (Nat.le_ceil y).trans (by exact_mod_cast (Finset.mem_Icc.mp hM).1)
    have hqlt : ((qm dd : ℕ) : ℝ) < (M : ℝ) := ((hQsizey dd.1 dd.2 hp1 hp2 hm1 hm2).trans_lt
      (by simpa using Real.rpow_lt_rpow_of_exponent_lt hy1 hS1)).trans_le hMge
    have hqpos : 0 < qm dd :=
      Nat.mul_pos hWpos (Finset.prod_pos fun s _ ↦ lcm_pos_of_mem_qstarPairs hq s)
    rw [hMp.coprime_iff_not_dvd]
    exact fun hdvd ↦ hqlt.not_ge (by exact_mod_cast Nat.le_of_dvd hqpos hdvd)
  -- The per-tuple split: average, discrepancy, edge.
  have hTbound : ∀ dd ∈ contr y, |Tsum dd - 1 / (Nat.totient (qm dd) : ℝ) * Pblk|
      ≤ ‖sumErrorDyadic y (fun n ↦ ((ρ n y : ℝ) : ℂ)) (qm dd) (ares dd + hh i₀)‖
        + (hh i₀ : ℝ) := by
    intro dd hdd
    have h1 := abs_shifted_class_sum_sub_le (ρ := ρ) (x := y)
      (fun n hn ↦ hρ.support y n hn) hminy (qm dd) (ares dd) (hh i₀)
    have h2 := sum_class_eq_average_add_discrepancy (ρ := ρ) (x := y) (q := qm dd)
      (a := ares dd + hh i₀) (hcopq dd hdd)
    rw [hTclass dd hdd]
    have h3 : |(∑ M ∈ dyadic y with M ≡ ares dd + hh i₀ [MOD qm dd], ρ M y)
        - 1 / (Nat.totient (qm dd) : ℝ) * Pblk|
        ≤ ‖sumErrorDyadic y (fun n ↦ ((ρ n y : ℝ) : ℂ)) (qm dd) (ares dd + hh i₀)‖ := by
      rw [h2, hPblkdef, add_sub_cancel_left]
      exact Complex.abs_re_le_norm _
    exact (abs_sub_le _ _ _).trans ((add_le_add h1 h3).trans_eq (add_comm _ _))
  -- The main-term sum, and the split.
  set Rsum : ℝ := ∑ dd ∈ qstarPairs p 44 y ε₀, divisorNumerator y Ft Gt dd /
    (Nat.totient (W y * ∏ i, (dd.1 i).lcm (dd.2 i)) : ℝ) with hRsumdef
  have hRsum : (∑ dd ∈ contr y, divisorNumerator y Ft Gt dd / (Nat.totient (qm dd) : ℝ))
      = Rsum := by
    rw [hRsumdef]
    refine Finset.sum_subset (fun dd hdd ↦ ((hcontrmem y dd).mp hdd).1) fun dd hdd hnot ↦ ?_
    rw [not_not.mp fun hc ↦ hnot ((hcontrmem y dd).mpr ⟨hdd, hc⟩), zero_div]
  obtain ⟨Err, hErr⟩ : ∃ z : ℝ, z = ∑ dd ∈ contr y, divisorNumerator y Ft Gt dd *
      (Tsum dd - 1 / (Nat.totient (qm dd) : ℝ) * Pblk) := ⟨_, rfl⟩
  have hsplit : (∑ dd ∈ contr y, divisorNumerator y Ft Gt dd * Tsum dd) = Pblk * Rsum + Err := by
    rw [hErr, ← hRsum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun dd _ ↦ by ring
  -- The error is `o(𝓒_x)`.
  have herrbnd : |Err| ≤ δ * calC 44 y + δ * calC 44 y := by
    have hcond : ∀ dd ∈ contr y, (∀ i, Squarefree (dd.1 i)) ∧ (∀ i, Squarefree (dd.2 i)) ∧
        (∀ i, Nat.Coprime ((dd.1 i).lcm (dd.2 i)) (W y)) ∧
        (∀ i i' : Fin 44, i ≠ i' →
          Nat.Coprime ((dd.1 i).lcm (dd.2 i)) ((dd.1 i').lcm (dd.2 i'))) ∧
        IsTupleResidue y b hh i₀ dd.1 dd.2 (ares dd + hh i₀) := by
      intro dd hdd
      obtain ⟨hq, hn0⟩ := (hcontrmem y dd).mp hdd
      obtain ⟨hsq1, hsq2⟩ := squarefree_of_divisorNumerator_ne_zero hn0
      obtain ⟨hcopW, hpw, -⟩ := (mem_qstarPairs_iff p dd).mp hq
      obtain ⟨hab, hadvd⟩ := (hares dd hdd (ares dd)).mpr (Nat.ModEq.refl _)
      refine ⟨hsq1, hsq2, fun i ↦ (hcopW i).symm, hpw, hab.add_right (hh i₀), fun s ↦ ?_⟩
      rw [Int.modEq_iff_dvd]
      have hz : ((hh i₀ : ℤ) - (hh (i₀.succAbove s) : ℤ)) - ((ares dd + hh i₀ : ℕ) : ℤ)
          = -((ares dd + hh (i₀.succAbove s) : ℕ) : ℤ) := by push_cast; ring
      rw [hz]
      exact Dvd.dvd.neg_right (Int.natCast_dvd_natCast.mpr (hadvd s))
    have hwesum := hwey b hb (contr y) (fun dd ↦ ares dd + hh i₀) hcond
    have hpart1 : (∑ dd ∈ contr y, |divisorNumerator y Ft Gt dd| *
        ‖sumErrorDyadic y (fun n ↦ ((ρ n y : ℝ) : ℂ)) (qm dd) (ares dd + hh i₀)‖)
        ≤ δ * calC 44 y := by
      refine le_trans (Finset.sum_le_sum fun dd _ ↦ ?_) hwesum
      exact mul_le_mul_of_nonneg_right (abs_divisorNumerator_le y Ft Gt dd) (norm_nonneg _)
    have hpart2 : (hh i₀ : ℝ) * ∑ dd ∈ contr y, |divisorNumerator y Ft Gt dd|
        ≤ δ * calC 44 y := by
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) hedgey
      exact (Finset.sum_le_card_nsmul _ _ Mp fun dd _ ↦ hnumbnd y dd).trans_eq
        (by rw [nsmul_eq_mul, mul_comm])
    rw [hErr]
    calc |∑ dd ∈ contr y, divisorNumerator y Ft Gt dd *
          (Tsum dd - 1 / (Nat.totient (qm dd) : ℝ) * Pblk)|
        ≤ ∑ dd ∈ contr y, |divisorNumerator y Ft Gt dd| *
            (‖sumErrorDyadic y (fun n ↦ ((ρ n y : ℝ) : ℂ)) (qm dd) (ares dd + hh i₀)‖
              + (hh i₀ : ℝ)) := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun dd hdd ↦ ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hTbound dd hdd) (abs_nonneg _)
      _ = (∑ dd ∈ contr y, |divisorNumerator y Ft Gt dd| *
            ‖sumErrorDyadic y (fun n ↦ ((ρ n y : ℝ) : ℂ)) (qm dd) (ares dd + hh i₀)‖)
            + (hh i₀ : ℝ) * ∑ dd ∈ contr y, |divisorNumerator y Ft Gt dd| := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun dd _ ↦ by ring
      _ ≤ δ * calC 44 y + δ * calC 44 y := add_le_add hpart1 hpart2
  -- The main term.
  have hdsn : (0 : ℝ) < divisorSumNorm 44 y := by rw [divisorSumNorm]; positivity
  set uu : ℝ := Pblk * Real.log y / y with huudef
  set zz : ℝ := Rsum / divisorSumNorm 44 y with hzzdef
  have hprodeq : Pblk * Rsum = uu * zz * calC 44 y := by
    rw [huudef, hzzdef, ← density_mul_divisorSumNorm 44 hy1]
    field_simp
  have huu1 : |uu - 1| ≤ ε₂ := by
    have hyl : (0 : ℝ) < Real.log y / y := by positivity
    have hid : uu - 1 = ((∑ n ∈ dyadic y, ρ n y) - y / Real.log y) * (Real.log y / y) := by
      rw [huudef, hPblkdef]
      field_simp
    rw [hid, abs_mul, abs_of_nonneg hyl.le]
    exact (mul_le_mul_of_nonneg_right hdensy hyl.le).trans_eq (by field_simp)
  have hmainbnd : |Pblk * Rsum - Pit * calC 44 y| ≤ δ * calC 44 y := by
    rw [hprodeq, ← sub_mul, abs_mul, abs_of_nonneg hcalC]
    refine mul_le_mul_of_nonneg_right ?_ hcalC
    have h2 : |uu| ≤ 1 + ε₂ := by
      linarith [abs_sub_abs_le_abs_sub uu 1, (abs_one : |(1 : ℝ)| = 1)]
    calc |uu * zz - Pit| ≤ |uu * (zz - Pit)| + |(uu - 1) * Pit| := by
          rw [show uu * zz - Pit = uu * (zz - Pit) + (uu - 1) * Pit by ring]
          exact abs_add_le _ _
      _ = |uu| * |zz - Pit| + |uu - 1| * |Pit| := by rw [abs_mul, abs_mul]
      _ ≤ (1 + ε₂) * ε₃ + ε₂ * |Pit| :=
          add_le_add (mul_le_mul h2 hzetay (abs_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_right huu1 (abs_nonneg _))
      _ ≤ δ := by rw [hε₃def] at *; nlinarith [hε₂pos, hδpos]
  -- Assemble.
  have hfinal : (∑ n ∈ Sy, ρ (n + hh i₀) y * ∏ i, lambdaF (F i) y (n + hh i) *
        lambdaF (G i) y (n + hh i)) - F i₀ 0 * G i₀ 0 * Pit * calC 44 y
      = F i₀ 0 * G i₀ 0 * (Pblk * Rsum - Pit * calC 44 y + Err) := by
    rw [hstep1, hstep2, hstep3, hsplit]
    ring
  rw [hfinal, abs_mul, ← hK₀def]
  have hδeq : 3 * δ * (K₀ + 1) = η := by rw [hδdef]; field_simp
  calc K₀ * |Pblk * Rsum - Pit * calC 44 y + Err|
      ≤ K₀ * (δ * calC 44 y + (δ * calC 44 y + δ * calC 44 y)) :=
        mul_le_mul_of_nonneg_left (le_trans (abs_add_le _ _) (add_le_add hmainbnd herrbnd)) hK₀0
    _ ≤ η * calC 44 y := by nlinarith [hcalC, hK₀0, hδpos]

/-- **The sieve asymptotic**, from `Gap212.Sieve.divisor_sum_over_qstar` and
`Gap212.Sieve.weighted_error_negligible`.

Both hypotheses hold: `Gap212.Sieve.TotientGramSumLimitOfSupport` follows from
`Gap212.Sieve.polymath41Totient` by
`Gap212.Sieve.totientGramSumLimitOfSupport_iff_polymath41Totient` (without its support clause the
Gram limit is false, `Gap212.Sieve.not_totientGramSumLimit`), and
`Gap212.Sieve.TotientSievingError 44` is `Gap212.Sieve.totientSievingError`. They are exactly the
hypotheses of `Gap212.Sieve.divisor_sum_over_qstar`;
`Gap212.Sieve.sieveAsymptotic_of_totientGramSumLimitOfSupport` is this theorem with the second
discharged.

**The `d_{i₀} = d'_{i₀} = 1` step does not need the roughness of `ρ`.** The usual route runs it
through the roughness clause `Gap212.Defs.RhoHypotheses.rough_exceeds_cap`
against the retreat coordinate bound. The **minorant** clause is already enough, and more
directly: a shift the weight does not annihilate is *prime*, so its only divisors are `1` and
itself, and `\log_x` of the second is at least `1` while a retreated profile vanishes from `1` on
(`Gap212.Sieve.exists_null_or_forall_eq_zero_of_one_le`). See `Gap212.Sieve.lambdaF_of_prime` and
`Gap212.Sieve.rho_mul_prod_lambdaF_eq`. Primality is used a second time, for the coprimality that
reconciles the average/discrepancy split with `Gap212.sumErrorDyadic`: see
`Gap212.Sieve.sum_class_eq_average_add_discrepancy`. -/
@[gap212 "lem_asymptotics"]
theorem sieveAsymptotic_of_obligations (hgram : TotientGramSumLimitOfSupport)
    (hsieve : TotientSievingError 44) : SieveAsymptotic 44 := by
  classical
  intro p ε₀ hε₀ hε₀' j j' hA ρ β hρ heq hh hmono i₀ F G hFC hGC hFB hGB hFsupp hGsupp hmarg η hη
  -- A factor vanishing on all of `[0,∞)`, or a vanishing boundary value at the removed
  -- coordinate, makes both sides identically zero.
  have hdeg : ((∃ i, (∀ t : ℝ, 0 ≤ t → F i t = 0) ∨ ∀ t : ℝ, 0 ≤ t → G i t = 0) ∨
      (∀ i, ∀ t : ℝ, 1 ≤ t → F i t = 0) ∧ (∀ i, ∀ t : ℝ, 1 ≤ t → G i t = 0) ∧
        F i₀ 0 * G i₀ 0 = 0) →
      ∃ X : ℝ, ∀ x > X, ∀ b : ℕ, IsPreSieved b (W x) hh →
        |(∑ n ∈ dyadic x with n % W x = b % W x,
              ρ (n + hh i₀) x * ∏ i, lambdaF (F i) x (n + hh i) * lambdaF (G i) x (n + hh i)) -
            (F i₀ 0 * G i₀ 0 * ∏ s : Fin 44, ∫ t in Set.Ioi (0 : ℝ),
                deriv (F (i₀.succAbove s)) t * deriv (G (i₀.succAbove s)) t) * scale (44 + 1) x|
          ≤ η * scale (44 + 1) x := by
    intro hd
    refine ⟨1, fun x hx1 b _ ↦ ?_⟩
    have hx1' : (1 : ℝ) < x := hx1
    suffices hL : (∑ n ∈ dyadic x with n % W x = b % W x,
        ρ (n + hh i₀) x * ∏ i, lambdaF (F i) x (n + hh i) * lambdaF (G i) x (n + hh i)) = 0 ∧
        F i₀ 0 * G i₀ 0 * ∏ s : Fin 44, ∫ t in Set.Ioi (0 : ℝ),
          deriv (F (i₀.succAbove s)) t * deriv (G (i₀.succAbove s)) t = 0 by
      rw [hL.1, hL.2, zero_mul, sub_zero, abs_zero]
      exact mul_nonneg hη.le (scale_pos hx1' (primorial_pos _)).le
    rcases hd with ⟨i, hi⟩ | ⟨hF1, hG1, hFG0⟩
    · refine ⟨Finset.sum_eq_zero fun n _ ↦ ?_, ?_⟩
      · rw [Finset.prod_eq_zero (Finset.mem_univ i) ?_, mul_zero]
        rcases hi with h | h <;> simp [lambdaF_eq_zero_of_null hx1' h]
      rcases eq_or_ne i i₀ with rfl | hne
      · rcases hi with h | h <;> simp [h 0 le_rfl]
      obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hne
      rw [Finset.prod_eq_zero (Finset.mem_univ s) ?_, mul_zero]
      rcases hi with h | h
      · exact setIntegral_deriv_eq_zero_of_null h
      · rw [setIntegral_deriv_congr_nonneg (F₂ := F (i₀.succAbove s)) (G₂ := fun _ ↦ (0 : ℝ))
          (fun _ _ ↦ rfl) h]
        simp
    · refine ⟨Finset.sum_eq_zero fun n hn ↦ ?_, by rw [hFG0, zero_mul]⟩
      rw [rho_mul_prod_lambdaF_eq hx1' hρ i₀ hF1 hG1 (Finset.mem_filter.mp hn).1, hFG0, zero_mul]
  rcases exists_null_or_forall_eq_zero_of_one_le hε₀.le hFsupp with ⟨iF, hiF⟩ | hF1
  · exact hdeg (.inl ⟨iF, .inl hiF⟩)
  rcases exists_null_or_forall_eq_zero_of_one_le hε₀.le hGsupp with ⟨iG, hiG⟩ | hG1
  · exact hdeg (.inl ⟨iG, .inr hiG⟩)
  by_cases hFG0 : F i₀ 0 * G i₀ 0 = 0
  · exact hdeg (.inr ⟨hF1, hG1, hFG0⟩)
  exact sieveAsymptotic_core hgram hsieve p hε₀ hε₀' j j' hA hρ heq hmono i₀ hFC hGC hFB hGB
    hFsupp hGsupp hmarg hF1 hG1 (left_ne_zero_of_mul hFG0) (right_ne_zero_of_mul hFG0) hη

/-- **The numerator asymptotic from the two hypotheses of the divisor sum over `Q⋆`.**
`Gap212.Sieve.numeratorAsymptotic_of_sieveAsymptotic` composed with
`Gap212.Sieve.sieveAsymptotic_of_obligations`. Since `Gap212.Sieve.TotientSievingError 44` is
`Gap212.Sieve.totientSievingError`,
`Gap212.Sieve.numeratorAsymptotic_of_totientGramSumLimitOfSupport` needs
`Gap212.Sieve.TotientGramSumLimitOfSupport` alone. -/
theorem numeratorAsymptotic_of_obligations (hgram : TotientGramSumLimitOfSupport)
    (hsieve : TotientSievingError 44) : NumeratorAsymptotic 44 :=
  numeratorAsymptotic_of_sieveAsymptotic (sieveAsymptotic_of_obligations hgram hsieve)

/-! ## The sieve asymptotic from the Gram limit -/

/-- **The sieve asymptotic from the Gram limit alone.**
`Gap212.Sieve.sieveAsymptotic_of_obligations` with its second hypothesis discharged by
`Gap212.Sieve.totientSievingError`, which proves `Gap212.Sieve.TotientSievingError m` at every
`m`. -/
theorem sieveAsymptotic_of_totientGramSumLimitOfSupport (hgram : TotientGramSumLimitOfSupport) :
    SieveAsymptotic 44 :=
  sieveAsymptotic_of_obligations hgram (totientSievingError 44)

/-- **The numerator asymptotic from the Gram limit alone**, by
`Gap212.Sieve.numeratorAsymptotic_of_sieveAsymptotic` composed with
`Gap212.Sieve.sieveAsymptotic_of_totientGramSumLimitOfSupport`. The denominator analogue is
`Gap212.Sieve.nuDenominator_of_lcmGramSumLimitOfSupport`. -/
theorem numeratorAsymptotic_of_totientGramSumLimitOfSupport
    (hgram : TotientGramSumLimitOfSupport) : NumeratorAsymptotic 44 :=
  numeratorAsymptotic_of_sieveAsymptotic (sieveAsymptotic_of_totientGramSumLimitOfSupport hgram)

end Gap212.Sieve
