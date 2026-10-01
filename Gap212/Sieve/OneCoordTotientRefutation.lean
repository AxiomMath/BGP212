/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.GramDatum
public import Gap212.Sieve.OneCoordLcmRefutation

/-!
# The totient-weight one-coordinate estimate at level `s` is false

`Gap212.Sieve.OneCoordTotientDecayAtLevel` is refuted here, at every exponent `s`
(`Gap212.Sieve.not_oneCoordTotientDecayAtLevel`), by the top block of moduli in the Selberg
diagonalisation of the totient-weight pair sum
(`Gap212.Sieve.sum_pairs_div_totient_lcm_eq_sum_moebiusTotient_mul_sq`), which is a sum of squares.

The statement `Gap212.Sieve.OneCoordTotientDecayAtLevelOfSupport` adds the hypothesis that the
profiles vanish from `β` on, and
`Gap212.Sieve.tendsto_boxDivisorSum_sub_sievedDivisorSum_of_support` derives the conclusion of
`Gap212.Sieve.TotientSievingError` from it.

## Main results

* `Gap212.Sieve.sum_pairs_div_totient_lcm_eq_sum_moebiusTotient_mul_sq`: the Selberg
  diagonalisation at the totient denominator.
* `Gap212.Sieve.totient_sq_le_two_mul_moebiusTotient`: the weight of a squarefree modulus with no
  small prime factor is of size `1/r`.
* `Gap212.Sieve.not_oneCoordTotientDecayAtLevel`: the refutation.
* `Gap212.Sieve.tendsto_boxDivisorSum_sub_sievedDivisorSum_of_support`: the totient sieving error
  at `β ≥ 1` from `Gap212.Sieve.OneCoordTotientDecayAtLevelOfSupport`.
-/

@[expose] public section

namespace Gap212.Sieve

open Asymptotics Filter Finset Gap212.Defs Gap212.GPY
open scoped ArithmeticFunction.Moebius

/-! ## Selberg diagonalisation of the totient-weight one-coordinate pair sum -/

/-- **`Gap212.Sieve.sum_divisors_moebiusTotient` read inside a truncated range.** -/
theorem sum_filter_Icc_moebiusTotient_eq_totient_gcd {B d d' : ℕ} (hd1 : 1 ≤ d) (hdB : d ≤ B) :
    ∑ r ∈ Icc 1 B with r ∣ d ∧ r ∣ d', moebiusTotient r = (Nat.totient (Nat.gcd d d') : ℝ) := by
  rw [filter_Icc_dvd_dvd_eq_divisors_gcd hd1 hdB]
  exact sum_divisors_moebiusTotient (Nat.gcd_pos_of_pos_left _ hd1)

/-- **The Selberg diagonalisation of a one-coordinate pair sum at the totient denominator.** For
any weight `l` on a finset `D ⊆ [1,B]`,

  `∑_{d,d' ∈ D} l(d)l(d')/φ([d,d']) = ∑_{r ≤ B} (μ*φ)(r)·(∑_{d ∈ D, r ∣ d} l(d)/φ(d))^2`.

This is `Gap212.Sieve.sum_pairs_div_lcm_eq_sum_totient_mul_sq` with `φ` for the identity: the
kernel `1/φ([d,d'])` is `φ((d,d'))/(φ(d)φ(d'))` (`Gap212.Sieve.div_totient_lcm_eq`, which needs no
squarefreeness — `φ((a,b))φ([a,b]) = φ(a)φ(b)` holds outright), and `φ((d,d'))` is expanded over
the common divisors by `Gap212.Sieve.sum_divisors_moebiusTotient`. An exact identity, no estimate.

**Its content is that the right side is a sum of squares** — the totient denominator changes the
weight from `φ(r)` to `(μ*φ)(r) = ∏_{p ∣ r}(p-2)` and nothing else. So the one-coordinate totient
pair sum at `e = 1` and `F = G` is bounded below by the contribution of any family of moduli whose
weight is nonnegative, and `Gap212.Sieve.moebiusTotient_nonneg_of_squarefree` says the squarefree
moduli are such a family. -/
theorem sum_pairs_div_totient_lcm_eq_sum_moebiusTotient_mul_sq (B : ℕ) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ B) (l : ℕ → ℝ) :
    ∑ d ∈ D, ∑ d' ∈ D, l d * l d' / (Nat.totient (Nat.lcm d d') : ℝ)
      = ∑ r ∈ Icc 1 B, moebiusTotient r *
          (∑ d ∈ D with r ∣ d, l d / (Nat.totient d : ℝ)) ^ 2 := by
  simp_rw [sq, Finset.sum_filter, Finset.sum_mul_sum, Finset.mul_sum, ite_zero_mul_ite_zero,
    mul_ite, mul_zero]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d' hd' ↦ ?_
  obtain ⟨hd1, hdB⟩ := hD d hd
  rw [← Finset.sum_filter, ← Finset.sum_mul, sum_filter_Icc_moebiusTotient_eq_totient_gcd hd1 hdB,
    div_totient_lcm_eq hd1 (hD d' hd').1]
  ring

/-! ## The top block: the weight is nonnegative, and of size `1/r` -/

/-- **The Gram weight is nonnegative on the squarefree integers**: `(μ*φ)(r) = ∏_{p ∣ r}(p-2)` and
every prime is at least `2`. This is what makes dropping moduli from
`Gap212.Sieve.sum_pairs_div_totient_lcm_eq_sum_moebiusTotient_mul_sq` a legitimate lower bound.

**`(μ*φ)(2) = 0`**, so the statement is not that the weight is positive, and a family of moduli
whose members may be even would carry no lower bound at all. The refutation's family is coprime to
`W(x)`, which is even, so every member is odd. -/
theorem moebiusTotient_nonneg_of_squarefree {r : ℕ} (hr : Squarefree r) : 0 ≤ moebiusTotient r := by
  rw [moebiusTotient_of_squarefree hr]
  exact Finset.prod_nonneg fun p hp ↦
    sub_nonneg.mpr (mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)

/-- **A modulus with a non-squarefree part sees no member of a squarefree family.** -/
theorem sum_filter_dvd_eq_zero_of_not_squarefree {D : Finset ℕ} (hsf : ∀ d ∈ D, Squarefree d)
    {r : ℕ} (hr : ¬ Squarefree r) (l : ℕ → ℝ) :
    ∑ d ∈ D with r ∣ d, l d / (Nat.totient d : ℝ) = 0 := by
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  obtain ⟨hdD, hrd⟩ := Finset.mem_filter.mp hd
  exact absurd ((hsf d hdD).squarefree_of_dvd hrd) hr

/-- **The totient-weight pair sum at `e = 1` dominates any block of top moduli.** The companion of
`Gap212.Sieve.sum_block_le_sum_pairs_div_lcm`: the diagonalisation
`Gap212.Sieve.sum_pairs_div_totient_lcm_eq_sum_moebiusTotient_mul_sq` is a sum of squares, and
above `B/2` the inner sum is the single term `l(r)/φ(r)`
(`Gap212.Sieve.filter_dvd_eq_singleton`).

Every member of `D` is required to be squarefree — which costs nothing at `l(d) = μ(d)F(\log_xd)`,
whose non-squarefree terms vanish — because that is what makes the *discarded* moduli harmless: a
non-squarefree `r` has an empty inner sum
(`Gap212.Sieve.sum_filter_dvd_eq_zero_of_not_squarefree`), and a squarefree one carries a
nonnegative weight (`Gap212.Sieve.moebiusTotient_nonneg_of_squarefree`). -/
theorem sum_block_le_sum_pairs_div_totient_lcm (B : ℕ) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ B) (hsf : ∀ d ∈ D, Squarefree d) (l : ℕ → ℝ) (Fam : Finset ℕ)
    (hsub : Fam ⊆ Icc 1 B) (hblk : ∀ r ∈ Fam, B < 2 * r ∧ r ∈ D) :
    ∑ r ∈ Fam, moebiusTotient r * (l r / (Nat.totient r : ℝ)) ^ 2
      ≤ ∑ d ∈ D, ∑ d' ∈ D, l d * l d' / (Nat.totient (Nat.lcm d d') : ℝ) := by
  rw [sum_pairs_div_totient_lcm_eq_sum_moebiusTotient_mul_sq B D hD l]
  refine (Finset.sum_congr rfl fun r hr ↦ ?_).trans_le
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ ↦ ?_)
  · rw [filter_dvd_eq_singleton hD (hblk r hr).1 (hblk r hr).2, Finset.sum_singleton]
  · by_cases hrs : Squarefree r
    · exact mul_nonneg (moebiusTotient_nonneg_of_squarefree hrs) (sq_nonneg _)
    · simp [sum_filter_dvd_eq_zero_of_not_squarefree hsf hrs]

/-- **The Gram weight of a squarefree modulus with no small prime factor is of size `1/r`**:
`φ(r)^2 ≤ 2r(μ*φ)(r)`.

Both sides are products over the primes dividing `r`, and
`p(p-2) = (p-1)^2(1 - 1/(p-1)^2)`, so what has to be beaten is
`∏_{p ∣ r}(1 - 1/(p-1)^2) ≥ 1/2`. With every prime factor above `100`,
`Gap212.Sieve.one_sub_sum_le_prod_one_sub` reduces that to `∑_{p ∣ r}1/(p-1)^2 ≤ 1/2`, and
`p ↦ p-1` embeds the prime factors injectively into `[100,r]`, where
`Gap212.Sieve.sum_Icc_one_div_sq_le` gives `1/99`.

The hypothesis on the prime factors is needed: at `p = 2` the left side is `1` and the right side
is `0`, and the bound is false for every even `r`. -/
theorem totient_sq_le_two_mul_moebiusTotient {r : ℕ} (hr : Squarefree r)
    (hbig : ∀ p : ℕ, p.Prime → p ∣ r → 100 < p) :
    (Nat.totient r : ℝ) ^ 2 ≤ 2 * (r : ℝ) * moebiusTotient r := by
  classical
  have hbigF : ∀ p ∈ r.primeFactors, 101 ≤ p := fun p hp ↦
    hbig p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hbigR : ∀ p ∈ r.primeFactors, (101 : ℝ) ≤ (p : ℝ) := fun p hp ↦ by
    exact_mod_cast hbigF p hp
  -- ### the prime-reciprocal sum over the prime factors
  have hsum : ∑ p ∈ r.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 1 / 99 := by
    have himg : r.primeFactors.image (fun p : ℕ ↦ p - 1) ⊆ Icc (99 + 1) r := by
      intro n hn
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
      have := hbigF p hp
      have := Nat.le_of_mem_primeFactors hp
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    calc ∑ p ∈ r.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) ^ 2
        = ∑ n ∈ r.primeFactors.image (fun p : ℕ ↦ p - 1), (1 : ℝ) / (n : ℝ) ^ 2 := by
          rw [Finset.sum_image fun a ha b hb ↦
            Nat.sub_one_cancel (Nat.pos_of_mem_primeFactors ha) (Nat.pos_of_mem_primeFactors hb)]
          exact Finset.sum_congr rfl fun p hp ↦ by
            rw [Nat.cast_pred (Nat.pos_of_mem_primeFactors hp)]
      _ ≤ ∑ n ∈ Icc (99 + 1) r, (1 : ℝ) / (n : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun n _ _ ↦ by positivity
      _ ≤ 1 / 99 := sum_Icc_one_div_sq_le (by norm_num) r
  -- ### so the product of local defects is at least `1/2`
  have hprod : (1 : ℝ) / 2 ≤ ∏ p ∈ r.primeFactors, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2) := by
    linarith [one_sub_sum_le_prod_one_sub (a := fun p : ℕ ↦ 1 / ((p : ℝ) - 1) ^ 2)
      (fun p _ ↦ by positivity) fun p hp ↦
        div_le_one_of_le₀ (by nlinarith [hbigR p hp]) (by positivity)]
  -- ### the two sides as products over the prime factors
  have hrprod : (r : ℝ) = ∏ p ∈ r.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hr]
  have hsplit : (∏ p ∈ r.primeFactors, (p : ℝ)) * ∏ p ∈ r.primeFactors, ((p : ℝ) - 2)
      = (∏ p ∈ r.primeFactors, ((p : ℝ) - 1) ^ 2) *
          ∏ p ∈ r.primeFactors, (1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    have : (p : ℝ) - 1 ≠ 0 := by linarith [hbigR p hp]
    field_simp
    ring
  rw [totient_of_squarefree hr, moebiusTotient_of_squarefree hr, ← Finset.prod_pow, hrprod,
    mul_assoc, hsplit]
  nlinarith [Finset.prod_nonneg fun p (_ : p ∈ r.primeFactors) ↦ sq_nonneg ((p : ℝ) - 1)]

/-! ## The refutation -/

/-- **`Gap212.Sieve.OneCoordTotientDecayAtLevel s` is false, for every `s`**, so the hypothesis
of `Gap212.Sieve.totientSievingError_of_oneCoordTotientDecayAtLevel` is never satisfied.

This is `Gap212.Sieve.not_oneCoordLcmDecayAtLevel` with the totient denominator, with the same
witness. Read the estimate at `β = 1`, at the truncation `B = ⌈x⌉` — so the hypothesis `x^β ≤ B`
is *satisfied* — and at the modulus `e = 1` — so the exponent `s` is irrelevant — with any `C¹`
compactly supported `F` with `F(1) = 1`, which does **not** vanish at `\log_xB = 1`.

At `F = G` the sum is a sum of squares
(`Gap212.Sieve.sum_pairs_div_totient_lcm_eq_sum_moebiusTotient_mul_sq`),

  `∑_{d,d'}μ(d)μ(d')F(\log_xd)F(\log_xd')/φ([d,d'])
     = ∑_{r ≤ B}(μ*φ)(r)(∑_{r ∣ d}μ(d)F(\log_xd)/φ(d))^2`,

so there is no cancellation left to appeal to and dropping moduli is a legitimate lower bound. Keep
only `r ∈ (B/2,B]`, where the inner sum is the single term `μ(r)F(\log_xr)/φ(r)`
(`Gap212.Sieve.filter_dvd_eq_singleton`), and `F(\log_xr) → F(1) = 1` uniformly. The weight of such
an `r` is `(μ*φ)(r)/φ(r)^2 ≥ 1/(2r)`
(`Gap212.Sieve.totient_sq_le_two_mul_moebiusTotient`), exactly the size the `[d,d']` weight
`φ(r)/r^2` has, so the block contributes at least `\#Fam/(8B)`;
`Gap212.Sieve.exists_dense_squarefree_block` makes that `1/(32W(x))`, against an asserted
`K/B_x ≤ KW(x)/\log x`. That needs `\log x ≤ 32KW(x)^2`, and
`Gap212.Sieve.eventually_const_mul_W_sq_lt_log` says the opposite.

**Where coprimality to `W(x)` is used.** `(μ*φ)(2) = 0`, so an even modulus contributes nothing
and a block containing even moduli would carry no lower bound at all. The family is coprime to
`W(x)`, which is even and absorbs every prime up to `\log\log\log x`; so every member is odd, every
prime factor of a member exceeds `100`, and `Gap212.Sieve.totient_sq_le_two_mul_moebiusTotient`
applies. The same coprimality is what `Gap212.Sieve.exists_dense_squarefree_block` counts with.

The statement requiring the profiles to vanish from `β` on is
`Gap212.Sieve.OneCoordTotientDecayAtLevelOfSupport`. -/
theorem not_oneCoordTotientDecayAtLevel (s : ℝ) : ¬ OneCoordTotientDecayAtLevel s := by
  classical
  intro h
  -- a `C¹` bump with `F(1) = 1`
  obtain ⟨F, -, hFc, hFd, -, hF1⟩ := exists_contDiff_tsupport_subset
    (E := ℝ) (s := Set.univ) (x := (1 : ℝ)) (n := 1) Filter.univ_mem
  have hFcd : ContDiff ℝ 1 F := by exact_mod_cast hFd
  obtain ⟨K, hK, hev⟩ := h 1 one_pos F F hFcd hFc hFcd hFc
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp (hFcd.continuous.continuousAt (x := (1 : ℝ)))
    (1 / 2) (by norm_num)
  have hFhalf : ∀ t : ℝ, |t - 1| < δ → (1 : ℝ) / 2 < F t := fun t ht ↦ by
    have := hδ (x := t) (by rwa [Real.dist_eq])
    rw [Real.dist_eq, hF1] at this
    linarith [(abs_lt.mp this).1]
  -- the largeness conditions on `x`
  obtain ⟨x, hxK, hxW, hxsq, hxC, hxδ, hx2, hxw⟩ := (hev.and <| W_sq_le_log.and <|
    (eventually_const_mul_log_le 1225).and <| (eventually_const_mul_W_sq_lt_log (32 * K + 1)).and <|
    (Real.tendsto_log_atTop.eventually_gt_atTop (Real.log 2 / δ)).and <|
    (eventually_gt_atTop (2 : ℝ)).and <| (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      Real.tendsto_log_atTop)).eventually_ge_atTop (100 : ℝ)).exists
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  set B : ℕ := ⌈x⌉₊ with hBdef
  have hxB : x ≤ (B : ℝ) := Nat.le_ceil x
  have hB0 : (0 : ℝ) < (B : ℝ) := by linarith
  have hW0 : 0 < W x := primorial_pos _
  have hWR : (0 : ℝ) < (W x : ℝ) := by exact_mod_cast hW0
  have hφ1 : (1 : ℝ) ≤ ((W x).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hW0
  -- ### the dense family of top moduli
  have hw100 : 100 ≤ ⌊Real.log (Real.log (Real.log x))⌋₊ := Nat.le_floor (by exact_mod_cast hxw)
  have hMw : ∀ p : ℕ, p.Prime → p ≤ ⌊Real.log (Real.log (Real.log x))⌋₊ → p ∣ W x :=
    fun p hp hpw ↦ hp.dvd_primorial_iff.mpr hpw
  have hMB : (35 * W x) ^ 2 ≤ B := by
    exact_mod_cast (by nlinarith : ((35 : ℝ) * W x) ^ 2 ≤ B)
  obtain ⟨Fam, hFam, hFamcard⟩ :=
    exists_dense_squarefree_block hW0 hw100 hMw hMB
  -- ### the profile is above `1/2` on the block
  have hblockF : ∀ r ∈ Fam, (1 : ℝ) / 2 < F (Notation.logx x r) := by
    intro r hr
    obtain ⟨⟨hr1, hrB⟩, hblk, -, -, -⟩ := hFam r hr
    refine hFhalf _ ?_
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
    have hrB' : (r : ℝ) ≤ B := by exact_mod_cast hrB
    have hBr : (B : ℝ) < 2 * r := by exact_mod_cast hblk
    have hBlt : (B : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
    have hup : Real.log r < Real.log x + Real.log 2 := by
      rw [← Real.log_mul (by linarith) (by norm_num)]
      exact Real.log_lt_log hr0 (by linarith)
    have hlow : Real.log x - Real.log 2 < Real.log r := by
      rw [← Real.log_div (by linarith) (by norm_num)]
      exact Real.log_lt_log (by linarith) (by linarith)
    rw [div_lt_iff₀ hδ0] at hxδ
    rw [Notation.logx, div_sub_one hlogx.ne', abs_div, abs_of_pos hlogx, div_lt_iff₀ hlogx]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  -- ### the pair sum at `e = 1` is at least `1/(32W(x))`
  set l : ℕ → ℝ := fun d ↦ (μ d : ℝ) * F (Notation.logx x d) with hldef
  set D : Finset ℕ := {d ∈ wBox x B | Squarefree d} with hDdef
  have hDsub : D ⊆ wBox x B := Finset.filter_subset _ _
  have hl0 : ∀ d ∈ wBox x B, d ∉ D → l d = 0 := fun d hd hnd ↦ by
    simp [hldef, ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      fun hs ↦ hnd (Finset.mem_filter.mpr ⟨hd, hs⟩)]
  have hexpand : ∑ d ∈ wBox x B, ∑ d' ∈ wBox x B, pairWeightTotient x F F (d, d')
      = ∑ d ∈ D, ∑ d' ∈ D, l d * l d' / (Nat.totient (Nat.lcm d d') : ℝ) := by
    change ∑ d ∈ wBox x B, ∑ d' ∈ wBox x B, l d * l d' / (Nat.totient (Nat.lcm d d') : ℝ) = _
    exact ((Finset.sum_subset hDsub fun d hd hnd ↦ Finset.sum_eq_zero fun d' _ ↦ by
        rw [hl0 d hd hnd, zero_mul, zero_div]).trans
      (Finset.sum_congr rfl fun d _ ↦ Finset.sum_subset hDsub fun d' hd' hnd' ↦ by
        rw [hl0 d' hd' hnd', mul_zero, zero_div])).symm
  have hlowsum : ∑ r ∈ Fam, moebiusTotient r * (l r / (Nat.totient r : ℝ)) ^ 2
      ≤ restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeightTotient x F F) 1 := by
    rw [restrictedSum_one, Finset.sum_product, hexpand]
    refine sum_block_le_sum_pairs_div_totient_lcm B D (fun d hd ↦ (mem_wBox.mp (hDsub hd)).1)
      (fun d hd ↦ (Finset.mem_filter.mp hd).2) l Fam (fun r hr ↦ Finset.mem_Icc.mpr (hFam r hr).1)
      fun r hr ↦ ?_
    obtain ⟨h1B, hb, hcop, hsf, -⟩ := hFam r hr
    exact ⟨hb, Finset.mem_filter.mpr ⟨mem_wBox.mpr ⟨h1B, hcop⟩, hsf⟩⟩
  have hterm : ∀ r ∈ Fam,
      (1 : ℝ) / (8 * (B : ℝ)) ≤ moebiusTotient r * (l r / (Nat.totient r : ℝ)) ^ 2 := by
    intro r hr
    obtain ⟨⟨hr1, hrB⟩, -, hcop, hsf, -⟩ := hFam r hr
    have hrRB : (r : ℝ) ≤ (B : ℝ) := by exact_mod_cast hrB
    -- every prime factor of a member of the block exceeds `100`
    have hbig : ∀ p : ℕ, p.Prime → p ∣ r → 100 < p := fun p hp hpr ↦ by
      by_contra
      exact hp.ne_one (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd (hMw p hp (by omega)) hpr))
    have hkey := totient_sq_le_two_mul_moebiusTotient hsf hbig
    have hμφ := moebiusTotient_nonneg_of_squarefree hsf
    have hφ0 : (0 : ℝ) < (Nat.totient r : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hr1
    have hl2 : (1 : ℝ) / 4 ≤ l r ^ 2 := by
      have hmu : ((μ r : ℤ) : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
      simp only [hldef, mul_pow, hmu, one_mul]
      nlinarith [hblockF r hr]
    rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl2 hμφ) hB0.le,
      mul_nonneg hμφ (sub_nonneg.2 hrRB)]
  -- ### against the asserted bound
  have hbd := hxK B 1 (by rwa [Real.rpow_one]) one_pos
  rw [Nat.cast_one, Real.one_rpow, mul_one] at hbd
  have hQ : 1 / (32 * (W x : ℝ)) ≤ K * W x / Real.log x := calc
    1 / (32 * (W x : ℝ)) = B / (4 * W x) * (1 / (8 * B)) := by field_simp; ring
    _ ≤ Fam.card * (1 / (8 * B)) := by gcongr
    _ = ∑ _r ∈ Fam, (1 : ℝ) / (8 * (B : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := (Finset.sum_le_sum hterm).trans hlowsum
    _ ≤ K / ((W x).totient / W x * Real.log x) := (le_abs_self _).trans hbd
    _ = K * W x / ((W x).totient * Real.log x) := by
      rw [div_mul_eq_mul_div, div_div_eq_mul_div]
    _ ≤ K * W x / Real.log x :=
      div_le_div_of_nonneg_left (mul_nonneg hK hWR.le) hlogx (le_mul_of_one_le_left hlogx.le hφ1)
  rw [div_le_div_iff₀ (by positivity) hlogx] at hQ
  linarith [pow_pos hWR 2]

/-! ## The one-coordinate estimate for profiles vanishing from `β` on -/

/-- **The totient-weight one-coordinate estimate with the profiles required to vanish from `β`
on**, the analogue of the clause of `Gap212.Sieve.TotientGramSumLimitOfSupport`. The bound is

  `|∑_{(d,d') ∈ [1,B]^2, (dd',W)=1, e ∣ [d,d']} μ(d)F(\log_xd)μ(d')G(\log_xd')/φ([d,d'])|
      ≤ K/(B_x·e^s)`,  `B_x = (φ(W)/W)\log x`,

asked for at truncations `B ≥ x^β` and only for profiles supported below `β`, so the truncation
does not cut the profiles' support.

Three witnesses refute weaker forms of this statement, and none applies to it.
`Gap212.Sieve.not_oneCoordTotientDecay` reads the truncation-free form at `B = 1`, where the box is
a single point: excluded by `x^β ≤ B`. The two-prime witness of the module docstring of
`Gap212.Sieve.SievingErrorReduction` needs `e = PQ ≍ B^2`: excluded by `s < 1`, and
independently by the support clause, both primes lying in the top of the box where the profiles
vanish. And `Gap212.Sieve.not_oneCoordTotientDecayAtLevel` reads the form without the support
clause at `β = 1`, `B = ⌈x⌉`, `e = 1` and a profile with `F(1) = 1`, where the top block of moduli
`r ∈ (B/2,B]` contributes `≍1/W(x)`, uncancelled, against an asserted `K/B_x`. With the clause the
same block contributes `O(\log^{-2}x)`, because a `C¹` profile vanishing from `β` on satisfies
`|F(\log_xr)| ≤ \|F'\|_∞(β - \log_xr) ≪ 1/\log x` for `r` within a constant factor of `x^β`.

The diagonalisation leaves `∑_r(μ*φ)(r)z_rz'_r` with `z_r = ∑_{r ∣ d}μ(d)F(\log_xd)/φ(d)`, so the
estimate reduces to each `z_r` being small:
`Gap212.Sieve.oneCoordTotientDecayAtLevelOfSupport_of_smoothMoebiusTotientInnerBound` derives this
statement at `s = 3/4` from `Gap212.Sieve.SmoothMoebiusTotientInnerBound`, the pointwise bound
`|z_r| ≤ C(W/φ(W))/((μ*φ)(r)\log x)`. The denominator there is `(μ*φ)(r)`, not `φ(r)` or `r`;
both of those readings are refuted by the primorial block `r = ∏_{\log\log\log x<p≤z}p`. -/
def OneCoordTotientDecayAtLevelOfSupport (s : ℝ) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ F G : ℝ → ℝ,
    ContDiff ℝ 1 F → HasCompactSupport F → ContDiff ℝ 1 G → HasCompactSupport G →
    (∀ t : ℝ, β ≤ t → F t = 0) → (∀ t : ℝ, β ≤ t → G t = 0) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop, ∀ B e : ℕ, x ^ β ≤ (B : ℝ) → 0 < e →
      |restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeightTotient x F G) e|
        ≤ K / ((((W x).totient : ℝ) / (W x : ℝ) * Real.log x) * (e : ℝ) ^ s)

/-- `Gap212.Sieve.OneCoordTotientDecayAtLevel` implies
`Gap212.Sieve.OneCoordTotientDecayAtLevelOfSupport`, the latter having two more hypotheses. -/
theorem oneCoordTotientDecayAtLevelOfSupport_of_oneCoordTotientDecayAtLevel {s : ℝ}
    (h : OneCoordTotientDecayAtLevel s) : OneCoordTotientDecayAtLevelOfSupport s :=
  fun β hβ F G hF hFc hG hGc _ _ ↦ h β hβ F G hF hFc hG hGc

/-- **A null factor kills the sieved divisor sum too**, the companion of
`Gap212.Sieve.boxDivisorSum_eq_zero_of_null`: `Gap212.Sieve.sievedPairs` carries the same summand
on a smaller index set. -/
theorem sievedDivisorSum_eq_zero_of_null {m : ℕ} {F G : Fin m → ℝ → ℝ} {i₀ : Fin m}
    (hnull : (∀ t : ℝ, 0 ≤ t → F i₀ t = 0) ∨ ∀ t : ℝ, 0 ≤ t → G i₀ t = 0) {x : ℝ} (hx : 1 < x)
    (B : ℕ) : sievedDivisorSum x B F G = 0 := by
  classical
  refine Finset.sum_eq_zero fun dd hdd ↦ ?_
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hdd).1
  have hd : ∀ i, 1 ≤ dd.1 i := fun i ↦
    (Finset.mem_Icc.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp h1 i)).1).1
  have hd' : ∀ i, 1 ≤ dd.2 i := fun i ↦
    (Finset.mem_Icc.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp h2 i)).1).1
  rw [sepSummand, divisorNumerator_eq_zero_of_null hnull hx hd hd', zero_div]

/-- **The totient sieving error at `β ≥ 1`, from the one-coordinate estimate for supported
profiles.** This is the conclusion of `Gap212.Sieve.TotientSievingError m`, which is stated at
`β ≥ 1`; `Gap212.Sieve.totientSievingError` is this with the hypothesis discharged.

The restriction `β ≥ 1` matches the hypotheses: `Gap212.Sieve.OneCoordTotientDecayAtLevelOfSupport`
asks that the profiles vanish from `β` on, and the reduced retreat gives that they vanish from `1`
on (`Gap212.Sieve.exists_null_or_forall_eq_zero_of_one_le_insertNth`), or that one of them is null
and both sums vanish identically (`Gap212.Sieve.boxDivisorSum_eq_zero_of_null`,
`Gap212.Sieve.sievedDivisorSum_eq_zero_of_null`). At `β < 1` the truncation `B ≍ x^β` cuts a
profile's support and the one-coordinate sums are `≍1/W(x)` rather than `≍1/B_x`
(`Gap212.Sieve.not_oneCoordTotientDecayAtLevel`).

Otherwise the proof is that of `Gap212.Sieve.totientSievingError_of_oneCoordTotientDecayAtLevel`:
the `m`-coordinate coupling is
`Gap212.Sieve.exists_threshold_abs_prod_sub_sum_pairwise_coprime_le_rpow`, the one-coordinate input
is the hypothesis, and `Gap212.Sieve.divisorSumNorm` absorbs the modulus's own `φ(W(x))`. -/
theorem tendsto_boxDivisorSum_sub_sievedDivisorSum_of_support {s : ℝ} (hs : 1 / 2 < s)
    (hdec : OneCoordTotientDecayAtLevelOfSupport s) (p : SupportParams) {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀)
    {m : ℕ} {j j' : Fin p.n} {i₀ : Fin (m + 1)} (F G : Fin m → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ 1 (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    (hsupp : IsReducedRetreat p m j j' ε₀ i₀ F G)
    {β : ℝ} (hβ1 : 1 ≤ β) (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦
        (boxDivisorSum x (B x) F G - sievedDivisorSum x (B x) F G) / divisorSumNorm m x)
      atTop (nhds 0) := by
  classical
  have hβ : 0 < β := by linarith
  -- the null cases: both sums vanish identically
  have hnullcase : ∀ i' : Fin m,
      ((∀ t : ℝ, 0 ≤ t → F i' t = 0) ∨ ∀ t : ℝ, 0 ≤ t → G i' t = 0) →
      Tendsto (fun x : ℝ ↦
          (boxDivisorSum x (B x) F G - sievedDivisorSum x (B x) F G) / divisorSumNorm m x)
        atTop (nhds 0) := by
    intro i' hn
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [boxDivisorSum_eq_zero_of_null hn hx, sievedDivisorSum_eq_zero_of_null hn hx, sub_self,
      zero_div]
  rcases exists_null_or_forall_eq_zero_of_one_le_insertNth hε₀
      (fun t ht hne ↦ ((hsupp t ht).1 hne).1) with ⟨i', hnF⟩ | hF1
  · exact hnullcase i' (Or.inl hnF)
  rcases exists_null_or_forall_eq_zero_of_one_le_insertNth hε₀
      (fun t ht hne ↦ (hsupp t ht).2 hne) with ⟨i', hnG⟩ | hG1
  · exact hnullcase i' (Or.inr hnG)
  refine Metric.tendsto_nhds.mpr fun ε' hε' ↦ ?_
  -- the support clause at `β`, from the retreat's clause at `1`
  choose K hK hKev using fun i : Fin m ↦ hdec β hβ (F i) (G i) (hF i) (hFc i) (hG i) (hGc i)
    (fun t ht ↦ hF1 i t (by linarith)) (fun t ht ↦ hG1 i t (by linarith))
  set KK : ℝ := ∑ i, K i with hKKdef
  have hKK0 : 0 ≤ KK := Finset.sum_nonneg fun i _ ↦ hK i
  have hKle : ∀ i, K i ≤ KK := fun i ↦
    Finset.single_le_sum (f := K) (fun j _ ↦ hK j) (Finset.mem_univ i)
  set ε : ℝ := ε' / (2 * (KK ^ m + 1)) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  obtain ⟨z, hz⟩ := exists_threshold_abs_prod_sub_sum_pairwise_coprime_le_rpow (Fin m) hs hε
  filter_upwards [eventually_all.mpr hKev, eventually_dvd_W_of_prime_le z,
    eventually_gt_atTop (1 : ℝ), hB] with x hxK hxW hx1 hxB
  have hW0 : 0 < W x := primorial_pos _
  have hWR : (0 : ℝ) < (W x : ℝ) := by exact_mod_cast hW0
  have hφ : (0 : ℝ) < ((W x).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hW0
  have hlog : 0 < Real.log x := Real.log_pos hx1
  set Bx : ℝ := ((W x).totient : ℝ) / (W x : ℝ) * Real.log x with hBxdef
  have hBx : 0 < Bx := by rw [hBxdef]; positivity
  have hB1 : 1 ≤ B x := by exact_mod_cast ((Real.one_lt_rpow hx1 hβ).trans_le hxB).le
  set E : Finset ℕ := {e ∈ Icc 1 ((B x) ^ 2) | Nat.Coprime (W x) e} with hEdef
  have hEpos : ∀ e ∈ E, 0 < e := fun e he ↦ (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
  have hEprime : ∀ e ∈ E, ∀ P : ℕ, P.Prime → P ∣ e → z < P := by
    intro e he P hP hPe
    by_contra hcon
    exact hP.ne_one (Nat.dvd_one.mp
      ((Finset.mem_filter.mp he).2 ▸ Nat.dvd_gcd (hxW P hP (by omega)) hPe))
  have hmpos : ∀ a ∈ wBox x (B x) ×ˢ wBox x (B x), 0 < lcmPair a := fun a ha ↦
    lcmPair_pos (mem_wBox.mp (Finset.mem_product.mp ha).1).1.1
      (mem_wBox.mp (Finset.mem_product.mp ha).2).1.1
  have h1E : (1 : ℕ) ∈ E := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨le_rfl, Nat.one_le_pow _ _ hB1⟩, Nat.coprime_one_right _⟩
  have hAbound : ∀ (i : Fin m) (e : ℕ), 0 < e →
      |restrictedSum (wBox x (B x) ×ˢ wBox x (B x)) lcmPair
          (pairWeightTotient x (F i) (G i)) e| ≤ KK / Bx / (e : ℝ) ^ s := by
    intro i e he
    refine (hxK i (B x) e hxB he).trans ?_
    rw [div_div]
    exact div_le_div_of_nonneg_right (hKle i) (by positivity)
  have key := hz (wBox x (B x) ×ˢ wBox x (B x)) lcmPair
    (fun i ↦ pairWeightTotient x (F i) (G i)) E (KK / Bx)
    hmpos (fun a ha _ ↦ mem_divisorSet_of_dvd_lcmPair ha) h1E hEpos hEprime (by positivity) hAbound
  -- the normalisation absorbs `φ(W(x))` and leaves `B_x^m`
  have hnorm : (boxDivisorSum x (B x) F G - sievedDivisorSum x (B x) F G) / divisorSumNorm m x
      = Bx ^ m * ((∏ i, ∑ q ∈ wBox x (B x) ×ˢ wBox x (B x),
            pairWeightTotient x (F i) (G i) q) -
          ∑ a ∈ Fintype.piFinset fun _ : Fin m ↦ wBox x (B x) ×ˢ wBox x (B x),
            (if ∀ i i' : Fin m, i ≠ i' → Nat.Coprime (lcmPair (a i)) (lcmPair (a i'))
              then ∏ i, pairWeightTotient x (F i) (G i) (a i) else 0)) := by
    rw [boxDivisorSum_eq_prod, sievedDivisorSum_eq_sum_guard, divisorSumNorm, hBxdef,
      mul_pow, div_pow]
    field_simp
    ring
  rw [Real.dist_eq, sub_zero, hnorm, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < Bx ^ m)]
  refine (mul_le_mul_of_nonneg_left (Eq.trans_le ?_ key) (by positivity)).trans_lt ?_
  · congr 2
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    by_cases h : ∀ i i' : Fin m, i ≠ i' → Nat.Coprime (lcmPair (a i)) (lcmPair (a i'))
    · simp
    · simp [h]
  rw [Fintype.card_fin, div_pow, hεdef]
  field_simp
  nlinarith [pow_nonneg hKK0 m, hε'.le]

end Gap212.Sieve
