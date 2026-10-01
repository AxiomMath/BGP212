/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MoebiusTotientTransfer
public import Gap212.Sieve.OneCoordTotientSelberg
public import Gap212.Sieve.SmoothMoebiusInner
public meta import Gap212.Attr

/-!
# The one-variable totient Möbius bound for the Selberg diagonalisation

`Gap212.Sieve.SmoothMoebiusTotientInnerBound` is the single input of
`Gap212.Sieve.oneCoordTotientDecayAtLevelOfSupport_of_smoothMoebiusTotientInnerBound`, hence of
the totient sieving error. This file proves it (`Gap212.Sieve.smoothMoebiusTotientInnerBound`).

The argument follows the reciprocal kernel's (`Gap212.Sieve.smoothMoebiusInnerBound`): summation
by parts, then removal of the modulus by a smooth-number decomposition before the integration. The
totient kernel's local factor `1 - 1/((p-1)p^s)` vanishes at `s = 0` for `p = 2`, so the modulus
is removed in two steps: the weight `1/φ` is first traded for `1/id` at the same modulus through a
transfer kernel of bounded mass (`Gap212.Sieve.moebiusTotientBelow_eq_sum_smoothDivWeight`). The
denominator `(μ*φ)(r)` comes from the inequality `r/φ(r)^2 ≤ 1/(μ*φ)(r)`
(`Gap212.Sieve.self_div_totient_sq_le_inv_moebiusTotient`).

## Main results

* `Gap212.Sieve.moebiusTotient_nonneg`: `(μ*φ)(n) ≥ 0` for every `n`.
* `Gap212.Sieve.moebiusTotientBelow_eq_sum_smoothDivWeight`: the double smooth-number
  decomposition.
* `Gap212.Sieve.smoothMoebiusTotientInnerBound`: the one-variable bound.
* `Gap212.Sieve.oneCoordTotientDecayAtLevelOfSupport_three_quarters`: the two-variable estimate.
* `Gap212.Sieve.totientSievingError`: `Gap212.Sieve.TotientSievingError m`, at every `m`.
-/

@[expose] public section

open ArithmeticFunction Filter Gap212.Defs Gap212.GPY MeasureTheory Real Set
open scoped ArithmeticFunction.Moebius

namespace Gap212.Sieve

/-! ## The transfer kernel's mass, uniformly in the modulus -/

/-- **The Euler-product bound on the transfer kernel, with a constant independent of the
modulus.** -/
theorem exists_sum_transferAbsWeight_le_uniform :
    ∃ Γ : ℝ, 0 < Γ ∧ ∀ (e : ℕ) (u : Finset ℕ), ∑ n ∈ u, transferAbsWeight e n ≤ Γ := by
  refine ⟨Real.exp (∑' k : ℕ, transferTailBound k), Real.exp_pos _, fun e u ↦ ?_⟩
  exact PrimeGaps.MertensShared.finset_sum_le_exp_tsum_of_local _ (transferAbsWeight_one e)
    (transferAbsWeight_zero e) (transferAbsWeight_nonneg e)
    (fun {a b} h ↦ transferAbsWeight_mul_of_coprime e h)
    (fun {p} hp ↦ summable_transferAbsWeight_prime_pow e hp) transferTailBound
    transferTailBound_nonneg summable_transferTailBound
    (fun p hp ↦ tsum_transferAbsWeight_prime_pow_le e hp) u

/-- The transfer kernel is absolutely summable with the same constant: `√n ≥ 1` on `n ≥ 1`. -/
theorem sum_abs_transferWeight_le {Γ : ℝ}
    (hΓ : ∀ (e : ℕ) (u : Finset ℕ), ∑ n ∈ u, transferAbsWeight e n ≤ Γ) (Q N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, |coprimeDivWeight Q moebiusTotientDivisorSum n| ≤ Γ := by
  refine le_trans (Finset.sum_le_sum fun n hn ↦ ?_) (hΓ Q (Finset.Ioc 0 N))
  rw [transferAbsWeight]
  exact le_mul_of_one_le_left (abs_nonneg _)
    (Real.one_le_sqrt.mpr (by exact_mod_cast (Finset.mem_Ioc.mp hn).1))

/-! ## The Gram weight is nonnegative everywhere, not only on the squarefree integers -/

/-- **`(μ*φ)(p^k) = φ(p^k) - φ(p^{k-1})`**, by Möbius inversion rather than by expanding the
convolution: `∑_{i ≤ j}(μ*φ)(p^i) = φ(p^j)` for every `j`
(`Gap212.Sieve.sum_divisors_moebiusTotient`), and the prime-power case telescopes. -/
theorem moebiusTotient_prime_pow_succ {p : ℕ} (hp : p.Prime) (j : ℕ) :
    moebiusTotient (p ^ (j + 1))
      = (Nat.totient (p ^ (j + 1)) : ℝ) - (Nat.totient (p ^ j) : ℝ) := by
  have hsum (k : ℕ) :
      ∑ i ∈ Finset.range (k + 1), moebiusTotient (p ^ i) = (Nat.totient (p ^ k) : ℝ) := by
    rw [← sum_divisors_moebiusTotient (Nat.pow_pos hp.pos), Nat.sum_divisors_prime_pow hp]
  rw [← hsum, ← hsum, Finset.sum_range_succ _ (j + 1)]
  ring

/-- **`(μ*φ)(n) ≥ 0` for every `n`.** On a squarefree `n` this is
`Gap212.Sieve.moebiusTotient_nonneg_of_squarefree` (`∏_{p ∣ n}(p-2)` with every factor `≥ 0`); in
general it is the multiplicative factorisation together with
`Gap212.Sieve.moebiusTotient_prime_pow_succ` and `φ(p^{k-1}) ∣ φ(p^k)`.

`Gap212.Sieve.SmoothMoebiusTotientInnerBound` divides by `(μ*φ)(r)` at **every** `r ≥ 1`, and at a
modulus where the left side vanishes — `r` non-squarefree, or sharing a factor with `W(x)` — the
statement is exactly the assertion `0 ≤ C(W/φ(W))/((μ*φ)(r)\log x)`, which needs this. -/
theorem moebiusTotient_nonneg (n : ℕ) : 0 ≤ moebiusTotient n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [moebiusTotient]
  rw [← muPhiAF_apply, isMultiplicative_muPhiAF.multiplicative_factorization _ hn, Finsupp.prod]
  refine Finset.prod_nonneg fun p hp ↦ ?_
  rw [Nat.support_factorization] at hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hk := hpp.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨j, hj⟩ : ∃ j, n.factorization p = j + 1 := ⟨n.factorization p - 1, by omega⟩
  rw [hj, muPhiAF_apply, moebiusTotient_prime_pow_succ hpp, sub_nonneg, Nat.cast_le]
  exact Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pow_pos hpp.pos))
    (Nat.totient_dvd_of_dvd (pow_dvd_pow p j.le_succ))

/-! ## The arithmetic inequality that turns `r/φ(r)^2` into `1/(μ*φ)(r)` -/

/-- **`r·(μ*φ)(r) ≤ φ(r)^2` on a squarefree `r`**, factor by factor: `p(p-2) ≤ (p-1)^2`.

This is the totient kernel's counterpart of the reciprocal kernel's identity
`(1/r)(rW/φ(rW)) = (W/φ(W))/φ(r)`, and it is where the denominator `(μ*φ)(r)` of
`Gap212.Sieve.SmoothMoebiusTotientInnerBound` comes from: the smooth-number decomposition produces
the mass `Q/φ(Q)` against the weight `1/φ(r)`, i.e. `r/φ(r)^2`, and this inequality is exactly the
statement that `r/φ(r)^2 ≤ 1/(μ*φ)(r)`. The two sides differ by `∏_{p ∣ r}(1 - 1/(p-1)^2)`, which
is bounded but *not* bounded away from `0` uniformly, so the inequality is one-way — which is why
the kernel's own denominator is the smaller `(μ*φ)(r)` and not `φ(r)`. -/
theorem self_mul_moebiusTotient_le_totient_sq {r : ℕ} (hsf : Squarefree r) :
    (r : ℝ) * moebiusTotient r ≤ (Nat.totient r : ℝ) ^ 2 := by
  rw [moebiusTotient_of_squarefree hsf, totient_of_squarefree hsf,
    show (r : ℝ) = ∏ p ∈ r.primeFactors, (p : ℝ) from by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsf],
    ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  refine Finset.prod_le_prod (fun p hp ↦ ?_) fun p hp ↦ ?_
  · have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    nlinarith
  · nlinarith

/-- **`r/φ(r)^2 ≤ 1/(μ*φ)(r)` on an odd squarefree `r`.** -/
theorem self_div_totient_sq_le_inv_moebiusTotient {r : ℕ} (hsf : Squarefree r) (hodd : ¬ 2 ∣ r) :
    (r : ℝ) / (Nat.totient r : ℝ) ^ 2 ≤ 1 / moebiusTotient r := by
  have hφ1 := one_le_moebiusTotient_of_odd_squarefree hsf hodd
  have hφr : (0 : ℝ) < (Nat.totient r : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hsf.ne_zero)
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  linarith [self_mul_moebiusTotient_le_totient_sq hsf]

/-! ## The inner sum after `d = rm` -/

/-- **The inner totient Möbius sum in the shifted coprime form.** For `r ≥ 1` squarefree and
coprime to `W(x)`,

  `z_r = (μ(r)/φ(r))∑_{f ≤ B/r, (f,rW)=1}(μ(f)/φ(f))F(\log_xr + \log_xf)`.

The analogue of `Gap212.Sieve.innerMoebiusSum_eq_mul_sum_coprimeBelow` with `1/φ` for `1/id`:
writing `d = rf`, the terms with `(f,r) > 1` carry a non-squarefree `d` and vanish, and `φ` is
multiplicative on the coprime pair `(r,f)` — which is what makes the factor in front
`μ(r)/φ(r)`. -/
theorem innerMoebiusTotientSum_eq_mul_sum_coprimeBelow {x : ℝ} {F : ℝ → ℝ} {B r : ℕ} (hr1 : 1 ≤ r)
    (hrW : Nat.Coprime (W x) r) :
    innerMoebiusTotientSum x F B r
      = (μ r : ℝ) / (Nat.totient r : ℝ) * ∑ f ∈ coprimeBelow (r * W x) ((B : ℝ) / (r : ℝ)),
          (μ f : ℝ) / (Nat.totient f : ℝ) * F (Notation.logx x r + Notation.logx x f) := by
  classical
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  rw [innerMoebiusTotientSum, Finset.mul_sum]
  symm
  set S : Finset ℕ := coprimeBelow (r * W x) ((B : ℝ) / (r : ℝ))
  have hmem : ∀ f ∈ S, r * f ∈ {d ∈ wBox x B | r ∣ d} := by
    intro f hf
    obtain ⟨hf0, hfB, hfcop⟩ := mem_coprimeBelow.mp hf
    refine Finset.mem_filter.mpr ⟨mem_wBox.mpr ⟨⟨Nat.pos_of_ne_zero (by positivity), ?_⟩,
      hrW.mul_right (Nat.coprime_mul_iff_right.mp hfcop).2.symm⟩, Dvd.intro f rfl⟩
    exact_mod_cast (le_div_iff₀' hrR).mp hfB
  have hterm : ∀ f ∈ S, (μ (r * f) : ℝ) * F (Notation.logx x ((r * f : ℕ) : ℝ))
        / (Nat.totient (r * f) : ℝ)
      = (μ r : ℝ) / (Nat.totient r : ℝ)
        * ((μ f : ℝ) / (Nat.totient f : ℝ) * F (Notation.logx x r + Notation.logx x f)) := by
    intro f hf
    obtain ⟨hf0, -, hfcop⟩ := mem_coprimeBelow.mp hf
    have hfr := (Nat.coprime_mul_iff_right.mp hfcop).1.symm
    have hmu : (μ (r * f) : ℝ) = (μ r : ℝ) * (μ f : ℝ) := by
      exact_mod_cast isMultiplicative_moebius.map_mul_of_coprime hfr
    have hlog : Notation.logx x ((r * f : ℕ) : ℝ) = Notation.logx x r + Notation.logx x f := by
      rw [Notation.logx, Notation.logx, Notation.logx, Nat.cast_mul,
        Real.log_mul hrR.ne' (by positivity), add_div]
    rw [hmu, Nat.totient_mul hfr, hlog, Nat.cast_mul]
    field_simp
  have hzero : ∀ d ∈ {d ∈ wBox x B | r ∣ d}, d ∉ S.image (fun f ↦ r * f) →
      (μ d : ℝ) * F (Notation.logx x d) / (Nat.totient d : ℝ) = 0 := by
    intro d hd hdn
    obtain ⟨hdbox, m, rfl⟩ := Finset.mem_filter.mp hd
    obtain ⟨⟨hd1, hdB⟩, hdW⟩ := mem_wBox.mp hdbox
    have hmr : ¬ Nat.Coprime m r := by
      refine fun hcop ↦ hdn (Finset.mem_image.mpr ⟨m, mem_coprimeBelow.mpr ⟨?_, ?_, ?_⟩, rfl⟩)
      · rintro rfl
        omega
      · rw [le_div_iff₀' hrR]
        exact_mod_cast hdB
      · exact hcop.mul_right hdW.coprime_mul_left_right.symm
    obtain ⟨p, hp, hpm, hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp hmr
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      fun h ↦ hp.not_isUnit (h p (mul_dvd_mul hpr hpm))]
    simp
  refine Eq.trans (Finset.sum_congr rfl hterm).symm ?_
  rw [← Finset.sum_image (f := fun d ↦ (μ d : ℝ) * F (Notation.logx x d) / (Nat.totient d : ℝ))
    fun f₁ _ f₂ _ h ↦ Nat.eq_of_mul_eq_mul_left (by omega) h]
  exact Finset.sum_subset (Finset.image_subset_iff.mpr hmem) hzero


/-! ## The double smooth-number decomposition -/

/-- **The smooth-number decomposition of the totient Möbius partial sum.** For `Q ≠ 0`, `w ≥ 0` and
every `N₀ ≥ ⌊w⌋₊`,

  `T_Q(w) = ∑_{n ≤ N₀}∑_{b ≤ N₀} g_Q(n)·h_Q(b)·M(w/(nb))`,

`g_Q` the transfer kernel `Gap212.Sieve.coprimeDivWeight Q moebiusTotientDivisorSum`, `h_Q` the
smooth-number weight `Gap212.Sieve.smoothDivWeight`, and `M = S_1` the modulus-free reciprocal
Möbius sum. Two steps: `Gap212.Sieve.moebiusTotientBelow_eq_sum` trades the weight `1/φ` for
`1/id` at the *same* modulus, and
`Gap212.Sieve.moebiusReciprocalBelow_eq_sum_smoothDivWeight` then removes the modulus. Both index
sets are fixed independently of `w`, which is what lets them be exchanged with an integration in
`w`: the terms past `⌊w⌋₊` vanish because `M` vanishes below `1`.

This is the totient kernel's analogue of the reciprocal kernel's single decomposition, and it is a
*double* sum because the totient weight is not itself a convolution of `μ/id` with a weight
supported on the primes of `Q` — the local factor `1 - 1/((p-1)p^s)` vanishes at `s = 0` for
`p = 2`, so the modulus cannot be removed in one step. The transfer kernel is what absorbs that. -/
theorem moebiusTotientBelow_eq_sum_smoothDivWeight {Q : ℕ} (hQ : Q ≠ 0) {w : ℝ} (hw : 0 ≤ w)
    {N₀ : ℕ} (hN₀ : ⌊w⌋₊ ≤ N₀) :
    moebiusTotientBelow Q w
      = ∑ n ∈ Finset.Ioc 0 N₀, ∑ b ∈ Finset.Ioc 0 N₀,
          coprimeDivWeight Q moebiusTotientDivisorSum n * smoothDivWeight Q b
            * moebiusReciprocalBelow 1 (w / ((n * b : ℕ) : ℝ)) := by
  have hext : moebiusTotientBelow Q w
      = ∑ n ∈ Finset.Ioc 0 N₀,
          coprimeDivWeight Q moebiusTotientDivisorSum n * moebiusReciprocalBelow Q (w / n) := by
    rw [moebiusTotientBelow_eq_sum Q w]
    refine Finset.sum_subset (Finset.Ioc_subset_Ioc_right hN₀) fun n hn hnn ↦ ?_
    rw [Finset.mem_Ioc] at hn hnn
    have hwn : w < n := (Nat.floor_lt hw).mp (by omega)
    rw [moebiusReciprocalBelow_eq_zero_of_lt_one Q
      ((div_lt_one (by exact_mod_cast hn.1)).mpr hwn), mul_zero]
  rw [hext]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
  rw [moebiusReciprocalBelow_eq_sum_smoothDivWeight hQ
    ((Nat.floor_le_floor (div_le_self hw hn1R)).trans hN₀), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Nat.cast_mul, div_div]
  ring


/-! ## The one-variable estimate, at a free shift and modulus -/

/-- **The profile summed against the totient Möbius weight, bounded.** For `F` of class `C¹` with
compact support vanishing on `[β,∞)`, any modulus `Q ≠ 0`, any shift `c` and any truncation
`y ≥ x^{β-c}`,

  `|∑_{f ≤ y, (f,Q)=1}(μ(f)/φ(f))F(c + \log_xf)| ≤ \|F'\|_∞·Γ·(Q/φ(Q))·C₀/\log x`.

Three steps and no analysis beyond the modulus-free reciprocal Möbius rate.
`Gap212.Sieve.sum_coprimeBelow_mul_profile` integrates by parts, at the modulus `Q`; in the support
of `v ↦ F'(c+v)` one has `v < β - c`, hence `x^v ≤ y`, so the truncation is invisible — this is the
one place `y ≥ x^{β-c}` is spent. Then `Gap212.Sieve.moebiusTotientBelow_eq_sum_smoothDivWeight`
replaces `T_Q(x^v)` by the modulus-free `M(x^v/(nb))` against the two masses `Γ` and `Q/φ(Q)`, and
each `(n,b)` contributes `C₀/\log x` by
`Gap212.Sieve.integrableOn_and_integral_abs_moebiusReciprocalBelow_one` — with no loss, the shift
by `nb` only translating an integrand that vanishes below `1`.

Both masses must be uniform in `Q`, and both are: `Γ` by
`Gap212.Sieve.exists_sum_transferAbsWeight_le_uniform` (an Euler product over *all* primes, so
restricting to those coprime to `Q` only shrinks it) and `Q/φ(Q)` by
`Gap212.Sieve.sum_inv_smoothSet_le_self_div_totient`. The `Q/φ(Q)` here is the *reciprocal*
kernel's mass, not this kernel's: what the totient weight costs is the extra factor `Γ`, and what
turns `Q/φ(Q)` into the statement's `(μ*φ)(r)` is the arithmetic of
`Gap212.Sieve.self_mul_moebiusTotient_le_totient_sq`, applied afterwards. -/
theorem abs_sum_coprimeBelow_totient_profile_le {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) {β : ℝ} (hFβ : ∀ t : ℝ, β ≤ t → F t = 0) {x : ℝ} (hx1 : 1 < x)
    {C₀ : ℝ} (hC₀ : ∀ w : ℝ, 1 ≤ w → |moebiusReciprocalBelow 1 w| ≤ C₀ / (1 + Real.log w) ^ 2)
    {Γ : ℝ} (hΓ : ∀ (e : ℕ) (u : Finset ℕ), ∑ n ∈ u, transferAbsWeight e n ≤ Γ)
    {D : ℝ} (hD : ∀ t : ℝ, |deriv F t| ≤ D) (hD0 : 0 ≤ D) {Q : ℕ} (hQ : Q ≠ 0) {c y : ℝ}
    (hy : x ^ (β - c) ≤ y) :
    |∑ f ∈ coprimeBelow Q y, (μ f : ℝ) / (Nat.totient f : ℝ) * F (c + Notation.logx x f)|
      ≤ D * (Γ * ((Q : ℝ) / (Q.totient : ℝ)) * (C₀ / Real.log x)) := by
  classical
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hC₀0 : 0 ≤ C₀ := by simpa using (abs_nonneg _).trans (hC₀ 1 le_rfl)
  set N₀ : ℕ := ⌊y⌋₊
  -- the two masses
  have hmass : ∑ b ∈ Finset.Ioc 0 N₀, smoothDivWeight Q b ≤ (Q : ℝ) / (Q.totient : ℝ) := by
    convert sum_inv_smoothSet_le_self_div_totient hQ N₀ using 1
    rw [smoothSet, Finset.sum_filter]
    refine Finset.sum_congr ?_ fun b _ ↦ rfl
    ext b
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hmass0 : (0 : ℝ) ≤ ∑ b ∈ Finset.Ioc 0 N₀, smoothDivWeight Q b :=
    Finset.sum_nonneg fun b _ ↦ smoothDivWeight_nonneg Q b
  have hGamma := sum_abs_transferWeight_le hΓ Q N₀
  have hΓ0 : 0 ≤ Γ := (Finset.sum_nonneg fun n _ ↦ abs_nonneg _).trans hGamma
  -- each `(n,b)` term, integrated
  have hterm : ∀ n ∈ Finset.Ioc 0 N₀, ∀ b ∈ Finset.Ioc 0 N₀,
      IntegrableOn (fun v ↦ |coprimeDivWeight Q moebiusTotientDivisorSum n|
          * smoothDivWeight Q b * |moebiusReciprocalBelow 1 (x ^ v / ((n * b : ℕ) : ℝ))|)
          (Ioi (0 : ℝ)) volume
        ∧ ∫ v in Ioi (0 : ℝ), |coprimeDivWeight Q moebiusTotientDivisorSum n|
            * smoothDivWeight Q b * |moebiusReciprocalBelow 1 (x ^ v / ((n * b : ℕ) : ℝ))|
          ≤ |coprimeDivWeight Q moebiusTotientDivisorSum n| * smoothDivWeight Q b
            * (C₀ / Real.log x) := by
    intro n hn b hb
    obtain ⟨hi, hv⟩ := integrableOn_and_integral_abs_moebiusReciprocalBelow_one hx1 hC₀
      (Nat.mul_pos (Finset.mem_Ioc.mp hn).1 (Finset.mem_Ioc.mp hb).1)
    refine ⟨hi.const_mul _, ?_⟩
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hv
      (mul_nonneg (abs_nonneg _) (smoothDivWeight_nonneg Q b))
  have hintb : ∀ n ∈ Finset.Ioc 0 N₀, IntegrableOn
      (fun v ↦ ∑ b ∈ Finset.Ioc 0 N₀, |coprimeDivWeight Q moebiusTotientDivisorSum n|
        * smoothDivWeight Q b * |moebiusReciprocalBelow 1 (x ^ v / ((n * b : ℕ) : ℝ))|)
      (Ioi (0 : ℝ)) volume :=
    fun n hn ↦ integrable_finsetSum _ fun b hb ↦ (hterm n hn b hb).1
  -- the pointwise majorisation
  have hmajor : ∀ v ∈ Ioi (0 : ℝ),
      |deriv F (c + v) * moebiusTotientBelow Q (min (x ^ v) y)|
        ≤ D * ∑ n ∈ Finset.Ioc 0 N₀, ∑ b ∈ Finset.Ioc 0 N₀,
            |coprimeDivWeight Q moebiusTotientDivisorSum n| * smoothDivWeight Q b
              * |moebiusReciprocalBelow 1 (x ^ v / ((n * b : ℕ) : ℝ))| := by
    intro v hv
    rcases le_or_gt β (c + v) with hvβ | hvβ
    · rw [deriv_eq_zero_of_profile_vanishes hF hFβ hvβ, zero_mul, abs_zero]
      exact mul_nonneg hD0 (Finset.sum_nonneg fun n _ ↦ Finset.sum_nonneg fun b _ ↦
        mul_nonneg (mul_nonneg (abs_nonneg _) (smoothDivWeight_nonneg Q b)) (abs_nonneg _))
    have hxvy : x ^ v ≤ y := le_trans ((Real.rpow_le_rpow_left_iff hx1).mpr (by linarith)) hy
    rw [min_eq_left hxvy, moebiusTotientBelow_eq_sum_smoothDivWeight hQ (by positivity)
      (Nat.floor_le_floor hxvy), abs_mul]
    refine mul_le_mul (hD _) ?_ (abs_nonneg _) hD0
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ ↦ ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ ↦ le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (smoothDivWeight_nonneg Q b)]
  -- assemble
  rw [sum_coprimeBelow_mul_profile hF hFc hx1 Q c y (fun f ↦ (μ f : ℝ) / (Nat.totient f : ℝ)),
    abs_neg]
  refine abs_integral_le_integral_abs.trans <| (integral_mono_of_nonneg
    (.of_forall fun v ↦ abs_nonneg _) ((integrable_finsetSum _ hintb).const_mul D) ?_).trans ?_
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
    exact hmajor v hv
  rw [integral_const_mul, integral_finsetSum _ hintb]
  refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun n hn ↦
    (integral_finsetSum _ fun b hb ↦ (hterm n hn b hb).1).trans_le
      (Finset.sum_le_sum fun b hb ↦ (hterm n hn b hb).2)).trans ?_) hD0
  simp_rw [← Finset.sum_mul, ← Finset.sum_mul_sum]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hGamma hmass hmass0 hΓ0) (by positivity)


/-! ## The one-variable input, proved -/

/-- **`Gap212.Sieve.SmoothMoebiusTotientInnerBound` is a theorem.** For every `C¹` profile `F`
vanishing on `[β,∞)` there is a `C` — namely `C₀‖F'‖_∞Γ` — with

  `|∑_{d ≤ B, (d,W)=1, r ∣ d}μ(d)F(\log_xd)/φ(d)| ≤ C(W/φ(W))/((μ*φ)(r)\log x)`

for every large `x`, every `B ≥ x^β` and every `r ≥ 1`.

Four steps, and only the last is this kernel's own. The moduli that are not squarefree or not
coprime to `W(x)` give `z_r = 0`, and the right-hand side is nonnegative there by
`Gap212.Sieve.moebiusTotient_nonneg`. For the rest,
`Gap212.Sieve.innerMoebiusTotientSum_eq_mul_sum_coprimeBelow` writes `d = rf` and pulls out
`μ(r)/φ(r)` — `φ`, not `id` — and `Gap212.Sieve.abs_sum_coprimeBelow_totient_profile_le` bounds
what is left by `‖F'‖_∞Γ(Q/φ(Q))C₀/\log x` at `Q = rW(x)`.

**The last step is where the kernels differ.** The reciprocal kernel finishes
`(1/r)(Q/φ(Q)) = (W/φ(W))/φ(r)`. Here the weight in front is `1/φ(r)`, so what comes out is
`(1/φ(r))(Q/φ(Q)) = (W/φ(W))·r/φ(r)^2`, and `r/φ(r)^2` is turned into `1/(μ*φ)(r)` by the
*inequality* `Gap212.Sieve.self_div_totient_sq_le_inv_moebiusTotient` — one-way, and the only
inequality in the modulus dependence. Oddness of `r`, from coprimality to the even `W(x)`, is what
makes `(μ*φ)(r) ≥ 1` and hence that step legitimate; `(μ*φ)(2) = 0`.

**The constant carries the extra factor `Γ`** of
`Gap212.Sieve.exists_sum_transferAbsWeight_le_uniform`, which the reciprocal kernel does not have.
mass of the transfer kernel `g_Q = 1_{(·,Q)=1}·(ζ * (id·μ/φ))/id`, and it is what the totient
weight costs: the modulus cannot be removed from `T_Q` in one step, because the local factor
`1 - 1/((p-1)p^s)` of this kernel's Dirichlet series *vanishes* at `s = 0` for `p = 2`, so the
weight supported on the primes of `Q` that would do it has infinite mass. Going through the
reciprocal kernel at the same modulus and removing the modulus there is what avoids that. -/
theorem smoothMoebiusTotientInnerBound : SmoothMoebiusTotientInnerBound := by
  classical
  intro β hβ F hF hFc hFβ
  obtain ⟨C₀, hC₀⟩ := exists_moebiusReciprocalBelow_log_sq_decay (q := 1) le_rfl
  have hC₀0 : 0 ≤ C₀ := by simpa using (abs_nonneg _).trans (hC₀ 1 le_rfl)
  obtain ⟨Γ, hΓ0, hΓ⟩ := exists_sum_transferAbsWeight_le_uniform
  obtain ⟨D, hDb⟩ := hFc.deriv.exists_bound_of_continuous (hF.continuous_deriv le_rfl)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hDb 0)
  have hD (t : ℝ) : |deriv F t| ≤ D := by simpa using hDb t
  refine ⟨C₀ * D * Γ, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_dvd_W_of_prime_le 2] with x hx1 hxW
  intro B r hB hr1
  have hx0 : (0 : ℝ) < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hφWR : (0 : ℝ) < ((W x).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (primorial_pos _)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  have hRHS0 : 0 ≤ C₀ * D * Γ * ((W x : ℝ) / ((W x).totient : ℝ))
      / (moebiusTotient r * Real.log x) :=
    div_nonneg (by positivity) (mul_nonneg (moebiusTotient_nonneg r) hL.le)
  by_cases hrsf : Squarefree r; swap
  · rw [innerMoebiusTotientSum_eq_zero_of_not_squarefree hrsf, abs_zero]
    exact hRHS0
  by_cases hrW : Nat.Coprime (W x) r; swap
  · rw [innerMoebiusTotientSum_eq_zero_of_not_coprime hrW, abs_zero]
    exact hRHS0
  have hrodd : ¬ 2 ∣ r := not_two_dvd_of_coprime (hxW 2 Nat.prime_two le_rfl) hrW
  have hφrR : (0 : ℝ) < (r.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hr1
  have hμφ : moebiusTotient r ≠ 0 :=
    (one_pos.trans_le (one_le_moebiusTotient_of_odd_squarefree hrsf hrodd)).ne'
  have hQ0 : r * W x ≠ 0 := Nat.mul_ne_zero (by omega) (primorial_pos _).ne'
  have hy : x ^ (β - Notation.logx x r) ≤ (B : ℝ) / (r : ℝ) := by
    rw [Real.rpow_sub hx0, logx_eq_logb, Real.rpow_logb hx0 hx1.ne' hrR]
    gcongr
  have habsmu : |(μ r : ℝ) / (Nat.totient r : ℝ)| ≤ 1 / (Nat.totient r : ℝ) := by
    rw [abs_div, abs_of_pos hφrR]
    gcongr
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [innerMoebiusTotientSum_eq_mul_sum_coprimeBelow hr1 hrW, abs_mul]
  refine (mul_le_mul habsmu (abs_sum_coprimeBelow_totient_profile_le hF hFc hFβ hx1 hC₀ hΓ hD hD0
    hQ0 hy) (abs_nonneg _) (by positivity)).trans ?_
  rw [Nat.totient_mul hrW.symm]
  push_cast
  calc _ = D * Γ * C₀ / Real.log x * ((W x : ℝ) / ((W x).totient : ℝ))
        * ((r : ℝ) / (Nat.totient r : ℝ) ^ 2) := by field_simp
    _ ≤ D * Γ * C₀ / Real.log x * ((W x : ℝ) / ((W x).totient : ℝ)) * (1 / moebiusTotient r) :=
      mul_le_mul_of_nonneg_left (self_div_totient_sq_le_inv_moebiusTotient hrsf hrodd)
        (by positivity)
    _ = _ := by field_simp

/-! ## The chain to the sieving error -/

/-- **`Gap212.Sieve.OneCoordTotientDecayAtLevelOfSupport (3/4)` holds**:
`Gap212.Sieve.oneCoordTotientDecayAtLevelOfSupport_of_smoothMoebiusTotientInnerBound` applied to
`Gap212.Sieve.smoothMoebiusTotientInnerBound`. -/
theorem oneCoordTotientDecayAtLevelOfSupport_three_quarters :
    OneCoordTotientDecayAtLevelOfSupport (3 / 4) :=
  oneCoordTotientDecayAtLevelOfSupport_of_smoothMoebiusTotientInnerBound
    smoothMoebiusTotientInnerBound

/-- **The totient sieving error at every `β ≥ 1`.** For reduced-retreated profile families and a
truncation `B(x) ≥ x^β` with `β ≥ 1`,

  `(Σ^{sep}_x(𝓑) - Σ^{sep}_x(𝓢))/divisorSumNorm → 0`,

which is the content of `Gap212.Sieve.TotientSievingError m`. -/
theorem tendsto_boxDivisorSum_sub_sievedDivisorSum (p : SupportParams) {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀)
    {m : ℕ} {j j' : Fin p.n} {i₀ : Fin (m + 1)} (F G : Fin m → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ 1 (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    (hsupp : IsReducedRetreat p m j j' ε₀ i₀ F G)
    {β : ℝ} (hβ1 : 1 ≤ β) (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦
        (boxDivisorSum x (B x) F G - sievedDivisorSum x (B x) F G) / divisorSumNorm m x)
      atTop (nhds 0) :=
  tendsto_boxDivisorSum_sub_sievedDivisorSum_of_smoothInnerBound smoothMoebiusTotientInnerBound
    p hε₀ F G hF hFc hG hGc hsupp hβ1 B hB

/-- **`Gap212.Sieve.TotientSievingError m` holds, at every `m`.**
`Gap212.Sieve.tendsto_boxDivisorSum_sub_sievedDivisorSum` is exactly its conclusion, at every
`β ≥ 1`. The restriction to `β ≥ 1` is because the two-variable estimate is fed the profiles'
support clause, which the reduced retreat supplies only from `1` on; at `β < 1` the truncation cuts
a retreated profile's support and the one-coordinate sums are `≍1/W(x)` rather than `≍1/B_x`
(`Gap212.Sieve.not_oneCoordTotientDecayAtLevel`). -/
@[gap212 "lem_divisor_sum_sieving_error"]
theorem totientSievingError (m : ℕ) : TotientSievingError m :=
  fun p _ε₀ hε₀ _ _j _j' _i₀ F G hF hFc hG hGc hsupp _β hβ1 B hB ↦
    tendsto_boxDivisorSum_sub_sievedDivisorSum p hε₀.le F G hF hFc hG hGc hsupp hβ1 B hB

end Gap212.Sieve
