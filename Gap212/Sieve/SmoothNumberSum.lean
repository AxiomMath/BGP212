/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MoebiusDecay
public import Gap212.Sieve.MoebiusTotientAsymptotic

/-!
# The smooth-number decomposition of the coprimality-restricted Möbius weight

`Gap212.Sieve.moebiusPartialSumDecay` is a *per-modulus* statement: the constant in
`|S_q(w)| ≤ C_q(1 + \log w)^{-1-ε}` depends on `q`, and it must, because the uniform form is
refuted (`Gap212.Sieve.not_uniformMoebiusPartialSumDecay`). A modulus-uniform bound therefore
cannot be had at the level of the partial sum, and Abel summation against the `q/φ(q)`-weighted
partial-sum form loses a `\log\log x`. What *is* uniform is obtained by moving the modulus out of
the Möbius sum entirely, before any summation by parts:

  `μ·1_{(·,Q)=1}/id = (μ/id) * h_Q`,  `h_Q(b) = 1/b` if every prime of `b` divides `Q`, else `0`,

an identity of arithmetic functions. Its summatory form is

  `S_Q(w) = ∑_{b ≤ N₀, b | Q^∞} (1/b)·M(w/b)`,  `M = S_1`,

for every `N₀ ≥ w` — the modulus-free `M` against a weight whose total mass is
`∑_{b | Q^∞} 1/b = Q/φ(Q)` exactly. Both halves are proved here: the mass bound
(`Gap212.Sieve.sum_inv_smoothSet_le_self_div_totient`) and the identity
(`Gap212.Sieve.moebiusReciprocalBelow_eq_sum_smoothDivWeight`).

The two are what make the smoothed bound uniform in the modulus: the `Q/φ(Q)` appears as a *mass*
multiplying one modulus-free estimate, not as a factor inside a bound whose `w`-dependence then has
to survive an Abel integration.

## Main definitions

* `Gap212.Sieve.smoothSet`: the positive integers `b ≤ N` all of whose prime factors lie in a
  finset `P`.
* `Gap212.Sieve.smoothDivWeight`: the arithmetic function `b ↦ 1/b` supported on the integers all
  of whose prime factors divide `Q`.

## Main results

* `Gap212.Sieve.sum_inv_smoothSet_le_self_div_totient`: `∑_{b ≤ N, b | Q^∞} 1/b ≤ Q/φ(Q)`.
* `Gap212.Sieve.coprimeDivWeight_one_mul_smoothDivWeight`: the convolution identity.
* `Gap212.Sieve.moebiusReciprocalBelow_eq_sum_smoothDivWeight`: its summatory form.
-/

@[expose] public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction ArithmeticFunction.Moebius

namespace Gap212.Sieve

/-! ## The mass of the smooth numbers -/

/-- The positive integers `b ≤ N` all of whose prime factors lie in `P`. -/
def smoothSet (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun b => b.primeFactors ⊆ P

/-- `b ∈ smoothSet P N` iff `1 ≤ b ≤ N` and every prime factor of `b` lies in `P`. -/
theorem mem_smoothSet {P : Finset ℕ} {N b : ℕ} :
    b ∈ smoothSet P N ↔ (1 ≤ b ∧ b ≤ N) ∧ b.primeFactors ⊆ P := by
  rw [smoothSet, Finset.mem_filter, Finset.mem_Icc]

/-- **The mass of the `P`-smooth numbers is at most the Euler product.** For a finset `P` of
primes, `∑_{b ≤ N, p ∣ b → p ∈ P} 1/b ≤ ∏_{p ∈ P}(1 - 1/p)^{-1}`, with no dependence on `N`.

The map `b ↦ (v_p(b), b/p^{v_p(b)})` is injective from the `insert p P`-smooth numbers below `N`
into the pairs (exponent, `P`-smooth number below `N`), and `1/b` is the product of the two
reciprocals; the geometric series in `p` and the induction hypothesis then separate. -/
theorem sum_inv_smoothSet_le (N : ℕ) : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
    ∑ b ∈ smoothSet P N, ((b : ℝ))⁻¹ ≤ ∏ p ∈ P, (1 - ((p : ℝ))⁻¹)⁻¹ := by
  intro P
  induction P using Finset.induction_on with
  | empty =>
    intro _
    refine (Finset.sum_le_sum_of_subset_of_nonneg (t := {1}) (fun b hb ↦ ?_)
      fun _ _ _ ↦ by positivity).trans (by simp)
    obtain ⟨⟨hb1, -⟩, hbp⟩ := mem_smoothSet.mp hb
    rcases Nat.primeFactors_eq_empty.mp (Finset.subset_empty.mp hbp) with rfl | rfl <;> simp_all
  | @insert p P hp ih =>
    intro hP
    have hpp : p.Prime := hP p (Finset.mem_insert_self p P)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq ↦ hP q (Finset.mem_insert_of_mem hq)
    have hinv : ∀ q : ℕ, q.Prime → 0 ≤ (1 - ((q : ℝ))⁻¹)⁻¹ := fun q hq ↦
      inv_nonneg.mpr (sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast hq.one_lt.le)))
    classical
    set Φ : ℕ → ℕ × ℕ := fun b ↦ (b.factorization p, ordCompl[p] b) with hΦ
    have hval : ∀ b ∈ smoothSet (insert p P) N,
        ((b : ℝ))⁻¹ = ((p : ℝ))⁻¹ ^ (Φ b).1 * (((Φ b).2 : ℝ))⁻¹ := fun b _ ↦ by
      simp only [hΦ]
      rw [inv_pow, ← mul_inv, ← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
    have hinj : ∀ b₁ ∈ smoothSet (insert p P) N, ∀ b₂ ∈ smoothSet (insert p P) N,
        Φ b₁ = Φ b₂ → b₁ = b₂ := by
      intro b₁ _ b₂ _ h
      simp only [hΦ, Prod.mk.injEq] at h
      rw [← Nat.ordProj_mul_ordCompl_eq_self b₁ p, h.2, h.1, Nat.ordProj_mul_ordCompl_eq_self]
    have hmaps : ∀ b ∈ smoothSet (insert p P) N,
        Φ b ∈ Finset.range (N + 1) ×ˢ smoothSet P N := by
      intro b hb
      obtain ⟨⟨hb1, hbN⟩, hbp⟩ := mem_smoothSet.mp hb
      have hb0 : b ≠ 0 := by omega
      simp only [hΦ]
      refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, mem_smoothSet.mpr
        ⟨⟨Nat.ordCompl_pos p hb0, (Nat.ordCompl_le b p).trans hbN⟩, fun q hq ↦ ?_⟩⟩
      · have := Nat.ordProj_le p hb0
        have := Nat.lt_pow_self (n := b.factorization p) hpp.one_lt
        omega
      · refine (Finset.mem_insert.mp
          (hbp (Nat.primeFactors_mono (Nat.ordCompl_dvd b p) hb0 hq))).resolve_left ?_
        rintro rfl
        exact Nat.not_dvd_ordCompl hpp hb0 (Nat.dvd_of_mem_primeFactors hq)
    have hgeom : ∑ j ∈ Finset.range (N + 1), ((p : ℝ))⁻¹ ^ j ≤ (1 - ((p : ℝ))⁻¹)⁻¹ := by
      have hr0 : (0 : ℝ) ≤ ((p : ℝ))⁻¹ := by positivity
      have hr1 : ((p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hpp.one_lt)
      rw [← tsum_geometric_of_lt_one hr0 hr1]
      exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ fun i _ ↦ pow_nonneg hr0 i
    calc ∑ b ∈ smoothSet (insert p P) N, ((b : ℝ))⁻¹
        = ∑ b ∈ smoothSet (insert p P) N, ((p : ℝ))⁻¹ ^ (Φ b).1 * (((Φ b).2 : ℝ))⁻¹ :=
          Finset.sum_congr rfl hval
      _ = ∑ y ∈ (smoothSet (insert p P) N).image Φ, ((p : ℝ))⁻¹ ^ y.1 * ((y.2 : ℝ))⁻¹ :=
          (Finset.sum_image (f := fun y : ℕ × ℕ ↦ ((p : ℝ))⁻¹ ^ y.1 * ((y.2 : ℝ))⁻¹) hinj).symm
      _ ≤ ∑ y ∈ Finset.range (N + 1) ×ˢ smoothSet P N, ((p : ℝ))⁻¹ ^ y.1 * ((y.2 : ℝ))⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
            fun y _ _ ↦ by positivity
      _ = (∑ j ∈ Finset.range (N + 1), ((p : ℝ))⁻¹ ^ j)
            * ∑ c ∈ smoothSet P N, ((c : ℝ))⁻¹ := by
          rw [Finset.sum_product, Finset.sum_mul_sum]
      _ ≤ (1 - ((p : ℝ))⁻¹)⁻¹ * ∏ q ∈ P, (1 - ((q : ℝ))⁻¹)⁻¹ :=
          mul_le_mul hgeom (ih hP') (Finset.sum_nonneg fun c _ ↦ by positivity) (hinv p hpp)
      _ = ∏ q ∈ insert p P, (1 - ((q : ℝ))⁻¹)⁻¹ := by rw [Finset.prod_insert hp]

/-- **The mass of the integers built from the primes of `Q` is `Q/φ(Q)`.** The Euler product of
`Gap212.Sieve.sum_inv_smoothSet_le` over the prime factors of `Q` is exactly `Q/φ(Q)`, by
`Gap212.Sieve.totient_div_eq_prod_one_sub_inv`. This is the total mass the smooth-number
decomposition puts on the modulus-free Möbius sum, and it is the whole of the modulus dependence of
the smoothed bound. -/
theorem sum_inv_smoothSet_le_self_div_totient {Q : ℕ} (hQ : Q ≠ 0) (N : ℕ) :
    ∑ b ∈ smoothSet Q.primeFactors N, ((b : ℝ))⁻¹ ≤ (Q : ℝ) / (Q.totient : ℝ) := by
  refine le_trans (sum_inv_smoothSet_le N Q.primeFactors
    fun p hp ↦ Nat.prime_of_mem_primeFactors hp) ?_
  simp [← one_div, ← totient_div_eq_prod_one_sub_inv hQ, one_div_div]

/-! ## The convolution identity -/

/-- The arithmetic function `b ↦ 1/b`, supported on the integers all of whose prime factors divide
`Q`. -/
noncomputable def smoothDivWeight (Q : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun b ↦ if b.primeFactors ⊆ Q.primeFactors then ((b : ℝ))⁻¹ else 0, by simp⟩

/-- `smoothDivWeight Q b` is `b⁻¹` if `b.primeFactors ⊆ Q.primeFactors`, and `0` otherwise. -/
@[simp] theorem smoothDivWeight_apply (Q b : ℕ) :
    smoothDivWeight Q b = if b.primeFactors ⊆ Q.primeFactors then ((b : ℝ))⁻¹ else 0 := rfl

/-- The weight `smoothDivWeight Q b` is non-negative. -/
theorem smoothDivWeight_nonneg (Q b : ℕ) : 0 ≤ smoothDivWeight Q b := by
  rw [smoothDivWeight_apply]
  positivity

/-- The smooth-number weight is multiplicative: prime factors of a product of coprimes are the
union of the two prime-factor sets. -/
theorem isMultiplicative_smoothDivWeight (Q : ℕ) : (smoothDivWeight Q).IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨by simp, fun {m n} hm hn _ ↦ ?_⟩
  simp only [smoothDivWeight_apply, Nat.primeFactors_mul hm hn, Finset.union_subset_iff]
  split_ifs <;> simp_all [mul_comm]

/-- `n ↦ μ(n)/n` restricted to the integers coprime to `q` is multiplicative. -/
theorem isMultiplicative_coprimeDivWeight_moebius (q : ℕ) :
    (coprimeDivWeight q (μ : ArithmeticFunction ℝ)).IsMultiplicative := by
  refine ⟨by simp, fun {m n} hmn ↦ ?_⟩
  simp only [coprimeDivWeight_apply, intCoe_apply, Nat.coprime_mul_iff_left,
    isMultiplicative_moebius.map_mul_of_coprime hmn]
  split_ifs <;> simp_all [mul_div_mul_comm]

/-- **The smooth-number decomposition of the coprimality-restricted Möbius weight.**

  `(μ/id) * h_Q = μ·1_{(·,Q)=1}/id`,

with `h_Q` the smooth-number weight `Gap212.Sieve.smoothDivWeight`. Both sides are multiplicative,
so it suffices to check prime powers: at `p ∤ Q` only `b = 1` contributes and the identity is
trivial, while at `p ∣ Q` the whole divisor sum is `p^{-k}∑_{i≤k}μ(p^i) = 0`, matching the
vanishing of the restricted weight. This is the step that moves the modulus out of the Möbius sum,
and the reason the smoothed bound can be uniform in the modulus when the partial-sum bound cannot
be. -/
theorem coprimeDivWeight_one_mul_smoothDivWeight {Q : ℕ} (hQ : Q ≠ 0) :
    coprimeDivWeight 1 (μ : ArithmeticFunction ℝ) * smoothDivWeight Q
      = coprimeDivWeight Q (μ : ArithmeticFunction ℝ) := by
  have hmul := (isMultiplicative_coprimeDivWeight_moebius 1).mul
    (isMultiplicative_smoothDivWeight Q)
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ hmul _
    (isMultiplicative_coprimeDivWeight_moebius Q)]
  intro p k hp
  have hconv : (coprimeDivWeight 1 (μ : ArithmeticFunction ℝ) * smoothDivWeight Q) (p ^ k)
      = ∑ i ∈ Finset.range (k + 1),
          coprimeDivWeight 1 (μ : ArithmeticFunction ℝ) (p ^ i)
            * smoothDivWeight Q (p ^ (k - i)) := by
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (f := fun a b ↦ coprimeDivWeight 1 (μ : ArithmeticFunction ℝ) a * smoothDivWeight Q b),
      Nat.sum_divisors_prime_pow hp]
    exact Finset.sum_congr rfl fun i hi ↦ by
      rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp.pos]
  rw [hconv]
  by_cases hpQ : p ∣ Q
  · -- every power of `p` is `Q`-smooth, and `∑_{i ≤ k} μ(p^i) = 0` for `k ≥ 1`
    have hterm : ∀ i ∈ Finset.range (k + 1),
        coprimeDivWeight 1 (μ : ArithmeticFunction ℝ) (p ^ i) * smoothDivWeight Q (p ^ (k - i))
          = ((μ (p ^ i) : ℤ) : ℝ) * ((p : ℝ) ^ k)⁻¹ := by
      intro i hi
      have hsub : (p ^ (k - i)).primeFactors ⊆ Q.primeFactors := by
        rcases eq_or_ne (k - i) 0 with h | h <;> simp [h, Nat.primeFactors_pow, hp, hpQ, hQ]
      rw [coprimeDivWeight_apply, if_pos (Nat.coprime_one_right _), smoothDivWeight_apply,
        if_pos hsub, intCoe_apply, div_eq_mul_inv, mul_assoc, Nat.cast_pow, Nat.cast_pow,
        ← mul_inv, ← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hk
    rw [coprimeDivWeight_apply, if_neg ((Nat.coprime_pow_left_iff hk p Q).not.mpr
      (hp.dvd_iff_not_coprime.mp hpQ))]
    simp [Finset.sum_range_succ', moebius_apply_prime_pow hp]
  · -- only `b = 1` is `Q`-smooth, and `p^k` is coprime to `Q`
    rw [Finset.sum_eq_single_of_mem k (Finset.self_mem_range_succ k) fun i hi hik ↦ by
      simp [Nat.primeFactors_prime_pow (show k - i ≠ 0 by grind) hp, hp, hpQ]]
    simp [Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpQ)]

/-- **The summatory form of the decomposition.** For every `N₀ ≥ w`,

  `S_Q(w) = ∑_{b ≤ N₀} h_Q(b)·M(w/b)`,  `M = S_1` the modulus-free Möbius partial sum.

The Dirichlet hyperbola identity gives the sum over `b ≤ w`; the terms with `w < b ≤ N₀` vanish
because `M` vanishes below `1`. Fixing the index set independently of `w` is what lets the sum be
exchanged with an integration in `w` later. -/
theorem moebiusReciprocalBelow_eq_sum_smoothDivWeight {Q : ℕ} (hQ : Q ≠ 0) {w : ℝ} {N₀ : ℕ}
    (hN₀ : ⌊w⌋₊ ≤ N₀) :
    moebiusReciprocalBelow Q w
      = ∑ b ∈ Finset.Ioc 0 N₀, smoothDivWeight Q b * moebiusReciprocalBelow 1 (w / b) := by
  calc moebiusReciprocalBelow Q w
      = summatory (coprimeDivWeight Q (μ : ArithmeticFunction ℝ)) w :=
        (summatory_coprimeMoebius Q w).symm
    _ = ∑ n ∈ Finset.Ioc 0 ⌊w⌋₊,
          (smoothDivWeight Q * coprimeDivWeight 1 (μ : ArithmeticFunction ℝ)) n := by
        rw [summatory, mul_comm, coprimeDivWeight_one_mul_smoothDivWeight hQ]
    _ = ∑ b ∈ Finset.Ioc 0 ⌊w⌋₊, smoothDivWeight Q b
          * summatory (coprimeDivWeight 1 (μ : ArithmeticFunction ℝ)) (w / b) :=
        summatory_hyperbola _ _ w
    _ = ∑ b ∈ Finset.Ioc 0 ⌊w⌋₊, smoothDivWeight Q b * moebiusReciprocalBelow 1 (w / b) :=
        Finset.sum_congr rfl fun b _ ↦ by rw [summatory_coprimeMoebius]
    _ = ∑ b ∈ Finset.Ioc 0 N₀, smoothDivWeight Q b * moebiusReciprocalBelow 1 (w / b) := by
        refine Finset.sum_subset (Finset.Ioc_subset_Ioc_right hN₀) fun b hb hbn ↦ ?_
        rw [Finset.mem_Ioc] at hb hbn
        have hb0 : (0 : ℝ) < b := by exact_mod_cast hb.1
        have hwb : w / b < 1 :=
          (div_lt_one hb0).mpr (lt_of_not_ge fun h ↦ hbn ⟨hb.1, Nat.le_floor h⟩)
        simp [moebiusReciprocalBelow, coprimeBelow, Nat.floor_eq_zero.mpr hwb]

end Gap212.Sieve
