/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.SievingErrorReduction

/-!
# The one-coordinate estimate at level `s` is false

`Gap212.Sieve.OneCoordLcmDecayAtLevel` is refuted here, at every exponent `s`
(`Gap212.Sieve.not_oneCoordLcmDecayAtLevel`). The witness is the top block `(B/2, B]` of moduli in
the Selberg diagonalisation of the one-coordinate pair sum
(`Gap212.Sieve.sum_pairs_div_lcm_eq_sum_totient_mul_sq`), which is a sum of squares.

The statement `Gap212.Sieve.OneCoordLcmDecayAtLevelOfSupport` adds the hypothesis that the profiles
vanish from `β` on, and `Gap212.Sieve.tendsto_boxPairSum_sub_sievedPairSum_of_support` derives the
conclusion of `Gap212.Sieve.SelbergSievingError` from it.

## Main results

* `Gap212.Sieve.sum_pairs_div_lcm_eq_sum_totient_mul_sq`: the Selberg diagonalisation.
* `Gap212.Sieve.exists_dense_squarefree_block`: a dense family of squarefree moduli in the top
  block.
* `Gap212.Sieve.not_oneCoordLcmDecayAtLevel`: the refutation.
* `Gap212.Sieve.tendsto_boxPairSum_sub_sievedPairSum_of_support`: the sieving error at `β ≥ 1`
  from `Gap212.Sieve.OneCoordLcmDecayAtLevelOfSupport`.
-/

@[expose] public section

namespace Gap212.Sieve

open Asymptotics Filter Finset Gap212.Defs Gap212.GPY
open scoped ArithmeticFunction.Moebius

/-! ## Selberg diagonalisation of the one-coordinate pair sum -/

/-- **The divisors of a gcd, read inside a truncated range.** -/
theorem filter_Icc_dvd_dvd_eq_divisors_gcd {B d d' : ℕ} (hd1 : 1 ≤ d) (hdB : d ≤ B) :
    {r ∈ Icc 1 B | r ∣ d ∧ r ∣ d'} = (Nat.gcd d d').divisors := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨h, (Nat.gcd_pos_of_pos_left _ hd1).ne'⟩
  · rintro ⟨⟨hrd, hrd'⟩, -⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hrd hd1, (Nat.le_of_dvd hd1 hrd).trans hdB⟩, hrd, hrd'⟩

/-- **`Nat.sum_totient` read inside a truncated range.** -/
theorem sum_filter_Icc_totient_eq_gcd {B d d' : ℕ} (hd1 : 1 ≤ d) (hdB : d ≤ B) :
    ∑ r ∈ Icc 1 B with r ∣ d ∧ r ∣ d', (r.totient : ℝ) = (Nat.gcd d d' : ℝ) := by
  rw [filter_Icc_dvd_dvd_eq_divisors_gcd hd1 hdB]
  exact_mod_cast Nat.sum_totient _

/-- **The Selberg diagonalisation of a one-coordinate pair sum.** For any weight `l` on a finset
`D ⊆ [1,B]`,

  `∑_{d,d' ∈ D} l(d)l(d')/[d,d'] = ∑_{r ≤ B} φ(r)·(∑_{d ∈ D, r ∣ d} l(d)/d)^2`.

This is `1/[d,d'] = \gcd(d,d')/(dd')` together with `∑_{r ∣ n}φ(r) = n` (`Nat.sum_totient`) and one
exchange of summation — an exact identity, no estimate. **Its content is that the right side is a
sum of squares**: the one-coordinate pair sum at `e = 1` is *nonnegative*, and bounded below by the
contribution of any single set of moduli `r`. Every bound on the sum that proceeds by cancellation
between the diagonal and the off-diagonal has to survive this. -/
theorem sum_pairs_div_lcm_eq_sum_totient_mul_sq (B : ℕ) (D : Finset ℕ)
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ B) (l : ℕ → ℝ) :
    ∑ d ∈ D, ∑ d' ∈ D, l d * l d' / (Nat.lcm d d' : ℝ)
      = ∑ r ∈ Icc 1 B, (r.totient : ℝ) * (∑ d ∈ D with r ∣ d, l d / (d : ℝ)) ^ 2 := by
  simp_rw [sq, Finset.sum_filter, Finset.sum_mul_sum, Finset.mul_sum, ite_zero_mul_ite_zero,
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
  linear_combination l d * l d' * hg

/-! ## The top block: a modulus above `B/2` sees a single multiple -/

/-- **Above `B/2` a modulus has exactly one multiple in the range.** -/
theorem filter_dvd_eq_singleton {B r : ℕ} {D : Finset ℕ} (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ B)
    (hB : B < 2 * r) (hrD : r ∈ D) : {d ∈ D | r ∣ d} = {r} := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_singleton]
  refine ⟨?_, by rintro rfl; exact ⟨hrD, dvd_rfl⟩⟩
  rintro ⟨hdD, m, rfl⟩
  obtain ⟨h1, h2⟩ := hD _ hdD
  rcases m with _ | _ | n
  · simp at h1
  · simp
  · nlinarith

/-- **The one-coordinate pair sum at `e = 1` dominates any block of top moduli.** The Selberg
diagonalisation `Gap212.Sieve.sum_pairs_div_lcm_eq_sum_totient_mul_sq` is a sum of squares, so
dropping every modulus outside a chosen family is a legitimate lower bound — and above `B/2` the
inner sum is the single term `l(r)/r` (`Gap212.Sieve.filter_dvd_eq_singleton`). -/
theorem sum_block_le_sum_pairs_div_lcm (B : ℕ) (D : Finset ℕ) (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ B)
    (l : ℕ → ℝ) (Fam : Finset ℕ) (hsub : Fam ⊆ Icc 1 B)
    (hblk : ∀ r ∈ Fam, B < 2 * r ∧ r ∈ D) :
    ∑ r ∈ Fam, (r.totient : ℝ) * (l r / (r : ℝ)) ^ 2
      ≤ ∑ d ∈ D, ∑ d' ∈ D, l d * l d' / (Nat.lcm d d' : ℝ) := by
  rw [sum_pairs_div_lcm_eq_sum_totient_mul_sq B D hD l]
  refine (Finset.sum_congr rfl fun r hr ↦ ?_).trans_le
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ ↦ by positivity)
  rw [filter_dvd_eq_singleton hD (hblk r hr).1 (hblk r hr).2, Finset.sum_singleton]

/-! ## Counting: elementary ingredients -/

/-- `∑_{w < n ≤ T} 1/n² ≤ 1/w`. -/
theorem sum_Icc_one_div_sq_le {w : ℕ} (hw : 1 ≤ w) (T : ℕ) :
    ∑ n ∈ Icc (w + 1) T, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (w : ℝ) := by
  rcases le_or_gt w T with h | h
  · have := sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : w ≠ 0) h
    rw [← Finset.Icc_add_one_left_eq_Ioc] at this
    simp only [one_div]
    linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) T)]
  · simp [Finset.Icc_eq_empty (by omega : ¬w + 1 ≤ T)]

/-- **A set of integers in `[1,B]` lying in a single class mod `K` has at most `B/K + 1`
elements.** -/
theorem card_le_of_modEq {B K : ℕ} {S : Finset ℕ}
    (hS : ∀ a ∈ S, 1 ≤ a ∧ a ≤ B) (hmod : ∀ a ∈ S, ∀ b ∈ S, Nat.ModEq K a b) :
    S.card ≤ B / K + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  set a₀ := S.min' hne
  have ha₀S : a₀ ∈ S := S.min'_mem hne
  refine (Finset.card_le_card_of_injOn (t := Finset.range (B / K + 1)) (fun r ↦ (r - a₀) / K)
    (fun r hr ↦ ?_) fun a ha b hb hab ↦ ?_).trans_eq (Finset.card_range _)
  · have := (hS r hr).2
    have := (hS a₀ ha₀S).1
    simpa [Nat.lt_succ_iff] using Nat.div_le_div_right (c := K) (by omega : r - a₀ ≤ B)
  · have hma := S.min'_le a ha
    have hmb := S.min'_le b hb
    have key : a - a₀ = b - a₀ := by
      rw [← Nat.div_mul_cancel ((Nat.modEq_iff_dvd' hma).mp (hmod a₀ ha₀S a ha)),
        ← Nat.div_mul_cancel ((Nat.modEq_iff_dvd' hmb).mp (hmod a₀ ha₀S b hb))]
      exact congrArg (· * K) hab
    omega

/-- **The count of a residue class mod `M` with an extra divisibility by `K`.** The two conditions
are coprime — `K` divides a member, which is coprime to `M` — so their conjunction is a single
class mod `MK`. -/
theorem card_filter_dvd_le {M B K : ℕ} {A : Finset ℕ}
    (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ B) (hcop : ∀ r ∈ A, Nat.Coprime M r)
    (hmod : ∀ r ∈ A, Nat.ModEq M r 1) :
    #{r ∈ A | K ∣ r} ≤ B / (M * K) + 1 := by
  rcases Finset.eq_empty_or_nonempty {r ∈ A | K ∣ r} with h | ⟨r₀, hr₀⟩
  · simp [h]
  obtain ⟨hr₀A, hr₀K⟩ := Finset.mem_filter.mp hr₀
  have hcopMK : Nat.Coprime M K := (hcop r₀ hr₀A).coprime_dvd_right hr₀K
  refine card_le_of_modEq (fun a ha ↦ hA a (Finset.mem_filter.mp ha).1) fun a ha b hb ↦ ?_
  rw [Finset.mem_filter] at ha hb
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcopMK).mp ⟨(hmod a ha.1).trans (hmod b hb.1).symm,
    (Nat.modEq_zero_iff_dvd.mpr ha.2).trans (Nat.modEq_zero_iff_dvd.mpr hb.2).symm⟩

/-! ## A dense family of squarefree moduli in the top block -/

/-- **The counting input to the refutation.** Let `M` absorb every prime up to `w ≥ 100` and let
the truncation satisfy `B ≥ (35M)^2`. Then the top block `(B/2,B]` contains at least `B/(4M)`
integers that are squarefree, coprime to `M`, and satisfy `φ(r) ≥ r/2`.

The density is `1/M` rather than `φ(M)/M` because the family is taken inside the single residue
class `1 mod M` — crude, and enough: what the refutation needs is only that the count beats
`M·B/\log x`, and `M^2 ≤ \log x` for the pre-sieving modulus.

Three removals, each paid for by the coprimality to `M`, which forces every prime factor of a
member above `w`:
* the class `1 mod M` in `(B/2,B]` has at least `B/(2M) - 2` members;
* a non-squarefree member is divisible by `n^2` for some `w < n ≤ √B`, and the class `1 mod M` with
  `n^2 ∣ ·` is a single class mod `Mn^2`, so at most `B/(Mn^2) + 1` members — `∑_{n>w}n^{-2} ≤ 1/w`
  kills the first part and `√B` bounds the second;
* a member with `φ(r) < r/2` has `∑_{p ∣ r}1/p > 1/2`, of which at most `1/4` can come from the
  single prime factor exceeding `√B`, so `∑_{w<p≤√B, p ∣ r}1/p > 1/4`; summing over the class and
  exchanging gives the same `B/(Mw) + √B`. -/
theorem exists_dense_squarefree_block {M w B : ℕ} (hM : 0 < M) (hw : 100 ≤ w)
    (hMw : ∀ p : ℕ, p.Prime → p ≤ w → p ∣ M) (hMB : (35 * M) ^ 2 ≤ B) :
    ∃ Fam : Finset ℕ, (∀ r ∈ Fam, (1 ≤ r ∧ r ≤ B) ∧ B < 2 * r ∧ Nat.Coprime M r ∧
      Squarefree r ∧ (r : ℝ) ≤ 2 * (r.totient : ℝ)) ∧ (B : ℝ) / (4 * M) ≤ (Fam.card : ℝ) := by
  -- ### size bookkeeping
  set T := Nat.sqrt B
  have h35T : 35 * M ≤ T := Nat.le_sqrt'.mpr hMB
  have hT2 : T ^ 2 ≤ B := Nat.sqrt_le' B
  have hT35 : 35 ≤ T := le_trans (by omega) h35T
  have hMTB : 35 * M * T ≤ B := by nlinarith [Nat.mul_le_mul_right T h35T]
  have hBT : B < (T + 1) ^ 2 := Nat.lt_succ_sqrt' B
  -- ### the arithmetic progression `1 mod M` in the top block
  set N := B / (2 * M)
  have h2M : 0 < 2 * M := by omega
  have hNle : 2 * M * N ≤ B := Nat.mul_div_le B (2 * M)
  have hNgt : B < 2 * M * (N + 1) := Nat.lt_mul_div_succ B h2M
  have hN2 : 2 ≤ N := (Nat.le_div_iff_mul_le h2M).mpr (by nlinarith)
  set A : Finset ℕ := (Finset.Ico (N + 1) (2 * N)).image (fun j ↦ 1 + M * j) with hAdef
  have hcardA : A.card = N - 1 := by
    rw [hAdef, Finset.card_image_of_injOn fun a _ b _ hab ↦
      Nat.eq_of_mul_eq_mul_left hM (Nat.add_left_cancel hab), Nat.card_Ico]
    omega
  have hAmem : ∀ r ∈ A, (1 ≤ r ∧ r ≤ B) ∧ B < 2 * r ∧ Nat.Coprime M r ∧ Nat.ModEq M r 1 := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    rw [Finset.mem_Ico] at hj
    have h₁ := Nat.mul_le_mul_left M (show j + 1 ≤ 2 * N by omega)
    have h₂ := Nat.mul_le_mul_left M hj.1
    refine ⟨⟨by omega, by linarith⟩, by linarith, ?_, Nat.add_mul_mod_self_left 1 M j⟩
    exact (Nat.coprime_add_mul_left_right M 1 j).mpr (Nat.coprime_one_right M)
  have hAcount : ∀ K : ℕ, #{r ∈ A | K ∣ r} ≤ B / (M * K) + 1 := fun K ↦
    card_filter_dvd_le (fun r hr ↦ (hAmem r hr).1) (fun r hr ↦ (hAmem r hr).2.2.1)
      (fun r hr ↦ (hAmem r hr).2.2.2)
  -- ### every prime factor of a member exceeds `w`
  have hbig : ∀ r ∈ A, ∀ p : ℕ, p.Prime → p ∣ r → w < p := fun r hr p hp hpr ↦ by
    by_contra hcon
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes (hAmem r hr).2.2.1 (hMw p hp (by omega)) hpr)
  -- ### the real-valued per-modulus count
  have hcountR : ∀ K : ℕ, ∀ S ⊆ A, (#{r ∈ S | K ∣ r} : ℝ) ≤ (B : ℝ) / (M * K) + 1 := by
    intro K S hS
    have h := (Finset.card_le_card (Finset.filter_subset_filter _ hS)).trans (hAcount K)
    calc (#{r ∈ S | K ∣ r} : ℝ) ≤ ((B / (M * K) : ℕ) : ℝ) + 1 := by exact_mod_cast h
      _ ≤ (B : ℝ) / (M * K) + 1 := by rw [← Nat.cast_mul]; gcongr; exact Nat.cast_div_le
  -- ### the two bad sets
  set bad₁ : Finset ℕ := {r ∈ A | ¬ Squarefree r}
  set bad₂ : Finset ℕ := {r ∈ A | ¬ ((r : ℝ) ≤ 2 * (r.totient : ℝ))}
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hwR : (100 : ℝ) ≤ w := by exact_mod_cast hw
  have hTR : (35 : ℝ) ≤ T := by exact_mod_cast hT35
  -- ### the tail bound both removals end in
  have hsumbd : ∑ n ∈ Icc (w + 1) T, ((B : ℝ) / M * (1 / (n : ℝ) ^ 2) + 1)
      ≤ (B : ℝ) / M * (1 / w) + T := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_one]
    gcongr
    · exact sum_Icc_one_div_sq_le (by omega) T
    · exact_mod_cast (by rw [Nat.card_Icc]; omega : #(Icc (w + 1) T) ≤ T)
  -- ### the non-squarefree members
  have hb₁card : (bad₁.card : ℝ) ≤ (B : ℝ) / M * (1 / w) + T := by
    have hcover : bad₁ ⊆ (Icc (w + 1) T).biUnion (fun n ↦ {r ∈ A | n ^ 2 ∣ r}) := by
      intro r hr
      obtain ⟨hrA, hrsq⟩ := Finset.mem_filter.mp hr
      obtain ⟨hr1, hrB⟩ := (hAmem r hrA).1
      obtain ⟨p, hp, hpr⟩ : ∃ p : ℕ, p.Prime ∧ p * p ∣ r := by
        simpa [Nat.squarefree_iff_prime_squarefree] using hrsq
      have hpw := hbig r hrA p hp ((dvd_mul_right p p).trans hpr)
      have hpT : p ≤ T := Nat.le_sqrt.mpr ((Nat.le_of_dvd hr1 hpr).trans hrB)
      exact Finset.mem_biUnion.mpr
        ⟨p, Finset.mem_Icc.mpr ⟨hpw, hpT⟩, Finset.mem_filter.mpr ⟨hrA, by rwa [sq]⟩⟩
    calc (bad₁.card : ℝ) ≤ ∑ n ∈ Icc (w + 1) T, (#{r ∈ A | n ^ 2 ∣ r} : ℝ) := by
          exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
      _ ≤ ∑ n ∈ Icc (w + 1) T, ((B : ℝ) / M * (1 / (n : ℝ) ^ 2) + 1) :=
          Finset.sum_le_sum fun n _ ↦ (hcountR _ A le_rfl).trans_eq (by push_cast; ring)
      _ ≤ _ := hsumbd
  -- ### the members with a small totient
  have hb₂card : (bad₂.card : ℝ) ≤ 4 * ((B : ℝ) / M * (1 / w) + T) := by
    have hkey : ∀ r ∈ bad₂, (1 : ℝ) / 4 ≤ ∑ p ∈ Icc (w + 1) T with p ∣ r, (1 : ℝ) / p := by
      intro r hr
      obtain ⟨hrA, hrtot⟩ := Finset.mem_filter.mp hr
      obtain ⟨hr1, hrB⟩ := (hAmem r hrA).1
      -- the totient product bound
      have htot : (r : ℝ) * (1 - ∑ p ∈ r.primeFactors, (1 : ℝ) / p) ≤ r.totient := by
        have hid := congrArg ((↑) : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors r)
        push_cast at hid
        rw [hid]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg r)
        simpa [one_div] using one_sub_sum_le_prod_one_sub (fun p _ ↦ by positivity)
          fun p hp ↦ inv_le_one_of_one_le₀
            (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
      -- so the prime-reciprocal sum exceeds 1/2
      have hhalf : (1 : ℝ) / 2 < ∑ p ∈ r.primeFactors, (1 : ℝ) / p := lt_of_not_ge fun h ↦
        hrtot (by nlinarith [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α := ℝ) r)])
      -- at most one prime factor exceeds `√B`, contributing at most `1/36`
      have hbigpart : ∑ p ∈ r.primeFactors with ¬ p ≤ T, (1 : ℝ) / p ≤ 1 / 4 := by
        have hcard : #{p ∈ r.primeFactors | ¬ p ≤ T} ≤ 1 := by
          refine Finset.card_le_one.mpr fun p hp q hq ↦ by_contra fun hne ↦ ?_
          rw [Finset.mem_filter] at hp hq
          have hpq : p * q ∣ r := Nat.Coprime.mul_dvd_of_dvd_of_dvd
            ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp.1)
              (Nat.prime_of_mem_primeFactors hq.1)).mpr hne)
            (Nat.dvd_of_mem_primeFactors hp.1) (Nat.dvd_of_mem_primeFactors hq.1)
          have : (T + 1) * (T + 1) ≤ p * q := Nat.mul_le_mul (by omega) (by omega)
          linarith [Nat.le_of_dvd hr1 hpq]
        refine (Finset.sum_le_card_nsmul _ _ (1 / 4) fun p hp ↦ ?_).trans ?_
        · have := (Finset.mem_filter.mp hp).2
          exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 4 ≤ p))
        · have : (#{p ∈ r.primeFactors | ¬ p ≤ T} : ℝ) ≤ 1 := by exact_mod_cast hcard
          rw [nsmul_eq_mul]
          linarith
      have hsplit := Finset.sum_filter_add_sum_filter_not r.primeFactors (· ≤ T)
        fun p ↦ (1 : ℝ) / p
      refine (by linarith : (1 : ℝ) / 4 ≤ ∑ p ∈ r.primeFactors with p ≤ T, (1 : ℝ) / p).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun p _ _ ↦ by positivity)
      obtain ⟨hp, hpT⟩ := Finset.mem_filter.mp hp
      have hpr := Nat.dvd_of_mem_primeFactors hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨hbig r hrA p (Nat.prime_of_mem_primeFactors hp) hpr, hpT⟩, hpr⟩
    have hswap : ∑ r ∈ bad₂, ∑ p ∈ Icc (w + 1) T with p ∣ r, (1 : ℝ) / p
        = ∑ p ∈ Icc (w + 1) T, 1 / (p : ℝ) * #{r ∈ bad₂ | p ∣ r} := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hterms : ∀ p ∈ Icc (w + 1) T, 1 / (p : ℝ) * #{r ∈ bad₂ | p ∣ r}
        ≤ (B : ℝ) / M * (1 / (p : ℝ) ^ 2) + 1 := by
      intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by simp at hp; omega : 1 ≤ p)
      calc 1 / (p : ℝ) * #{r ∈ bad₂ | p ∣ r} ≤ 1 / p * ((B : ℝ) / (M * p) + 1) := by
            gcongr; exact hcountR p bad₂ (Finset.filter_subset _ _)
        _ = (B : ℝ) / M * (1 / (p : ℝ) ^ 2) + 1 / p := by ring
        _ ≤ (B : ℝ) / M * (1 / (p : ℝ) ^ 2) + 1 := by
            gcongr; exact (div_le_one (by linarith)).mpr hp1
    have := ((Finset.card_nsmul_le_sum _ _ _ hkey).trans_eq hswap).trans
      ((Finset.sum_le_sum hterms).trans hsumbd)
    rw [nsmul_eq_mul] at this
    linarith
  -- ### the family, and its count
  refine ⟨A \ (bad₁ ∪ bad₂), fun r hr ↦ ?_, ?_⟩
  · obtain ⟨hrA, hrn⟩ := Finset.mem_sdiff.mp hr
    obtain ⟨hr1B, hrblk, hcop, -⟩ := hAmem r hrA
    exact ⟨hr1B, hrblk, hcop,
      by_contra fun h ↦ hrn (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hrA, h⟩)),
      by_contra fun h ↦ hrn (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrA, h⟩))⟩
  · have hcards : (A.card : ℝ) ≤ (A \ (bad₁ ∪ bad₂)).card + (bad₁.card + bad₂.card) := by
      exact_mod_cast Finset.card_le_card_sdiff_add_card.trans
        (Nat.add_le_add_left (Finset.card_union_le bad₁ bad₂) _)
    have hcardAR : (A.card : ℝ) = N - 1 := by rw [hcardA, Nat.cast_sub (by omega), Nat.cast_one]
    -- the conclusion, in the single variable `B/M`
    have hq : (B : ℝ) / M < 2 * (N + 1) := by
      have : (B : ℝ) < 2 * M * (N + 1) := by exact_mod_cast hNgt
      rw [div_lt_iff₀ hMR]
      linarith
    have hq35T : 35 * (T : ℝ) ≤ B / M := by
      have : (35 : ℝ) * M * T ≤ B := by exact_mod_cast hMTB
      rw [le_div_iff₀ hMR]
      linarith
    have e3 : (B : ℝ) / M * (1 / w) ≤ B / M / 100 := by
      rw [mul_one_div]
      gcongr
    rw [show (B : ℝ) / (4 * M) = B / M / 4 by ring]
    linarith

/-! ## Two growth facts -/

/-- `C\log x ≤ x` eventually, for every constant: `Real.isLittleO_log_id_atTop`. -/
theorem eventually_const_mul_log_le (C : ℝ) : ∀ᶠ x : ℝ in atTop, C * Real.log x ≤ x := by
  filter_upwards [(Real.isLittleO_log_id_atTop.const_mul_left C).bound one_pos,
    eventually_ge_atTop 0] with x hx hx0
  simp only [Real.norm_eq_abs, id_eq, one_mul, abs_of_nonneg hx0] at hx
  exact (le_abs_self _).trans hx

/-- **`W(x)^2` is smaller than any fixed multiple of `\log x`**: `Gap212.Sieve.W_sq_le_log` with a
constant in front. `W(x) ≤ 4^{\log u}` with `u = \log\log x`, so `C·W(x)^2 ≤ C\exp(2\log4\log u)`,
and `\log C + 2\log4\log u < u` eventually because `\log u = o(u)`. -/
theorem eventually_const_mul_W_sq_lt_log (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * ((W x : ℝ)) ^ 2 < Real.log x := by
  have key : ∀ᶠ u : ℝ in atTop, Real.log (|C| + 1) + 2 * Real.log 4 * Real.log u < u ∧ 1 ≤ u := by
    filter_upwards [(Real.isLittleO_log_id_atTop.const_mul_left (2 * Real.log 4)).bound
        (c := 1 / 2) (by norm_num), eventually_ge_atTop 1,
      eventually_gt_atTop (2 * Real.log (|C| + 1))] with u hu hu1 hu2
    simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u)] at hu
    exact ⟨by linarith [le_abs_self (2 * Real.log 4 * Real.log u)], hu1⟩
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually key,
    eventually_gt_atTop 1] with x ⟨hkey, hu1⟩ hx1
  set u := Real.log (Real.log x)
  have hW : (W x : ℝ) ≤ Real.exp (Real.log u * Real.log 4) := by
    calc (W x : ℝ) ≤ (4 : ℝ) ^ (⌊Real.log u⌋₊ : ℝ) := by
          rw [Real.rpow_natCast]; exact_mod_cast primorial_le_four_pow _
      _ ≤ (4 : ℝ) ^ Real.log u :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le (Real.log_nonneg hu1))
      _ = _ := by rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  calc C * (W x : ℝ) ^ 2 ≤ (|C| + 1) * Real.exp (Real.log u * Real.log 4) ^ 2 := by
        gcongr; linarith [le_abs_self C]
    _ = Real.exp (Real.log (|C| + 1) + 2 * Real.log 4 * Real.log u) := by
        rw [Real.exp_add, Real.exp_log (by positivity), ← Real.exp_nat_mul]
        ring_nf
    _ < Real.exp u := Real.exp_lt_exp.mpr hkey
    _ = Real.log x := Real.exp_log (Real.log_pos hx1)

/-! ## The refutation -/

/-- **`Gap212.Sieve.OneCoordLcmDecayAtLevel s` is false, for every `s`**, so the hypothesis of
`Gap212.Sieve.selbergSievingError_of_oneCoordLcmDecayAtLevel` is never satisfied.

Read the estimate at `β = 1`, at the truncation `B = ⌈x⌉` and at the modulus `e = 1`, with a
profile that does **not** vanish at `\log_xB = 1` — any `C¹` bump with `F(1) = 1`. Then the
one-coordinate pair sum is exactly
(`Gap212.Sieve.sum_pairs_div_lcm_eq_sum_totient_mul_sq`)

  `∑_{d,d'} μ(d)μ(d')F(\log_xd)F(\log_xd')/[d,d'] = ∑_{r ≤ B} φ(r)(∑_{r ∣ d}μ(d)F(\log_xd)/d)^2`,

a **sum of squares** — at `F = G` there is no cancellation left to exploit. Keep only the moduli
`r ∈ (B/2,B]`, where the inner sum is the single term `μ(r)F(\log_xr)/r`
(`Gap212.Sieve.filter_dvd_eq_singleton`): the sum is at least
`\tfrac14∑_{r ∈ (B/2,B]}φ(r)/r^2` over the `r` that are squarefree and coprime to `W(x)`, because
`F(\log_xr) → F(1) = 1` uniformly on that block. `Gap212.Sieve.exists_dense_squarefree_block` gives
`B/(4W(x))` such moduli with `φ(r) ≥ r/2`, so the sum is at least `1/(32W(x))` — while the asserted
bound at `e = 1` is `K/B_x ≤ KW(x)/\log x`, since `φ(W(x)) ≥ 1`. That needs
`\log x ≤ 32KW(x)^2`, and `Gap212.Sieve.eventually_const_mul_W_sq_lt_log` says the opposite.

If the profiles are required to vanish from `β` on, as in
`Gap212.Sieve.LcmGramSumLimitOfSupport` (`Gap212.Sieve.tendsto_boxPairSum`, hypothesis `hFβ`), the
block above is `O(\log^{-2}x)` instead of `Θ(φ(W)/W)`, because
`|F(\log_xr)| ≤ \|F'\|_∞(β - \log_xr) ≪ 1/\log x` there; see
`Gap212.Sieve.OneCoordLcmDecayAtLevelOfSupport`. -/
theorem not_oneCoordLcmDecayAtLevel (s : ℝ) : ¬ OneCoordLcmDecayAtLevel s := by
  intro h
  -- a `C¹` bump with `F(1) = 1`
  obtain ⟨F, -, hFc, hFd, -, hF1⟩ := exists_contDiff_tsupport_subset
    (E := ℝ) (s := Set.univ) (x := (1 : ℝ)) (n := 1) Filter.univ_mem
  have hFcd : ContDiff ℝ 1 F := by exact_mod_cast hFd
  obtain ⟨K, hK, hev⟩ := h 1 one_pos F F hFcd hFc hFcd hFc
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp (hFcd.continuous.continuousAt (x := (1 : ℝ)))
    (1 / 2) (by norm_num)
  have hFhalf : ∀ t : ℝ, |t - 1| < δ → (1 : ℝ) / 2 < F t := fun t ht ↦ by
    have := hδ (x := t) ht
    rw [Real.dist_eq, hF1] at this
    linarith [(abs_lt.mp this).1]
  -- the largeness conditions on `x`
  obtain ⟨x, hxK, hxW, hxsq, hxC, hxδ, hx2, hxw⟩ := (hev.and <| W_sq_le_log.and <|
    (eventually_const_mul_log_le 1225).and <| (eventually_const_mul_W_sq_lt_log (32 * K + 1)).and <|
    (Real.tendsto_log_atTop.eventually_gt_atTop (Real.log 2 / δ)).and <|
    (eventually_gt_atTop (2 : ℝ)).and <| (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      Real.tendsto_log_atTop)).eventually_ge_atTop (100 : ℝ)).exists
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  set B : ℕ := ⌈x⌉₊
  have hxB : x ≤ (B : ℝ) := Nat.le_ceil x
  have hBlt : (B : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hW0 : 0 < W x := primorial_pos _
  have hWR : (0 : ℝ) < W x := by exact_mod_cast hW0
  -- ### the dense family of top moduli
  have hMB : (35 * W x) ^ 2 ≤ B := by
    have : (35 * W x : ℝ) ^ 2 ≤ B := by linarith
    exact_mod_cast this
  obtain ⟨Fam, hFam, hFamcard⟩ := exists_dense_squarefree_block hW0
    (Nat.le_floor (by exact_mod_cast hxw)) (fun p hp hpw ↦ hp.dvd_primorial_iff.mpr hpw) hMB
  -- ### the profile is above `1/2` on the block
  have hblockF : ∀ r ∈ Fam, (1 : ℝ) / 2 < F (Notation.logx x r) := by
    intro r hr
    obtain ⟨⟨hr1, hrB⟩, hblk, -⟩ := hFam r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
    have hrB : (r : ℝ) ≤ B := by exact_mod_cast hrB
    have hBr : (B : ℝ) < 2 * r := by exact_mod_cast hblk
    have hup : Real.log r ≤ Real.log x + Real.log 2 := by
      rw [← Real.log_mul (by linarith) (by norm_num)]
      exact Real.log_le_log hr0 (by linarith)
    have hlow : Real.log x - Real.log 2 < Real.log r := by
      rw [← Real.log_div (by linarith) (by norm_num)]
      exact Real.log_lt_log (by linarith) (by linarith)
    rw [div_lt_iff₀ hδ0] at hxδ
    refine hFhalf _ ?_
    rw [Notation.logx, show Real.log r / Real.log x - 1 = (Real.log r - Real.log x) / Real.log x by
      field_simp, abs_div, abs_of_pos hlogx, div_lt_iff₀ hlogx, abs_lt]
    constructor <;> linarith
  -- ### the pair sum at `e = 1` is at least `1/(32W(x))`
  set l : ℕ → ℝ := fun d ↦ (μ d : ℝ) * F (Notation.logx x d) with hldef
  have hlowsum : ∑ r ∈ Fam, (r.totient : ℝ) * (l r / r) ^ 2
      ≤ restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeight x F F) 1 := by
    rw [restrictedSum_one, Finset.sum_product]
    exact sum_block_le_sum_pairs_div_lcm B (wBox x B) (fun d hd ↦ (mem_wBox.mp hd).1) l Fam
      (fun r hr ↦ Finset.mem_Icc.mpr (hFam r hr).1)
      fun r hr ↦ ⟨(hFam r hr).2.1, mem_wBox.mpr ⟨(hFam r hr).1, (hFam r hr).2.2.1⟩⟩
  have hB0 : (0 : ℝ) < B := by linarith
  have hterm : ∀ r ∈ Fam, (1 : ℝ) / (8 * B) ≤ (r.totient : ℝ) * (l r / r) ^ 2 := by
    intro r hr
    obtain ⟨⟨hr1, hrB⟩, -, -, hsf, hphi⟩ := hFam r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
    have hrB : (r : ℝ) ≤ B := by exact_mod_cast hrB
    have hl2 : (1 : ℝ) / 4 ≤ l r ^ 2 := by
      have hmu : ((μ r : ℤ) : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
      have := hblockF r hr
      simp only [hldef, mul_pow, hmu, one_mul]
      nlinarith
    calc (1 : ℝ) / (8 * B) ≤ 1 / (8 * r) := by gcongr
      _ = 1 / 4 * (r / 2) / r ^ 2 := by field_simp; ring
      _ ≤ l r ^ 2 * r.totient / r ^ 2 := by gcongr; linarith
      _ = (r.totient : ℝ) * (l r / r) ^ 2 := by ring
  have hQlow : (1 : ℝ) / (32 * W x)
      ≤ restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeight x F F) 1 := by
    refine le_trans ?_ ((Finset.card_nsmul_le_sum _ _ _ hterm).trans hlowsum)
    rw [nsmul_eq_mul]
    calc (1 : ℝ) / (32 * W x) = B / (4 * W x) * (1 / (8 * B)) := by field_simp; ring
      _ ≤ _ := by gcongr
  -- ### against the asserted bound
  have hbd := hxK B 1 (by rwa [Real.rpow_one]) one_pos
  rw [Nat.cast_one, Real.one_rpow, mul_one, div_mul_eq_mul_div, div_div_eq_mul_div] at hbd
  have hchain : (1 : ℝ) / (32 * W x) ≤ K * W x / Real.log x :=
    (hQlow.trans ((le_abs_self _).trans hbd)).trans (div_le_div_of_nonneg_left
      (mul_nonneg hK hWR.le) hlogx (le_mul_of_one_le_left hlogx.le
        (by exact_mod_cast Nat.totient_pos.mpr hW0)))
  rw [div_le_div_iff₀ (by positivity) hlogx] at hchain
  linarith [pow_pos hWR 2]

/-! ## The one-coordinate estimate for profiles vanishing from `β` on -/

/-- **The one-coordinate estimate with the profiles required to vanish from `β` on**, the analogue
of the clause of `Gap212.Sieve.LcmGramSumLimitOfSupport` (`Gap212.Sieve.tendsto_boxPairSum`,
hypothesis `hFβ`). The bound is

  `|∑_{(d,d') ∈ [1,B]^2, (dd',W)=1, e ∣ [d,d']} μ(d)F(\log_xd)μ(d')G(\log_xd')/[d,d']|
      ≤ K/(B_x·e^s)`,  `B_x = (φ(W)/W)\log x`,

asked for at truncations `B ≥ x^β` and only for profiles supported below `β` — so the truncation
does not cut the profiles' support.

`Gap212.Sieve.not_oneCoordLcmDecayAtLevel` refutes the statement without the support clause at
`β = 1`, `B = ⌈x⌉`, `e = 1` and a profile with `F(1) = 1`: the top block of moduli `r ∈ (B/2,B]`
then contributes `≍φ(W)/W`, uncancelled, against an asserted `K/B_x`. With the clause the same
block contributes `O(\log^{-2}x)`, because a `C^1` profile vanishing from `β` on satisfies
`|F(\log_xr)| ≤ \|F'\|_∞(β - \log_xr) ≪ 1/\log x` for `r` within a constant factor of `x^β`.

The absolute value of the one-coordinate pair sum is `≍B_x^3` where the signed sum is `≍B_x^{-1}`;
the diagonal `d = d'` alone is `≍B_x/p` at `p ∣ d`, positive, and is cancelled only against the
off-diagonal. At `F = G` the sum is `∑_rφ(r)y_r^2` with `y_r = ∑_{r ∣ d}μ(d)F(\log_xd)/d`
(`Gap212.Sieve.sum_pairs_div_lcm_eq_sum_totient_mul_sq`), so the estimate amounts to each `y_r`
being small. A bound `|y_r| ≪ 1/r` uniform in `r` is false, by the primorial block
`r = ∏_{⌊log log log x⌋ < p ≤ z} p`; and the partial-sum bound
`|S_q(w)| ≤ C(q/φ(q))/(1+log w)` loses `log log x` under Abel summation. The input used instead is
the smoothed bound `Gap212.Sieve.SmoothMoebiusInnerBound`, proved as
`Gap212.Sieve.smoothMoebiusInnerBound`, from which
`Gap212.Sieve.oneCoordLcmDecayAtLevelOfSupport_of_smoothMoebiusInnerBound` derives this `Prop` at
`s = 3/4`. -/
def OneCoordLcmDecayAtLevelOfSupport (s : ℝ) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ F G : ℝ → ℝ,
    ContDiff ℝ 1 F → HasCompactSupport F → ContDiff ℝ 1 G → HasCompactSupport G →
    (∀ t : ℝ, β ≤ t → F t = 0) → (∀ t : ℝ, β ≤ t → G t = 0) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop, ∀ B e : ℕ, x ^ β ≤ (B : ℝ) → 0 < e →
      |restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeight x F G) e|
        ≤ K / ((((W x).totient : ℝ) / (W x : ℝ) * Real.log x) * (e : ℝ) ^ s)

/-- **A null factor kills the sieved pair sum too**, the companion of
`Gap212.Sieve.boxPairSum_eq_zero_of_null`: the restricted sum has the same summands on a smaller
index set. -/
theorem sievedPairSum_eq_zero_of_null {k : ℕ} {F G : Fin k → ℝ → ℝ} {i₀ : Fin k}
    (hnull : (∀ t : ℝ, 0 ≤ t → F i₀ t = 0) ∨ ∀ t : ℝ, 0 ≤ t → G i₀ t = 0) {x : ℝ} (hx : 1 < x)
    (B : ℕ) : sievedPairSum x B F G = 0 := by
  have hmem : ∀ e ∈ Fintype.piFinset fun _ : Fin k ↦ {d ∈ Icc 1 B | Nat.Coprime (W x) d},
      ∀ i, 1 ≤ e i := fun e he i ↦
    (Finset.mem_Icc.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp he i)).1).1
  rw [sievedPairSum]
  refine Finset.sum_eq_zero fun d hd ↦ Finset.sum_eq_zero fun d' hd' ↦ ?_
  rcases hnull with hn | hn
  · simp [coeffProd_eq_zero_of_null hn hx (hmem d hd)]
  · simp [coeffProd_eq_zero_of_null hn hx (hmem d' hd')]

/-- **The sieving error at `β ≥ 1`, from the one-coordinate estimate for supported profiles.**
This is the conclusion of `Gap212.Sieve.SelbergSievingError m`, which is stated for `β ≥ 1`.

The restriction `β ≥ 1` matches the hypotheses: `Gap212.Sieve.OneCoordLcmDecayAtLevelOfSupport`
asks that the profiles vanish from `β` on, and the retreat condition gives that they vanish from
`1` on (`Gap212.Sieve.exists_null_or_forall_eq_zero_of_one_le`), or that one of them is null and
both sums vanish identically. At `β < 1` the truncation `B ≍ x^β` cuts a profile's support and the
one-coordinate sums are `≍φ(W)/W` rather than `≍1/B_x`
(`Gap212.Sieve.not_oneCoordLcmDecayAtLevel`).

Otherwise the proof is that of `Gap212.Sieve.selbergSievingError_of_oneCoordLcmDecayAtLevel`: the
`k`-coordinate coupling is
`Gap212.Sieve.exists_threshold_abs_prod_sub_sum_pairwise_coprime_le_rpow` and the one-coordinate
input is the hypothesis. -/
theorem tendsto_boxPairSum_sub_sievedPairSum_of_support {s : ℝ} (hs : 1 / 2 < s)
    (hdec : OneCoordLcmDecayAtLevelOfSupport s) (p : SupportParams) {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀)
    {m : ℕ} {j j' : Fin p.n} (F G : Fin (m + 1) → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ 1 (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    (hsupp : IsRetreatedPair p (m + 1) j j' ε₀ F G)
    {β : ℝ} (hβ1 : 1 ≤ β) (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦ (((W x).totient : ℝ) / (W x : ℝ) * Real.log x) ^ (m + 1) *
        (boxPairSum x (B x) F G - sievedPairSum x (B x) F G)) atTop (nhds 0) := by
  have hβ : 0 < β := by linarith
  -- the null cases: both sums vanish identically
  have hnullcase : ∀ i₀ : Fin (m + 1),
      ((∀ t : ℝ, 0 ≤ t → F i₀ t = 0) ∨ ∀ t : ℝ, 0 ≤ t → G i₀ t = 0) →
      Tendsto (fun x : ℝ ↦ (((W x).totient : ℝ) / (W x : ℝ) * Real.log x) ^ (m + 1) *
        (boxPairSum x (B x) F G - sievedPairSum x (B x) F G)) atTop (nhds 0) := by
    intro i₀ hn
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [boxPairSum_eq_zero_of_null hn hx, sievedPairSum_eq_zero_of_null hn hx, sub_self, mul_zero]
  rcases exists_null_or_forall_eq_zero_of_one_le hε₀
      (fun t ht hne ↦ (hsupp t ht).1 hne) with ⟨i₀, hnF⟩ | hF1
  · exact hnullcase i₀ (Or.inl hnF)
  rcases exists_null_or_forall_eq_zero_of_one_le hε₀
      (fun t ht hne ↦ (hsupp t ht).2 hne) with ⟨i₀, hnG⟩ | hG1
  · exact hnullcase i₀ (Or.inr hnG)
  refine Metric.tendsto_nhds.mpr fun ε' hε' ↦ ?_
  -- the support clause at `β`, from the retreat's clause at `1`
  choose K hK hKev using fun i : Fin (m + 1) ↦
    hdec β hβ (F i) (G i) (hF i) (hFc i) (hG i) (hGc i) (fun t ht ↦ hF1 i t (by linarith))
      (fun t ht ↦ hG1 i t (by linarith))
  set KK : ℝ := ∑ i, K i
  have hKK0 : 0 ≤ KK := Finset.sum_nonneg fun i _ ↦ hK i
  have hε : 0 < ε' / (2 * (KK ^ (m + 1) + 1)) := by positivity
  obtain ⟨z, hz⟩ := exists_threshold_abs_prod_sub_sum_pairwise_coprime_le_rpow (Fin (m + 1)) hs hε
  filter_upwards [eventually_all.mpr hKev, eventually_dvd_W_of_prime_le z,
    eventually_gt_atTop (1 : ℝ), hB] with x hxK hxW hx1 hxB
  set Bx : ℝ := ((W x).totient : ℝ) / (W x : ℝ) * Real.log x
  have hW0 : 0 < W x := primorial_pos _
  have hBx : 0 < Bx :=
    mul_pos (div_pos (mod_cast Nat.totient_pos.mpr hW0) (mod_cast hW0)) (Real.log_pos hx1)
  have hB1 : 1 ≤ B x := by
    exact_mod_cast ((Real.one_lt_rpow_iff_of_pos (by linarith)).mpr (Or.inl ⟨hx1, hβ⟩)).le.trans hxB
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (by positivity), boxPairSum_eq_prod,
    sievedPairSum_eq_sum_guard]
  calc _ ≤ Bx ^ (m + 1) * ((KK / Bx) ^ Fintype.card (Fin (m + 1)) *
        (ε' / (2 * (KK ^ (m + 1) + 1)))) := by
        refine mul_le_mul_of_nonneg_left (Eq.trans_le (by congr!) <| hz _ lcmPair
          (fun i ↦ pairWeight x (F i) (G i)) {e ∈ Icc 1 (B x ^ 2) | (W x).Coprime e} _
          (fun a ha ↦ ?_) (fun a ha e he ↦ mem_divisorSet_of_dvd_lcmPair ha he) ?_
          (fun e he ↦ (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1) ?_ (by positivity) ?_)
          (by positivity)
        · obtain ⟨h1, h2⟩ := Finset.mem_product.mp ha
          exact lcmPair_pos (mem_wBox.mp h1).1.1 (mem_wBox.mp h2).1.1
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨le_rfl, Nat.one_le_pow _ _ hB1⟩, Nat.coprime_one_right _⟩
        · exact fun e he P hP hPe ↦ lt_of_not_ge fun hPz ↦ hP.ne_one
            (Nat.eq_one_of_dvd_coprimes (Finset.mem_filter.mp he).2 (hxW P hP hPz) hPe)
        · intro i e he
          have : (0 : ℝ) < (e : ℝ) ^ s := Real.rpow_pos_of_pos (mod_cast he) _
          refine (hxK i (B x) e hxB he).trans ?_
          rw [div_div]
          exact div_le_div_of_nonneg_right
            (Finset.single_le_sum (fun j _ ↦ hK j) (Finset.mem_univ i)) (by positivity)
    _ = KK ^ (m + 1) * ε' / (2 * (KK ^ (m + 1) + 1)) := by
        rw [Fintype.card_fin, div_pow]; field_simp
    _ < ε' := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [pow_nonneg hKK0 (m + 1)]

end Gap212.Sieve
