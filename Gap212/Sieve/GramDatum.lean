/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.SelbergDecoupling
public import PrimeGapsTheory.Arithmetic.GammaLogSum
public import PrimeGapsTheory.Sieve.Common.SieveDatumEval.PartialSummation

/-!
# The Gram weight is a sieve datum

`Gap212.Sieve.SelbergDecoupling` ends the algebra of the two divisor-sum asymptotics at the
one-coordinate form

  `∑_{d,d'≤B} μ(d)F(d)μ(d')G(d')/φ([d,d']) = ∑_{e≤B} g(e) Y_F(e) Y_G(e)`,

`g = Gap212.Sieve.gramWeight`, and `Gap212.Sieve.gramWeight_prime` computes `g(p) = (p-2)/(p-1)²`.
That is exactly the value `PrimeGaps.SieveDatum.gStar` takes at the density

  `γ(p) = p(p-2)/(p²-p-1)`,

so the outer `e`-sum is a sieve-datum sum and the whole `PrimeGaps` partial-summation apparatus
applies to it. This file builds the datum.

## The density must be `W`-tricked

`PrimeGaps.SieveDatum.γ_zero_of_dvd` demands `γ p = 0` at *every* prime dividing the datum's
modulus `V`. The bare density `p(p-2)/(p²-p-1)` has numerator `p(p-2)`, so it vanishes only at
`p = 2`; at `p = 3` it is `3/5`. So the bare density admits no modulus beyond `V = 2`, and in
particular cannot be paired with `V = W(x)`.

The fix is the `W`-trick the sieve wants anyway: kill the density on the primes dividing `V`,

  `γ_V(p) = if p ∣ V then 0 else p(p-2)/(p²-p-1)`  (`Gap212.Sieve.gramLocalOff`).

Then `γ_V` is a legitimate density at *any* squarefree `V`, its `gStar` is `gramWeight` off `V` and
`0` on it, and its `h` is `gramWeight` restricted to the integers coprime to `V`
(`Gap212.Sieve.gramDatum_h`) — which is exactly the weight of the `e`-sum, since the
tuples the counting leaves standing have every `[dᵢ,d'ᵢ]` coprime to `W`. Taking `V = W(x)` is
`Gap212.Sieve.wDatum`.

## Main definitions

* `Gap212.Sieve.gramLocal`: `p ↦ p(p-2)/(p²-p-1)`, the bare density at a prime.
* `Gap212.Sieve.gramLocalOff`: the same, killed on the primes dividing `V`.
* `Gap212.Sieve.gramGamma`: the totally multiplicative extension of `gramLocalOff V` to `ℕ`.
* `Gap212.Sieve.gramDatum`: the `PrimeGaps.SieveDatum` with density `gramGamma V`, modulus `V`,
  `A₁ = 1/2`, `A₃ = 2`, and Mertens constants `gramMertensConst V`.
* `Gap212.Sieve.wDatum`: `gramDatum` at `V = Gap212.GPY.W x`.

## Main results

* `Gap212.Sieve.gramLocal_div_sub_eq`: `γ(p)/(p - γ(p)) = (p-2)/(p-1)²`, the identity that makes
  this density the right one — the right-hand side is `gramWeight p`.
* `Gap212.Sieve.abs_delta_le`: the Mertens deviation of *one* density killed on the primes dividing
  a fixed modulus `V` is bounded by an explicit constant. This is `PrimeGaps.core_estimate` for a
  single density at an arbitrary fixed `V`, and supplies the datum's `mertens_bound` field.
* `Gap212.Sieve.gramDatum_h`: `(gramDatum V _ _).h n = gramWeight n` for `n` coprime to `V`, and
  `0` otherwise.
* `Gap212.Sieve.exists_gram_partial_sum_bound`: **Estimate A**, the outer `e`-sum evaluation
  `∑_{0<e<z, (e,V)=1} g(e) G(log e/log z) = 𝔖(γ_V) log z ∫₀¹ G + O(M)`, from
  `PrimeGaps.S1_partial_sum_sharp` at `gramDatum`.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset

/-! ### The density at a prime -/

/-- The bare local density `γ(p) = p(p-2)/(p²-p-1)` at a prime `p`: the unique density whose
`PrimeGaps.SieveDatum.gStar` value is the Gram weight `(p-2)/(p-1)²` of
`Gap212.Sieve.gramWeight_prime`. -/
noncomputable def gramLocal (p : ℕ) : ℝ := (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) ^ 2 - p - 1)

/-- The denominator `p² - p - 1` of the density is positive at every `p ≥ 2`. -/
theorem gram_denom_pos {p : ℕ} (hp : 2 ≤ p) : (0 : ℝ) < (p : ℝ) ^ 2 - p - 1 := by
  have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  nlinarith

/-- The density is nonnegative at every `p ≥ 2`. -/
theorem gramLocal_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ gramLocal p := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  exact div_nonneg (by nlinarith) (gram_denom_pos hp).le

/-- **The identity that picks this density.** `γ(p)/(p - γ(p)) = (p-2)/(p-1)²`, whose right-hand
side is `Gap212.Sieve.gramWeight p` by `gramWeight_prime`; the left-hand side is
`PrimeGaps.SieveDatum.gStar p` by `PrimeGaps.SieveDatum.gStar_prime`. -/
theorem gramLocal_div_sub_eq {p : ℕ} (hp : p.Prime) :
    gramLocal p / ((p : ℝ) - gramLocal p) = ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hD := gram_denom_pos hp.two_le
  have hsub : (p : ℝ) - gramLocal p = (p : ℝ) * ((p : ℝ) - 1) ^ 2 / ((p : ℝ) ^ 2 - p - 1) := by
    rw [gramLocal, eq_div_iff hD.ne', sub_mul, div_mul_cancel₀ _ hD.ne']
    ring
  rw [hsub, gramLocal, div_div_div_cancel_right₀ hD.ne']
  field_simp [show (p : ℝ) ≠ 0 by positivity, show (p : ℝ) - 1 ≠ 0 by linarith]

/-- `γ(p) < p`: equivalent to `0 < (p-1)²`. -/
theorem gramLocal_lt {p : ℕ} (hp : 2 ≤ p) : gramLocal p < (p : ℝ) := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  rw [gramLocal, div_lt_iff₀ (gram_denom_pos hp)]
  nlinarith

/-- `γ(p)/p = (p-2)/(p²-p-1) ≤ 1/2`: equivalent to `0 ≤ p² - 3p + 3`, which has negative
discriminant. -/
theorem gramLocal_density {p : ℕ} (hp : 2 ≤ p) : gramLocal p / (p : ℝ) ≤ 1 - 1 / 2 := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  rw [gramLocal, div_div,
    div_le_iff₀ (mul_pos (gram_denom_pos hp) (by linarith : (0 : ℝ) < (p : ℝ)))]
  nlinarith [gram_denom_pos hp]

/-- `|γ(p) - 1| = (p-1)/(p²-p-1) ≤ 2/p`: equivalent to `0 ≤ (p-2)(p+1)`. -/
theorem gramLocal_approx {p : ℕ} (hp : 2 ≤ p) : |gramLocal p - 1| ≤ 2 / (p : ℝ) := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hD := gram_denom_pos hp
  have hval : gramLocal p - 1 = (1 - (p : ℝ)) / ((p : ℝ) ^ 2 - p - 1) := by
    rw [gramLocal, div_sub_one hD.ne']; ring_nf
  rw [hval, abs_div, abs_of_pos hD, abs_of_nonpos (by linarith : (1 : ℝ) - (p : ℝ) ≤ 0),
    div_le_div_iff₀ hD (by linarith : (0 : ℝ) < (p : ℝ))]
  nlinarith

/-- The `W`-tricked local density: the bare density off `V`, and `0` on the primes dividing `V`.
Killing the small primes is what lets the density be paired with a modulus larger than `2`. -/
noncomputable def gramLocalOff (V p : ℕ) : ℝ := if p ∣ V then 0 else gramLocal p

/-- `gramLocalOff V p = 0` when `p ∣ V`. -/
theorem gramLocalOff_of_dvd {V p : ℕ} (h : p ∣ V) : gramLocalOff V p = 0 := if_pos h

/-- `gramLocalOff V p = gramLocal p` when `p ∤ V`. -/
theorem gramLocalOff_of_not_dvd {V p : ℕ} (h : ¬ p ∣ V) : gramLocalOff V p = gramLocal p :=
  if_neg h

/-- `0 ≤ gramLocalOff V p` for `p ≥ 2`. -/
theorem gramLocalOff_nonneg (V : ℕ) {p : ℕ} (hp : 2 ≤ p) : 0 ≤ gramLocalOff V p := by
  rw [gramLocalOff]
  split_ifs
  exacts [le_rfl, gramLocal_nonneg hp]

/-- `gramLocalOff V p < p` for `p ≥ 2`. -/
theorem gramLocalOff_lt (V : ℕ) {p : ℕ} (hp : 2 ≤ p) : gramLocalOff V p < (p : ℝ) := by
  rw [gramLocalOff]
  split_ifs
  exacts [by positivity, gramLocal_lt hp]

/-- `gramLocalOff V p / p ≤ 1 - 1/2` for `p ≥ 2`. -/
theorem gramLocalOff_density (V : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    gramLocalOff V p / (p : ℝ) ≤ 1 - 1 / 2 := by
  rw [gramLocalOff]
  split_ifs
  exacts [by norm_num, gramLocal_density hp]

/-! ### The density on all of `ℕ` -/

/-- The totally multiplicative extension of `gramLocalOff V` to all of `ℕ`, realized through the
prime factorization: `γ(n) = ∏_{p^k ‖ n} γ(p)^k`. In particular `γ(1) = 1` and
`γ(p) = gramLocalOff V p`. -/
noncomputable def gramGamma (V n : ℕ) : ℝ :=
  n.factorization.prod fun p k ↦ gramLocalOff V p ^ k

/-- At a prime `p`, `gramGamma V p = gramLocalOff V p`. -/
theorem gramGamma_prime (V : ℕ) {p : ℕ} (hp : p.Prime) : gramGamma V p = gramLocalOff V p := by
  simp [gramGamma, hp.factorization]

/-- `gramGamma V 1 = 1`. -/
theorem gramGamma_one (V : ℕ) : gramGamma V 1 = 1 := by simp [gramGamma]

/-- `gramGamma V n` is nonnegative. -/
theorem gramGamma_nonneg (V n : ℕ) : 0 ≤ gramGamma V n :=
  Finset.prod_nonneg fun _ hp ↦
    pow_nonneg (gramLocalOff_nonneg V (Nat.prime_of_mem_primeFactors hp).two_le) _

/-- `gramGamma V` is multiplicative: `γ(mn) = γ(m)γ(n)` for coprime `m` and `n`. -/
theorem gramGamma_mul (V : ℕ) {m n : ℕ} (h : Nat.Coprime m n) :
    gramGamma V (m * n) = gramGamma V m * gramGamma V n := by
  rw [gramGamma, Nat.factorization_mul_of_coprime h,
    Finsupp.prod_add_index_of_disjoint h.disjoint_primeFactors]
  rfl

/-- `gramGamma V p = 0` at a prime `p` dividing `V`. -/
theorem gramGamma_eq_zero_of_dvd (V : ℕ) {p : ℕ} (hp : p.Prime) (hpV : p ∣ V) :
    gramGamma V p = 0 := by rw [gramGamma_prime V hp, gramLocalOff_of_dvd hpV]

/-- `|γ(p) - 1| ≤ 2/p` at the primes *not* dividing `V`, which is all
`PrimeGaps.SieveDatum.γ_approx` asks. On a prime dividing `V` the density is `0`, so
`|γ(p) - 1| = 1`, which exceeds `2/p` as soon as `p ≥ 3`: the bound genuinely holds only off
`V`. -/
theorem gramGamma_approx (V : ℕ) {p : ℕ} (hp : p.Prime) (hpV : ¬ p ∣ V) :
    |gramGamma V p - 1| ≤ 2 / (p : ℝ) := by
  rw [gramGamma_prime V hp, gramLocalOff_of_not_dvd hpV]
  exact gramLocal_approx hp.two_le

/-! ### The Mertens deviation of a single density -/

/-- The convergent comparison series `∑_p 2 log p / p²`. -/
noncomputable def logSqSeries : ℝ := ∑' p : Nat.Primes, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2

/-- `logSqSeries` is nonnegative. -/
theorem logSqSeries_nonneg : 0 ≤ logSqSeries := tsum_nonneg fun _ ↦ by positivity

/-- A finite sum of `2 log p / p²` over primes is at most the full series. -/
theorem sum_two_log_div_sq_le {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    ∑ p ∈ S, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ logSqSeries := by
  classical
  rw [← Finset.sum_subtype_of_mem _ hS]
  exact PrimeGaps.summable_two_log_div_sq.sum_le_tsum (show Finset Nat.Primes from S.subtype _)
    fun _ _ ↦ by positivity

/-- `∑_{p ∣ V} log p / p`: the cost of the primes a density is allowed to kill. -/
noncomputable def killCost (V : ℕ) : ℝ := ∑ p ∈ V.primeFactors, Real.log p / p

/-- `killCost V` is nonnegative. -/
theorem killCost_nonneg (V : ℕ) : 0 ≤ killCost V :=
  Finset.sum_nonneg fun _ _ ↦ by positivity

/-- The `O(1)` of Mertens' second theorem on intervals, named from
`PrimeGaps.mertens_interval`. -/
noncomputable def mertensIntervalConst : ℝ := PrimeGaps.mertens_interval.choose

/-- `mertensIntervalConst` is nonnegative. -/
theorem mertensIntervalConst_nonneg : 0 ≤ mertensIntervalConst :=
  PrimeGaps.mertens_interval.choose_spec.1

/-- For `2 ≤ w ≤ z`, `|∑_{w ≤ p ≤ z} log p / p - log(z/w)| ≤ mertensIntervalConst`. -/
theorem abs_intervalPrimeSum_one_sub_log_le (w z : ℝ) (hw : 2 ≤ w) (hwz : w ≤ z) :
    |PrimeGaps.intervalPrimeSum (fun _ ↦ 1) w z - Real.log (z / w)| ≤ mertensIntervalConst :=
  PrimeGaps.mertens_interval.choose_spec.2 w z hw hwz

/-- The interval prime sums of two weights differ by the interval sum of their difference. -/
theorem intervalPrimeSum_sub (f g : ℕ → ℝ) (w z : ℝ) :
    PrimeGaps.intervalPrimeSum f w z - PrimeGaps.intervalPrimeSum g w z =
      ∑ p ∈ {p ∈ Finset.range (⌊z⌋₊ + 1) |
          Nat.Prime p ∧ (w : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) ≤ z}, (f p - g p) * Real.log p / p := by
  rw [PrimeGaps.intervalPrimeSum, PrimeGaps.intervalPrimeSum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ ↦ by ring

/-- The per-prime defect bound: at a prime dividing `V` the density is `0` and the term is
`log p / p`; off `V` it is `1 + O(1/p)` and the term is `O(log p / p²)`. -/
theorem abs_defect_term_le {γ : ℕ → ℝ} {V : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hkill : ∀ p : ℕ, p.Prime → p ∣ V → γ p = 0)
    (hunit : ∀ p : ℕ, p.Prime → ¬ p ∣ V → |γ p - 1| ≤ c / (p : ℝ))
    {p : ℕ} (hp : p.Prime) :
    |(γ p - 1) * Real.log p / p| ≤
      c * (2 * Real.log p / (p : ℝ) ^ 2) + (if p ∣ V then Real.log p / p else 0) := by
  have hlp : 0 ≤ Real.log p / p := by positivity
  have htail : 0 ≤ c / p * (Real.log p / p) := by positivity
  rw [mul_div_assoc, abs_mul, abs_of_nonneg hlp,
    show c * (2 * Real.log p / (p : ℝ) ^ 2) = 2 * (c / p * (Real.log p / p)) by ring]
  split_ifs with hd
  · simp [hkill p hp hd, htail]
  · linarith [mul_le_mul_of_nonneg_right (hunit p hp hd) hlp]

/-- **The weight defect is uniformly bounded.** For a density killed on the primes dividing `V` and
equal to `1 + O(1/p)` off them, the weighted interval prime sum differs from the unweighted one by
at most `c · ∑_p 2 log p/p² + ∑_{p ∣ V} log p/p`, uniformly in `w` and `z`. -/
theorem abs_intervalPrimeSum_sub_one_le {γ : ℕ → ℝ} {V : ℕ} {c : ℝ} (hV : V ≠ 0) (hc : 0 ≤ c)
    (hkill : ∀ p : ℕ, p.Prime → p ∣ V → γ p = 0)
    (hunit : ∀ p : ℕ, p.Prime → ¬ p ∣ V → |γ p - 1| ≤ c / (p : ℝ)) (w z : ℝ) :
    |PrimeGaps.intervalPrimeSum γ w z - PrimeGaps.intervalPrimeSum (fun _ ↦ 1) w z| ≤
      c * logSqSeries + killCost V := by
  classical
  rw [intervalPrimeSum_sub]
  set F := {p ∈ Finset.range (⌊z⌋₊ + 1) |
      Nat.Prime p ∧ (w : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) ≤ z} with hF
  have hFprime : ∀ p ∈ F, Nat.Prime p := fun p hp ↦ (Finset.mem_filter.mp hp).2.1
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun p hp ↦
    abs_defect_term_le hc hkill hunit (hFprime p hp)).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  refine add_le_add (mul_le_mul_of_nonneg_left (sum_two_log_div_sq_le hFprime) hc) ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun _ _ _ ↦ by positivity
  rw [Finset.mem_filter] at hp
  exact Nat.mem_primeFactors.mpr ⟨hFprime p hp.1, hp.2, hV⟩

/-- **Mertens deviation for one density at one fixed modulus.** A density killed on the primes
dividing `V` and equal to `1 + O(1/p)` off them has Mertens deviation
`Δ γ w z = ∑_{w ≤ p ≤ z} γ(p) log p/p - log(z/w)` bounded by the explicit constant
`mertensIntervalConst + (c · logSqSeries + killCost V)`, uniformly in `2 ≤ w ≤ z`.

This is `PrimeGaps.core_estimate` for a *single* density at an *arbitrary* fixed modulus.
`core_estimate` is stated for a family `γ : ℝ → ℕ → ℝ` with `V = W N` and exploits that a
primorial's prime divisors form an initial segment of the primes; its lower bound therefore carries
a `log (D₀ N)`, which grows with `N`. Here `V` is fixed, the primes it kills contribute the fixed
constant `killCost V`, and the bound is two-sided and symmetric — which is what
`PrimeGaps.SieveDatum.mertens_bound` needs, since a `SieveDatum` has one fixed `V`. -/
theorem abs_delta_le {γ : ℕ → ℝ} {V : ℕ} {c : ℝ} (hV : V ≠ 0) (hc : 0 ≤ c)
    (hkill : ∀ p : ℕ, p.Prime → p ∣ V → γ p = 0)
    (hunit : ∀ p : ℕ, p.Prime → ¬ p ∣ V → |γ p - 1| ≤ c / (p : ℝ)) (w z : ℝ)
    (hw : 2 ≤ w) (hwz : w ≤ z) :
    |PrimeGaps.Δ γ w z| ≤ mertensIntervalConst + (c * logSqSeries + killCost V) := by
  rw [PrimeGaps.Δ]
  exact (abs_sub_le _ (PrimeGaps.intervalPrimeSum (fun _ ↦ 1) w z) _).trans <| by
    linarith [abs_intervalPrimeSum_sub_one_le hV hc hkill hunit w z,
      abs_intervalPrimeSum_one_sub_log_le w z hw hwz]

/-! ### The datum -/

/-- The explicit Mertens constant of the density `gramGamma V`. -/
noncomputable def gramMertensConst (V : ℕ) : ℝ :=
  mertensIntervalConst + (2 * logSqSeries + killCost V)

/-- `gramMertensConst V` is nonnegative. -/
theorem gramMertensConst_nonneg (V : ℕ) : 0 ≤ gramMertensConst V := by
  rw [gramMertensConst]
  linarith [mertensIntervalConst_nonneg, logSqSeries_nonneg, killCost_nonneg V]

/-- The Mertens deviation of `gramGamma V` is bounded by `gramMertensConst V`: the density kills
exactly the primes dividing `V` and satisfies `|γ(p) - 1| ≤ 2/p` at every prime. -/
theorem abs_gram_delta_le (V : ℕ) (hV : V ≠ 0) (w z : ℝ) (hw : 2 ≤ w) (hwz : w ≤ z) :
    |PrimeGaps.Δ (gramGamma V) w z| ≤ gramMertensConst V :=
  abs_delta_le hV (by norm_num) (fun p hp hpV ↦ gramGamma_eq_zero_of_dvd V hp hpV)
    (fun p hp hpV ↦ gramGamma_approx V hp hpV) w z hw hwz

/-- **The sieve datum of the `W`-tricked Gram weight.** Density
`γ(p) = if p ∣ V then 0 else p(p-2)/(p²-p-1)`, modulus `V`, `A₁ = 1/2`, `A₃ = 2`; its `gStar` is
`(p-2)/(p-1)²` off `V` and `0` on it, so its `h` is `Gap212.Sieve.gramWeight` restricted to the
integers coprime to `V` (`gramDatum_h`). -/
noncomputable def gramDatum (V : ℕ) (hV0 : 0 < V) (hVsq : Squarefree V) : PrimeGaps.SieveDatum where
  γ := gramGamma V
  A₁ := 1 / 2
  V := V
  A₃ := 2
  γ_nonneg := gramGamma_nonneg V
  γ_one := gramGamma_one V
  γ_mul := fun _ _ h ↦ gramGamma_mul V h
  γ_lt := fun p hp ↦ by rw [gramGamma_prime V hp]; exact gramLocalOff_lt V hp.two_le
  A₁_pos := by norm_num
  A₁_lt_one := by norm_num
  γ_density := fun p hp ↦ by rw [gramGamma_prime V hp]; exact gramLocalOff_density V hp.two_le
  V_pos := hV0
  V_squarefree := hVsq
  A₃_nonneg := by norm_num
  γ_zero_of_dvd := fun p hp hpV ↦ gramGamma_eq_zero_of_dvd V hp hpV
  γ_approx := fun p hp hpV ↦ gramGamma_approx V hp hpV
  A₂ := gramMertensConst V + 1
  L := gramMertensConst V
  A₂_pos := by linarith [gramMertensConst_nonneg V]
  L_nonneg := gramMertensConst_nonneg V
  mertens_bound := fun w z hw hwz ↦
    (abs_le.mp (abs_gram_delta_le V hV0.ne' w z hw hwz)).imp_right (·.trans (by linarith))

/-- The `γ` field of `Gap212.Sieve.gramDatum V` is `gramGamma V`. -/
@[simp] theorem gramDatum_γ (V : ℕ) (hV0 : 0 < V) (hVsq : Squarefree V) :
    (gramDatum V hV0 hVsq).γ = gramGamma V := rfl

/-- The `V` field of `Gap212.Sieve.gramDatum V` is `V`. -/
@[simp] theorem gramDatum_V (V : ℕ) (hV0 : 0 < V) (hVsq : Squarefree V) :
    (gramDatum V hV0 hVsq).V = V := rfl

/-- The `A₁` field of `Gap212.Sieve.gramDatum V` is `1 / 2`. -/
@[simp] theorem gramDatum_A₁ (V : ℕ) (hV0 : 0 < V) (hVsq : Squarefree V) :
    (gramDatum V hV0 hVsq).A₁ = 1 / 2 := rfl

/-- The `A₃` field of `Gap212.Sieve.gramDatum V` is `2`. -/
@[simp] theorem gramDatum_A₃ (V : ℕ) (hV0 : 0 < V) (hVsq : Squarefree V) :
    (gramDatum V hV0 hVsq).A₃ = 2 := rfl

/-- **`gStar` of the datum is the Gram weight, at a prime not dividing `V`.** This is the identity
`gramLocal_div_sub_eq` read through `PrimeGaps.SieveDatum.gStar_prime` and
`Gap212.Sieve.gramWeight_prime`. -/
theorem gramDatum_gStar_prime (V : ℕ) (hV0 : 0 < V) (hVsq : Squarefree V) {p : ℕ}
    (hp : p.Prime) (hpV : ¬ p ∣ V) : (gramDatum V hV0 hVsq).gStar p = gramWeight p := by
  rw [PrimeGaps.SieveDatum.gStar_prime _ p hp, gramWeight_prime hp, gramDatum_γ,
    gramGamma_prime V hp, gramLocalOff_of_not_dvd hpV]
  exact gramLocal_div_sub_eq hp

/-! ### `μ * φ` and `φ` on the squarefree integers

`Gap212.Sieve.moebiusTotient` is the Dirichlet convolution `μ * φ` written out as a real-valued
sum. To evaluate it, and `φ` itself, on a squarefree argument we present both as multiplicative
`ArithmeticFunction ℝ`s and use `ArithmeticFunction.IsMultiplicative.prod_primeFactors`. -/

/-- Euler's totient as an arithmetic function. -/
def totientAF : ArithmeticFunction ℕ := ⟨fun n ↦ Nat.totient n, Nat.totient_zero⟩

/-- `totientAF n = Nat.totient n`. -/
@[simp] theorem totientAF_apply (n : ℕ) : totientAF n = Nat.totient n := rfl

/-- `totientAF` is multiplicative. -/
theorem isMultiplicative_totientAF : totientAF.IsMultiplicative :=
  ⟨Nat.totient_one, fun h ↦ Nat.totient_mul h⟩

/-- The Dirichlet convolution `μ * φ` as a real-valued arithmetic function. -/
noncomputable def muPhiAF : ArithmeticFunction ℝ :=
  (↑ArithmeticFunction.moebius : ArithmeticFunction ℝ) * (↑totientAF : ArithmeticFunction ℝ)

/-- `muPhiAF n = moebiusTotient n`. -/
theorem muPhiAF_apply (n : ℕ) : muPhiAF n = moebiusTotient n := by
  rw [muPhiAF, ArithmeticFunction.mul_apply, moebiusTotient]
  exact Finset.sum_congr rfl fun x _ ↦ by
    simp [ArithmeticFunction.intCoe_apply, ArithmeticFunction.natCoe_apply, totientAF_apply]

/-- `muPhiAF` is multiplicative. -/
theorem isMultiplicative_muPhiAF : muPhiAF.IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.mul
    (ArithmeticFunction.isMultiplicative_moebius.intCast)
    (isMultiplicative_totientAF.natCast)

/-- `(μ * φ)(n) = ∏_{p ∣ n}(p-2)` on a squarefree `n`. -/
theorem moebiusTotient_of_squarefree {n : ℕ} (hn : Squarefree n) :
    moebiusTotient n = ∏ p ∈ n.primeFactors, ((p : ℝ) - 2) := by
  rw [← muPhiAF_apply, ← isMultiplicative_muPhiAF.prod_primeFactors hn]
  exact Finset.prod_congr rfl fun p hp ↦ by
    rw [muPhiAF_apply, moebiusTotient_prime (Nat.prime_of_mem_primeFactors hp)]

/-- `φ(n) = ∏_{p ∣ n}(p-1)` on a squarefree `n`. -/
theorem totient_of_squarefree {n : ℕ} (hn : Squarefree n) :
    (Nat.totient n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
  have hcoe : ∀ m : ℕ, (↑totientAF : ArithmeticFunction ℝ) m = (Nat.totient m : ℝ) := fun m ↦ by
    simp [ArithmeticFunction.natCoe_apply, totientAF_apply]
  rw [← hcoe, ← (isMultiplicative_totientAF.natCast (R := ℝ)).prod_primeFactors hn]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  rw [hcoe, Nat.totient_prime hp', Nat.cast_sub hp'.one_le, Nat.cast_one]

private theorem moebius_cast_sq_of_squarefree {n : ℕ} (hn : Squarefree n) :
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 = 1 := by
  rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hn, Int.cast_one]

/-- **The Gram weight is a product of local factors on the squarefree integers.** -/
theorem gramWeight_of_squarefree {n : ℕ} (hn : Squarefree n) :
    gramWeight n = ∏ p ∈ n.primeFactors, ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
  rw [gramWeight, moebiusTotient_of_squarefree hn, totient_of_squarefree hn, div_pow,
    moebius_cast_sq_of_squarefree hn,
    mul_one_div, Finset.prod_div_distrib, Finset.prod_pow]

/-- **`h` of the datum is the Gram weight restricted to the integers coprime to `V`.** Off the
squarefree integers both sides vanish; on a squarefree `n` coprime to `V` both are
`∏_{p ∣ n} (p-2)/(p-1)²`; and on an `n` sharing a prime with `V` the datum's weight vanishes by
`PrimeGaps.SieveDatum.h_eq_zero_of_gcd_gt_one`.

This is what makes the datum the right one for the `e`-sum: the tuples the counting
leaves standing have every `[dᵢ,d'ᵢ]` coprime to `W`, so the `e`-sum runs over `e` coprime to `W`
and its weight is exactly this `h` at `V = W`. -/
theorem gramDatum_h (V : ℕ) (hV0 : 0 < V) (hVsq : Squarefree V) (n : ℕ) :
    (gramDatum V hV0 hVsq).h n = if Nat.Coprime n V then gramWeight n else 0 := by
  classical
  by_cases hcop : Nat.Coprime n V
  · rw [if_pos hcop]
    by_cases hsq : Squarefree n
    · rw [PrimeGaps.SieveDatum.h, moebius_cast_sq_of_squarefree hsq, one_mul,
        PrimeGaps.SieveDatum.gStar_squarefree_eq_prod _ n hsq, gramWeight_of_squarefree hsq]
      refine Finset.prod_congr rfl fun p hp ↦ ?_
      have hp' := Nat.prime_of_mem_primeFactors hp
      rw [gramDatum_gStar_prime V hV0 hVsq hp' fun hpV ↦ hp'.ne_one <|
        Nat.eq_one_of_dvd_coprimes hcop (Nat.dvd_of_mem_primeFactors hp) hpV, gramWeight_prime hp']
    · simp [PrimeGaps.SieveDatum.h, gramWeight,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
  · rw [if_neg hcop]
    exact (gramDatum V hV0 hVsq).h_eq_zero_of_gcd_gt_one n
      (lt_of_le_of_ne (Nat.gcd_pos_of_pos_right n hV0) (Ne.symm hcop))

/-! ### Estimate A: the outer `e`-sum

`Gap212.Sieve.sum_pair_moebius_div_totient_lcm_eq_gram` leaves the one-coordinate pair sum as
`∑_{e ≤ B} g(e) Y_F(e) Y_G(e)` with `g = gramWeight`. Against a Lipschitz test function of
`log e / log z` that outer sum is now a direct application of `PrimeGaps.S1_partial_sum_sharp` at
`gramDatum`, whose main term is `𝔖(γ) · log z · ∫₀¹`. -/

/-- The decaying error factor of `PrimeGaps.S1_partial_sum_sharp` is bounded on `[2, ∞)`:
`z^{-1/8} log (2Vz) ≤ 8 · (2V)`, by `Real.log_le_rpow_div` at exponent `1/8`. -/
theorem rpow_mul_log_le {A z : ℝ} (hA : 1 ≤ A) (hz : 2 ≤ z) :
    z ^ (-(1 : ℝ) / 8) * Real.log (A * z) ≤ 8 * A := by
  have hz : (0 : ℝ) < z := by linarith
  have hcancel : z ^ (-(1 : ℝ) / 8) * z ^ ((1 : ℝ) / 8) = 1 := by
    rw [← Real.rpow_add hz]; norm_num
  calc z ^ (-(1 : ℝ) / 8) * Real.log (A * z)
      ≤ z ^ (-(1 : ℝ) / 8) * ((A * z) ^ ((1 : ℝ) / 8) / ((1 : ℝ) / 8)) := by
        gcongr
        exact Real.log_le_rpow_div (by nlinarith) (by norm_num)
    _ = 8 * A ^ ((1 : ℝ) / 8) := by
        rw [Real.mul_rpow (by linarith) hz.le]
        linear_combination 8 * A ^ ((1 : ℝ) / 8) * hcancel
    _ ≤ 8 * A := by grw [Real.rpow_le_self_of_one_le hA (by norm_num)]

/-- **Estimate A: the Gram-weighted partial sum.** For every test function `G` on `[0,1]` bounded
by `M` and `M`-Lipschitz,

  `∑_{0 < e < z, (e,V) = 1} g(e) G(log e / log z) = 𝔖(γ_V) · log z · ∫₀¹ G + O_V(M)`

uniformly in `z ≥ 2`, with `g = Gap212.Sieve.gramWeight`. The error is a *constant* multiple of
`M`, so it is `o(log z)` against the main term; the constant depends on `V` only through `τ(V)`,
`log V` and `PrimeGaps.ellV V`.

This is `PrimeGaps.S1_partial_sum_sharp` at `gramDatum`, with `gramDatum_h` identifying `h` with
the restricted Gram weight and `rpow_mul_log_le` absorbing the `z`-dependence of the error. -/
theorem exists_gram_partial_sum_bound (V : ℕ) (hV0 : 0 < V) (hVsq : Squarefree V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : ℝ → ℝ) (M : ℝ), 0 ≤ M →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |G x| ≤ M) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |G x - G y| ≤ M * |x - y|) →
      ∀ z : ℝ, 2 ≤ z →
        |∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (d : ℝ) < z,
              (if Nat.Coprime d V then gramWeight d else 0) * G (Real.log d / Real.log z) -
            PrimeGaps.singularSeries (gramGamma V) * Real.log z * ∫ x in (0 : ℝ)..1, G x| ≤
          C * M := by
  classical
  obtain ⟨C₁, C₂, hC₁, hC₂, hS⟩ := PrimeGaps.S1_partial_sum_sharp
  set S := gramDatum V hV0 hVsq with hSdef
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA1 : (1 : ℝ) ≤ 2 * (V : ℝ) := by linarith [show (1 : ℝ) ≤ V by exact_mod_cast hV0]
  have hlogA : 0 ≤ Real.log (2 * (S.V : ℝ)) := Real.log_nonneg hA1
  have h𝔖 : 0 < PrimeGaps.singularSeries S.γ := PrimeGaps.singularSeries_pos S
  have hell : 0 ≤ PrimeGaps.ellV S.V := PrimeGaps.ellV_nonneg _
  set a := C₁ S.A₁ S.A₃ with ha
  set b := C₂ S.A₁ S.A₃ with hb
  have hapos : 0 < a := hC₁ _ _
  have hbpos : 0 < b := hC₂ _ _
  set τ : ℝ := (#S.V.divisors : ℝ) with hτ
  have hτnn : 0 ≤ τ := by rw [hτ]; positivity
  set E : ℝ := 8 * (2 * (V : ℝ)) + (8 * Real.log (2 * (V : ℝ)) + 64) / Real.log 2 with hE
  have hEnn : 0 ≤ E := by rw [hE]; positivity
  refine ⟨2 * (2 * a * PrimeGaps.singularSeries S.γ * (1 + PrimeGaps.ellV S.V) + b * τ * E),
    by positivity, fun G M hM hbdd hlip z hz ↦ ?_⟩
  have hrw : ∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (d : ℝ) < z,
        (if Nat.Coprime d V then gramWeight d else 0) * G (Real.log d / Real.log z) =
      ∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (d : ℝ) < z,
        S.h d * G (Real.log d / Real.log z) :=
    Finset.sum_congr rfl fun d _ ↦ by rw [hSdef, gramDatum_h V hV0 hVsq]
  rw [hrw]
  refine (hS S G M hM hbdd hlip z hz).trans ?_
  have hfac : z ^ (-(1 : ℝ) / 8) * Real.log (2 * (S.V : ℝ) * z) +
      (8 * Real.log (2 * (S.V : ℝ)) + 64) / Real.log z ≤ E :=
    add_le_add (rpow_mul_log_le hA1 hz)
      (div_le_div_of_nonneg_left (by linarith) hlog2 (Real.log_le_log (by norm_num) hz))
  calc _ ≤ 2 * M * (2 * a * PrimeGaps.singularSeries S.γ * (1 + PrimeGaps.ellV S.V) +
          b * τ * E) := by gcongr
    _ = _ := by ring

/-- The partial-summation index set at `z = B + 1` is `Finset.Icc 1 B`, which is the index set the
algebra of `Gap212.Sieve.sum_pair_moebius_div_totient_lcm_eq_gram` hands over. -/
theorem filter_range_eq_Icc (B : ℕ) :
    {d ∈ Finset.range ⌈((B : ℝ) + 1)⌉₊ | (0 : ℕ) < d ∧ (d : ℝ) < (B : ℝ) + 1} =
      Finset.Icc 1 B := by
  have hceil : ⌈((B : ℝ) + 1)⌉₊ = B + 1 := by exact_mod_cast Nat.ceil_natCast (B + 1)
  ext d
  simp only [hceil, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  norm_cast
  omega

/-- **Estimate A over the algebra's index set.** `exists_gram_partial_sum_bound` transported to
`z = B + 1`, where the index set is `Finset.Icc 1 B` — the shape in which
`Gap212.Sieve.sum_pair_moebius_div_totient_lcm_eq_gram` produces the outer `e`-sum. -/
theorem exists_gram_partial_sum_bound_Icc (V : ℕ) (hV0 : 0 < V) (hVsq : Squarefree V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : ℝ → ℝ) (M : ℝ), 0 ≤ M →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |G x| ≤ M) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |G x - G y| ≤ M * |x - y|) →
      ∀ B : ℕ, 1 ≤ B →
        |∑ e ∈ Finset.Icc 1 B, (if Nat.Coprime e V then gramWeight e else 0) *
              G (Real.log e / Real.log ((B : ℝ) + 1)) -
            PrimeGaps.singularSeries (gramGamma V) * Real.log ((B : ℝ) + 1) *
              ∫ x in (0 : ℝ)..1, G x| ≤ C * M := by
  obtain ⟨C, hC, hbound⟩ := exists_gram_partial_sum_bound V hV0 hVsq
  refine ⟨C, hC, fun G M hM hbdd hlip B hB ↦ ?_⟩
  rw [← filter_range_eq_Icc B]
  exact hbound G M hM hbdd hlip _ (by norm_cast; omega)

/-! ### The datum at the pre-sieving modulus -/

/-- **The datum at `V = W(x)`.** `Gap212.GPY.W x` is a primorial, hence positive and squarefree, so
the `W`-tricked Gram density is a sieve datum at exactly the pre-sieving modulus. -/
noncomputable def wDatum (x : ℝ) : PrimeGaps.SieveDatum :=
  gramDatum (Gap212.GPY.W x) (primorial_pos _) (squarefree_primorial _)

/-- The `V` field of `Gap212.Sieve.wDatum x` is `Gap212.GPY.W x`. -/
@[simp] theorem wDatum_V (x : ℝ) : (wDatum x).V = Gap212.GPY.W x := rfl

/-- The `γ` field of `Gap212.Sieve.wDatum x` is `gramGamma (Gap212.GPY.W x)`. -/
@[simp] theorem wDatum_γ (x : ℝ) : (wDatum x).γ = gramGamma (Gap212.GPY.W x) := rfl

/-- The datum at `V = W(x)` carries the Gram weight of the integers coprime to `W(x)`. -/
theorem wDatum_h (x : ℝ) (n : ℕ) :
    (wDatum x).h n = if Nat.Coprime n (Gap212.GPY.W x) then gramWeight n else 0 :=
  gramDatum_h _ _ _ n

end Gap212.Sieve

end
