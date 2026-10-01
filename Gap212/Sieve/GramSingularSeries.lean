/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.GramDatum
public import Gap212.Sieve.MoebiusTotientAsymptotic

/-!
# The constant of Estimate A, identified

`Gap212.Sieve.exists_gram_partial_sum_bound` — Estimate A — evaluates the Gram-weighted partial sum
against the main term `PrimeGaps.singularSeries (gramGamma V) · log z · ∫₀¹ G`. The normalisation
used for the two divisor-sum asymptotics is instead `W^{k-1}/(φ(W)^k(\log x)^{k-1})`, that is
`φ(W)^{-1}` times `B_x^{-(k-1)}` with `B_x = (φ(W)/W)\log x`. So the two can only be compared once
`𝔖(γ_V)` is written in terms of `φ(V)/V`, and that is what is proved here.

## The identity

The local factor of `PrimeGaps.singularSeries` at a prime `p` is `(1 - 1/p)/(1 - γ(p)/p)`. For the
`W`-tricked Gram density `γ_V` of `Gap212.Sieve.GramDatum`:

* at `p ∣ V` the density is `0`, so the factor is `1 - 1/p`;
* at `p ∤ V` the density is `p(p-2)/(p²-p-1)`, so `1 - γ(p)/p = (p-1)²/(p²-p-1)` and the factor is
  `(p²-p-1)/(p(p-1)) = 1 - 1/(p(p-1))`.

Splitting the Euler product at `p ∣ V` therefore gives

  `𝔖(γ_V) = (φ(V)/V) · ∏_{p ∤ V}(1 - 1/(p(p-1)))`,

which is `Gap212.Sieve.singularSeries_gramGamma_eq`. The first factor is `φ(V)/V`; the second is
absolutely convergent — its logarithm is dominated by `∑_p 2/p²` — and at
`V = 1` it is **Artin's constant** `∏_p(1 - 1/(p(p-1))) = 0.3739558…`.

## Positivity

`Gap212.Sieve.tprod_gram_corr_pos` records that the correction product is strictly positive, read
off `PrimeGaps.singularSeries_pos` through the identity.

## Main results

* `Gap212.Sieve.gramCorrFactor`: the local correction `1 - 1/(p(p-1))` off `V`, and `1` on it.
* `Gap212.Sieve.singularSeries_gramGamma_eq`: `𝔖(γ_V) = (φ(V)/V) · ∏'_p gramCorrFactor V p`.
* `Gap212.Sieve.tprod_gram_corr_pos`: the correction product is strictly positive.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset

/-! ### The local factors -/

/-- The local correction factor of `Gap212.Sieve.singularSeries_gramGamma_eq`: `1 - 1/(p(p-1))` at
a prime not dividing `V`, and `1` elsewhere. At `V = 1` its infinite product is Artin's
constant. -/
noncomputable def gramCorrFactor (V p : ℕ) : ℝ :=
  if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) * ((p : ℝ) - 1)) else 1

/-- The local factor of `Gap212.Sieve.gramLocal` off `V`:
`(1 - 1/p)/(1 - γ(p)/p) = 1 - 1/(p(p-1))`.

At `p = 2` both sides are `1/2`, the density vanishing there. -/
theorem gram_local_factor_eq {p : ℕ} (hp : p.Prime) :
    (1 - 1 / (p : ℝ)) / (1 - gramLocal p / (p : ℝ)) = 1 - 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hD : (0 : ℝ) < (p : ℝ) ^ 2 - p - 1 := gram_denom_pos hp.two_le
  have hp0' : (p : ℝ) ≠ 0 := hp0.ne'
  have hp1' : (p : ℝ) - 1 ≠ 0 := hp1.ne'
  have hcancel : (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) ^ 2 - p - 1) / (p : ℝ)
      = ((p : ℝ) - 2) / ((p : ℝ) ^ 2 - p - 1) := by
    rw [mul_div_assoc, mul_div_cancel_left₀ _ hp0']
  have hden : 1 - gramLocal p / (p : ℝ) = ((p : ℝ) - 1) ^ 2 / ((p : ℝ) ^ 2 - p - 1) := by
    rw [gramLocal, hcancel, eq_div_iff hD.ne', sub_mul, div_mul_cancel₀ _ hD.ne']
    ring
  rw [hden, div_div_eq_mul_div]
  field_simp

/-- **The Euler factor of `𝔖(γ_V)` splits.** At every `p`, the local factor of
`PrimeGaps.singularSeries (gramGamma V)` is the product of `1 - 1/p` over the primes dividing `V`
with `Gap212.Sieve.gramCorrFactor V p`. -/
theorem singularSeries_factor_eq (V p : ℕ) :
    (if p.Prime then (1 - 1 / (p : ℝ)) / (1 - gramGamma V p / (p : ℝ)) else 1)
      = (if p.Prime ∧ p ∣ V then 1 - 1 / (p : ℝ) else 1) * gramCorrFactor V p := by
  unfold gramCorrFactor
  by_cases hp : p.Prime
  · rw [if_pos hp, gramGamma_prime V hp]
    by_cases hpV : p ∣ V
    · rw [gramLocalOff_of_dvd hpV, if_pos ⟨hp, hpV⟩, if_neg (by tauto)]
      simp
    · rw [gramLocalOff_of_not_dvd hpV, if_neg (by tauto), if_pos ⟨hp, hpV⟩, one_mul]
      exact gram_local_factor_eq hp
  · rw [if_neg hp, if_neg (by tauto), if_neg (by tauto)]
    norm_num

/-! ### Multipliability -/

/-- The factors over the primes dividing `V` have finite multiplicative support. -/
theorem multipliable_gram_head {V : ℕ} (hV : V ≠ 0) :
    Multipliable (fun p : ℕ ↦ if p.Prime ∧ p ∣ V then 1 - 1 / (p : ℝ) else 1) := by
  refine multipliable_of_ne_finset_one (s := V.primeFactors) fun p hp ↦ ?_
  rw [if_neg]
  rintro ⟨hpp, hpV⟩
  exact hp (Nat.mem_primeFactors.mpr ⟨hpp, hpV, hV⟩)

/-- The tail `∑_p 1/(p(p-1))` is summable: the terms are at most `2/p²`. -/
theorem summable_gram_corr (V : ℕ) :
    Summable (fun p : ℕ ↦ if p.Prime ∧ ¬ p ∣ V then 1 / ((p : ℝ) * ((p : ℝ) - 1)) else 0) := by
  have hb : Summable (fun p : ℕ ↦ 2 / (p : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using (Real.summable_one_div_nat_pow.2 one_lt_two).mul_left (2 : ℝ)
  refine Summable.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_) hb
  · split_ifs with h
    · have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.1.two_le
      have : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
      positivity
    · norm_num
  · split_ifs with h
    · have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.1.two_le
      have hA : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
      have hB : (0 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
      rw [div_le_div_iff₀ hA hB]
      nlinarith
    · positivity

/-- The correction product converges. -/
theorem multipliable_gramCorrFactor (V : ℕ) : Multipliable (gramCorrFactor V) := by
  have hs : Summable
      (fun p : ℕ ↦ -(if p.Prime ∧ ¬ p ∣ V then 1 / ((p : ℝ) * ((p : ℝ) - 1)) else 0)) :=
    (summable_gram_corr V).neg
  have h := Real.multipliable_one_add_of_summable hs
  refine h.congr fun p ↦ ?_
  unfold gramCorrFactor
  split_ifs <;> ring

/-! ### The identity -/

/-- For `V ≠ 0`, the product of `1 - 1/p` over the primes `p ∣ V` is `φ(V)/V`. -/
theorem tprod_gram_head {V : ℕ} (hV : V ≠ 0) :
    ∏' p : ℕ, (if p.Prime ∧ p ∣ V then 1 - 1 / (p : ℝ) else 1) = (V.totient : ℝ) / (V : ℝ) := by
  have hz : ∀ p ∉ V.primeFactors, (if p.Prime ∧ p ∣ V then 1 - 1 / (p : ℝ) else 1) = 1 := by
    intro p hp
    rw [if_neg]
    rintro ⟨hpp, hpV⟩
    exact hp (Nat.mem_primeFactors.mpr ⟨hpp, hpV, hV⟩)
  rw [tprod_eq_prod hz, totient_div_eq_prod_one_sub_inv hV]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  rw [if_pos ⟨Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩]

/-- **Estimate A's constant, identified.** For `V ≠ 0`,

  `𝔖(γ_V) = (φ(V)/V) · ∏_{p ∤ V}(1 - 1/(p(p-1)))`.

The first factor is `φ(V)/V`, so this is the step that makes Estimate A's main term
comparable with the normalisation `W^{k-1}/(φ(W)^k(\log x)^{k-1})`; the second is absolutely
convergent, and is Artin's constant at `V = 1`. -/
theorem singularSeries_gramGamma_eq {V : ℕ} (hV : V ≠ 0) :
    PrimeGaps.singularSeries (gramGamma V)
      = (V.totient : ℝ) / (V : ℝ) * ∏' p : ℕ, gramCorrFactor V p := by
  rw [PrimeGaps.singularSeries,
    tprod_congr (singularSeries_factor_eq V),
    Multipliable.tprod_mul (multipliable_gram_head hV) (multipliable_gramCorrFactor V),
    tprod_gram_head hV]

/-- **The correction product is strictly positive.** This is read
off `PrimeGaps.singularSeries_pos` through `Gap212.Sieve.singularSeries_gramGamma_eq`: the datum
`Gap212.Sieve.gramDatum` exists, so its singular series is positive, and `φ(V)/V` is positive. -/
theorem tprod_gram_corr_pos (V : ℕ) (hV0 : 0 < V) (hVsq : Squarefree V) :
    0 < ∏' p : ℕ, gramCorrFactor V p := by
  have hS : 0 < PrimeGaps.singularSeries (gramGamma V) :=
    PrimeGaps.singularSeries_pos (gramDatum V hV0 hVsq)
  rw [singularSeries_gramGamma_eq hV0.ne'] at hS
  have hφ : (0 : ℝ) < (V.totient : ℝ) / (V : ℝ) :=
    div_pos (by exact_mod_cast Nat.totient_pos.2 hV0) (by exact_mod_cast hV0)
  nlinarith

/-- The identity at the pre-sieving modulus `V = W(x)`, where `Gap212.Sieve.wDatum` lives. -/
theorem singularSeries_wDatum_eq (x : ℝ) :
    PrimeGaps.singularSeries (wDatum x).γ
      = ((Gap212.GPY.W x).totient : ℝ) / ((Gap212.GPY.W x) : ℝ) *
          ∏' p : ℕ, gramCorrFactor (Gap212.GPY.W x) p := by
  rw [wDatum_γ]
  exact singularSeries_gramGamma_eq (primorial_pos _).ne'

end Gap212.Sieve

end
