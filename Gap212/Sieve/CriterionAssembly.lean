/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Asymptotics
public import Gap212.Sieve.SieveWeights
public import Gap212.Sieve.PreSieved
public import Gap212.Auxiliary.Certificate
public meta import Gap212.Attr

/-!
# The GPY sieve, assembled from the denominator and numerator asymptotics

`Gap212.Sieve.GPYSieve` is declared in `Gap212.Sieve.Criterion`. This module proves it from the
denominator and numerator asymptotics of `Gap212.Sieve.Asymptotics`, together with
`Gap212.Sieve.sieveWeights` and elementary steps.

## The argument

Given an admissible tuple `h : Fin (m+1) → ℕ`, `Gap212.Sieve.sieveWeights` turns the continuum
certificate into finite tensor data `(L, c, F)` supported in the retreat region, together with
index sets `𝓛, 𝓤` and the strict inequality `0 < 𝓘 < ∑ᵢ 𝓙ᵢ` between the discrete forms *of that
datum*. Because `Gap212.Sieve.gramInner`, `gramInnerSkip` and `gramBdry` read the Gram data off `F`
itself, the same `(L, c, F)` is what `Gap212.Sieve.NuDenominator` and
`Gap212.Sieve.NumeratorAsymptotic` are evaluated at, and the three compose.

With `η = (∑ᵢ𝓙ᵢ - 𝓘)/4` the denominator is at most `(𝓘 + η)` times the scale and the numerator at
least `(∑ᵢ𝓙ᵢ - η)` times it; `η` is a quarter of the gap, so the numerator wins by half of it, and
`Gap212.Sieve.scale_pos` is the only property of the scale used. `Gap212.GPY.pos_of_ratio_gt_one`
then makes the GPY sum positive, `Gap212.GPY.nu_nonneg` supplies the sign of the weight,
`Gap212.GPY.two_primes_of_pos` produces an `n` in the block with `∑ᵢ ρ(n + hᵢ) > 1`, and
`Gap212.Sieve.two_le_card_prime_of_one_lt_sum` reads that off as two prime translates. The `n`
produced lies in `Gap212.dyadic x` with `x` as large as we please, so
`Gap212.Auxiliary.infinitely_many_of_unbounded` gives the infinitude `Gap212.DHL` asks for.

## The shape of the hypotheses

* `NumeratorAsymptotic` carries the equidistribution hypothesis
  `Gap212.HasEquidistributionOverQstarFamily p (fun n x ↦ ((ρ n x : ℝ) : ℂ))`, which
  `Gap212.Sieve.dhl_of_tensorData` takes as `hequi` and forwards.
* Both asymptotics quantify the residue `b` inside their `∃ X` —
  `∀ η > 0, ∃ X, ∀ x > X, ∀ b, IsPreSieved b (W x) h → …` — so the residue that
  `Gap212.Sieve.exists_isPreSieved` produces after `x` is fixed can be fed to them and to
  `Gap212.GPY.two_primes_of_pos`.
* `Gap212.Sieve.gpySieve_of_obligations` takes the instances `NuDenominator 45` and
  `NumeratorAsymptotic 44` only, since `sieveWeights` produces its datum at `m = 44`;
  `Gap212.Sieve.dhl_of_tensorData` is stated at a general `p` and `m`.

## Main results

* `Gap212.Sieve.two_le_card_prime_of_one_lt_sum`: a minorant sum exceeding `1` means two prime
  translates.
* `Gap212.Sieve.dhl_of_tensorData`: `DHL[k,2]` from one tensor datum and the two asymptotics, at a
  general `p` and `m`.
* `Gap212.Sieve.gpySieve_of_obligations`: `GPYSieve` from `NuDenominator 45` and
  `NumeratorAsymptotic 44`, the datum supplied by `Gap212.Sieve.sieveWeights`.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset Real Gap212.Defs Gap212.GPY

/-- **Two prime translates, from the minorant sum exceeding one.** `ρ` is bounded by the prime
indicator on the block and vanishes off it, so `∑ᵢ ρ(n + hᵢ; x)` is at most the number of prime
translates; a sum above `1` therefore forces at least two.

The off-block case is the `support` field, not the `minorant` field: `n ∈ dyadic x` does not put
`n + hᵢ` in the block, and there is nothing to prove there because `ρ` is zero. -/
theorem two_le_card_prime_of_one_lt_sum {k : ℕ} {p : SupportParams} {ρ : ℕ → ℝ → ℝ} {β : ℝ}
    (hρ : RhoHypotheses p ρ β) {x : ℝ} (hx : 1 < x) {n : ℕ} {h : Fin k → ℕ}
    (hsum : 1 < ∑ i : Fin k, ρ (n + h i) x) :
    2 ≤ #{i : Fin k | (n + h i).Prime} := by
  suffices (1 : ℝ) < #{i : Fin k | (n + h i).Prime} by exact_mod_cast this
  rw [← Finset.sum_boole]
  refine hsum.trans_le (Finset.sum_le_sum fun i _ ↦ ?_)
  by_cases hmem : n + h i ∈ dyadic x
  · exact (hρ.minorant x hx _ hmem).2
  · rw [hρ.support x _ hmem]
    split_ifs <;> norm_num

/-- **Positivity produces two primes.** If `ν ≥ 0`, `ρ` satisfies the minorant hypotheses, and the
GPY sum is positive, then some `n` in the block has at least two prime translates.

`Gap212.GPY.two_primes_of_pos` gives `1 < ∑ᵢ ρ(n + hᵢ)` for some `n` in the block, and
`Gap212.Sieve.two_le_card_prime_of_one_lt_sum`, using the minorant clause of `RhoHypotheses`, turns
this into two prime translates. -/
@[gap212 "lem_positivity_two_primes"]
theorem exists_two_primes_of_pos {k : ℕ} {p : SupportParams} {ρ : ℕ → ℝ → ℝ} {β : ℝ}
    (hρ : RhoHypotheses p ρ β)
    {ν : ℕ → ℝ} {h : Fin k → ℕ} {b : ℕ} {x : ℝ} (hx : 1 < x) (hν : ∀ n, 0 ≤ ν n)
    (hpos : 0 < N ρ ν h b x) :
    ∃ n ∈ dyadic x, 2 ≤ #{i : Fin k | (n + h i).Prime} := by
  obtain ⟨n, hn, hsum⟩ := two_primes_of_pos hν hpos
  exact ⟨n, hn, two_le_card_prime_of_one_lt_sum hρ hx hsum⟩

/-- **The ratio exceeds one.** For all sufficiently large `x` and every pre-sieved residue at that
`x`, the weighted count of prime translates strictly exceeds the total weight,
`∑_{n ≡ b (W)} ν(n) < ∑_{i ≤ k} ∑_{n ≡ b (W)} ν(n) ρ(n + hᵢ; x)`.

`NuDenominator` gives `Sₓ/𝓒ₓ → 𝓘` and `NumeratorAsymptotic` gives `liminf Pₓ/𝓒ₓ ≥ ∑ᵢ𝓙ᵢ`; with
`η = (∑ᵢ𝓙ᵢ - 𝓘)/4 > 0` the two bands `Sₓ/𝓒ₓ < 𝓘 + η` and `Pₓ/𝓒ₓ > ∑ᵢ𝓙ᵢ - η` are separated because
`𝓘 < ∑ᵢ𝓙ᵢ`.

The residue `b` is quantified inside the threshold and guarded by `Gap212.Defs.IsPreSieved`, as in
the two asymptotics: the pre-sieved class produced by `Gap212.Sieve.exists_isPreSieved` depends on
`x`. `ν` is the tensor sieve weight of a tensor datum and the tuple is strictly increasing, as both
asymptotics require; `hUc` and `hmarg` are the low/high split. The statement holds at an arbitrary
`m`, and only `𝓘 < ∑ᵢ𝓙ᵢ` is assumed, not `0 < 𝓘`.

Compare `Gap212.Auxiliary.ratio_exceeds_one`, the real-number step `1 < num / den → den < num`. -/
@[gap212 "lem_ratio_exceeds_one"]
theorem ratio_exceeds_one (p : SupportParams) (m : ℕ) (hden : NuDenominator (m + 1))
    (hnum : NumeratorAsymptotic m) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) {j : Fin p.n}
    (hA : p.ε < p.A j.succ)
    (D : TensorDatum p (m + 1) j ε₀) {𝓛 𝓤 : Fin (m + 1) → Finset (Fin D.L)}
    (hUc : ∀ i, 𝓤 i = (𝓛 i)ᶜ)
    (hmarg : ∀ i : Fin (m + 1), ∀ l ∈ 𝓛 i, ∀ t : Fin m → ℝ, (∀ s, 0 ≤ t s) →
      (∏ s, D.f l (i.succAbove s) (t s)) ≠ 0 → t ∈ marginalRegion p m j ε₀)
    {hh : Fin (m + 1) → ℕ} (hmono : StrictMono hh)
    (hIJ : formI D.c (gramInner D.f) <
      ∑ i : Fin (m + 1), formJMarginal D.c (gramBdry D.f i) (gramInnerSkip D.f i) (𝓛 i) (𝓤 i))
    {ρ : ℕ → ℝ → ℝ} {β : ℝ} (hρ : RhoHypotheses p ρ β)
    (hequi : HasEquidistributionOverQstarFamily p (fun n x ↦ ((ρ n x : ℝ) : ℂ))) :
    ∃ X : ℝ, ∀ x > X, ∀ b : ℕ, Defs.IsPreSieved b (W x) hh →
      (∑ n ∈ dyadic x with n % W x = b % W x, nu D.L D.c D.f hh x n) <
        ∑ i : Fin (m + 1), ∑ n ∈ dyadic x with n % W x = b % W x,
          nu D.L D.c D.f hh x n * ρ (n + hh i) x := by
  have hηpos : 0 < (∑ i : Fin (m + 1),
      formJMarginal D.c (gramBdry D.f i) (gramInnerSkip D.f i) (𝓛 i) (𝓤 i) -
        formI D.c (gramInner D.f)) / 4 := by linarith
  obtain ⟨X₁, hX₁⟩ := hden p ε₀ hε₀ hε₀' j D hh hmono _ hηpos
  obtain ⟨X₂, hX₂⟩ :=
    hnum p ε₀ hε₀ hε₀' j hA D ρ β hρ hequi hh hmono 𝓛 𝓤 hUc hmarg _ hηpos
  refine ⟨max X₁ (max X₂ 1), fun x hx b hb ↦ ?_⟩
  obtain ⟨hxX₁, hxX₂, hx1⟩ : X₁ < x ∧ X₂ < x ∧ 1 < x := by simpa using hx
  linarith [(abs_le.mp (hX₁ x hxX₁ b hb)).2, hX₂ x hxX₂ b hb,
    mul_pos hηpos (scale_pos hx1 (primorial_pos _) : 0 < scale (m + 1) x)]

/-- **`DHL[k,2]` from one tensor datum and the two asymptotics.** The argument of the GPY sieve,
stated at the data `Gap212.Sieve.sieveWeights` produces rather than at the certificate, and at a
general `p` and `m`. `Gap212.Sieve.gpySieve_of_obligations` is this at `p_⋆` and `m = 44`.

Only the strict inequality `𝓘 < ∑ᵢ 𝓙ᵢ` is assumed, not `0 < 𝓘`: see
`Gap212.GPY.pos_of_ratio_gt_one`. -/
theorem dhl_of_tensorData (p : SupportParams) (m : ℕ) (hden : NuDenominator (m + 1))
    (hnum : NumeratorAsymptotic m) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) {j : Fin p.n}
    (hA : p.ε < p.A j.succ)
    (D : TensorDatum p (m + 1) j ε₀) {𝓛 𝓤 : Fin (m + 1) → Finset (Fin D.L)}
    (hUc : ∀ i, 𝓤 i = (𝓛 i)ᶜ)
    (hmarg : ∀ i : Fin (m + 1), ∀ l ∈ 𝓛 i, ∀ t : Fin m → ℝ, (∀ s, 0 ≤ t s) →
      (∏ s, D.f l (i.succAbove s) (t s)) ≠ 0 → t ∈ marginalRegion p m j ε₀)
    (hIJ : formI D.c (gramInner D.f) <
      ∑ i : Fin (m + 1), formJMarginal D.c (gramBdry D.f i) (gramInnerSkip D.f i) (𝓛 i) (𝓤 i))
    {ρ : ℕ → ℝ → ℝ} {β : ℝ} (hρ : RhoHypotheses p ρ β)
    (hequi : HasEquidistributionOverQstarFamily p (fun n x ↦ ((ρ n x : ℝ) : ℂ))) :
    DHL (m + 1) 2 := by
  intro hh hmono hadm
  refine Gap212.Auxiliary.infinitely_many_of_unbounded fun M ↦ ?_
  -- The central comparison is `Gap212.Sieve.ratio_exceeds_one`.
  -- `hmono` is `DHL`'s own binder, the strict monotonicity the denominator asymptotic asks for.
  obtain ⟨X, hX⟩ := ratio_exceeds_one p m hden hnum hε₀ hε₀' hA D (𝓛 := 𝓛) (𝓤 := 𝓤) hUc hmarg
    hmono hIJ hρ hequi
  obtain ⟨x, hx1, hxM, hxX⟩ : ∃ x : ℝ, 1 < x ∧ (M : ℝ) < x ∧ x > X :=
    ⟨max X M + 2, by linarith [le_max_right X (M : ℝ), M.cast_nonneg (α := ℝ)],
      by linarith [le_max_right X (M : ℝ)], by linarith [le_max_left X (M : ℝ)]⟩
  -- `b` is bound inside the threshold, so the pre-sieved class is chosen at this `x`.
  obtain ⟨b, hb⟩ := exists_isPreSieved hh x hadm
  have hkey : (∑ n ∈ dyadic x with n % W x = b % W x, nu D.L D.c D.f hh x n) <
      ∑ n ∈ dyadic x with n % W x = b % W x,
        nu D.L D.c D.f hh x n * ∑ i : Fin (m + 1), ρ (n + hh i) x := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact hX x hxX b hb
  obtain ⟨n, hnmem, hn2⟩ :=
    exists_two_primes_of_pos (ν := fun n ↦ nu D.L D.c D.f hh x n) (ρ := ρ) (h := hh) (b := b) hρ
      hx1 (fun n ↦ nu_nonneg D.L D.c D.f hh x n) (pos_of_ratio_gt_one hkey)
  exact ⟨n, hn2, (Nat.lt_ceil.2 hxM).le.trans (Finset.mem_Icc.1 hnmem).1⟩

/-- **The GPY sieve from the two asymptotics.** `Gap212.Sieve.GPYSieve`, proved from
`Gap212.Sieve.NuDenominator 45` and `Gap212.Sieve.NumeratorAsymptotic 44`, the tensor data coming
from `Gap212.Sieve.sieveWeights` (a datum at `m = 44`, i.e. `k = 45`). Both hypotheses are
theorems, `Gap212.Sieve.nuDenominator_45` and `Gap212.Sieve.numeratorAsymptotic_44`. -/
theorem gpySieve_of_obligations (hden : NuDenominator 45)
    (hnum : NumeratorAsymptotic 44) :
    GPYSieve := by
  intro ρ β hρ hequi hcert
  obtain ⟨ε₀, hε₀, hε₀', D, 𝓛, 𝓤, hUc, hmarg, -, -, hIJ⟩ := sieveWeights hcert
  exact dhl_of_tensorData gap212Params 44 hden hnum hε₀ hε₀'
    (by simp only [gap212Params]; norm_num) D (𝓛 := 𝓛) (𝓤 := 𝓤) hUc hmarg hIJ
    hρ hequi


end Gap212.Sieve
