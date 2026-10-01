/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Gap212.Attr
public import Gap212.Routing.Defs.Equidistribution

/-!
# Convolutions of coefficient sequences

A Dirichlet convolution of two coefficient sequences located at `M` and `N` is a coefficient
sequence located at the product scale `M * N`, for a bundle depending only on the original.

The bundle is `ConstantBundle.conv`: `C ↦ C ^ 2`, `k ↦ 2 * k + 1`, `l ↦ 2 * l`, and the support
endpoints squared, `c₋ ↦ c₋ ^ 2`, `c₊ ↦ c₊ ^ 2`.

Two steps. **Support**: if `(α ⋆ β) n ≠ 0` with `n ≥ 1` then some `d ∣ n` has `α d ≠ 0` and
`β (n / d) ≠ 0`, both indices are at least `1`, so `c₋M ≤ d ≤ c₊M` and `c₋N ≤ n/d ≤ c₊N`;
multiplying and using `d * (n / d) = n` gives `c₋²MN ≤ n ≤ c₊²MN`. **Size**: each of the `τ(n)`
terms is bounded by `C τ(d)^k (1 + log d)^l · C τ(n/d)^k (1 + log (n/d))^l`, and `τ(d) ≤ τ(n)`,
`d ≤ n` for `d ∣ n`, so the whole sum is at most `C² τ(n)^(2k+1) (1 + log n)^(2l)`, the extra
factor of `τ(n)` being the number of terms.

## Main definitions

* `Gap212.ConstantBundle.conv`: the bundle the convolution satisfies, a function of the original
  bundle alone.

## Main results

* `Gap212.isCoefficientSequence_and_locatedAtScale_dconv`: both clauses pass to `dconv α β`, at the
  bundle `K.conv` and the scale `M * N`, with no hypothesis beyond the four they are read from.

## Implementation notes

Nothing is asked of `K.coeffConst`, of `M` or of `N`; the lemma is usually stated at `M ≥ 1`
and `N ≥ 1`. Non-negativity of the coefficient constant comes from the coefficient bound itself,
read at `n = 1`, where `τ(1) ^ k = 1` and `(1 + log 1) ^ l = 1`, so that the bound reads
`‖α 1‖ ≤ C`. Positivity of the two scales comes from the support clause, in the only place it is
used: the half begins by producing a divisor `d` of `n` with `1 ≤ d ≤ c₊ * M`, whence `0 < c₊ * M`
and so `0 < M`, and likewise `0 < N` from `n / d`.

Dropping the scale hypotheses does not make the conclusion vacuous at a non-positive scale either,
since the hypotheses are then vacuous in the same degree: a sequence located at `M ≤ 0` vanishes at
every `n ≥ 1`, such an `n` needing `n ≤ c₊ * M ≤ 0`.
-/

@[expose] public section

namespace Gap212

open Real Finset

namespace ConstantBundle

/-- **The convolution bundle**: the coefficient constant squared, the divisor exponent doubled and
raised by one, the logarithmic exponent doubled, and the support endpoints squared. -/
noncomputable def conv (K : ConstantBundle) : ConstantBundle where
  coeffConst := K.coeffConst ^ 2
  coeffFstPow := 2 * K.coeffFstPow + 1
  coeffSndPow := 2 * K.coeffSndPow
  scaleLo := K.scaleLo ^ 2
  scaleHi := K.scaleHi ^ 2
  asympLo := K.asympLo
  asympHi := K.asympHi
  smoothConst := K.smoothConst
  smoothPow := K.smoothPow
  siegelWalfiszConst := K.siegelWalfiszConst
  siegelWalfiszPow := K.siegelWalfiszPow
  scaleLo_pos := pow_pos K.scaleLo_pos 2
  scaleLo_lt_scaleHi := pow_lt_pow_left₀ K.scaleLo_lt_scaleHi K.scaleLo_pos.le two_ne_zero
  asympLo_pos := K.asympLo_pos
  asympLo_lt_asympHi := K.asympLo_lt_asympHi

end ConstantBundle

/-- The constant of a coefficient bound is non-negative: the bound read at `n = 1`, where
`τ(1) ^ k = 1` and `(1 + log 1) ^ l = 1`, says `‖α 1‖ ≤ C`. -/
private theorem const_nonneg {C : ℝ} {k l : ℕ} {α : ℕ → ℂ}
    (hα : IsCoefficientSequence C k l α) : 0 ≤ C := by
  simpa using (norm_nonneg (α 1)).trans (hα 1 le_rfl)

/-- The number of divisors is monotone under divisibility. -/
private theorem card_divisors_le_of_dvd {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    (d.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) :=
  Nat.cast_le.2 (Finset.card_le_card (Nat.divisors_subset_of_dvd hn hd))

/-- **A convolution is a coefficient sequence at the product scale.**

`α ⋆ β` is a `K.conv`-coefficient sequence, and is `K.conv`-located at `M * N` whenever `α` is
`K`-located at `M` and `β` at `N`. No positivity is asked of the coefficient constant, of `M` or of
`N`: each of the three is already carried by the four clauses. -/
@[gap212 "lem_dconv_coefficient_sequence"]
theorem isCoefficientSequence_and_locatedAtScale_dconv {K : ConstantBundle} {α β : ℕ → ℂ}
    {M N : ℝ} (hα : K.IsCoefficientSequence α) (hβ : K.IsCoefficientSequence β)
    (hαloc : K.LocatedAtScale α M) (hβloc : K.LocatedAtScale β N) :
    K.conv.IsCoefficientSequence (dconv α β) ∧
      K.conv.LocatedAtScale (dconv α β) (M * N) := by
  have hC0 : (0 : ℝ) ≤ K.coeffConst := const_nonneg hα
  refine ⟨fun n hn ↦ ?_, fun n hn hne ↦ ?_⟩
  · -- size: bound each term of the convolution
    have hn0 : n ≠ 0 := by omega
    have hterm : ∀ d ∈ n.divisors, ‖α d * β (n / d)‖ ≤ (K.coeffConst *
        (n.divisors.card : ℝ) ^ K.coeffFstPow * (1 + log n) ^ K.coeffSndPow) ^ 2 := by
      intro d hd
      have hdvd := Nat.dvd_of_mem_divisors hd
      have hd0 := Nat.pos_of_mem_divisors hd
      have hdn : d ≤ n := Nat.le_of_dvd (by omega) hdvd
      have hq0 : 0 < n / d := Nat.div_pos hdn hd0
      have hqn : n / d ≤ n := Nat.div_le_self _ _
      have hτd := card_divisors_le_of_dvd hn0 hdvd
      have hτq := card_divisors_le_of_dvd hn0 (Nat.div_dvd_of_dvd hdvd)
      rw [norm_mul, sq]
      refine (mul_le_mul (hα d hd0) (hβ (n / d) hq0) (norm_nonneg _) (by positivity)).trans ?_
      gcongr
    calc ‖dconv α β n‖ ≤ ∑ d ∈ n.divisors, ‖α d * β (n / d)‖ := norm_sum_le _ _
      _ ≤ ∑ _d ∈ n.divisors, (K.coeffConst * (n.divisors.card : ℝ) ^ K.coeffFstPow
            * (1 + log n) ^ K.coeffSndPow) ^ 2 := Finset.sum_le_sum hterm
      _ = K.conv.coeffConst * (n.divisors.card : ℝ) ^ K.conv.coeffFstPow
            * (1 + log n) ^ K.conv.coeffSndPow := by
          rw [Finset.sum_const, nsmul_eq_mul]
          change _ = K.coeffConst ^ 2 * (n.divisors.card : ℝ) ^ (2 * K.coeffFstPow + 1)
            * (1 + log n) ^ (2 * K.coeffSndPow)
          ring
  · -- support: some divisor contributes, and its two indices lie in the two windows
    obtain ⟨d, hd, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hq1 : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (Nat.pos_of_mem_divisors hd)
    obtain ⟨hαlo, hαhi⟩ := hαloc d (Nat.pos_of_mem_divisors hd) (left_ne_zero_of_mul hne')
    obtain ⟨hβlo, hβhi⟩ := hβloc (n / d) hq1 (right_ne_zero_of_mul hne')
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hq1' : (1 : ℝ) ≤ (n / d : ℕ) := by exact_mod_cast hq1
    have hM : 0 < M := by nlinarith [K.scaleHi_pos]
    have hN : 0 < N := by nlinarith [K.scaleHi_pos]
    have hdq : (d : ℝ) * (n / d : ℕ) = n := by rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
    change K.scaleLo ^ 2 * (M * N) ≤ n ∧ n ≤ K.scaleHi ^ 2 * (M * N)
    have := K.scaleLo_pos
    have := K.scaleHi_pos
    rw [← hdq]
    constructor
    · calc K.scaleLo ^ 2 * (M * N) = (K.scaleLo * M) * (K.scaleLo * N) := by ring
        _ ≤ _ := mul_le_mul hαlo hβlo (by positivity) (by positivity)
    · calc _ ≤ (K.scaleHi * M) * (K.scaleHi * N) :=
            mul_le_mul hαhi hβhi (by positivity) (by positivity)
        _ = K.scaleHi ^ 2 * (M * N) := by ring

end Gap212
