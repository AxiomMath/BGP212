/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Harman.Challenge
public import Gap212.Sieve.DyadicPNT

/-!
# The sieve criterion in the form `Gap212.SieveCriterion`

`Gap212.Sieve.dhl_of_gpySieve` derives `DHL[45, 2]` from `Gap212.Sieve.GPYSieve`, given the
equidistribution hypothesis in the form `Gap212.HasEquidistributionOverQstarFamily`. This module
derives `Gap212.SieveCriterion`, whose equidistribution antecedent is
`Gap212.HasEquidistributionOverQstar` for `x ≥ 3`, from `GPYSieve` alone.

## The antecedent transfer

The two equidistribution hypotheses fix the constant after `ε₀` and `A` and before `x` and the
residue class, and differ in two respects:

* `Gap212.SieveCriterion` quantifies over `x ≥ 3`, the family form over `x > 1`;
* `Gap212.SieveCriterion` asks for `∃ C`, the family form for `∃ c > 0`.

The summands are the same real number:
`Gap212.HasEquidistributionOverQstar` unfolds to a sum of `‖Gap212.sumError (primeInterval x) q a‖`
over the squarefree moduli of `Gap212.Qstar`, and `Gap212.sumError_primeInterval_eq_sumErrorDyadic`
identifies that with `‖Gap212.sumErrorDyadic x primeIndicator q a‖`, which is precisely the
discrepancy `Gap212.HasEquidistributionOverQstarFamily` inlines at `primeIndicatorFamily` — the two
prime indicators being the same function, one of them carrying an unused scale argument. The index
sets agree by `Finset.filter_filter`.

## Why the bounded range is free

On `1 < x < 3` nothing analytic happens. The left-hand side is bounded by an absolute constant:
`⌊x⌋₊ ≤ 2` leaves at most two moduli, the block `Gap212.dyadic x = Icc ⌈x⌉₊ ⌊2x⌋₊` has at most four
elements, `‖1_ℙ n‖ ≤ 1` and `1 / φ q ≤ 1`, so each discrepancy is at most `8` and the whole sum at
most `16`. The right-hand side, on the other hand, is bounded *below*: `x ≥ 1` and
`(log x)^A ≤ (log 3)^A`, so `x / (log x)^A ≥ 1 / (log 3)^A`. Taking `c` to be
`max C (16 (log 3)^A)` therefore covers `(1, 3)` as well as `[3, ∞)`, and is positive.

`Gap212.hasEquidistribution_of_forall_ge` absorbs a *different* bounded range — `[3, x₀]`, against
a coefficient-sequence majorant and a modulus range `Gap212.moduliRange` — so it does not apply
here; below `3` the trivial majorant is not needed, three bounded cardinalities are enough.

## Main results

* `Gap212.hasEquidistributionOverQstarFamily_of_forall_ge_three`: the antecedent transfer.
* `Gap212.sieveCriterion_of_gpySieve_challengeShape`: `Gap212.Sieve.GPYSieve` alone gives
  `Gap212.SieveCriterion`.
-/

@[expose] public section

namespace Gap212

open Finset Real

/-! ## The prime indicator is bounded by `1` -/

/-- `‖1_ℙ n‖ ≤ 1`: the indicator takes the values `1` and `0`. -/
private theorem norm_primeIndicator_le (n : ℕ) : ‖primeIndicator n‖ ≤ 1 := by
  simp only [primeIndicator]
  split_ifs <;> simp

/-- A sum of `1_ℙ` over a subset of the dyadic block is bounded by the block's cardinality. -/
private theorem norm_sum_primeIndicator_le {x : ℝ} {s : Finset ℕ} (hs : s ⊆ dyadic x) :
    ‖∑ n ∈ s, primeIndicator n‖ ≤ ((dyadic x).card : ℝ) :=
  (norm_sum_le _ _).trans <| (sum_le_card_nsmul _ _ 1 fun n _ ↦ norm_primeIndicator_le n).trans <|
    by simpa using card_le_card hs

/-! ## The trivial bound on the dyadic discrepancy of `1_ℙ` -/

/-- **The dyadic discrepancy of `1_ℙ` is at most twice the block size.** Both sums range over
subsets of `𝒟(x)` where `‖1_ℙ‖ ≤ 1`, and the weight `1 / φ(d)` has modulus at most `1` once
`d ≥ 1`. No hypothesis on `x` or on `a`. -/
private theorem norm_sumErrorDyadic_primeIndicator_le {x : ℝ} {d a : ℕ} (hd : 1 ≤ d) :
    ‖sumErrorDyadic x primeIndicator d a‖ ≤ 2 * ((dyadic x).card : ℝ) := by
  have hφ : ‖(1 / (Nat.totient d : ℂ))‖ ≤ 1 := by
    rw [norm_div, norm_one, Complex.norm_natCast]
    exact div_le_one_of_le₀ (by exact_mod_cast Nat.totient_pos.mpr hd) (Nat.cast_nonneg _)
  have h1 := norm_sum_primeIndicator_le (x := x)
    (Finset.filter_subset (fun n ↦ n ≡ a [MOD d]) (dyadic x))
  have h2 := norm_sum_primeIndicator_le (x := x)
    (Finset.filter_subset (fun n ↦ Nat.Coprime n d) (dyadic x))
  rw [sumErrorDyadic]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  linarith [mul_le_mul hφ h2 (norm_nonneg _) zero_le_one]

/-! ## The two bounded cardinalities below `3` -/

/-- Below `3` the dyadic block has at most four elements: `⌈x⌉₊ ≥ 2` and `⌊2x⌋₊ ≤ 5`. -/
private theorem card_dyadic_le_of_lt_three {x : ℝ} (hx1 : 1 < x) (hx3 : x < 3) :
    (dyadic x).card ≤ 4 := by
  have hc : 1 < ⌈x⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hx1)
  have hf : ⌊2 * x⌋₊ < 6 := (Nat.floor_lt (by linarith)).mpr (by push_cast; linarith)
  simp only [dyadic, Nat.card_Icc]
  omega

/-! ## The antecedent transfer -/

open Classical in
/-- **From `x ≥ 3` at `1_ℙ^{(x)}` to `x > 1` at `1_ℙ`.** The equidistribution antecedent of
`Gap212.SieveCriterion` implies `Gap212.HasEquidistributionOverQstarFamily` at the prime
indicator.

Above `3` this is the hypothesis itself, the constant having only grown. Below `3` the left-hand
side is at most `16` by `Gap212.norm_sumErrorDyadic_primeIndicator_le` and
`Gap212.card_dyadic_le_of_lt_three`, while the right-hand side is at least `16` because
`x / (log x)^A ≥ 1 / (log 3)^A` there; so the constant `max C (16 (log 3)^A)` serves both ranges,
and it is positive, which the `...Family` form also demands. -/
theorem hasEquidistributionOverQstarFamily_of_forall_ge_three {p : SupportParams}
    (h : ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ, ∀ x ≥ (3 : ℝ), ∀ a : ℕ, CoprimeBelow a x →
      HasEquidistributionOverQstar p x ε₀ (primeInterval x) a A C) :
    HasEquidistributionOverQstarFamily p primeIndicatorFamily := by
  intro ε₀ hε₀ A hA
  obtain ⟨C, hC⟩ := h ε₀ hε₀ A hA
  have hL3 : (0 : ℝ) < Real.log 3 ^ A := Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) A
  refine ⟨max C (16 * Real.log 3 ^ A),
    lt_of_lt_of_le (by positivity) (le_max_right _ _), ?_⟩
  intro x hx1 a ha
  have hx0 : (0 : ℝ) < x := by linarith
  have hLx : (0 : ℝ) < Real.log x ^ A := Real.rpow_pos_of_pos (Real.log_pos hx1) A
  rcases lt_or_ge x 3 with hx3 | hx3
  · -- Below `3`: at most two moduli, a block of at most four integers, and `‖1_ℙ‖ ≤ 1`.
    have hcd : ((dyadic x).card : ℝ) ≤ 4 := by
      exact_mod_cast card_dyadic_le_of_lt_three hx1 hx3
    have hcard : ((Finset.Icc 1 ⌊x⌋₊).card : ℝ) ≤ 2 := by
      have hfl : ⌊x⌋₊ < 3 := (Nat.floor_lt hx0.le).mpr hx3
      rw [Nat.card_Icc]
      exact_mod_cast (by lia : ⌊x⌋₊ + 1 - 1 ≤ 2)
    have hmono : Real.log x ^ A ≤ Real.log 3 ^ A :=
      Real.rpow_le_rpow (Real.log_pos hx1).le (Real.log_le_log hx0 hx3.le) hA.le
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun q _ _ ↦ norm_nonneg _)) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ 8 ?_) ?_
    · intro q hq
      change ‖sumErrorDyadic x primeIndicator q a‖ ≤ (8 : ℝ)
      linarith [norm_sumErrorDyadic_primeIndicator_le (x := x) (a := a) (mem_Icc.mp hq).1]
    · calc ((Finset.Icc 1 ⌊x⌋₊).card • (8 : ℝ)) ≤ 16 := by rw [nsmul_eq_mul]; linarith
        _ ≤ 16 * Real.log 3 ^ A * x / Real.log x ^ A := by
            rw [le_div_iff₀ hLx]
            nlinarith [mul_nonneg (sub_nonneg.mpr hx1.le) hL3.le, hmono]
        _ ≤ max C (16 * Real.log 3 ^ A) * x / Real.log x ^ A := by
            gcongr; exact le_max_right _ _
  · -- Above `3` the hypothesis applies verbatim; only the constant grows.
    have hb := hC x hx3 a ha
    simp only [HasEquidistributionOverQstar, HasEquidistribution, Finset.filter_filter,
      sumError_primeInterval_eq_sumErrorDyadic, sumErrorDyadic] at hb
    exact hb.trans (by gcongr; exact le_max_left _ _)

/-! ## The criterion in the form `Gap212.SieveCriterion` -/

/-- **The sieve criterion in the form `Gap212.SieveCriterion`.** `Gap212.Sieve.GPYSieve` alone
gives `Gap212.SieveCriterion`.

`Gap212.hasEquidistributionOverQstarFamily_of_forall_ge_three` converts the equidistribution
antecedent, and `Gap212.Sieve.dhl_of_gpySieve` applies the criterion at `β = 1/2`, with the
dyadic prime number theorem supplied by `Gap212.Sieve.primeNumberTheoremDyadic`. The certificate
hypothesis is the same proposition on both sides. -/
theorem sieveCriterion_of_gpySieve_challengeShape (hgpy : Sieve.GPYSieve) : SieveCriterion :=
  fun harith hcert ↦
    Sieve.dhl_of_gpySieve hgpy Sieve.primeNumberTheoremDyadic (β := 1 / 2) (by norm_num)
      (fun _ ↦ by change gap212Cap 1 < _; rw [gap212Cap]; norm_num)
      (hasEquidistributionOverQstarFamily_of_forall_ge_three harith) hcert

end Gap212
