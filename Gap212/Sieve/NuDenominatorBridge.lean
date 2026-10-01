/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Asymptotics
public import Gap212.Sieve.ScaleCalC

/-!
# The denominator asymptotic, expanded into pair sums

`Gap212.Sieve.NuDenominator` is the denominator asymptotic. Its content is
`Gap212.Sieve.selberg_progression_sum`, which is a statement about a *pair* of profile families
`(F_i), (G_i)` — and the statement is about the tensor weight `ν`, which is a *square*. So the
join between them is an algebraic expansion, and that expansion is what this file proves.

## The expansion

`Gap212.GPY.nu L c F h x n = (∑_l c_l ∏_i λ_{F l i}(n + h i))²`, so summing over a block and
expanding the square,

  `∑_{n ∈ s} ν(n) = ∑_l ∑_{l'} c_l c_{l'} · ∑_{n ∈ s}`
  `  (∏_i λ_{F l i}(n + h i))(∏_i λ_{F l' i}(n + h i))`,

and each inner sum is exactly the left-hand side of `Gap212.Sieve.selberg_progression_sum` at the
pair `(F l ·, F l' ·)`. There are `L²` of them, and the coefficient of each is `c_l c_{l'}`.

## Comparison with the target

The target `Gap212.Defs.formI c (Gap212.Sieve.gramInner F)` is *by definition*
`∑_l ∑_{l'} c_l c_{l'} ∏_s gramInner F l l' s`, and `gramInner F l l' s` is
`∫_{t > 0} (F l s)' (F l' s)'`. So its conclusion for the pair `(F l ·, F l' ·)` — that the inner
sum is `(∏_s ∫ (F l s)'(F l' s)' + o(1))·𝓒_x` — is termwise what `formI` sums. Matching them needs
nothing further about the mathematics: only the expansion below, the identification
`scale (m+1) x = 𝓒_x` of `Gap212.Sieve.scale_succ_eq_calC`, and an `ε`-budget split over the `L²`
pairs.

## Main results

* `Gap212.Sieve.sum_nu_eq_sum_pairs`: the expansion, over an arbitrary `Finset` of naturals.
* `Gap212.Sieve.sum_nu_dyadic_eq_sum_pairs`: the same at the block `Gap212.Sieve.NuDenominator` sums
  over.
* `Gap212.Sieve.formI_gramInner_eq`: `formI c (gramInner F)` written out as the matching double
  sum, so the two sides can be compared term by term.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset Gap212.Defs Gap212.GPY

variable {k L : ℕ}

/-- **The tensor weight's block sum, expanded into pair sums.** `ν` is a square, so summing it over
a finite set of `n` and expanding gives `L²` sums, one for each ordered pair `(l, l')` of tensor
indices, each weighted by `c_l c_{l'}`:

`∑_{n ∈ s} ν(n) = ∑_l ∑_{l'} c_l c_{l'} ∑_{n ∈ s} (∏_i λ_{F l i}(n+h i))(∏_i λ_{F l' i}(n+h i))`.

Each inner sum is the left-hand side of `Gap212.Sieve.selberg_progression_sum` at the pair of
families `(F l ·, F l' ·)`. This is the algebraic content of discharging
`Gap212.Sieve.NuDenominator` from it. -/
theorem sum_nu_eq_sum_pairs (s : Finset ℕ) (c : Fin L → ℝ) (F : Fin L → Fin k → ℝ → ℝ)
    (h : Fin k → ℕ) (x : ℝ) :
    ∑ n ∈ s, nu L c F h x n
      = ∑ l : Fin L, ∑ l' : Fin L, c l * c l' *
          ∑ n ∈ s, (∏ i : Fin k, lambdaF (F l i) x (n + h i)) *
            (∏ i : Fin k, lambdaF (F l' i) x (n + h i)) := by
  have hpt : ∀ n : ℕ, nu L c F h x n
      = ∑ l : Fin L, ∑ l' : Fin L, c l * c l' *
          ((∏ i : Fin k, lambdaF (F l i) x (n + h i)) *
            (∏ i : Fin k, lambdaF (F l' i) x (n + h i))) := by
    intro n
    rw [nu, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    ring
  calc ∑ n ∈ s, nu L c F h x n
      = ∑ n ∈ s, ∑ l : Fin L, ∑ l' : Fin L, c l * c l' *
          ((∏ i : Fin k, lambdaF (F l i) x (n + h i)) *
            (∏ i : Fin k, lambdaF (F l' i) x (n + h i))) :=
        Finset.sum_congr rfl fun n _ => hpt n
    _ = ∑ l : Fin L, ∑ l' : Fin L, ∑ n ∈ s, c l * c l' *
          ((∏ i : Fin k, lambdaF (F l i) x (n + h i)) *
            (∏ i : Fin k, lambdaF (F l' i) x (n + h i))) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
        rw [← Finset.mul_sum]

/-- **The expansion at the dyadic block.** `Gap212.Sieve.NuDenominator` sums `ν`
over `{n ∈ dyadic x | n ≡ b (W x)}`; this is `Gap212.Sieve.sum_nu_eq_sum_pairs` at that set, in the
spelling `Gap212.Sieve.NuDenominator` uses. -/
theorem sum_nu_dyadic_eq_sum_pairs (c : Fin L → ℝ) (F : Fin L → Fin k → ℝ → ℝ)
    (h : Fin k → ℕ) (x : ℝ) (b : ℕ) :
    ∑ n ∈ dyadic x with n % W x = b % W x, nu L c F h x n
      = ∑ l : Fin L, ∑ l' : Fin L, c l * c l' *
          ∑ n ∈ dyadic x with n % W x = b % W x,
            (∏ i : Fin k, lambdaF (F l i) x (n + h i)) *
              (∏ i : Fin k, lambdaF (F l' i) x (n + h i)) :=
  sum_nu_eq_sum_pairs _ c F h x

/-- **The target, written as the matching double sum.** `Gap212.Defs.formI c (gramInner F)` is
`∑_l ∑_{l'} c_l c_{l'} ∏_s ∫_{t>0} (F l s)'(F l' s)'`, term for term the limit of the pair sums of
`Gap212.Sieve.sum_nu_eq_sum_pairs`.

This holds by unfolding `formI` and `gramInner`. -/
theorem formI_gramInner_eq (c : Fin L → ℝ) (F : Fin L → Fin k → ℝ → ℝ) :
    formI c (gramInner F)
      = ∑ l : Fin L, ∑ l' : Fin L, c l * c l' *
          ∏ s : Fin k, ∫ t in Set.Ioi (0 : ℝ), deriv (F l s) t * deriv (F l' s) t := rfl

end Gap212.Sieve
