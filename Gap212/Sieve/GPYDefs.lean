/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Equidistribution.Basic
public import Gap212.Sieve.Support
public import Gap212.Notation
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Primorial
public meta import Gap212.Attr

/-!
# The Goldston–Pintz–Yıldırım sieve: the objects, and the positivity step

The vocabulary the sieve criterion is stated in — the pre-sieving modulus, a prime minorant, the
divisor weight, the tensor sieve weight, the GPY sum — together with the elementary step that
turns positivity of that sum into two primes among the translates.

The analytic content (the asymptotic evaluation of numerator and denominator) is separate; what is
here is the part that needs no estimates, only the definitions and the sign of a square.

## Main definitions

* `Gap212.GPY.W`: the pre-sieving modulus `∏_{p ≤ log log log x} p`.
* `Gap212.GPY.IsPrimeMinorant`: `ρ(n;x) ≤ 1_ℙ(n)` on the dyadic block.
* `Gap212.GPY.lambdaF`: the divisor weight `∑_{d ∣ n} μ(d) F(log_x d)`.
* `Gap212.GPY.nu`: the tensor sieve weight, a square.
* `Gap212.GPY.N`: the GPY sum.
* `Gap212.GPY.retreatRegion`, `marginalRegion`: the two support retreats.

## Main results

* `Gap212.GPY.nu_nonneg`: the sieve weight is nonnegative, being a square.
* `Gap212.GPY.two_primes_of_pos`: positivity of the GPY sum gives an `n` with two prime
  translates.
* `Gap212.GPY.pos_of_ratio_gt_one`: the ratio form implies the difference form.
-/

@[expose] public section

namespace Gap212.GPY

open Finset Real

variable {k : ℕ}

/-- **The pre-sieving modulus** `W(x) = ∏_{p ≤ log log log x} p`. Small enough to be
`(log log x)^{O(1)}`, large enough that residues coprime to it have no small prime factors. -/
@[gap212 "def_wsieve"]
noncomputable def W (x : ℝ) : ℕ := primorial ⌊Real.log (Real.log (Real.log x))⌋₊

/-- **A prime minorant**: `ρ` never exceeds the prime indicator on the dyadic block. The sieve
runs on a minorant rather than on `1_ℙ` itself so that the Harman decomposition can be applied;
at the chosen parameters the minorant degenerates to `1_ℙ`. -/
@[gap212 "def_minorant"]
def IsPrimeMinorant (ρ : ℕ → ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 1 < x → ∀ n ∈ dyadic x, ρ n x ≤ (if n.Prime then 1 else 0)

/-- **The divisor weight** `λ_F(n) = ∑_{d ∣ n} μ(d) F(log_x d)`, the one-variable building block
of the sieve weight. -/
@[gap212 "def_lambda_F"]
noncomputable def lambdaF (F : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * F (Gap212.Notation.logx x d)

/-- **The tensor sieve weight**: a finite combination of products of divisor weights, squared. The
square is what makes it nonnegative, which is the only property of it the positivity step uses. -/
@[gap212 "def_tensor_weight"]
noncomputable def nu (L : ℕ) (c : Fin L → ℝ) (F : Fin L → Fin k → ℝ → ℝ)
    (h : Fin k → ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  (∑ l : Fin L, c l * ∏ i : Fin k, lambdaF (F l i) x (n + h i)) ^ 2

/-- **The sieve weight is nonnegative**, being a square. -/
@[gap212 "lem_nu_nonneg"]
theorem nu_nonneg (L : ℕ) (c : Fin L → ℝ) (F : Fin L → Fin k → ℝ → ℝ)
    (h : Fin k → ℕ) (x : ℝ) (n : ℕ) : 0 ≤ nu L c F h x n := sq_nonneg _

/-- **The Goldston–Pintz–Yıldırım sum.** Each `n` in the dyadic block, restricted to the
pre-sieved class, is weighted by `ν(n)` and counted with the excess of prime translates over one.
Positivity forces some `n` to have at least two. -/
@[gap212 "def_gpy_sum"]
noncomputable def N (ρ : ℕ → ℝ → ℝ) (ν : ℕ → ℝ) (h : Fin k → ℕ) (b : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ dyadic x with n % W x = b % W x,
    ν n * ((∑ i : Fin k, ρ (n + h i) x) - 1)

/-- **Positivity gives a large minorant sum**: if `ν ≥ 0` and the GPY sum is positive, then some
`n` in the block has `1 < ∑ᵢ ρ(n + hᵢ)`.

The conclusion is a bound on the minorant sum, with no primality in it; `ρ` is not assumed to be a
minorant. The primality statement, that some `n₀ ∈ [x,2x]` has at least two of
`n₀ + h₁, …, n₀ + h_k` prime, is `Gap212.Sieve.exists_two_primes_of_pos`, this composed with
`Gap212.Sieve.two_le_card_prime_of_one_lt_sum`.

Contrapositive: if every `n` had `∑ᵢ ρ(n + hᵢ) ≤ 1` then each bracket `∑ᵢ ρ(n + hᵢ) - 1` would be
`≤ 0`; with `ν ≥ 0` every term would be `≤ 0` and the sum could not be positive. -/
theorem two_primes_of_pos {ρ : ℕ → ℝ → ℝ} {ν : ℕ → ℝ} {h : Fin k → ℕ} {b : ℕ} {x : ℝ}
    (hν : ∀ n, 0 ≤ ν n) (hpos : 0 < N ρ ν h b x) :
    ∃ n ∈ dyadic x, 1 < ∑ i : Fin k, ρ (n + h i) x := by
  by_contra hcon
  push Not at hcon
  have : N ρ ν h b x ≤ 0 := by
    unfold N
    refine Finset.sum_nonpos ?_
    intro n hn
    have hnd : n ∈ dyadic x := (Finset.mem_filter.mp hn).1
    have hle : (∑ i : Fin k, ρ (n + h i) x) - 1 ≤ 0 := by
      have := hcon n hnd
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos (hν n) hle
  exact absurd hpos (not_lt.mpr this)

/-- **The ratio form implies the difference form.** If the weighted count of prime translates
exceeds the total weight, the GPY sum is positive. This is the shape the asymptotic evaluation
delivers: a quotient above `1`. -/
@[gap212 "lem_ratio_gives_positivity"]
theorem pos_of_ratio_gt_one {ρ : ℕ → ℝ → ℝ} {ν : ℕ → ℝ} {h : Fin k → ℕ} {b : ℕ} {x : ℝ}
    (hgt : (∑ n ∈ dyadic x with n % W x = b % W x, ν n) <
      ∑ n ∈ dyadic x with n % W x = b % W x, ν n * ∑ i : Fin k, ρ (n + h i) x) :
    0 < N ρ ν h b x := by
  unfold N
  have hsplit : ∑ n ∈ dyadic x with n % W x = b % W x,
      ν n * ((∑ i : Fin k, ρ (n + h i) x) - 1) =
      (∑ n ∈ dyadic x with n % W x = b % W x, ν n * ∑ i : Fin k, ρ (n + h i) x) -
        ∑ n ∈ dyadic x with n % W x = b % W x, ν n := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ ↦ by ring
  rw [hsplit]
  linarith

/-- **The retreat region.** The support pulled in by `ε₀`: the total mass and every rough-mass cap
are scaled by `1 - ε₀`. It is where the sieve weights are supported, which is what keeps the
generated moduli inside `Q*`.

Two departures from a retreated stratum, without which the region would be empty:

The rough threshold is non-strict. A stratum constrains the coordinates *exceeding* `δ`
(`Gap212.SupportParams.large`); the moduli a support generates constrain the rough factors, which
are the ones of size *at least* `x^δ` (`Gap212.Qgen`). The constraint this region has to transport
is the second, so the second is what it asserts.

And the cap inequality is non-strict while the total-mass inequality is strict. A strict cap makes
the region empty: at `I = ∅` it reads `0 < (1 - ε₀) * B_{j,0} = 0`, so no point all of whose
coordinates are below `δ` could belong — and those are exactly the points the downward boxes of
the tensor construction have to reach. `Gap212.Qgen` carries the same inequality non-strictly, for
the same reason: there the empty rough product is `1 = x^0`. -/
@[gap212 "def_retreat_region"]
noncomputable def retreatRegion (p : SupportParams) (k : ℕ) (j : Fin p.n) (ε₀ : ℝ) :
    Set (Fin k → ℝ) :=
  {t | (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) ∧
    (∑ i, t i) < (1 - ε₀) * (p.A j.succ + p.ε) ∧
    ∑ i ∈ p.roughIdx k t, t i ≤ (1 - ε₀) * p.B j (p.roughIdx k t).card}

/-- **The marginal region.** The retreat of the first `k - 1` coordinates against the lower node
`A_j - ε`, which is the constraint the `J`-form's outer integral carries. -/
@[gap212 "def_marginal_region"]
def marginalRegion (p : SupportParams) (m : ℕ) (j : Fin p.n) (ε₀ : ℝ) : Set (Fin m → ℝ) :=
  {t | (∑ i, t i) < (1 - ε₀) * (p.A j.succ - p.ε)}

end Gap212.GPY
