/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Defs
public import Gap212.Routing.Defs.GeneratedModuli
public import Gap212.Sieve.GPY
public meta import Gap212.Attr

/-!
# The direct-prime sieve criterion

The GPY sieve is stated for a general prime minorant `ρ`, admissible for a pair `(β, T)`. At the
Point A parameters the minorant degenerates — `ξ₂ = 2/5` makes the Harman construction return the
prime indicator itself — so the criterion is applied at `ρ = 1_ℙ^{(x)}`, the prime indicator cut
down to the dyadic block. This module declares the criterion, verifies that `1_ℙ^{(x)}` is
admissible, and specializes.

* `Gap212.Sieve.GPYSieve` is the sieve criterion of §3 of Stadlmann's paper: the retreat, the
  mollification, the finite-tensor construction, the asymptotic evaluation of numerator and
  denominator, and the comparison of main term against error. It takes
  `Gap212.Certificate gap212Params 44 0 0` as the variational inequality, and is proved in
  `Gap212.Sieve.CriterionAssembly` as `Gap212.Sieve.gpySieve_of_obligations`.
* `Gap212.Sieve.PrimeNumberTheoremDyadic` is proved in `Gap212.Sieve.DyadicPNT`, from the
  dependency's `PNT.primeCountingIoc_self_two_mul`. Since that module imports this one, it is a
  hypothesis of `rhoHypotheses_primeIndicator` and `dhl_of_gpySieve` below; it is discharged in
  `Gap212.sieveCriterion_of_gpySieve_challengeShape`.

## The minorant

The minorant is the block-restricted indicator `Gap212.Sieve.primeIntervalReal`, not the bare
indicator `Gap212.Sieve.primeIndicatorReal`. The bare indicator has infinite support, so it fails
`Gap212.Defs.RhoHypotheses.support` (`primeIndicatorReal 2 x = 1` while `2 ∉ Gap212.dyadic x` for
every `x > 2`), and the unrestricted discrepancy sums of the equidistribution clause would not be
finite sums for it. The `rough` clause of `Gap212.Defs.RhoHypotheses` is likewise stated on the
block: off the block, `1_ℙ(2) ≠ 0` while `x^β > 2` for all large `x`.

## Main definitions

* `Gap212.Sieve.primeIntervalReal`: `1_ℙ^{(x)}` valued in `ℝ`, the shape `RhoHypotheses` takes.
* `Gap212.Sieve.primeIndicatorReal`: the bare `1_ℙ` in the same shape, used for counting.
* `Gap212.Sieve.GPYSieve`: the sieve criterion at the datum.
* `Gap212.Sieve.PrimeNumberTheoremDyadic`: the prime number theorem on `[x, 2x]`.

## Main results

* `Gap212.Sieve.rhoHypotheses_primeIndicator`: `1_ℙ^{(x)}` is admissible for `(β, T)` whenever
  `max_j B_{j,1} < β < 1`.
* `Gap212.Sieve.hasEquidistributionOverQstarFamily_congr`: the equidistribution norm only sees the
  dyadic block, so it transfers between families agreeing there.
* `Gap212.Sieve.dhl_of_gpySieve`: the direct-prime criterion — equidistribution of `1_ℙ` over the
  generated moduli plus the variational inequality gives `DHL[45, 2]`.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset Real Gap212.Defs

/-! ## The prime indicator, in the shape the criterion consumes -/

/-- **`1_ℙ`, valued in `ℝ`, with a dummy scale argument.**

It has infinite support, so it is not an admissible minorant (it fails
`Gap212.Defs.RhoHypotheses.support`); it is the indicator used for counting primes, in
`Gap212.Sieve.PrimeNumberTheoremDyadic` and `Gap212.Sieve.sum_primeIndicatorReal_dyadic`, and on
the dyadic block it agrees with the minorant `Gap212.Sieve.primeIntervalReal`. -/
def primeIndicatorReal : ℕ → ℝ → ℝ := fun n _ ↦ if n.Prime then 1 else 0

/-- **`1_ℙ^{(x)}`, valued in `ℝ`**: the prime indicator cut down to the dyadic block, in the
argument order `Gap212.Defs.RhoHypotheses` takes.

This is the minorant the criterion is applied to.
`Gap212.primeInterval` is the same sequence valued in `ℂ`, which is the shape the equidistribution
norm sums; `Gap212.Sieve.primeInterval_coe` identifies the two. -/
noncomputable def primeIntervalReal : ℕ → ℝ → ℝ :=
  fun n x ↦ if n ∈ dyadic x then (if n.Prime then 1 else 0) else 0

/-- On the dyadic block, `1_ℙ^{(x)}` is the prime indicator. -/
theorem primeIntervalReal_of_mem {x : ℝ} {n : ℕ} (hn : n ∈ dyadic x) :
    primeIntervalReal n x = if n.Prime then 1 else 0 :=
  if_pos hn

/-- Off the dyadic block, `1_ℙ^{(x)}` vanishes. This is the `support` field of
`Gap212.Defs.RhoHypotheses`. -/
theorem primeIntervalReal_of_notMem {x : ℝ} {n : ℕ} (hn : n ∉ dyadic x) :
    primeIntervalReal n x = 0 :=
  if_neg hn

/-- On the dyadic block the restricted and the bare indicator agree. -/
theorem primeIntervalReal_eq_primeIndicatorReal {x : ℝ} {n : ℕ} (hn : n ∈ dyadic x) :
    primeIntervalReal n x = primeIndicatorReal n x := by
  rw [primeIntervalReal_of_mem hn, primeIndicatorReal]

/-- The two shapes of `1_ℙ^{(x)}` agree under the coercion. `Gap212.primeInterval` lands in `ℂ`
because the equidistribution norm sums complex discrepancies; `Gap212.Defs.RhoHypotheses` is about
a real-valued minorant, so both shapes are needed. -/
theorem primeInterval_coe :
    (fun (n : ℕ) (x : ℝ) ↦ ((primeIntervalReal n x : ℝ) : ℂ)) = fun n x ↦ primeInterval x n := by
  funext n x
  simp only [primeIntervalReal, primeInterval, primeIndicator]
  split_ifs <;> norm_num

/-! ## The two named inputs -/

/-- **The prime number theorem on a dyadic block.** The count of primes in `[x, 2x]` is
`(1 + o(1)) x / log x`.

This is the form the density condition of `Gap212.Defs.RhoHypotheses` asks for. It is stated with
the bare `Gap212.Sieve.primeIndicatorReal`; the density field is about `1_ℙ^{(x)}`, and the two
sums agree because the summation range is the block itself.

It is proved as `Gap212.Sieve.primeNumberTheoremDyadic` in `Gap212.Sieve.DyadicPNT`, from the
dependency's `PNT.primeCountingIoc_self_two_mul`. -/
def PrimeNumberTheoremDyadic : Prop :=
  ∀ ε > (0 : ℝ), ∃ X : ℝ, ∀ x > X,
    |(∑ n ∈ dyadic x, primeIndicatorReal n x) - x / Real.log x| ≤ ε * x / Real.log x

/-- **The GPY sieve** (§3 of Stadlmann's paper) at the datum `p_⋆ = Gap212.gap212Params` and
`k = 45`. For a minorant `ρ` admissible for `(β, T)` that equidistributes over the moduli the
support generates, a symmetric `F ∈ L²(T)` with `0 < I_T(F) < 45 J_T(F)` gives `DHL[45, 2]`.

The variational inequality is `Gap212.Certificate gap212Params 44 0 0`, the cleared form of
`45 J_T(F) / I_T(F) > 1`. The equidistribution clause is a separate hypothesis rather than a field
of `RhoHypotheses`, because `Gap212.HasEquidistributionOverQstarFamily` is defined downstream of
`Gap212.Defs`; the two together are the five-clause admissibility condition.

This criterion is not available from `PrimeGapsLib`, whose sieve requires `θ < 1/2` and works on
the `ε`-enlarged simplex. Compare `Gap212.Sieve.GPYCriterion`, the same content with the weaker
`NthPrimeGapLE` conclusion. Proved as `Gap212.Sieve.gpySieve_of_obligations`. -/
@[gap212 "prop_gpy_sieve"]
def GPYSieve : Prop :=
  ∀ (ρ : ℕ → ℝ → ℝ) (β : ℝ),
    RhoHypotheses gap212Params ρ β →
    HasEquidistributionOverQstarFamily gap212Params (fun n x ↦ ((ρ n x : ℝ) : ℂ)) →
    Certificate gap212Params 44 0 0 → DHL 45 2

/-! ## The restricted prime indicator is admissible -/

/-- **`1_ℙ^{(x)}` is admissible for `(β, T)`** whenever `max_j B_{j,1} < β < 1`.

The four clauses of `Gap212.Defs.RhoHypotheses`:

* *support*: the restriction itself, by `if_neg`;
* *minorant*: on the block `1_ℙ^{(x)}` reduces to `1_ℙ`, which is between `0` and itself;
* *rough*: if `1_ℙ^{(x)}(n) ≠ 0` then `n` is prime, so its only prime factor is `n` itself, and
  `n ≥ ⌈x⌉ ≥ x > x^β` since `β < 1` and `x > 1`;
* *density*: exactly the prime number theorem on the block, `1_ℙ^{(x)}` agreeing with `1_ℙ` there.

The equidistribution clause of admissibility is not part of `Gap212.Defs.RhoHypotheses` (it is a
separate hypothesis of `Gap212.Sieve.GPYSieve`), so no equidistribution input is needed here.

The lower bound `hcap : max_j B_{j,1} < β` is the clause `RhoHypotheses.rough_exceeds_cap`. It
does not follow from `Gap212.SupportParams`, which places no upper bound on `B`; at
`Gap212.gap212Params` the first rung is `777/5000`. -/
@[gap212 "lem_prime_indicator_hyps"]
theorem rhoHypotheses_primeIndicator (hpnt : PrimeNumberTheoremDyadic)
    {p : SupportParams} {β : ℝ} (hβ : β < 1) (hcap : ∀ j : Fin p.n, p.B j 1 < β) :
    RhoHypotheses p primeIntervalReal β where
  support := fun _ _ hn ↦ primeIntervalReal_of_notMem hn
  minorant := by
    intro x _ n hn
    rw [primeIntervalReal_of_mem hn]
    split_ifs <;> norm_num
  rough := by
    intro x hx n hn hne r hr hrn
    -- On the block the value reduces, and `1_ℙ(n) ≠ 0` forces `n` prime, so `r ∣ n` forces
    -- `r = n`.
    rw [primeIntervalReal_of_mem hn] at hne
    have hnp : n.Prime := by
      by_contra h
      rw [if_neg h] at hne
      exact hne rfl
    have hrn' : r = n := ((Nat.prime_dvd_prime_iff_eq hr hnp).mp hrn)
    -- `n` is in the block, so `x ≤ n`; and `x ^ β < x ^ 1 = x` because `β < 1 < x`.
    have hxn : x ≤ (n : ℝ) := by
      have h₁ : ⌈x⌉₊ ≤ n := (Finset.mem_Icc.mp hn).1
      exact le_trans (Nat.le_ceil x) (by exact_mod_cast h₁)
    have hlt : x ^ β < x := by
      have := Real.rpow_lt_rpow_left_iff (x := x) hx |>.mpr hβ
      simpa using this
    rw [hrn']
    exact lt_of_lt_of_le hlt hxn
  rough_exceeds_cap := hcap
  density := by
    intro ε hε
    obtain ⟨X, hX⟩ := hpnt ε hε
    refine ⟨X, fun x hx ↦ ?_⟩
    rw [Finset.sum_congr rfl fun n hn ↦ primeIntervalReal_eq_primeIndicatorReal hn]
    exact hX x hx

/-! ## The equidistribution hypothesis transfers to the restricted indicator -/

/-- Two families agreeing on the dyadic block have the same sums over any subset of it cut out by a
predicate. -/
private theorem sum_filter_dyadic_congr {f g : ℕ → ℝ → ℂ} {x : ℝ}
    (hfg : ∀ n ∈ dyadic x, f n x = g n x) (P : ℕ → Prop) [DecidablePred P] :
    ∑ n ∈ dyadic x with P n, g n x = ∑ n ∈ dyadic x with P n, f n x :=
  Finset.sum_congr rfl fun n hn ↦ (hfg n (Finset.mem_filter.mp hn).1).symm

/-- **The equidistribution norm only sees the block.** Both sums inside
`Gap212.HasEquidistributionOverQstarFamily` range over subsets of `Gap212.dyadic x`, so two
families agreeing there satisfy it together — with the *same* constant, the two left-hand sides
being equal term by term. -/
theorem hasEquidistributionOverQstarFamily_congr {p : SupportParams} {f g : ℕ → ℝ → ℂ}
    (hfg : ∀ x : ℝ, ∀ n ∈ dyadic x, f n x = g n x)
    (hf : HasEquidistributionOverQstarFamily p f) :
    HasEquidistributionOverQstarFamily p g := by
  intro ε₀ hε₀ A hA
  obtain ⟨c, hc, hb⟩ := hf ε₀ hε₀ A hA
  refine ⟨c, hc, fun x hx a ha ↦ ?_⟩
  refine le_of_eq_of_le (Finset.sum_congr rfl fun q _ ↦ ?_) (hb x hx a ha)
  rw [sum_filter_dyadic_congr (hfg x), sum_filter_dyadic_congr (hfg x)]

/-- **The prime indicator's equidistribution is the restricted indicator's.** The two sequences
agree on the dyadic block, which is all
`Gap212.HasEquidistributionOverQstarFamily` looks at. -/
theorem hasEquidistributionOverQstarFamily_primeIntervalReal {p : SupportParams}
    (h : HasEquidistributionOverQstarFamily p primeIndicatorFamily) :
    HasEquidistributionOverQstarFamily p (fun n x ↦ ((primeIntervalReal n x : ℝ) : ℂ)) := by
  refine hasEquidistributionOverQstarFamily_congr (fun x n hn ↦ ?_) h
  rw [primeIntervalReal_of_mem hn]
  simp only [primeIndicatorFamily]
  split_ifs <;> norm_num

/-! ## The direct-prime criterion -/

/-- **The direct-prime sieve criterion.** If the prime indicator equidistributes over the moduli
the datum generates, and the datum carries the variational inequality, then `DHL[45, 2]` holds.

This is `Gap212.Sieve.GPYSieve` at the restricted indicator `ρ = 1_ℙ^{(x)}`, which is admissible by
`Gap212.Sieve.rhoHypotheses_primeIndicator`; the equidistribution hypothesis, stated at the bare
indicator, transfers by `Gap212.Sieve.hasEquidistributionOverQstarFamily_primeIntervalReal`.
`Gap212.Certificate gap212Params 44 0 0` reads `0 < I < 45 J`. -/
theorem dhl_of_gpySieve (hgpy : GPYSieve) (hpnt : PrimeNumberTheoremDyadic) {β : ℝ} (hβ : β < 1)
    (hcap : ∀ j : Fin gap212Params.n, gap212Params.B j 1 < β)
    (harith : HasEquidistributionOverQstarFamily gap212Params primeIndicatorFamily)
    (hcert : Certificate gap212Params 44 0 0) :
    DHL 45 2 :=
  hgpy primeIntervalReal β (rhoHypotheses_primeIndicator hpnt hβ hcap)
    (hasEquidistributionOverQstarFamily_primeIntervalReal harith) hcert

end Gap212.Sieve
