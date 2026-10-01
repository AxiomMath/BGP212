/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Asymptotics
public import Gap212.Sieve.DyadicPNT
public import Gap212.Sieve.WSieve

/-!
# The unrestricted sieve asymptotic is false at `k = 1`

`Gap212.Sieve.SieveAsymptotic` is the asymptotic for the sieve sum weighted by `ρ(n + h_{i₀})`,
stated for a support datum with `A_j > ε`, a level `ε₀ ∈ (0,1)`, an admissible tuple, a
pre-sieved residue `b`, and smooth profiles `Fᵢ, Gᵢ` with `supp ∏ᵢFᵢ ⊆ R⁺_k(j,ε₀)`,
`supp ∏ᵢGᵢ ⊆ R⁺_k(j',ε₀)` and `supp ∏_{i≠i₀}Fᵢ ⊆ M⁻_k(j,i₀,ε₀)`.
`Gap212.Sieve.SieveAsymptoticUnrestricted` drops all of these hypotheses, leaves `b` an arbitrary
natural number bound before `∃ X`, and quantifies the inner products existentially instead of
fixing them to `∫₀^∞F'ᵢG'ᵢ`. This module shows that the unrestricted form is false at `k = 1`.

## The refutation

`Gap212.Sieve.not_sieveAsymptotic_one` kills `Gap212.Sieve.SieveAsymptoticUnrestricted 1` using the
unguarded residue alone: at `b = 0` every member of the class is divisible by `W(x)`, hence even,
hence not prime, so `ρ` annihilates the whole sum — while the main term `F_{i₀}(0)G_{i₀}(0)` is `1`
at the constant profiles. At `k = 1` the product `∏_{i≠i₀}` is empty, so the existential inner
products cannot rescue it.

For `k ≥ 2` this witness does not refute the statement, since `inner` can be taken `0`, making
the main term vanish with the sum.

## Main results

* `Gap212.Sieve.not_sieveAsymptotic_one`: `¬ Gap212.Sieve.SieveAsymptoticUnrestricted 1`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.Defs Gap212.GPY

/-- **`Gap212.Sieve.SieveAsymptoticUnrestricted 1` is false.**

The witness is the unguarded residue: `b = 0`, so the class is the multiples of `W(x)` in the
dyadic block. Every one of them is even once `2 ∣ W(x)`, which holds for all large `x`
(`Gap212.Sieve.eventually_dvd_W_of_prime_le`), and even numbers above `2` are not prime, so the
minorant clause of `Gap212.Defs.RhoHypotheses` forces `ρ = 0` on the whole class and the sum is
`0`. The main term, at `F = G = 1` and `k = 1`, is `F(0)G(0) = 1` times the scale — the empty
product `∏_{i≠i₀}` leaving the existentially quantified Gram data no room. So the claim says
`𝓒_x ≤ η·𝓒_x` for every `η > 0`, and the scale is positive.

`ρ` is the restricted prime indicator, admissible by `Gap212.Sieve.rhoHypotheses_primeIndicator`
and `Gap212.Sieve.primeNumberTheoremDyadic`.

`Gap212.Sieve.SieveAsymptotic` requires `b` to be pre-sieved, so this witness does not apply to
it. -/
theorem not_sieveAsymptotic_one : ¬ SieveAsymptoticUnrestricted 1 := by
  intro hasym
  obtain ⟨inner, hinner⟩ := hasym gap212Params primeIntervalReal (1 / 2)
    (rhoHypotheses_primeIndicator primeNumberTheoremDyadic (by norm_num)
      (fun _ ↦ by change gap212Cap 1 < _; rw [gap212Cap]; norm_num))
    (fun _ ↦ 0) 0 (fun _ _ ↦ 1) (fun _ _ ↦ 1) 0
  obtain ⟨X, hX⟩ := hinner (1 / 2) (by norm_num)
  obtain ⟨x, ⟨⟨hdvd, hx4⟩, hxX⟩⟩ :=
    (((eventually_dvd_W_of_prime_le 2).and (eventually_gt_atTop (4 : ℝ))).and
      (eventually_gt_atTop X)).exists
  have hx1 : (1 : ℝ) < x := by linarith
  have h2W : 2 ∣ W x := hdvd 2 Nat.prime_two le_rfl
  -- Every member of the class is even and exceeds `2`, so `ρ` kills every term.
  have hzero : ∀ n ∈ {n ∈ dyadic x | n % W x = 0 % W x},
      primeIntervalReal (n + 0) x *
        ∏ _i : Fin 1, lambdaF (fun _ ↦ (1 : ℝ)) x (n + 0) *
          lambdaF (fun _ ↦ (1 : ℝ)) x (n + 0) = 0 := by
    intro n hn
    obtain ⟨hnmem, hnmod⟩ := Finset.mem_filter.mp hn
    have hn4 : 4 ≤ n := by
      rw [Gap212.dyadic, Finset.mem_Icc] at hnmem
      have : (4 : ℝ) < (⌈x⌉₊ : ℕ) := lt_of_lt_of_le hx4 (Nat.le_ceil x)
      have h4 : 4 < ⌈x⌉₊ := by exact_mod_cast this
      omega
    have h2n : 2 ∣ n := dvd_trans h2W (Nat.dvd_of_mod_eq_zero (by simpa using hnmod))
    have hnp : ¬ n.Prime := by
      intro hp
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2n
      omega
    rw [Nat.add_zero, primeIntervalReal_of_mem hnmem, if_neg hnp, zero_mul]
  have hbound := hX x hxX
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at hbound
  -- The main term is `1`, the product over the empty `univ.erase i₀` being `1`.
  have herase : (Finset.univ.erase (0 : Fin 1)) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun i hi ↦ ?_
    have := Finset.ne_of_mem_erase hi
    exact this (Subsingleton.elim i 0)
  rw [herase, Finset.prod_empty, mul_one, mul_one, one_mul, zero_sub, abs_neg] at hbound
  have hsc : 0 < scale 1 x := scale_pos hx1 (primorial_pos _)
  rw [abs_of_nonneg hsc.le] at hbound
  linarith

end Gap212.Sieve
