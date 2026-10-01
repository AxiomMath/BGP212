/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import PrimeGapsTheory.ArithmeticFunction.Tau
public import PrimeGapsTheory.Discrete.FinMulAntidiag

/-!
# The divisor-moment bound

The error term of `Gap212.Sieve.selberg_progression_sum` is the number of divisor tuples that
contribute at all, and it is bounded by

  `∑_{m ≤ N} τ_{2k}(m) ≪ N (log N)^{2k-1}`,

proved here in sharp form, with constant `1`. Neither Mathlib nor `PrimeGapsLib` provides it.
`PrimeGapsLib` has the reciprocal-weighted Mertens family
(`ArithmeticFunction.sum_moebius_sq_mul_tau_div_totient_le`, `WeightedDivisorSum.weightedSum_le`,
`MaynardS2Error.tau4_totient_full_sum_le`), whose `1/φ(q)` decay is what makes those proofs
converge; the crude `MaynardS2Error.tau_le_rpow` (`τ_r(m) ≤ C m^ε`); and the short-range
`MaynardS2Error.tau_sq_sum_bound`, whose saving comes from its hypothesis `θ < 1` by a Rankin
trick. Mathlib has no average order for any divisor function, only the exact identity
`ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div`; the Dirichlet hyperbola method is not in Mathlib.

## The statement

`Gap212.Sieve.sum_tau_le` is

  `∑_{m=1}^{N} τ_{r+1}(m) ≤ N · (1 + log N)^r`,

in the dependency's own `ArithmeticFunction.τ` — the `r`-fold Dirichlet power of `ζ`. No new
divisor function is introduced.

## The proof

`τ_r(m)` counts the ordered `r`-tuples with product `m`
(`ArithmeticFunction.tau_apply_eq_card_finMulAntidiag`), so `∑_{m ≤ N} τ_r(m)` counts the
`r`-tuples of positive integers with product **at most** `N` — the dependency's
`Nat.finMulAntidiagLE (Fin r) N`. That identification is
`Gap212.Sieve.sum_tau_eq_card_finMulAntidiagLE`, and it replaces the Dirichlet hyperbola identity:
the recursion on the number of coordinates is then a *fibrewise cardinality*
(`Gap212.Sieve.card_finMulAntidiagLE_succ`), splitting a tuple at its first coordinate,

  `#(finMulAntidiagLE (Fin (r+1)) N) = ∑_{a=1}^{N} #(finMulAntidiagLE (Fin r) ⌊N/a⌋)`.

Induction on `r` then gives the bound: the count at one coordinate is exactly `N`, and

  `#(finMulAntidiagLE (Fin (r+2)) N) ≤ ∑_{a=1}^{N} (N/a)(1 + log(N/a))^r
      ≤ N (1 + log N)^r ∑_{a=1}^{N} 1/a ≤ N (1 + log N)^{r+1}`,

the last step being Mathlib's harmonic bound `harmonic_le_one_add_log`. Every constant is `1`;
nothing here is asymptotic, so the result is available at every `N` and not only eventually.

## Main results

* `Gap212.Sieve.card_finMulAntidiagLE_succ`: the hyperbola recursion, as a fibrewise cardinality.
* `Gap212.Sieve.card_finMulAntidiagLE_le`: `#(finMulAntidiagLE (Fin (r+1)) N) ≤ N (1 + log N)^r`.
* `Gap212.Sieve.sum_tau_eq_card_finMulAntidiagLE`: `∑_{m ≤ N} τ_r(m)` as that cardinality.
* `Gap212.Sieve.sum_tau_le`: the bound, `∑_{m ≤ N} τ_{r+1}(m) ≤ N (1 + log N)^r`.
* `Gap212.Sieve.sum_tau_two_mul_le`: the same at `r = 2k`.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset
open scoped ArithmeticFunction ArithmeticFunction.zeta

/-! ### Coordinates of a tuple of bounded product -/

/-- A coordinate of a tuple in `Nat.finMulAntidiagLE` is at most the bound: the ambient box of that
definition imposes nothing beyond positivity and the product bound. -/
theorem coord_le_of_mem_finMulAntidiagLE {r N : ℕ} {d : Fin r → ℕ}
    (hd : d ∈ Nat.finMulAntidiagLE (Fin r) N) (i : Fin r) : d i ≤ N := by
  rw [Nat.mem_finMulAntidiagLE_iff] at hd
  exact le_trans (Finset.single_le_prod' (fun j _ ↦ Nat.one_le_iff_ne_zero.mpr (hd.2 j))
    (Finset.mem_univ i)) hd.1

/-- **The empty tuple.** There is exactly one `0`-tuple, and its (empty) product is `1`, so it is
counted as soon as `N ≥ 1`. -/
theorem card_finMulAntidiagLE_zero {N : ℕ} (hN : 1 ≤ N) :
    #(Nat.finMulAntidiagLE (Fin 0) N) = 1 := by
  classical
  rw [Nat.finMulAntidiagLE, Finset.filter_true_of_mem fun d _ ↦ by simpa using hN,
    Fintype.card_piFinset]
  simp

/-! ### The hyperbola recursion -/

/-- **The recursion on the number of coordinates**, which is the Dirichlet hyperbola identity in
counting form: splitting an `(r+1)`-tuple at its first coordinate `a` — which ranges over `[1,N]` —
leaves an `r`-tuple whose product is at most `⌊N/a⌋`.

This is a fibrewise cardinality for the map `d ↦ d 0`, together with the bijection
`d ↦ Fin.tail d` on each fibre. -/
theorem card_finMulAntidiagLE_succ (r N : ℕ) :
    #(Nat.finMulAntidiagLE (Fin (r + 1)) N)
      = ∑ a ∈ Finset.Icc 1 N, #(Nat.finMulAntidiagLE (Fin r) (N / a)) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun d : Fin (r + 1) → ℕ ↦ d 0)
    (t := Finset.Icc 1 N) fun d hd ↦ Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr ((Nat.mem_finMulAntidiagLE_iff.mp hd).2 0),
        coord_le_of_mem_finMulAntidiagLE hd 0⟩]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have ha1 : 0 < a := (Finset.mem_Icc.mp ha).1
  refine Finset.card_nbij' (fun d ↦ Fin.tail d) (fun v ↦ Fin.cons a v) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_finMulAntidiagLE_iff,
      Fin.prod_univ_succ] at hd
    obtain ⟨⟨hprod, hne⟩, rfl⟩ := hd
    exact Nat.mem_finMulAntidiagLE_iff.mpr
      ⟨(Nat.le_div_iff_mul_le ha1).mpr (by rwa [mul_comm]), fun i ↦ hne i.succ⟩
  · intro v hv
    rw [Finset.mem_coe, Nat.mem_finMulAntidiagLE_iff] at hv
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Fin.cons_zero, and_true,
      Nat.mem_finMulAntidiagLE_iff, Fin.prod_univ_succ, Fin.cons_succ, Fin.forall_fin_succ]
    exact ⟨mul_comm a _ ▸ (Nat.le_div_iff_mul_le ha1).mp hv.1, ha1.ne', hv.2⟩
  · intro d hd
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hd
    exact hd.2 ▸ Fin.cons_self_tail d
  · exact fun v _ ↦ Fin.tail_cons _ _

/-- **One coordinate.** There are exactly `N` positive integers at most `N`. -/
theorem card_finMulAntidiagLE_one (N : ℕ) : #(Nat.finMulAntidiagLE (Fin 1) N) = N := by
  rw [card_finMulAntidiagLE_succ, Finset.sum_congr rfl fun a ha ↦ card_finMulAntidiagLE_zero
    (N := N / a) ((Nat.one_le_div_iff (Finset.mem_Icc.mp ha).1).mpr (Finset.mem_Icc.mp ha).2)]
  simp

/-! ### The bound -/

/-- The harmonic bound in the shape used below: `∑_{a=1}^{N} 1/a ≤ 1 + log N`. This is Mathlib's
`harmonic_le_one_add_log`, restated over `ℝ`. -/
theorem sum_inv_Icc_le (N : ℕ) : ∑ a ∈ Finset.Icc 1 N, ((a : ℝ))⁻¹ ≤ 1 + Real.log N := by
  simpa [harmonic_eq_sum_Icc] using harmonic_le_one_add_log N

/-- **The divisor-moment bound in counting form**, sharp and with constant `1`:

  `#{(d₁,…,d_{r+1}) : dᵢ ≥ 1, ∏ᵢ dᵢ ≤ N} ≤ N · (1 + log N)^r`.

Here `Nat.finMulAntidiagLE (Fin (r+1)) N` is this Finset. -/
theorem card_finMulAntidiagLE_le (r N : ℕ) :
    (#(Nat.finMulAntidiagLE (Fin (r + 1)) N) : ℝ) ≤ (N : ℝ) * (1 + Real.log N) ^ r := by
  induction r generalizing N with
  | zero => rw [card_finMulAntidiagLE_one]; simp
  | succ r ih =>
    calc (#(Nat.finMulAntidiagLE (Fin (r + 1 + 1)) N) : ℝ)
        = ∑ a ∈ Icc 1 N, (#(Nat.finMulAntidiagLE (Fin (r + 1)) (N / a)) : ℝ) := by
          rw [card_finMulAntidiagLE_succ]; push_cast; rfl
      _ ≤ ∑ a ∈ Icc 1 N, (N : ℝ) * (1 + Real.log N) ^ r * ((a : ℝ))⁻¹ := by
          refine sum_le_sum fun a ha ↦ (ih (N / a)).trans ?_
          obtain ⟨ha1, haN⟩ := mem_Icc.mp ha
          rw [mul_right_comm, ← div_eq_mul_inv]
          gcongr
          exacts [Nat.cast_div_le, by exact_mod_cast Nat.div_pos haN ha1, Nat.div_le_self N a]
      _ ≤ (N : ℝ) * (1 + Real.log N) ^ r * (1 + Real.log N) := by
          rw [← mul_sum]; gcongr; exact sum_inv_Icc_le N
      _ = (N : ℝ) * (1 + Real.log N) ^ (r + 1) := by ring

/-! ### The count is the divisor moment -/

/-- **`∑_{m ≤ N} τ_r(m)` counts the `r`-tuples of product at most `N`.** Grouping the tuples by
their product, the fibre over `m` is `Nat.finMulAntidiag r m`, whose cardinality is `τ_r(m)` by
`ArithmeticFunction.tau_apply_eq_card_finMulAntidiag`.

This replaces the Dirichlet hyperbola identity: with the divisor moment written as a tuple count,
the recursion in `r` is `Gap212.Sieve.card_finMulAntidiagLE_succ`. -/
theorem sum_tau_eq_card_finMulAntidiagLE (r N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (τ r) m = #(Nat.finMulAntidiagLE (Fin r) N) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun d : Fin r → ℕ ↦ ∏ i, d i)
    (t := Finset.Icc 1 N) fun d hd ↦ ?_]
  · refine Finset.sum_congr rfl fun m hm ↦ ?_
    rw [ArithmeticFunction.tau_apply_eq_card_finMulAntidiag]
    congr 1
    ext d
    simp only [Finset.mem_filter, Nat.mem_finMulAntidiagLE_iff, Nat.mem_finMulAntidiag]
    refine ⟨fun h ↦ ⟨⟨h.1 ▸ (mem_Icc.mp hm).2, fun i hi ↦ ?_⟩, h.1⟩, fun h ↦ ⟨h.2, by grind⟩⟩
    exact h.2 (h.1 ▸ prod_eq_zero (mem_univ i) hi)
  · rw [Finset.mem_coe, Nat.mem_finMulAntidiagLE_iff] at hd
    exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero (prod_ne_zero_iff.mpr fun i _ ↦ hd.2 i), hd.1⟩

/-- **The divisor-moment bound.**

  `∑_{m=1}^{N} τ_{r+1}(m) ≤ N · (1 + log N)^r`,

with constant `1` and valid at every `N`.

This is the estimate usually quoted as `∑_{m ≤ x^S} τ_{2k}(m) ≪ x^S(\log x)^{2k-1}`. -/
theorem sum_tau_le (r N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, (τ (r + 1)) m : ℝ) ≤ (N : ℝ) * (1 + Real.log N) ^ r := by
  rw [← Nat.cast_sum, sum_tau_eq_card_finMulAntidiagLE]
  exact card_finMulAntidiagLE_le r N

/-- **The divisor-moment bound at `r = 2k`:**
`∑_{m ≤ N} τ_{2k}(m) ≤ N (1 + log N)^{2k-1}` — which at `N = ⌊x^S⌋` is
`≪ x^S(\log x)^{2k-1}`, since `log(x^S) = S log x`. -/
theorem sum_tau_two_mul_le {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, (τ (2 * k)) m : ℝ) ≤ (N : ℝ) * (1 + Real.log N) ^ (2 * k - 1) := by
  have := sum_tau_le (2 * k - 1) N
  rwa [Nat.sub_add_cancel (by omega)] at this

end Gap212.Sieve

end
