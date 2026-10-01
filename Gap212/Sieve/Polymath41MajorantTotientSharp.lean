/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41MajorantTotient

/-!
# The totient kernel's Fubini majorant at the source's rate

`Gap212.Sieve.tsum_pairTotientMajorant_le` bounds the totient kernel's pair sum by `Z(1+σ)⁶`, which
is enough for the interchange but is `log⁶x` at `σ = 1/log x` where the source has `log³x`. The
whole of that loss sits in `Gap212.Sieve.totientKernelSeries_le`, `T(σ) ≤ Z(1+σ)²`, which bounds
one `1/φ(n)` by `τ₂(n)/n` and so pays a whole extra `ζ`. This file removes it:

  `T(σ) ≤ Z(1+σ) · T(1+σ) ≤ Z(1+σ) · Z(2)²`

(`Gap212.Sieve.totientKernelSeries_le_mul`, `Gap212.Sieve.totientKernelSeries_le_sharp`), whence

  `∑_{d,d'} |μ(d)μ(d')| / (φ([d,d']) d^σ (d')^σ) ≤ Z(2)⁶ · Z(1+σ)³`

(`Gap212.Sieve.tsum_pairTotientMajorant_le_sharp`) — the reciprocal kernel's own `Z(1+σ)³`, up to
the absolute constant `Z(2)⁶ = ζ(2)⁶ = (π²/6)⁶`. At `σ = 1/log x` this is `≪ log³x`, so the totient
side of step 2 matches the source's stated bound and not merely its finiteness.

## The mechanism: one Dirichlet factor is *shifted*, not spent

The identity behind it is `n/φ(n) = ∑_{e ∣ n} μ(e)²/φ(e)`
(`ArithmeticFunction.sum_moebius_sq_div_totient`), exact for every `n` and needing no
squarefreeness. Feeding it into `T(σ) = ∑_n |μ(n)|/(φ(n)n^σ) ≤ ∑_n (n/φ(n)) n^{-(1+σ)}` and
splitting `n = e·f` turns the single sum into a double one whose two variables separate: `e`
carries `|μ(e)|/(φ(e)e^{1+σ})` and `f` carries `f^{-(1+σ)}`, so

  `T(σ) ≤ T(1+σ) · Z(1+σ)`.

The point is that the surviving totient factor is `T` at `1+σ`, not at `σ` — a series whose terms
are `O(n^{-2+ε})` and which is therefore bounded by an absolute constant, uniformly as `σ → 0`. The
crude `T(σ) ≤ Z(1+σ)²` of `Gap212.Sieve.totientKernelSeries_le` is then applied *there*, where the
extra `ζ` it costs is `Z(2+σ)² ≤ Z(2)²` and costs nothing in `σ`. So the loss is not removed but
relocated to a place where it is `O(1)`.

In Lean the splitting is a sum over the pairs `e ∣ n`, i.e. over `(n : ℕ) × n.divisors`, injected
into `ℕ × ℕ` by `Gap212.Sieve.divisorSplit`, `⟨n, e⟩ ↦ (e, n/e)`. That map is injective, since
`n = e·(n/e)` recovers `n`, and `Gap212.Sieve.tsum_fiber_divisorSplit` evaluates its fibre over `n`
as exactly `n^{-(1+σ)}·(n/φ(n))`, which is where the divisor identity is consumed.

## `p = 2`

No oddness hypothesis is needed: `∑_{e ∣ n} μ(e)²/φ(e) = n/φ(n)` is an identity
valid at every `n`, with local factor `1 + 1/(p-1)` at `p`, which at `p = 2` is `2` — finite and
nonzero. The object whose local factor vanishes at `p = 2` is `(μ * φ)`, which does not appear here
either.

## Main results

* `Gap212.Sieve.totientKernelSeries_le_mul`: `T(σ) ≤ Z(1+σ)·T(1+σ)`.
* `Gap212.Sieve.totientKernelSeries_le_sharp`: `T(σ) ≤ Z(1+σ)·Z(2)²`.
* `Gap212.Sieve.tsum_pairTotientMajorant_le_sharp`: `Z(2)⁶·Z(1+σ)³` for the pair sum.
-/

@[expose] public section

namespace Gap212.Sieve

open Real
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ## `|μ|` as `μ²`, and the divisor expansion of `n/φ(n)` -/

/-- `|μ(n)| = μ(n)²` over `ℝ`: both are the indicator of squarefreeness. -/
theorem abs_moebius_eq_sq (n : ℕ) : |(μ n : ℝ)| = (μ n : ℝ) ^ 2 := by
  exact_mod_cast ArithmeticFunction.abs_moebius.trans ArithmeticFunction.moebius_sq.symm

/-- **The divisor expansion of `n/φ(n)`** in the `|μ|` spelling this file uses:
`∑_{e ∣ n} |μ(e)|/φ(e) = n/φ(n)`, an identity for every `n`
(`ArithmeticFunction.sum_moebius_sq_div_totient`). -/
theorem sum_divisors_abs_moebius_div_totient (n : ℕ) :
    ∑ e ∈ n.divisors, |(μ e : ℝ)| / (e.totient : ℝ) = (n : ℝ) / (n.totient : ℝ) := by
  rw [← ArithmeticFunction.sum_moebius_sq_div_totient (α := ℝ) (n := n)]
  exact Finset.sum_congr rfl fun e _ ↦ by rw [abs_moebius_eq_sq]

/-! ## The separated two-variable term, and the divisor injection -/

/-- **The separated term**: `T`'s term at `e` with exponent `1+σ`, against `f^{-(1+σ)}`. Its sum
over `ℕ × ℕ` is `T(1+σ)·Z(1+σ)`. -/
noncomputable def pairShiftedTerm (σ : ℝ) (y : ℕ × ℕ) : ℝ :=
  totientKernelTerm (1 + σ) y.1 * (y.2 : ℝ) ^ (-(1 + σ))

/-- **The divisor splitting** `⟨n, e⟩ ↦ (e, n/e)`, defined on the pairs `e ∣ n`. -/
def divisorSplit (x : (n : ℕ) × ↥(n.divisors)) : ℕ × ℕ := ((x.2 : ℕ), x.1 / (x.2 : ℕ))

/-- **`Gap212.Sieve.divisorSplit` is injective**: `e` and `n/e` multiply back to `n`, since `e ∣ n`
and `n ≠ 0` on the index set. -/
theorem divisorSplit_injective : Function.Injective divisorSplit := by
  rintro ⟨n, e, he⟩ ⟨m, f, hf⟩ h
  simp only [divisorSplit, Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  obtain rfl : n = m := by
    rw [← Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he), h2,
      Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hf)]
  rfl

/-- Every term `pairShiftedTerm σ y` is nonnegative. -/
theorem pairShiftedTerm_nonneg (σ : ℝ) (y : ℕ × ℕ) : 0 ≤ pairShiftedTerm σ y :=
  mul_nonneg (totientKernelTerm_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- For `σ > 0` the family `pairShiftedTerm σ` is summable over `ℕ × ℕ`. -/
theorem summable_pairShiftedTerm {σ : ℝ} (hσ : 0 < σ) : Summable (pairShiftedTerm σ) :=
  (summable_totientKernelTerm (by linarith : (0:ℝ) < 1 + σ)).mul_of_nonneg
    (summable_natRpow_neg (by linarith : (1:ℝ) < 1 + σ))
    (totientKernelTerm_nonneg _) (fun n ↦ natRpow_neg_nonneg _ n)

/-- `∑_{e,f} |μ(e)|/(φ(e)e^{1+σ}) · f^{-(1+σ)} = T(1+σ)·Z(1+σ)`. -/
theorem tsum_pairShiftedTerm {σ : ℝ} (hσ : 0 < σ) :
    ∑' y, pairShiftedTerm σ y = totientKernelSeries (1 + σ) * zetaSeries (1 + σ) := by
  simp only [pairShiftedTerm, totientKernelSeries, zetaSeries]
  exact (tsum_mul_tsum_of_summable_norm
    (summable_norm_totientKernelTerm (by linarith : (0:ℝ) < 1 + σ))
    (summable_norm_natRpow_neg (by linarith : (1:ℝ) < 1 + σ))).symm

/-! ## The fibre of the splitting, and the shifted bound -/

/-- **The fibre of `Gap212.Sieve.divisorSplit` over `n`** sums to `n^{-(1+σ)}·(n/φ(n))`: each
divisor `e` contributes `|μ(e)|/(φ(e) n^{1+σ})`, because `e^{1+σ}(n/e)^{1+σ} = n^{1+σ}`, and the
divisor sum of `|μ(e)|/φ(e)` is `n/φ(n)`. This is the step that consumes the identity. -/
theorem tsum_fiber_divisorSplit (σ : ℝ) (n : ℕ) :
    ∑' e : ↥(n.divisors), pairShiftedTerm σ (divisorSplit ⟨n, e⟩)
      = (n : ℝ) ^ (-(1 + σ)) * ((n : ℝ) / (n.totient : ℝ)) := by
  simp only [divisorSplit]
  rw [Finset.tsum_subtype n.divisors fun e : ℕ ↦ pairShiftedTerm σ (e, n / e)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have key : ∀ e ∈ n.divisors,
      pairShiftedTerm σ (e, n / e) = (n : ℝ) ^ (-(1 + σ)) * (|(μ e : ℝ)| / (e.totient : ℝ)) := by
    intro e he
    have hed := Nat.dvd_of_mem_divisors he
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos hed hn
    have heR : (0 : ℝ) < e := by exact_mod_cast he0
    have hqR : (0 : ℝ) < ((n / e : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_pos (Nat.le_of_dvd hn hed) he0
    have hphi : (0 : ℝ) < e.totient := by exact_mod_cast Nat.totient_pos.2 he0
    have hmul : (n : ℝ) ^ (1 + σ) = (e : ℝ) ^ (1 + σ) * ((n / e : ℕ) : ℝ) ^ (1 + σ) := by
      rw [← Real.mul_rpow heR.le hqR.le, ← Nat.cast_mul, Nat.mul_div_cancel' hed]
    simp only [pairShiftedTerm, totientKernelTerm]
    rw [Real.rpow_neg hqR.le, Real.rpow_neg hnR.le, hmul]
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, sum_divisors_abs_moebius_div_totient]

/-- Every term of `T(σ)` is at most its fibre sum: `|μ(n)| ≤ 1` and
`n^{-(1+σ)}(n/φ(n)) = 1/(φ(n)n^σ)`. -/
theorem totientKernelTerm_le_tsum_fiber (σ : ℝ) (n : ℕ) :
    totientKernelTerm σ n ≤ ∑' e : ↥(n.divisors), pairShiftedTerm σ (divisorSplit ⟨n, e⟩) := by
  rw [tsum_fiber_divisorSplit]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [totientKernelTerm]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hphi : (0 : ℝ) < (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.2 hn
  have hrp : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnR _
  have hsplit : (n : ℝ) ^ (-(1 + σ)) * ((n : ℝ) / (n.totient : ℝ))
      = 1 / ((n.totient : ℝ) * (n : ℝ) ^ σ) := by
    rw [Real.rpow_neg hnR.le, Real.rpow_add hnR, Real.rpow_one]
    field_simp
  have hmu : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [hsplit, totientKernelTerm]
  gcongr

/-- **The shifted bound `T(σ) ≤ Z(1+σ)·T(1+σ)`**, for every `σ > 0`. The totient factor survives at
the *shifted* exponent `1+σ`, where it is `O(1)` uniformly in `σ`; that is what makes this sharp in
`σ` where `Gap212.Sieve.totientKernelSeries_le` is not. -/
theorem totientKernelSeries_le_mul {σ : ℝ} (hσ : 0 < σ) :
    totientKernelSeries σ ≤ zetaSeries (1 + σ) * totientKernelSeries (1 + σ) := by
  have hFs : Summable (pairShiftedTerm σ) := summable_pairShiftedTerm hσ
  have hh : Summable (pairShiftedTerm σ ∘ divisorSplit) :=
    hFs.comp_injective divisorSplit_injective
  obtain ⟨hfib1, hfib2⟩ :=
    (summable_sigma_of_nonneg (f := pairShiftedTerm σ ∘ divisorSplit)
      (fun x ↦ pairShiftedTerm_nonneg σ _)).1 hh
  calc totientKernelSeries σ
      ≤ ∑' n : ℕ, ∑' e : ↥(n.divisors), (pairShiftedTerm σ ∘ divisorSplit) ⟨n, e⟩ :=
        Summable.tsum_le_tsum (fun n ↦ totientKernelTerm_le_tsum_fiber σ n)
          (summable_totientKernelTerm hσ) hfib2
    _ = ∑' x, (pairShiftedTerm σ ∘ divisorSplit) x := (Summable.tsum_sigma' hfib1 hh).symm
    _ ≤ ∑' y, pairShiftedTerm σ y :=
        tsum_comp_le_tsum_of_inj hFs (pairShiftedTerm_nonneg σ) divisorSplit_injective
    _ = zetaSeries (1 + σ) * totientKernelSeries (1 + σ) := by
        rw [tsum_pairShiftedTerm hσ, mul_comm]

/-- **`T(σ) ≤ Z(1+σ)·Z(2)²`**: the shifted factor `T(1+σ)` is bounded by `Z(2+σ)² ≤ Z(2)²`, an
absolute constant. So `T(σ) ≍ 1/σ` up to a constant, as it should be. -/
theorem totientKernelSeries_le_sharp {σ : ℝ} (hσ : 0 < σ) :
    totientKernelSeries σ ≤ zetaSeries (1 + σ) * zetaSeries 2 ^ 2 := by
  refine (totientKernelSeries_le_mul hσ).trans ?_
  have hz : 0 ≤ zetaSeries (1 + σ) := tsum_nonneg fun n ↦ natRpow_neg_nonneg _ n
  have h1 := totientKernelSeries_le (σ := 1 + σ) (by linarith)
  rw [show (1 : ℝ) + (1 + σ) = 2 + σ by ring] at h1
  have h2 : zetaSeries (2 + σ) ≤ zetaSeries 2 := zetaSeries_antitone (by norm_num) (by linarith)
  have h2nn : 0 ≤ zetaSeries (2 + σ) := tsum_nonneg fun n ↦ natRpow_neg_nonneg _ n
  gcongr
  exact h1.trans (by gcongr)

/-- **The totient kernel's Fubini bound at the source's rate**: for every `σ > 0`,

  `∑_{d,d'} |μ(d)μ(d')| / (φ([d,d']) d^σ (d')^σ) ≤ Z(2)⁶ · Z(1+σ)³`.

The `σ`-dependence is the reciprocal kernel's own `Z(1+σ)³` of
`Gap212.Sieve.tsum_pairMajorant_le`; the price of the totient kernel is the absolute constant
`Z(2)⁶`, not a power of `log x`. At `σ = 1/log x` this is `≪ log³x`, the source's bound. -/
theorem tsum_pairTotientMajorant_le_sharp {σ : ℝ} (hσ : 0 < σ) :
    ∑' p, pairTotientMajorant σ p ≤ zetaSeries 2 ^ 6 * zetaSeries (1 + σ) ^ 3 := by
  refine (tsum_pairTotientMajorant_le_mul hσ).trans ?_
  have hz : 0 ≤ zetaSeries (1 + σ) := tsum_nonneg fun n ↦ natRpow_neg_nonneg _ n
  have hz2 : 0 ≤ zetaSeries 2 := tsum_nonneg fun n ↦ natRpow_neg_nonneg _ n
  have hT := totientKernelSeries_le_sharp hσ
  have hT2 : totientKernelSeries (2 * σ) ≤ zetaSeries (1 + σ) * zetaSeries 2 ^ 2 :=
    (totientKernelSeries_le_sharp (by linarith)).trans
      (by gcongr; exact zetaSeries_antitone (by linarith) (by linarith))
  have hT0 := totientKernelSeries_nonneg σ
  have hT20 := totientKernelSeries_nonneg (2 * σ)
  calc _ ≤ zetaSeries (1 + σ) * zetaSeries 2 ^ 2 *
          (zetaSeries (1 + σ) * zetaSeries 2 ^ 2 * (zetaSeries (1 + σ) * zetaSeries 2 ^ 2)) := by
        gcongr
    _ = zetaSeries 2 ^ 6 * zetaSeries (1 + σ) ^ 3 := by ring

end Gap212.Sieve
