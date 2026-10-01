/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Defs
public import Gap212.Sieve.GPYDefs
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public meta import Gap212.Attr

/-!
# The pre-sieving modulus: its size, and what it makes coprime

The four elementary facts about `W(x) = ∏_{p ≤ log log log x} p` the sieve's averaging step spends:
that `W(x)` is small, that it nevertheless absorbs every prime up to the tuple's diameter, and the
two coprimality statements those two facts buy for the shifts of a pre-sieved residue class.

## Why `4 ^ n` and not `w₀ log w₀`

The elementary bound on `log W(x)` is `w₀ log w₀`, counting at most `w₀` primes below `w₀ = log log
log x` and `log p ≤ log w₀` for each. Mathlib already has the sharper `primorial_le_four_pow`, so
the bound used here is `W(x) ≤ 4^{⌊w₀⌋}`, and what remains to check is `(log 4)(log u) ≤ u` at
`u = log log x` — one application of `Real.isLittleO_log_id_atTop`. Both routes reduce to "a double
logarithm beats a single one"; this one borrows the prime counting instead of redoing it.

## The two coprimality statements

They are different facts and they need different hypotheses. Coprimality to `W(x)` is pure
transport: a congruence modulo `W(x)` does not move a gcd with `W(x)`, so it holds at every `x`.
Pairwise coprimality of the shifts needs `W(x)` to contain every prime up to the diameter — a prime
dividing two shifts divides their difference, which is a nonzero integer bounded by the diameter —
and that is the hypothesis `Gap212.Sieve.eventually_dvd_W_of_prime_le` supplies for large `x`.

## Main results

* `Gap212.Sieve.W_le_log`: `W(x) ≤ log x` for large `x`.
* `Gap212.Sieve.eventually_dvd_W_of_prime_le`: every prime `p ≤ D` divides `W(x)` for large `x`.
* `Gap212.Sieve.coprime_W_of_modEq`: the shifts of a pre-sieved class are coprime to `W(x)`.
* `Gap212.Sieve.coprime_shifts_of_modEq`: those shifts are pairwise coprime.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.Defs Gap212.GPY

/-! ## The size of the pre-sieving modulus -/

/-- **The pre-sieving modulus is small**: `W(x) ≤ log x` for every large `x`.

`W(x) = ⌊w₀⌋# ≤ 4^{⌊w₀⌋} ≤ 4^{w₀}` with `w₀ = log log log x`, and `4^{w₀} = exp(w₀ log 4)` is at
most `exp(log log x) = log x` as soon as `(log 4)(log u) ≤ u` at `u = log log x`, which is
`Real.isLittleO_log_id_atTop` with the constant `1 / log 4`. -/
@[gap212 "lem_wsieve_size"]
theorem W_le_log : ∀ᶠ x : ℝ in atTop, (W x : ℝ) ≤ Real.log x := by
  have hl4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have key : ∀ᶠ u : ℝ in atTop, Real.log 4 * Real.log u ≤ u ∧ 1 ≤ u := by
    have hb := Real.isLittleO_log_id_atTop.bound (c := 1 / Real.log 4) (by positivity)
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with u hu hu1
    refine ⟨?_, hu1⟩
    rwa [id_eq, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ u),
      Real.norm_of_nonneg (Real.log_nonneg hu1), one_div_mul_eq_div, le_div_iff₀' hl4] at hu
  have hcomp : ∀ᶠ x : ℝ in atTop, Real.log 4 * Real.log (Real.log (Real.log x))
      ≤ Real.log (Real.log x) ∧ 1 ≤ Real.log (Real.log x) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually key
  filter_upwards [hcomp, eventually_gt_atTop (1 : ℝ)] with x ⟨hkey, hu1⟩ hx1
  set u := Real.log (Real.log x)
  calc (W x : ℝ) ≤ ((4 : ℕ) ^ (⌊Real.log u⌋₊ : ℕ) : ℕ) := by
        exact_mod_cast primorial_le_four_pow _
    _ = (4 : ℝ) ^ ((⌊Real.log u⌋₊ : ℕ) : ℝ) := by push_cast [Real.rpow_natCast]; ring
    _ ≤ (4 : ℝ) ^ Real.log u :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le (Real.log_nonneg hu1))
    _ = Real.exp (Real.log u * Real.log 4) := by
        rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
    _ ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
    _ = Real.log x := Real.exp_log (Real.log_pos hx1)

/-! ## The small primes it absorbs -/

/-- **The pre-sieving modulus absorbs the small primes**: for every `D` and every large `x`, every
prime `p ≤ D` divides `W(x)`.

`log log log x → ∞`, so eventually `D ≤ ⌊log log log x⌋`, and a prime divides a primorial exactly
when it is below the bound (`Nat.Prime.dvd_primorial_iff`). -/
@[gap212 "lem_wsieve_contains_diameter"]
theorem eventually_dvd_W_of_prime_le (D : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ p : ℕ, p.Prime → p ≤ D → p ∣ W x := by
  have h3 : Tendsto (fun x : ℝ ↦ Real.log (Real.log (Real.log x))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [h3.eventually_ge_atTop (D : ℝ)] with x hx p hp hpD
  exact hp.dvd_primorial_iff.2 (hpD.trans (Nat.le_floor hx))

/-! ## The two coprimality statements -/

/-- **The shifts are coprime to the pre-sieving modulus.** If `b` is a pre-sieved residue and
`n ≡ b (mod W(x))`, then `n + hᵢ` is coprime to `W(x)` for every `i`.

A congruence modulo `W(x)` survives a shift and does not move a gcd with `W(x)`
(`Nat.ModEq.gcd_eq`), so this is the pre-sieved property of `b` read at `n`. No largeness of `x` is
involved. -/
@[gap212 "lem_shift_coprime_to_W"]
theorem coprime_W_of_modEq {k : ℕ} {b n : ℕ} {h : Fin k → ℕ} {x : ℝ}
    (hb : IsPreSieved b (W x) h) (hn : n ≡ b [MOD W x]) (i : Fin k) :
    Nat.Coprime (n + h i) (W x) :=
  ((hn.add_right (h i)).gcd_eq).trans (hb i)

/-- **The shifts are pairwise coprime.** For a strictly increasing tuple `h` whose diameter's
primes all divide `W(x)`, a pre-sieved residue `b` and `n ≡ b (mod W(x))`, the integers `n + hᵢ`
are pairwise coprime.

A prime `q` dividing `n + hᵢ` and `n + h_{i'}` divides the difference `h_{i'} - hᵢ`, which is
nonzero by strict monotonicity and at most the diameter; so `q ≤ D`, hence `q ∣ W(x)`, hence `q`
divides `gcd(n + hᵢ, W(x)) = 1` by `Gap212.Sieve.coprime_W_of_modEq`. -/
@[gap212 "lem_shifts_pairwise_coprime"]
theorem coprime_shifts_of_modEq {k : ℕ} {h : Fin k → ℕ} (hmono : StrictMono h) {x : ℝ}
    (hD : ∀ p : ℕ, p.Prime → p ≤ (Finset.image h Finset.univ).diameter → p ∣ W x)
    {b n : ℕ} (hb : IsPreSieved b (W x) h) (hn : n ≡ b [MOD W x])
    {i i' : Fin k} (hii : i ≠ i') : Nat.Coprime (n + h i) (n + h i') := by
  have core : ∀ j j' : Fin k, h j < h j' → Nat.Coprime (n + h j) (n + h j') := by
    intro j j' hlt
    refine Nat.coprime_of_dvd fun q hq hqj hqj' ↦ ?_
    have hne : (image h univ).Nonempty := ⟨h j, mem_image_of_mem h (mem_univ j)⟩
    have hdiff : q ∣ h j' - h j := by
      simpa [Nat.add_sub_add_left] using Nat.dvd_sub hqj' hqj
    have hle : h j' - h j ≤ (image h univ).diameter :=
      (tsub_le_tsub (le_max' _ _ (mem_image_of_mem h (mem_univ j')))
        (min'_le _ _ (mem_image_of_mem h (mem_univ j)))).trans_eq
        (diameter_eq_max_sub_min hne).symm
    have hqW : q ∣ W x := hD q hq ((Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdiff).trans hle)
    exact hq.one_lt.ne' (Nat.eq_one_of_dvd_one ((coprime_W_of_modEq hb hn j) ▸
      Nat.dvd_gcd hqj hqW))
  rcases lt_or_gt_of_ne (hmono.injective.ne hii) with hlt | hgt
  · exact core i i' hlt
  · exact (core i' i hgt).symm

end Gap212.Sieve
