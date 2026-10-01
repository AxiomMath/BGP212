/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Ring
public meta import Gap212.Attr

/-!
# The smooth reservoir: a smooth number has a divisor in any wide-enough window

All three factor-extraction lemmas end the same way. The rough factors are placed
into bins by the packing condition, which lands the partial product somewhere below the target
window; the `x^δ`-smooth part `ee'` is then used as a *reservoir*, contributing prime factors one
at a time until the product enters the window. Because each available prime is at most `x^δ`, a
window of multiplicative width `x^δ` cannot be jumped over.

This module isolates that step. The clean formulation is multiplicative and involves no logarithms:

> if every prime factor of `n` is at most `S`, and `A ≤ n`, then `n` has a divisor in `[A, A·S]`.

The proof is the same minimal-witness trick as `Gap212.Packing.exists_subset_sum_mem_Icc`, but on
divisibility rather than on sums: take the **smallest** divisor `d` of `n` with `d ≥ A`. If `d > 1`
pick a prime `p ∣ d`; then `d / p` is a smaller divisor of `n`, so by minimality `d / p < A`, and
therefore `d = p · (d / p) < p · A ≤ S · A`. No greedy iteration, no induction on a factorization.

## Main results

* `Gap212.Packing.exists_divisor_mem_Icc`: the reservoir lemma over `ℕ`.
* `Gap212.Packing.exists_divisor_mem_Icc_real`: the same with a real target and real smoothness
  bound, which is the form the extraction workhorse needs.
* `Gap212.Packing.exists_divisor_mem_Icc_real_strict`: the same with **both ends strict**, which is
  what an open window `(x^a, x^b)` needs.
* `Gap212.Packing.exists_divisor_mem_Icc_rpow`: the exponent form, window `[x^a, x^(a+δ)]`.
* `Gap212.Packing.exists_divisor_window_witness`: the extraction workhorse, with the consumed part
  of the reservoir exposed — needed when drawing from the reservoir twice.
* `Gap212.Packing.exists_divisor_window`: its bare-existence corollary.
* `Gap212.Packing.exists_divisor_window_witness_strict` and
  `Gap212.Packing.exists_divisor_window_strict`: the same two with an **open** window, which is
  what membership in a modulus family asks for.
* `Gap212.Packing.exists_two_divisors_window`: two divisors in prescribed windows, drawing twice
  from one reservoir.
* `Gap212.Packing.exists_two_divisors_window_strict`: the same with **both windows open**, which is
  what the nested modulus families `D_IIb` and `D_IIc` ask for.
-/

@[expose] public section

namespace Gap212.Packing

open Finset

/-- The minimal-witness step shared by the reservoir lemmas: among the divisors of `n ≠ 0`
satisfying `P`, where `P n` holds, the least one `d` is either `1` or has a prime factor `p` whose
cofactor `d / p`, a strictly smaller divisor of `n`, fails `P`. -/
private lemma exists_minimal_divisor {n : ℕ} {P : ℕ → Prop} (hn : n ≠ 0) (hPn : P n) :
    ∃ d, d ∣ n ∧ P d ∧ (d = 1 ∨ ∃ p, p.Prime ∧ p ∣ d ∧ ¬ P (d / p)) := by
  classical
  have h : ∃ d, d ∣ n ∧ P d := ⟨n, dvd_rfl, hPn⟩
  obtain ⟨hdn, hPd⟩ := Nat.find_spec h
  refine ⟨_, hdn, hPd, or_iff_not_imp_left.2 fun hd1 ↦ ?_⟩
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
  refine ⟨p, hp, hpd, fun hP ↦ ?_⟩
  have hd0 : 0 < Nat.find h := Nat.pos_of_ne_zero fun h0 ↦ hn (Nat.eq_zero_of_zero_dvd (h0 ▸ hdn))
  exact (Nat.div_lt_self hd0 hp.one_lt).not_ge
    (Nat.find_min' h ⟨(Nat.div_dvd_of_dvd hpd).trans hdn, hP⟩)

/-- **The reservoir lemma.** If every prime factor of `n` is at most `S`, and `A ≤ n`, then `n` has
a divisor in `[A, A·S]`.

A window of multiplicative width `S` cannot be jumped over by multiplying in factors that are each
at most `S`. -/
theorem exists_divisor_mem_Icc {n S A : ℕ} (hn : 1 ≤ n) (hS : 1 ≤ S) (hA : 1 ≤ A) (hAn : A ≤ n)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ S) :
    ∃ d, d ∣ n ∧ A ≤ d ∧ d ≤ A * S := by
  -- Take the least divisor `d` of `n` reaching `A`; if `d = 1` then `A = 1`.
  obtain ⟨d, hdn, hdA, rfl | ⟨p, hp, hpd, hlt⟩⟩ :=
    exists_minimal_divisor (P := (A ≤ ·)) (by omega) hAn
  · exact ⟨1, hdn, hdA, by nlinarith⟩
  -- Otherwise `d / p` misses `A` by minimality, hence `d = p · (d / p) < p · A ≤ S · A`.
  refine ⟨d, hdn, hdA, ?_⟩
  rw [← Nat.mul_div_cancel' hpd, mul_comm A]
  exact Nat.mul_le_mul (hsmooth p hp (hpd.trans hdn)) (not_le.1 hlt).le

/-! ## The reservoir with a general real target

The exponent form above takes the target to be a power of `x`. The factor-extraction lemmas need an
arbitrary real target, because the rough part already chosen has been divided out. -/

/-- **The reservoir lemma, real target.** If every prime factor of `n` is at most `S`, and the real
target `A > 1` satisfies `A ≤ n`, then `n` has a divisor in `[A, A·S]`. -/
theorem exists_divisor_mem_Icc_real {n : ℕ} {A S : ℝ} (hn : 1 ≤ n)
    (hA : 1 < A) (hAn : A ≤ (n : ℝ)) (hS : 0 ≤ S)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ S) :
    ∃ d, d ∣ n ∧ A ≤ (d : ℝ) ∧ (d : ℝ) ≤ A * S := by
  obtain ⟨d, hdn, hdA, rfl | ⟨p, hp, hpd, hlt⟩⟩ :=
    exists_minimal_divisor (P := fun d : ℕ ↦ A ≤ (d : ℝ)) (by omega) hAn
  · -- `A > 1` forces `d > 1`.
    simp only [Nat.cast_one] at hdA
    linarith
  refine ⟨d, hdn, hdA, ?_⟩
  rw [← Nat.mul_div_cancel' hpd, Nat.cast_mul, mul_comm A]
  exact mul_le_mul (hsmooth p hp (hpd.trans hdn)) (not_le.1 hlt).le (Nat.cast_nonneg _) hS

/-- **The reservoir lemma with an open window.** If every prime factor of `n` is *strictly* below
`S`, and the real target `A ≥ 1` is *strictly* below `n`, then `n` has a divisor `d` with
`A < d < A·S`.

Each end's strictness has its own source, and neither costs anything that the non-strict form has.
The lower one comes from taking the least divisor lying strictly *above* `A`, which exists
precisely because `A < n`. The upper one comes from the smoothness bound being strict — which is
how the generated moduli state it, each prime of the smooth part being `< x^δ` — since the minimal
witness satisfies `d = p · (d/p) ≤ p · A < S · A`.

This is the shape an **open** divisor window `(x^a, x^b)` reduces to, and membership in any of the
modulus families is stated with open windows. -/
theorem exists_divisor_mem_Icc_real_strict {n : ℕ} {A S : ℝ} (hn : 1 ≤ n)
    (hA : 1 ≤ A) (hAn : A < (n : ℝ))
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) < S) :
    ∃ d, d ∣ n ∧ A < (d : ℝ) ∧ (d : ℝ) < A * S := by
  obtain ⟨d, hdn, hdA, rfl | ⟨p, hp, hpd, hle⟩⟩ :=
    exists_minimal_divisor (P := fun d : ℕ ↦ A < (d : ℝ)) (by omega) hAn
  · -- `1 ≤ A < d` forces `d > 1`.
    simp only [Nat.cast_one] at hdA
    linarith
  -- By minimality the cofactor `d / p` does not clear `A`.
  refine ⟨d, hdn, hdA, ?_⟩
  rw [← Nat.mul_div_cancel' hpd, Nat.cast_mul, mul_comm A]
  exact (mul_le_mul_of_nonneg_left (not_lt.1 hle) (Nat.cast_nonneg p)).trans_lt
    (mul_lt_mul_of_pos_right (hsmooth p hp (hpd.trans hdn)) (by linarith))

/-- **The reservoir lemma in exponent form.** If `n` is `x^δ`-smooth and `x^a ≤ n`, then `n` has a
divisor in `[x^a, x^(a+δ)]`.

This is the shape the factor extraction consumes: the smooth part supplies a divisor
anywhere in a window of logarithmic width `δ`, which is exactly why the partition conditions demand
windows of width at least `δ`. It is the real-target lemma at `A = x^a`, `S = x^δ`, using
`x^a · x^δ = x^{a+δ}`. -/
theorem exists_divisor_mem_Icc_rpow {n : ℕ} {x a δ : ℝ} (hx : 1 < x) (hn : 1 ≤ n)
    (ha : 1 < x ^ a) (han : x ^ a ≤ (n : ℝ))
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ x ^ δ) :
    ∃ d, d ∣ n ∧ x ^ a ≤ (d : ℝ) ∧ (d : ℝ) ≤ x ^ (a + δ) := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
  obtain ⟨d, hd, h1, h2⟩ :=
    exists_divisor_mem_Icc_real hn ha han (Real.rpow_nonneg hx0.le δ) hsmooth
  exact ⟨d, hd, h1, by rwa [← Real.rpow_add hx0] at h2⟩

/-! ## The extraction workhorse

This is the shape all three factor-extraction lemmas reduce to. The packing condition has already
selected a set of rough factors whose product `R` fits under `x^b`; `S` is the `x^δ`-smooth
reservoir; and the modulus being large enough is what guarantees `R · S ≥ x^a`, so the reservoir
can carry `R` up into the window. -/

/-- **Extraction, with the witness exposed.** The divisor produced is `R · s` for an explicit
`s ∣ S`, so the part of the reservoir that got consumed is visible.

Three-factor extraction needs this: it draws twice from the same reservoir, and the second draw
must avoid the primes the first one used. The bare existence statement below is not enough for
that. -/
theorem exists_divisor_window_witness {R S : ℕ} {x a b δ : ℝ}
    (hx : 1 < x) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hRb : (R : ℝ) ≤ x ^ b)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ S → (p : ℝ) ≤ x ^ δ)
    (hbig : x ^ a ≤ ((R * S : ℕ) : ℝ)) (hwidth : a + δ ≤ b) :
    ∃ s, s ∣ S ∧ x ^ a ≤ ((R * s : ℕ) : ℝ) ∧ ((R * s : ℕ) : ℝ) ≤ x ^ b := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
  have hR0 : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  by_cases hcase : x ^ a ≤ (R : ℝ)
  · -- The rough part already reaches the window; nothing is drawn.
    exact ⟨1, one_dvd _, by simpa using hcase, by simpa using hRb⟩
  -- Draw from the reservoir, with target `x^a / R`.
  obtain ⟨s, hsS, hs1, hs2⟩ := exists_divisor_mem_Icc_real hS
    ((one_lt_div hR0).mpr (not_le.mp hcase))
    ((div_le_iff₀ hR0).2 (hbig.trans_eq (by push_cast; ring))) (Real.rpow_nonneg hx0.le δ) hsmooth
  have hab : x ^ a * x ^ δ ≤ x ^ b := by
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx.le hwidth
  refine ⟨s, hsS, ?_, ?_⟩ <;> rw [Nat.cast_mul]
  · exact (div_le_iff₀' hR0).1 hs1
  · exact (le_div_iff₀' hR0).1 (hs2.trans (by rw [div_mul_eq_mul_div]; gcongr))

/-- **Extraction of a divisor in a window.** Let `R · S ∣ q` with `S` `x^δ`-smooth, let `R ≤ x^b`,
and suppose `x^a ≤ R · S`. If the window is at least as wide as the smoothness, `a + δ ≤ b`, then
`q` has a divisor in `[x^a, x^b]`.

Note that `R · S` need only *divide* `q`, not equal it. In the factor-extraction lemmas the rough
factors the partition leaves *unselected* are part of the modulus but play no role in the divisor
being built, so demanding `q = R · S` would be too rigid; correspondingly the size hypothesis is on
`R · S` rather than on `q`.

Two cases, and both are short. Either `R` already reaches `x^a`, and then `R` itself is the divisor
since it is below `x^b`; or it does not, and the reservoir supplies a divisor `s` of `S` carrying
`R · s` into `[x^a, x^{a+δ}] ⊆ [x^a, x^b]`. The width hypothesis is used exactly once, in that last
inclusion — which is why the partition conditions demand windows of width at least `δ`.

No hypothesis `1 < x^a` is needed: in the second case it follows from `R < x^a` and `1 ≤ R`. -/
theorem exists_divisor_window {q R S : ℕ} {x a b δ : ℝ}
    (hx : 1 < x) (hdvd : R * S ∣ q) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hRb : (R : ℝ) ≤ x ^ b)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ S → (p : ℝ) ≤ x ^ δ)
    (hbig : x ^ a ≤ ((R * S : ℕ) : ℝ)) (hwidth : a + δ ≤ b) :
    ∃ r, r ∣ q ∧ x ^ a ≤ (r : ℝ) ∧ (r : ℝ) ≤ x ^ b := by
  obtain ⟨s, hsS, h1, h2⟩ := exists_divisor_window_witness hx hR hS hRb hsmooth hbig hwidth
  exact ⟨R * s, (mul_dvd_mul_left R hsS).trans hdvd, h1, h2⟩

/-! ## The same, with an open window

Membership in any of the modulus families asks for a divisor in an **open** window,
`x^a < r < x^b`. The two strict variants below produce one, from strict hypotheses the caller
already has: the selected rough part is `< x^b` because its logarithm is `(1 - ε₀)` times a
quantity bounded by `b`, and the reservoir together with it is `> x^a` because the modulus
threshold `ε₁` may be taken strictly below its bound. Nothing has to be pulled inward — in
particular the packing conditions are consumed at their bare capacities. -/

/-- **Extraction into an open window, with the witness exposed.** Same as
`Gap212.Packing.exists_divisor_window_witness`, with all three inequalities strict: `R < x^b`,
`x^a < R·S`, and the smoothness bound `p < x^δ` on the reservoir, as `Gap212.Qgen` states it.

The two cases are the two sources of strictness, and both are needed. If the rough part already
passes `x^a` *strictly*, it is itself the divisor and the strict cap `R < x^b` finishes — this is
where the retreat `(1 - ε₀)` earns its keep. Otherwise `R ≤ x^a`, the reservoir is drawn on with
target `x^a / R`, and `Gap212.Packing.exists_divisor_mem_Icc_real_strict` lands `R·s` strictly
inside `(x^a, x^{a+δ}] ⊆ (x^a, x^b]` — strictly below `x^b` because the smooth primes are below
`x^δ`. The width hypothesis `a + δ ≤ b` is unchanged, and in particular non-strict. -/
theorem exists_divisor_window_witness_strict {R S : ℕ} {x a b δ : ℝ}
    (hx : 1 < x) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hRb : (R : ℝ) < x ^ b)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ S → (p : ℝ) < x ^ δ)
    (hbig : x ^ a < ((R * S : ℕ) : ℝ)) (hwidth : a + δ ≤ b) :
    ∃ s, s ∣ S ∧ x ^ a < ((R * s : ℕ) : ℝ) ∧ ((R * s : ℕ) : ℝ) < x ^ b := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
  have hR0 : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  by_cases hcase : x ^ a < (R : ℝ)
  · -- The rough part already passes the window's lower end; nothing is drawn.
    exact ⟨1, one_dvd _, by simpa using hcase, by simpa using hRb⟩
  -- Draw from the reservoir, with target `x^a / R`.
  obtain ⟨s, hsS, hs1, hs2⟩ := exists_divisor_mem_Icc_real_strict hS
    ((one_le_div hR0).mpr (not_lt.mp hcase))
    ((div_lt_iff₀ hR0).2 (hbig.trans_eq (by push_cast; ring))) hsmooth
  have hab : x ^ a * x ^ δ ≤ x ^ b := by
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx.le hwidth
  refine ⟨s, hsS, ?_, ?_⟩ <;> rw [Nat.cast_mul]
  · exact (div_lt_iff₀' hR0).1 hs1
  · exact (lt_div_iff₀' hR0).1 (hs2.trans_le (by rw [div_mul_eq_mul_div]; gcongr))

/-- **Extraction of a divisor in an open window.** With `R · S ∣ q`, the reservoir `S` having every
prime strictly below `x^δ`, `R < x^b` and `x^a < R · S`, the modulus `q` has a divisor `r` with
`x^a < r < x^b`, provided `a + δ ≤ b`.

This is the form `Gap212.HasDivisorIn` is stated in, so it is what the containments
`Q ⊆ D_type` consume. Its non-strict sibling `Gap212.Packing.exists_divisor_window` cannot serve
there: a closed window forces the caller to run the extraction on a window strictly inside the
target, and the inward inset that costs is slack the packing conditions do not have. -/
theorem exists_divisor_window_strict {q R S : ℕ} {x a b δ : ℝ}
    (hx : 1 < x) (hdvd : R * S ∣ q) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hRb : (R : ℝ) < x ^ b)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ S → (p : ℝ) < x ^ δ)
    (hbig : x ^ a < ((R * S : ℕ) : ℝ)) (hwidth : a + δ ≤ b) :
    ∃ r, r ∣ q ∧ x ^ a < (r : ℝ) ∧ (r : ℝ) < x ^ b := by
  obtain ⟨s, hsS, h1, h2⟩ := exists_divisor_window_witness_strict hx hR hS hRb hsmooth hbig hwidth
  exact ⟨R * s, (mul_dvd_mul_left R hsS).trans hdvd, h1, h2⟩

/-! ## Drawing twice from one reservoir

Three-factor extraction wants two divisors of prescribed sizes *simultaneously*. The rough factors
are split into two selected parts `R₁`, `R₂` and a remainder; both draws come from the same smooth
reservoir, and the second must avoid whatever the first consumed. -/

/-- **Two divisors in prescribed windows.** With `R₁ · R₂ · S ∣ q`, `S` being `x^δ`-smooth,
`Rᵢ ≤ x^{bᵢ}`, and both windows at least as wide as the smoothness, `q` has divisors
`u ∈ [x^{a₂}, x^{b₂}]` and `r ∈ [x^{a₁}, x^{b₁}]` whose product still divides `q`.

The size hypotheses are asymmetric on purpose. The first draw needs only `x^{a₂} ≤ R₂ · S`. The
second draws from what is left, and since the first consumed at most `x^{b₂}` worth of the modulus,
what it needs is `x^{a₁ + b₂} ≤ R₁ · R₂ · S` — the `b₂` being exactly the price of the first draw.
That is where the caller uses the condition `b₁ - b₂ ≥ a₁ - a₂`. -/
theorem exists_two_divisors_window {q R₁ R₂ S : ℕ} {x a₁ b₁ a₂ b₂ δ : ℝ}
    (hx : 1 < x) (hdvd : R₁ * R₂ * S ∣ q)
    (hR₁ : 1 ≤ R₁) (hR₂ : 1 ≤ R₂) (hS : 1 ≤ S)
    (hR₁b : (R₁ : ℝ) ≤ x ^ b₁) (hR₂b : (R₂ : ℝ) ≤ x ^ b₂)
    (hsmooth : ∀ r : ℕ, r.Prime → r ∣ S → (r : ℝ) ≤ x ^ δ)
    (hbig₂ : x ^ a₂ ≤ ((R₂ * S : ℕ) : ℝ))
    (hbig₁ : x ^ (a₁ + b₂) ≤ ((R₁ * R₂ * S : ℕ) : ℝ))
    (hw₁ : a₁ + δ ≤ b₁) (hw₂ : a₂ + δ ≤ b₂) :
    ∃ u r : ℕ, u * r ∣ q ∧
      x ^ a₂ ≤ (u : ℝ) ∧ (u : ℝ) ≤ x ^ b₂ ∧
      x ^ a₁ ≤ (r : ℝ) ∧ (r : ℝ) ≤ x ^ b₁ := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
  -- First draw: `u = R₂ · s₂`.
  obtain ⟨s₂, hs₂S, hu1, hu2⟩ := exists_divisor_window_witness hx hR₂ hS hR₂b hsmooth hbig₂ hw₂
  -- What remains of the reservoir is `t = S / s₂`.
  obtain ⟨t, rfl⟩ := hs₂S
  obtain ⟨hs₂, ht⟩ := CanonicallyOrderedAdd.mul_pos.1 (show 0 < s₂ * t from hS)
  -- The second draw has `x^{a₁} ≤ R₁ · t`, after paying `x^{b₂}` for the first.
  have hbigT : x ^ a₁ ≤ ((R₁ * t : ℕ) : ℝ) := by
    refine le_of_mul_le_mul_right ?_ (Nat.cast_pos.2 (Nat.mul_pos hR₂ hs₂))
    calc x ^ a₁ * ((R₂ * s₂ : ℕ) : ℝ) ≤ x ^ a₁ * x ^ b₂ :=
          mul_le_mul_of_nonneg_left hu2 (Real.rpow_nonneg hx0.le a₁)
      _ = x ^ (a₁ + b₂) := (Real.rpow_add hx0 a₁ b₂).symm
      _ ≤ _ := hbig₁
      _ = _ := by push_cast; ring
  -- Second draw: `r = R₁ · s₁` with `s₁` from the remainder.
  obtain ⟨s₁, hs₁t, hr1, hr2⟩ := exists_divisor_window_witness hx hR₁ ht hR₁b
    (fun r hr hrt ↦ hsmooth r hr (hrt.trans (dvd_mul_left t s₂))) hbigT hw₁
  -- The two draws are disjoint in the reservoir, so their product still divides `q`.
  refine ⟨R₂ * s₂, R₁ * s₁, dvd_trans ?_ hdvd, hu1, hu2, hr1, hr2⟩
  convert mul_dvd_mul_left (R₁ * R₂ * s₂) hs₁t using 1 <;> ring

/-- **Two divisors in prescribed open windows.** The strict counterpart of
`Gap212.Packing.exists_two_divisors_window`: with `Rᵢ < x^{bᵢ}`, the reservoir's primes *strictly*
below `x^δ`, and `x^{a₂} < R₂ · S`, the two divisors land strictly inside their windows.

Only three of the six hypotheses become strict, and the asymmetry is the point. The two upper ends
`Rᵢ < x^{bᵢ}` and the strict smoothness are what
`Gap212.Packing.exists_divisor_window_witness_strict` needs at each draw. The lower end of the
first window needs `x^{a₂} < R₂ · S`. But `hbig₁` stays **non-strict**: the first draw now returns
`u < x^{b₂}` strictly, and that one strictness is already enough to make the second draw's target
`x^{a₁} < R₁ · (S / s₂)` strict, since `x^{a₁} · u < x^{a₁ + b₂} ≤ R₁ R₂ S = (R₁ (S/s₂)) · u`. So
the caller pays for strictness at the top ends and at one bottom end, and gets it at both. -/
theorem exists_two_divisors_window_strict {q R₁ R₂ S : ℕ} {x a₁ b₁ a₂ b₂ δ : ℝ}
    (hx : 1 < x) (hdvd : R₁ * R₂ * S ∣ q)
    (hR₁ : 1 ≤ R₁) (hR₂ : 1 ≤ R₂) (hS : 1 ≤ S)
    (hR₁b : (R₁ : ℝ) < x ^ b₁) (hR₂b : (R₂ : ℝ) < x ^ b₂)
    (hsmooth : ∀ r : ℕ, r.Prime → r ∣ S → (r : ℝ) < x ^ δ)
    (hbig₂ : x ^ a₂ < ((R₂ * S : ℕ) : ℝ))
    (hbig₁ : x ^ (a₁ + b₂) ≤ ((R₁ * R₂ * S : ℕ) : ℝ))
    (hw₁ : a₁ + δ ≤ b₁) (hw₂ : a₂ + δ ≤ b₂) :
    ∃ u r : ℕ, u * r ∣ q ∧
      x ^ a₂ < (u : ℝ) ∧ (u : ℝ) < x ^ b₂ ∧
      x ^ a₁ < (r : ℝ) ∧ (r : ℝ) < x ^ b₁ := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
  -- First draw: `u = R₂ · s₂`, strictly inside its window.
  obtain ⟨s₂, hs₂S, hu1, hu2⟩ :=
    exists_divisor_window_witness_strict hx hR₂ hS hR₂b hsmooth hbig₂ hw₂
  obtain ⟨t, rfl⟩ := hs₂S
  obtain ⟨-, ht⟩ := CanonicallyOrderedAdd.mul_pos.1 (show 0 < s₂ * t from hS)
  -- The second draw's target is strict, bought by the first draw's strict upper end.
  have hbigT : x ^ a₁ < ((R₁ * t : ℕ) : ℝ) := by
    refine lt_of_mul_lt_mul_right ?_ (Nat.cast_nonneg (α := ℝ) (R₂ * s₂))
    calc x ^ a₁ * ((R₂ * s₂ : ℕ) : ℝ) < x ^ a₁ * x ^ b₂ :=
          mul_lt_mul_of_pos_left hu2 (Real.rpow_pos_of_pos hx0 a₁)
      _ = x ^ (a₁ + b₂) := (Real.rpow_add hx0 a₁ b₂).symm
      _ ≤ _ := hbig₁
      _ = _ := by push_cast; ring
  obtain ⟨s₁, hs₁t, hr1, hr2⟩ := exists_divisor_window_witness_strict hx hR₁ ht hR₁b
    (fun r hr hrt ↦ hsmooth r hr (hrt.trans (dvd_mul_left t s₂))) hbigT hw₁
  refine ⟨R₂ * s₂, R₁ * s₁, dvd_trans ?_ hdvd, hu1, hu2, hr1, hr2⟩
  convert mul_dvd_mul_left (R₁ * R₂ * s₂) hs₁t using 1 <;> ring

end Gap212.Packing
