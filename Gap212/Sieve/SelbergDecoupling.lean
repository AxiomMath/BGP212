/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.GPYDefs
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The denominator divisor sum: decoupling the totient, and diagonalizing the pair

The divisor sum over `Q⋆` and the Selberg progression sum both reduce to one asymptotic, the
multidimensional divisor-sum evaluation

  `∑_{d,d'} (∏_i μ(dᵢ)μ(d'ᵢ)Fᵢ(log_x dᵢ)Gᵢ(log_x d'ᵢ)) / φ(W ∏_i [dᵢ,d'ᵢ])
     = (∏_i ∫₀^∞ Fᵢ'Gᵢ' + o(1)) · W^{k-1}/(φ(W)^k (log x)^{k-1})`,

and the counting that reduces the progression sum to it is
`Gap212.Sieve.SelbergProgressionSum`. What is here is the *algebra* of that asymptotic,
in the two places where it is algebra and not
analysis: the totient of the generated modulus factors over the coordinates, and in a single
coordinate the pair sum is a diagonal bilinear form in the divisor variable.

## The two algebraic reductions

**Coordinatewise decoupling.** On the tuples the counting leaves standing — those whose least
common multiples `[dᵢ,d'ᵢ]` are pairwise coprime and coprime to `W` — the denominator splits,
`φ(W ∏_i [dᵢ,d'ᵢ]) = φ(W) ∏_i φ([dᵢ,d'ᵢ])`, so the summand is `φ(W)⁻¹` times a product over `i` of
one-coordinate summands (`sum_div_totient_decouple`). Over a *full* box of tuples the resulting sum
is then literally a product of one-coordinate sums (`sum_pair_prod_eq_prod`). The two together are
the reduction of the `k`-fold asymptotic to the one-coordinate one: what separates them is only the
sieving error incurred by dropping the pairwise-coprimality restriction,
`Gap212.Sieve.TotientSievingError`, proved as `Gap212.Sieve.totientSievingError`.

**Selberg diagonalization.** In one coordinate, `1/φ([d,d']) = φ((d,d'))/(φ(d)φ(d'))` — this is
`totient_gcd_mul_totient_lcm` — and
`φ = 1 * (μ * φ)` by Möbius inversion, so the pair sum becomes the diagonal form

  `∑_{d,d'≤B} μ(d)μ(d')F(log_x d)G(log_x d')/φ([d,d'])
     = ∑_{e≤B} (μ*φ)(e) · X_F(e) · X_G(e)`,  `X_F(e) = ∑_{d≤B, e ∣ d} μ(d)F(log_x d)/φ(d)`,

which is `sum_pair_div_totient_lcm_eq_diagonal`. The weight `(μ*φ)(e)` is `p - 2` at a prime
(`moebiusTotient_prime`), so the form is genuinely the Gram matrix of the classical evaluation and
not a rearrangement of nothing.

## The asymptotic

The analytic evaluation — the passage from the diagonal form to `∫₀^∞ F'G'` — is not in this file.
It is the Gram-sum limit `Gap212.Sieve.TotientGramSumLimitOfSupport`, which follows from
`Gap212.Sieve.polymath41Totient` by
`Gap212.Sieve.totientGramSumLimitOfSupport_iff_polymath41Totient` and is assembled into the divisor
sum over `Q⋆` in `Gap212.Sieve.divisor_sum_over_qstar`.

## Main results

* `Gap212.Sieve.totient_gcd_mul_totient_lcm`: `φ((a,b)) φ([a,b]) = φ(a) φ(b)`, unconditionally.
* `Gap212.Sieve.div_totient_lcm_eq`: the real form, `uv/φ([a,b]) = (u/φ(a))(v/φ(b))φ((a,b))`.
* `Gap212.Sieve.totient_mul_prod_of_pairwise_coprime`: `φ(W ∏ᵢmᵢ) = φ(W) ∏ᵢφ(mᵢ)`.
* `Gap212.Sieve.sum_div_totient_decouple`: the coordinatewise decoupling of the denominator.
* `Gap212.Sieve.sum_pair_prod_eq_prod`: a pair sum of products over a box is a product of pair
  sums.
* `Gap212.Sieve.moebiusTotient`: the Dirichlet convolution `μ * φ`, the Gram weight.
* `Gap212.Sieve.sum_pair_div_totient_lcm_eq_diagonal`: the Selberg diagonalization.
* `Gap212.Sieve.sum_moebius_div_totient_filter_dvd`: `μ(e)/φ(e)` comes out of each diagonal sum.
* `Gap212.Sieve.gramWeight`, `gramWeight_prime`: the resulting weight, `(p-2)/(p-1)²` at a prime.
* `Gap212.Sieve.sum_pair_moebius_div_totient_lcm_eq_gram`: the one-coordinate divisor sum written
  as a sum against that weight.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset

/-! ## The totient at a least common multiple

The one-coordinate denominator is `φ([d,d'])`, and the classical evaluation needs it
expressed through `φ(d)`, `φ(d')` and the greatest common divisor. Mathlib has the *product* form
`Nat.totient_gcd_mul_totient_mul` (`φ((a,b)) φ(ab) = φ(a) φ(b) (a,b)`); the lcm form below is
the one wanted, and follows by applying the product form a second time at the pair
`((a,b),[a,b])`. -/

/-- **The totient at a greatest common divisor and a least common multiple.**
`φ((a,b)) · φ([a,b]) = φ(a) · φ(b)` for all `a, b`, with no positivity hypothesis: at `a = 0` both
sides vanish, `[0,b]` being `0`.

This is the exact multiplicativity that survives when `a` and `b` are *not* coprime, and is the
identity behind the Selberg diagonalization of `Gap212.Sieve.sum_pair_div_totient_lcm_eq_diagonal`.
-/
theorem totient_gcd_mul_totient_lcm (a b : ℕ) :
    Nat.totient (Nat.gcd a b) * Nat.totient (Nat.lcm a b) = a.totient * b.totient := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  have h := Nat.totient_gcd_mul_totient_mul (Nat.gcd a b) (Nat.lcm a b)
  rw [Nat.gcd_eq_left ((Nat.gcd_dvd_left a b).trans (Nat.dvd_lcm_left a b)), Nat.gcd_mul_lcm,
    Nat.totient_gcd_mul_totient_mul] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.gcd_pos_of_pos_left _ ha) h.symm

/-- **The real form of the lcm identity**: the reciprocal of `φ([a,b])` splits as
`φ((a,b))/(φ(a)φ(b))`.

Stated with the numerators `u` and `v` attached to their own coordinate, which is the shape the
pair sum is rewritten in. -/
theorem div_totient_lcm_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (u v : ℝ) :
    u * v / (Nat.totient (Nat.lcm a b) : ℝ)
      = u / (Nat.totient a : ℝ) * (v / (Nat.totient b : ℝ)) *
          (Nat.totient (Nat.gcd a b) : ℝ) := by
  have hla : (0 : ℝ) < (Nat.totient a : ℝ) := by exact_mod_cast Nat.totient_pos.mpr ha
  have hlb : (0 : ℝ) < (Nat.totient b : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hb
  have hl : (0 : ℝ) < (Nat.totient (Nat.lcm a b) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.lcm_pos ha hb)
  have h' : (Nat.totient (Nat.gcd a b) : ℝ) * (Nat.totient (Nat.lcm a b) : ℝ)
      = (Nat.totient a : ℝ) * (Nat.totient b : ℝ) := by
    exact_mod_cast totient_gcd_mul_totient_lcm a b
  field_simp
  linear_combination (-(u * v)) * h'

/-! ## The denominator decouples over the coordinates

The counting of `Gap212.Sieve.SelbergProgressionSum` leaves only the tuples whose least common
multiples are pairwise coprime and coprime to `W(x)` — that is
`Gap212.Sieve.coprime_of_forall_dvd`, and it is automatic rather than imposed. On exactly those
tuples the generated modulus `W ∏ᵢ[dᵢ,d'ᵢ]` has a totient that factors, so the `k`-fold summand
becomes `φ(W)⁻¹` times a product of one-coordinate summands. -/

/-- **The totient of a pairwise coprime product** is the product of the totients. The indexed
form of `Nat.totient_mul`; repeated values among the `mᵢ` are not merged, which is what a
`Finset` of moduli would do. -/
theorem totient_prod_of_pairwise_coprime {ι : Type*} (m : ι → ℕ) (s : Finset ι)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (m i) (m j)) :
    Nat.totient (∏ i ∈ s, m i) = ∏ i ∈ s, Nat.totient (m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.totient_mul, ih]
      · exact fun i hi j hj hij ↦
          hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      · exact Nat.Coprime.prod_right fun j hj ↦
          hcop a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
            fun hEq ↦ ha (hEq ▸ hj)

/-- **The generated modulus has a factoring totient.** For moduli `mᵢ` pairwise coprime and each
coprime to `W`, `φ(W ∏ᵢmᵢ) = φ(W) ∏ᵢφ(mᵢ)`.

Applied at `mᵢ = [dᵢ,d'ᵢ]` this is the factor `φ(W)^{-1} B_x^{-(k-1)}`: one `φ(W)` comes out, and
every coordinate contributes its own `φ([dᵢ,d'ᵢ])`. -/
theorem totient_mul_prod_of_pairwise_coprime {ι : Type*} [Fintype ι] {W : ℕ} {m : ι → ℕ}
    (hWm : ∀ i, Nat.Coprime W (m i)) (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) :
    Nat.totient (W * ∏ i, m i) = Nat.totient W * ∏ i, Nat.totient (m i) := by
  rw [Nat.totient_mul (Nat.Coprime.prod_right fun i _ ↦ hWm i),
    totient_prod_of_pairwise_coprime m Finset.univ fun i _ j _ hij ↦ hcop i j hij]

/-- **The summand decouples.** For moduli `mᵢ` pairwise coprime and coprime to `W`, a product of
numerators over the generated modulus is `φ(W)⁻¹` times the product of the one-coordinate
quotients. -/
theorem prod_div_totient_decouple {ι : Type*} [Fintype ι] {W : ℕ} {m : ι → ℕ}
    (hWm : ∀ i, Nat.Coprime W (m i))
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) (a : ι → ℝ) :
    (∏ i, a i) / (Nat.totient (W * ∏ i, m i) : ℝ)
      = 1 / (Nat.totient W : ℝ) * ∏ i, (a i / (Nat.totient (m i) : ℝ)) := by
  rw [totient_mul_prod_of_pairwise_coprime hWm hcop, Finset.prod_div_distrib]
  push_cast
  ring

/-- **The coordinatewise decoupling of the denominator divisor sum.** Over any finite collection
`T` of pairs of divisor tuples whose least common multiples are positive, pairwise coprime and
coprime to
`W`, the sum against `φ(W ∏ᵢ[dᵢ,d'ᵢ])` is `φ(W)⁻¹` times the same sum against the *product* of the
one-coordinate totients `φ([dᵢ,d'ᵢ])`.

This is the step performed silently when the right-hand side is written as
`W^{k-1}/(φ(W)^k(\log x)^{k-1})`: one `φ(W)` is the modulus's own, and the remaining `k-1` factors
`(φ(W)/W)\log x` are one per coordinate. The hypotheses are exactly the conclusions of
`Gap212.Sieve.coprime_of_forall_dvd`, so on the tuples that contribute they hold automatically.

Combined with `Gap212.Sieve.sum_pair_prod_eq_prod` — which needs `T` to be a full box — this
reduces the `k`-fold evaluation to the one-coordinate one. The difference between a full box and
the coprime tuples inside it is the sieving error `Gap212.Sieve.TotientSievingError`. -/
theorem sum_div_totient_decouple {ι : Type*} [Fintype ι] {W : ℕ}
    (T : Finset ((ι → ℕ) × (ι → ℕ))) (a : (ι → ℕ) × (ι → ℕ) → ι → ℝ)
    (hT : ∀ p ∈ T, (∀ i, 0 < (p.1 i).lcm (p.2 i)) ∧
      (∀ i, Nat.Coprime W ((p.1 i).lcm (p.2 i))) ∧
      (∀ i j, i ≠ j → Nat.Coprime ((p.1 i).lcm (p.2 i)) ((p.1 j).lcm (p.2 j)))) :
    ∑ p ∈ T, (∏ i, a p i) / (Nat.totient (W * ∏ i, (p.1 i).lcm (p.2 i)) : ℝ)
      = 1 / (Nat.totient W : ℝ) *
          ∑ p ∈ T, ∏ i, (a p i / (Nat.totient ((p.1 i).lcm (p.2 i)) : ℝ)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  obtain ⟨hm, hWm, hcop⟩ := hT p hp
  exact prod_div_totient_decouple hWm hcop (a p)

/-! ## A pair sum of products over a box is a product of pair sums

The other half of the reduction. Once the denominator has decoupled, the `k`-fold sum over a full
box of tuples is a product of `k` one-coordinate pair sums — the elementary distribution law, at the
pair of tuple variables the expansion of `Gap212.Sieve.sum_prod_lambdaF_pair` produces. -/

/-- **The coordinates separate.** A double sum over tuples in a box `box^ι`, of a product over the
coordinates, is the product over the coordinates of the double sum over `box × box`.

Two applications of `Finset.prod_univ_sum`: the inner tuple sum separates at each fixed outer
tuple, and then the outer one separates. -/
theorem sum_pair_prod_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (box : Finset ℕ)
    (f : ι → ℕ → ℕ → ℝ) :
    ∑ d ∈ Fintype.piFinset fun _ : ι ↦ box, ∑ d' ∈ Fintype.piFinset fun _ : ι ↦ box,
        ∏ i, f i (d i) (d' i)
      = ∏ i, ∑ a ∈ box, ∑ b ∈ box, f i a b := by
  rw [Finset.sum_congr rfl fun d _ ↦ (Finset.prod_univ_sum _ fun i b ↦ f i (d i) b).symm]
  exact (Finset.prod_univ_sum (fun _ ↦ box) fun i a ↦ ∑ b ∈ box, f i a b).symm

/-! ## The Selberg diagonalization in one coordinate

The one-coordinate pair sum is a quadratic form in the divisor variable with the non-diagonal
kernel `1/φ([d,d'])`. Writing `1/φ([d,d']) = φ((d,d'))/(φ(d)φ(d'))` and then `φ = 1 * (μ * φ)`
makes the kernel diagonal: the sum becomes `∑_e (μ*φ)(e) X_F(e) X_G(e)` with `X_F(e)` a sum over
the multiples of `e`. This is the change of variables the classical evaluation is carried out
in. -/

/-- **The Gram weight** `(μ * φ)(e) = ∑_{f ∣ e} μ(e/f) φ(f)`, the Dirichlet convolution of the
Möbius function with the totient.

It is `p - 2` at a prime (`Gap212.Sieve.moebiusTotient_prime`) and `1` at `1`, so on squarefree `e`
it is `∏_{p ∣ e}(p-2)` — the weight of the Selberg diagonalization. Written through
`Nat.divisorsAntidiagonal` so that `Gap212.Sieve.sum_divisors_moebiusTotient` is exactly Möbius
inversion. -/
noncomputable def moebiusTotient (e : ℕ) : ℝ :=
  ∑ x ∈ e.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) * (Nat.totient x.2 : ℝ)

/-- The Gram weight at `1`. -/
theorem moebiusTotient_one : moebiusTotient 1 = 1 := by simp [moebiusTotient]

/-- **The Gram weight sums to the totient**: `∑_{e ∣ n} (μ*φ)(e) = φ(n)` for `n > 0`.

Möbius inversion (`ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq`) at `g = φ`. This is what
makes the kernel `φ((d,d'))` of `Gap212.Sieve.div_totient_lcm_eq` diagonal. -/
theorem sum_divisors_moebiusTotient {n : ℕ} (hn : 0 < n) :
    ∑ e ∈ n.divisors, moebiusTotient e = (Nat.totient n : ℝ) := by
  refine (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq (f := moebiusTotient)
    (g := fun n ↦ (Nat.totient n : ℝ))).mpr ?_ n hn
  intro m _
  simp [moebiusTotient, zsmul_eq_mul]

/-- **The Gram weight at a prime is `p - 2`.** So the diagonal form of
`Gap212.Sieve.sum_pair_div_totient_lcm_eq_diagonal` has the weights of the classical evaluation,
and in particular is not a rearrangement of a vanishing kernel. -/
theorem moebiusTotient_prime {p : ℕ} (hp : p.Prime) : moebiusTotient p = (p : ℝ) - 2 := by
  have h := sum_divisors_moebiusTotient hp.pos
  rw [hp.divisors, Finset.sum_insert (by simpa using Ne.symm hp.ne_one), Finset.sum_singleton,
    moebiusTotient_one, Nat.totient_prime hp, Nat.cast_sub hp.one_le] at h
  push_cast at h
  linarith

/-- **The Selberg diagonalization of the one-coordinate pair sum.** For any numerator weights
`u, v` and any bound `B`,

  `∑_{d,d'≤B} u(d)v(d')/φ([d,d'])
     = ∑_{e≤B} (μ*φ)(e) · (∑_{d≤B, e ∣ d} u(d)/φ(d)) · (∑_{d'≤B, e ∣ d'} v(d')/φ(d'))`.

The non-diagonal kernel `1/φ([d,d'])` becomes `φ((d,d'))/(φ(d)φ(d'))` by
`Gap212.Sieve.div_totient_lcm_eq`, and `φ((d,d'))` is then expanded over the common divisors `e` by
`Gap212.Sieve.sum_divisors_moebiusTotient`; the sums are interchanged and the `e`-th term factors.

At `u(d) = μ(d)F(log_x d)`, `v(d') = μ(d')G(log_x d')` this is the one-coordinate case of the
divisor sum, written in the variables the classical evaluation uses. -/
theorem sum_pair_div_totient_lcm_eq_diagonal (B : ℕ) (u v : ℕ → ℝ) :
    ∑ d ∈ Icc 1 B, ∑ d' ∈ Icc 1 B, u d * v d' / (Nat.totient (Nat.lcm d d') : ℝ)
      = ∑ e ∈ Icc 1 B, moebiusTotient e *
          ((∑ d ∈ Icc 1 B with e ∣ d, u d / (Nat.totient d : ℝ)) *
            ∑ d' ∈ Icc 1 B with e ∣ d', v d' / (Nat.totient d' : ℝ)) := by
  classical
  set A : ℕ → ℝ := fun d ↦ u d / (Nat.totient d : ℝ)
  set V : ℕ → ℝ := fun d ↦ v d / (Nat.totient d : ℝ)
  have step : ∀ d ∈ Icc 1 B, ∀ d' ∈ Icc 1 B,
      u d * v d' / (Nat.totient (Nat.lcm d d') : ℝ)
        = ∑ e ∈ Icc 1 B, if e ∣ d ∧ e ∣ d' then A d * V d' * moebiusTotient e else 0 := by
    intro d hd d' hd'
    obtain ⟨hd1, hdB⟩ := Finset.mem_Icc.mp hd
    obtain ⟨hd1', hdB'⟩ := Finset.mem_Icc.mp hd'
    have hgpos : 0 < Nat.gcd d d' := Nat.gcd_pos_of_pos_left _ (by omega)
    have hset : (Nat.gcd d d').divisors = {e ∈ Icc 1 B | e ∣ d ∧ e ∣ d'} := by
      ext e
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc, Nat.dvd_gcd_iff]
      exact ⟨fun h ↦ ⟨⟨Nat.pos_of_dvd_of_pos h.1.1 hd1, (Nat.le_of_dvd hd1 h.1.1).trans hdB⟩,
        h.1⟩, fun h ↦ ⟨h.2, hgpos.ne'⟩⟩
    rw [div_totient_lcm_eq (by omega) (by omega), ← sum_divisors_moebiusTotient hgpos, hset,
      Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun d hd ↦ Finset.sum_congr rfl fun d' hd' ↦ step d hd d' hd',
    Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d' _ ↦ ?_
  split_ifs <;> first | tauto | ring

/-! ## Pulling the Möbius factor out of a diagonal sum

The last step the algebra reaches. Each `X_F(e) = ∑_{d≤B, e ∣ d} μ(d)F(d)/φ(d)` of the diagonal
form is `μ(e)/φ(e)` times a sum over the integers coprime to `e`: reindex `d = e f`, note that a
tuple with `(e,f) > 1` has `ef` non-squarefree and so contributes nothing, and split `μ` and `φ`
over the coprime factorization. The diagonal form then reads `∑_e g(e) Y_F(e) Y_G(e)` with the
*nonnegative* weight `g(e) = μ(e)²(μ*φ)(e)/φ(e)²`, which is `(p-2)/(p-1)²` at a prime. -/

/-- **Reindexing a sum over the multiples of `e`.** -/
theorem sum_filter_dvd_eq_sum_mul (B : ℕ) {e : ℕ} (he : 0 < e) (u : ℕ → ℝ) :
    ∑ d ∈ Icc 1 B with e ∣ d, u d = ∑ f ∈ Icc 1 (B / e), u (e * f) := by
  classical
  refine Finset.sum_nbij' (fun d ↦ d / e) (fun f ↦ e * f) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
    exact ⟨(Nat.one_le_div_iff he).2 (Nat.le_of_dvd hd.1.1 hd.2), Nat.div_le_div_right hd.1.2⟩
  · intro f hf
    obtain ⟨hf1, hfB⟩ := Finset.mem_Icc.mp hf
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos he (by omega), ?_⟩, Dvd.intro f rfl⟩
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le he).mp hfB
  · exact fun d hd ↦ Nat.mul_div_cancel' (Finset.mem_filter.1 hd).2
  · exact fun f _ ↦ Nat.mul_div_cancel_left f he
  · exact fun d hd ↦ by rw [Nat.mul_div_cancel' (Finset.mem_filter.1 hd).2]

/-- **A product of two integers sharing a factor is not squarefree**, so its Möbius value is `0`.
This is what lets the reindexed sum be restricted to the `f` coprime to `e`. -/
theorem moebius_mul_eq_zero_of_not_coprime {e f : ℕ} (h : ¬ Nat.Coprime e f) :
    ArithmeticFunction.moebius (e * f) = 0 := by
  refine ArithmeticFunction.moebius_eq_zero_of_not_squarefree ?_
  rw [Nat.squarefree_mul_iff]
  tauto

/-- **The Möbius factor comes out of the diagonal sum.**
`∑_{d≤B, e ∣ d} μ(d)G(d)/φ(d) = (μ(e)/φ(e)) ∑_{f≤B/e, (f,e)=1} μ(f)G(ef)/φ(f)`.

The profile is read at `d = ef`, which is why `G` is carried as a function of the integer rather
than of its logarithm: at `G d = F (log_x d)` the inner sum is the classical
`∑_{f≤B/e,(f,e)=1} μ(f)F(log_x e + log_x f)/φ(f)`. -/
theorem sum_moebius_div_totient_filter_dvd (B : ℕ) {e : ℕ} (he : 0 < e) (G : ℕ → ℝ) :
    ∑ d ∈ Icc 1 B with e ∣ d, (ArithmeticFunction.moebius d : ℝ) * G d / (Nat.totient d : ℝ)
      = (ArithmeticFunction.moebius e : ℝ) / (Nat.totient e : ℝ) *
          ∑ f ∈ Icc 1 (B / e) with Nat.Coprime e f,
            (ArithmeticFunction.moebius f : ℝ) * G (e * f) / (Nat.totient f : ℝ) := by
  classical
  have hvanish : ∀ f ∈ Icc 1 (B / e),
      (ArithmeticFunction.moebius (e * f) : ℝ) * G (e * f) / (Nat.totient (e * f) : ℝ) ≠ 0 →
        Nat.Coprime e f :=
    fun f _ hne ↦ by_contra fun hc ↦ hne (by simp [moebius_mul_eq_zero_of_not_coprime hc])
  rw [sum_filter_dvd_eq_sum_mul B he, ← Finset.sum_filter_of_ne hvanish, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f hf ↦ ?_
  have hcop := (Finset.mem_filter.1 hf).2
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop, Nat.totient_mul hcop]
  push_cast
  ring

/-- **The Gram weight of the diagonalized form**, `g(e) = (μ*φ)(e) · (μ(e)/φ(e))²`.

Nonnegative on the squarefree integers with every prime factor at least `3`, and `(p-2)/(p-1)²` at
a prime (`Gap212.Sieve.gramWeight_prime`). -/
noncomputable def gramWeight (e : ℕ) : ℝ :=
  moebiusTotient e * ((ArithmeticFunction.moebius e : ℝ) / (Nat.totient e : ℝ)) ^ 2

/-- **The Gram weight at a prime is `(p-2)/(p-1)²`.** -/
theorem gramWeight_prime {p : ℕ} (hp : p.Prime) :
    gramWeight p = ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
  rw [gramWeight, moebiusTotient_prime hp, ArithmeticFunction.moebius_apply_prime hp,
    Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  push_cast
  rw [div_pow]
  ring

/-- **The one-coordinate divisor sum as a Gram sum.** Combining the diagonalization with the
Möbius pull-out,

  `∑_{d,d'≤B} μ(d)F(d)μ(d')G(d')/φ([d,d'])
     = ∑_{e≤B} g(e) · Y_F(e) · Y_G(e)`,
  `Y_F(e) = ∑_{f≤B/e, (f,e)=1} μ(f)F(ef)/φ(f)`,  `g(e) = (μ*φ)(e)(μ(e)/φ(e))²`.

The evaluation of the right-hand side — `Y_F(e) ≍ -F'(log_x e)/\log x` up to the sieve factor, and
the `e`-sum against `g` converging to `∫₀^∞ F'G'` — is the Gram-sum limit
`Gap212.Sieve.TotientGramSumLimitOfSupport`. -/
theorem sum_pair_moebius_div_totient_lcm_eq_gram (B : ℕ) (F G : ℕ → ℝ) :
    ∑ d ∈ Icc 1 B, ∑ d' ∈ Icc 1 B,
        (ArithmeticFunction.moebius d : ℝ) * F d *
          ((ArithmeticFunction.moebius d' : ℝ) * G d') / (Nat.totient (Nat.lcm d d') : ℝ)
      = ∑ e ∈ Icc 1 B, gramWeight e *
          ((∑ f ∈ Icc 1 (B / e) with Nat.Coprime e f,
              (ArithmeticFunction.moebius f : ℝ) * F (e * f) / (Nat.totient f : ℝ)) *
            ∑ f ∈ Icc 1 (B / e) with Nat.Coprime e f,
              (ArithmeticFunction.moebius f : ℝ) * G (e * f) / (Nat.totient f : ℝ)) := by
  classical
  rw [sum_pair_div_totient_lcm_eq_diagonal B (fun d ↦ (ArithmeticFunction.moebius d : ℝ) * F d)
    (fun d ↦ (ArithmeticFunction.moebius d : ℝ) * G d)]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  have he0 : 0 < e := (Finset.mem_Icc.mp he).1
  rw [sum_moebius_div_totient_filter_dvd B he0 F, sum_moebius_div_totient_filter_dvd B he0 G,
    gramWeight]
  ring

end Gap212.Sieve
