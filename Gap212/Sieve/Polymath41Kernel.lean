/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41

/-!
# Step 3 of Polymath8b Lemma 4.1: the kernel's local factor

After step 1 expands the profiles (`Gap212.Sieve.Polymath41Fourier`) and step 2 licenses
Fubini (`Gap212.Sieve.Polymath41Majorant`), the source's kernel is

  `K(ξ,ξ') = ∑_{d,d'} μ(d)μ(d') / ([d,d'] d^{(1+iξ)/log x} (d')^{(1+iξ')/log x})`,

which it factorises as `∏_{p∤W} K_p` with local factors `K_p`. Collecting the pair
sum by `n = [d,d']` turns `K` into an ordinary Dirichlet series `∑_n a(n)` whose coefficient is

  `a(n) = (1/n) ∑_{[d,d']=n} μ(d)μ(d') d^{-s} (d')^{-s'}`,

and that is `Gap212.Sieve.kernelCoeff` here. This file computes `a` at `1` and at a prime, in both
kernels, and identifies the results with the Euler-factor algebra of `Gap212.Sieve.Polymath41`:

* `Gap212.Sieve.one_add_kernelCoeff_prime`:
  `1 + a(p) = Gap212.Sieve.localFactorRecip p (p^{-s}) (p^{-s'})`, which is literally the source's
  `K_p` at `k = 1`;
* `Gap212.Sieve.one_add_kernelCoeffTotient_prime`: the same for `φ([d,d'])`, giving
  `Gap212.Sieve.localFactorTotient`, which is the closing sentence of the source's proof,
  computed.

`Gap212.Sieve.localFactorRecip` is defined as a polynomial in `u, v`; these two theorems identify it
with *the local factor of the kernel*, which is how the Euler-factor algebra
(`Gap212.Sieve.localFactorRecip_mul_one_sub`, `Gap212.Sieve.localFactorTotient_eq_sub`) bears on
the actual sum.

## The Euler product

`ArithmeticFunction.IsMultiplicative.eulerProduct_tprod` needs two things this file does not
supply: multiplicativity of `a`, which is `Gap212.Sieve.kernelCoeff_mul_of_coprime` in
`Gap212.Sieve.Polymath41Euler`, and summability of `‖a‖`, which is
`Gap212.Sieve.summable_norm_kernelCoeff` in `Gap212.Sieve.Polymath41AssembleDirichlet`.

## Main definitions

* `Gap212.Sieve.kernelCoeff`, `Gap212.Sieve.kernelCoeffTotient`: the Dirichlet coefficients of the
  source's `K` in the two kernels.

## Main results

* `Gap212.Sieve.kernelCoeff_one`, `Gap212.Sieve.kernelCoeffTotient_one`: `a(1) = 1`.
* `Gap212.Sieve.one_add_kernelCoeff_prime`, `Gap212.Sieve.one_add_kernelCoeffTotient_prime`: the
  source's `K_p` and its totient variant, computed.
* `Gap212.Sieve.gcd_lcm_distrib`: `gcd` distributes over `lcm`.
* `Gap212.Sieve.lcm_gcd_left_of_lcm_eq_mul`: the maps-to half of the multiplicativity bijection.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset
open scoped ArithmeticFunction.Moebius

/-! ## The fibre of the pair sum over `n = [d,d']` -/

/-- **The pairs with a given least common multiple.** For `n ≥ 1` both `d` and `d'` divide
`[d,d'] = n`, so the fibre sits inside `n.divisors ×ˢ n.divisors`. This is the same `Finset`
Mathlib's `Nat.card_pair_lcm_eq` computes the cardinality of, unfolded. -/
noncomputable def lcmFibre (n : ℕ) : Finset (ℕ × ℕ) :=
  {q ∈ n.divisors ×ˢ n.divisors | Nat.lcm q.1 q.2 = n}

/-- The fibre over `1` is the single pair `(1,1)`. -/
theorem lcmFibre_one : lcmFibre 1 = {(1, 1)} := by
  simp [lcmFibre]

/-- **The fibre over a prime has exactly three pairs**: `(1,p)`, `(p,1)` and `(p,p)`. The pair
`(1,1)` has `[1,1] = 1 ≠ p`, and no other pair of divisors of `p` exists. This is the source's
"`[d_1,…,d'_k] = p`" index set of `K_p` at `k = 1`. -/
theorem lcmFibre_prime {p : ℕ} (hp : p.Prime) : lcmFibre p = {(1, p), (p, 1), (p, p)} := by
  have h1 : (1 : ℕ) ≠ p := hp.one_lt.ne
  ext ⟨a, b⟩
  simp only [lcmFibre, mem_filter, mem_product, Nat.Prime.divisors hp, mem_insert,
    mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨ha | ha, hb | hb⟩, hl⟩ <;> subst ha <;> subst hb <;> simp_all
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩) <;> subst ha <;> subst hb <;> simp

/-! ## `gcd` distributes over `lcm` -/

/-- **`gcd` distributes over `lcm` on the positive naturals**:

  `([a,b], c) = [(a,c), (b,c)]`,  with `(·,·)` the `gcd` and `[·,·]` the `lcm`.

It is proved through `Nat.factorization`, where it is `min (max α β) γ = max (min α γ) (min β γ)`
prime by prime.

It is the key to multiplicativity of `Gap212.Sieve.kernelCoeff`, which the source's Euler
factorisation needs. Its consequence `Gap212.Sieve.lcm_gcd_left_of_lcm_eq_mul` is the
step that identifies the fibre `{(d,d') : [d,d'] = mn}` with a product of two fibres. -/
theorem gcd_lcm_distrib {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Nat.gcd (Nat.lcm a b) c = Nat.lcm (Nat.gcd a c) (Nat.gcd b c) := by
  have hl : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  have hga : Nat.gcd a c ≠ 0 := Nat.gcd_ne_zero_left ha
  have hgb : Nat.gcd b c ≠ 0 := Nat.gcd_ne_zero_left hb
  refine Nat.factorization_inj (by simpa using Nat.gcd_ne_zero_left hl)
    (by simpa using Nat.lcm_ne_zero hga hgb) ?_
  rw [Nat.factorization_gcd hl hc, Nat.factorization_lcm ha hb,
    Nat.factorization_lcm hga hgb, Nat.factorization_gcd ha hc, Nat.factorization_gcd hb hc]
  ext q
  simp only [Finsupp.inf_apply, Finsupp.sup_apply]
  lia

/-- **The `m`-part of a pair whose least common multiple is `m·n` has least common multiple `m`.**
If `[d,d'] = m·n` then `[(d,m), (d',m)] = m`, immediately from
`Gap212.Sieve.gcd_lcm_distrib` and `(m·n, m) = m`.

This is the maps-to half of the bijection
`{(d,d') : [d,d'] = mn} ≃ {[d₁,d₁'] = m} × {[d₂,d₂'] = n}` that multiplicativity of
`Gap212.Sieve.kernelCoeff` needs — and, run at `n` in place of `m`, its surjectivity half too. Note
that **no coprimality of `m` and `n` is used**; coprimality is what makes the map injective, not
what makes it land. -/
theorem lcm_gcd_left_of_lcm_eq_mul {d d' m n : ℕ} (hd : d ≠ 0) (hd' : d' ≠ 0) (hm : m ≠ 0)
    (h : Nat.lcm d d' = m * n) : Nat.lcm (Nat.gcd d m) (Nat.gcd d' m) = m := by
  rw [← gcd_lcm_distrib hd hd' hm, h]
  exact Nat.gcd_eq_right (dvd_mul_right m n)

/-! ## The two Dirichlet coefficients -/

/-- **The Dirichlet coefficient of the source's kernel, reciprocal kernel**:

  `a(n) = (1/n) ∑_{[d,d']=n} μ(d)μ(d') d^{-s} (d')^{-s'}`.

Summing `a` over `n` is the source's `K`, since `[d,d'] = n` partitions the pair
sum. -/
noncomputable def kernelCoeff (s s' : ℂ) (n : ℕ) : ℂ :=
  (∑ q ∈ lcmFibre n, (μ q.1 : ℂ) * (μ q.2 : ℂ) * (q.1 : ℂ) ^ (-s) * (q.2 : ℂ) ^ (-s')) / (n : ℂ)

/-- **The same with `[d,d']` replaced by `φ([d,d'])`** — the substitution of the lemma's closing
sentence. A **distinct** arithmetic function from `Gap212.Sieve.kernelCoeff`, not a
rescaling of it: the numerators agree but the denominator is `φ(n)`, and at `n = 2` that
denominator is `1` rather than `2`. -/
noncomputable def kernelCoeffTotient (s s' : ℂ) (n : ℕ) : ℂ :=
  (∑ q ∈ lcmFibre n, (μ q.1 : ℂ) * (μ q.2 : ℂ) * (q.1 : ℂ) ^ (-s) * (q.2 : ℂ) ^ (-s')) /
    (Nat.totient n : ℂ)

/-- `a(1) = 1`: the fibre over `1` is `{(1,1)}` and `μ(1) = 1`. This is the `1 +` of the source's
`K_p`. -/
theorem kernelCoeff_one (s s' : ℂ) : kernelCoeff s s' 1 = 1 := by
  simp [kernelCoeff, lcmFibre_one]

/-- `a^φ(1) = 1`, since `φ(1) = 1`. -/
theorem kernelCoeffTotient_one (s s' : ℂ) : kernelCoeffTotient s s' 1 = 1 := by
  simp [kernelCoeffTotient, lcmFibre_one]

/-- **The numerator of the source's local factor `K_p`, computed.** For a prime `p`,

  `∑_{[d,d']=p} μ(d)μ(d') d^{-s}(d')^{-s'} = -u - v + uv`  with `u = p^{-s}`, `v = p^{-s'}`,

from the three pairs of `Gap212.Sieve.lcmFibre_prime` and `μ(p) = -1`. The `1/p` (or `1/φ(p)`) is
what separates the two kernels, so it is kept out of this lemma and both of them use it. -/
theorem sum_lcmFibre_prime {p : ℕ} (hp : p.Prime) (s s' : ℂ) :
    ∑ q ∈ lcmFibre p, (μ q.1 : ℂ) * (μ q.2 : ℂ) * (q.1 : ℂ) ^ (-s) * (q.2 : ℂ) ^ (-s')
      = -(p : ℂ) ^ (-s) - (p : ℂ) ^ (-s') + (p : ℂ) ^ (-s) * (p : ℂ) ^ (-s') := by
  have h1 : (1 : ℕ) ≠ p := hp.one_lt.ne
  rw [lcmFibre_prime hp, sum_insert (by simp [h1]), sum_insert (by simp [h1]), sum_singleton]
  simp only [ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime hp,
    Nat.cast_one, Complex.one_cpow, Int.cast_one, Int.cast_neg]
  ring

/-- **The source's `K_p` at `k = 1`, reciprocal kernel**: for a prime `p`,

  `1 + a(p) = Gap212.Sieve.localFactorRecip p (p^{-s}) (p^{-s'})`.

This is what makes `Gap212.Sieve.localFactorRecip` the *local factor of the kernel* rather than a
polynomial that happens to satisfy `Gap212.Sieve.localFactorRecip_mul_one_sub`. -/
theorem one_add_kernelCoeff_prime {p : ℕ} (hp : p.Prime) (s s' : ℂ) :
    1 + kernelCoeff s s' p
      = localFactorRecip (p : ℂ) ((p : ℂ) ^ (-s)) ((p : ℂ) ^ (-s')) := by
  have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  rw [kernelCoeff, sum_lcmFibre_prime hp, localFactorRecip]
  field_simp
  ring

/-- **The closing sentence of the proof of Lemma 4.1 at `k = 1`, computed**: for a prime `p`,

  `1 + a^φ(p) = Gap212.Sieve.localFactorTotient p (p^{-s}) (p^{-s'})`,

because `φ(p) = p - 1`. The passage from this to the reciprocal factor is
`Gap212.Sieve.localFactorTotient_eq_sub` — and it is an equation, not the source's "may be absorbed
into the `1+O(1/p²)`".

This is a **separate** theorem from `Gap212.Sieve.one_add_kernelCoeff_prime` because the two
kernels are separate assertions; only `Gap212.Sieve.sum_lcmFibre_prime` is shared. -/
theorem one_add_kernelCoeffTotient_prime {p : ℕ} (hp : p.Prime) (s s' : ℂ) :
    1 + kernelCoeffTotient s s' p
      = localFactorTotient (p : ℂ) ((p : ℂ) ^ (-s)) ((p : ℂ) ^ (-s')) := by
  have hpne : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.2 (mod_cast hp.one_lt.ne')
  rw [kernelCoeffTotient, sum_lcmFibre_prime hp, Nat.totient_prime hp,
    Nat.cast_sub hp.one_lt.le, Nat.cast_one, localFactorTotient]
  field_simp
  ring

end Gap212.Sieve
