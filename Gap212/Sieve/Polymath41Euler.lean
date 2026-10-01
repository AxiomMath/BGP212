/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41Kernel

/-!
# Step 3 of Polymath8b Lemma 4.1, continued: the kernel's coefficient is multiplicative

`Gap212.Sieve.Polymath41Kernel` computes the Dirichlet coefficient
`Gap212.Sieve.kernelCoeff` of the source's kernel `K` at `1` and at a prime, and
identifies the answers with the source's local factor `K_p`. Assembling those local answers into
the source's Euler product needs `a` to be *multiplicative*, and multiplicativity is the bijection

  `{(d,d') : [d,d'] = mn} ≃ {(d₁,d₁') : [d₁,d₁'] = m} × {(d₂,d₂') : [d₂,d₂'] = n}`,
  `(d,d') ↦ ((d,m),(d',m)), ((d,n),(d',n))`,   inverse `((a,a'),(b,b')) ↦ (ab, a'b')`.

This file proves it. The `Gap212.Sieve.lcmFibre` of a product splits as a product of fibres
(`Gap212.Sieve.lcmFibre_mul`), the summand splits along it, and so both kernels' coefficients
are multiplicative: `Gap212.Sieve.kernelCoeff_mul_of_coprime` and
`Gap212.Sieve.kernelCoeffTotient_mul_of_coprime`. With that in hand the coefficients are packaged
as genuine `ArithmeticFunction`s carrying `ArithmeticFunction.IsMultiplicative` —
`Gap212.Sieve.kernelArith` and `Gap212.Sieve.kernelArithTotient` — which is the shape
`ArithmeticFunction.IsMultiplicative.eulerProduct_tprod` consumes.

## Four facts about `gcd` and `lcm`

Of the four ingredients the bijection needs, `Gap212.Sieve.Polymath41Kernel` supplied the
first; the other three are general facts about `Nat.gcd`, `Nat.lcm` and multiplicative functions
that **Mathlib does not state**, and they are proved here in their general form rather than
specialised to the fibre:

* *the map lands*: `Gap212.Sieve.lcm_gcd_left_of_lcm_eq_mul`, in
  `Gap212.Sieve.Polymath41Kernel`, via the `gcd`/`lcm` distributivity
  `Gap212.Sieve.gcd_lcm_distrib` proved there.
* *the inverse lands*: `Gap212.Sieve.lcm_mul_lcm_of_coprime`, `[ab,a'b'] = [a,a']·[b,b']` whenever
  `aa'` and `bb'` are coprime. Mathlib has neither this nor its `gcd` analogue.
* *the two are mutually inverse*: `Gap212.Sieve.gcd_mul_eq_left_of_coprime`, `(ab,m) = a` for
  `a ∣ m` and `b` coprime to `m`. The other direction, `(d,m)·(d,n) = d` for `d ∣ mn`, *is* in
  Mathlib as `Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime`.
* *the summand splits*: `Gap212.Sieve.IsMultiplicative.map_eq_gcd_mul_gcd`, i.e.
  `f d = f((d,m))·f((d,n))` for multiplicative `f` and `d ∣ mn` — the previous item fed through
  `ArithmeticFunction.IsMultiplicative.map_mul_of_coprime`, with
  `Gap212.Sieve.moebius_eq_gcd_mul_gcd` its `μ` instance. This is the gcd-side form; because
  `Gap212.Sieve.lcmFibre_mul` presents the bijection as an image under reassembly, the proofs below
  reach for the equivalent product-side form directly, and `Complex.cpow` splits by
  `Complex.natCast_mul_natCast_cpow`.

The three new ones are stated for `Nat` and for an arbitrary multiplicative function, with no
reference to the sieve.

## Main definitions

* `Gap212.Sieve.kernelArith`, `Gap212.Sieve.kernelArithTotient`: the two coefficients bundled as
  `ArithmeticFunction`s.

## Main results

* `Gap212.Sieve.lcm_mul_lcm_of_coprime`, `Gap212.Sieve.gcd_mul_eq_left_of_coprime`,
  `Gap212.Sieve.IsMultiplicative.map_eq_gcd_mul_gcd`: the three general facts.
* `Gap212.Sieve.lcmFibre_mul`: the multiplicativity bijection as an identity of `Finset`s, and
  `Gap212.Sieve.sum_lcmFibre_mul` the reindexing of an arbitrary sum along it.
* `Gap212.Sieve.kernelCoeff_mul_of_coprime`, `Gap212.Sieve.kernelCoeffTotient_mul_of_coprime`, and
  their bundled forms `Gap212.Sieve.isMultiplicative_kernelArith`,
  `Gap212.Sieve.isMultiplicative_kernelArithTotient`: multiplicativity of the two kernels'
  Dirichlet coefficients.
* `Gap212.Sieve.kernelCoeff_prime_pow`, `Gap212.Sieve.kernelCoeffTotient_prime_pow`: `a(p^e) = 0`
  for `e ≥ 2`, which is what makes the source's `1 + a(p)` the *whole* local factor rather than a
  truncation of `∑_k a(p^k)`.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset
open scoped ArithmeticFunction.Moebius

/-! ## Three general facts Mathlib lacks

Each is stated with no reference to the sieve: `Nat` and, for the last one, an arbitrary
multiplicative arithmetic function. -/

/-- **`lcm` is multiplicative across a coprime splitting**: if `a·a'` is coprime to `b·b'` then

  `[ab, a'b'] = [a,a'] · [b,b']`.

`Nat.Coprime.lcm_mul_lcm` does not exist in Mathlib, nor does the `gcd` analogue. The hypothesis is
the weakest one that works — it is exactly "each of `a, a'` is coprime to each of `b, b'`" — and in
the intended application `a, a' ∣ m`, `b, b' ∣ n` with `m` coprime to `n`, which supplies it.

Both divisibilities are elementary; the content is that `[a,a']·[b,b']` divides `[ab,a'b']`, which
needs the coprimality to turn "each factor divides" into "the product divides". -/
theorem lcm_mul_lcm_of_coprime {a a' b b' : ℕ} (h : Nat.Coprime (a * a') (b * b')) :
    Nat.lcm (a * b) (a' * b') = Nat.lcm a a' * Nat.lcm b b' := by
  have hcop : Nat.Coprime (Nat.lcm a a') (Nat.lcm b b') :=
    (h.coprime_dvd_left (Nat.lcm_dvd_mul a a')).coprime_dvd_right (Nat.lcm_dvd_mul b b')
  refine Nat.dvd_antisymm (Nat.lcm_dvd ?_ ?_) ?_
  · exact Nat.mul_dvd_mul (Nat.dvd_lcm_left _ _) (Nat.dvd_lcm_left _ _)
  · exact Nat.mul_dvd_mul (Nat.dvd_lcm_right _ _) (Nat.dvd_lcm_right _ _)
  · refine hcop.mul_dvd_of_dvd_of_dvd (Nat.lcm_dvd ?_ ?_) (Nat.lcm_dvd ?_ ?_)
    · exact (Nat.dvd_mul_right a b).trans (Nat.dvd_lcm_left _ _)
    · exact (Nat.dvd_mul_right a' b').trans (Nat.dvd_lcm_right _ _)
    · exact (Nat.dvd_mul_left b a).trans (Nat.dvd_lcm_left _ _)
    · exact (Nat.dvd_mul_left b' a').trans (Nat.dvd_lcm_right _ _)

/-- **A coprime factor is invisible to a `gcd` it is coprime to**: if `a ∣ m` and `b` is coprime to
`m` then `(ab, m) = a`.

This is the left inverse of `d ↦ ((d,m),(d,n))` on the reassembled `d = ab`. Mathlib has the
cancellation `Nat.Coprime.gcd_mul_right_cancel` but not this one-step consequence. -/
theorem gcd_mul_eq_left_of_coprime {a b m : ℕ} (ha : a ∣ m) (hb : Nat.Coprime b m) :
    Nat.gcd (a * b) m = a := by
  rw [hb.gcd_mul_right_cancel a, Nat.gcd_eq_left ha]

/-- **A multiplicative function on a divisor of a coprime product splits along the two parts**: for
`f` multiplicative, `m` coprime to `n` and `d ∣ m·n`,

  `f(d) = f((d,m)) · f((d,n))`.

The splitting `d = (d,m)·(d,n)` is Mathlib's `Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime`; what is
new is pushing a multiplicative function through it, which needs the two parts to be coprime.
Stated for a general `ArithmeticFunction` over a `CommMonoidWithZero`, so `μ` is one instance of
it. -/
theorem IsMultiplicative.map_eq_gcd_mul_gcd {R : Type*} [CommMonoidWithZero R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {d m n : ℕ} (hmn : Nat.Coprime m n)
    (hd : d ∣ m * n) : f d = f (Nat.gcd d m) * f (Nat.gcd d n) := by
  have hsplit : Nat.gcd d m * Nat.gcd d n = d :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hmn).2 hd
  have hcop : Nat.Coprime (Nat.gcd d m) (Nat.gcd d n) :=
    (hmn.coprime_dvd_left (Nat.gcd_dvd_right d m)).coprime_dvd_right (Nat.gcd_dvd_right d n)
  rw [← hf.map_mul_of_coprime hcop, hsplit]

/-- `μ(d) = μ((d,m))·μ((d,n))` for `d ∣ mn` with `m` coprime to `n` — the Möbius instance of
`Gap212.Sieve.IsMultiplicative.map_eq_gcd_mul_gcd`, which is how the two `μ` factors of
`Gap212.Sieve.kernelCoeff`'s summand are separated. -/
theorem moebius_eq_gcd_mul_gcd {d m n : ℕ} (hmn : Nat.Coprime m n) (hd : d ∣ m * n) :
    μ d = μ (Nat.gcd d m) * μ (Nat.gcd d n) :=
  IsMultiplicative.map_eq_gcd_mul_gcd ArithmeticFunction.isMultiplicative_moebius hmn hd

/-- **Reassembling recovers both parts**: for `m` coprime to `n`, `a ∣ m` and `b ∣ n`,

  `(ab, m) = a`  and  `(ab, n) = b`.

Two applications of `Gap212.Sieve.gcd_mul_eq_left_of_coprime`; stated together because the
reassembly map `((a,a'),(b,b')) ↦ (ab,a'b')` is injective exactly because *both* hold. -/
theorem gcd_mul_split_of_coprime {a b m n : ℕ} (hmn : Nat.Coprime m n) (ha : a ∣ m) (hb : b ∣ n) :
    Nat.gcd (a * b) m = a ∧ Nat.gcd (a * b) n = b :=
  ⟨gcd_mul_eq_left_of_coprime ha (hmn.symm.coprime_dvd_left hb),
    Nat.mul_comm b a ▸ gcd_mul_eq_left_of_coprime hb (hmn.coprime_dvd_left ha)⟩

/-! ## The fibre over a product is the reassembly of a product of fibres -/

/-- **Membership in `Gap212.Sieve.lcmFibre`, with the two divisibilities dropped.** The definition
cuts `n.divisors ×ˢ n.divisors` down by `[q.1,q.2] = n`, but for `n ≠ 0` that condition already
forces `q.1 ∣ n` and `q.2 ∣ n`, so the product is no constraint at all. Every proof below uses this
form rather than unfolding the `Finset`. -/
theorem mem_lcmFibre {n : ℕ} {q : ℕ × ℕ} : q ∈ lcmFibre n ↔ n ≠ 0 ∧ Nat.lcm q.1 q.2 = n := by
  simp only [lcmFibre, mem_filter, mem_product, Nat.mem_divisors]
  exact ⟨fun h => ⟨h.1.1.2, h.2⟩, fun ⟨hn, hl⟩ =>
    ⟨⟨⟨hl ▸ Nat.dvd_lcm_left q.1 q.2, hn⟩, hl ▸ Nat.dvd_lcm_right q.1 q.2, hn⟩, hl⟩⟩

/-- **The multiplicativity bijection, as an identity of `Finset`s**: for `m` coprime to `n`, both
nonzero,

  `{(d,d') : [d,d'] = mn}` = the image of `{[a,a'] = m} × {[b,b'] = n}`
  under `((a,a'),(b,b')) ↦ (ab, a'b')`.

This is the source's Euler factorisation of the kernel at the level of index sets. The
forward inclusion is `Gap212.Sieve.lcm_gcd_left_of_lcm_eq_mul` run at `m` and at `n`, which is
where the `gcd`/`lcm` distributivity of `Gap212.Sieve.Polymath41Kernel` is spent; the reverse
is `Gap212.Sieve.lcm_mul_lcm_of_coprime`. -/
theorem lcmFibre_mul {m n : ℕ} (hmn : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0) :
    lcmFibre (m * n)
      = (lcmFibre m ×ˢ lcmFibre n).image fun r => (r.1.1 * r.2.1, r.1.2 * r.2.2) := by
  have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  ext ⟨d, d'⟩
  simp only [mem_image, Finset.mem_product, mem_lcmFibre]
  constructor
  · rintro ⟨-, hl⟩
    obtain ⟨hd, hd'⟩ : d ≠ 0 ∧ d' ≠ 0 := by simpa [not_or] using hl.trans_ne hmn0
    refine ⟨((Nat.gcd d m, Nat.gcd d' m), (Nat.gcd d n, Nat.gcd d' n)),
      ⟨⟨hm, lcm_gcd_left_of_lcm_eq_mul hd hd' hm hl⟩,
        ⟨hn, lcm_gcd_left_of_lcm_eq_mul hd hd' hn (hl.trans (Nat.mul_comm m n))⟩⟩, ?_⟩
    exact Prod.ext ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hmn).2 (hl ▸ Nat.dvd_lcm_left d d'))
      ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hmn).2 (hl ▸ Nat.dvd_lcm_right d d'))
  · rintro ⟨⟨⟨a, a'⟩, b, b'⟩, ⟨⟨-, hlm⟩, -, hln⟩, ⟨⟩⟩
    have ha : a ∣ m := hlm ▸ Nat.dvd_lcm_left a a'
    have ha' : a' ∣ m := hlm ▸ Nat.dvd_lcm_right a a'
    have hb : b ∣ n := hln ▸ Nat.dvd_lcm_left b b'
    have hb' : b' ∣ n := hln ▸ Nat.dvd_lcm_right b b'
    have hcop : Nat.Coprime (a * a') (b * b') :=
      (((hmn.mul_left hmn).mul_right (hmn.mul_left hmn)).coprime_dvd_left
        (mul_dvd_mul ha ha')).coprime_dvd_right (mul_dvd_mul hb hb')
    exact ⟨hmn0, by rw [lcm_mul_lcm_of_coprime hcop, hlm, hln]⟩

/-- Reassembly is injective on the product of fibres — the second half of what
`Finset.sum_image` needs, and immediate from `Gap212.Sieve.gcd_mul_split_of_coprime`: `(ab, a'b')`
determines `a = (ab, m)`, `b = (ab, n)`, `a' = (a'b', m)`, `b' = (a'b', n)`. -/
theorem lcmFibre_mul_injOn {m n : ℕ} (hmn : Nat.Coprime m n) :
    ∀ r ∈ lcmFibre m ×ˢ lcmFibre n, ∀ r' ∈ lcmFibre m ×ˢ lcmFibre n,
      ((r.1.1 * r.2.1, r.1.2 * r.2.2) : ℕ × ℕ) = (r'.1.1 * r'.2.1, r'.1.2 * r'.2.2) → r = r' := by
  have key : ∀ r ∈ lcmFibre m ×ˢ lcmFibre n,
      Nat.gcd (r.1.1 * r.2.1) m = r.1.1 ∧ Nat.gcd (r.1.1 * r.2.1) n = r.2.1 ∧
        Nat.gcd (r.1.2 * r.2.2) m = r.1.2 ∧ Nat.gcd (r.1.2 * r.2.2) n = r.2.2 := by
    rintro ⟨⟨a, a'⟩, b, b'⟩ hr
    rw [Finset.mem_product, mem_lcmFibre, mem_lcmFibre] at hr
    obtain ⟨⟨-, hlm⟩, -, hln⟩ := hr
    obtain ⟨h1, h2⟩ := gcd_mul_split_of_coprime hmn (hlm ▸ Nat.dvd_lcm_left a a')
      (hln ▸ Nat.dvd_lcm_left b b')
    obtain ⟨h3, h4⟩ := gcd_mul_split_of_coprime hmn (hlm ▸ Nat.dvd_lcm_right a a')
      (hln ▸ Nat.dvd_lcm_right b b')
    exact ⟨h1, h2, h3, h4⟩
  intro r hr r' hr' h
  obtain ⟨e1, e2, e3, e4⟩ := key r hr
  obtain ⟨f1, f2, f3, f4⟩ := key r' hr'
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · rw [← e1, ← f1, h₁]
  · rw [← e3, ← f3, h₂]
  · rw [← e2, ← f2, h₁]
  · rw [← e4, ← f4, h₂]

/-- **Any sum over the fibre of a product factors as a sum over the product of fibres.** The
`Finset` identity `Gap212.Sieve.lcmFibre_mul` plus injectivity, with the summand still arbitrary —
the reindexing is done once here, so the two kernels only have to split their own summand. -/
theorem sum_lcmFibre_mul {M : Type*} [AddCommMonoid M] {m n : ℕ} (hmn : Nat.Coprime m n)
    (hm : m ≠ 0) (hn : n ≠ 0) (f : ℕ × ℕ → M) :
    ∑ q ∈ lcmFibre (m * n), f q
      = ∑ r ∈ lcmFibre m ×ˢ lcmFibre n, f (r.1.1 * r.2.1, r.1.2 * r.2.2) := by
  rw [lcmFibre_mul hmn hm hn, Finset.sum_image (lcmFibre_mul_injOn hmn)]

/-! ## Multiplicativity of the two kernels' coefficients -/

/-- **The numerator shared by both kernels is multiplicative.** For `m` coprime to `n`, both
nonzero,

  `∑_{[d,d']=mn} μ(d)μ(d')d^{-s}(d')^{-s'} = (∑_{[d,d']=m} ⋯)(∑_{[d,d']=n} ⋯)`.

Over the reindexing of `Gap212.Sieve.sum_lcmFibre_mul` the summand splits because `μ` is
multiplicative on the coprime factors `a ∣ m`, `b ∣ n` and because `Complex.cpow` of a product of
nonnegative reals splits. Both kernels' coefficients are this quotiented by a multiplicative
denominator, so this is the whole content. -/
theorem sum_lcmFibre_mul_of_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0)
    (s s' : ℂ) :
    ∑ q ∈ lcmFibre (m * n), (μ q.1 : ℂ) * (μ q.2 : ℂ) * (q.1 : ℂ) ^ (-s) * (q.2 : ℂ) ^ (-s')
      = (∑ q ∈ lcmFibre m, (μ q.1 : ℂ) * (μ q.2 : ℂ) * (q.1 : ℂ) ^ (-s) * (q.2 : ℂ) ^ (-s')) *
        ∑ q ∈ lcmFibre n, (μ q.1 : ℂ) * (μ q.2 : ℂ) * (q.1 : ℂ) ^ (-s) * (q.2 : ℂ) ^ (-s') := by
  rw [sum_lcmFibre_mul hmn hm hn, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun t ht => ?_
  rw [mem_lcmFibre] at hr ht
  have hcop : ∀ {a b : ℕ}, a ∣ m → b ∣ n → Nat.Coprime a b := fun ha hb =>
    (hmn.coprime_dvd_left ha).coprime_dvd_right hb
  have h1 : Nat.Coprime r.1 t.1 :=
    hcop (hr.2 ▸ Nat.dvd_lcm_left r.1 r.2) (ht.2 ▸ Nat.dvd_lcm_left t.1 t.2)
  have h2 : Nat.Coprime r.2 t.2 :=
    hcop (hr.2 ▸ Nat.dvd_lcm_right r.1 r.2) (ht.2 ▸ Nat.dvd_lcm_right t.1 t.2)
  have hmu : ∀ {a b : ℕ}, Nat.Coprime a b → ((μ (a * b) : ℤ) : ℂ) = (μ a : ℂ) * (μ b : ℂ) := by
    intro a b h
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h]
    push_cast
    ring
  simp only [hmu h1, hmu h2, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

/-! ## The coefficient vanishes at higher prime powers

Multiplicativity alone would make the local factor of `K` at `p` the whole series
`∑_k a(p^k)`. The source writes only `1 + a(p)`, and this section is why that is not a
truncation: every term with `k ≥ 2` is zero, so `Gap212.Sieve.one_add_kernelCoeff_prime` computes
the *entire* local factor. -/

/-- **The numerator vanishes over the fibre of a square-full prime power.** For `p` prime and
`e ≥ 2`, every pair with `[d,d'] = p^e` has `μ(d)μ(d') = 0`.

Both `d` and `d'` are powers of `p`, say `p^i` and `p^j`, and `[p^i,p^j] = p^{max(i,j)}`, so one of
`i, j` equals `e`. That factor is `p^e` with `e ≥ 2`, which is not squarefree, so its `μ` is
`0`. -/
theorem sum_lcmFibre_prime_pow {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) (s s' : ℂ) :
    ∑ q ∈ lcmFibre (p ^ e),
        (μ q.1 : ℂ) * (μ q.2 : ℂ) * (q.1 : ℂ) ^ (-s) * (q.2 : ℂ) ^ (-s') = 0 := by
  have hz : (μ (p ^ e) : ℤ) = 0 := by
    refine ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun hsq => ?_
    exact hp.one_lt.ne' (Nat.isUnit_iff.1 (hsq p (sq p ▸ pow_dvd_pow p he)))
  refine Finset.sum_eq_zero ?_
  rintro ⟨d, d'⟩ hq
  obtain ⟨-, hl⟩ := mem_lcmFibre.1 hq
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 (hl ▸ Nat.dvd_lcm_left d d')
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 (hl ▸ Nat.dvd_lcm_right (p ^ i) d')
  replace hl : Nat.lcm (p ^ i) (p ^ j) = p ^ e := hl
  have hpow : ∀ x y : ℕ, p ^ x = p ^ y → x = y := fun _ _ h => Nat.pow_right_injective hp.two_le h
  have hmax : i = e ∨ j = e := by
    rcases le_total i j with h | h
    · exact Or.inr (hpow j e (by rw [← hl, Nat.lcm_eq_right (pow_dvd_pow p h)]))
    · exact Or.inl (hpow i e (by rw [← hl, Nat.lcm_comm, Nat.lcm_eq_right (pow_dvd_pow p h)]))
  rcases hmax with h | h <;> rw [h] <;> simp [hz]

/-- **`a` vanishes at `p^e` for `e ≥ 2`**, so the local factor of the source's `K` at `p` really is
just `1 + a(p)` and `Gap212.Sieve.one_add_kernelCoeff_prime` computes all of it. -/
theorem kernelCoeff_prime_pow {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) (s s' : ℂ) :
    kernelCoeff s s' (p ^ e) = 0 := by
  rw [kernelCoeff, sum_lcmFibre_prime_pow hp he, zero_div]

/-- The same for the totient kernel: `a^φ(p^e) = 0` for `e ≥ 2`, so
`Gap212.Sieve.one_add_kernelCoeffTotient_prime` likewise computes the whole local factor. -/
theorem kernelCoeffTotient_prime_pow {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) (s s' : ℂ) :
    kernelCoeffTotient s s' (p ^ e) = 0 := by
  rw [kernelCoeffTotient, sum_lcmFibre_prime_pow hp he, zero_div]

/-- `a(0) = 0`, because the fibre over `0` is empty *and* the denominator is `0`. Needed to make
`Gap212.Sieve.kernelCoeff` an `ArithmeticFunction`. -/
theorem kernelCoeff_zero (s s' : ℂ) : kernelCoeff s s' 0 = 0 := by simp [kernelCoeff]

/-- `a^φ(0) = 0`, since `φ(0) = 0`. -/
theorem kernelCoeffTotient_zero (s s' : ℂ) : kernelCoeffTotient s s' 0 = 0 := by
  simp [kernelCoeffTotient]

/-- **The Dirichlet coefficient of the source's kernel is multiplicative**: `a(mn) = a(m)a(n)` for
`m` coprime to `n`. With `Gap212.Sieve.one_add_kernelCoeff_prime` it says that the source's `K` has
Euler factor `K_p` at every prime.

No nonvanishing hypothesis is needed: at `m = 0` or `n = 0` both sides are `0`. -/
theorem kernelCoeff_mul_of_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (s s' : ℂ) :
    kernelCoeff s s' (m * n) = kernelCoeff s s' m * kernelCoeff s s' n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [kernelCoeff_zero]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [kernelCoeff_zero]
  rw [kernelCoeff, kernelCoeff, kernelCoeff, sum_lcmFibre_mul_of_coprime hmn hm hn, Nat.cast_mul]
  ring

/-- **The totient kernel's coefficient is multiplicative too**, by the same numerator computation
and `Nat.totient_mul`. A separate theorem because the two kernels are separate assertions: only
`Gap212.Sieve.sum_lcmFibre_mul_of_coprime` is shared. -/
theorem kernelCoeffTotient_mul_of_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (s s' : ℂ) :
    kernelCoeffTotient s s' (m * n)
      = kernelCoeffTotient s s' m * kernelCoeffTotient s s' n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [kernelCoeffTotient_zero]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [kernelCoeffTotient_zero]
  rw [kernelCoeffTotient, kernelCoeffTotient, kernelCoeffTotient,
    sum_lcmFibre_mul_of_coprime hmn hm hn, Nat.totient_mul hmn, Nat.cast_mul]
  ring

/-! ## The coefficients as multiplicative arithmetic functions

With multiplicativity proved, `Gap212.Sieve.kernelCoeff` and `Gap212.Sieve.kernelCoeffTotient`
are bundled as multiplicative arithmetic functions. -/

/-- The source's kernel coefficient as an `ArithmeticFunction` — the shape
`ArithmeticFunction.IsMultiplicative.eulerProduct_tprod` consumes. -/
noncomputable def kernelArith (s s' : ℂ) : ArithmeticFunction ℂ :=
  ⟨kernelCoeff s s', kernelCoeff_zero s s'⟩

/-- `kernelArith s s' n = kernelCoeff s s' n`. -/
@[simp] theorem kernelArith_apply (s s' : ℂ) (n : ℕ) :
    kernelArith s s' n = kernelCoeff s s' n := rfl

/-- The totient kernel's coefficient as an `ArithmeticFunction`. -/
noncomputable def kernelArithTotient (s s' : ℂ) : ArithmeticFunction ℂ :=
  ⟨kernelCoeffTotient s s', kernelCoeffTotient_zero s s'⟩

/-- `kernelArithTotient s s' n = kernelCoeffTotient s s' n`. -/
@[simp] theorem kernelArithTotient_apply (s s' : ℂ) (n : ℕ) :
    kernelArithTotient s s' n = kernelCoeffTotient s s' n := rfl

/-- **`Gap212.Sieve.kernelArith` is multiplicative.** Together with
`Gap212.Sieve.one_add_kernelCoeff_prime` this is the source's Euler factorisation of `K`, up to
the summability that licenses the product, which is step 2
(`Gap212.Sieve.summable_norm_kernelCoeff`). -/
theorem isMultiplicative_kernelArith (s s' : ℂ) :
    ArithmeticFunction.IsMultiplicative (kernelArith s s') :=
  ⟨kernelCoeff_one s s', fun h => kernelCoeff_mul_of_coprime h s s'⟩

/-- **`Gap212.Sieve.kernelArithTotient` is multiplicative**, the companion of
`Gap212.Sieve.isMultiplicative_kernelArith` for the lemma's closing sentence. -/
theorem isMultiplicative_kernelArithTotient (s s' : ℂ) :
    ArithmeticFunction.IsMultiplicative (kernelArithTotient s s') :=
  ⟨kernelCoeffTotient_one s s', fun h => kernelCoeffTotient_mul_of_coprime h s s'⟩

end Gap212.Sieve
