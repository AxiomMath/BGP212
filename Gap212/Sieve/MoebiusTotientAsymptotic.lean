/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MoebiusTotient
public import PrimeNumberTheoremAnd.IEANTN.Mertens
public meta import Gap212.Attr

/-!
# The Möbius-totient product over a coprimality class

Let `V` be a nonzero natural number and `P(y) = ∏_{p ≤ y} p`. Two statements are proved here.

* The **exact identity**: the divisor sum of `μ/φ` over the divisors of `P(y)` coprime to `V` is
  the finite product `∏_{p ≤ y, p ∤ V}(1 - 1/(p-1))`. This is pure multiplicativity — it is
  `Gap212.Sieve.sum_moebius_div_totient_eq_prod` applied at `P(y)` with the primes dividing `V`
  removed, and the work is the Finset bookkeeping that identifies the two index sets.

* The **limit**: `log y` times that product converges, to
  `e^{-γ} · (V/φ(V)) · ∏_{p ∤ V}(1 - 1/(p-1)^2)`.

The limit is *elementary*: no prime number theorem. The route is the exact factorisation
`1 - 1/(p-1) = (1 - 1/p)(1 - 1/(p-1)^2)` of `Gap212.Sieve.one_sub_inv_sub_one_prime`, which splits
the product into a Mertens factor and an absolutely convergent correction. Mertens' third theorem —
`Mertens.prod_one_minus_div_prime_eq` together with `Mertens.E₃.bound'` of
`PrimeNumberTheoremAnd` — supplies `log y · ∏_{p ≤ y}(1 - 1/p) → e^{-γ}`; dividing out the primes
dividing `V` costs the factor `∏_{p ∣ V}(1 - 1/p) = φ(V)/V`; and `∑_p 1/(p-1)^2 < ∞` makes the
correction's partial products converge to its infinite product.

The module docstring of `Gap212.Sieve.MoebiusTotient` explains why the corresponding sum over the
integers `f ≤ y` coprime to `V` has no `1/log y` main term: its Dirichlet series has a zero at
`s = 0`, not a pole. The `1/log y` lives over the divisors of `P(y)`.

## Main results

* `Gap212.Sieve.sum_moebius_div_totient_primorial_coprime`: the exact identity.
* `Gap212.Sieve.tendsto_log_mul_prod_one_sub_inv_sub_one`: the limit.
-/

@[expose] public section

open ArithmeticFunction Filter Finset Topology
open scoped ArithmeticFunction.totient ArithmeticFunction.Moebius

namespace Gap212.Sieve

/-! ### The exact identity -/

/-- For squarefree `N`, the `μ/φ` divisor sum restricted to the divisors coprime to `V` is the
Euler product over the prime factors of `N` that do not divide `V`. -/
theorem sum_moebius_div_totient_coprime_eq_prod {N V : ℕ} (hN : Squarefree N) :
    ∑ f ∈ N.divisors with Nat.Coprime f V, (μ f : ℝ) / (f.totient : ℝ)
      = ∏ p ∈ N.primeFactors with ¬ p ∣ V, (1 - 1 / ((p : ℝ) - 1)) := by
  have hN0 : N ≠ 0 := hN.ne_zero
  have hSsub : N.primeFactors.filter (fun p => ¬ p ∣ V) ⊆ N.primeFactors :=
    Finset.filter_subset _ _
  have hSprime : ∀ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ V), p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (hSsub hp)
  have hnpf : (∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ V), p).primeFactors
      = N.primeFactors.filter (fun p => ¬ p ∣ V) := Nat.primeFactors_prod hSprime
  have hndvd : (∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ V), p) ∣ N :=
    (Finset.prod_dvd_prod_of_subset _ _ _ hSsub).trans (Nat.prod_primeFactors_dvd N)
  have hnsf : Squarefree (∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ V), p) :=
    hN.squarefree_of_dvd hndvd
  have hncop : Nat.Coprime (∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ V), p) V :=
    Nat.Coprime.prod_left fun p hp =>
      ((hSprime p hp).coprime_iff_not_dvd).2 (Finset.mem_filter.1 hp).2
  have hdiv : N.divisors.filter (fun f => Nat.Coprime f V)
      = (∏ p ∈ N.primeFactors.filter (fun p => ¬ p ∣ V), p).divisors := by
    ext f
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨fun h => ⟨?_, hnsf.ne_zero⟩, fun h => ⟨⟨h.1.trans hndvd, hN0⟩, ?_⟩⟩
    · obtain ⟨⟨hfN, -⟩, hfV⟩ := h
      have hfsf : Squarefree f := hN.squarefree_of_dvd hfN
      have hsub : f.primeFactors ⊆ N.primeFactors.filter (fun p => ¬ p ∣ V) := by
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpf : p ∣ f := Nat.dvd_of_mem_primeFactors hp
        refine Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hpp, hpf.trans hfN, hN0⟩, ?_⟩
        exact (hpp.coprime_iff_not_dvd).1 (Nat.Coprime.coprime_dvd_left hpf hfV)
      calc f = ∏ p ∈ f.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hfsf).symm
        _ ∣ _ := Finset.prod_dvd_prod_of_subset _ _ _ hsub
    · exact Nat.Coprime.coprime_dvd_left h.1 hncop
  rw [hdiv]
  have h := sum_moebius_div_totient_eq_prod hnsf
  rwa [hnpf] at h

/-- The exact Möbius-totient identity: with `P(y) = ∏_{p ≤ y} p`,
`∑_{f ∣ P(y), (f,V)=1} μ(f)/φ(f) = ∏_{p ≤ y, p ∤ V}(1 - 1/(p-1))`. -/
@[gap212 "lem_moebius_totient_asymptotic"]
theorem sum_moebius_div_totient_primorial_coprime (V : ℕ) (y : ℝ) :
    ∑ f ∈ (primorial ⌊y⌋₊).divisors with Nat.Coprime f V, (μ f : ℝ) / (f.totient : ℝ)
      = ∏ p ∈ Finset.Ioc 0 ⌊y⌋₊ with (p.Prime ∧ ¬ p ∣ V), (1 - 1 / ((p : ℝ) - 1)) := by
  rw [sum_moebius_div_totient_coprime_eq_prod (squarefree_primorial _), primeFactors_primorial]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, Nat.mem_primesLE, Finset.mem_Ioc]
  exact ⟨fun h => ⟨⟨h.1.2.pos, h.1.1⟩, h.1.2, h.2⟩, fun h => ⟨⟨h.1.2, h.2.1⟩, h.2.2⟩⟩

/-! ### The Mertens factor -/

/-- `φ(V)/V = ∏_{p ∣ V}(1 - 1/p)`. -/
theorem totient_div_eq_prod_one_sub_inv {V : ℕ} (hV : V ≠ 0) :
    (V.totient : ℝ) / (V : ℝ) = ∏ p ∈ V.primeFactors, (1 - 1 / (p : ℝ)) := by
  have hV0 : (V : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hV
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors V)
  push_cast at h
  rw [h]
  field_simp

/-- `∏_{p ∣ V}(1 - 1/p)` is positive. -/
theorem prod_primeFactors_one_sub_inv_pos (V : ℕ) :
    0 < ∏ p ∈ V.primeFactors, (1 - 1 / (p : ℝ)) := by
  refine Finset.prod_pos fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  linarith

/-- Mertens' third theorem in the shape used here: `log y · ∏_{p ≤ y}(1 - 1/p) → e^{-γ}`. -/
theorem tendsto_log_mul_prod_one_sub_inv :
    Tendsto (fun y : ℝ => Real.log y * ∏ p ∈ Finset.Ioc 0 ⌊y⌋₊ with p.Prime, (1 - 1 / (p : ℝ)))
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  have hE : Tendsto Mertens.E₃ atTop (nhds 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).1 Mertens.E₃.bound'
  have hexp : Tendsto (fun y : ℝ => Real.exp (Mertens.E₃ y)) atTop (nhds 1) := by
    simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hE
  have h1 : Tendsto (fun y : ℝ => Real.exp (-Real.eulerMascheroniConstant) *
      Real.exp (Mertens.E₃ y)) atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
    simpa using hexp.const_mul (Real.exp (-Real.eulerMascheroniConstant))
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
  rw [Mertens.prod_one_minus_div_prime_eq hy]
  have hlog : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  field_simp

/-! ### The convergent correction -/

/-- The series `∑_{p prime, p ∤ V} 1/(p-1)^2` converges. -/
theorem summable_corr_aux (V : ℕ) :
    Summable (fun p : ℕ => if p.Prime ∧ ¬ p ∣ V then 1 / ((p : ℝ) - 1) ^ 2 else 0) := by
  have hb : Summable (fun p : ℕ => 4 / (p : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using (Real.summable_one_div_nat_pow.2 one_lt_two).mul_left (4 : ℝ)
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hb
  · split_ifs
    · positivity
    · norm_num
  · split_ifs with h
    · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.1.two_le
      have hp0 : (p : ℝ) ≠ 0 := by intro hh; rw [hh] at hp2; norm_num at hp2
      have hp1 : (p : ℝ) - 1 ≠ 0 := by
        intro hh; rw [sub_eq_zero] at hh; rw [hh] at hp2; norm_num at hp2
      have hA : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
      have hB : (0 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
      rw [← sub_nonneg, show 4 / (p : ℝ) ^ 2 - 1 / ((p : ℝ) - 1) ^ 2
          = (4 * ((p : ℝ) - 1) ^ 2 - (p : ℝ) ^ 2) / ((p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2) by
        field_simp]
      refine div_nonneg ?_ (by positivity)
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3 * (p:ℝ) - 2)
        (by linarith : (0:ℝ) ≤ (p:ℝ) - 2)]
    · positivity

/-- The product `∏_{p prime, p ∤ V}(1 - 1/(p-1)^2)` converges. -/
theorem multipliable_corr (V : ℕ) :
    Multipliable (fun p : ℕ => if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) := by
  have hs : Summable (fun p : ℕ => -(if p.Prime ∧ ¬ p ∣ V then 1 / ((p : ℝ) - 1) ^ 2 else 0)) :=
    (summable_corr_aux V).neg
  have h := Real.multipliable_one_add_of_summable hs
  have heq : (fun p : ℕ => 1 + -(if p.Prime ∧ ¬ p ∣ V then 1 / ((p : ℝ) - 1) ^ 2 else 0))
      = fun p : ℕ => if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 := by
    funext p; split_ifs <;> ring
  rwa [heq] at h

/-- The correction's partial products over the primes `≤ y` converge to its infinite product. -/
theorem tendsto_prod_corr (V : ℕ) :
    Tendsto (fun y : ℝ => ∏ p ∈ Finset.Ioc 0 ⌊y⌋₊ with (p.Prime ∧ ¬ p ∣ V),
        (1 - 1 / ((p : ℝ) - 1) ^ 2))
      atTop (nhds (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)) := by
  have hfloor : Tendsto (fun y : ℝ => Finset.Iic ⌊y⌋₊) atTop atTop :=
    tendsto_atTop_finset_of_monotone
      (fun _ _ hab => Finset.Iic_subset_Iic.2 (Nat.floor_mono hab))
      (fun x => ⟨(x : ℝ), by simp⟩)
  have hHP : Tendsto (fun s : Finset ℕ =>
      ∏ p ∈ s, if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) atTop
      (nhds (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)) :=
    (multipliable_corr V).hasProd
  refine (hHP.comp hfloor).congr fun y => ?_
  simp only [Function.comp_apply]
  have h0 : Finset.Iic ⌊y⌋₊ = insert 0 (Finset.Ioc 0 ⌊y⌋₊) := by
    ext p; simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Ioc]; omega
  rw [h0, Finset.prod_insert (by simp), Finset.prod_filter]
  simp only [Nat.not_prime_zero, false_and, if_false, one_mul]

/-- For even `V` the correction's infinite product is positive: every factor is, the prime `2`
being excluded by `2 ∣ V`. -/
theorem tprod_corr_pos {V : ℕ} (hV2 : 2 ∣ V) :
    0 < ∏' p : ℕ, if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 := by
  have hs : Summable (fun p : ℕ => -(if p.Prime ∧ ¬ p ∣ V then 1 / ((p : ℝ) - 1) ^ 2 else 0)) :=
    (summable_corr_aux V).neg
  have hlog : Summable
      (fun p : ℕ => Real.log (if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)) :=
    (Real.summable_log_one_add_of_summable hs).congr fun p => by congr 1; split_ifs <;> ring
  have hpos : ∀ p : ℕ, (0 : ℝ) < if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 := by
    intro p
    split_ifs with h
    · have hne2 : p ≠ 2 := fun hh => h.2 (hh ▸ hV2)
      have hp3 : 3 ≤ p := by have := h.1.two_le; omega
      have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      have h4 : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
      rw [sub_pos, div_lt_one (by nlinarith)]
      linarith
    · norm_num
  rw [(Real.hasProd_of_hasSum_log hpos hlog.hasSum).tprod_eq]
  exact Real.exp_pos _

/-! ### The limit -/

/-- The Möbius-totient limit. For `V ≥ 2` squarefree and even,
`log y · ∏_{p ≤ y, p ∤ V}(1 - 1/(p-1)) → e^{-γ} · (V/φ(V)) · ∏_{p ∤ V}(1 - 1/(p-1)^2)`.

Evenness is what makes the limit nonzero: for odd `V` the prime `2` survives in the product,
`1 - 1/(2-1) = 0`, and both sides are `0`. The proof does not use it. -/
@[gap212 "lem_moebius_totient_asymptotic"]
theorem tendsto_log_mul_prod_one_sub_inv_sub_one {V : ℕ} (hV : Squarefree V) (_hV2 : 2 ∣ V) :
    Tendsto (fun y : ℝ => Real.log y *
        ∏ p ∈ Finset.Ioc 0 ⌊y⌋₊ with (p.Prime ∧ ¬ p ∣ V), (1 - 1 / ((p : ℝ) - 1)))
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant) * ((V : ℝ) / (V.totient : ℝ)) *
        ∏' p : ℕ, if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)) := by
  have hV0 : V ≠ 0 := hV.ne_zero
  have hVR : (V : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hV0
  have hφR : (V.totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.totient_pos.2 (Nat.pos_of_ne_zero hV0)).ne'
  have key := (tendsto_log_mul_prod_one_sub_inv.mul (tendsto_prod_corr V)).const_mul
    ((V : ℝ) / (V.totient : ℝ))
  rw [show ((V : ℝ) / (V.totient : ℝ)) * (Real.exp (-Real.eulerMascheroniConstant) *
      ∏' p : ℕ, if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)
      = Real.exp (-Real.eulerMascheroniConstant) * ((V : ℝ) / (V.totient : ℝ)) *
        ∏' p : ℕ, if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 from by ring] at key
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop (V : ℝ)] with y hy
  have hVle : V ≤ ⌊y⌋₊ := Nat.le_floor hy
  have hfilt : ((Finset.Ioc 0 ⌊y⌋₊).filter (fun p => p.Prime)).filter (fun p => p ∣ V)
      = V.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primeFactors]
    refine ⟨fun h => ⟨h.1.2, h.2, hV0⟩, fun h => ⟨⟨⟨h.1.pos, ?_⟩, h.1⟩, h.2.1⟩⟩
    exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hV0) h.2.1) hVle
  have hA : ∏ p ∈ Finset.Ioc 0 ⌊y⌋₊ with p.Prime, (1 - 1 / (p : ℝ))
      = (V.totient : ℝ) / (V : ℝ) *
        ∏ p ∈ Finset.Ioc 0 ⌊y⌋₊ with (p.Prime ∧ ¬ p ∣ V), (1 - 1 / (p : ℝ)) := by
    have h := Finset.prod_filter_mul_prod_filter_not
      ((Finset.Ioc 0 ⌊y⌋₊).filter (fun p => p.Prime)) (fun p => p ∣ V)
      (fun p => 1 - 1 / (p : ℝ))
    rw [hfilt, Finset.filter_filter, ← totient_div_eq_prod_one_sub_inv hV0] at h
    exact h.symm
  have hsplit : ∏ p ∈ Finset.Ioc 0 ⌊y⌋₊ with (p.Prime ∧ ¬ p ∣ V), (1 - 1 / ((p : ℝ) - 1))
      = (∏ p ∈ Finset.Ioc 0 ⌊y⌋₊ with (p.Prime ∧ ¬ p ∣ V), (1 - 1 / (p : ℝ)))
        * ∏ p ∈ Finset.Ioc 0 ⌊y⌋₊ with (p.Prime ∧ ¬ p ∣ V), (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p hp =>
      one_sub_inv_sub_one_prime (Finset.mem_filter.1 hp).2.1
  rw [hsplit, hA]
  field_simp

/-- The limit constant is positive for even squarefree `V`. -/
theorem moebius_totient_limit_pos {V : ℕ} (hV : Squarefree V) (hV2 : 2 ∣ V) :
    0 < Real.exp (-Real.eulerMascheroniConstant) * ((V : ℝ) / (V.totient : ℝ)) *
      ∏' p : ℕ, if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 := by
  have hV0 : V ≠ 0 := hV.ne_zero
  have hVp : (0 : ℝ) < (V : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hV0
  have hφp : (0 : ℝ) < (V.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero hV0)
  exact mul_pos (mul_pos (Real.exp_pos _) (div_pos hVp hφp)) (tprod_corr_pos hV2)

end Gap212.Sieve
