/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Defs
public import Gap212.Sieve.GPYDefs
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Primorial
public meta import Gap212.Attr

/-!
# A pre-sieved residue exists

The sieve runs over one residue class modulo the pre-sieving modulus `W(x)`, chosen so that every
shift of the class is coprime to `W(x)`. That such a class exists is what admissibility of the
tuple buys, and the Chinese remainder theorem assembles the local choices into a global one.

## The two steps, and where each hypothesis is spent

**Locally.** Admissibility says the reductions of the tuple modulo `p` omit some residue `a`.
Translating by `-a` turns that into what the sieve wants: a residue `r` with `p ∤ (r + hᵢ)` for
every `i`. The translation is where `ZMod p` earns its keep — natural subtraction would make
`r = p(a+1) - a` unpleasant, whereas in `ZMod p` it is just `-a`.

**Globally.** `W(x)` is squarefree, so its prime factors are pairwise coprime and
`Nat.chineseRemainderOfFinset` glues the local residues. Coprimality to `W(x)` is then checked one
prime at a time, which is exactly `Nat.coprime_of_dvd`.

## Main results

* `Gap212.Sieve.exists_presieved_of_local`: the CRT assembly, from local avoidance.
* `Gap212.Sieve.exists_local_residue`: admissibility gives local avoidance.
* `Gap212.Sieve.exists_isPreSieved`: a pre-sieved residue exists for any admissible tuple.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset Gap212.Defs

/-! ## The global step -/

/-- **The Chinese remainder assembly.** If for every prime factor `p` of a squarefree `W` there is
a residue avoiding every shift modulo `p`, then some single `b` is coprime to `W` after every
shift.

Squarefreeness is used twice: it makes the prime factors pairwise coprime, which is what
`Nat.chineseRemainderOfFinset` needs, and it makes `W` nonzero, which is what puts a prime divisor
of `W` into `W.primeFactors`. -/
theorem exists_presieved_of_local {k : ℕ} (W : ℕ) (hW : Squarefree W) (h : Fin k → ℕ)
    (hloc : ∀ p : ℕ, p.Prime → p ∣ W → ∃ r : ℕ, ∀ i : Fin k, ¬ (p ∣ (r + h i))) :
    ∃ b : ℕ, ∀ i : Fin k, Nat.Coprime (b + h i) W := by
  classical
  have hW0 : W ≠ 0 := hW.ne_zero
  -- Choose a local residue at each prime factor.
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℕ, ∀ p ∈ W.primeFactors, ∀ i : Fin k, ¬ (p ∣ (r p + h i)) := by
    refine ⟨fun p ↦ if hp : p ∈ W.primeFactors then
      Classical.choose (hloc p (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)) else 0, ?_⟩
    intro p hp i
    simp only [hp, dif_pos]
    exact Classical.choose_spec
      (hloc p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)) i
  -- Glue them.
  obtain ⟨b, hb⟩ : ∃ b : ℕ, ∀ p ∈ W.primeFactors, b ≡ r p [MOD p] := by
    have hne : ∀ p ∈ W.primeFactors, id p ≠ 0 := fun p hp ↦ (Nat.pos_of_mem_primeFactors hp).ne'
    have hcop : (↑W.primeFactors : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
      intro p hp q hq hpq
      simp only [Function.onFun, id]
      exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq
    exact ⟨(Nat.chineseRemainderOfFinset r id W.primeFactors hne hcop).1,
      (Nat.chineseRemainderOfFinset r id W.primeFactors hne hcop).2⟩
  -- Coprimality, one prime at a time.
  refine ⟨b, fun i ↦ Nat.coprime_of_dvd fun q hq hqbhi hqW ↦ ?_⟩
  have hqmem : q ∈ W.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqW, hW0⟩
  refine hr q hqmem i ?_
  have hshift : (b + h i) ≡ (r q + h i) [MOD q] := (hb q hqmem).add_right (h i)
  have hzero : (b + h i) ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr hqbhi
  exact Nat.modEq_zero_iff_dvd.mp (hshift.symm.trans hzero)

/-! ## The local step -/

/-- **Admissibility gives a residue avoiding every shift.** If the reductions of the tuple modulo
`p` omit `a`, then `r ≡ -a` has `p ∤ (r + hᵢ)` for every `i`.

Working in `ZMod p` is what keeps this short: `p ∣ n` is `(n : ZMod p) = 0`, congruence is equality
of casts, and the translation by `-a` is subtraction in a ring rather than in `ℕ`. -/
theorem exists_local_residue {k : ℕ} {p : ℕ} (hp : p.Prime) {h : Fin k → ℕ} {a : ℕ}
    (ha : ∀ i : Fin k, ¬ (h i ≡ a [MOD p])) :
    ∃ r : ℕ, ∀ i : Fin k, ¬ (p ∣ (r + h i)) := by
  have hple : a ≤ p * (a + 1) := le_trans (Nat.le_succ a) (Nat.le_mul_of_pos_left _ hp.pos)
  refine ⟨p * (a + 1) - a, fun i hdvd ↦ ?_⟩
  have hcast : ((p * (a + 1) - a + h i : ℕ) : ZMod p) = (h i : ZMod p) - (a : ZMod p) := by
    push_cast [Nat.cast_sub hple]
    simp
    ring
  have hzero : ((p * (a + 1) - a + h i : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  rw [hcast, sub_eq_zero] at hzero
  exact ha i ((ZMod.natCast_eq_natCast_iff _ _ _).mp hzero)

/-! ## The two together -/

/-- **A pre-sieved residue exists** for every admissible tuple and every `x`.

`W(x)` is a primorial, hence squarefree; admissibility supplies the local residues; and the Chinese
remainder theorem glues them. No largeness hypothesis on `x` is needed — `W(x)` is squarefree at
every `x`, and the argument never looks at its size. -/
@[gap212 "lem_b_exists"]
theorem exists_isPreSieved {k : ℕ} (h : Fin k → ℕ) (x : ℝ)
    (hadm : Gap212.Defs.Admissible (Finset.image h Finset.univ)) :
    ∃ b : ℕ, IsPreSieved b (Gap212.GPY.W x) h := by
  refine exists_presieved_of_local _ (squarefree_primorial _) h fun p hp _ ↦ ?_
  obtain ⟨a, hna⟩ := hadm p hp
  exact exists_local_residue hp fun i hi ↦
    hna (h i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) hi

end Gap212.Sieve
