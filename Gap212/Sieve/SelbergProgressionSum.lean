/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.AveragingFacts

/-!
# The denominator divisor sum: the elementary reassembly steps

The sum `∑_{x≤n≤2x, n≡b (W)} ∏_{i≤k} λ_{F_i}(n+h_i) λ_{G_i}(n+h_i)` is evaluated in five steps:
expand the `2k` divisor weights, interchange the `n`-sum with the divisor sums, discard the tuples
whose least common multiples are not pairwise coprime and coprime to `W(x)`, collapse the surviving
congruences to a single class modulo `q = W(x)∏ᵢ[dᵢ,d'ᵢ]` by the Chinese remainder theorem, and
count that class in the dyadic block. This file proves these five elementary steps. The
asymptotic analysis of the resulting main term, and the assembled statement
`Gap212.Sieve.selberg_progression_sum`, are in `Gap212.Sieve.SelbergAssembly`.

## Main results

* `Gap212.Sieve.prod_lambdaF_eq_sum`: a product of divisor weights is a sum over divisor tuples.
* `Gap212.Sieve.sum_prod_lambdaF_pair`: the interchange — the weighted sum over the block equals a
  sum over pairs of divisor tuples of the Möbius coefficient times the number of `n` the tuple
  divides.
* `Gap212.Sieve.coprime_of_forall_dvd`: a tuple dividing a pre-sieved shift family has pairwise
  coprime moduli, all coprime to `W(x)` — so the coprimality restriction on the main
  term discards only tuples of count zero.
* `Gap212.Sieve.card_pair_le`: what one divisor pair contributes to the block is at most
  `x/q + 1` at the modulus `q = W(x)∏ᵢ[dᵢ,d'ᵢ]` it generates.
* `Gap212.Sieve.exists_crt_class`: the congruences a tuple imposes collapse to a single class
  modulo `W(x)∏ᵢmᵢ`.
* `Gap212.Sieve.card_filter_modEq_ge`: the sharp lower bound on the number of block members in one
  class, the companion of `Gap212.Sieve.card_filter_modEq_le`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.Defs Gap212.GPY

/-! ## The two logarithmic scales agree

`Gap212.GPY.lambdaF` reads its profile at `Gap212.Notation.logx`, while the support estimates of
`Gap212.Sieve.DivisorSumFacts` and `Gap212.Sieve.AveragingFacts` are stated at
`Gap212.logScale`. The two definitions are the same quotient. -/

/-- `log_x d` and the logarithmic size of `d` are the same number. -/
theorem logx_eq_logScale (x d : ℝ) : Gap212.Notation.logx x d = Gap212.logScale x d := rfl

/-! ## Expanding the divisor weights -/

/-- **The divisor expansion.** A product of divisor weights over a finite index type is a single
sum over tuples of divisors, one coordinate at a time.

This is `Finset.prod_univ_sum` at the summands of `Gap212.GPY.lambdaF`; the content is that the
index type is finite, so the distribution terminates. -/
theorem prod_lambdaF_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → ℝ → ℝ) (x : ℝ) (N : ι → ℕ) :
    ∏ i, lambdaF (F i) x (N i)
      = ∑ D ∈ Fintype.piFinset (fun i ↦ (N i).divisors),
          ∏ i, (ArithmeticFunction.moebius (D i) : ℝ) * F i (Gap212.Notation.logx x (D i)) := by
  simpa [lambdaF] using Finset.prod_univ_sum (fun i ↦ (N i).divisors)
    (fun i d ↦ (ArithmeticFunction.moebius d : ℝ) * F i (Gap212.Notation.logx x d))

/-- **The divisor tuples of a bounded family live in a fixed box.** For positive `Nᵢ` bounded by
`B`, the tuples of divisors are exactly the tuples in `[1,B]^ι` dividing coordinatewise.

Replacing the `n`-dependent summation range by a fixed one is what makes the interchange with the
`n`-sum available. -/
theorem piFinset_divisors_eq_filter {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ℕ}
    {N : ι → ℕ} (hN : ∀ i, 0 < N i) (hB : ∀ i, N i ≤ B) :
    Fintype.piFinset (fun i ↦ (N i).divisors)
      = {d ∈ Fintype.piFinset (fun _ : ι ↦ Finset.Icc 1 B) | ∀ i, d i ∣ N i} := by
  ext d
  simp only [Fintype.mem_piFinset, Nat.mem_divisors, mem_filter, mem_Icc]
  exact ⟨fun h ↦ ⟨fun i ↦ ⟨Nat.one_le_iff_ne_zero.2 fun h0 ↦ (hN i).ne'
        (Nat.eq_zero_of_zero_dvd (h0 ▸ (h i).1)),
      le_trans (Nat.le_of_dvd (hN i) (h i).1) (hB i)⟩, fun i ↦ (h i).1⟩,
    fun h i ↦ ⟨h.2 i, (hN i).ne'⟩⟩

/-- **The divisor expansion over a fixed box**: the same sum, over a summation range that does not
depend on the integers being divided. -/
theorem prod_lambdaF_eq_box {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ℕ}
    (F : ι → ℝ → ℝ) (x : ℝ) {N : ι → ℕ} (hN : ∀ i, 0 < N i) (hB : ∀ i, N i ≤ B) :
    ∏ i, lambdaF (F i) x (N i)
      = ∑ d ∈ Fintype.piFinset (fun _ : ι ↦ Finset.Icc 1 B),
          if ∀ i, d i ∣ N i then
            ∏ i, (ArithmeticFunction.moebius (d i) : ℝ) * F i (Gap212.Notation.logx x (d i))
          else 0 := by
  rw [prod_lambdaF_eq_sum, piFinset_divisors_eq_filter hN hB, sum_filter]

/-- **The interchange.** For any finite set `S` of integers whose shifts are positive and bounded
by `B`, the sum over `S` of the `2k`-fold divisor weight equals a sum over *pairs* of divisor
tuples in `[1,B]^k` of the Möbius coefficient times the number of members of `S` that the pair
divides.

This is the first two of the five steps: the `2k` weights are expanded by
`Gap212.GPY.lambdaF`, and the `n`-sum is moved inside. The arithmetic of the remaining count — the
Chinese remainder step — is the next section. -/
theorem sum_prod_lambdaF_pair {k : ℕ} {x : ℝ} {B : ℕ} (S : Finset ℕ) (h : Fin k → ℕ)
    (F G : Fin k → ℝ → ℝ) (hN : ∀ n ∈ S, ∀ i, 0 < n + h i) (hB : ∀ n ∈ S, ∀ i, n + h i ≤ B) :
    ∑ n ∈ S, ∏ i, lambdaF (F i) x (n + h i) * lambdaF (G i) x (n + h i)
      = ∑ d ∈ Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 B),
          ∑ d' ∈ Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 B),
            (∏ i, (ArithmeticFunction.moebius (d i) : ℝ) * F i (Gap212.Notation.logx x (d i))) *
              (∏ i, (ArithmeticFunction.moebius (d' i) : ℝ) * G i (Gap212.Notation.logx x (d' i))) *
              (#{n ∈ S | (∀ i, d i ∣ n + h i) ∧ (∀ i, d' i ∣ n + h i)} : ℝ) := by
  set box := Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 B)
  set A : (Fin k → ℕ) → ℝ := fun d ↦
    ∏ i, (ArithmeticFunction.moebius (d i) : ℝ) * F i (Gap212.Notation.logx x (d i)) with hA
  set A' : (Fin k → ℕ) → ℝ := fun d ↦
    ∏ i, (ArithmeticFunction.moebius (d i) : ℝ) * G i (Gap212.Notation.logx x (d i)) with hA'
  have step : ∀ n ∈ S, ∏ i, lambdaF (F i) x (n + h i) * lambdaF (G i) x (n + h i)
      = ∑ d ∈ box, ∑ d' ∈ box,
          if (∀ i, d i ∣ n + h i) ∧ (∀ i, d' i ∣ n + h i) then A d * A' d' else 0 := by
    intro n hn
    rw [prod_mul_distrib, prod_lambdaF_eq_box F x (hN n hn) (hB n hn),
      prod_lambdaF_eq_box G x (hN n hn) (hB n hn), sum_mul_sum]
    exact sum_congr rfl fun d _ ↦ sum_congr rfl fun d' _ ↦ by split_ifs <;> simp_all
  rw [sum_congr rfl step, sum_comm]
  refine sum_congr rfl fun d _ ↦ sum_comm.trans (sum_congr rfl fun d' _ ↦ ?_)
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

/-- **The interchange at the block.** The left-hand side of the denominator divisor sum, expanded
over pairs of divisor tuples in `[1, ⌊2x⌋ + H]^k`.

`H` is any bound for the tuple's entries; `0 < x` is what makes every `n` in the block positive, so
that the shifts have divisors at all. -/
theorem sum_prod_lambdaF_dyadic {k : ℕ} {x : ℝ} (hx : 0 < x) (b H : ℕ) (h : Fin k → ℕ)
    (hH : ∀ i, h i ≤ H) (F G : Fin k → ℝ → ℝ) :
    ∑ n ∈ dyadic x with n % W x = b % W x,
        ∏ i, lambdaF (F i) x (n + h i) * lambdaF (G i) x (n + h i)
      = ∑ d ∈ Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 (⌊2 * x⌋₊ + H)),
          ∑ d' ∈ Fintype.piFinset (fun _ : Fin k ↦ Finset.Icc 1 (⌊2 * x⌋₊ + H)),
            (∏ i, (ArithmeticFunction.moebius (d i) : ℝ) * F i (Gap212.Notation.logx x (d i))) *
              (∏ i, (ArithmeticFunction.moebius (d' i) : ℝ) * G i (Gap212.Notation.logx x (d' i))) *
              (#(Finset.filter (fun n ↦ (∀ i, d i ∣ n + h i) ∧ (∀ i, d' i ∣ n + h i))
                  {n ∈ dyadic x | n % W x = b % W x}) : ℝ) := by
  refine sum_prod_lambdaF_pair _ h F G (fun n hn i ↦ ?_) (fun n hn i ↦ ?_) <;>
  · have := mem_Icc.mp (mem_filter.mp hn).1
    have := hH i
    have := Nat.one_le_ceil_iff.mpr hx
    omega

/-- **The two divisibility conditions are one.** A pair of divisors both divide `N` exactly when
their least common multiple does; this is what turns the pair `(dᵢ, d'ᵢ)` of the expansion into the
single modulus `[dᵢ,d'ᵢ]` the Chinese remainder step is applied to. -/
theorem forall_dvd_iff_forall_lcm_dvd {ι : Type*} {d d' N : ι → ℕ} :
    ((∀ i, d i ∣ N i) ∧ (∀ i, d' i ∣ N i)) ↔ ∀ i, (d i).lcm (d' i) ∣ N i :=
  ⟨fun h i ↦ Nat.lcm_dvd (h.1 i) (h.2 i), fun h ↦
    ⟨fun i ↦ (Nat.dvd_lcm_left _ _).trans (h i), fun i ↦ (Nat.dvd_lcm_right _ _).trans (h i)⟩⟩

/-! ## The moduli a contributing tuple has -/

/-- **A tuple dividing the shifts has pairwise coprime moduli, all coprime to `W(x)`.** If `n` is
congruent to a pre-sieved residue `b` modulo `W(x)` and `mᵢ ∣ n + hᵢ` for every `i`, then the `mᵢ`
are pairwise coprime and each is coprime to `W(x)`.

This is "a tuple contributes only if the `[dᵢ,d'ᵢ]` are pairwise coprime and
coprime to `W(x)`", stated positively: the shifts `n + hᵢ` are pairwise coprime by
`Gap212.Sieve.coprime_shifts_of_modEq` and coprime to `W(x)` by
`Gap212.Sieve.coprime_W_of_modEq`, and coprimality is inherited by divisors. So the coprimality
restriction on the main term is not a restriction at all — it discards only tuples whose
count is zero.

The two conclusions are exactly the hypotheses of `Gap212.Sieve.exists_crt_class`. -/
theorem coprime_of_forall_dvd {k : ℕ} {h : Fin k → ℕ} (hmono : StrictMono h) {x : ℝ}
    (hD : ∀ p : ℕ, p.Prime → p ≤ (Finset.image h Finset.univ).diameter → p ∣ W x)
    {b n : ℕ} (hb : IsPreSieved b (W x) h) (hn : n ≡ b [MOD W x])
    {m : Fin k → ℕ} (hdvd : ∀ l, m l ∣ n + h l) :
    (∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) ∧ ∀ i, Nat.Coprime (W x) (m i) :=
  ⟨fun i j hij ↦ (((coprime_shifts_of_modEq hmono hD hb hn hij).coprime_dvd_left
      (hdvd i)).coprime_dvd_right (hdvd j)),
    fun i ↦ (((coprime_W_of_modEq hb hn i).coprime_dvd_left (hdvd i))).symm⟩

/-! ## The Chinese remainder step -/

/-- A congruence modulo each of a pairwise coprime family of moduli is a congruence modulo their
product. Unlike `Gap212.Sieve.modEq_prod` the moduli are indexed rather than collected into a
`Finset`, so repeated values — several `mᵢ = 1`, say — are not silently merged. -/
theorem modEq_prod_of_pairwise {ι : Type*} {m : ι → ℕ} {u v : ℕ}
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) (hmod : ∀ i, u ≡ v [MOD m i])
    (s : Finset ι) : u ≡ v [MOD ∏ i ∈ s, m i] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Nat.modEq_one]
  | insert p s hp ih =>
      rw [Finset.prod_insert hp]
      exact (Nat.modEq_and_modEq_iff_modEq_mul
        (Nat.Coprime.prod_right fun j hj ↦ hcop p j fun hEq ↦ hp (hEq ▸ hj))).mp ⟨hmod p, ih⟩

/-- **The shift congruences are one congruence.** For positive pairwise coprime `mᵢ` there is a
residue `a` with `(∀ i, mᵢ ∣ n + hᵢ) ↔ n ≡ a (mod ∏ᵢmᵢ)`.

Existence is the Chinese remainder theorem at the residues `-hᵢ`
(`Gap212.Sieve.exists_natCast_eq`); uniqueness is `Gap212.Sieve.modEq_prod_of_pairwise`. -/
theorem exists_shift_class {ι : Type*} [Fintype ι] {m : ι → ℕ} (h : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) :
    ∃ a : ℕ, ∀ n : ℕ, ((∀ i, m i ∣ n + h i) ↔ n ≡ a [MOD ∏ i, m i]) := by
  haveI : ∀ i, NeZero (m i) := fun i ↦ ⟨(hm i).ne'⟩
  obtain ⟨a, ha⟩ := exists_natCast_eq m hm hcop fun i ↦ -((h i : ℕ) : ZMod (m i))
  have ham : ∀ i, m i ∣ a + h i := fun i ↦
    (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast [ha i]; ring)
  refine ⟨a, fun n ↦ ⟨fun hn ↦ modEq_prod_of_pairwise hcop (fun i ↦ ?_) _, fun hn i ↦ ?_⟩⟩
  · exact Nat.ModEq.add_right_cancel' (h i)
      ((Nat.modEq_zero_iff_dvd.mpr (hn i)).trans (Nat.modEq_zero_iff_dvd.mpr (ham i)).symm)
  · exact Nat.modEq_zero_iff_dvd.mp (((hn.of_dvd (Finset.dvd_prod_of_mem m (mem_univ i))).add_right
      (h i)).trans (Nat.modEq_zero_iff_dvd.mpr (ham i)))

/-- **The Chinese remainder step.** For positive pairwise coprime `mᵢ`,
all coprime to `W`, the conditions `n ≡ b (W)` and `mᵢ ∣ n + hᵢ` for every `i` cut out exactly one
class modulo `q = W∏ᵢmᵢ`.

Applied at `mᵢ = [dᵢ,d'ᵢ]` this is the collapse of the fourth step, the hypotheses being
exactly what `Gap212.Sieve.coprime_of_forall_dvd` provides for a contributing tuple. The residue it
produces is the tuple residue of `Gap212.GPY.IsTupleResidue`, read at the shift `h` rather than at
the removed coordinate. -/
theorem exists_crt_class {ι : Type*} [Fintype ι] {W b : ℕ} {m : ι → ℕ}
    (h : ι → ℕ) (hm : ∀ i, 0 < m i) (hWm : ∀ i, Nat.Coprime W (m i))
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) :
    ∃ a : ℕ, ∀ n : ℕ,
      ((n ≡ b [MOD W] ∧ ∀ i, m i ∣ n + h i) ↔ n ≡ a [MOD W * ∏ i, m i]) := by
  obtain ⟨a', ha'⟩ := exists_shift_class h hm hcop
  have hcopW : Nat.Coprime W (∏ i, m i) := Nat.Coprime.prod_right fun i _ ↦ hWm i
  obtain ⟨a, haW, ham⟩ := Nat.chineseRemainder hcopW b a'
  refine ⟨a, fun n ↦ ?_⟩
  rw [ha' n, ← Nat.modEq_and_modEq_iff_modEq_mul hcopW]
  exact and_congr ⟨(·.trans haW.symm), (·.trans haW)⟩ ⟨(·.trans ham.symm), (·.trans ham)⟩

/-! ## Counting one class in a block

`Gap212.Sieve.card_filter_modEq_le` bounds the count above by `(B-A)/q + 1`. The count needed here
is two-sided — "the number of `n ∈ [x,2x]` in one class modulo `q` is `x/q + O(1)`" — so the lower
bound is needed too. -/

/-- **The sharp lower bound on a class in a block**: at least `(B+1-A)/q` members of `Icc A B` lie
in any fixed class modulo `q`.

The least member of the class at or above `A` is `A + δ` with `δ = (a + q - A % q) % q < q`, and
adding multiples of `q` to it stays in the block for as long as `q` times the multiple fits into
`B + 1 - A`. That gives an injection from `Finset.range ((B+1-A)/q)`. -/
theorem card_filter_modEq_ge {A B q a : ℕ} (hq : 0 < q) :
    (B + 1 - A) / q ≤ #{n ∈ Finset.Icc A B | n ≡ a [MOD q]} := by
  set δ := (a + q - A % q) % q with hδ
  have hδlt : δ < q := Nat.mod_lt _ hq
  -- The base point `A + δ` lies in the class, and is the least such at or above `A`.
  have hbase : (A + δ) % q = a % q := by
    have := Nat.div_add_mod A q
    have := Nat.mod_lt A hq
    rw [hδ, Nat.add_mod_mod, show A + (a + q - A % q) = a + q * (A / q + 1) by
      rw [Nat.mul_succ]; omega, Nat.add_mul_mod_self_left]
  rw [← Finset.card_range ((B + 1 - A) / q)]
  refine Finset.card_le_card_of_injOn (fun j ↦ (A + δ) + q * j) (fun j hj ↦ ?_)
    fun j _ j' _ heq ↦ Nat.eq_of_mul_eq_mul_left hq (by simpa using heq)
  have : q * j + q ≤ q * ((B + 1 - A) / q) := by
    simpa [Nat.mul_succ] using Nat.mul_le_mul_left q (Finset.mem_range.mp hj)
  have := Nat.mul_div_le (B + 1 - A) q
  dsimp only
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [Nat.ModEq, Nat.add_mul_mod_self_left, hbase]

/-! ## What one divisor pair contributes

Steps three to five, assembled: a divisor pair either divides nothing in
the block, or the `n` it divides form a single class modulo the modulus it generates, of which the
block holds `x/q + O(1)` members. -/

/-- **The count a divisor pair contributes to the expansion** is at most `x/q + 1`, with
`q = W(x)∏ᵢ[dᵢ,d'ᵢ]` the modulus it generates — whether or not the generated lcms are pairwise
coprime.

Two cases, and both are sharp in their own regime. If the `[dᵢ,d'ᵢ]` are pairwise coprime and
coprime to `W(x)`, the conditions cut out one class modulo `q` by
`Gap212.Sieve.exists_crt_class`, and `Gap212.Sieve.card_dyadic_filter_modEq_le` counts it.
Otherwise no `n` of the pre-sieved class is divided at all, by
`Gap212.Sieve.coprime_of_forall_dvd`, and the count is zero — which is why the main term may be
restricted to the coprime tuples without changing the sum.

The companion lower bound at a coprime tuple is `Gap212.Sieve.card_filter_modEq_ge`. -/
theorem card_pair_le {k : ℕ} {x : ℝ} (hx : 0 ≤ x) {b : ℕ} {h : Fin k → ℕ} (hmono : StrictMono h)
    (hD : ∀ p : ℕ, p.Prime → p ≤ (Finset.image h Finset.univ).diameter → p ∣ W x)
    (hb : IsPreSieved b (W x) h) {d d' : Fin k → ℕ} (hd : ∀ i, 0 < d i) (hd' : ∀ i, 0 < d' i) :
    (#(Finset.filter (fun n ↦ (∀ i, d i ∣ n + h i) ∧ (∀ i, d' i ∣ n + h i))
        {n ∈ dyadic x | n % W x = b % W x}) : ℝ)
      ≤ x / ((W x * ∏ i, (d i).lcm (d' i) : ℕ) : ℝ) + 1 := by
  set m : Fin k → ℕ := fun i ↦ (d i).lcm (d' i) with hm
  have hmpos : ∀ i, 0 < m i := fun i ↦ Nat.lcm_pos (hd i) (hd' i)
  have hqpos : 0 < W x * ∏ i, m i :=
    Nat.mul_pos (primorial_pos _) (Finset.prod_pos fun i _ ↦ hmpos i)
  -- Every member of the filtered set satisfies the pre-sieved congruence and divides the shifts.
  have hchar : ∀ n, (n ∈ Finset.filter (fun n ↦ (∀ i, d i ∣ n + h i) ∧ (∀ i, d' i ∣ n + h i))
      {n ∈ dyadic x | n % W x = b % W x}) ↔
      (n ∈ dyadic x ∧ n ≡ b [MOD W x] ∧ ∀ i, m i ∣ n + h i) := by
    simp [hm, ← forall_dvd_iff_forall_lcm_dvd, and_assoc, Nat.ModEq]
  by_cases hcop : (∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) ∧ ∀ i, Nat.Coprime (W x) (m i)
  · obtain ⟨a, ha⟩ := exists_crt_class (W := W x) (b := b) h hmpos hcop.2 hcop.1
    have hset : Finset.filter (fun n ↦ (∀ i, d i ∣ n + h i) ∧ (∀ i, d' i ∣ n + h i))
        {n ∈ dyadic x | n % W x = b % W x} = {n ∈ dyadic x | n ≡ a [MOD W x * ∏ i, m i]} := by
      ext n
      rw [hchar n, Finset.mem_filter, ← ha n]
    rw [hset]
    exact card_dyadic_filter_modEq_le hx hqpos
  · -- No member at all: a member would supply the coprimality the case assumption denies.
    have hempty : Finset.filter (fun n ↦ (∀ i, d i ∣ n + h i) ∧ (∀ i, d' i ∣ n + h i))
        {n ∈ dyadic x | n % W x = b % W x} = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr fun n hn ↦ ?_
      obtain ⟨-, hnW, hndvd⟩ := (hchar n).mp hn
      exact hcop (coprime_of_forall_dvd hmono hD hb hnW hndvd)
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

end Gap212.Sieve
