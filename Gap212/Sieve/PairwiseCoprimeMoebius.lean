/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.SievingErrorTails

/-!
# Pairwise coprimality at `k` coordinates: the Möbius expansion and the prime-wise bound

`Gap212.Sieve.sum_coprime_pairs_eq_sum_moebius` expands a pairwise-coprimality restriction by
Möbius inversion at **two** coordinates. This file does it at `k`, and — the point — supplies the
bound on the resulting configuration sum, which at `k` coordinates is *not* the two-coordinate
bound with more indices.

## Why `k` coordinates is not bookkeeping

After expanding over the pair moduli `e_{ii'}` (one per ordered pair `i ≠ i'`), coordinate `i`
carries `L_i = [e_{ii'} : i' ≠ i]` — the least common multiple of the moduli of the edges at `i` —
and the surviving sum is over configurations `(e_{ii'})`, weighted by `∏_i 1/L_i`. The
two-coordinate argument pays for that with `∑_{e>z}e^{-2}`, one term per edge. **Edge-factorised
accounting fails from `k = 4` on.** At `k = 4` with all six `e_{ii'} = p`:

  `∏_i L_i = p^4`  while  `∏_{i<i'} e_{ii'} = p^6`,

so `∏_i L_i^{-1} ≤ ∏_{i<i'} e_{ii'}^{-1}` is **false**, and a union bound taken edge by edge
diverges: fixing one edge's modulus leaves the other `k(k-1)/2 - 1` free, and `∑_e e^{-2}` over
each of them contributes a constant, not a saving. `Gap212.Sieve.prod_incLcm_lt_prod_edges_four` is
that counterexample, as a checked inequality.

## The prime-wise bound

Group the configurations by prime. For a prime `P`, let `S_P` be the set of coordinates incident to
an edge whose modulus `P` divides. If `S_P ≠ ∅` then `|S_P| ≥ 2`, an edge having two *distinct*
endpoints, so `v_P(∏_i L_i) ≥ 2`. Equivalently, and this is the form proved here,

  `M^2 ∣ ∏_i L_i`,  `M = [e_{ii'} : i ≠ i']` the least common multiple of **all** the edge moduli

(`Gap212.Sieve.sq_configLcm_dvd_prod_incLcm`): each edge modulus divides the `L` of *both* its
endpoints, and the endpoints are distinct, so its square divides the product. That is the whole of
the prime-wise saving, and it needs no factorisation argument.

Grouping the configurations by `M` then costs a divisor count — at most `τ(M)^{k^2}`
configurations share a value of `M`, each edge modulus being a divisor of it — and that count is
beaten by `M^{1/2}` as soon as every prime factor of `M` exceeds `2^{2k^2}`
(`Gap212.Sieve.card_divisors_pow_le_of_primeFactors_gt`). So the configuration sum is at most
`∑_{M>z}M^{-3/2}`, a convergent tail, and
`Gap212.Sieve.exists_threshold_sum_one_div_prod_incLcm_lt` is that. Every prime in play exceeds `z`
because every edge modulus divides a least common multiple coprime to `W(x)`, the primorial of
`z = ⌊\log\log\log x⌋`, and `z → ∞`.

## Main results

* `Gap212.Sieve.prod_incLcm_lt_prod_edges_four`: the `k = 4` refutation of edge-factorised
  accounting, `16 < 64`.
* `Gap212.Sieve.sq_configLcm_dvd_prod_incLcm`: the prime-wise saving, as a divisibility.
* `Gap212.Sieve.exists_threshold_sum_one_div_prod_incLcm_lt`: the configuration sum is small once
  every prime in play exceeds a threshold depending only on `ε` and `k`.
* `Gap212.Sieve.sum_pairwise_coprime_eq_sum_moebius`: the exact `k`-coordinate identity.
* `Gap212.Sieve.exists_threshold_abs_prod_sub_sum_pairwise_coprime_le`: the two together — granting
  the one-coordinate cost `c/e`, the pairwise-coprimality restriction costs at most `c^kε`.
* `Gap212.Sieve.sum_pair_tuples_eq`: the pair of tuples reindexed as a tuple of pairs, which is
  what puts a sum `∑_d∑_{d'}` over a box into the shape the identity is stated at.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset
open scoped ArithmeticFunction.Moebius

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The incidence least common multiples -/

/-- **The moduli of the edges at a coordinate.** The pairs `(i',i'')` — read as edges of the
complete graph on the coordinates, with the diagonal carried along harmlessly — one of whose
endpoints is `i`. -/
def edgesAt (ι : Type*) [Fintype ι] [DecidableEq ι] (i : ι) : Finset (ι × ι) :=
  {q ∈ Finset.univ | q.1 = i ∨ q.2 = i}

/-- `q ∈ edgesAt ι i` if and only if one of the endpoints of `q` is `i`. -/
theorem mem_edgesAt {i : ι} {q : ι × ι} : q ∈ edgesAt ι i ↔ (q.1 = i ∨ q.2 = i) := by
  simp [edgesAt]

/-- **The modulus coordinate `i` carries**, `L_i = [e_q : i ∈ q]`: the least common multiple of the
moduli of the edges at `i`. This is what the `k`-coordinate Möbius expansion forces into the `i`-th
one-coordinate sum. -/
def incLcm (c : ι × ι → ℕ) (i : ι) : ℕ := (edgesAt ι i).lcm c

/-- **The least common multiple of every edge modulus**, `M`. The prime-wise bound is that its
square divides `∏_i L_i`. -/
def configLcm (c : ι × ι → ℕ) : ℕ := Finset.univ.lcm c

/-- The modulus of an edge at `i` divides `incLcm c i`. -/
theorem dvd_incLcm {c : ι × ι → ℕ} {i : ι} {q : ι × ι} (h : q.1 = i ∨ q.2 = i) :
    c q ∣ incLcm c i :=
  Finset.dvd_lcm (mem_edgesAt.mpr h)

/-- If `n` is divisible by the modulus of every edge at `i`, then `incLcm c i ∣ n`. -/
theorem incLcm_dvd_of_forall {c : ι × ι → ℕ} {i : ι} {n : ℕ}
    (h : ∀ q : ι × ι, (q.1 = i ∨ q.2 = i) → c q ∣ n) : incLcm c i ∣ n :=
  Finset.lcm_dvd fun q hq ↦ h q (mem_edgesAt.mp hq)

omit [DecidableEq ι] in
/-- Every edge modulus `c q` divides `configLcm c`. -/
theorem dvd_configLcm (c : ι × ι → ℕ) (q : ι × ι) : c q ∣ configLcm c :=
  Finset.dvd_lcm (Finset.mem_univ q)

omit [DecidableEq ι] in
/-- If `n` is divisible by every edge modulus, then `configLcm c ∣ n`. -/
theorem configLcm_dvd {c : ι × ι → ℕ} {n : ℕ} (h : ∀ q : ι × ι, c q ∣ n) : configLcm c ∣ n :=
  Finset.lcm_dvd fun q _ ↦ h q

/-- `L_i = 1` at the trivial configuration. -/
theorem incLcm_one (i : ι) : incLcm (fun _ : ι × ι ↦ 1) i = 1 :=
  Nat.dvd_one.mp (incLcm_dvd_of_forall fun _ _ ↦ dvd_rfl)

omit [DecidableEq ι] in
/-- **The configuration lcm is positive** when every edge modulus is. -/
theorem configLcm_pos {c : ι × ι → ℕ} (hc : ∀ q, 0 < c q) : 0 < configLcm c :=
  Nat.pos_of_ne_zero <| Finset.lcm_ne_zero_iff.mpr fun q _ ↦ (hc q).ne'

/-- **An incidence lcm is positive** when every edge modulus is. -/
theorem incLcm_pos {c : ι × ι → ℕ} (hc : ∀ q, 0 < c q) (i : ι) : 0 < incLcm c i :=
  Nat.pos_of_ne_zero <| Finset.lcm_ne_zero_iff.mpr fun q _ ↦ (hc q).ne'

/-- **A prime dividing a least common multiple over a finite set divides one of the terms.** -/
theorem exists_dvd_of_prime_dvd_finset_lcm {β : Type*} {s : Finset β} {c : β → ℕ} {p : ℕ}
    (hp : p.Prime) (h : p ∣ s.lcm c) : ∃ b ∈ s, p ∣ c b :=
  (Prime.dvd_finsetProd_iff hp.prime c).mp
    (h.trans (Finset.lcm_dvd fun _ hb ↦ Finset.dvd_prod_of_mem c hb))

/-! ## The prime-wise saving

The one inequality the `k`-coordinate expansion turns on. Its two-element core is
`Gap212.Sieve.sq_lcm_dvd_of_sq_dvd`: if `a^2` and `b^2` both divide `N` then so does `[a,b]^2`,
which is `2\max(v_P a, v_P b) = \max(2v_P a, 2v_P b)` read at every prime. -/

/-- **`[a,b]^2` divides anything `a^2` and `b^2` both divide.** -/
theorem sq_lcm_dvd_of_sq_dvd {a b N : ℕ} (ha : a ^ 2 ∣ N) (hb : b ^ 2 ∣ N) :
    Nat.lcm a b ^ 2 ∣ N :=
  Nat.pow_lcm_pow ▸ Nat.lcm_dvd ha hb

/-- **`M^2` divides anything every `c q ^ 2` divides.** The finite-set form of
`Gap212.Sieve.sq_lcm_dvd_of_sq_dvd`. -/
theorem sq_finset_lcm_dvd_of_sq_dvd {β : Type*} {s : Finset β} {c : β → ℕ} {N : ℕ}
    (h : ∀ b ∈ s, c b ^ 2 ∣ N) : s.lcm c ^ 2 ∣ N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
      rw [Finset.lcm_insert]
      exact sq_lcm_dvd_of_sq_dvd (h b (Finset.mem_insert_self _ _))
        (ih fun b' hb' ↦ h b' (Finset.mem_insert_of_mem hb'))

/-- **The prime-wise saving.** For a configuration of edge moduli that is trivial on the diagonal,

  `M^2 ∣ ∏_i L_i`,  `M = [c_q : q]`,  `L_i = [c_q : i ∈ q]`.

**This, and not an edge-by-edge bound, is what makes the `k`-coordinate expansion summable.** The
proof is the one line the module docstring gives: an off-diagonal `q` has two *distinct* endpoints
and `c q` divides the incidence lcm of each, so `(c q)^2` divides the product over all coordinates;
the diagonal entries are `1`. Read at a prime `P` this says `v_P(∏_i L_i) ≥ 2v_P(M)`, i.e. that the
set of coordinates an edge divisible by `P` touches has at least two elements.

Contrast `Gap212.Sieve.prod_incLcm_lt_prod_edges_four`: the analogous statement with `∏_q c q` in
place of `M^2` is **false** at four coordinates. -/
theorem sq_configLcm_dvd_prod_incLcm {c : ι × ι → ℕ} (hdiag : ∀ i : ι, c (i, i) = 1) :
    configLcm c ^ 2 ∣ ∏ i, incLcm c i := by
  refine sq_finset_lcm_dvd_of_sq_dvd fun ⟨i, j⟩ _ ↦ ?_
  by_cases hq : i = j
  · subst hq; simp [hdiag]
  -- The two endpoints are distinct, so both incidence lcms occur in the product.
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ {i, j}))
  rw [Finset.prod_pair hq, sq]
  exact mul_dvd_mul (dvd_incLcm (Or.inl rfl)) (dvd_incLcm (Or.inr rfl))

/-! ## Edge-factorised accounting is false at four coordinates

The two-coordinate bound, read edge by edge, asserts `∏_i L_i^{-1} ≤ ∏_q e_q^{-1}`
over the unordered pairs. The configuration with every edge modulus `2` refutes it at `k = 4`. -/

/-- **The `k = 4` counterexample to edge-factorised accounting.** With all six edge moduli equal to
`2`, every coordinate carries `L_i = 2`, so

  `∏_i L_i = 2^4 = 16`  while  `∏_{i<i'} e_{ii'} = 2^6 = 64`,

and `∏_{pairs} e ≤ ∏_i L_i` — the inequality an edge-by-edge union bound needs — fails. The gap is
`p^{k(k-1)/2 - k}`, so it opens at `k = 4` and widens; at `k = 3` the two sides agree (`2^3 = 8`
both ways) and at `k = 2` the edge bound is the identity. This is why
`Gap212.Sieve.sq_configLcm_dvd_prod_incLcm` — which only ever claims `M^2`, one factor per
*endpoint* — is the right accounting, and why extending the two-coordinate expansion to `k` is not
bookkeeping. -/
theorem prod_incLcm_lt_prod_edges_four :
    (∏ i : Fin 4, incLcm (fun q : Fin 4 × Fin 4 ↦ if q.1 = q.2 then 1 else 2) i) = 16 ∧
      (∏ q ∈ {q : Fin 4 × Fin 4 | q.1 < q.2},
          (if q.1 = q.2 then 1 else 2 : ℕ)) = 64 ∧
      (∏ i : Fin 4, incLcm (fun q : Fin 4 × Fin 4 ↦ if q.1 = q.2 then 1 else 2) i) <
        ∏ q ∈ {q : Fin 4 × Fin 4 | q.1 < q.2}, (if q.1 = q.2 then 1 else 2 : ℕ) := by
  simp only [incLcm, edgesAt]
  decide

/-! ## Counting the configurations with a given least common multiple -/

/-- **A divisor count is beaten by its modulus once every prime factor is large.**
`τ(M)^r ≤ M` as soon as `2^r ≤ p` for every prime `p ∣ M`: the local comparison is
`(v+1)^r ≤ (2^v)^r = (2^r)^v ≤ p^v`.

This is what pays for grouping the configurations by their least common multiple: the fibre has at
most `τ(M)^{k^2}` members, and `r = 2k^2` turns that into `M^{1/2}` against the `M^{-2}` the
prime-wise saving supplies. -/
theorem card_divisors_pow_le_of_primeFactors_gt {M r : ℕ} (hM : M ≠ 0)
    (h : ∀ p ∈ M.primeFactors, 2 ^ r ≤ p) : (M.divisors.card) ^ r ≤ M := by
  nth_rw 2 [← Nat.prod_factorization_pow_eq_self hM]
  rw [Nat.card_divisors hM, ← Finset.prod_pow, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_le_prod' fun p hp ↦ (Nat.pow_le_pow_left Nat.lt_two_pow_self r).trans ?_
  rw [pow_right_comm]
  exact Nat.pow_le_pow_left (h p hp) _

/-- **The reciprocal-square term against the `3/2` majorant.** If `t^2 ≤ M` then
`t/M^2 ≤ M^{-3/2}` — the step that turns the fibre count into a convergent tail. -/
theorem div_sq_le_rpow_neg_three_halves {t M : ℕ} (hM : 0 < M) (h : t ^ 2 ≤ M) :
    (t : ℝ) / (M : ℝ) ^ 2 ≤ 1 / (M : ℝ) ^ ((3 : ℝ) / 2) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc (t : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 2) ≤ (M : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) ^ ((3 : ℝ) / 2) := by
        gcongr
        rw [← Real.sqrt_eq_rpow]
        exact Real.le_sqrt_of_sq_le (by exact_mod_cast h)
    _ = (M : ℝ) ^ 2 := by rw [← Real.rpow_add (by exact_mod_cast hM)]; norm_num

/-- `∑_n n^{-3/2}` converges. -/
theorem summable_one_div_rpow_three_halves :
    Summable fun n : ℕ ↦ 1 / (n : ℝ) ^ ((3 : ℝ) / 2) :=
  Real.summable_one_div_nat_rpow.mpr (by norm_num)

/-! ## The configuration sum -/

/-- **The configurations of edge moduli**: one modulus from `E` per ordered pair of distinct
coordinates, and `1` on the diagonal. The Möbius expansion of the pairwise-coprimality restriction
at `k` coordinates runs over exactly these. -/
def pairConfigs (ι : Type*) [Fintype ι] [DecidableEq ι] (E : Finset ℕ) :
    Finset (ι × ι → ℕ) :=
  Fintype.piFinset fun q : ι × ι ↦ if q.1 = q.2 then {1} else E

/-- Membership in `pairConfigs ι E`: `c q = 1` on the diagonal and `c q ∈ E` off it. -/
theorem mem_pairConfigs {E : Finset ℕ} {c : ι × ι → ℕ} : c ∈ pairConfigs ι E ↔
    ∀ q : ι × ι, c q ∈ (if q.1 = q.2 then ({1} : Finset ℕ) else E) := by
  simp [pairConfigs]

/-- A configuration in `pairConfigs ι E` is `1` on the diagonal. -/
theorem pairConfigs_diag {E : Finset ℕ} {c : ι × ι → ℕ} (hc : c ∈ pairConfigs ι E) (i : ι) :
    c (i, i) = 1 := by
  simpa using mem_pairConfigs.mp hc (i, i)

/-- A configuration in `pairConfigs ι E` takes values in `E` off the diagonal. -/
theorem pairConfigs_mem {E : Finset ℕ} {c : ι × ι → ℕ} (hc : c ∈ pairConfigs ι E) {q : ι × ι}
    (hq : q.1 ≠ q.2) : c q ∈ E := by
  simpa [hq] using mem_pairConfigs.mp hc q

/-- A configuration in `pairConfigs ι E` is `1` at every diagonal pair. -/
private theorem pairConfigs_eq_one {E : Finset ℕ} {c : ι × ι → ℕ} (hc : c ∈ pairConfigs ι E)
    {q : ι × ι} (hq : q.1 = q.2) : c q = 1 := by
  simpa [hq] using mem_pairConfigs.mp hc q

/-- If every element of `E` is positive, then every modulus of a configuration in `pairConfigs ι E`
is positive. -/
theorem pairConfigs_pos {E : Finset ℕ} (hE : ∀ e ∈ E, 0 < e) {c : ι × ι → ℕ}
    (hc : c ∈ pairConfigs ι E) (q : ι × ι) : 0 < c q := by
  by_cases hq : q.1 = q.2
  · simp [pairConfigs_eq_one hc hq]
  · exact hE _ (pairConfigs_mem hc hq)

/-- **Every prime in play divides an edge modulus.** -/
theorem primeFactors_configLcm_gt {E : Finset ℕ} {z : ℕ}
    (hEprime : ∀ e ∈ E, ∀ p : ℕ, p.Prime → p ∣ e → z < p) {c : ι × ι → ℕ}
    (hc : c ∈ pairConfigs ι E) {p : ℕ} (hp : p.Prime) (hdvd : p ∣ configLcm c) : z < p := by
  obtain ⟨q, -, hq⟩ := exists_dvd_of_prime_dvd_finset_lcm hp hdvd
  by_cases hd : q.1 = q.2
  · exact (hp.not_dvd_one (pairConfigs_eq_one hc hd ▸ hq)).elim
  · exact hEprime _ (pairConfigs_mem hc hd) p hp hq

/-- **A non-trivial configuration has a large least common multiple.** -/
theorem lt_configLcm_of_ne_one {E : Finset ℕ} {z : ℕ} (hE : ∀ e ∈ E, 0 < e)
    (hEprime : ∀ e ∈ E, ∀ p : ℕ, p.Prime → p ∣ e → z < p) {c : ι × ι → ℕ}
    (hc : c ∈ pairConfigs ι E) (hne : c ≠ fun _ ↦ 1) : z < configLcm c := by
  obtain ⟨q, hq⟩ := Function.ne_iff.mp hne
  obtain ⟨p, hp, hpd⟩ :=
    Nat.exists_prime_and_dvd fun h ↦ hq (Nat.dvd_one.mp (h ▸ dvd_configLcm c q))
  exact (primeFactors_configLcm_gt hEprime hc hp hpd).trans_le
    (Nat.le_of_dvd (configLcm_pos (pairConfigs_pos hE hc)) hpd)

/-- **The fibre of the configuration lcm is bounded by a divisor count.** Each edge modulus of a
configuration with `[c_q : q] = M` divides `M`, so the fibre embeds in the tuples of divisors. -/
theorem card_fiber_configLcm_le {E : Finset ℕ} {M : ℕ} (hM : M ≠ 0) :
    #{c ∈ pairConfigs ι E | configLcm c = M} ≤ #M.divisors ^ Fintype.card (ι × ι) := by
  refine le_trans (Finset.card_le_card (t := Fintype.piFinset fun _ : ι × ι ↦ M.divisors)
    fun c hc ↦ Fintype.mem_piFinset.mpr fun q ↦
      Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hc).2 ▸ dvd_configLcm c q, hM⟩) ?_
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]

/-- The prime-wise saving `Gap212.Sieve.sq_configLcm_dvd_prod_incLcm`, cast to `ℝ`. -/
private theorem sq_configLcm_le_prod {E : Finset ℕ} (hE : ∀ e ∈ E, 0 < e) {c : ι × ι → ℕ}
    (hc : c ∈ pairConfigs ι E) : (configLcm c : ℝ) ^ 2 ≤ ∏ i, (incLcm c i : ℝ) := by
  exact_mod_cast Nat.le_of_dvd (Finset.prod_pos fun i _ ↦ incLcm_pos (pairConfigs_pos hE hc) i)
    (sq_configLcm_dvd_prod_incLcm (pairConfigs_diag hc))

/-- `Gap212.Sieve.card_fiber_configLcm_le` for the non-trivial configurations, cast to `ℝ`. -/
private theorem card_fiber_le {E : Finset ℕ} {M : ℕ} (hM : M ≠ 0) :
    (#{c ∈ {c ∈ pairConfigs ι E | c ≠ fun _ ↦ 1} | configLcm c = M} : ℝ) ≤
      (#M.divisors : ℝ) ^ Fintype.card (ι × ι) := by
  exact_mod_cast (Finset.card_le_card
    (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans (card_fiber_configLcm_le hM)

/-- Every prime factor of the configuration lcm exceeds any `B ≤ z`. -/
private theorem le_of_mem_primeFactors_configLcm {E : Finset ℕ} {z B : ℕ} (hB : B ≤ z)
    (hEprime : ∀ e ∈ E, ∀ p : ℕ, p.Prime → p ∣ e → z < p) {c : ι × ι → ℕ}
    (hc : c ∈ pairConfigs ι E) : ∀ p ∈ (configLcm c).primeFactors, B ≤ p := fun _ hp ↦
  hB.trans (primeFactors_configLcm_gt hEprime hc (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp)).le

/-- Every non-trivial configuration lcm exceeds any `z₁ ≤ z`. -/
private theorem lt_configLcm_image {E : Finset ℕ} {z z₁ : ℕ} (hE : ∀ e ∈ E, 0 < e)
    (hEprime : ∀ e ∈ E, ∀ p : ℕ, p.Prime → p ∣ e → z < p) (hz : z₁ ≤ z) :
    ∀ M ∈ {c ∈ pairConfigs ι E | c ≠ fun _ ↦ 1}.image configLcm, z₁ < M :=
  Finset.forall_mem_image.mpr fun _ hc ↦ hz.trans_lt
    (lt_configLcm_of_ne_one hE hEprime (Finset.mem_filter.mp hc).1 (Finset.mem_filter.mp hc).2)

omit [DecidableEq ι] in
/-- **Regrouping a configuration sum by the configuration lcm.** -/
private theorem sum_le_sum_image_configLcm {S : Finset (ι × ι → ℕ)} {f : (ι × ι → ℕ) → ℝ}
    {g h : ℕ → ℝ} (hf : ∀ c ∈ S, f c ≤ g (configLcm c))
    (hg : ∀ c ∈ S, #{c' ∈ S | configLcm c' = configLcm c} * g (configLcm c) ≤ h (configLcm c)) :
    ∑ c ∈ S, f c ≤ ∑ M ∈ S.image configLcm, h M := by
  calc ∑ c ∈ S, f c ≤ ∑ c ∈ S, g (configLcm c) := Finset.sum_le_sum hf
    _ = ∑ M ∈ S.image configLcm, #{c ∈ S | configLcm c = M} • g M := Finset.sum_comp g configLcm
    _ ≤ _ := Finset.sum_le_sum <| Finset.forall_mem_image.mpr fun c hc ↦ by
        rw [nsmul_eq_mul]; exact hg c hc

/-- **The configuration sum is small once every prime in play is large.** For every `ε > 0` there
is a threshold `z`, depending only on `ε` and the number of coordinates, such that

  `∑_{(e_q) ≠ 1} ∏_i 1/L_i < ε`

whenever every prime factor of every `e ∈ E` exceeds `z`.

**This is the `k`-coordinate replacement for `∑_{e>z}e^{-2}`, and it is not that sum with more
indices.** The proof groups the configurations by `M = [e_q : q]`: the prime-wise saving
`Gap212.Sieve.sq_configLcm_dvd_prod_incLcm` gives `∏_i L_i ≥ M^2`, the fibre over `M` has at most
`τ(M)^{k^2}` members (`Gap212.Sieve.card_fiber_configLcm_le`), and
`Gap212.Sieve.card_divisors_pow_le_of_primeFactors_gt` beats that count by `M^{1/2}` once every
prime factor of `M` exceeds `2^{2k^2}` — leaving the convergent tail `∑_{M>z}M^{-3/2}`.
Edge-by-edge accounting has no such regrouping available and diverges from `k = 4` on
(`Gap212.Sieve.prod_incLcm_lt_prod_edges_four`).

Uniform in `E` for the same reason as `Gap212.Sieve.exists_threshold_sum_lt`: the consumer's set of
moduli varies with `x`. -/
theorem exists_threshold_sum_one_div_prod_incLcm_lt (ι : Type*) [Fintype ι] [DecidableEq ι]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℕ, ∀ E : Finset ℕ, (∀ e ∈ E, 0 < e) →
      (∀ e ∈ E, ∀ p : ℕ, p.Prime → p ∣ e → z < p) →
        ∑ c ∈ {c ∈ pairConfigs ι E | c ≠ fun _ ↦ 1}, 1 / ∏ i, (incLcm c i : ℝ) < ε := by
  set n := Fintype.card (ι × ι)
  obtain ⟨z₁, hz₁⟩ := exists_threshold_sum_lt summable_one_div_rpow_three_halves hε
  refine ⟨max z₁ (2 ^ (2 * n)), fun E hE hEprime ↦ ?_⟩
  refine (sum_le_sum_image_configLcm (g := fun M ↦ 1 / (M : ℝ) ^ 2) (fun c hc ↦ ?_)
    fun c hc ↦ ?_).trans_lt (hz₁ _ (lt_configLcm_image hE hEprime (le_max_left _ _)))
  all_goals obtain ⟨hcE, -⟩ := Finset.mem_filter.mp hc
  all_goals have hM0 := configLcm_pos (pairConfigs_pos hE hcE)
  · exact one_div_le_one_div_of_le (by positivity) (sq_configLcm_le_prod hE hcE)
  -- the fibre count, and the exponent arithmetic that beats it
  calc _ ≤ ((#(configLcm c).divisors ^ n : ℕ) : ℝ) * (1 / (configLcm c : ℝ) ^ 2) := by
        gcongr; exact_mod_cast card_fiber_le hM0.ne'
    _ ≤ _ := by
      rw [mul_one_div]
      refine div_sq_le_rpow_neg_three_halves hM0 ?_
      rw [← pow_mul, mul_comm]
      exact card_divisors_pow_le_of_primeFactors_gt hM0.ne'
        (le_of_mem_primeFactors_configLcm (le_max_right _ _) hEprime hcE)

/-! ## The `k`-coordinate Möbius identity -/

variable {α : Type*}

/-- **The pairwise-coprimality restriction at `k` coordinates, expanded by Möbius — and the
coordinates still separate.** For a finite one-coordinate index set `X`, a modulus `m` and one
weight per coordinate,

  `∑_{a : ∀i, aᵢ∈X, pairwise coprime} ∏_i w_i(a_i)
      = ∑_{(e_q)} (∏_q μ(e_q))·∏_i A_i(L_i)`,
  `L_i = [e_q : i ∈ q]`,  `A_i(e) = ∑_{a∈X, e ∣ m a} w_i(a)`,

the configurations running over the moduli of the ordered pairs of coordinates, with `1` on the
diagonal, and the outer index set `E` being any `Finset` containing every divisor of every `m a`.

**An exact identity, at every `k`.** This is `Gap212.Sieve.sum_coprime_pairs_eq_sum_moebius` at `k`
coordinates instead of two: the coprimality indicator of each pair is Möbius-inverted, the
resulting divisibility conditions are collected coordinate by coordinate into the incidence lcm
`L_i`, and no absolute value is taken anywhere — so no cancellation is lost.

What is *not* the two-coordinate case with more indices is the **bound** on the surviving
configuration sum; see `Gap212.Sieve.exists_threshold_sum_one_div_prod_incLcm_lt` and the module
docstring. -/
theorem sum_pairwise_coprime_eq_sum_moebius (X : Finset α) (m : α → ℕ) (w : ι → α → ℝ)
    (E : Finset ℕ) (hm : ∀ a ∈ X, 0 < m a) (hE : ∀ a ∈ X, ∀ e, e ∣ m a → e ∈ E) :
    ∑ a ∈ Fintype.piFinset fun _ : ι ↦ X,
        (if ∀ i i' : ι, i ≠ i' → Nat.Coprime (m (a i)) (m (a i')) then ∏ i, w i (a i) else 0)
      = ∑ c ∈ pairConfigs ι E, (∏ q : ι × ι, ((μ (c q) : ℤ) : ℝ)) *
          ∏ i, restrictedSum X m (w i) (incLcm c i) := by
  set t : ι × ι → Finset ℕ := fun q ↦ if q.1 = q.2 then {1} else E with ht
  set g : (ι → α) → ι × ι → ℕ → ℝ := fun a q e ↦
    if e ∣ m (a q.1) ∧ e ∣ m (a q.2) then ((μ e : ℤ) : ℝ) else 0 with hg
  have hpc : pairConfigs ι E = Fintype.piFinset t := by rw [ht, pairConfigs]
  -- The coprimality indicator of one pair, Möbius-expanded.
  have hpair : ∀ a ∈ Fintype.piFinset fun _ : ι ↦ X, ∀ q : ι × ι,
      ∑ e ∈ t q, g a q e = if q.1 = q.2 then 1 else
        (if Nat.Coprime (m (a q.1)) (m (a q.2)) then 1 else 0) := by
    intro a ha q
    have haX : ∀ i, a i ∈ X := Fintype.mem_piFinset.mp ha
    by_cases hq : q.1 = q.2
    · simp [ht, hg, hq]
    have hset : {e ∈ E | e ∣ m (a q.1) ∧ e ∣ m (a q.2)}
        = (Nat.gcd (m (a q.1)) (m (a q.2))).divisors := by
      ext e
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      exact ⟨fun h ↦ ⟨h.2, (Nat.gcd_pos_of_pos_left _ (hm _ (haX q.1))).ne'⟩,
        fun h ↦ ⟨hE _ (haX q.1) e h.1.1, h.1⟩⟩
    simp only [ht, hg, if_neg hq]
    rw [← Finset.sum_filter, hset, sum_divisors_moebius_real]
  -- The full product of indicators is the pairwise-coprimality indicator.
  have hIndic : ∀ a ∈ Fintype.piFinset fun _ : ι ↦ X,
      ∏ q : ι × ι, ∑ e ∈ t q, g a q e =
        if ∀ i i' : ι, i ≠ i' → Nat.Coprime (m (a i)) (m (a i')) then 1 else 0 := by
    intro a ha
    rw [Finset.prod_congr rfl fun q _ ↦ hpair a ha q]
    simp [Finset.prod_ite_zero, Prod.forall, ← ite_or, or_iff_not_imp_left]
  -- Expand, swap, and reassemble the one-coordinate sums.
  calc ∑ a ∈ Fintype.piFinset fun _ : ι ↦ X,
        (if ∀ i i' : ι, i ≠ i' → Nat.Coprime (m (a i)) (m (a i')) then ∏ i, w i (a i) else 0)
      = ∑ a ∈ Fintype.piFinset fun _ : ι ↦ X,
          ∑ c ∈ pairConfigs ι E, (∏ q : ι × ι, g a q (c q)) * ∏ i, w i (a i) := by
        refine Finset.sum_congr rfl fun a ha ↦ ?_
        rw [hpc, ← Finset.sum_mul, ← prod_univ_sum t (g a), hIndic a ha]
        simp only [ite_mul, one_mul, zero_mul]
    _ = ∑ c ∈ pairConfigs ι E, ∑ a ∈ Fintype.piFinset fun _ : ι ↦ X,
          (∏ q : ι × ι, g a q (c q)) * ∏ i, w i (a i) := Finset.sum_comm
    _ = ∑ c ∈ pairConfigs ι E, (∏ q : ι × ι, ((μ (c q) : ℤ) : ℝ)) *
          ∏ i, restrictedSum X m (w i) (incLcm c i) := by
        refine Finset.sum_congr rfl fun c hc ↦ ?_
        -- separate the Möbius weight from the divisibility guard
        have hfac : ∀ a ∈ Fintype.piFinset fun _ : ι ↦ X,
            (∏ q : ι × ι, g a q (c q)) * ∏ i, w i (a i)
              = (∏ q : ι × ι, ((μ (c q) : ℤ) : ℝ)) *
                  ∏ i, (if incLcm c i ∣ m (a i) then w i (a i) else 0) := by
          intro a ha
          have hiff : (∀ q : ι × ι, c q ∣ m (a q.1) ∧ c q ∣ m (a q.2))
              ↔ ∀ i, incLcm c i ∣ m (a i) := by
            refine ⟨fun h i ↦ incLcm_dvd_of_forall fun q hq ↦ ?_, fun h q ↦
              ⟨(dvd_incLcm (Or.inl rfl)).trans (h q.1), (dvd_incLcm (Or.inr rfl)).trans (h q.2)⟩⟩
            rcases hq with rfl | rfl
            exacts [(h q).1, (h q).2]
          simp only [hg, Finset.prod_ite_zero, Finset.mem_univ, forall_const, ← hiff]
          split_ifs <;> simp
        rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum,
          ← prod_univ_sum (fun _ : ι ↦ X) fun i a ↦ if incLcm c i ∣ m a then w i a else 0]
        refine congrArg _ (Finset.prod_congr rfl fun i _ ↦ ?_)
        rw [restrictedSum_eq_sum_ite]

/-! ## The union bound over the configurations -/

/-- **The `k`-coordinate union bound, with the cancellation kept.** The difference between the
product of the `k` unrestricted one-coordinate sums and the pairwise-coprime restriction of the
coupled sum is at most the sum, over the non-trivial configurations, of the products of the `k`
*one-coordinate* restricted sums. No absolute value is taken inside a coordinate. -/
theorem abs_prod_sub_sum_pairwise_coprime_le (X : Finset α) (m : α → ℕ) (w : ι → α → ℝ)
    (E : Finset ℕ) (hm : ∀ a ∈ X, 0 < m a) (hE : ∀ a ∈ X, ∀ e, e ∣ m a → e ∈ E) (h1 : 1 ∈ E) :
    |∏ i, (∑ a ∈ X, w i a) -
        ∑ a ∈ Fintype.piFinset fun _ : ι ↦ X,
          (if ∀ i i' : ι, i ≠ i' → Nat.Coprime (m (a i)) (m (a i')) then ∏ i, w i (a i) else 0)|
      ≤ ∑ c ∈ {c ∈ pairConfigs ι E | c ≠ fun _ ↦ 1},
          ∏ i, |restrictedSum X m (w i) (incLcm c i)| := by
  have hone : (fun _ : ι × ι ↦ 1) ∈ pairConfigs ι E :=
    mem_pairConfigs.mpr fun q ↦ by split_ifs <;> simp [h1]
  rw [sum_pairwise_coprime_eq_sum_moebius X m w E hm hE,
    ← Finset.sum_filter_add_sum_filter_not (pairConfigs ι E) (fun c ↦ c = fun _ ↦ 1),
    Finset.filter_eq', if_pos hone, Finset.sum_singleton]
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, Finset.prod_const_one, one_mul,
    incLcm_one, restrictedSum_one, sub_add_cancel_left, abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ ↦ ?_)
  simp only [abs_mul, Finset.abs_prod]
  exact mul_le_of_le_one_left (by positivity)
    (Finset.prod_le_one (fun _ _ ↦ abs_nonneg _) fun q _ ↦ abs_moebius_real_le_one (c q))

/-- **The union bound, cashed against the one-coordinate cost `C/e`.** If forcing `e` into the
modulus costs a factor `C/e` in each coordinate, the coupling costs
`C^k∑_{configs ≠ 1}∏_i L_i^{-1}`, which
`Gap212.Sieve.exists_threshold_sum_one_div_prod_incLcm_lt` makes small. -/
theorem abs_prod_sub_sum_pairwise_coprime_le_prod (X : Finset α) (m : α → ℕ) (w : ι → α → ℝ)
    (E : Finset ℕ) (hm : ∀ a ∈ X, 0 < m a) (hE : ∀ a ∈ X, ∀ e, e ∣ m a → e ∈ E) (h1 : 1 ∈ E)
    (hEpos : ∀ e ∈ E, 0 < e) {C : ℝ}
    (hA : ∀ (i : ι) (e : ℕ), 0 < e → |restrictedSum X m (w i) e| ≤ C / e) :
    |∏ i, (∑ a ∈ X, w i a) -
        ∑ a ∈ Fintype.piFinset fun _ : ι ↦ X,
          (if ∀ i i' : ι, i ≠ i' → Nat.Coprime (m (a i)) (m (a i')) then ∏ i, w i (a i) else 0)|
      ≤ C ^ Fintype.card ι *
          ∑ c ∈ {c ∈ pairConfigs ι E | c ≠ fun _ ↦ 1}, 1 / ∏ i, (incLcm c i : ℝ) := by
  refine (abs_prod_sub_sum_pairwise_coprime_le X m w E hm hE h1).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c hc ↦ ?_
  have hpos := incLcm_pos (pairConfigs_pos hEpos (Finset.mem_filter.mp hc).1)
  rw [mul_one_div, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_div_distrib]
  exact Finset.prod_le_prod (fun i _ ↦ abs_nonneg _) fun i _ ↦ hA i _ (hpos i)

/-- **The `k`-coordinate determination, as one statement.** For every `ε > 0` there is a threshold
`z`, depending only on `ε` and the number of coordinates, such that: whenever every one-coordinate
restricted sum obeys `|A_i(e)| ≤ C/e` and every prime factor of every modulus in play exceeds `z`,
the pairwise-coprimality restriction costs at most `C^kε`.

**This is the `k`-coordinate replacement for
`Gap212.Sieve.exists_threshold_abs_sub_sum_coprime_pairs_le`.** The identity extends by
bookkeeping; the bound does not (`Gap212.Sieve.prod_incLcm_lt_prod_edges_four`), and the prime-wise
regrouping `Gap212.Sieve.sq_configLcm_dvd_prod_incLcm` is what replaces it.

In the sieve `z` is supplied by `W(x)`: every modulus in play divides a least common multiple
coprime to `W(x)`, so every prime factor of it exceeds every prime dividing `W(x)`, and the largest
of those tends to infinity with `x`. -/
theorem exists_threshold_abs_prod_sub_sum_pairwise_coprime_le (ι : Type*) [Fintype ι]
    [DecidableEq ι] {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℕ, ∀ {α : Type*} (X : Finset α) (m : α → ℕ) (w : ι → α → ℝ) (E : Finset ℕ) (C : ℝ),
      (∀ a ∈ X, 0 < m a) → (∀ a ∈ X, ∀ e, e ∣ m a → e ∈ E) → 1 ∈ E → (∀ e ∈ E, 0 < e) →
      (∀ e ∈ E, ∀ p : ℕ, p.Prime → p ∣ e → z < p) → 0 ≤ C →
      (∀ (i : ι) (e : ℕ), 0 < e → |restrictedSum X m (w i) e| ≤ C / e) →
        |∏ i, (∑ a ∈ X, w i a) -
            ∑ a ∈ Fintype.piFinset fun _ : ι ↦ X,
              (if ∀ i i' : ι, i ≠ i' → Nat.Coprime (m (a i)) (m (a i')) then ∏ i, w i (a i)
                else 0)|
          ≤ C ^ Fintype.card ι * ε := by
  obtain ⟨z, hz⟩ := exists_threshold_sum_one_div_prod_incLcm_lt ι hε
  refine ⟨z, fun X m w E C hm hE h1 hEpos hEprime hC hA ↦ ?_⟩
  refine (abs_prod_sub_sum_pairwise_coprime_le_prod X m w E hm hE h1 hEpos hA).trans ?_
  exact mul_le_mul_of_nonneg_left (hz E hEpos hEprime).le (by positivity)

/-! ## A pair of tuples is a tuple of pairs

The two sums the sieving-error statements compare are iterated sums over a pair of boxes; the
identity above is stated at a single sum over tuples in one box of *pairs*. This is the
reindexing. -/

/-- **A pair of tuples reindexed as a tuple of pairs.** -/
theorem sum_pair_tuples_eq {β : Type*} {M : Type*} [AddCommMonoid M] (D D' : Finset β)
    (f : (ι → β × β) → M) :
    ∑ d ∈ Fintype.piFinset fun _ : ι ↦ D, ∑ d' ∈ Fintype.piFinset fun _ : ι ↦ D',
        f (fun i ↦ (d i, d' i))
      = ∑ a ∈ Fintype.piFinset fun _ : ι ↦ D ×ˢ D', f a := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun p i ↦ (p.1 i, p.2 i)) (fun a ↦ (fun i ↦ (a i).1, fun i ↦ (a i).2))
    ?_ ?_ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun _ _ ↦ rfl
  all_goals simp +contextual [Fintype.mem_piFinset, forall_and]

/-! ## The same bound at an exponent below one

The one-coordinate cost the sieve can actually supply is not `C/e` but `C/e^s` for an `s` strictly
between `1/2` and `1`: at the very top of the modulus range the one-coordinate sum degenerates to a
*single* term, and the `\log x` saving that `C = O(1/B_x)` asserts is not available there. See
`Gap212.Sieve.SievingErrorReduction` for the witness. The prime-wise regrouping has room for
that, because the fibre count `τ(M)^{k^2}` is beaten by `M^η` for *every* `η > 0` once the primes
in play are large enough — so `∑_M M^{η-2s}` converges for any `s > 1/2`. -/

/-- **A natural power bound transferred to an `r`-th root.** -/
theorem cast_le_rpow_inv_natCast {t M r : ℕ} (hr : r ≠ 0) (h : t ^ r ≤ M) :
    (t : ℝ) ≤ (M : ℝ) ^ ((r : ℝ)⁻¹) := by
  rw [Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by positivity),
    Real.rpow_natCast]
  exact_mod_cast h

/-- **The divisor count is beaten by every positive power of the modulus**, once every prime factor
is large enough. The threshold depends on the exponent and on the power taken, which is all the
prime-wise regrouping needs: `τ(M)^{k^2} ≤ M^η` for the `η` the exponent `s` leaves free. -/
theorem exists_pow_card_divisors_le_rpow (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ r : ℕ, r ≠ 0 ∧ ∀ M : ℕ, M ≠ 0 → (∀ p ∈ M.primeFactors, 2 ^ r ≤ p) →
      ((#M.divisors : ℝ)) ^ n ≤ (M : ℝ) ^ η := by
  obtain ⟨r₀, hr₀⟩ := exists_nat_gt ((n : ℝ) / η)
  refine ⟨r₀ + 1, r₀.succ_ne_zero, fun M hM hbig ↦ ?_⟩
  rw [div_lt_iff₀ hη] at hr₀
  calc ((#M.divisors : ℝ)) ^ n ≤ ((M : ℝ) ^ (((r₀ + 1 : ℕ) : ℝ)⁻¹)) ^ n := by
        gcongr
        exact cast_le_rpow_inv_natCast r₀.succ_ne_zero
          (card_divisors_pow_le_of_primeFactors_gt hM hbig)
    _ = (M : ℝ) ^ (((r₀ + 1 : ℕ) : ℝ)⁻¹ * n) := by
        rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
    _ ≤ (M : ℝ) ^ η := by
        refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM) ?_
        rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
        push_cast
        linarith

/-- **The configuration sum at an exponent above `1/2`.** For every `s > 1/2` and every `ε > 0`
there is a threshold `z` — depending on `s`, `ε` and the number of coordinates — with

  `∑_{(e_q) ≠ 1} (∏_i L_i)^{-s} < ε`

whenever every prime factor of every `e ∈ E` exceeds `z`.

`s = 1` is `Gap212.Sieve.exists_threshold_sum_one_div_prod_incLcm_lt`; the point of the general `s`
is that the one-coordinate estimate the sieve can supply carries an exponent strictly below `1`,
and `1/2` is where the prime-wise saving `M^{-2s}` stops beating the fibre count. -/
theorem exists_threshold_sum_one_div_prod_incLcm_rpow_lt (ι : Type*) [Fintype ι] [DecidableEq ι]
    {s ε : ℝ} (hs : 1 / 2 < s) (hε : 0 < ε) :
    ∃ z : ℕ, ∀ E : Finset ℕ, (∀ e ∈ E, 0 < e) →
      (∀ e ∈ E, ∀ p : ℕ, p.Prime → p ∣ e → z < p) →
        ∑ c ∈ {c ∈ pairConfigs ι E | c ≠ fun _ ↦ 1},
          1 / (∏ i, (incLcm c i : ℝ)) ^ s < ε := by
  set n := Fintype.card (ι × ι)
  obtain ⟨r, -, hrbig⟩ := exists_pow_card_divisors_le_rpow n (η := s - 1 / 2) (by linarith)
  obtain ⟨z₁, hz₁⟩ := exists_threshold_sum_lt
    (Real.summable_one_div_nat_rpow.mpr (show (1 : ℝ) < s + 1 / 2 by linarith)) hε
  refine ⟨max z₁ (2 ^ r), fun E hE hEprime ↦ ?_⟩
  refine (sum_le_sum_image_configLcm (g := fun M ↦ 1 / (M : ℝ) ^ (2 * s)) (fun c hc ↦ ?_)
    fun c hc ↦ ?_).trans_lt (hz₁ _ (lt_configLcm_image hE hEprime (le_max_left _ _)))
  all_goals obtain ⟨hcE, -⟩ := Finset.mem_filter.mp hc
  all_goals have hM0 := configLcm_pos (pairConfigs_pos hE hcE)
  -- Step 1: the prime-wise saving at the exponent `s`.
  · refine one_div_le_one_div_of_le (by positivity) ?_
    rw [Real.rpow_mul (by positivity), Real.rpow_two]
    exact Real.rpow_le_rpow (by positivity) (sq_configLcm_le_prod hE hcE) (by linarith)
  -- Step 2: cash the divisor count against the fibre.
  have hcard := (card_fiber_le (E := E) hM0.ne').trans (hrbig _ hM0.ne'
    (le_of_mem_primeFactors_configLcm (le_max_right _ _) hEprime hcE))
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
    show 2 * s = (s - 1 / 2) + (s + 1 / 2) by ring, Real.rpow_add (by positivity) (s - 1 / 2)]
  gcongr

/-- **The union bound cashed against the one-coordinate cost `C/e^s`.** -/
theorem abs_prod_sub_sum_pairwise_coprime_le_rpow (X : Finset α) (m : α → ℕ) (w : ι → α → ℝ)
    (E : Finset ℕ) (hm : ∀ a ∈ X, 0 < m a) (hE : ∀ a ∈ X, ∀ e, e ∣ m a → e ∈ E) (h1 : 1 ∈ E)
    (hEpos : ∀ e ∈ E, 0 < e) {C s : ℝ}
    (hA : ∀ (i : ι) (e : ℕ), 0 < e → |restrictedSum X m (w i) e| ≤ C / (e : ℝ) ^ s) :
    |∏ i, (∑ a ∈ X, w i a) -
        ∑ a ∈ Fintype.piFinset fun _ : ι ↦ X,
          (if ∀ i i' : ι, i ≠ i' → Nat.Coprime (m (a i)) (m (a i')) then ∏ i, w i (a i) else 0)|
      ≤ C ^ Fintype.card ι *
          ∑ c ∈ {c ∈ pairConfigs ι E | c ≠ fun _ ↦ 1}, 1 / (∏ i, (incLcm c i : ℝ)) ^ s := by
  refine (abs_prod_sub_sum_pairwise_coprime_le X m w E hm hE h1).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c hc ↦ ?_
  have hpos := incLcm_pos (pairConfigs_pos hEpos (Finset.mem_filter.mp hc).1)
  rw [mul_one_div, ← Real.finsetProd_rpow _ _ (fun i _ ↦ by positivity) s, ← Finset.card_univ,
    ← Finset.prod_const, ← Finset.prod_div_distrib]
  exact Finset.prod_le_prod (fun i _ ↦ abs_nonneg _) fun i _ ↦ hA i _ (hpos i)

/-- **The `k`-coordinate determination at an exponent above `1/2`.** The form the sieve can use:
for every `s > 1/2` and every `ε > 0` there is a threshold `z` such that, whenever every
one-coordinate restricted sum obeys `|A_i(e)| ≤ C/e^s` and every prime factor of every modulus in
play exceeds `z`, the pairwise-coprimality restriction costs at most `C^kε`.

`Gap212.Sieve.exists_threshold_abs_prod_sub_sum_pairwise_coprime_le` is the `s = 1` case. The
general `s` is the form used: the one-coordinate estimate is proved at `s = 3/4`
(`Gap212.Sieve.oneCoordLcmDecayAtLevelOfSupport_of_smoothMoebiusInnerBound`). -/
theorem exists_threshold_abs_prod_sub_sum_pairwise_coprime_le_rpow (ι : Type*) [Fintype ι]
    [DecidableEq ι] {s ε : ℝ} (hs : 1 / 2 < s) (hε : 0 < ε) :
    ∃ z : ℕ, ∀ {α : Type*} (X : Finset α) (m : α → ℕ) (w : ι → α → ℝ) (E : Finset ℕ) (C : ℝ),
      (∀ a ∈ X, 0 < m a) → (∀ a ∈ X, ∀ e, e ∣ m a → e ∈ E) → 1 ∈ E → (∀ e ∈ E, 0 < e) →
      (∀ e ∈ E, ∀ p : ℕ, p.Prime → p ∣ e → z < p) → 0 ≤ C →
      (∀ (i : ι) (e : ℕ), 0 < e → |restrictedSum X m (w i) e| ≤ C / (e : ℝ) ^ s) →
        |∏ i, (∑ a ∈ X, w i a) -
            ∑ a ∈ Fintype.piFinset fun _ : ι ↦ X,
              (if ∀ i i' : ι, i ≠ i' → Nat.Coprime (m (a i)) (m (a i')) then ∏ i, w i (a i)
                else 0)|
          ≤ C ^ Fintype.card ι * ε := by
  obtain ⟨z, hz⟩ := exists_threshold_sum_one_div_prod_incLcm_rpow_lt ι hs hε
  refine ⟨z, fun X m w E C hm hE h1 hEpos hEprime hC hA ↦ ?_⟩
  refine (abs_prod_sub_sum_pairwise_coprime_le_rpow X m w E hm hE h1 hEpos hA).trans ?_
  exact mul_le_mul_of_nonneg_left (hz E hEpos hEprime).le (by positivity)

end Gap212.Sieve
