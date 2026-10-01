/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.PrimeTailProduct
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The tails behind the two sieving errors

`Gap212.Sieve.SelbergSievingError` and `Gap212.Sieve.TotientSievingError` both say that passing
from a sum over the tuples whose least common multiples are merely coprime to `W(x)` to the sub-sum
over those whose lcms are in addition **pairwise coprime** costs `o` of the main term. This file
determines which shape of argument can do that, and proves its elementary parts.

## The setting

Write `m_i = [d_i,d'_i]` and `B_x = (φ(W)/W)\log x`. The difference of the two sums is supported on
the tuples where two of the `m_i` share a prime `p`. Every `m_i` is coprime to `W(x)`, and `W(x)`
is the primorial of `z = ⌊\log\log\log x⌋`, so such a `p` does not divide `W(x)` and therefore
**exceeds `z`** — and `z → ∞`.

## The determination: the naive union bound fails, the Möbius union bound does not

**Taking absolute values under a union bound over the pairs `(i,i')` and the shared primes `p` is
hopeless, by `(\log x)^{4k}`.** Not because the factorization breaks — it does not;
`|∏_i| = ∏_i| |` — but because the one-coordinate factors change size. The signed one-coordinate
pair sum is `∑_{d,d'} μ(d)μ(d')F(\log_x d)G(\log_x d')/[d,d'] ≍ B_x^{-1}`, while its absolute-value
analogue is `∑_{d,d'} |…|/[d,d'] ≍ B_x^{3}`: writing `1/[d,d'] = (d,d')/(dd')` gives three nested
harmonic sums instead of one cancelling sum. So each coordinate loses a factor
`B_x^4 ≍ ((φ(W)/W)\log x)^4`, `k` coordinates lose `B_x^{4k}`, and the target `o(B_x^{-k})` has no
room at all. Against that the prime tail supplies only `∑_{p>z}p^{-2} ≍ 1/(z\log z)`, i.e. about
`1/\log\log\log x`. The two scales are not comparable.

**A union bound need not take absolute values.** Möbius-invert the coprimality indicator instead:
for squarefree `a,b`, `[(a,b)=1] = ∑_{e ∣ (a,b)} μ(e)`, so

  `∑_{pairwise coprime} = ∑_{(e_{ii'})} (∏_{i≠i'} μ(e_{ii'})) · ∏_i A^{±}(E_i)`,
  `E_i = [e_{ii'} : i' ≠ i]`,  `A^{±}(E) = ∑_{E ∣ [d,d'], (dd',W)=1} μ(d)μ(d')FG/[d,d']`,

an **exact identity** in which every term is a product of one-coordinate sums and no absolute value
has been taken. The `(e_{ii'}) = (1,…,1)` term is the full-box sum, so the difference is the sum of
the remaining terms, and only there — at the very end, over the `(e_{ii'})` — is the triangle
inequality used. `Gap212.Sieve.sum_coprime_pairs_eq_sum_moebius` is this identity at two
coordinates, which is the case where the pair index is a single `e`.

**At `k` coordinates the bound needs more than bookkeeping.** The *identity* extends directly
(`Gap212.Sieve.sum_pairwise_coprime_eq_sum_moebius`); the **bound** does not. At `k` coordinates
coordinate `i` carries `L_i = [e_{ii'} : i' ≠ i]`, and the edge-by-edge accounting that pays for
two coordinates with `∑_{e>z}e^{-2}` requires `∏_{pairs}e_{ii'} ≤ ∏_iL_i`, which is **false from
`k = 4` on**: with all six `e_{ii'} = p` one has `∏_iL_i = p^4` against `∏_{i<i'}e_{ii'} = p^6`, so
summing edge by edge diverges (`Gap212.Sieve.prod_incLcm_lt_prod_edges_four`). The bound is
prime-wise instead — `Gap212.Sieve.sq_configLcm_dvd_prod_incLcm`, `M^2 ∣ ∏_iL_i` for `M` the lcm of
*all* the edge moduli, one factor per endpoint — and is proved in
`Gap212.Sieve.PairwiseCoprimeMoebius`.

So a union bound over pairs `(i,i')` and primes `p` survives the factorization over coordinates;
what absolute values destroy is the *cancellation*, and Möbius inversion of the indicator never
takes them.

## What the union bound then needs, exactly

`|A^{±}(E)| = O(1/(E^s·B_x))` for an exponent `s` strictly between `1/2` and `1`, uniformly in the
`E` coprime to `W(x)`. **The exponent is not slack: at `s = 1` the statement is false.** Two large
primes `P ∈ (B/2,B]`, `Q ∈ (B/4,B/2]` and `E = PQ` leave the one-coordinate sum exactly two terms —
`PQ > B`, so `P` and `Q` divide different coordinates and each pins its coordinate — whence
`A^{±}(PQ) ≍ 1/(PQ)` with no `\log x` saving at all, against an asserted `K/(PQ·B_x)`. The failure
mode is `Gap212.Sieve.not_uniformMoebiusPartialSumDecay`'s: a modulus large enough that the inner
Möbius sum has one term, and one term does not cancel. See
`Gap212.Sieve.OneCoordLcmDecayAtLevel` in `Gap212.Sieve.SievingErrorReduction`. The truncation-free
form `Gap212.Sieve.OneCoordLcmDecay` is false at every exponent
(`Gap212.Sieve.not_oneCoordLcmDecay`), because at `B = 1` the box is one point and the sum is the
uncancelled `F(0)G(0)`. At a prime the constant is computable: in the Euler
product of the one-coordinate sum the local factor at `p ∤ W` is `1 - 2/p + 1/p = 1 - 1/p` for the
denominator `[d,d']` (the four local patterns `(1,1),(p,1),(1,p),(p,p)` contributing
`1,-1/p,-1/p,+1/p`), of which the part with `p ∣ [d,d']` is `-1/p`; the ratio is `-1/(p-1)`. For
the totient denominator `φ([d,d'])` the same four patterns give `1 - 1/(p-1)` and restricted part
`-1/(p-1)`, ratio `-1/(p-2)`. So the cost of forcing `p ∣ [d,d']` in one coordinate is

  `≍ 1/(p-1)` for `Gap212.Sieve.SelbergSievingError` and `≍ 1/(p-2)` for
  `Gap212.Sieve.TotientSievingError` — in both cases `O(1/p)`,

**not** `O(\log p/p)` and nothing worse. Squared and summed over `p > z` this is
`∑_{p>z}1/(p-1)^2`, which is exactly `Gap212.Sieve.primeTailWeight` — already known summable in
`Gap212.Sieve.PrimeTailProduct` — so the `p`-sum converges with room to spare, and over
general `E > 1` the same holds by comparison with `∑_{n>z}n^{-2} ≍ 1/z`.

## The one-coordinate estimate

Both sieving errors therefore reduce to the signed one-coordinate estimate
`|A^{±}(E)| = O(1/(E^sB_x))` uniform in `E`, i.e. Möbius cancellation uniform in a growing modulus;
the reduction, at every number of coordinates, is in `Gap212.Sieve.SievingErrorReduction`. The
elementary `Gap212.Sieve.sum_one_div_lcm_prime_dvd_le` below shows that the `1/p` holds at the
level of the *support* of the restriction; the `\log x`-power saving is the analytic part.

That estimate is proved for both kernels. `Gap212.Sieve.SmoothMoebiusInner` removes the modulus
before the integration in the summation by parts, which avoids the `\log\log x` the partial-sum
route loses, and `Gap212.Sieve.selbergSievingError` proves `Gap212.Sieve.SelbergSievingError m` at
every `m`. `Gap212.Sieve.SmoothTotientInner` does the same for the `1/(p-2)` column — in two steps,
this kernel's local factor `1 - 1/((p-1)p^s)` vanishing at `s = 0` for `p = 2`, so the modulus
cannot be removed in one — and `Gap212.Sieve.totientSievingError` proves
`Gap212.Sieve.TotientSievingError m` at every `m`. Both statements are at `β ≥ 1`.

## Main results

* `Gap212.Sieve.exists_threshold_sum_lt`, `Gap212.Sieve.exists_threshold_sum_one_div_sq_lt`,
  `Gap212.Sieve.exists_threshold_sum_primeTailWeight_lt`: the tails above a threshold, uniformly
  over the finite set summed — the shape of `Gap212.Sieve.exists_threshold_prod_one_sub_ge`, and
  for the same reason: the consumer's set of moduli varies with `x`.
* `Gap212.Sieve.lcm_eq_prime_mul_lcm_stripPrime`: `p ∣ [d,d']` with `d,d'` squarefree gives
  `[d,d'] = p·[d/p^{ε},d'/p^{ε'}]` — the arithmetic behind "forcing `p ∣ [d,d']` costs `1/p`".
* `Gap212.Sieve.sum_one_div_lcm_prime_dvd_le`: that cost, as the bound `3/p` on the reciprocal-lcm
  sum over the pairs with `p ∣ [d,d']`.
* `Gap212.Sieve.sum_coprime_pairs_eq_sum_moebius`: the coprimality restriction expanded by Möbius,
  with the coordinates separated and no absolute value taken.
* `Gap212.Sieve.exists_threshold_abs_sub_sum_coprime_pairs_le`: the two together — granting the
  one-coordinate cost `c/e`, the coupling costs at most `cc'ε` once every non-trivial `e` in play
  exceeds a threshold depending only on `ε`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset
open scoped ArithmeticFunction.Moebius

/-! ## Tails above a threshold, uniformly in the finite set -/

/-- **Uniform tail vanishing.** For a summable `f` on the naturals and every `ε > 0` there is a
threshold `z` such that *every* finite sum of `f` over naturals exceeding `z` is below `ε`. -/
theorem exists_threshold_sum_lt {f : ℕ → ℝ} (hf : Summable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℕ, ∀ s : Finset ℕ, (∀ n ∈ s, z < n) → ∑ n ∈ s, f n < ε := by
  classical
  obtain ⟨F, hF⟩ := hf.vanishing (gt_mem_nhds hε)
  exact ⟨F.sup id, fun s hs ↦ hF s <| Finset.disjoint_left.mpr fun n hns hnF ↦
    (hs n hns).not_ge (Finset.le_sup (f := id) hnF)⟩

/-- `∑ 1/n²` converges. -/
theorem summable_one_div_sq : Summable fun n : ℕ ↦ 1 / (n : ℝ) ^ 2 :=
  Real.summable_one_div_nat_pow.mpr one_lt_two

/-- **The reciprocal-square tail above a threshold.** For every `ε > 0` there is a `z` such that
every finite sum of `1/n²` over naturals exceeding `z` is below `ε`. -/
theorem exists_threshold_sum_one_div_sq_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℕ, ∀ s : Finset ℕ, (∀ n ∈ s, z < n) → ∑ n ∈ s, 1 / (n : ℝ) ^ 2 < ε :=
  exists_threshold_sum_lt summable_one_div_sq hε

/-- **The `1/(p-1)²` tail above a threshold**, the sum companion of
`Gap212.Sieve.exists_threshold_prod_one_sub_ge`. -/
theorem exists_threshold_sum_primeTailWeight_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℕ, ∀ s : Finset Nat.Primes, (∀ p ∈ s, z < (p : ℕ)) →
      ∑ p ∈ s, primeTailWeight p < ε := by
  classical
  obtain ⟨F, hF⟩ := summable_primeTailWeight.vanishing (gt_mem_nhds hε)
  exact ⟨F.sup (↑), fun s hs ↦ hF s <| Finset.disjoint_left.mpr fun p hps hpF ↦
    (hs p hps).not_ge (Finset.le_sup (f := ((↑) : Nat.Primes → ℕ)) hpF)⟩

/-! ## Stripping a prime from a least common multiple -/

/-- **One factor `p` removed from `d`**, when there is one to remove. -/
def stripPrime (p d : ℕ) : ℕ := if p ∣ d then d / p else d

/-- `stripPrime p d` divides `d`. -/
theorem stripPrime_dvd (p d : ℕ) : stripPrime p d ∣ d := by
  unfold stripPrime
  split
  · exact Nat.div_dvd_of_dvd ‹p ∣ d›
  · exact dvd_rfl

/-- `d` divides `p * stripPrime p d`. -/
theorem dvd_prime_mul_stripPrime (p d : ℕ) : d ∣ p * stripPrime p d := by
  unfold stripPrime
  split
  · simp [Nat.mul_div_cancel' ‹p ∣ d›]
  · exact dvd_mul_left d p

/-- For positive `p` and `d`, `stripPrime p d` is positive. -/
theorem stripPrime_pos {p d : ℕ} (hp : 0 < p) (hd : 0 < d) : 0 < stripPrime p d := by
  unfold stripPrime
  split
  · exact Nat.div_pos (Nat.le_of_dvd hd ‹p ∣ d›) hp
  · exact hd

/-- For positive `d`, `stripPrime p d ≤ d`. -/
theorem stripPrime_le {p d : ℕ} (hd : 0 < d) : stripPrime p d ≤ d :=
  Nat.le_of_dvd hd (stripPrime_dvd p d)

/-- **The stripped number is no longer divisible by `p`** — this is where squarefreeness enters:
`d` carries at most one factor `p`, so removing one removes them all. -/
theorem not_dvd_stripPrime {p d : ℕ} (hp : p.Prime) (hd : Squarefree d) :
    ¬ p ∣ stripPrime p d := by
  unfold stripPrime
  split_ifs with hpd
  · exact fun h ↦ hp.one_lt.ne' <| Nat.isUnit_iff.mp <| hd p <|
      Nat.mul_div_cancel' hpd ▸ mul_dvd_mul_left p h
  · exact hpd

/-- **A prime divides a least common multiple of squarefree numbers exactly once**: stripping it
from both arguments pulls one factor `p` out of the lcm.

  `p ∣ [d,d'] → [d,d'] = p · [d/p^{ε}, d'/p^{ε'}]`,

the exponents being `1` where `p` divides and `0` where it does not. This is the whole arithmetic
content of "forcing `p ∣ [d,d']` costs a factor `1/p`". -/
theorem lcm_eq_prime_mul_lcm_stripPrime {p d d' : ℕ} (hp : p.Prime) (hd : Squarefree d)
    (hd' : Squarefree d') (hdvd : p ∣ Nat.lcm d d') :
    Nat.lcm d d' = p * Nat.lcm (stripPrime p d) (stripPrime p d') := by
  have hcop : Nat.Coprime p (Nat.lcm (stripPrime p d) (stripPrime p d')) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h ↦
      ((Nat.Prime.dvd_mul hp).mp (h.trans (Nat.lcm_dvd_mul _ _))).elim
        (not_dvd_stripPrime hp hd) (not_dvd_stripPrime hp hd')
  refine Nat.dvd_antisymm (Nat.lcm_dvd ?_ ?_) (hcop.mul_dvd_of_dvd_of_dvd hdvd ?_)
  · exact (dvd_prime_mul_stripPrime p d).trans (mul_dvd_mul_left p (Nat.dvd_lcm_left _ _))
  · exact (dvd_prime_mul_stripPrime p d').trans (mul_dvd_mul_left p (Nat.dvd_lcm_right _ _))
  · exact Nat.lcm_dvd ((stripPrime_dvd p d).trans (Nat.dvd_lcm_left d d'))
      ((stripPrime_dvd p d').trans (Nat.dvd_lcm_right d d'))

/-- **Stripping is injective where the divisibility pattern is fixed.** -/
theorem eq_of_stripPrime_eq {p a b : ℕ} (hab : p ∣ a ↔ p ∣ b)
    (h : stripPrime p a = stripPrime p b) : a = b := by
  by_cases ha : p ∣ a
  · exact (Nat.div_left_inj ha (hab.mp ha)).mp (by simpa [stripPrime, ha, hab.mp ha] using h)
  · simpa [stripPrime, ha, mt hab.mpr ha] using h

/-- A prime dividing a least common multiple divides one of the arguments. -/
theorem dvd_or_dvd_of_prime_dvd_lcm {p d d' : ℕ} (hp : p.Prime) (h : p ∣ Nat.lcm d d') :
    p ∣ d ∨ p ∣ d' :=
  (Nat.Prime.dvd_mul hp).mp (h.trans (Nat.lcm_dvd_mul d d'))

/-! ## The cost of forcing a prime into one coordinate -/

open Classical in
/-- **The pairs of squarefree divisors up to `B`**: the one-coordinate index set of a pair sum. -/
noncomputable def sqfreePairs (B : ℕ) : Finset (ℕ × ℕ) :=
  {q ∈ Icc 1 B ×ˢ Icc 1 B | Squarefree q.1 ∧ Squarefree q.2}

/-- A pair `q` lies in `sqfreePairs B` iff both coordinates lie in `[1, B]` and are squarefree. -/
theorem mem_sqfreePairs {B : ℕ} {q : ℕ × ℕ} : q ∈ sqfreePairs B ↔
    (1 ≤ q.1 ∧ q.1 ≤ B) ∧ (1 ≤ q.2 ∧ q.2 ≤ B) ∧ Squarefree q.1 ∧ Squarefree q.2 := by
  classical
  simp only [sqfreePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

open Classical in
/-- **One case of the cost bound.** On a set of pairs where the divisibility pattern of `p` is
constant, stripping `p` from both coordinates is injective and divides every lcm by exactly `p`, so
the sum over that set is at most `1/p` times the sum over the whole box. -/
private lemma sum_one_div_lcm_piece_le {p : ℕ} (hp : p.Prime) {B : ℕ} (T : Finset (ℕ × ℕ))
    (hT : ∀ q ∈ T, q ∈ sqfreePairs B ∧ p ∣ Nat.lcm q.1 q.2)
    (hpat : ∀ q ∈ T, ∀ r ∈ T, (p ∣ q.1 ↔ p ∣ r.1) ∧ (p ∣ q.2 ↔ p ∣ r.2)) :
    ∑ q ∈ T, (1 : ℝ) / (Nat.lcm q.1 q.2 : ℝ)
      ≤ 1 / p * ∑ q ∈ sqfreePairs B, (1 : ℝ) / (Nat.lcm q.1 q.2 : ℝ) := by
  classical
  set g : ℕ × ℕ → ℕ × ℕ := fun q ↦ (stripPrime p q.1, stripPrime p q.2)
  have hginj : ∀ q ∈ T, ∀ r ∈ T, g q = g r → q = r := fun q hq r hr h ↦
    Prod.ext (eq_of_stripPrime_eq (hpat q hq r hr).1 (congrArg Prod.fst h))
      (eq_of_stripPrime_eq (hpat q hq r hr).2 (congrArg Prod.snd h))
  have hgmem : ∀ q ∈ T, g q ∈ sqfreePairs B := fun q hq ↦ by
    obtain ⟨⟨h11, h12⟩, ⟨h21, h22⟩, hs1, hs2⟩ := mem_sqfreePairs.mp (hT q hq).1
    exact mem_sqfreePairs.mpr ⟨⟨stripPrime_pos hp.pos h11, (stripPrime_le h11).trans h12⟩,
      ⟨stripPrime_pos hp.pos h21, (stripPrime_le h21).trans h22⟩,
      hs1.squarefree_of_dvd (stripPrime_dvd p q.1), hs2.squarefree_of_dvd (stripPrime_dvd p q.2)⟩
  have hterm : ∀ q ∈ T, (1 : ℝ) / (Nat.lcm q.1 q.2 : ℝ)
      = 1 / p * (1 / (Nat.lcm (g q).1 (g q).2 : ℝ)) := fun q hq ↦ by
    obtain ⟨⟨-, -, hs1, hs2⟩, hdvd⟩ := (hT q hq).imp_left mem_sqfreePairs.mp
    rw [lcm_eq_prime_mul_lcm_stripPrime hp hs1 hs2 hdvd]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    ← Finset.sum_image (f := fun r ↦ 1 / (Nat.lcm r.1 r.2 : ℝ)) hginj]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.image_subset_iff.mpr hgmem) fun r _ _ ↦ by positivity) (by positivity)

open Classical in
/-- **Forcing `p ∣ [d,d']` costs a factor `3/p`.** The reciprocal-lcm sum over the pairs of
squarefree divisors up to `B` whose least common multiple is divisible by `p` is at most `3/p`
times the same sum with no constraint.

This is the elementary half of the sieving-error bound, and it is the *absolute-value* half: no
cancellation is used, and the three comes from the three divisibility patterns `p ∣ d`, `p ∣ d'`,
`p ∣ (d,d')`. See the module docstring for why a bound of this shape is not by itself enough. -/
theorem sum_one_div_lcm_prime_dvd_le {p : ℕ} (hp : p.Prime) (B : ℕ) :
    ∑ q ∈ {q ∈ sqfreePairs B | p ∣ Nat.lcm q.1 q.2}, (1 : ℝ) / (Nat.lcm q.1 q.2 : ℝ)
      ≤ 3 / p * ∑ q ∈ sqfreePairs B, (1 : ℝ) / (Nat.lcm q.1 q.2 : ℝ) := by
  classical
  set S := {q ∈ sqfreePairs B | p ∣ Nat.lcm q.1 q.2}
  have hS : ∀ q ∈ S, q ∈ sqfreePairs B ∧ p ∣ Nat.lcm q.1 q.2 := fun q hq ↦ Finset.mem_filter.mp hq
  rw [← Finset.sum_filter_add_sum_filter_not S (fun q ↦ p ∣ q.1),
    ← Finset.sum_filter_add_sum_filter_not {q ∈ S | p ∣ q.1} (fun q ↦ p ∣ q.2)]
  have h1 := sum_one_div_lcm_piece_le hp {q ∈ {q ∈ S | p ∣ q.1} | p ∣ q.2}
    (fun q hq ↦ hS q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1) fun q hq r hr ↦ by
      simp only [Finset.mem_filter] at hq hr
      tauto
  have h2 := sum_one_div_lcm_piece_le hp {q ∈ {q ∈ S | p ∣ q.1} | ¬ p ∣ q.2}
    (fun q hq ↦ hS q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1) fun q hq r hr ↦ by
      simp only [Finset.mem_filter] at hq hr
      tauto
  have h3 := sum_one_div_lcm_piece_le hp {q ∈ S | ¬ p ∣ q.1}
    (fun q hq ↦ hS q (Finset.mem_filter.mp hq).1) fun q hq r hr ↦ by
      simp only [S, Finset.mem_filter] at hq hr
      have := dvd_or_dvd_of_prime_dvd_lcm hp hq.1.2
      have := dvd_or_dvd_of_prime_dvd_lcm hp hr.1.2
      tauto
  exact (add_le_add (add_le_add h1 h2) h3).trans_eq (by ring)

open Classical in
/-- **The weighted form of the cost bound.** A bounded weight is carried through unchanged. -/
theorem sum_abs_weight_div_lcm_prime_dvd_le {p : ℕ} (hp : p.Prime) (B : ℕ) {w : ℕ → ℕ → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ d d', |w d d'| ≤ C) :
    ∑ q ∈ {q ∈ sqfreePairs B | p ∣ Nat.lcm q.1 q.2}, |w q.1 q.2| / (Nat.lcm q.1 q.2 : ℝ)
      ≤ 3 * C / p * ∑ q ∈ sqfreePairs B, (1 : ℝ) / (Nat.lcm q.1 q.2 : ℝ) := by
  classical
  calc _ ≤ ∑ q ∈ {q ∈ sqfreePairs B | p ∣ Nat.lcm q.1 q.2},
        C * ((1 : ℝ) / (Nat.lcm q.1 q.2 : ℝ)) := Finset.sum_le_sum fun q _ ↦ by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_right (hw q.1 q.2) (by positivity)
    _ ≤ C * (3 / p * ∑ q ∈ sqfreePairs B, (1 : ℝ) / (Nat.lcm q.1 q.2 : ℝ)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_one_div_lcm_prime_dvd_le hp B) hC
    _ = _ := by ring

/-! ## The coprimality restriction, expanded by Möbius -/

/-- The Möbius sum over the divisors of `n`, read in `ℝ`. -/
theorem sum_divisors_moebius_real (n : ℕ) :
    ∑ e ∈ n.divisors, ((μ e : ℤ) : ℝ) = if n = 1 then 1 else 0 := by
  rw [← Int.cast_sum, ← ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  split <;> simp

/-- The Möbius function, read in `ℝ`, has absolute value at most `1`. -/
theorem abs_moebius_real_le_one (e : ℕ) : |((μ e : ℤ) : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e)

variable {α : Type*}

/-- **The one-coordinate sum with `e` forced into the modulus**: the quantity whose size decides
whether the sieving error closes. -/
def restrictedSum (X : Finset α) (m : α → ℕ) (w : α → ℝ) (e : ℕ) : ℝ :=
  ∑ a ∈ X with e ∣ m a, w a

/-- `restrictedSum X m w e` is the sum over `X` of `w a` where `e ∣ m a` and `0` elsewhere. -/
theorem restrictedSum_eq_sum_ite (X : Finset α) (m : α → ℕ) (w : α → ℝ) (e : ℕ) :
    restrictedSum X m w e = ∑ a ∈ X, if e ∣ m a then w a else 0 :=
  Finset.sum_filter _ _

/-- With `e = 1` the restriction is vacuous: `restrictedSum X m w 1 = ∑ a ∈ X, w a`. -/
theorem restrictedSum_one (X : Finset α) (m : α → ℕ) (w : α → ℝ) :
    restrictedSum X m w 1 = ∑ a ∈ X, w a := by
  simp [restrictedSum]

/-- **The coprimality restriction, expanded by Möbius — and the coordinates still separate.**
For a finite index set `X`, a modulus `m` and two weights `w`, `v`,

  `∑_{a,b ∈ X, (m a, m b) = 1} w(a)v(b) = ∑_e μ(e)·(∑_{a : e ∣ m a} w(a))·(∑_{b : e ∣ m b} v(b))`,

the outer sum running over any `E` containing every divisor of every `m a`.

The left side couples the two coordinates; every term of the right side is a *product of
one-coordinate sums*, and the expansion is an exact identity, not an estimate — no absolute value
is taken anywhere, so no cancellation is lost. -/
theorem sum_coprime_pairs_eq_sum_moebius (X : Finset α) (m : α → ℕ) (w v : α → ℝ) (E : Finset ℕ)
    (hm : ∀ a ∈ X, 0 < m a) (hE : ∀ a ∈ X, ∀ e, e ∣ m a → e ∈ E) :
    ∑ a ∈ X, ∑ b ∈ X, (if Nat.Coprime (m a) (m b) then w a * v b else 0)
      = ∑ e ∈ E, ((μ e : ℤ) : ℝ) * (restrictedSum X m w e * restrictedSum X m v e) := by
  classical
  have key : ∀ a ∈ X, ∀ b ∈ X, (if Nat.Coprime (m a) (m b) then w a * v b else 0)
      = ∑ e ∈ E, ((μ e : ℤ) : ℝ) *
          ((if e ∣ m a then w a else 0) * (if e ∣ m b then v b else 0)) := by
    intro a ha b hb
    have hset : {e ∈ E | e ∣ m b ∧ e ∣ m a} = (Nat.gcd (m a) (m b)).divisors := by
      ext e
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      exact ⟨fun h ↦ ⟨h.2.symm, (Nat.gcd_pos_of_pos_left _ (hm a ha)).ne'⟩,
        fun h ↦ ⟨hE a ha e h.1.1, h.1.symm⟩⟩
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, ← ite_and]
    rw [← Finset.sum_filter, hset, ← Finset.sum_mul, sum_divisors_moebius_real]
    split_ifs <;> simp_all [Nat.Coprime]
  simp_rw [restrictedSum_eq_sum_ite, Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm (s := E)]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [Finset.sum_comm (s := E)]
  exact Finset.sum_congr rfl fun b hb ↦ key a ha b hb

/-- **The union bound over the shared divisors, with the cancellation kept.** The difference
between the unrestricted double sum and its pairwise-coprime restriction is at most the sum, over
the non-trivial `e`, of the products of the two *one-coordinate* restricted sums. -/
theorem abs_sub_sum_coprime_pairs_le (X : Finset α) (m : α → ℕ) (w v : α → ℝ) (E : Finset ℕ)
    (hm : ∀ a ∈ X, 0 < m a) (hE : ∀ a ∈ X, ∀ e, e ∣ m a → e ∈ E) (h1 : 1 ∈ E) :
    |(∑ a ∈ X, w a) * (∑ b ∈ X, v b) -
        ∑ a ∈ X, ∑ b ∈ X, (if Nat.Coprime (m a) (m b) then w a * v b else 0)|
      ≤ ∑ e ∈ E with e ≠ 1, |restrictedSum X m w e| * |restrictedSum X m v e| := by
  classical
  rw [sum_coprime_pairs_eq_sum_moebius X m w v E hm hE, ← restrictedSum_one X m w,
    ← restrictedSum_one X m v, ← Finset.sum_filter_add_sum_filter_not E (fun e ↦ e = 1),
    Finset.filter_eq' E 1, if_pos h1, Finset.sum_singleton, ArithmeticFunction.moebius_apply_one,
    Int.cast_one, one_mul, sub_add_cancel_left, abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ ↦ ?_)
  rw [abs_mul, abs_mul]
  exact mul_le_of_le_one_left (by positivity) (abs_moebius_real_le_one e)

/-- **The union bound, cashed against the one-coordinate cost `c/e`.** If forcing `e` into the
modulus costs a factor `1/e` in each coordinate, the coupling costs `cc'∑_{e>1}e^{-2}`. -/
theorem abs_sub_sum_coprime_pairs_le_sq (X : Finset α) (m : α → ℕ) (w v : α → ℝ) (E : Finset ℕ)
    (hm : ∀ a ∈ X, 0 < m a) (hE : ∀ a ∈ X, ∀ e, e ∣ m a → e ∈ E) (h1 : 1 ∈ E) {c c' : ℝ}
    (hc : 0 ≤ c)
    (hAw : ∀ e ∈ E, e ≠ 1 → |restrictedSum X m w e| ≤ c / e)
    (hAv : ∀ e ∈ E, e ≠ 1 → |restrictedSum X m v e| ≤ c' / e) :
    |(∑ a ∈ X, w a) * (∑ b ∈ X, v b) -
        ∑ a ∈ X, ∑ b ∈ X, (if Nat.Coprime (m a) (m b) then w a * v b else 0)|
      ≤ c * c' * ∑ e ∈ E with e ≠ 1, 1 / (e : ℝ) ^ 2 := by
  classical
  refine (abs_sub_sum_coprime_pairs_le X m w v E hm hE h1).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun e he ↦ ?_
  obtain ⟨heE, hne⟩ := Finset.mem_filter.mp he
  calc |restrictedSum X m w e| * |restrictedSum X m v e|
      ≤ (c / e) * (c' / e) :=
        mul_le_mul (hAw e heE hne) (hAv e heE hne) (abs_nonneg _)
          (div_nonneg hc (Nat.cast_nonneg e))
    _ = c * c' * (1 / (e : ℝ) ^ 2) := by ring

/-- **The determination, as one statement.** For every `ε > 0` there is a threshold `z` such that
whenever the one-coordinate restricted sums obey `|A(e)| ≤ c/e` and every non-trivial `e` in play
exceeds `z`, the pairwise-coprimality restriction costs at most `cc'ε`.

Uniform in the data, in the same way and for the same reason as
`Gap212.Sieve.exists_threshold_prod_one_sub_ge`: the consumer's index set varies with `x`, so a
threshold depending on it would be useless. In the sieve `z` is supplied by `W(x)`: every divisor
`e > 1` of a least common multiple coprime to `W(x)` exceeds every prime dividing `W(x)`, and the
largest of those tends to infinity with `x`. -/
theorem exists_threshold_abs_sub_sum_coprime_pairs_le {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℕ, ∀ (X : Finset α) (m : α → ℕ) (w v : α → ℝ) (E : Finset ℕ) (c c' : ℝ),
      (∀ a ∈ X, 0 < m a) → (∀ a ∈ X, ∀ e, e ∣ m a → e ∈ E) → 1 ∈ E → 0 ≤ c → 0 ≤ c' →
      (∀ e ∈ E, e ≠ 1 → z < e) →
      (∀ e ∈ E, e ≠ 1 → |restrictedSum X m w e| ≤ c / e) →
      (∀ e ∈ E, e ≠ 1 → |restrictedSum X m v e| ≤ c' / e) →
        |(∑ a ∈ X, w a) * (∑ b ∈ X, v b) -
            ∑ a ∈ X, ∑ b ∈ X, (if Nat.Coprime (m a) (m b) then w a * v b else 0)|
          ≤ c * c' * ε := by
  classical
  obtain ⟨z, hz⟩ := exists_threshold_sum_one_div_sq_lt hε
  refine ⟨z, fun X m w v E c c' hm hE h1 hc hc' hlarge hAw hAv ↦ ?_⟩
  refine (abs_sub_sum_coprime_pairs_le_sq X m w v E hm hE h1 hc hAw hAv).trans ?_
  exact mul_le_mul_of_nonneg_left (hz {e ∈ E | e ≠ 1} fun e he ↦
    hlarge e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2).le (mul_nonneg hc hc')

end Gap212.Sieve
