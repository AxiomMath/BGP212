/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.SelbergDecoupling
public import Gap212.Sieve.InnerSumReciprocal
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The denominator divisor sum: the main term

The main term of the denominator divisor sum is

  `(x/W)∑_{d,d'}∏ᵢμ(dᵢ)μ(d'ᵢ)Fᵢ(log_x dᵢ)Gᵢ(log_x d'ᵢ)/∏ᵢ[dᵢ,d'ᵢ]`,

and unlike the totient-denominator sum of `Gap212.Sieve.SelbergDecoupling` its denominator is
already a product over the coordinates. So the reduction to one coordinate costs nothing beyond
dropping the pairwise-coprimality restriction, and the whole algebra of the main term is here.

## The algebra, in full

**Coordinate separation.** Over a full box the `k`-fold pair sum is literally the product of the
`k` one-coordinate pair sums (`Gap212.Sieve.sum_pair_prod_moebius_div_prod_lcm_eq_prod`), by
`Gap212.Sieve.sum_pair_prod_eq_prod` and `Finset.prod_div_distrib`. No coprimality is used, because
`1/∏ᵢ[dᵢ,d'ᵢ]` is a product whatever the tuples are.

**Selberg diagonalization at the plain least common multiple.** `1/[d,d'] = (d,d')/(dd')` and
`(d,d') = ∑_{e ∣ (d,d')}φ(e)` (`Nat.sum_totient`), so

  `∑_{d,d'≤B}u(d)v(d')/[d,d'] = ∑_{e≤B}φ(e)·(∑_{d≤B, e ∣ d}u(d)/d)(∑_{d'≤B, e ∣ d'}v(d')/d')`

(`Gap212.Sieve.sum_pair_div_lcm_eq_diagonal`). The diagonal weight is the bare totient, not the
`(μ*φ)` of the totient-denominator form: the plain reciprocal is the easier kernel.

**Pulling out the Möbius factor.**
`∑_{d≤B, e ∣ d}μ(d)H(d)/d = (μ(e)/e)∑_{f≤B/e,(f,e)=1}μ(f)H(ef)/f`
(`Gap212.Sieve.sum_moebius_div_filter_dvd`), so the one-coordinate pair sum is the Gram form

  `∑_{e≤B}φ(e)(μ(e)/e)²·Y_F(e)·Y_G(e)`

with the weight `Gap212.Sieve.lcmGramWeight`, which is `(p-1)/p²` at a prime. Carrying the
coprimality to `W(x)` through the weights turns `Y_F(e)` into exactly the inner sum of the
reciprocal-weight asymptotic at modulus `eW`
(`Gap212.Sieve.pairSumRecip_eq_gramSum`).

## Why the fixed-modulus inner-sum asymptotic does not close the limit

`Gap212.Sieve.tendsto_logx_mul_innerSumReciprocal` evaluates `\log x·Z_F(q) → -F'(0)q/φ(q)` for a
**fixed** modulus `q`. The modulus occurring here is `e·W(x)`, and it fails to be fixed for two
independent reasons:

* `e` runs over the whole box, and `log_x e` does not tend to `0`: the retreat region confines
  `∑ᵢtᵢ < (1-ε₀)(A_j+ε)`, so `log_x e` sweeps a fixed compact interval reaching about `0.265` at
  `p_⋆`. Summing over `e` against the Gram weight with `t = log_x e` is what reconstructs
  `∫₀^∞F'ᵢG'ᵢ`, so the `F'(0)` has to become `F'(log_x e)`;
* `W(x) = primorial ⌊\log\log\log x⌋` itself tends to infinity, so even at `e = 1` the hypothesis
  that `q` be fixed is not met.

Beyond uniformity, the `e`-sum needs the Mertens-type asymptotic
`∑_{e≤y,(e,W)=1}μ²(e)/φ(e) ∼ (φ(W)/W)\log y` to turn the Gram sum into the integral; that estimate,
with explicit error, is `Gap212.Sieve.sum_moebiusSq_div_totient_coprime`. That is the right sum,
and its constant really is `φ(W)/W`: the per-`e` heuristic contributes
`g⋆(e)(e/φ(e))²(W/φ(W))² = μ²(e)/φ(e)·(W/φ(W))²`, and the Euler factors of `∑μ²(e)/φ(e)` at `p ∤ W`
are `(1+1/(p-1))(1-1/p) = 1`, leaving exactly `∏_{p∣W}(1-1/p)`. This is why the normalization
`(φ(W)/W)\log x` produces `∫F'G'` with no correction factor.

## The Gram-sum limit

`Gap212.Sieve.LcmGramSumLimit` states the limit at exactly the quantity the algebra produces. It
quantifies over the profiles and over `B` independently, and as such it is false
(`Gap212.Sieve.not_lcmGramSumLimit`): the Gram sum reads `F` and `G` only on `[0,\log_xB]`, so a
profile supported above `\log_xB` makes the sum vanish identically while `∫₀^∞F'G'` does not. The
refutation is at `β = 1`, `B(x) = ⌊x⌋+1` and a bump supported in `(2,4)`.

`Gap212.Sieve.LcmGramSumLimitOfSupport` adds the hypothesis that the profiles vanish from `β` on,
and `Gap212.Sieve.tendsto_prod_pairSumRecip_of_support` is the main term derived from it.

## The residual sieving error

The main term of the sieve is restricted to the tuples whose least common multiples are pairwise
coprime; what is proved here is the sum over the **full** coprime-to-`W` box. The difference is a
sieving error, not estimated here: it is `Gap212.Sieve.SelbergSievingError`, proved as
`Gap212.Sieve.selbergSievingError`, and the totient-denominator sum has the same gap.

## Main results

* `Gap212.Sieve.sum_pair_div_lcm_eq_diagonal`: the Selberg diagonalization at the plain lcm.
* `Gap212.Sieve.sum_moebius_div_filter_dvd`: the Möbius pull-out.
* `Gap212.Sieve.pairSumRecip_eq_gramSum`: the one-coordinate pair sum as a Gram form in the inner
  sums of the reciprocal weight.
* `Gap212.Sieve.sum_pair_prod_moebius_div_prod_lcm_eq_prod`: the coordinates separate.
* `Gap212.Sieve.LcmGramSumLimit`: the Gram-sum limit without a support hypothesis.
* `Gap212.Sieve.not_lcmGramSumLimit`: that statement is false.
* `Gap212.Sieve.LcmGramSumLimitOfSupport`: the Gram-sum limit for profiles vanishing from `β` on.
* `Gap212.Sieve.tendsto_prod_pairSumRecip`: the main term, granting `LcmGramSumLimit`.
* `Gap212.Sieve.tendsto_prod_pairSumRecip_of_support`: the main term, granting
  `LcmGramSumLimitOfSupport`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY MeasureTheory
open scoped ArithmeticFunction.Moebius

/-! ## The kernel `1/[d,d']` -/

/-- **The real form of the plain lcm identity**: `1/[a,b] = (a,b)/(ab)`, with the numerators
attached to their own coordinate. The companion of `Gap212.Sieve.div_totient_lcm_eq`, and the
reason the reciprocal weight is the easier of the two kernels: no totient identity is needed, only
`Nat.gcd_mul_lcm`, which holds for all `a` and `b`. -/
theorem div_lcm_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (u v : ℝ) :
    u * v / (Nat.lcm a b : ℝ)
      = u / (a : ℝ) * (v / (b : ℝ)) * (Nat.gcd a b : ℝ) := by
  have h : (Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ) = (a : ℝ) * (b : ℝ) :=
    mod_cast Nat.gcd_mul_lcm a b
  have : (Nat.lcm a b : ℝ) ≠ 0 := mod_cast (Nat.lcm_pos ha hb).ne'
  have : (a : ℝ) ≠ 0 := mod_cast ha.ne'
  have : (b : ℝ) ≠ 0 := mod_cast hb.ne'
  field_simp
  linear_combination (-(u * v)) * h

/-- **The totient sums over the divisors to the integer**, over `ℝ`: `∑_{e ∣ n}φ(e) = n`. This is
`Nat.sum_totient`, and it is the expansion that makes the kernel `(d,d')` diagonal. -/
theorem sum_divisors_totient_real (n : ℕ) :
    ∑ e ∈ n.divisors, (Nat.totient e : ℝ) = (n : ℝ) := by
  exact_mod_cast Nat.sum_totient n

/-! ## The Selberg diagonalization in one coordinate -/

/-- **The Selberg diagonalization of the one-coordinate pair sum, at the plain least common
multiple.** For any weights `u, v` and any bound `B`,

  `∑_{d,d'≤B}u(d)v(d')/[d,d']
     = ∑_{e≤B}φ(e)·(∑_{d≤B, e ∣ d}u(d)/d)·(∑_{d'≤B, e ∣ d'}v(d')/d')`.

The kernel `1/[d,d']` becomes `(d,d')/(dd')` by `Gap212.Sieve.div_lcm_eq`, and `(d,d')` is expanded
over the common divisors `e` by `Gap212.Sieve.sum_divisors_totient_real`; the sums are interchanged
and the `e`-th term factors.

No hypothesis on `u, v` — in particular the coprimality to `W(x)` that the main term carries
is passed in through the weights, and the `e`-sum then has vanishing terms at every `e` sharing a
factor with `W(x)`. -/
theorem sum_pair_div_lcm_eq_diagonal (B : ℕ) (u v : ℕ → ℝ) :
    ∑ d ∈ Icc 1 B, ∑ d' ∈ Icc 1 B, u d * v d' / (Nat.lcm d d' : ℝ)
      = ∑ e ∈ Icc 1 B, (Nat.totient e : ℝ) *
          ((∑ d ∈ Icc 1 B with e ∣ d, u d / (d : ℝ)) *
            ∑ d' ∈ Icc 1 B with e ∣ d', v d' / (d' : ℝ)) := by
  classical
  have step : ∀ d ∈ Icc 1 B, ∀ d' ∈ Icc 1 B, u d * v d' / (Nat.lcm d d' : ℝ) = ∑ e ∈ Icc 1 B,
      if e ∣ d ∧ e ∣ d' then u d / (d : ℝ) * (v d' / (d' : ℝ)) * (Nat.totient e : ℝ) else 0 := by
    intro d hd d' hd'
    obtain ⟨hd1, hdB⟩ := Finset.mem_Icc.mp hd
    obtain ⟨hd1', hdB'⟩ := Finset.mem_Icc.mp hd'
    have hgpos : 0 < Nat.gcd d d' := Nat.gcd_pos_of_pos_left _ (by omega)
    have hset : (Nat.gcd d d').divisors = {e ∈ Icc 1 B | e ∣ d ∧ e ∣ d'} := by
      ext e
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc, Nat.dvd_gcd_iff]
      refine ⟨fun ⟨⟨h₁, h₂⟩, _⟩ ↦ ⟨⟨Nat.pos_of_dvd_of_pos h₁ (by omega),
        (Nat.le_of_dvd (by omega) h₁).trans hdB⟩, h₁, h₂⟩, fun ⟨_, h⟩ ↦ ⟨h, hgpos.ne'⟩⟩
    rw [div_lcm_eq (by omega) (by omega), ← sum_divisors_totient_real (Nat.gcd d d'), hset,
      Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun d hd ↦ Finset.sum_congr rfl fun d' hd' ↦ step d hd d' hd',
    Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  simp_rw [Finset.sum_filter, Finset.sum_mul_sum, Finset.mul_sum, ite_and]
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun d' _ ↦ ?_
  split_ifs <;> ring

/-- **The Möbius factor comes out of the diagonal sum**, at the reciprocal weight:
`∑_{d≤B, e ∣ d}μ(d)H(d)/d = (μ(e)/e)∑_{f≤B/e,(f,e)=1}μ(f)H(ef)/f`.

The reindexing `d = ef` is `Gap212.Sieve.sum_filter_dvd_eq_sum_mul`; the terms with `(e,f) > 1`
drop out because `ef` is then not squarefree (`Gap212.Sieve.moebius_mul_eq_zero_of_not_coprime`);
and on the rest `μ` and the identity function both split over the coprime factorization. -/
theorem sum_moebius_div_filter_dvd (B : ℕ) {e : ℕ} (he : 0 < e) (H : ℕ → ℝ) :
    ∑ d ∈ Icc 1 B with e ∣ d, (μ d : ℝ) * H d / (d : ℝ)
      = (μ e : ℝ) / (e : ℝ) *
          ∑ f ∈ Icc 1 (B / e) with Nat.Coprime e f, (μ f : ℝ) * H (e * f) / (f : ℝ) := by
  classical
  have hvanish : ∀ f ∈ Icc 1 (B / e),
      (μ (e * f) : ℝ) * H (e * f) / ((e * f : ℕ) : ℝ) ≠ 0 → Nat.Coprime e f :=
    fun f _ hne ↦ by_contra fun hc ↦ hne (by simp [moebius_mul_eq_zero_of_not_coprime hc])
  rw [sum_filter_dvd_eq_sum_mul B he, ← Finset.sum_filter_of_ne hvanish, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f hf ↦ ?_
  obtain ⟨hfmem, hcop⟩ := Finset.mem_filter.mp hf
  have : (e : ℝ) ≠ 0 := mod_cast he.ne'
  have : (f : ℝ) ≠ 0 := mod_cast (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hfmem).1)
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
  push_cast
  field_simp

/-! ## The Gram weight of the reciprocal kernel -/

/-- **The Gram weight of the diagonalized reciprocal form**, `g(e) = φ(e)(μ(e)/e)²`.

Nonnegative everywhere, unlike the `(μ*φ)(e)(μ(e)/φ(e))²` of the totient kernel, which is negative
at `e = 2`. It is `(p-1)/p²` at a prime, so the `e`-sum against it is `∑μ²(e)/e·∏(1-1/p)`, whose
logarithmic growth is what reconstructs the integral. -/
noncomputable def lcmGramWeight (e : ℕ) : ℝ :=
  (Nat.totient e : ℝ) * ((μ e : ℝ) / (e : ℝ)) ^ 2

/-- **The Gram weight at a prime is `(p-1)/p²`**, so the diagonalized form is not a rearrangement
of a vanishing kernel. -/
theorem lcmGramWeight_prime {p : ℕ} (hp : p.Prime) :
    lcmGramWeight p = ((p : ℝ) - 1) / (p : ℝ) ^ 2 := by
  simp [lcmGramWeight, ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, div_eq_mul_inv]

/-- **The one-coordinate pair sum as a Gram form.** Combining the diagonalization with the Möbius
pull-out,

  `∑_{d,d'≤B}μ(d)F(d)μ(d')G(d')/[d,d'] = ∑_{e≤B}g(e)·Y_F(e)·Y_G(e)`,
  `Y_F(e) = ∑_{f≤B/e,(f,e)=1}μ(f)F(ef)/f`,  `g(e) = φ(e)(μ(e)/e)²`.

`F` and `G` are read at the integer rather than at its logarithm, so that the inner sum's profile
argument `ef` is visible; at `F d = F₀(log_x d)` it is
`∑_{f≤B/e}μ(f)F₀(log_x(ef))/f`. -/
theorem sum_pair_moebius_div_lcm_eq_gram (B : ℕ) (F G : ℕ → ℝ) :
    ∑ d ∈ Icc 1 B, ∑ d' ∈ Icc 1 B,
        (μ d : ℝ) * F d * ((μ d' : ℝ) * G d') / (Nat.lcm d d' : ℝ)
      = ∑ e ∈ Icc 1 B, lcmGramWeight e *
          ((∑ f ∈ Icc 1 (B / e) with Nat.Coprime e f, (μ f : ℝ) * F (e * f) / (f : ℝ)) *
            ∑ f ∈ Icc 1 (B / e) with Nat.Coprime e f, (μ f : ℝ) * G (e * f) / (f : ℝ)) := by
  classical
  rw [sum_pair_div_lcm_eq_diagonal B (fun d ↦ (μ d : ℝ) * F d) (fun d ↦ (μ d : ℝ) * G d)]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  have he0 : 0 < e := (Finset.mem_Icc.mp he).1
  rw [sum_moebius_div_filter_dvd B he0 F, sum_moebius_div_filter_dvd B he0 G, lcmGramWeight]
  ring

/-! ## The coordinates separate -/

/-- **The `k`-fold main-term sum is a product of one-coordinate pair sums.** Over any box, with no
coprimality hypothesis whatever:

  `∑_{d,d'∈box^k}(∏ᵢμ(dᵢ)Fᵢ(dᵢ))(∏ᵢμ(d'ᵢ)Gᵢ(d'ᵢ))/∏ᵢ[dᵢ,d'ᵢ]
     = ∏ᵢ∑_{a,b∈box}μ(a)Fᵢ(a)μ(b)Gᵢ(b)/[a,b]`.

This is where the reciprocal kernel is genuinely easier than the totient one: `1/∏ᵢ[dᵢ,d'ᵢ]` is
already a product over the coordinates, so no analogue of
`Gap212.Sieve.totient_mul_prod_of_pairwise_coprime` — and hence no pairwise-coprimality hypothesis
— is needed to separate them. -/
theorem sum_pair_prod_moebius_div_prod_lcm_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (box : Finset ℕ) (F G : ι → ℕ → ℝ) :
    ∑ d ∈ Fintype.piFinset fun _ : ι ↦ box, ∑ d' ∈ Fintype.piFinset fun _ : ι ↦ box,
        (∏ i, (μ (d i) : ℝ) * F i (d i)) * (∏ i, (μ (d' i) : ℝ) * G i (d' i))
          / ∏ i, (Nat.lcm (d i) (d' i) : ℝ)
      = ∏ i, ∑ a ∈ box, ∑ b ∈ box,
          (μ a : ℝ) * F i a * ((μ b : ℝ) * G i b) / (Nat.lcm a b : ℝ) := by
  classical
  rw [← sum_pair_prod_eq_prod box
    fun i a b ↦ (μ a : ℝ) * F i a * ((μ b : ℝ) * G i b) / (Nat.lcm a b : ℝ)]
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun d' _ ↦ ?_
  rw [Finset.prod_div_distrib, ← Finset.prod_mul_distrib]

/-! ## The one-coordinate pair sum in terms of its own inner sums

The three definitions below are the quantities the algebra produces; the Gram-sum limits are
stated at the last of them. -/

/-- **The one-coordinate main-term pair sum**: the `i`-th factor of the main term of the
denominator divisor sum, over the divisors up to `B` that are coprime to the pre-sieving
modulus `W`. The coprimality is the restriction `Gap212.Sieve.coprime_of_forall_dvd` shows is
automatic on the tuples that contribute. -/
noncomputable def pairSumRecip (W B : ℕ) (x : ℝ) (F G : ℝ → ℝ) : ℝ :=
  ∑ d ∈ Icc 1 B with Nat.Coprime W d, ∑ d' ∈ Icc 1 B with Nat.Coprime W d',
    (μ d : ℝ) * F (Notation.logx x d) * ((μ d' : ℝ) * G (Notation.logx x d'))
      / (Nat.lcm d d' : ℝ)

/-- **The inner sum at modulus `eW`**, `∑_{f ≤ B/e, (f,eW)=1}μ(f)F(log_x(ef))/f`.

This is the `Z_F` of the fixed-modulus inner-sum asymptotic up to one difference that matters: the
profile is read at `log_x(ef)`, not at `log_x(eWf)`, and the truncation is at `B/e`, not at
`B/(eW)`. That is what the diagonalization produces, so that is what is written here;
`Gap212.Sieve.tendsto_logx_mul_innerSumReciprocal` is stated in the second shape. -/
noncomputable def innerRecip (W e : ℕ) (F : ℝ → ℝ) (x : ℝ) (B : ℕ) : ℝ :=
  ∑ f ∈ coprimeBelow (e * W) ((B : ℝ) / (e : ℝ)),
    (μ f : ℝ) * F (Notation.logx x (e * f)) / (f : ℝ)

/-- **The Gram sum**: the diagonalized form of the one-coordinate pair sum,
`∑_{e ≤ B, (e,W)=1}φ(e)(μ(e)/e)²·Z_F(e)·Z_G(e)`. -/
noncomputable def gramSumRecip (W B : ℕ) (x : ℝ) (F G : ℝ → ℝ) : ℝ :=
  ∑ e ∈ Icc 1 B with Nat.Coprime W e,
    lcmGramWeight e * (innerRecip W e F x B * innerRecip W e G x B)

/-- **The `f`-range of the inner sum is exactly the diagonalization's**:

  `coprimeBelow (eW) (B/e) = {f ≤ B/e : (e,f) = 1 ∧ (W,f) = 1}`,

the natural-number division on the right agreeing with the real one by `Nat.floor_div_eq_div`. At
`e = 0` both sides are empty, so no positivity is needed. -/
theorem coprimeBelow_mul_eq_filter (W e B : ℕ) :
    coprimeBelow (e * W) ((B : ℝ) / (e : ℝ))
      = {f ∈ Icc 1 (B / e) | Nat.Coprime e f ∧ Nat.Coprime W f} := by
  classical
  ext f
  simp only [coprimeBelow, Finset.mem_filter, Finset.mem_Icc, Nat.floor_div_eq_div,
    Nat.coprime_mul_iff_right]
  exact and_congr_right fun _ ↦ and_congr Nat.coprime_comm Nat.coprime_comm

/-- **The one-coordinate pair sum is the Gram sum.** This is the whole algebra of the main term in
one coordinate:

  `∑_{d,d'≤B, (dd',W)=1}μ(d)F(log_x d)μ(d')G(log_x d')/[d,d']
     = ∑_{e≤B, (e,W)=1}φ(e)(μ(e)/e)²·Z_F(e)·Z_G(e)`

with `Z_F(e) = ∑_{f≤B/e, (f,eW)=1}μ(f)F(log_x(ef))/f`.

The coprimality to `W` is carried through the weights, so
`Gap212.Sieve.sum_pair_div_lcm_eq_diagonal` applies unchanged; the `e` sharing a factor with `W`
then contribute nothing, because every multiple of such an `e` is dropped by the weight. -/
theorem pairSumRecip_eq_gramSum (W B : ℕ) (x : ℝ) (F G : ℝ → ℝ) :
    pairSumRecip W B x F G = gramSumRecip W B x F G := by
  classical
  -- The filters become weights.
  let K : (ℝ → ℝ) → ℕ → ℝ := fun H d ↦ if Nat.Coprime W d then H (Notation.logx x d) else 0
  have hpair : pairSumRecip W B x F G = ∑ d ∈ Icc 1 B, ∑ d' ∈ Icc 1 B,
      (μ d : ℝ) * K F d * ((μ d' : ℝ) * K G d') / (Nat.lcm d d' : ℝ) := by
    simp only [pairSumRecip, Finset.sum_filter, K]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    split_ifs <;> simp [ite_div]
  rw [hpair, sum_pair_moebius_div_lcm_eq_gram, gramSumRecip, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  -- The inner range is the one above, and the whole inner sum vanishes unless `(e,W) = 1`.
  have hY : ∀ H, ∑ f ∈ Icc 1 (B / e) with Nat.Coprime e f, (μ f : ℝ) * K H (e * f) / (f : ℝ)
      = if Nat.Coprime W e then innerRecip W e H x B else 0 := by
    intro H
    rw [innerRecip, coprimeBelow_mul_eq_filter, Finset.sum_filter, Finset.sum_filter]
    split_ifs with hWe
    · refine Finset.sum_congr rfl fun f _ ↦ ?_
      simp only [K, Nat.coprime_mul_iff_right, ite_and]
      split_ifs <;> push_cast <;> ring
    · exact Finset.sum_eq_zero fun f _ ↦ by simp [K, Nat.coprime_mul_iff_right, hWe]
  rw [hY, hY]
  split_ifs <;> simp

/-! ## The Gram-sum limit -/

/-- **The Gram-sum limit, without a support hypothesis.** For every admissible pair of profiles and
every truncation `B ≥ x^β`,

  `(φ(W)/W)·\log x·∑_{e ≤ B, (e,W)=1}φ(e)(μ(e)/e)²·Z_F(e)·Z_G(e) ⟶ ∫₀^∞F'G'`,

with `Z_F(e) = ∑_{f ≤ B/e, (f,eW)=1}μ(f)F(log_x(ef))/f` (`Gap212.Sieve.innerRecip`) and
`W = W(x)`.

The `k`-fold main term is the product over the coordinates of `Gap212.Sieve.pairSumRecip`
(`Gap212.Sieve.sum_pair_prod_moebius_div_prod_lcm_eq_prod`), each of which is the Gram sum above
(`Gap212.Sieve.pairSumRecip_eq_gramSum`), so this limit applied once per coordinate gives the main
term (`Gap212.Sieve.tendsto_prod_pairSumRecip`); the normalization `(φ(W)/W)\log x` is `B_x`.

The profile argument is `log_x(ef)` and the truncation `B/e`, as
`Gap212.Sieve.sum_moebius_div_filter_dvd` delivers — not `log_x(eWf)` and `B/(eW)`, the shape of
the fixed-modulus inner-sum asymptotic `Gap212.Sieve.tendsto_logx_mul_innerSumReciprocal`, which
gives `\log x·Z_F(q) → -F'(0)·q/φ(q)` at a **fixed** modulus `q`. Three things separate that from
this limit:

* the modulus is `eW(x)`, and `W(x) = primorial ⌊\log\log\log x⌋` tends to infinity, so the
  fixed-modulus hypothesis fails already at `e = 1`;
* `e` runs over the box, so `log_x e` does not tend to `0` — the retreat region confines
  `∑ᵢtᵢ < (1-ε₀)(A_j+ε)`, which lets `log_x e` sweep a fixed compact interval reaching about
  `0.265` at `p_⋆` — and `F'(0)` has to become `F'(log_x e)`;
* turning the `e`-sum into the integral needs
  `∑_{e≤y,(e,W)=1}μ²(e)/φ(e) ∼ (φ(W)/W)\log y` (`Gap212.Sieve.sum_moebiusSq_div_totient_coprime`).

As stated, this is false (`Gap212.Sieve.not_lcmGramSumLimit`); the form with the profiles vanishing
from `β` on is `Gap212.Sieve.LcmGramSumLimitOfSupport`.

This is the main term over the **full** coprime-to-`W` box; the sieve's main term is restricted to
tuples with pairwise coprime least common multiples, and that difference is the sieving error
`Gap212.Sieve.SelbergSievingError`. -/
def LcmGramSumLimit : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F → ContDiff ℝ 1 G → HasCompactSupport G →
    ∀ β : ℝ, 0 < β → ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
      Filter.Tendsto (fun x : ℝ ↦ ((W x).totient : ℝ) / (W x : ℝ) * Real.log x *
          gramSumRecip (W x) (B x) x F G) Filter.atTop
        (nhds (∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t))

/-! ## `Gap212.Sieve.LcmGramSumLimit` is false

`Gap212.Sieve.LcmGramSumLimit` quantifies over the profiles and over `B` **independently**: `F` and
`G` are any `C¹` functions with compact support, and `B` is any truncation with `x^β ≤ B(x)`, with
nothing tying the support of the profiles to `β`. Every term of the Gram sum reads the profiles at
`log_x(ef)` with `e ≤ B` and `f ≤ B/e`, hence at arguments in `[0, log_x B]` only, so the Gram sum
depends on `F` and `G` **only through their restriction to** `[0, log_x B]`, while the claimed limit
`∫₀^∞F'G'` sees all of them.

So take `β = 1`, `B(x) = ⌊x⌋ + 1` — which satisfies `x^β ≤ B(x)` for every `x` — and for `F = G` a
bump supported in `(2,4)`. For `x ≥ 2` one has `B(x) ≤ x²`, so every argument `log_x(ef)` is at
most `2` and every term of the Gram sum vanishes: the normalized Gram sum is identically `0` for
`x ≥ 2`, and its limit is `0`. But `∫₀^∞F'G' = ∫₀^∞(F')² > 0`, because `F` is not constant and its
derivative is supported in `[2,4] ⊆ (0,∞)`. That is `Gap212.Sieve.not_lcmGramSumLimit`.

The missing hypothesis is that the profiles vanish from `β` on, i.e. that the truncation reaches
past their support: `Gap212.Sieve.LcmGramSumLimitOfSupport` below, from which
`Gap212.Sieve.tendsto_prod_pairSumRecip_of_support` derives the main term.

The `e`-sum the passage to the integral needs is `∑_{e≤y,(e,W)=1}μ²(e)/φ(e) ∼ (φ(W)/W)\log y` and
not a sum against `g⋆` itself: the per-`e` heuristic `\log x·Y_F(e) ≈ -F'(\log_xe)·eW/φ(eW)`
contributes `g⋆(e)·(e/φ(e))²(W/φ(W))² = μ²(e)/φ(e)·(W/φ(W))²` per `e`. Its constant is exactly
`φ(W)/W` — the Euler factors at `p ∤ W` are `(1+1/(p-1))(1-1/p) = 1` — which is what makes the
normalization `(φ(W)/W)\log x` produce `∫F'G'` with no correction factor. The sum against
`μ²(e)φ(e)/e²` would instead carry `∏_{p∤W}(p²+p-1)(p-1)/p³ ≈ 0.4302`. -/

/-- The counterexample's bump: centred at `3` with `rOut = 1`, so `support = ball 3 1 = (2,4)` and
`tsupport = [2,4]`. Its support lies above `\log_xB = 1`. -/
noncomputable def gramCexBump : ContDiffBump (3 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The counterexample's profile: `Gap212.Sieve.gramCexBump` read as a function. -/
noncomputable def gramCexProfile : ℝ → ℝ := gramCexBump

/-- The counterexample's profile is smooth. -/
theorem gramCexProfile_contDiffTop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) gramCexProfile :=
  gramCexBump.contDiff

/-- The counterexample's profile is `C¹`. -/
theorem gramCexProfile_contDiff_one : ContDiff ℝ 1 gramCexProfile :=
  gramCexProfile_contDiffTop.of_le (by simp)

/-- The counterexample's profile has compact support. -/
theorem gramCexProfile_hasCompactSupport : HasCompactSupport gramCexProfile :=
  gramCexBump.hasCompactSupport

/-- The profile vanishes on `(-∞,2]`: its support is `(2,4)`. -/
theorem gramCexProfile_eq_zero_of_le_two {u : ℝ} (hu : u ≤ 2) : gramCexProfile u = 0 := by
  have h : (1 : ℝ) ≤ dist u (3 : ℝ) := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 3 - u)]
    linarith
  exact gramCexBump.zero_of_le_dist h

/-- The profile is `1` at the centre, so it is not the zero function. -/
theorem gramCexProfile_three : gramCexProfile 3 = 1 :=
  gramCexBump.one_of_mem_closedBall (by simp [Metric.mem_closedBall, gramCexBump])

/-- The topological support of the counterexample's profile is `closedBall 3 1 = [2,4]`. -/
theorem gramCexProfile_tsupport : tsupport gramCexProfile = Metric.closedBall (3 : ℝ) 1 :=
  gramCexBump.tsupport_eq

/-- **The inner sum vanishes when the truncation does not reach the profile's support.** If
`\log B ≤ c·\log x` and `F` vanishes on `(-∞,c]` then every term of `Gap212.Sieve.innerRecip` is
read at `\log_x(ef) ≤ \log_xB ≤ c`, where `F` is zero. -/
theorem innerRecip_eq_zero_of_profile_vanishing {x : ℝ} (hx : 1 < x) {B e W : ℕ} {c : ℝ}
    (hB : Real.log (B : ℝ) ≤ c * Real.log x) {F : ℝ → ℝ} (hF : ∀ u ≤ c, F u = 0) :
    innerRecip W e F x B = 0 := by
  refine Finset.sum_eq_zero fun f hf => ?_
  obtain ⟨hf0, hfle, -⟩ := mem_coprimeBelow.mp hf
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := mod_cast Nat.one_le_iff_ne_zero.mpr hf0
  have he : (0 : ℝ) < (e : ℝ) := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · simp [hf0] at hfle
    · exact_mod_cast h
  rw [le_div_iff₀ he] at hfle
  have hle : Notation.logx x ((e : ℝ) * (f : ℝ)) ≤ c := by
    rw [Notation.logx, div_le_iff₀ (Real.log_pos hx)]
    exact (Real.log_le_log (by positivity) (by linarith)).trans hB
  rw [hF _ hle, mul_zero, zero_div]

/-- **The Gram sum vanishes when the truncation does not reach the profile's support**: every
`e`-term carries the inner sum of `F` as a factor. -/
theorem gramSumRecip_eq_zero_of_profile_vanishing {x : ℝ} (hx : 1 < x) {B W : ℕ} {c : ℝ}
    (hB : Real.log (B : ℝ) ≤ c * Real.log x) {F G : ℝ → ℝ} (hF : ∀ u ≤ c, F u = 0) :
    gramSumRecip W B x F G = 0 := by
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [innerRecip_eq_zero_of_profile_vanishing hx hB hF, zero_mul, mul_zero]

/-- **The counterexample's target integral is positive.** `(F')²` is continuous, nonnegative and
integrable, its support is open, nonempty — `F` is not constant, so `F'` is somewhere nonzero — and
contained in `tsupport F = [2,4] ⊆ (0,∞)`, so the set integral over `(0,∞)` is positive. -/
theorem integral_deriv_gramCexProfile_sq_pos :
    0 < ∫ t in Set.Ioi (0 : ℝ), deriv gramCexProfile t * deriv gramCexProfile t := by
  have hcont : Continuous (deriv gramCexProfile) :=
    gramCexProfile_contDiff_one.continuous_deriv_one
  have hint : Integrable (fun t => deriv gramCexProfile t * deriv gramCexProfile t) :=
    (hcont.mul hcont).integrable_of_hasCompactSupport
      gramCexProfile_hasCompactSupport.deriv.mul_right
  rw [setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun t => mul_self_nonneg _) hint.integrableOn]
  have hsupp : Function.support (fun t => deriv gramCexProfile t * deriv gramCexProfile t)
      = Function.support (deriv gramCexProfile) := by
    ext t; simp [Function.mem_support]
  have hsub : Function.support (deriv gramCexProfile) ⊆ Set.Ioi (0 : ℝ) := fun t ht ↦ by
    have hts : t ∈ tsupport gramCexProfile := support_deriv_subset ht
    rw [gramCexProfile_tsupport, Metric.mem_closedBall, Real.dist_eq] at hts
    exact Set.mem_Ioi.mpr (by linarith [(abs_le.mp hts).1])
  rw [hsupp, Set.inter_eq_self_of_subset_left hsub]
  refine hcont.isOpen_support.measure_pos volume (Set.nonempty_iff_ne_empty.mpr fun hall ↦ ?_)
  have hconst := is_const_of_deriv_eq_zero (gramCexProfile_contDiff_one.differentiable
    (by norm_num)) (congrFun (Function.support_eq_empty_iff.mp hall))
  simpa [gramCexProfile_three, gramCexProfile_eq_zero_of_le_two] using hconst 3 0

/-- **`Gap212.Sieve.LcmGramSumLimit` is false.** At `β = 1`, `B(x) = ⌊x⌋+1` and
`F = G = Gap212.Sieve.gramCexProfile` (a bump supported in `(2,4)`), the normalized Gram sum is
identically `0` for `x ≥ 2` — every argument `\log_x(ef)` is at most `2`, since `ef ≤ B(x) ≤ x²` —
so it tends to `0`, while the asserted limit `∫₀^∞(F')²` is positive.

The profiles and `B` are quantified independently; see `Gap212.Sieve.LcmGramSumLimitOfSupport`
for the statement with the profiles vanishing from `β` on. -/
theorem not_lcmGramSumLimit : ¬ LcmGramSumLimit := by
  intro h
  have hBge : ∀ᶠ x : ℝ in atTop, x ^ (1 : ℝ) ≤ ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
    filter_upwards with x
    simpa using (Nat.lt_floor_add_one x).le
  have hlim := h gramCexProfile gramCexProfile gramCexProfile_contDiff_one
    gramCexProfile_hasCompactSupport gramCexProfile_contDiff_one
    gramCexProfile_hasCompactSupport 1 one_pos (fun x => ⌊x⌋₊ + 1) hBge
  have hzero : (fun x : ℝ ↦ ((W x).totient : ℝ) / (W x : ℝ) * Real.log x *
        gramSumRecip (W x) (⌊x⌋₊ + 1) x gramCexProfile gramCexProfile)
      =ᶠ[atTop] fun _ ↦ (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx1 : (1 : ℝ) < x := by linarith
    have hfl : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hB : Real.log (((⌊x⌋₊ + 1 : ℕ) : ℝ)) ≤ 2 * Real.log x :=
      (Real.log_le_log (by positivity) (by push_cast; nlinarith : _ ≤ x ^ 2)).trans_eq
        (by simp [Real.log_pow])
    rw [gramSumRecip_eq_zero_of_profile_vanishing hx1 hB
      (fun u hu => gramCexProfile_eq_zero_of_le_two hu), mul_zero]
  exact integral_deriv_gramCexProfile_sq_pos.ne
    (tendsto_nhds_unique (tendsto_const_nhds.congr' hzero.symm) hlim)

/-! ## The Gram-sum limit for profiles vanishing from `β` on -/

/-- **The Gram-sum limit for profiles vanishing from `β` on.** `Gap212.Sieve.LcmGramSumLimit` with
the hypothesis whose absence makes it false (`Gap212.Sieve.not_lcmGramSumLimit`): the profiles
vanish from `β` on, so the truncation `B ≥ x^β` reaches past their support and the Gram sum sees
all of `F` and `G`. Since `F` is `C¹` and vanishes on `[β,∞)`, `F'` vanishes there too, and the
target integral `∫₀^∞F'G'` is `∫₀^βF'G'`. The normalization is `B_x = (φ(W)/W)\log x`, and the
limit is `∫₀^∞F'G'` with no correction factor.

It holds: it is equivalent to `Gap212.Sieve.Polymath41Recip`
(`Gap212.Sieve.lcmGramSumLimitOfSupport_iff_polymath41Recip`), which `Gap212.Sieve.polymath41Recip`
proves.

The profiles are `C^∞`. This suffices for the application: the profiles at the end of the chain
`Gap212.Sieve.tendsto_prod_pairSumRecip_of_support` → `Gap212.Sieve.tendsto_boxPairSum` →
`Gap212.Sieve.selberg_progression_sum` → `Gap212.Sieve.nuDenominator_of_tensorDatum` are the
factors of a `Gap212.GPY.TensorDatum`, whose `smooth` field is `ContDiff ℝ (⊤ : ℕ∞)`. At `C^∞` the
Fourier transform of `t ↦ e^tF(t)` decays rapidly, so Mathlib's inversion theorem, which needs
`Integrable (𝓕 f)`, applies; for `F` only `C¹` it need not. This is also the regularity class of
Polymath8b's Lemma 4.1, `Gap212.Sieve.Polymath41Recip`.

The exponent is `(⊤ : ℕ∞)`, i.e. `C^∞`, and not `(⊤ : WithTop ℕ∞)`, which is analyticity: an
analytic function on `ℝ` with compact support is identically zero. -/
@[gap212 "lem_lcm_gram_sum_limit"]
def LcmGramSumLimitOfSupport : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → ContDiff ℝ (⊤ : ℕ∞) G →
    HasCompactSupport G →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) → (∀ t, β ≤ t → G t = 0) →
      ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
        Filter.Tendsto (fun x : ℝ ↦ ((W x).totient : ℝ) / (W x : ℝ) * Real.log x *
            gramSumRecip (W x) (B x) x F G) Filter.atTop
          (nhds (∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t))

/-- `Gap212.Sieve.LcmGramSumLimit` implies `Gap212.Sieve.LcmGramSumLimitOfSupport`, the latter
having two more hypotheses and its profiles narrowed from `C¹` to `C^∞`. -/
theorem lcmGramSumLimitOfSupport_of_lcmGramSumLimit (h : LcmGramSumLimit) :
    LcmGramSumLimitOfSupport :=
  fun F G hF hFc hG hGc β hβ _ _ B hB ↦
    h F G (hF.of_le (mod_cast le_top)) hFc (hG.of_le (mod_cast le_top)) hGc β hβ B hB

/-! ## The main term -/

/-- **The normalized `k`-fold box pair sum is the product of the normalized Gram sums.** The
coordinate separation (`Gap212.Sieve.sum_pair_prod_moebius_div_prod_lcm_eq_prod`) followed by
`Gap212.Sieve.pairSumRecip_eq_gramSum` in each coordinate, the `k`-th power of the normalization
being distributed over the `k` factors. This is the whole algebra of the main term; only the limit
of one factor remains. -/
theorem normalized_boxPairSum_eq_prod_gramSum (x : ℝ) (B : ℕ) {k : ℕ} (F G : Fin k → ℝ → ℝ) :
    (((W x).totient : ℝ) / (W x : ℝ) * Real.log x) ^ k *
        ∑ d ∈ Fintype.piFinset fun _ : Fin k ↦ {d ∈ Icc 1 B | Nat.Coprime (W x) d},
          ∑ d' ∈ Fintype.piFinset fun _ : Fin k ↦ {d ∈ Icc 1 B | Nat.Coprime (W x) d},
            (∏ i, (μ (d i) : ℝ) * F i (Notation.logx x (d i))) *
                (∏ i, (μ (d' i) : ℝ) * G i (Notation.logx x (d' i)))
              / ∏ i, (Nat.lcm (d i) (d' i) : ℝ)
      = ∏ i, (((W x).totient : ℝ) / (W x : ℝ) * Real.log x *
          gramSumRecip (W x) B x (F i) (G i)) := by
  classical
  rw [sum_pair_prod_moebius_div_prod_lcm_eq_prod
    (box := {d ∈ Icc 1 B | Nat.Coprime (W x) d})
    (F := fun i d ↦ F i (Notation.logx x d)) (G := fun i d ↦ G i (Notation.logx x d)),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine congrArg _ (Finset.prod_congr rfl fun i _ ↦ ?_)
  rw [← pairSumRecip_eq_gramSum, pairSumRecip]

/-- **The main term of the denominator divisor sum, granting `Gap212.Sieve.LcmGramSumLimit`.**
`Fᵢ, Gᵢ` of class `C¹` with compact support and a truncation `B ≥ x^β`,

  `B_x^k·∑_{d,d'}(∏ᵢμ(dᵢ)Fᵢ(log_x dᵢ))(∏ᵢμ(d'ᵢ)Gᵢ(log_x d'ᵢ))/∏ᵢ[dᵢ,d'ᵢ]
     ⟶ ∏ᵢ∫₀^∞F'ᵢG'ᵢ`,  `B_x = (φ(W)/W)\log x`,

the sum being over the pairs of tuples in the box of divisors coprime to `W(x)`. Together with the
error term `Gap212.Sieve.card_contributing_isLittleO_calC` and the counting of
`Gap212.Sieve.SelbergProgressionSum`, this is the evaluation of the denominator divisor sum, up to
the sieving error of dropping the pairwise-coprimality restriction on the tuples.

The proof is the coordinate separation followed by `Gap212.Sieve.pairSumRecip_eq_gramSum` in each
coordinate and one application of `Gap212.Sieve.LcmGramSumLimit` per coordinate, the `k`-th power
of the normalization being distributed over the `k` factors.

The hypothesis is false (`Gap212.Sieve.not_lcmGramSumLimit`);
`Gap212.Sieve.tendsto_prod_pairSumRecip_of_support` is the form with a satisfiable hypothesis. -/
theorem tendsto_prod_pairSumRecip (hlim : LcmGramSumLimit) {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ 1 (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    {β : ℝ} (hβ : 0 < β) (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Filter.Tendsto (fun x : ℝ ↦
        (((W x).totient : ℝ) / (W x : ℝ) * Real.log x) ^ k *
          ∑ d ∈ Fintype.piFinset fun _ : Fin k ↦ {d ∈ Icc 1 (B x) | Nat.Coprime (W x) d},
            ∑ d' ∈ Fintype.piFinset fun _ : Fin k ↦ {d ∈ Icc 1 (B x) | Nat.Coprime (W x) d},
              (∏ i, (μ (d i) : ℝ) * F i (Notation.logx x (d i))) *
                  (∏ i, (μ (d' i) : ℝ) * G i (Notation.logx x (d' i)))
                / ∏ i, (Nat.lcm (d i) (d' i) : ℝ))
      Filter.atTop
      (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) := by
  simp only [normalized_boxPairSum_eq_prod_gramSum]
  exact tendsto_finsetProd Finset.univ fun i _ ↦
    hlim (F i) (G i) (hF i) (hFc i) (hG i) (hGc i) β hβ B hB

/-- **The main term, granting `Gap212.Sieve.LcmGramSumLimitOfSupport`.** The same conclusion as
`Gap212.Sieve.tendsto_prod_pairSumRecip`, under the additional hypothesis that each profile
vanishes from `β` on, so the truncation `B ≥ x^β` reaches past its support. The retreat condition
on `∏ᵢFᵢ` confines each `tᵢ` to a fixed compact interval, and `Gap212.Sieve.SelbergAssembly`
applies this at `β = 1`. The profiles are `C^∞`, as in `Gap212.Sieve.LcmGramSumLimitOfSupport`. -/
theorem tendsto_prod_pairSumRecip_of_support (hlim : LcmGramSumLimitOfSupport) {k : ℕ}
    (F G : Fin k → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    {β : ℝ} (hβ : 0 < β) (hFβ : ∀ i, ∀ t, β ≤ t → F i t = 0)
    (hGβ : ∀ i, ∀ t, β ≤ t → G i t = 0)
    (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Filter.Tendsto (fun x : ℝ ↦
        (((W x).totient : ℝ) / (W x : ℝ) * Real.log x) ^ k *
          ∑ d ∈ Fintype.piFinset fun _ : Fin k ↦ {d ∈ Icc 1 (B x) | Nat.Coprime (W x) d},
            ∑ d' ∈ Fintype.piFinset fun _ : Fin k ↦ {d ∈ Icc 1 (B x) | Nat.Coprime (W x) d},
              (∏ i, (μ (d i) : ℝ) * F i (Notation.logx x (d i))) *
                  (∏ i, (μ (d' i) : ℝ) * G i (Notation.logx x (d' i)))
                / ∏ i, (Nat.lcm (d i) (d' i) : ℝ))
      Filter.atTop
      (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) := by
  simp only [normalized_boxPairSum_eq_prod_gramSum]
  exact tendsto_finsetProd Finset.univ fun i _ ↦
    hlim (F i) (G i) (hF i) (hFc i) (hG i) (hGc i) β hβ (hFβ i) (hGβ i) B hB

end Gap212.Sieve
