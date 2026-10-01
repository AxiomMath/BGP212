/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.AveragingFacts
public import Gap212.Sieve.DivisorSumDefs
public import Gap212.Sieve.SelbergDecoupling
public meta import Gap212.Attr

/-!
# The divisor-sum asymptotic over a support's moduli

For a support datum `p` with `A_j > ε`, a retreat `ε₀ ∈ (0,1)`, a
removed coordinate `i₀` and families `(Fᵢ)_{i≠i₀}`, `(Gᵢ)_{i≠i₀}` smooth, compactly supported and
`i₀`-retreated at `(j,j',ε₀)`,

  `∑_{d,d'}∏_{i≠i₀}μ(dᵢ)μ(d'ᵢ)Fᵢ(log_x dᵢ)Gᵢ(log_x d'ᵢ)/φ(W∏_{i≠i₀}[dᵢ,d'ᵢ])
     = (∏_{i≠i₀}∫₀^∞F'ᵢG'ᵢ + o(1))·W^{k-1}/(φ(W)^k(\log x)^{k-1})`,

the sum running over the tuples with `[dᵢ,d'ᵢ]` pairwise coprime and coprime to `W` whose modulus
lies in `Q⋆(p,x,ε₀/2)`. This file proves the three steps below; the asymptotic itself is
assembled from them in `Gap212.Sieve.DivisorSumAssembly` (`Gap212.Sieve.divisor_sum_over_qstar`),
with the sieving error `Gap212.Sieve.TotientSievingError` and the Gram-sum limit
`Gap212.Sieve.TotientGramSumLimitOfSupport` as hypotheses.

## Step one: the restriction to `Q⋆` removes no term

By `Gap212.Sieve.generated_modulus_mem_Qstar` every tuple with a non-zero numerator already has its
modulus in `Q⋆(p,x,ε₀/2)` for large `x` — the two clauses of `Gap212.GPY.IsReducedRetreat` are
exactly that lemma's hypotheses — so the restricted sum equals the unrestricted one
(`Gap212.Sieve.sum_filter_mem_Qstar_eq_sum`).

What is added to that lemma is that a non-zero numerator supplies its hypotheses: the Möbius
factors force every `dᵢ, d'ᵢ` to be positive (`μ(0) = 0`), and the products `∏ᵢFᵢ(log_x dᵢ)` and
`∏ᵢGᵢ(log_x d'ᵢ)` are then non-zero factors of it. Since only the numerator is read, the
restriction is removed from `∑ (numerator · c)` for an *arbitrary* weight `c`, which covers the
asymptotic's own summand `c = 1/φ(W∏ᵢ[dᵢ,d'ᵢ])`, the decoupled denominator
`c = 1/(φ(W)∏ᵢφ([dᵢ,d'ᵢ]))` step two produces. The statement is made for every finite family of
tuples, as in `Gap212.Sieve.weighted_error_negligible`.

## Step two: the algebra, to the Gram form

Unconditional, and assembled entirely from `Gap212.Sieve.SelbergDecoupling`:

* the denominator decouples, `φ(W∏ᵢ[dᵢ,d'ᵢ]) = φ(W)∏ᵢφ([dᵢ,d'ᵢ])`, on the tuples summed over
  (`Gap212.Sieve.sum_divisorNumerator_div_totient_decouple`);
* over a box the coordinates separate into a product of one-coordinate pair sums
  (`Gap212.Sieve.sum_divisorNumerator_div_prod_totient_eq_prod`);
* each one-coordinate pair sum is its Gram form `∑_e(μ*φ)(e)(μ(e)/φ(e))²Y_F(e)Y_G(e)`
  (`Gap212.Sieve.pairSumTotient_eq_gramSumTotient`), by the Selberg diagonalization and Möbius
  pull-out.

The decoupling is exact on the tuples whose least common multiples are pairwise coprime — which
is what the asymptotic sums over — while the separation needs a full box. The difference is the
sieving error `Gap212.Sieve.TotientSievingError` of `Gap212.Sieve.DivisorSumAssembly`, the analogue
of the reciprocal-weight sieving error of `Gap212.Sieve.SelbergMainTerm`.

## Step three: the outer `e`-sum

`Gap212.Sieve.tendsto_divisorSum_box_of_support` is the asymptotic over the box, in the
normalization `Gap212.Sieve.divisorSumNorm`, granting `Gap212.Sieve.TotientGramSumLimitOfSupport`:
that `(φ(W)/W)\log x` times the one-coordinate Gram sum tends to `∫₀^∞F'G'`, for profiles
vanishing from `β` on and truncations `B ≥ x^β`.

At a fixed `W` the normalized Gram sum carries the correction factor `∏_{p∤W}(1-1/(p-1)²)`; since
`W = W(x)` contains every prime below a bound tending to infinity, the factor tends to `1`
(`Gap212.Sieve.tendsto_tprod_corr_W`). `Gap212.Sieve.totientGramSumLimitOfSupport_iff` reduces the
Gram-sum limit to a Riemann sum against the weight `μ²(e)/(μ*φ)(e)`.

The variant `Gap212.Sieve.TotientGramSumLimit`, in which the profiles and the truncation are
quantified independently, is false (`Gap212.Sieve.not_totientGramSumLimit`);
`Gap212.Sieve.tendsto_divisorSum_box` and `Gap212.Sieve.tendsto_divisorSum_box_qstar` take it as
hypothesis.

## Main definitions

* `Gap212.Sieve.divisorNumerator`: the numerator,
  `∏_{i≠i₀}μ(dᵢ)Fᵢ(log_x dᵢ)μ(d'ᵢ)Gᵢ(log_x d'ᵢ)`.
* `Gap212.Sieve.pairSumTotient`, `innerTotient`, `gramSumTotient`: the one-coordinate pair sum, its
  inner sums and its Gram form.
* `Gap212.Sieve.divisorSumNorm`: `W^{k-1}/(φ(W)^k(\log x)^{k-1})`.
* `Gap212.Sieve.TotientGramSumLimitOfSupport`: the Gram-sum limit, for profiles vanishing from
  `β` on.
* `Gap212.Sieve.TotientGramSumLimit`: the same without the support hypothesis; it is false
  (`Gap212.Sieve.not_totientGramSumLimit`).

## Main results

* `Gap212.Sieve.mem_Qstar_of_divisorNumerator_ne_zero`: a non-zero numerator puts the generated
  modulus in `Q⋆`.
* `Gap212.Sieve.sum_filter_mem_Qstar_eq_sum`: the restriction to `Q⋆` removes no term.
* `Gap212.Sieve.sum_filter_mem_Qstar_div_totient_eq_sum`: the same at the asymptotic's own
  summand.
* `Gap212.Sieve.pairSumTotient_eq_gramSumTotient`: the Selberg diagonalization in one coordinate.
* `Gap212.Sieve.sum_divisorNumerator_div_totient_decouple`: the denominator decouples.
* `Gap212.Sieve.sum_divisorNumerator_div_prod_totient_eq_prod`: the coordinates separate over a
  box.
* `Gap212.Sieve.sum_divisorNumerator_div_totient_box_eq_prod_gramSum`: the box sum in Gram form.
* `Gap212.Sieve.tendsto_divisorSum_box_of_support`: the asymptotic over the box, from
  `TotientGramSumLimitOfSupport`.
* `Gap212.Sieve.tendsto_divisorSum_box`, `Gap212.Sieve.tendsto_divisorSum_box_qstar`: the
  asymptotic over the box, and over the moduli of the support, from the false
  `TotientGramSumLimit`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.Defs Gap212.GPY
open scoped ArithmeticFunction.Moebius

/-! ## The numerator -/

/-- **The numerator of the divisor sum**,
`∏_{i≠i₀}μ(dᵢ)Fᵢ(log_x dᵢ)·μ(d'ᵢ)Gᵢ(log_x d'ᵢ)`, at the `k - 1 = m` coordinates other than the
removed one, read on a pair of tuples. -/
noncomputable def divisorNumerator {m : ℕ} (x : ℝ) (F G : Fin m → ℝ → ℝ)
    (dd : (Fin m → ℕ) × (Fin m → ℕ)) : ℝ :=
  ∏ i, (μ (dd.1 i) : ℝ) * F i (Notation.logx x (dd.1 i)) *
    ((μ (dd.2 i) : ℝ) * G i (Notation.logx x (dd.2 i)))

/-! ## A non-zero numerator generates a modulus of the support -/

/-- **A tuple with a non-zero numerator has its modulus in `Q⋆`.** For a support datum `p` with
`ε < A_j`, a retreat `ε₀ ∈ (0,1)`, bands `j, j'`, a removed coordinate `i₀` and families
`(Fᵢ)_{i≠i₀}`, `(Gᵢ)_{i≠i₀}` that are `i₀`-retreated at `(j,j',ε₀)`, for all large `x` every pair
of tuples with `Gap212.Sieve.divisorNumerator ≠ 0` satisfies
`W(x)∏ᵢ[dᵢ,d'ᵢ] ∈ Q⋆(p,x,ε₀/2)`.

This is `Gap212.Sieve.generated_modulus_mem_Qstar` supplied with its hypotheses. A non-zero product
has non-zero factors, so `μ(dᵢ) ≠ 0` — whence `dᵢ ≠ 0`, since `μ(0) = 0` — and
`∏ᵢFᵢ(log_x dᵢ) ≠ 0`, `∏ᵢGᵢ(log_x d'ᵢ) ≠ 0`; the two clauses of
`Gap212.GPY.IsReducedRetreat` then give the retreat and marginal memberships that lemma asks for.
The logarithmic sizes are non-negative because `x > 1` and `dᵢ ≥ 1`. -/
theorem mem_Qstar_of_divisorNumerator_ne_zero (p : SupportParams) {m : ℕ} {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) (j j' : Fin p.n) (hA : p.ε < p.A j.succ)
    (i₀ : Fin (m + 1)) {F G : Fin m → ℝ → ℝ}
    (hsupp : IsReducedRetreat p m j j' ε₀ i₀ F G) :
    ∀ᶠ x : ℝ in atTop, ∀ dd : (Fin m → ℕ) × (Fin m → ℕ),
      divisorNumerator x F G dd ≠ 0 →
        W x * ∏ i, (dd.1 i).lcm (dd.2 i) ∈ Qstar p x (ε₀ / 2) := by
  filter_upwards [generated_modulus_mem_Qstar p m hε₀ hε₀' j j' hA i₀,
    eventually_gt_atTop (1 : ℝ)] with x hQ hx1 dd hne
  -- Every factor of the numerator is non-zero.
  rw [divisorNumerator] at hne
  have hfac : ∀ i : Fin m, (μ (dd.1 i) : ℝ) * F i (Notation.logx x (dd.1 i)) *
      ((μ (dd.2 i) : ℝ) * G i (Notation.logx x (dd.2 i))) ≠ 0 := fun i ↦
    Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i)
  have hd1 : ∀ i, 0 < dd.1 i := by
    intro i
    rcases Nat.eq_zero_or_pos (dd.1 i) with h | h
    · exact absurd (by simp [h]) (hfac i)
    · exact h
  have hd2 : ∀ i, 0 < dd.2 i := by
    intro i
    rcases Nat.eq_zero_or_pos (dd.2 i) with h | h
    · exact absurd (by simp [h]) (hfac i)
    · exact h
  -- The logarithmic sizes, in the two spellings.
  have hlogx : ∀ d : ℕ, Notation.logx x (d : ℝ) = Gap212.logScale x (d : ℝ) := fun _ ↦ rfl
  have hnn : ∀ (d : Fin m → ℕ), (∀ i, 0 < d i) → ∀ i, 0 ≤ Gap212.logScale x (d i) := by
    intro d hd i
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hd i)) (Real.log_nonneg hx1.le)
  -- The two profile products are non-zero factors of the numerator.
  have hnzF : (∏ i, F i (Gap212.logScale x (dd.1 i))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_
    rw [← hlogx]
    intro h
    exact hfac i (by rw [h]; ring)
  have hnzG : (∏ i, G i (Gap212.logScale x (dd.2 i))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_
    rw [← hlogx]
    intro h
    exact hfac i (by rw [h]; ring)
  obtain ⟨hret1, hmarg1⟩ := (hsupp _ (hnn dd.1 hd1)).1 hnzF
  exact hQ dd.1 dd.2 hd1 hd2 hret1 hmarg1 ((hsupp _ (hnn dd.2 hd2)).2 hnzG)

open Classical in
/-- **The restriction to `Q⋆` removes no term.** Under the hypotheses of
`Gap212.Sieve.mem_Qstar_of_divisorNumerator_ne_zero`, for all large `x`, every finite family `T` of
pairs of divisor tuples and every weight `c`,

  `∑_{dd ∈ T, W(x)∏ᵢ[dᵢ,d'ᵢ] ∈ Q⋆(p,x,ε₀/2)} N(dd)·c(dd) = ∑_{dd ∈ T} N(dd)·c(dd)`,

`N` being `Gap212.Sieve.divisorNumerator`: the sum over the moduli of the support equals the sum
over all tuples. The weight `c` is arbitrary because the argument reads only the numerator. -/
theorem sum_filter_mem_Qstar_eq_sum (p : SupportParams) {m : ℕ} {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) (j j' : Fin p.n) (hA : p.ε < p.A j.succ)
    (i₀ : Fin (m + 1)) {F G : Fin m → ℝ → ℝ}
    (hsupp : IsReducedRetreat p m j j' ε₀ i₀ F G) :
    ∀ᶠ x : ℝ in atTop, ∀ (T : Finset ((Fin m → ℕ) × (Fin m → ℕ)))
      (c : (Fin m → ℕ) × (Fin m → ℕ) → ℝ),
      ∑ dd ∈ T with W x * ∏ i, (dd.1 i).lcm (dd.2 i) ∈ Qstar p x (ε₀ / 2),
          divisorNumerator x F G dd * c dd
        = ∑ dd ∈ T, divisorNumerator x F G dd * c dd := by
  filter_upwards [mem_Qstar_of_divisorNumerator_ne_zero p hε₀ hε₀' j j' hA i₀ hsupp]
    with x hx T c
  exact Finset.sum_filter_of_ne fun dd _ hne ↦ hx dd (left_ne_zero_of_mul hne)

open Classical in
/-- **The restriction to `Q⋆` removes no term, at the asymptotic's own summand.**

  `∑_{dd ∈ T, W(x)∏ᵢ[dᵢ,d'ᵢ] ∈ Q⋆} N(dd)/φ(W(x)∏ᵢ[dᵢ,d'ᵢ]) = ∑_{dd ∈ T} N(dd)/φ(W(x)∏ᵢ[dᵢ,d'ᵢ])`.

`Gap212.Sieve.sum_filter_mem_Qstar_eq_sum` at `c(dd) = φ(W(x)∏ᵢ[dᵢ,d'ᵢ])⁻¹`. -/
theorem sum_filter_mem_Qstar_div_totient_eq_sum (p : SupportParams) {m : ℕ} {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) (j j' : Fin p.n) (hA : p.ε < p.A j.succ)
    (i₀ : Fin (m + 1)) {F G : Fin m → ℝ → ℝ}
    (hsupp : IsReducedRetreat p m j j' ε₀ i₀ F G) :
    ∀ᶠ x : ℝ in atTop, ∀ T : Finset ((Fin m → ℕ) × (Fin m → ℕ)),
      ∑ dd ∈ T with W x * ∏ i, (dd.1 i).lcm (dd.2 i) ∈ Qstar p x (ε₀ / 2),
          divisorNumerator x F G dd /
            (Nat.totient (W x * ∏ i, (dd.1 i).lcm (dd.2 i)) : ℝ)
        = ∑ dd ∈ T, divisorNumerator x F G dd /
            (Nat.totient (W x * ∏ i, (dd.1 i).lcm (dd.2 i)) : ℝ) := by
  filter_upwards [sum_filter_mem_Qstar_eq_sum p hε₀ hε₀' j j' hA i₀ hsupp] with x hx T
  simpa only [div_eq_mul_inv] using
    hx T fun dd ↦ ((Nat.totient (W x * ∏ i, (dd.1 i).lcm (dd.2 i)) : ℝ))⁻¹

/-! ## The one-coordinate pair sum and its Gram form -/

/-- **The one-coordinate pair sum**,
`∑_{d,d'≤B, (dd',W)=1}μ(d)F(log_x d)μ(d')G(log_x d')/φ([d,d'])`: the `i`-th factor the decoupled
divisor sum separates into. The coprimality to `W` is the restriction the tuples carry
automatically. -/
noncomputable def pairSumTotient (W B : ℕ) (x : ℝ) (F G : ℝ → ℝ) : ℝ :=
  ∑ d ∈ Icc 1 B with Nat.Coprime W d, ∑ d' ∈ Icc 1 B with Nat.Coprime W d',
    (μ d : ℝ) * F (Notation.logx x d) * ((μ d' : ℝ) * G (Notation.logx x d'))
      / (Nat.totient (Nat.lcm d d') : ℝ)

/-- **The inner sum at modulus `eW`**, `∑_{f ≤ B/e, (f,e)=1, (f,W)=1}μ(f)F(log_x(ef))/φ(f)`.

This is the `Y_F` of the inner-sum asymptotic up to two differences that the diagonalization
produces: the profile is read at `log_x(ef)` rather than at `log_x(eWf)`, and the coprimality is to
`eW` while the truncation is at `B/e` rather than at `B/(eW)`. The index range is
`Gap212.Sieve.coprimeBelow (e*W) (B/e)` (the natural-number division agreeing with the real one by
`Nat.floor_div_eq_div`), written out here as a filter. -/
noncomputable def innerTotient (W e : ℕ) (F : ℝ → ℝ) (x : ℝ) (B : ℕ) : ℝ :=
  ∑ f ∈ Icc 1 (B / e) with Nat.Coprime e f ∧ Nat.Coprime W f,
    (μ f : ℝ) * F (Notation.logx x (e * f)) / (Nat.totient f : ℝ)

/-- **The Gram sum**: the diagonalized one-coordinate pair sum,
`∑_{e≤B, (e,W)=1}(μ*φ)(e)(μ(e)/φ(e))²·Y_F(e)·Y_G(e)`, against the weight
`Gap212.Sieve.gramWeight`. -/
noncomputable def gramSumTotient (W B : ℕ) (x : ℝ) (F G : ℝ → ℝ) : ℝ :=
  ∑ e ∈ Icc 1 B with Nat.Coprime W e,
    gramWeight e * (innerTotient W e F x B * innerTotient W e G x B)

/-- **The one-coordinate pair sum is the Gram sum.** The Selberg diagonalization of the kernel,
carried out at the coprimality to `W` the sum is restricted by:

  `∑_{d,d'≤B, (dd',W)=1}μ(d)F(log_x d)μ(d')G(log_x d')/φ([d,d'])
     = ∑_{e≤B, (e,W)=1}(μ*φ)(e)(μ(e)/φ(e))²·Y_F(e)·Y_G(e)`.

`Gap212.Sieve.sum_pair_div_totient_lcm_eq_diagonal` makes the kernel
diagonal and `Gap212.Sieve.sum_moebius_div_totient_filter_dvd` pulls `μ(e)/φ(e)` out of each
diagonal sum. The coprimality to `W` is carried through the numerator weights, so the
diagonalization applies unchanged; the `e` sharing a factor with `W` then contribute nothing, every
multiple of such an `e` being dropped by the weight. -/
theorem pairSumTotient_eq_gramSumTotient (W B : ℕ) (x : ℝ) (F G : ℝ → ℝ) :
    pairSumTotient W B x F G = gramSumTotient W B x F G := by
  classical
  set Hu : ℕ → ℝ := fun d ↦ if Nat.Coprime W d then F (Notation.logx x d) else 0 with hHu
  set Hv : ℕ → ℝ := fun d ↦ if Nat.Coprime W d then G (Notation.logx x d) else 0 with hHv
  set u : ℕ → ℝ := fun d ↦ (μ d : ℝ) * Hu d with hu
  set v : ℕ → ℝ := fun d ↦ (μ d : ℝ) * Hv d with hv
  -- The two filters become weights.
  have hterm : ∀ d d' : ℕ,
      (if Nat.Coprime W d then (if Nat.Coprime W d' then
          (μ d : ℝ) * F (Notation.logx x d) * ((μ d' : ℝ) * G (Notation.logx x d'))
            / (Nat.totient (Nat.lcm d d') : ℝ) else 0) else 0)
        = u d * v d' / (Nat.totient (Nat.lcm d d') : ℝ) := by
    intro d d'
    simp only [hu, hv, hHu, hHv]
    by_cases h1 : Nat.Coprime W d
    · by_cases h2 : Nat.Coprime W d'
      · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]
      · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]; ring
    · rw [if_neg h1, if_neg h1]; ring
  have hpair : pairSumTotient W B x F G
      = ∑ d ∈ Icc 1 B, ∑ d' ∈ Icc 1 B, u d * v d' / (Nat.totient (Nat.lcm d d') : ℝ) := by
    rw [pairSumTotient, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    by_cases h1 : Nat.Coprime W d
    · rw [if_pos h1, Finset.sum_filter]
      exact Finset.sum_congr rfl fun d' _ ↦ by rw [← hterm d d', if_pos h1]
    · rw [if_neg h1]
      refine (Finset.sum_eq_zero fun d' _ ↦ ?_).symm
      rw [← hterm d d', if_neg h1]
  rw [hpair, sum_pair_div_totient_lcm_eq_diagonal B u v, gramSumTotient, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  have he0 : 0 < e := (Finset.mem_Icc.mp he).1
  by_cases hWe : Nat.Coprime W e
  · -- The Möbius pull-out, and the inner range is the one `innerTotient` is written at.
    have hrange : ∀ (H : ℝ → ℝ) (K : ℕ → ℝ),
        (∀ d, K d = if Nat.Coprime W d then H (Notation.logx x d) else 0) →
        (∑ f ∈ Icc 1 (B / e) with Nat.Coprime e f, (μ f : ℝ) * K (e * f) / (Nat.totient f : ℝ))
          = innerTotient W e H x B := by
      intro H K hK
      rw [innerTotient, Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun f _ ↦ ?_
      by_cases hef : Nat.Coprime e f
      · by_cases hWf : Nat.Coprime W f
        · have hcop : Nat.Coprime W (e * f) := Nat.Coprime.mul_right hWe hWf
          rw [if_pos hef, if_pos ⟨hef, hWf⟩, hK (e * f), if_pos hcop]
          push_cast
          ring
        · have hcop : ¬ Nat.Coprime W (e * f) := fun h ↦
            hWf (Nat.Coprime.coprime_dvd_right (dvd_mul_left f e) h)
          rw [if_pos hef, if_neg (fun h : Nat.Coprime e f ∧ Nat.Coprime W f ↦ hWf h.2),
            hK (e * f), if_neg hcop]
          ring
      · rw [if_neg hef, if_neg (fun h : Nat.Coprime e f ∧ Nat.Coprime W f ↦ hef h.1)]
    have hinner : ∀ (H : ℝ → ℝ) (K : ℕ → ℝ),
        (∀ d, K d = if Nat.Coprime W d then H (Notation.logx x d) else 0) →
        ∑ d ∈ Icc 1 B with e ∣ d, (μ d : ℝ) * K d / (Nat.totient d : ℝ)
          = (μ e : ℝ) / (Nat.totient e : ℝ) * innerTotient W e H x B := fun H K hK ↦ by
      rw [sum_moebius_div_totient_filter_dvd B he0 K, hrange H K hK]
    rw [if_pos hWe, hinner F Hu (fun d ↦ by rw [hHu]), hinner G Hv (fun d ↦ by rw [hHv]),
      gramWeight]
    ring
  · -- Every multiple of `e` is dropped by the weight, so the `e`-th term vanishes.
    have hzero : (∑ d ∈ Icc 1 B with e ∣ d, u d / (Nat.totient d : ℝ)) = 0 := by
      refine Finset.sum_eq_zero fun d hd ↦ ?_
      have hdvd : e ∣ d := (Finset.mem_filter.mp hd).2
      have hnc : ¬ Nat.Coprime W d := fun h ↦ hWe (Nat.Coprime.coprime_dvd_right hdvd h)
      simp [hu, hHu, hnc]
    rw [if_neg hWe, hzero]
    ring

/-! ## The denominator decouples, and the coordinates separate -/

/-- **The denominator decouples on a pairwise coprime family.** Over any finite family `T` of pairs
of tuples whose least common multiples are positive, pairwise coprime and coprime to `W`,

  `∑_{T}N(d,d')/φ(W∏ᵢ[dᵢ,d'ᵢ])
     = φ(W)⁻¹∑_{T}∏ᵢμ(dᵢ)Fᵢ(log_x dᵢ)μ(d'ᵢ)Gᵢ(log_x d'ᵢ)/φ([dᵢ,d'ᵢ])`,

`N` being `Gap212.Sieve.divisorNumerator`. This is `Gap212.Sieve.sum_div_totient_decouple` at the
numerator above, and it is exact: the factor `W^{k-1}/φ(W)^k` is this `φ(W)⁻¹` together with one
`(φ(W)/W)\log x` per remaining coordinate. -/
theorem sum_divisorNumerator_div_totient_decouple {m : ℕ} (x : ℝ) (F G : Fin m → ℝ → ℝ) {W : ℕ}
    (T : Finset ((Fin m → ℕ) × (Fin m → ℕ)))
    (hT : ∀ dd ∈ T, (∀ i, 0 < (dd.1 i).lcm (dd.2 i)) ∧
      (∀ i, Nat.Coprime W ((dd.1 i).lcm (dd.2 i))) ∧
      (∀ i i', i ≠ i' → Nat.Coprime ((dd.1 i).lcm (dd.2 i)) ((dd.1 i').lcm (dd.2 i')))) :
    ∑ dd ∈ T, divisorNumerator x F G dd /
        (Nat.totient (W * ∏ i, (dd.1 i).lcm (dd.2 i)) : ℝ)
      = 1 / (Nat.totient W : ℝ) * ∑ dd ∈ T, ∏ i,
          ((μ (dd.1 i) : ℝ) * F i (Notation.logx x (dd.1 i)) *
              ((μ (dd.2 i) : ℝ) * G i (Notation.logx x (dd.2 i)))
            / (Nat.totient ((dd.1 i).lcm (dd.2 i)) : ℝ)) :=
  sum_div_totient_decouple T
    (fun dd i ↦ (μ (dd.1 i) : ℝ) * F i (Notation.logx x (dd.1 i)) *
      ((μ (dd.2 i) : ℝ) * G i (Notation.logx x (dd.2 i)))) hT

/-- **The coordinates separate over a box.** With the denominator already decoupled, the `k-1`-fold
sum over a full box of tuples coprime to `W` is the product over the coordinates of
`Gap212.Sieve.pairSumTotient`.

This is `Gap212.Sieve.sum_pair_prod_eq_prod`. The asymptotic's sum runs over the tuples whose least
common multiples are pairwise coprime; the difference between those and the full box is the
sieving error `Gap212.Sieve.TotientSievingError`, proved as `Gap212.Sieve.totientSievingError`. -/
theorem sum_divisorNumerator_div_prod_totient_eq_prod {m : ℕ} (W B : ℕ) (x : ℝ)
    (F G : Fin m → ℝ → ℝ) :
    ∑ d ∈ Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 B | Nat.Coprime W d},
        ∑ d' ∈ Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 B | Nat.Coprime W d},
          divisorNumerator x F G (d, d') / ∏ i, (Nat.totient ((d i).lcm (d' i)) : ℝ)
      = ∏ i, pairSumTotient W B x (F i) (G i) := by
  simp only [pairSumTotient]
  rw [← sum_pair_prod_eq_prod (box := {d ∈ Icc 1 B | Nat.Coprime W d})
    (f := fun i a b ↦ (μ a : ℝ) * F i (Notation.logx x a) * ((μ b : ℝ) * G i (Notation.logx x b))
      / (Nat.totient (Nat.lcm a b) : ℝ))]
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun d' _ ↦ ?_
  simp only [divisorNumerator]
  rw [Finset.prod_div_distrib]

/-- **The box sum in Gram form.** Over the box of divisors coprime to `W`, at the decoupled
denominator `φ(W)∏ᵢφ([dᵢ,d'ᵢ])`,

  `∑_{d,d'}N(d,d')/(φ(W)∏ᵢφ([dᵢ,d'ᵢ])) = φ(W)⁻¹∏ᵢ∑_{e}(μ*φ)(e)(μ(e)/φ(e))²Y_{Fᵢ}(e)Y_{Gᵢ}(e)`.

The two previous results composed: the coordinates separate and each factor is its Gram sum. -/
theorem sum_divisorNumerator_div_totient_box_eq_prod_gramSum {m : ℕ} (W B : ℕ) (x : ℝ)
    (F G : Fin m → ℝ → ℝ) :
    ∑ d ∈ Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 B | Nat.Coprime W d},
        ∑ d' ∈ Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 B | Nat.Coprime W d},
          divisorNumerator x F G (d, d') /
            ((Nat.totient W : ℝ) * ∏ i, (Nat.totient ((d i).lcm (d' i)) : ℝ))
      = 1 / (Nat.totient W : ℝ) * ∏ i, gramSumTotient W B x (F i) (G i) := by
  have hswap : ∀ d d' : Fin m → ℕ,
      divisorNumerator x F G (d, d') /
          ((Nat.totient W : ℝ) * ∏ i, (Nat.totient ((d i).lcm (d' i)) : ℝ))
        = (divisorNumerator x F G (d, d') / ∏ i, (Nat.totient ((d i).lcm (d' i)) : ℝ))
            / (Nat.totient W : ℝ) := fun d d' ↦ div_mul_eq_div_div_swap _ _ _
  rw [Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun d' _ ↦ hswap d d',
    Finset.sum_congr rfl fun d _ ↦ (Finset.sum_div _ _ _).symm, ← Finset.sum_div,
    sum_divisorNumerator_div_prod_totient_eq_prod, div_eq_inv_mul, ← one_div]
  exact congrArg _ (Finset.prod_congr rfl fun i _ ↦ pairSumTotient_eq_gramSumTotient W B x _ _)

/-! ## The normalization -/

/-- **The normalization** `W^{k-1}/(φ(W)^k(\log x)^{k-1})`, written at `k - 1 = m` so that
the exponent is the literal number of remaining coordinates. It is `φ(W)⁻¹B_x^{-m}` with
`B_x = (φ(W)/W)\log x`: one `φ(W)` is the modulus's own, and each remaining coordinate contributes
one `B_x`. -/
noncomputable def divisorSumNorm (m : ℕ) (x : ℝ) : ℝ :=
  (W x : ℝ) ^ m / (((W x).totient : ℝ) ^ (m + 1) * Real.log x ^ m)

/-! ## The Gram-sum limit -/

/-- **The Gram-sum limit without a support hypothesis.** For every pair of `C¹` compactly
supported profiles and every truncation `B ≥ x^β`,

  `(φ(W)/W)·\log x·∑_{e ≤ B, (e,W)=1}(μ*φ)(e)(μ(e)/φ(e))²·Y_F(e)·Y_G(e) ⟶ ∫₀^∞F'G'`,

with `Y_F(e) = ∑_{f ≤ B/e, (f,e)=1, (f,W)=1}μ(f)F(log_x(ef))/φ(f)`
(`Gap212.Sieve.innerTotient`), the `e`-sum being `Gap212.Sieve.gramSumTotient` and `W = W(x)`.

This statement is false (`Gap212.Sieve.not_totientGramSumLimit`): the Gram sum reads the profiles
only on `[0, log_x B]`. `Gap212.Sieve.TotientGramSumLimitOfSupport` adds the support hypothesis. -/
def TotientGramSumLimit : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F → ContDiff ℝ 1 G → HasCompactSupport G →
    ∀ β : ℝ, 0 < β → ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
      Tendsto (fun x : ℝ ↦ ((W x).totient : ℝ) / (W x : ℝ) * Real.log x *
          gramSumTotient (W x) (B x) x F G) atTop
        (nhds (∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t))

/-- **The totient Gram-sum limit.** For `C^∞` compactly supported profiles `F, G` vanishing from
`β > 0` on, and every truncation `B ≥ x^β`,

  `(φ(W)/W)·\log x·∑_{e ≤ B, (e,W)=1}(μ*φ)(e)(μ(e)/φ(e))²·Y_F(e)·Y_G(e) ⟶ ∫₀^∞F'G'`,

with `Y_F(e) = ∑_{f ≤ B/e, (f,e)=1, (f,W)=1}μ(f)F(log_x(ef))/φ(f)` (`Gap212.Sieve.innerTotient`)
and `W = W(x)`.

The `k-1`-fold sum of `Gap212.Sieve.divisor_sum_over_qstar` is `φ(W)⁻¹` times a product over the
remaining coordinates of `Gap212.Sieve.pairSumTotient`, each of which is the Gram sum above
(`Gap212.Sieve.pairSumTotient_eq_gramSumTotient`); this limit, once per coordinate, gives the
asymptotic, the normalization being `φ(W)⁻¹B_x^{-(k-1)}` with `B_x = (φ(W)/W)\log x`.

The support hypothesis puts the whole profile inside the window `[0, log_x B]` that the Gram sum
reads, since `B ≥ x^β`; without it the limit is false (`Gap212.Sieve.TotientGramSumLimit`,
`Gap212.Sieve.not_totientGramSumLimit`). At a fixed `W` the normalized sum would tend to
`∏_{p ∤ W}(1 - 1/(p-1)²)·∫₀^∞F'G'`; the limit holds because `W(x)` grows
(`Gap212.Sieve.tendsto_tprod_corr_W`).

Equivalent forms: a Riemann sum against the weight `μ²(e)/(μ*φ)(e)`, with the inner sums
normalized by `Gap212.Sieve.innerTotientRatio` (`Gap212.Sieve.totientGramSumLimitOfSupport_iff`);
the vanishing of the weighted average defect `Gap212.Sieve.TotientGramRatioDefectVanishes`
(`Gap212.Sieve.totientGramSumLimitOfSupport_iff_totientGramRatioDefectVanishes`); and
`Gap212.Sieve.Polymath41Totient`, Lemma 4.1 of Polymath8b
(`Gap212.Sieve.totientGramSumLimitOfSupport_iff_polymath41Totient`), which
`Gap212.Sieve.polymath41Totient` proves.

The profiles are `C^∞`, with exponent `(⊤ : ℕ∞)`; at this regularity their Fourier transforms are
integrable. (In `WithTop ℕ∞`, `⊤` is analyticity, and an analytic function on `ℝ` with compact
support vanishes.) -/
@[gap212 "lem_totient_gram_sum_limit"]
def TotientGramSumLimitOfSupport : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → ContDiff ℝ (⊤ : ℕ∞) G →
    HasCompactSupport G →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) → (∀ t, β ≤ t → G t = 0) →
      ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
        Tendsto (fun x : ℝ ↦ ((W x).totient : ℝ) / (W x : ℝ) * Real.log x *
            gramSumTotient (W x) (B x) x F G) atTop
          (nhds (∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t))

/-- `Gap212.Sieve.TotientGramSumLimit` implies `Gap212.Sieve.TotientGramSumLimitOfSupport`, which
adds two hypotheses and restricts the profiles from `C¹` to `C^∞`. -/
theorem totientGramSumLimitOfSupport_of_totientGramSumLimit (h : TotientGramSumLimit) :
    TotientGramSumLimitOfSupport :=
  fun F G hF hFc hG hGc β hβ _ _ B hB ↦
    h F G (hF.of_le (by exact_mod_cast le_top)) hFc (hG.of_le (by exact_mod_cast le_top)) hGc β hβ
      B hB

/-! ## The box asymptotic -/

/-- **The divisor-sum asymptotic over the box, from `Gap212.Sieve.TotientGramSumLimit`.** For
profiles `Fᵢ, Gᵢ` of class `C¹` with compact support and a truncation `B ≥ x^β`,

  `∑_{d,d'}N(d,d')/(φ(W)∏ᵢφ([dᵢ,d'ᵢ])) / (W^{k-1}/(φ(W)^k(\log x)^{k-1})) ⟶ ∏ᵢ∫₀^∞F'ᵢG'ᵢ`,

the sum running over the pairs of tuples in the box of divisors up to `B` coprime to `W(x)`.

The hypothesis is false (`Gap212.Sieve.not_totientGramSumLimit`);
`Gap212.Sieve.tendsto_divisorSum_box_of_support` is the same conclusion from
`Gap212.Sieve.TotientGramSumLimitOfSupport`. -/
theorem tendsto_divisorSum_box (hlim : TotientGramSumLimit) {m : ℕ} (F G : Fin m → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ 1 (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    {β : ℝ} (hβ : 0 < β) (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦
        (∑ d ∈ Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 (B x) | Nat.Coprime (W x) d},
            ∑ d' ∈ Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 (B x) | Nat.Coprime (W x) d},
              divisorNumerator x F G (d, d') /
                (((W x).totient : ℝ) * ∏ i, (Nat.totient ((d i).lcm (d' i)) : ℝ)))
          / divisorSumNorm m x)
      atTop (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) := by
  have hprod : Tendsto (fun x : ℝ ↦ ∏ i, (((W x).totient : ℝ) / (W x : ℝ) * Real.log x *
      gramSumTotient (W x) (B x) x (F i) (G i))) atTop
      (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) :=
    tendsto_finsetProd Finset.univ fun i _ ↦
      hlim (F i) (G i) (hF i) (hFc i) (hG i) (hGc i) β hβ B hB
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx1
  have hWpos : 0 < W x := primorial_pos _
  have ha : (0 : ℝ) < ((W x).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hWpos
  have hw : (0 : ℝ) < (W x : ℝ) := by exact_mod_cast hWpos
  rw [sum_divisorNumerator_div_totient_box_eq_prod_gramSum, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  set P : ℝ := ∏ i, gramSumTotient (W x) (B x) x (F i) (G i) with hP
  rw [divisorSumNorm, div_div_eq_mul_div, pow_succ]
  rw [mul_pow, div_pow]
  field_simp

/-- **The divisor-sum asymptotic over the box.** For `C^∞` compactly supported profiles
`Fᵢ, Gᵢ` vanishing from `β` on and a truncation `B ≥ x^β`, granting
`Gap212.Sieve.TotientGramSumLimitOfSupport`,

  `∑_{d,d'}N(d,d')/(φ(W)∏ᵢφ([dᵢ,d'ᵢ])) / (W^{k-1}/(φ(W)^k(\log x)^{k-1})) ⟶ ∏ᵢ∫₀^∞F'ᵢG'ᵢ`,

the sum running over the pairs of tuples in the box of divisors up to `B` coprime to `W(x)`.
This is the totient-kernel companion of `Gap212.Sieve.tendsto_prod_pairSumRecip_of_support`. -/
theorem tendsto_divisorSum_box_of_support (hlim : TotientGramSumLimitOfSupport) {m : ℕ}
    (F G : Fin m → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    {β : ℝ} (hβ : 0 < β) (hFβ : ∀ i, ∀ t, β ≤ t → F i t = 0)
    (hGβ : ∀ i, ∀ t, β ≤ t → G i t = 0)
    (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦
        (∑ d ∈ Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 (B x) | Nat.Coprime (W x) d},
            ∑ d' ∈ Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 (B x) | Nat.Coprime (W x) d},
              divisorNumerator x F G (d, d') /
                (((W x).totient : ℝ) * ∏ i, (Nat.totient ((d i).lcm (d' i)) : ℝ)))
          / divisorSumNorm m x)
      atTop (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) := by
  have hprod : Tendsto (fun x : ℝ ↦ ∏ i, (((W x).totient : ℝ) / (W x : ℝ) * Real.log x *
      gramSumTotient (W x) (B x) x (F i) (G i))) atTop
      (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) :=
    tendsto_finsetProd Finset.univ fun i _ ↦
      hlim (F i) (G i) (hF i) (hFc i) (hG i) (hGc i) β hβ (hFβ i) (hGβ i) B hB
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx1
  have hWpos : 0 < W x := primorial_pos _
  have ha : (0 : ℝ) < ((W x).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hWpos
  have hw : (0 : ℝ) < (W x : ℝ) := by exact_mod_cast hWpos
  rw [sum_divisorNumerator_div_totient_box_eq_prod_gramSum, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  set P : ℝ := ∏ i, gramSumTotient (W x) (B x) x (F i) (G i) with hP
  rw [divisorSumNorm, div_div_eq_mul_div, pow_succ]
  rw [mul_pow, div_pow]
  field_simp

open Classical in
/-- **The divisor-sum asymptotic over the moduli of the support, from
`Gap212.Sieve.TotientGramSumLimit`.** The limit of `Gap212.Sieve.tendsto_divisorSum_box`, with the
sum restricted to the tuples whose modulus lies in `Q⋆(p,x,ε₀/2)`; by
`Gap212.Sieve.sum_filter_mem_Qstar_eq_sum` the restriction removes no non-zero term once `x` is
large.

The hypothesis is false (`Gap212.Sieve.not_totientGramSumLimit`). The asymptotic
`Gap212.Sieve.divisor_sum_over_qstar` restricts to `Q⋆` after subtracting the sieving error, in
`Gap212.Sieve.sievedDivisorSum_eq_qstarSum`. -/
theorem tendsto_divisorSum_box_qstar (hlim : TotientGramSumLimit) (p : SupportParams) {m : ℕ}
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) (j j' : Fin p.n) (hA : p.ε < p.A j.succ)
    (i₀ : Fin (m + 1)) {F G : Fin m → ℝ → ℝ}
    (hsupp : IsReducedRetreat p m j j' ε₀ i₀ F G)
    (hF : ∀ i, ContDiff ℝ 1 (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ 1 (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    {β : ℝ} (hβ : 0 < β) (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦
        (∑ dd ∈ (Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 (B x) | Nat.Coprime (W x) d}) ×ˢ
              Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 (B x) | Nat.Coprime (W x) d}
            with W x * ∏ i, (dd.1 i).lcm (dd.2 i) ∈ Qstar p x (ε₀ / 2),
          divisorNumerator x F G dd /
            (((W x).totient : ℝ) * ∏ i, (Nat.totient ((dd.1 i).lcm (dd.2 i)) : ℝ)))
          / divisorSumNorm m x)
      atTop (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) := by
  refine (tendsto_divisorSum_box hlim F G hF hFc hG hGc hβ B hB).congr' ?_
  filter_upwards [sum_filter_mem_Qstar_eq_sum p hε₀ hε₀' j j' hA i₀ hsupp] with x hx
  refine congrArg (fun S ↦ S / divisorSumNorm m x) ?_
  have hc := hx ((Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 (B x) | Nat.Coprime (W x) d}) ×ˢ
      Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 (B x) | Nat.Coprime (W x) d})
    fun dd ↦ (((W x).totient : ℝ) * ∏ i, (Nat.totient ((dd.1 i).lcm (dd.2 i)) : ℝ))⁻¹
  simp only [← div_eq_mul_inv] at hc
  rw [hc, Finset.sum_product]

end Gap212.Sieve
