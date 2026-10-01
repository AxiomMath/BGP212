/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.DivisorSumOverQstar
public import Gap212.Sieve.RetreatOneLe
public meta import Gap212.Attr

/-!
# The divisor-sum asymptotic over a support's moduli: the assembly

The divisor-sum asymptotic over a support's moduli, assembled from what
`Gap212.Sieve.DivisorSumOverQstar` proves and two hypotheses. For a support datum `p` with
`ε < A_j`, a retreat `ε₀ ∈ (0,1)`, bands `j, j'`, a removed coordinate `i₀` and families
`(Fᵢ)_{i≠i₀}`, `(Gᵢ)_{i≠i₀}` of class `C¹` with compact support and `i₀`-retreated at
`(j,j',ε₀)`,

  `∑_{d,d'}∏_{i≠i₀}μ(dᵢ)Fᵢ(log_x dᵢ)μ(d'ᵢ)Gᵢ(log_x d'ᵢ)/φ(W∏_{i≠i₀}[dᵢ,d'ᵢ])
     = (∏_{i≠i₀}∫₀^∞F'ᵢG'ᵢ + o(1))·W^{k-1}/(φ(W)^k(\log x)^{k-1})`,

the sum running over the tuples with `[dᵢ,d'ᵢ]` pairwise coprime and coprime to `W(x)` whose
modulus `W(x)∏ᵢ[dᵢ,d'ᵢ]` lies in `Q⋆(p,x,ε₀/2)`. That is
`Gap212.Sieve.divisor_sum_over_qstar`.

## The index set is finite, and nothing is truncated away

`Gap212.Sieve.qstarPairs` is the asymptotic's index set. It is *written* as a subset of the box of
divisors up to `⌊x⌋₊`, and `Gap212.Sieve.mem_qstarPairs_iff` says that box costs nothing: a modulus
of `Q⋆(p,x,ε₀/2)` lies in `[1,x]` by `Gap212.Sieve.one_le_and_le_of_mem_Qstar` — both bounds are in
`Gap212.Qgen` itself — and every `dᵢ` divides it. So membership of `qstarPairs` is equivalent
to the three conditions displayed, with no size restriction, and the asymptotic's sum is a
genuinely finite sum over exactly the tuples it names.

## The two hypotheses

* `Gap212.Sieve.TotientGramSumLimitOfSupport`, stated in `Gap212.Sieve.DivisorSumOverQstar`: the
  normalized one-coordinate Gram sum tends to `∫₀^∞F'G'`, for profiles vanishing from `β` on. Its
  support clause is supplied, at `β = 1`, from the asymptotic's own reduced retreat, in
  `Gap212.Sieve.tendsto_boxDivisorSum_of_retreat`. It is equivalent to
  `Gap212.Sieve.Polymath41Totient`
  (`Gap212.Sieve.totientGramSumLimitOfSupport_iff_polymath41Totient`), which
  `Gap212.Sieve.polymath41Totient` proves.
* `Gap212.Sieve.TotientSievingError`, stated here: the difference between the sum over the full
  box of tuples coprime to `W(x)` and the sum over those whose least common multiples are in
  addition pairwise coprime is `o` of the asymptotic's normalization. It is proved at every `m` as
  `Gap212.Sieve.totientSievingError`, in `Gap212.Sieve.SmoothTotientInner`.

The other steps are proved in `Gap212.Sieve.DivisorSumOverQstar`:

* the restriction to `Q⋆` removes no non-zero term
  (`Gap212.Sieve.mem_Qstar_of_divisorNumerator_ne_zero`, from
  `Gap212.Sieve.generated_modulus_mem_Qstar`);
* the denominator decouples on the pairwise coprime tuples,
  `Gap212.Sieve.sum_divisorNumerator_div_totient_decouple`;
* the coordinates separate over a box,
  `Gap212.Sieve.sum_divisorNumerator_div_prod_totient_eq_prod`;
* each one-coordinate pair sum is its Gram form,
  `Gap212.Sieve.pairSumTotient_eq_gramSumTotient`;
* the box asymptotic in the asymptotic's own normalization,
  `Gap212.Sieve.tendsto_divisorSum_box_of_support`.

## The separated denominator

Both sums compared by `Gap212.Sieve.TotientSievingError`,
`Gap212.Sieve.boxDivisorSum` and `Gap212.Sieve.sievedDivisorSum`, carry the separated denominator
`φ(W)∏ᵢφ([dᵢ,d'ᵢ])`. On `𝓢` it equals `φ(W∏ᵢ[dᵢ,d'ᵢ])` — the decoupling
`φ(W∏ᵢmᵢ) = φ(W)∏ᵢφ(mᵢ)` on pairwise coprime lcms, `Gap212.Sieve.sum_sepSummand_eq_sum_div_totient`
— while the coordinates separate only over the full box `𝓑`.

## Main definitions

* `Gap212.Sieve.boxPairs`, `Gap212.Sieve.sievedPairs`: `𝓑` and `𝓢` at a truncation.
* `Gap212.Sieve.qstarPairs`: the asymptotic's index set.
* `Gap212.Sieve.sepSummand`: the summand at the separated denominator `φ(W)∏ᵢφ([dᵢ,d'ᵢ])`.
* `Gap212.Sieve.boxDivisorSum`, `Gap212.Sieve.sievedDivisorSum`: `Σ^{sep}_x(𝓑)`, `Σ^{sep}_x(𝓢)`.
* `Gap212.Sieve.TotientSievingError`: the sieving error.

## Main results

* `Gap212.Sieve.one_le_and_le_of_mem_Qstar`: a modulus of the support lies in `[1,x]`.
* `Gap212.Sieve.mem_qstarPairs_iff`: the asymptotic's index set is cut out by the three
  conditions.
* `Gap212.Sieve.sum_sepSummand_eq_sum_div_totient`: on pairwise coprime tuples the separated
  denominator is the asymptotic's own.
* `Gap212.Sieve.divisorNumerator_eq_zero_of_null`, `Gap212.Sieve.boxDivisorSum_eq_zero_of_null`: a
  profile vanishing on all of `[0,∞)` kills the box sum, which is the degenerate branch of the
  support dispatch.
* `Gap212.Sieve.tendsto_boxDivisorSum_of_retreat`: the box asymptotic from
  `TotientGramSumLimitOfSupport`, its support clause discharged from the reduced retreat
  hypothesis.
* `Gap212.Sieve.tendsto_sievedDivisorSum`: the asymptotic over `𝓢`, from the Gram limit and the
  sieving error at `β = 1`.
* `Gap212.Sieve.lt_rpow_half_of_divisorNumerator_ne_zero`: a contributing tuple has every
  coordinate below `x^{1/2}`, whatever the truncation.
* `Gap212.Sieve.totientSievingError_of_subsingleton`, `..._zero`, `..._one`: the sieving error
  where there is at most one coordinate.
* `Gap212.Sieve.divisor_sum_over_qstar`: the assembled asymptotic.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.Defs Gap212.GPY
open scoped ArithmeticFunction.Moebius

/-! ## The moduli of a support are bounded -/

/-- **A modulus of the support lies in `[1,x]`.** Both bounds are in `Gap212.Qgen`, which is the
set of `q` with `1 ≤ q ≤ x` admitting the prescribed factorization; `Gap212.Qstar` is a union of
those, so it inherits them.

This is what makes the asymptotic's sum finite: a tuple whose modulus `W(x)∏ᵢ[dᵢ,d'ᵢ]` lies in `Q⋆`
has every `dᵢ` and `d'ᵢ` a divisor of that modulus, hence at most `x`. -/
theorem one_le_and_le_of_mem_Qstar {p : SupportParams} {x ε₀ : ℝ} {q : ℕ}
    (hq : q ∈ Qstar p x ε₀) : 1 ≤ q ∧ (q : ℝ) ≤ x := by
  simp only [Qstar, Set.mem_iUnion] at hq
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := hq
  exact ⟨h1, h2⟩

/-! ## The three index sets -/

/-- **The index set `𝓑`**: the pairs of divisor tuples in the box `[1,B]` all of whose
coordinates are coprime to `W(x)` — equivalently, all of whose least common multiples are coprime
to `W(x)`. -/
noncomputable def boxPairs (m : ℕ) (x : ℝ) (B : ℕ) : Finset ((Fin m → ℕ) × (Fin m → ℕ)) :=
  (Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 B | Nat.Coprime (W x) d}) ×ˢ
    Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 B | Nat.Coprime (W x) d}

/-- **The index set `𝓢`**: the members of `Gap212.Sieve.boxPairs` whose least common multiples
`[dᵢ,d'ᵢ]` are in addition pairwise coprime. These, and not the full box, are the tuples the
statement sums over — and the ones on which the totient denominator decouples exactly. -/
noncomputable def sievedPairs (m : ℕ) (x : ℝ) (B : ℕ) : Finset ((Fin m → ℕ) × (Fin m → ℕ)) :=
  {dd ∈ boxPairs m x B |
    ∀ i i' : Fin m, i ≠ i' → Nat.Coprime ((dd.1 i).lcm (dd.2 i)) ((dd.1 i').lcm (dd.2 i'))}

open Classical in
/-- **The asymptotic's index set**: the pairs of divisor tuples whose least common multiples are
pairwise coprime and coprime to `W(x)` and whose modulus `W(x)∏ᵢ[dᵢ,d'ᵢ]` lies in `Q⋆(p,x,ε₀/2)`.

The box `[1,⌊x⌋₊]` in the definition is not a restriction — see
`Gap212.Sieve.mem_qstarPairs_iff` — it is only what makes the index set a `Finset`. -/
noncomputable def qstarPairs (p : SupportParams) (m : ℕ) (x ε₀ : ℝ) :
    Finset ((Fin m → ℕ) × (Fin m → ℕ)) :=
  {dd ∈ (Fintype.piFinset fun _ : Fin m ↦ Icc 1 ⌊x⌋₊) ×ˢ
      Fintype.piFinset fun _ : Fin m ↦ Icc 1 ⌊x⌋₊ |
    (∀ i, Nat.Coprime (W x) ((dd.1 i).lcm (dd.2 i))) ∧
      (∀ i i' : Fin m, i ≠ i' → Nat.Coprime ((dd.1 i).lcm (dd.2 i)) ((dd.1 i').lcm (dd.2 i'))) ∧
      W x * ∏ i, (dd.1 i).lcm (dd.2 i) ∈ Qstar p x (ε₀ / 2)}

/-- **The asymptotic's index set is cut out by the three conditions.** A pair of tuples belongs to
`Gap212.Sieve.qstarPairs` exactly when its least common multiples are coprime to `W(x)`, pairwise
coprime, and generate a modulus of `Q⋆(p,x,ε₀/2)`. No size bound is assumed: the modulus is at most
`x` by `Gap212.Sieve.one_le_and_le_of_mem_Qstar` and every coordinate divides it, so the box in the
definition is implied rather than imposed. -/
theorem mem_qstarPairs_iff (p : SupportParams) {m : ℕ} {x ε₀ : ℝ}
    (dd : (Fin m → ℕ) × (Fin m → ℕ)) :
    dd ∈ qstarPairs p m x ε₀ ↔
      (∀ i, Nat.Coprime (W x) ((dd.1 i).lcm (dd.2 i))) ∧
        (∀ i i' : Fin m, i ≠ i' → Nat.Coprime ((dd.1 i).lcm (dd.2 i)) ((dd.1 i').lcm (dd.2 i'))) ∧
        W x * ∏ i, (dd.1 i).lcm (dd.2 i) ∈ Qstar p x (ε₀ / 2) := by
  classical
  rw [qstarPairs, Finset.mem_filter]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  obtain ⟨-, -, hQ⟩ := h
  obtain ⟨hq1, hqx⟩ := one_le_and_le_of_mem_Qstar hQ
  -- Every coordinate divides the modulus, which is a positive integer at most `x`.
  have key : ∀ d : Fin m → ℕ, (∀ i, d i ∣ (dd.1 i).lcm (dd.2 i)) →
      ∀ i, d i ∈ Icc 1 ⌊x⌋₊ := by
    intro d hd i
    have hdq : d i ∣ W x * ∏ j, (dd.1 j).lcm (dd.2 j) :=
      (hd i).trans ((Finset.dvd_prod_of_mem (fun j ↦ (dd.1 j).lcm (dd.2 j))
        (Finset.mem_univ i)).trans (dvd_mul_left _ _))
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdq hq1,
      Nat.le_floor ((Nat.cast_le.mpr (Nat.le_of_dvd hq1 hdq)).trans hqx)⟩
  exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr (key dd.1 fun i ↦ Nat.dvd_lcm_left _ _),
    Fintype.mem_piFinset.mpr (key dd.2 fun i ↦ Nat.dvd_lcm_right _ _)⟩

/-- **The coordinates of a member of the asymptotic's index set are positive.** -/
theorem lcm_pos_of_mem_qstarPairs {p : SupportParams} {m : ℕ} {x ε₀ : ℝ}
    {dd : (Fin m → ℕ) × (Fin m → ℕ)} (h : dd ∈ qstarPairs p m x ε₀) (i : Fin m) :
    0 < (dd.1 i).lcm (dd.2 i) := by
  classical
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp h).1
  exact Nat.lcm_pos (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp h1 i)).1
    (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp h2 i)).1

/-! ## The two sums the sieving error compares -/

/-- **The summand at the separated denominator** `φ(W(x))∏ᵢφ([dᵢ,d'ᵢ])`. On the tuples whose least
common multiples are pairwise coprime and coprime to `W(x)` this is the asymptotic's own summand
`N(d,d')/φ(W(x)∏ᵢ[dᵢ,d'ᵢ])` (`Gap212.Sieve.sum_sepSummand_eq_sum_div_totient`); over a full box it
is the quantity whose coordinates separate. -/
noncomputable def sepSummand {m : ℕ} (x : ℝ) (F G : Fin m → ℝ → ℝ)
    (dd : (Fin m → ℕ) × (Fin m → ℕ)) : ℝ :=
  divisorNumerator x F G dd /
    (((W x).totient : ℝ) * ∏ i, (Nat.totient ((dd.1 i).lcm (dd.2 i)) : ℝ))

/-- **`Σ^{sep}_x(𝓑)`**: the separated summand over the full box of tuples coprime to `W(x)`. This
is the quantity `Gap212.Sieve.tendsto_divisorSum_box_of_support` evaluates. -/
noncomputable def boxDivisorSum {m : ℕ} (x : ℝ) (B : ℕ) (F G : Fin m → ℝ → ℝ) : ℝ :=
  ∑ dd ∈ boxPairs m x B, sepSummand x F G dd

/-- **`Σ^{sep}_x(𝓢)`**: the same summand over the tuples whose least common multiples are in
addition pairwise coprime. This is the asymptotic's own sum — on `𝓢` the separated denominator *is*
`φ(W(x)∏ᵢ[dᵢ,d'ᵢ])`. -/
noncomputable def sievedDivisorSum {m : ℕ} (x : ℝ) (B : ℕ) (F G : Fin m → ℝ → ℝ) : ℝ :=
  ∑ dd ∈ sievedPairs m x B, sepSummand x F G dd

/-- **The box sum, written as the iterated sum `Gap212.Sieve.tendsto_divisorSum_box_of_support` is
stated at.** `Gap212.Sieve.boxPairs` is a product of two boxes, so `Finset.sum_product` applies. -/
theorem boxDivisorSum_eq {m : ℕ} (x : ℝ) (B : ℕ) (F G : Fin m → ℝ → ℝ) :
    boxDivisorSum x B F G
      = ∑ d ∈ Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 B | Nat.Coprime (W x) d},
          ∑ d' ∈ Fintype.piFinset fun _ : Fin m ↦ {d ∈ Icc 1 B | Nat.Coprime (W x) d},
            divisorNumerator x F G (d, d') /
              (((W x).totient : ℝ) * ∏ i, (Nat.totient ((d i).lcm (d' i)) : ℝ)) :=
  Finset.sum_product _ _ _

/-- **On pairwise coprime tuples the separated denominator is the asymptotic's own.** Over a finite
family whose least common multiples are positive, pairwise coprime and coprime to `W(x)`,

  `∑ N(d,d')/(φ(W)∏ᵢφ([dᵢ,d'ᵢ])) = ∑ N(d,d')/φ(W∏ᵢ[dᵢ,d'ᵢ])`.

This is `Gap212.Sieve.sum_divisorNumerator_div_totient_decouple`, together with the fact that a
product of quotients is the quotient of the products. -/
theorem sum_sepSummand_eq_sum_div_totient {m : ℕ} (x : ℝ) (F G : Fin m → ℝ → ℝ)
    (T : Finset ((Fin m → ℕ) × (Fin m → ℕ)))
    (hT : ∀ dd ∈ T, (∀ i, 0 < (dd.1 i).lcm (dd.2 i)) ∧
      (∀ i, Nat.Coprime (W x) ((dd.1 i).lcm (dd.2 i))) ∧
      (∀ i i' : Fin m, i ≠ i' → Nat.Coprime ((dd.1 i).lcm (dd.2 i)) ((dd.1 i').lcm (dd.2 i')))) :
    ∑ dd ∈ T, sepSummand x F G dd
      = ∑ dd ∈ T, divisorNumerator x F G dd /
          (Nat.totient (W x * ∏ i, (dd.1 i).lcm (dd.2 i)) : ℝ) := by
  have hWpos : 0 < W x := primorial_pos _
  rw [sum_divisorNumerator_div_totient_decouple x F G T hT, Finset.mul_sum]
  refine Finset.sum_congr rfl fun dd _ ↦ ?_
  rw [sepSummand, divisorNumerator, Finset.prod_div_distrib]
  ring

/-! ## The sieving error -/

/-- **The sieving error of the totient divisor sum.** For a support datum `p`, a retreat
`ε₀ ∈ (0,1)`, bands `j, j'`, a removed coordinate `i₀`, families `(Fᵢ)_{i≠i₀}` and `(Gᵢ)_{i≠i₀}`
of class `C¹` with compact support and `i₀`-retreated at `(j,j',ε₀)`, and a truncation `B ≥ x^β`
with `β ≥ 1`,

  `(Σ^{sep}_x(𝓑) - Σ^{sep}_x(𝓢)) / (W^{k-1}/(φ(W)^k(\log x)^{k-1})) ⟶ 0`,

`𝓑` being the tuples in the box with every `[dᵢ,d'ᵢ]` coprime to `W(x)` and `𝓢 ⊆ 𝓑` those whose
lcms are in addition pairwise coprime (`Gap212.Sieve.boxDivisorSum`,
`Gap212.Sieve.sievedDivisorSum`), and the normalization `Gap212.Sieve.divisorSumNorm`.

The retreat condition is the reduced one, `Gap212.GPY.IsReducedRetreat`: the sum runs over the
`k-1` coordinates other than `i₀` and is asymmetric between the two families. The companion
`Gap212.Sieve.SelbergSievingError` carries the symmetric full-`k` `Gap212.Sieve.IsRetreatedPair`
instead.

Both sums carry the separated denominator `φ(W)∏ᵢφ([dᵢ,d'ᵢ])`, which equals `φ(W∏ᵢ[dᵢ,d'ᵢ])` on
`𝓢` (`Gap212.Sieve.sum_sepSummand_eq_sum_div_totient`); the usual display writes both sums with
the latter, and the two first terms differ by a sum supported on the tuples where two lcms share
a prime, the same tuples the difference is about.

The proof keeps the Möbius cancellation in every coordinate: a prime shared between two lcms of a
tuple coprime to `W(x)` exceeds `log log log x`, so its reciprocal square is summably small, and
the one-coordinate pair sum restricted to `q ∣ [d,d']` is bounded uniformly in `q`. The coprimality
indicator over the pairs `(i,i')` is Möbius-inverted
(`Gap212.Sieve.sum_coprime_pairs_eq_sum_moebius`,
`Gap212.Sieve.exists_threshold_abs_sub_sum_coprime_pairs_le`; see `Gap212.Sieve.SievingErrorTails`),
and the `k`-coordinate expansion of `Gap212.Sieve.PairwiseCoprimeMoebius` is bounded prime-wise
(edge-wise accounting fails from `k = 4` on, `Gap212.Sieve.prod_incLcm_lt_prod_edges_four`). The
resulting one-coordinate estimate is `Gap212.Sieve.OneCoordTotientDecayAtLevelOfSupport (3/4)`,
proved by `Gap212.Sieve.oneCoordTotientDecayAtLevelOfSupport_three_quarters`, and
`Gap212.Sieve.tendsto_boxDivisorSum_sub_sievedDivisorSum_of_support` concludes the limit from it.
This gives `Gap212.Sieve.totientSievingError`, at every `m`.

The one-coordinate estimate asks that the profiles vanish from `β` on, and
`Gap212.GPY.IsReducedRetreat` gives vanishing from `1` on; hence `β ≥ 1`. Whether the limit holds
for `β < 1` is not decided here. -/
@[gap212 "lem_divisor_sum_sieving_error"]
def TotientSievingError (m : ℕ) : Prop :=
  ∀ (p : SupportParams) (ε₀ : ℝ), 0 < ε₀ → ε₀ < 1 → ∀ (j j' : Fin p.n) (i₀ : Fin (m + 1))
      (F G : Fin m → ℝ → ℝ),
    (∀ i, ContDiff ℝ 1 (F i)) → (∀ i, HasCompactSupport (F i)) →
    (∀ i, ContDiff ℝ 1 (G i)) → (∀ i, HasCompactSupport (G i)) →
    IsReducedRetreat p m j j' ε₀ i₀ F G →
    ∀ β : ℝ, 1 ≤ β → ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
      Tendsto (fun x : ℝ ↦
          (boxDivisorSum x (B x) F G - sievedDivisorSum x (B x) F G) / divisorSumNorm m x)
        atTop (nhds 0)

/-! ## Contributing tuples are bounded

Every tuple with a non-zero numerator has every coordinate below `x^{1/2}`, whatever the truncation
`B` (`Gap212.Sieve.lt_rpow_half_of_divisorNumerator_ne_zero`), because
`Gap212.GPY.IsReducedRetreat` confines `log_x dᵢ` to the retreat region. With at most one
coordinate the pairwise-coprimality restriction is vacuous
(`Gap212.Sieve.totientSievingError_of_subsingleton`). -/

/-- **A tuple with a non-zero numerator has every coordinate below `x^{1/2}`, whatever the
truncation.** A non-zero numerator forces both `∏ᵢFᵢ(\log_xdᵢ) ≠ 0` and `∏ᵢGᵢ(\log_xd'ᵢ) ≠ 0`, so
`Gap212.GPY.IsReducedRetreat` puts both extended points in the retreat region, where every
coordinate is below `1/2` (`Gap212.Sieve.coord_lt_half_of_mem_retreatRegion`).

So the box beyond `x^{1/2}` contributes nothing to either of the two sums
`Gap212.Sieve.TotientSievingError` compares. -/
theorem lt_rpow_half_of_divisorNumerator_ne_zero {p : SupportParams} {m : ℕ} {j j' : Fin p.n}
    {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) {i₀ : Fin (m + 1)} {F G : Fin m → ℝ → ℝ}
    (hsupp : IsReducedRetreat p m j j' ε₀ i₀ F G) {x : ℝ} (hx : 1 < x)
    {dd : (Fin m → ℕ) × (Fin m → ℕ)} (hd : ∀ i, 1 ≤ dd.1 i) (hd' : ∀ i, 1 ≤ dd.2 i)
    (h : divisorNumerator x F G dd ≠ 0) (i : Fin m) :
    (dd.1 i : ℝ) < x ^ (1 / 2 : ℝ) ∧ (dd.2 i : ℝ) < x ^ (1 / 2 : ℝ) := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hnn : ∀ e : Fin m → ℕ, (∀ i, 1 ≤ e i) → ∀ i, (0 : ℝ) ≤ Notation.logx x (e i) := fun e he i ↦
    div_nonneg (Real.log_nonneg (by exact_mod_cast he i)) (Real.log_nonneg hx.le)
  -- Both products are non-zero factors of the numerator.
  have hprod : (∏ i, F i (Notation.logx x (dd.1 i))) ≠ 0 ∧
      (∏ i, G i (Notation.logx x (dd.2 i))) ≠ 0 := by
    constructor <;> intro h0 <;> refine h (Finset.prod_eq_zero_iff.mpr ?_)
    · obtain ⟨i', -, hi'⟩ := Finset.prod_eq_zero_iff.mp h0
      exact ⟨i', Finset.mem_univ i', by rw [hi', mul_zero, zero_mul]⟩
    · obtain ⟨i', -, hi'⟩ := Finset.prod_eq_zero_iff.mp h0
      exact ⟨i', Finset.mem_univ i', by rw [hi', mul_zero, mul_zero]⟩
  have hhalf : ∀ e : Fin m → ℕ, (∀ i, 1 ≤ e i) → ∀ jj : Fin p.n,
      i₀.insertNth 0 (fun i ↦ Notation.logx x (e i)) ∈ retreatRegion p (m + 1) jj ε₀ →
        (e i : ℝ) < x ^ (1 / 2 : ℝ) := by
    intro e he jj hmem
    have hlt := coord_lt_half_of_mem_retreatRegion hε₀ hmem (i₀.succAbove i)
    rw [Fin.insertNth_apply_succAbove, Notation.logx, div_lt_iff₀ hlx] at hlt
    rw [← Real.log_lt_log_iff (by exact_mod_cast he i) (by positivity),
      Real.log_rpow (by linarith)]
    linarith
  exact ⟨hhalf dd.1 hd j (((hsupp _ (hnn _ hd)).1 hprod.1).1),
    hhalf dd.2 hd' j' ((hsupp _ (hnn _ hd')).2 hprod.2)⟩

/-- **With at most one coordinate there is nothing to sieve.** The pairwise-coprimality restriction
is a condition on *distinct* coordinates, so on a subsingleton index type it is vacuous and `𝓢` is
all of `𝓑`. -/
theorem sievedPairs_eq_boxPairs_of_subsingleton {m : ℕ} (hk : ∀ i i' : Fin m, i = i') (x : ℝ)
    (B : ℕ) : sievedPairs m x B = boxPairs m x B := by
  classical
  rw [sievedPairs, Finset.filter_eq_self]
  exact fun dd _ i i' hne ↦ absurd (hk i i') hne

/-- **The sieving error holds outright when there is at most one coordinate**, both sums being over
the same index set by `Gap212.Sieve.sievedPairs_eq_boxPairs_of_subsingleton`.
`Gap212.Sieve.totientSievingError` proves every `m`. -/
theorem totientSievingError_of_subsingleton {m : ℕ} (hk : ∀ i i' : Fin m, i = i') :
    TotientSievingError m := by
  intro p ε₀ _ _ j j' i₀ F G _ _ _ _ _ β _ B _
  refine tendsto_const_nhds.congr fun x ↦ ?_
  rw [sievedDivisorSum, sievedPairs_eq_boxPairs_of_subsingleton hk, ← boxDivisorSum, sub_self,
    zero_div]

/-- **`Gap212.Sieve.TotientSievingError m` for `m ≤ 1`**: there are no two distinct coordinates to
share a prime. -/
theorem totientSievingError_zero : TotientSievingError 0 :=
  totientSievingError_of_subsingleton fun i i' ↦ by omega

@[inherit_doc totientSievingError_zero]
theorem totientSievingError_one : TotientSievingError 1 :=
  totientSievingError_of_subsingleton fun i i' ↦ by omega

/-! ## The asymptotic over the pairwise coprime tuples -/

/-- **The box asymptotic, at `Gap212.Sieve.boxDivisorSum`.**
`Gap212.Sieve.tendsto_divisorSum_box_of_support` with the iterated sum folded into the one over
`Gap212.Sieve.boxPairs`, for `C^∞` profiles vanishing from `β` on. -/
theorem tendsto_boxDivisorSum (hgram : TotientGramSumLimitOfSupport) {m : ℕ} (F G : Fin m → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    {β : ℝ} (hβ : 0 < β) (hFβ : ∀ i, ∀ t, β ≤ t → F i t = 0)
    (hGβ : ∀ i, ∀ t, β ≤ t → G i t = 0)
    (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦ boxDivisorSum x (B x) F G / divisorSumNorm m x) atTop
      (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) := by
  refine (tendsto_divisorSum_box_of_support hgram F G hF hFc hG hGc hβ hFβ hGβ B hB).congr
    fun x ↦ ?_
  rw [boxDivisorSum_eq]

/-! ## The support clause at a reduced retreat -/

/-- **A null factor kills the numerator of every tuple in the box.** The numerator reads `F i₀` at
`log_x (d i₀)` and `G i₀` at `log_x (d' i₀)`, both nonnegative for coordinates at least `1` and
`x > 1`, so a profile vanishing on all of `[0,∞)` zeroes the whole product. -/
theorem divisorNumerator_eq_zero_of_null {m : ℕ} {F G : Fin m → ℝ → ℝ} {i₀ : Fin m}
    (hnull : (∀ t : ℝ, 0 ≤ t → F i₀ t = 0) ∨ ∀ t : ℝ, 0 ≤ t → G i₀ t = 0) {x : ℝ} (hx : 1 < x)
    {dd : (Fin m → ℕ) × (Fin m → ℕ)} (hd : ∀ i, 1 ≤ dd.1 i) (hd' : ∀ i, 1 ≤ dd.2 i) :
    divisorNumerator x F G dd = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
  have hnn : ∀ e : ℕ, 1 ≤ e → (0 : ℝ) ≤ Notation.logx x e := fun e he ↦
    div_nonneg (Real.log_nonneg (by exact_mod_cast he)) (Real.log_nonneg hx.le)
  rcases hnull with h | h
  · rw [h _ (hnn _ (hd i₀)), mul_zero, zero_mul]
  · rw [h _ (hnn _ (hd' i₀)), mul_zero, mul_zero]

/-- **A null factor on either side kills the full-box sum.** Every tuple of
`Gap212.Sieve.boxPairs` has all coordinates at least `1`, so
`Gap212.Sieve.divisorNumerator_eq_zero_of_null` applies to each term and each term is
`0` divided by something. -/
theorem boxDivisorSum_eq_zero_of_null {m : ℕ} {F G : Fin m → ℝ → ℝ} {i₀ : Fin m}
    (hnull : (∀ t : ℝ, 0 ≤ t → F i₀ t = 0) ∨ ∀ t : ℝ, 0 ≤ t → G i₀ t = 0) {x : ℝ} (hx : 1 < x)
    (B : ℕ) : boxDivisorSum x B F G = 0 := by
  classical
  refine Finset.sum_eq_zero fun dd hdd ↦ ?_
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hdd
  have hd : ∀ i, 1 ≤ dd.1 i := fun i ↦
    (Finset.mem_Icc.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp h1 i)).1).1
  have hd' : ∀ i, 1 ≤ dd.2 i := fun i ↦
    (Finset.mem_Icc.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp h2 i)).1).1
  rw [sepSummand, divisorNumerator_eq_zero_of_null hnull hx hd hd', zero_div]

/-- **The box asymptotic at a reduced retreat.** The conclusion of
`Gap212.Sieve.tendsto_boxDivisorSum` at `β = 1`, with the support clause discharged from
`Gap212.GPY.IsReducedRetreat`.

`Gap212.Sieve.exists_null_or_forall_eq_zero_of_one_le_insertNth` splits each family: either every
factor vanishes from `1` on, or some factor vanishes on all of `[0,∞)`, and then both sides are
identically zero (`Gap212.Sieve.boxDivisorSum_eq_zero_of_null`,
`Gap212.Sieve.prod_integral_eq_zero_of_null_left`). -/
theorem tendsto_boxDivisorSum_of_retreat (hgram : TotientGramSumLimitOfSupport)
    (p : SupportParams) {m : ℕ} {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) {j j' : Fin p.n} {i₀ : Fin (m + 1)}
    (F G : Fin m → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    (hsupp : IsReducedRetreat p m j j' ε₀ i₀ F G)
    (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ (1 : ℝ) ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦ boxDivisorSum x (B x) F G / divisorSumNorm m x) atTop
      (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) := by
  have hnull : ∀ i' : Fin m, (∀ t : ℝ, 0 ≤ t → F i' t = 0) ∨ (∀ t : ℝ, 0 ≤ t → G i' t = 0) →
      Tendsto (fun x : ℝ ↦ boxDivisorSum x (B x) F G / divisorSumNorm m x) atTop
        (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) := by
    intro i' h
    rw [h.elim prod_integral_eq_zero_of_null_left prod_integral_eq_zero_of_null_right]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [boxDivisorSum_eq_zero_of_null h hx, zero_div]
  rcases exists_null_or_forall_eq_zero_of_one_le_insertNth hε₀
      (fun t ht hne ↦ ((hsupp t ht).1 hne).1) with ⟨i', hnF⟩ | hF1
  · exact hnull i' (Or.inl hnF)
  rcases exists_null_or_forall_eq_zero_of_one_le_insertNth hε₀
      (fun t ht hne ↦ (hsupp t ht).2 hne) with ⟨i', hnG⟩ | hG1
  · exact hnull i' (Or.inr hnG)
  exact tendsto_boxDivisorSum hgram F G hF hFc hG hGc one_pos hF1 hG1 B hB

/-- **The asymptotic over the pairwise coprime tuples.** The full-box limit of
`Gap212.Sieve.tendsto_boxDivisorSum_of_retreat` minus the sieving error
`Gap212.Sieve.TotientSievingError` (proved as `Gap212.Sieve.totientSievingError`), at `β = 1`.

The profiles are `C^∞`, as `hgram` asks; `hsieve` is stated for `C¹` profiles. -/
theorem tendsto_sievedDivisorSum (hgram : TotientGramSumLimitOfSupport) {m : ℕ}
    (hsieve : TotientSievingError m) (p : SupportParams) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1)
    (j j' : Fin p.n) (i₀ : Fin (m + 1)) (F G : Fin m → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    (hsupp : IsReducedRetreat p m j j' ε₀ i₀ F G)
    (B : ℝ → ℕ) (hB : ∀ᶠ x : ℝ in atTop, x ^ (1 : ℝ) ≤ (B x : ℝ)) :
    Tendsto (fun x : ℝ ↦ sievedDivisorSum x (B x) F G / divisorSumNorm m x) atTop
      (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) := by
  have h := (tendsto_boxDivisorSum_of_retreat hgram p hε₀.le F G hF hFc hG hGc hsupp B hB).sub
    (hsieve p ε₀ hε₀ hε₀' j j' i₀ F G (fun i ↦ (hF i).of_le (by exact_mod_cast le_top)) hFc
      (fun i ↦ (hG i).of_le (by exact_mod_cast le_top)) hGc hsupp 1 le_rfl B hB)
  rw [sub_zero] at h
  exact h.congr fun x ↦ by ring

/-! ## The `Q⋆` restriction, and the asymptotic -/

/-- **The asymptotic's index set sits inside `𝓢`.** Every member of `Gap212.Sieve.qstarPairs` has
its coordinates in the box `[1,⌊x⌋₊]`, hence in `[1,B]` for `B ≥ ⌊x⌋₊`, and is coprime to `W(x)`
and pairwise coprime coordinatewise. -/
theorem qstarPairs_subset_sievedPairs (p : SupportParams) {m : ℕ} {x ε₀ : ℝ} {B : ℕ}
    (hB : ⌊x⌋₊ ≤ B) : qstarPairs p m x ε₀ ⊆ sievedPairs m x B := by
  classical
  intro dd hdd
  obtain ⟨hb1, hb2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hdd).1
  obtain ⟨hcop, hpw, -⟩ := (mem_qstarPairs_iff p dd).mp hdd
  rw [sievedPairs, Finset.mem_filter]
  refine ⟨Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun i ↦ ?_,
    Fintype.mem_piFinset.mpr fun i ↦ ?_⟩, hpw⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hb1 i)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2.trans hB⟩,
      (hcop i).coprime_dvd_right (Nat.dvd_lcm_left _ _)⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hb2 i)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2.trans hB⟩,
      (hcop i).coprime_dvd_right (Nat.dvd_lcm_right _ _)⟩

/-- **The restriction to `Q⋆` removes no term from `𝓢`.** For all large `x`, the sum over `𝓢` of
the separated summand is the sum over the asymptotic's index set of the asymptotic's own summand:
the tuples of `𝓢` outside `Gap212.Sieve.qstarPairs` have a vanishing numerator
(`Gap212.Sieve.mem_Qstar_of_divisorNumerator_ne_zero` — the hypothesis `hQ` here), and on
`Gap212.Sieve.qstarPairs` the separated denominator is the asymptotic's
(`Gap212.Sieve.sum_sepSummand_eq_sum_div_totient`). -/
theorem sievedDivisorSum_eq_qstarSum (p : SupportParams) {m : ℕ} {x ε₀ : ℝ} {B : ℕ}
    (hB : ⌊x⌋₊ ≤ B) (F G : Fin m → ℝ → ℝ)
    (hQ : ∀ dd : (Fin m → ℕ) × (Fin m → ℕ), divisorNumerator x F G dd ≠ 0 →
      W x * ∏ i, (dd.1 i).lcm (dd.2 i) ∈ Qstar p x (ε₀ / 2)) :
    sievedDivisorSum x B F G
      = ∑ dd ∈ qstarPairs p m x ε₀, divisorNumerator x F G dd /
          (Nat.totient (W x * ∏ i, (dd.1 i).lcm (dd.2 i)) : ℝ) := by
  classical
  rw [← sum_sepSummand_eq_sum_div_totient x F G (qstarPairs p m x ε₀) fun dd hdd ↦
    ⟨fun i ↦ lcm_pos_of_mem_qstarPairs hdd i, ((mem_qstarPairs_iff p dd).mp hdd).1,
      ((mem_qstarPairs_iff p dd).mp hdd).2.1⟩, sievedDivisorSum]
  refine (Finset.sum_subset (qstarPairs_subset_sievedPairs p hB) fun dd hdd hnot ↦ ?_).symm
  rw [sepSummand]
  rcases eq_or_ne (divisorNumerator x F G dd) 0 with h0 | h0
  · rw [h0, zero_div]
  · -- A non-zero numerator puts the modulus in `Q⋆`, so the tuple is in the index set.
    obtain ⟨hboxW, hpw⟩ := Finset.mem_filter.mp hdd
    obtain ⟨hb1, hb2⟩ := Finset.mem_product.mp hboxW
    refine absurd ((mem_qstarPairs_iff p dd).mpr ⟨fun i ↦ ?_, hpw, hQ dd h0⟩) hnot
    exact Nat.Coprime.coprime_dvd_right
      (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))
      (Nat.Coprime.mul_right (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hb1 i)).2
        (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hb2 i)).2)

/-- **The divisor-sum asymptotic over a support's moduli.** For a support datum `p` with `ε < A_j`,
a retreat `ε₀ ∈ (0,1)`, bands `j, j'`, a removed coordinate `i₀` and families `(Fᵢ)_{i≠i₀}`,
`(Gᵢ)_{i≠i₀}` of class `C¹` with compact support and `i₀`-retreated at `(j,j',ε₀)`,

  `∑_{d,d'}∏ᵢμ(dᵢ)Fᵢ(log_x dᵢ)μ(d'ᵢ)Gᵢ(log_x d'ᵢ)/φ(W(x)∏ᵢ[dᵢ,d'ᵢ])
     = (∏ᵢ∫₀^∞F'ᵢG'ᵢ + o(1))·W^{k-1}/(φ(W)^k(\log x)^{k-1})`,

the sum running over the tuples with `[dᵢ,d'ᵢ]` pairwise coprime and coprime to `W(x)` whose
modulus lies in `Q⋆(p,x,ε₀/2)` (`Gap212.Sieve.qstarPairs`, whose membership is exactly those three
conditions by `Gap212.Sieve.mem_qstarPairs_iff`), and the normalization being
`Gap212.Sieve.divisorSumNorm` at `k - 1 = m`. The `+o(1)` form is the quotient by the normalization
tending to the product of integrals.

The hypotheses are `Gap212.Sieve.TotientGramSumLimitOfSupport` and
`Gap212.Sieve.TotientSievingError`; both are theorems, the first by
`Gap212.Sieve.totientGramSumLimitOfSupport_iff_polymath41Totient` and
`Gap212.Sieve.polymath41Totient`, the second as `Gap212.Sieve.totientSievingError`. The support
clause of the first is discharged by `Gap212.Sieve.tendsto_boxDivisorSum_of_retreat`. Both are
used at the truncation `B = ⌊2x⌋`, which contains the box `[1,⌊x⌋₊]`, so at `β = 1`. -/
@[gap212 "lem_divisor_sum_over_qstar"]
theorem divisor_sum_over_qstar (hgram : TotientGramSumLimitOfSupport) {m : ℕ}
    (hsieve : TotientSievingError m) (p : SupportParams) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1)
    (j j' : Fin p.n) (hA : p.ε < p.A j.succ) (i₀ : Fin (m + 1)) (F G : Fin m → ℝ → ℝ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (hFc : ∀ i, HasCompactSupport (F i))
    (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    (hsupp : IsReducedRetreat p m j j' ε₀ i₀ F G) :
    Tendsto (fun x : ℝ ↦
        (∑ dd ∈ qstarPairs p m x ε₀, divisorNumerator x F G dd /
            (Nat.totient (W x * ∏ i, (dd.1 i).lcm (dd.2 i)) : ℝ)) / divisorSumNorm m x)
      atTop (nhds (∏ i, ∫ t in Set.Ioi (0 : ℝ), deriv (F i) t * deriv (G i) t)) := by
  refine (tendsto_sievedDivisorSum hgram hsieve p hε₀ hε₀' j j' i₀ F G hF hFc hG hGc hsupp
    (fun y ↦ ⌊2 * y⌋₊) ?_).congr' ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy1
    rw [Real.rpow_one]
    linarith [Nat.sub_one_lt_floor (2 * y)]
  filter_upwards [mem_Qstar_of_divisorNumerator_ne_zero p hε₀ hε₀' j j' hA i₀ hsupp,
    eventually_ge_atTop (0 : ℝ)] with x hQ hx0
  rw [sievedDivisorSum_eq_qstarSum p (Nat.floor_le_floor (by linarith)) F G hQ]

end Gap212.Sieve
