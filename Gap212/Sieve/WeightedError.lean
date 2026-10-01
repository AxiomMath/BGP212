/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.AveragingFacts
public import Gap212.Defs
public meta import Gap212.Attr

/-!
# The weighted discrepancy error is negligible

The weighted sum of dyadic discrepancies over the divisor tuples a retreated pair of
weight families produces is `o(𝓒_x)`.

The three inputs are in `Gap212.Sieve.AveragingFacts`: the modulus a tuple generates lies in `Q⋆`
(`Gap212.Sieve.generated_modulus_mem_Qstar`), one sample of residues detects every tuple residue at
an exact density (`Gap212.Sieve.exists_averaging_sample`, used through
`Gap212.Sieve.norm_sumErrorDyadic_le_sample_average`), and the weighted discrepancy has a crude
moment bound with no distribution input (`Gap212.Sieve.crude_discrepancy_moment`). This file adds
the bookkeeping: group the tuples by their modulus with
`Gap212.Sieve.card_tuple_multiplicity`, pay the two multiplicities into
`Gap212.GPY.residueWeight`, and trade the crude moment against the equidistribution hypothesis.

## The squarefree restriction

Every `dᵢ` and `d'ᵢ` is assumed squarefree. That is what the Möbius factors
`∏_{i≠i₀}μ(dᵢ)μ(d'ᵢ)` of the quantity this bounds impose. Dropping them and summing over all
tuples gives a **false** statement. Without the restriction some `dᵢ`
is non-squarefree, and since `dᵢ ∣ [dᵢ,d'ᵢ]` the modulus `q = W(x)∏[dᵢ,d'ᵢ]` is then non-squarefree
too — whereas every input below is squarefree-only: `Gap212.Sieve.card_tuple_multiplicity` and
`Gap212.Sieve.residueWeight_bounds` hypothesise `Squarefree q`,
`Gap212.Sieve.crude_discrepancy_moment` sums over squarefree `q`, and
`Gap212.HasEquidistributionOverQstarFamily` is a bound over the squarefree members of `Q⋆`. On the
non-squarefree part only the trivial bound survives, and grouped by modulus that is
`≍ x(log x)^{O(1)}` while `𝓒_x ≍ x(log x)^{-45}`.

The restriction is also what makes `q` squarefree, which is what the proof consumes: a least common
multiple of squarefrees is squarefree (`Gap212.Sieve.squarefree_lcm`), pairwise coprimality makes
the product squarefree, `W(x)` is squarefree as a primorial, and coprimality to `W(x)` closes it
(`Gap212.Sieve.squarefree_generated_modulus`).

## The form of the statement

**The sum is read as every finite subfamily.** The estimate is about a sum over *all* admissible
tuples; the summand vanishes off a finite set because the weights are compactly supported, but
nothing here
needs that, and quantifying over every `Finset` of admissible tuples is *stronger* than bounding
one infinite sum — for a non-negative summand the two are equivalent when the support is finite,
and the `Finset` form does not have to produce the cutoff. So no cutoff is invented and no tuple is
dropped.

**`a(underline d)` is a choice function.** `Gap212.GPY.IsTupleResidue` is a predicate, not a
function: it records the congruences cutting out the class, uniqueness being a separate CRT
statement. So the statement takes an arbitrary `A : tuple → ℕ` together with the hypothesis that
`A` picks a tuple residue at every tuple summed over. That is the strongest of the two available
readings — it holds for *every* choice — and it is the one the sum needs, the summand depending on
the tuple through its residue. Quantifying `∀ a₀, IsTupleResidue … a₀ → …` inside the summand is
not available: there is no summand to write.

**The equidistribution is an explicit hypothesis.** `Gap212.Defs.RhoHypotheses` does
not carry the equidistribution clause — that is
`Gap212.HasEquidistributionOverQstarFamily`, which lives downstream of
`Gap212.Defs` — so it is passed separately, exactly as `Gap212.Sieve.GPYSieve` does.
Of `Gap212.Defs.RhoHypotheses` only the `minorant` clause is used, and only through
`0 ≤ ρ(·;x) ≤ 1` on the block; the support clause is not needed because
`Gap212.HasEquidistributionOverQstarFamily` is already stated with the *dyadic* discrepancy, so no
identification of the two discrepancies is required here.

**The weights are assumed bounded, not smooth.** The usual statement asks the `Fᵢ, Gᵢ` to be
smooth and compactly supported; the proof uses only a uniform bound `M` on their values together
with the
support condition `Gap212.GPY.IsReducedRetreat`, so those are what is hypothesised. Likewise the
tuple `h` is asked to be strictly monotone rather than admissible, which is what
`Gap212.Sieve.exists_averaging_sample` consumes. Both are generalizations.

## The order of the constants is forced

`C'` comes from the crude moment and depends on the divisor exponents alone; the saving
`A = C' + 2(k + 2)` is chosen after it; the equidistribution constant `c` is chosen after `A` and
before `x`, which is what lets one bound serve every residue of the sample even though the sample
grows with `x`. The statement carries none of the three. The classical argument asks for
`A > C' + 2(k + 3)` and lands at `x(log x)^{-(k+3)}`; one power less suffices, since `𝓒_x` is only
bounded below by `x(log x)^{-(k+1)}` and a single spare logarithm already absorbs the constant.

Cauchy–Schwarz is replaced by the pointwise inequality `2·v·D ≤ λ·D + λ^{-1}·v²·D`, which is
`D·(λ - v)² ≥ 0` divided by `λ`, at `λ = (log x)^{C'+k+2}`, summed. It is the same trade with the
optimising parameter written down, and it needs no inner-product space.

## Main results

* `Gap212.Sieve.weighted_error_negligible`: the weighted discrepancy error is `o(𝓒_x)`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.Defs Gap212.GPY

/-! ## Squarefreeness of the generated modulus -/

/-- **The modulus a squarefree tuple generates is squarefree.** `W(x)` is a primorial, hence
squarefree; each `[dᵢ,d'ᵢ]` is squarefree by `Gap212.Sieve.squarefree_lcm`; pairwise coprimality
makes their product squarefree; and coprimality of each factor to `W(x)` closes the last step.

This is the hypothesis every downstream input of the weighted-error estimate asks for, and the
reason the statement restricts the sum to squarefree tuples. -/
theorem squarefree_generated_modulus {m : ℕ} {x : ℝ} {d d' : Fin m → ℕ}
    (hd : ∀ i, Squarefree (d i)) (hd' : ∀ i, Squarefree (d' i))
    (hW : ∀ i, Nat.Coprime ((d i).lcm (d' i)) (W x))
    (hcop : ∀ i i', i ≠ i' → Nat.Coprime ((d i).lcm (d' i)) ((d i').lcm (d' i'))) :
    Squarefree (W x * ∏ i, (d i).lcm (d' i)) := by
  refine Nat.squarefree_mul_iff.mpr ⟨Nat.Coprime.prod_right fun i _ ↦ (hW i).symm,
    squarefree_primorial _, Finset.squarefree_prod_of_pairwise_isCoprime
      (fun i _ i' _ hii ↦ Nat.coprime_iff_isRelPrime.mp (hcop i i' hii)) fun i _ ↦
      squarefree_lcm (hd i) (hd' i)⟩

/-! ## The size of the generated modulus, at the removed coordinate -/

/-- **The modulus a reduced divisor pair generates has exponent below one.**
`Gap212.Sieve.denominator_modulus_exponent` is stated for two families on the *same* index type;
the numerator's families live on the `k - 1` coordinates other than `i₀`, so it is applied here to
the two families extended by `1` at `i₀` — which is the extension by `0` of the logarithmic sizes,
and contributes the factor `[1,1] = 1` to the product.

The exponent is `S = (A_j + ε) + (A_{j'} + ε)`, which
`Gap212.Sieve.denominator_modulus_exponent` also certifies to be `< 1`; that is what puts the
modulus inside the range of `Gap212.Sieve.crude_discrepancy_moment`. -/
theorem generated_modulus_le_rpow {m : ℕ} (p : SupportParams) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) (j j' : Fin p.n) (i₀ : Fin (m + 1)) :
    ∀ᶠ x : ℝ in atTop, ∀ d d' : Fin m → ℕ, (∀ i, 0 < d i) → (∀ i, 0 < d' i) →
      i₀.insertNth 0 (fun i ↦ logScale x (d i)) ∈ retreatRegion p (m + 1) j ε₀ →
      i₀.insertNth 0 (fun i ↦ logScale x (d' i)) ∈ retreatRegion p (m + 1) j' ε₀ →
      ((W x * ∏ i, (d i).lcm (d' i) : ℕ) : ℝ)
        ≤ x ^ ((p.A j.succ + p.ε) + (p.A j'.succ + p.ε)) := by
  filter_upwards [(denominator_modulus_exponent p (m + 1) hε₀ hε₀' j j').2] with x hx d d' hd hd'
    hmem hmem'
  have hext : ∀ e : Fin m → ℕ, (∀ i, 0 < e i) →
      (∀ i, 0 < (i₀.insertNth 1 e : Fin (m + 1) → ℕ) i) ∧
      (fun i ↦ logScale x ((i₀.insertNth 1 e : Fin (m + 1) → ℕ) i))
        = i₀.insertNth 0 (fun i ↦ logScale x (e i)) := fun e he ↦
    ⟨by refine Fin.succAboveCases i₀ ?_ ?_ <;> simp [he], funext fun i ↦ by
      refine Fin.succAboveCases i₀ ?_ ?_ i <;> simp [Gap212.logScale]⟩
  have hmain := hx _ _ (hext d hd).1 (hext d' hd').1 (by rwa [(hext d hd).2])
    (by rwa [(hext d' hd').2])
  rw [Fin.prod_univ_succAbove _ i₀] at hmain
  simpa using hmain

/-! ## The weighted discrepancy error -/

/-- **The weighted discrepancy error is negligible.** Let `p` be a support datum with `ε < A_j`,
let `ε₀ ∈ (0,1)`, let `j, j'` be bands, let `i₀` be the removed coordinate of a strictly monotone
tuple `h` of dimension `k = 45`, let `ρ` satisfy the minorant hypotheses and equidistribute over
the moduli `p` generates, and let `(Fᵢ)_{i≠i₀}` and `(Gᵢ)_{i≠i₀}` be bounded by `M` and
`i₀`-retreated at `(j,j',ε₀)`. Then for every `ε > 0` and every large `x`, every pre-sieved `b`,
every finite family `𝒯` of divisor tuples with all `dᵢ, d'ᵢ` **squarefree** and the `[dᵢ,d'ᵢ]`
pairwise coprime and coprime to `W(x)`, and every choice `A` of tuple residues on `𝒯`,
`∑_{𝒯}|∏ᵢFᵢ(log_x dᵢ)Gᵢ(log_x d'ᵢ)|·‖Δ_𝒟(ρ(·;x);x,W(x)∏ᵢ[dᵢ,d'ᵢ],A(d,d'))‖ ≤ ε·𝓒_x`.

Without the squarefree hypothesis the statement is false; see the module docstring, which also
discusses the form of the remaining hypotheses.

The proof groups the tuples by their modulus, paying
`Gap212.Sieve.card_tuple_multiplicity` for the grouping and the density of
`Gap212.Sieve.exists_averaging_sample` for the passage to the sample's residues; the product of the
two multiplicities is exactly `Gap212.GPY.residueWeight`, which is where `k = 45` enters and is why
`hm` is not dispensable. The trade of the crude moment against the equidistribution bound is a
pointwise `D(λ - v)² ≥ 0` at `λ = (log x)^{C'+m+3}` rather than Cauchy–Schwarz. -/
@[gap212 "lem_weighted_error_negligible"]
theorem weighted_error_negligible {m : ℕ} (hm : m = 44) (p : SupportParams) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) (j j' : Fin p.n) (hA : p.ε < p.A j.succ)
    (i₀ : Fin (m + 1)) {h : Fin (m + 1) → ℕ} (hmono : StrictMono h)
    {ρ : ℕ → ℝ → ℝ} {β : ℝ} (hρ : RhoHypotheses p ρ β)
    (heq : HasEquidistributionOverQstarFamily p fun n x ↦ ((ρ n x : ℝ) : ℂ))
    {F G : Fin m → ℝ → ℝ} {M : ℝ} (hF : ∀ i t, |F i t| ≤ M) (hG : ∀ i t, |G i t| ≤ M)
    (hsupp : IsReducedRetreat p m j j' ε₀ i₀ F G) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ b : ℕ, IsPreSieved b (W x) h →
      ∀ (𝒯 : Finset ((Fin m → ℕ) × (Fin m → ℕ))) (A : (Fin m → ℕ) × (Fin m → ℕ) → ℕ),
        (∀ dd ∈ 𝒯, (∀ i, Squarefree (dd.1 i)) ∧ (∀ i, Squarefree (dd.2 i)) ∧
            (∀ i, Nat.Coprime ((dd.1 i).lcm (dd.2 i)) (W x)) ∧
            (∀ i i', i ≠ i' → Nat.Coprime ((dd.1 i).lcm (dd.2 i)) ((dd.1 i').lcm (dd.2 i'))) ∧
            IsTupleResidue x b h i₀ dd.1 dd.2 (A dd)) →
        ∑ dd ∈ 𝒯, |∏ i, F i (logScale x (dd.1 i)) * G i (logScale x (dd.2 i))| *
            ‖sumErrorDyadic x (fun n ↦ ((ρ n x : ℝ) : ℂ))
              (W x * ∏ i, (dd.1 i).lcm (dd.2 i)) (A dd)‖ ≤ ε * calC m x := by
  classical
  subst hm
  -- The numerator is at most `M^{2(k-1)}`.
  have hnum : ∀ u v : Fin 44 → ℝ, |∏ i, F i (u i) * G i (v i)| ≤ M ^ 88 := fun u v ↦ by
    rw [Finset.abs_prod]
    calc ∏ i, |F i (u i) * G i (v i)| ≤ ∏ _i : Fin 44, M * M :=
          Finset.prod_le_prod (fun i _ ↦ abs_nonneg _) fun i _ ↦
            (abs_mul _ _).trans_le
              (mul_le_mul (hF i _) (hG i _) (abs_nonneg _) ((abs_nonneg _).trans (hF 0 0)))
      _ = M ^ 88 := by simp [← sq, ← pow_mul]
  -- `C'` first, then the saving `A = C' + 94`, then the equidistribution constant `c`.
  obtain ⟨hS1, -⟩ := denominator_modulus_exponent p 45 hε₀ hε₀' j j'
  have hρ1 : ∀ᶠ x : ℝ in atTop, ∀ n ∈ dyadic x, 0 ≤ ρ n x ∧ ρ n x ≤ 1 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx n hn
    obtain ⟨h1, h2⟩ := hρ.minorant x hx n hn
    refine ⟨h1, h2.trans ?_⟩
    split_ifs <;> norm_num
  obtain ⟨C', X, hC'⟩ := crude_discrepancy_moment hS1 hρ1
  obtain ⟨c, hcpos, hc⟩ := heq (ε₀ / 2) (by positivity) ((C' + 94 : ℕ) : ℝ)
    (by exact_mod_cast (by omega : 0 < C' + 94))
  filter_upwards [generated_modulus_mem_Qstar p 44 hε₀ hε₀' j j' hA i₀,
    generated_modulus_le_rpow p hε₀ hε₀' j j' i₀,
    eventually_dvd_W_of_prime_le (Finset.image h Finset.univ).diameter,
    calC_lower_bound 44, eventually_ge_atTop X, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (M ^ 88 * ((c + 1) / 2) / ε))]
    with x hQgen hQsize hDdvd hcalC hxX hx1 hLge b hb 𝒯 A hadm
  have hL0 : (0 : ℝ) < Real.log x := zero_lt_one.trans_le ((le_max_left _ _).trans hLge)
  have hKL : M ^ 88 * ((c + 1) / 2) / ε ≤ Real.log x := le_trans (le_max_right _ _) hLge
  have hWpos : 0 < W x := primorial_pos _
  have hxS : x ^ ((p.A j.succ + p.ε) + (p.A j'.succ + p.ε)) ≤ x :=
    (Real.rpow_le_rpow_of_exponent_le hx1.le hS1.le).trans_eq (Real.rpow_one x)
  -- The sample of residues, and the three abbreviations the bookkeeping is written in.
  obtain ⟨𝓑, hBne, hBcop, hBcount⟩ :=
    exists_averaging_sample (m := 44) (by norm_num) hmono i₀ b hb hDdvd
  obtain ⟨Dl, hDl⟩ : ∃ Dl : ℕ → ℕ → ℝ, ∀ q a : ℕ,
      Dl q a = ‖sumErrorDyadic x (fun n ↦ ((ρ n x : ℝ) : ℂ)) q a‖ := ⟨_, fun _ _ ↦ rfl⟩
  obtain ⟨Qm, hQm⟩ : ∃ Qm : (Fin 44 → ℕ) × (Fin 44 → ℕ) → ℕ,
      ∀ dd, Qm dd = W x * ∏ i, (dd.1 i).lcm (dd.2 i) := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨Num, hNum⟩ : ∃ Num : (Fin 44 → ℕ) × (Fin 44 → ℕ) → ℝ,
      ∀ dd, Num dd = ∏ i, F i (logScale x (dd.1 i)) * G i (logScale x (dd.2 i)) :=
    ⟨_, fun _ ↦ rfl⟩
  have hDlnn : ∀ q a, 0 ≤ Dl q a := fun q a ↦ by rw [hDl]; exact norm_nonneg _
  simp only [← hQm, ← hNum, ← hDl]
  set 𝒯' : Finset ((Fin 44 → ℕ) × (Fin 44 → ℕ)) := {dd ∈ 𝒯 | Num dd ≠ 0} with hT'def
  set Qs : Finset ℕ := 𝒯'.image Qm with hQsdef
  -- Everything the grouping needs about one tuple with a non-zero numerator.
  have hfacts : ∀ dd ∈ 𝒯', Squarefree (Qm dd) ∧ W x ∣ Qm dd ∧
      ((Qm dd : ℕ) : ℝ) ≤ x ^ ((p.A j.succ + p.ε) + (p.A j'.succ + p.ε)) ∧
      Qm dd ∈ Qstar p x (ε₀ / 2) ∧
      #{a ∈ 𝓑 | a ≡ A dd [MOD Qm dd]} * 44 ^ (Qm dd / W x).primeFactors.card = 𝓑.card := by
    intro dd hdd
    obtain ⟨hddT, hnz⟩ := Finset.mem_filter.mp hdd
    obtain ⟨hd1, hd2, hWc, hcop, htres⟩ := hadm dd hddT
    have hd1pos : ∀ i, 0 < dd.1 i := fun i ↦ Nat.pos_of_ne_zero (hd1 i).ne_zero
    have hd2pos : ∀ i, 0 < dd.2 i := fun i ↦ Nat.pos_of_ne_zero (hd2 i).ne_zero
    have hts : ∀ n : ℕ, 0 < n → 0 ≤ logScale x n := fun n hn ↦
      div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (Real.log_nonneg hx1.le)
    rw [hNum, Finset.prod_mul_distrib] at hnz
    obtain ⟨hnzF, hnzG⟩ := mul_ne_zero_iff.mp hnz
    obtain ⟨hret1, hmarg1⟩ := (hsupp _ fun i ↦ hts _ (hd1pos i)).1 hnzF
    have hret2 := (hsupp _ fun i ↦ hts _ (hd2pos i)).2 hnzG
    have hsize := hQsize dd.1 dd.2 hd1pos hd2pos hret1 hret2
    have hsf' := squarefree_generated_modulus hd1 hd2 hWc hcop
    have hdiv : Qm dd / W x = ∏ i, (dd.1 i).lcm (dd.2 i) := by
      rw [hQm, Nat.mul_div_cancel_left _ hWpos]
    obtain ⟨hcW, -, hsfP⟩ := Nat.squarefree_mul_iff.mp hsf'
    refine ⟨?_, ?_, ?_, ?_, hBcount (Qm dd) dd.1 dd.2 (A dd) ?_ (hQm dd) (by rwa [hdiv])
      (by rw [hdiv]; exact hcW.symm) htres⟩ <;> rw [hQm]
    exacts [hsf', dvd_mul_right _ _, hsize, hQgen dd.1 dd.2 hd1pos hd2pos hret1 hmarg1 hret2,
      hsize.trans hxS]
  have hQsfacts : ∀ q ∈ Qs, Squarefree q ∧ W x ∣ q ∧
      (q : ℝ) ≤ x ^ ((p.A j.succ + p.ε) + (p.A j'.succ + p.ε)) ∧ q ∈ Qstar p x (ε₀ / 2) := by
    intro q hq
    obtain ⟨dd, hdd, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨h1, h2, h3, h4, -⟩ := hfacts dd hdd
    exact ⟨h1, h2, h3, h4⟩
  have hsub1 : Qs ⊆ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x (ε₀ / 2) ∧ Squarefree q} := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := hQsfacts q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr h1.ne_zero,
      Nat.le_floor (le_trans h3 hxS)⟩, h4, h1⟩
  have hsub2 : Qs ⊆ {q ∈ Finset.Icc 1 ⌊x ^ ((p.A j.succ + p.ε) + (p.A j'.succ + p.ε))⌋₊ |
      W x ∣ q ∧ Squarefree q} := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := hQsfacts q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr h1.ne_zero,
      Nat.le_floor h3⟩, h2, h1⟩
  -- The trade: one pointwise `D(λ - v)² ≥ 0` at `λ = (log x)^{C'+47}`, summed.
  have hkey : ∀ a ∈ 𝓑, ∑ q ∈ Qs, (residueWeight x q : ℝ) * Dl q a
      ≤ (c + 1) / 2 * (x / Real.log x ^ 47) := by
    intro a ha
    have hLp : (0 : ℝ) < Real.log x ^ (C' + 47) := pow_pos hL0 _
    have h1 : ∑ q ∈ Qs, Dl q a ≤ c * x / Real.log x ^ (C' + 94) :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun q _ _ ↦ hDlnn q a).trans <| by
        simpa only [hDl, Gap212.sumErrorDyadic, Real.rpow_natCast] using hc x hx1 a (hBcop a ha)
    have h2 : ∑ q ∈ Qs, (residueWeight x q : ℝ) ^ 2 * Dl q a ≤ x * Real.log x ^ C' :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun q _ _ ↦
        mul_nonneg (by positivity) (hDlnn q a)).trans <| by simpa only [hDl] using hC' x hxX a
    have hpt : ∀ q : ℕ, (residueWeight x q : ℝ) * Dl q a
        ≤ (Real.log x ^ (C' + 47) * Dl q a
          + (residueWeight x q : ℝ) ^ 2 * Dl q a / Real.log x ^ (C' + 47)) / 2 := by
      intro q
      rw [le_div_iff₀ two_pos, ← sub_nonneg]
      convert div_nonneg (mul_nonneg (hDlnn q a)
        (sq_nonneg (Real.log x ^ (C' + 47) - residueWeight x q))) hLp.le using 1
      field_simp
      ring
    calc ∑ q ∈ Qs, (residueWeight x q : ℝ) * Dl q a
        ≤ ∑ q ∈ Qs, (Real.log x ^ (C' + 47) * Dl q a
            + (residueWeight x q : ℝ) ^ 2 * Dl q a / Real.log x ^ (C' + 47)) / 2 :=
          Finset.sum_le_sum fun q _ ↦ hpt q
      _ = (Real.log x ^ (C' + 47) * ∑ q ∈ Qs, Dl q a
            + (∑ q ∈ Qs, (residueWeight x q : ℝ) ^ 2 * Dl q a)
              / Real.log x ^ (C' + 47)) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
      _ ≤ (Real.log x ^ (C' + 47) * (c * x / Real.log x ^ (C' + 94))
            + x * Real.log x ^ C' / Real.log x ^ (C' + 47)) / 2 := by gcongr
      _ = (c + 1) / 2 * (x / Real.log x ^ 47) := by
          rw [show C' + 94 = C' + 47 + 47 by omega, pow_add]
          field_simp
          ring
  -- The grouping by modulus, and the two multiplicities paid into `v(q)`.
  obtain ⟨gfn, hgfn⟩ : ∃ gfn : ℕ → ℝ, ∀ q,
      gfn q = (44 : ℝ) ^ (q / W x).primeFactors.card * ∑ a ∈ 𝓑, Dl q a := ⟨_, fun _ ↦ rfl⟩
  have hgfnn : ∀ q, 0 ≤ gfn q := fun q ↦
    hgfn q ▸ mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ ↦ hDlnn q a)
  have hstep1 : ∀ dd ∈ 𝒯', |Num dd| * Dl (Qm dd) (A dd)
      ≤ M ^ 88 / (𝓑.card : ℝ) * gfn (Qm dd) := by
    intro dd hdd
    obtain ⟨-, -, -, -, hcount⟩ := hfacts dd hdd
    calc |Num dd| * Dl (Qm dd) (A dd)
        ≤ M ^ 88 * (((44 ^ (Qm dd / W x).primeFactors.card : ℕ) : ℝ) / (𝓑.card : ℝ)
            * ∑ a ∈ 𝓑, Dl (Qm dd) a) :=
          mul_le_mul (hNum dd ▸ hnum _ _)
            (by simpa only [hDl] using norm_sumErrorDyadic_le_sample_average hBne hcount)
            (hDlnn _ _) (by positivity)
      _ = M ^ 88 / (𝓑.card : ℝ) * gfn (Qm dd) := by
          rw [hgfn]
          push_cast
          ring
  have hgroup : ∑ dd ∈ 𝒯', gfn (Qm dd)
      ≤ ∑ q ∈ Qs, (132 : ℝ) ^ (q / W x).primeFactors.card * gfn q := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (show ∀ dd ∈ 𝒯', Qm dd ∈ Qs from fun dd hdd ↦ Finset.mem_image_of_mem Qm hdd)
      fun dd ↦ gfn (Qm dd)]
    refine Finset.sum_le_sum fun q hq ↦ ?_
    have hfib : ∑ dd ∈ 𝒯' with Qm dd = q, gfn (Qm dd)
        = (#{dd ∈ 𝒯' | Qm dd = q} : ℝ) * gfn q := by
      rw [Finset.sum_congr rfl (fun dd hdd ↦ by rw [(Finset.mem_filter.mp hdd).2]),
        Finset.sum_const, nsmul_eq_mul]
    rw [hfib]
    refine mul_le_mul_of_nonneg_right ?_ (hgfnn q)
    obtain ⟨hsf, hWdvd, -, -⟩ := hQsfacts q hq
    obtain ⟨hfin, hncard⟩ := card_tuple_multiplicity (m := 44) (by norm_num) hsf hWdvd
    have hsubset : (↑{dd ∈ 𝒯' | Qm dd = q} : Set ((Fin 44 → ℕ) × (Fin 44 → ℕ)))
        ⊆ {dd : (Fin 44 → ℕ) × (Fin 44 → ℕ) | (∀ i, 0 < dd.1 i) ∧ (∀ i, 0 < dd.2 i) ∧
            W x * ∏ i, Nat.lcm (dd.1 i) (dd.2 i) = q} := by
      intro dd hdd
      obtain ⟨hdd1, hdd2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hdd)
      obtain ⟨hd1, hd2, -, -, -⟩ := hadm dd (Finset.mem_filter.mp hdd1).1
      exact ⟨fun i ↦ Nat.pos_of_ne_zero (hd1 i).ne_zero,
        fun i ↦ Nat.pos_of_ne_zero (hd2 i).ne_zero, (hQm dd).symm.trans hdd2⟩
    have hcard : (#{dd ∈ 𝒯' | Qm dd = q} : ℕ) ≤ 132 ^ (q / W x).primeFactors.card := by
      rw [← Set.ncard_coe_finset]
      exact (Set.ncard_le_ncard hsubset hfin).trans hncard
    exact_mod_cast hcard
  have hv : ∀ q : ℕ, (132 : ℝ) ^ (q / W x).primeFactors.card * gfn q
      = (residueWeight x q : ℝ) * ∑ a ∈ 𝓑, Dl q a := by
    intro q
    rw [hgfn, ← mul_assoc, ← mul_pow]
    congr 1
    rw [residueWeight]
    push_cast
    norm_num
  have hswap : ∑ q ∈ Qs, (residueWeight x q : ℝ) * ∑ a ∈ 𝓑, Dl q a
      = ∑ a ∈ 𝓑, ∑ q ∈ Qs, (residueWeight x q : ℝ) * Dl q a := by
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  -- Only the tuples with a non-zero numerator contribute.
  have hzero : ∀ dd ∈ 𝒯, dd ∉ 𝒯' → |Num dd| * Dl (Qm dd) (A dd) = 0 := fun dd hdd hnot ↦ by
    rw [not_not.mp fun hne ↦ hnot (Finset.mem_filter.mpr ⟨hdd, hne⟩), abs_zero, zero_mul]
  rw [← Finset.sum_subset (Finset.filter_subset _ _) hzero]
  have hMB : (0 : ℝ) ≤ M ^ 88 / (𝓑.card : ℝ) := by positivity
  rw [div_le_iff₀ hε] at hKL
  calc ∑ dd ∈ 𝒯', |Num dd| * Dl (Qm dd) (A dd)
      ≤ ∑ dd ∈ 𝒯', M ^ 88 / (𝓑.card : ℝ) * gfn (Qm dd) := Finset.sum_le_sum hstep1
    _ = M ^ 88 / (𝓑.card : ℝ) * ∑ dd ∈ 𝒯', gfn (Qm dd) := by rw [Finset.mul_sum]
    _ ≤ M ^ 88 / (𝓑.card : ℝ) * ∑ q ∈ Qs, (132 : ℝ) ^ (q / W x).primeFactors.card * gfn q :=
        mul_le_mul_of_nonneg_left hgroup hMB
    _ = M ^ 88 / (𝓑.card : ℝ) * ∑ a ∈ 𝓑, ∑ q ∈ Qs, (residueWeight x q : ℝ) * Dl q a := by
        rw [Finset.sum_congr rfl fun q _ ↦ hv q, hswap]
    _ ≤ M ^ 88 / (𝓑.card : ℝ) * ∑ _a ∈ 𝓑, (c + 1) / 2 * (x / Real.log x ^ 47) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hkey) hMB
    _ = M ^ 88 * ((c + 1) / 2) / Real.log x * (x / Real.log x ^ 46) := by
        rw [Finset.sum_const, nsmul_eq_mul, show (47 : ℕ) = 46 + 1 from rfl, pow_succ]
        field_simp
    _ ≤ ε * (x / Real.log x ^ 46) :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hL0).mpr (by linarith)) (by positivity)
    _ ≤ ε * calC 44 x := mul_le_mul_of_nonneg_left (by simpa using hcalC.1) hε.le

end Gap212.Sieve
