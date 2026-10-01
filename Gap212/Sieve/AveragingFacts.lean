/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Main
public import Gap212.Sieve.DivisorSumFacts
public import Gap212.Sieve.RetreatFacts
public import Gap212.Routing.Defs.Equidistribution
public import PrimeGapsTheory.ArithmeticFunction.Estimates
public import Mathlib.Data.ZMod.QuotientRing
public meta import Gap212.Attr

/-!
# The generated moduli, and the common-residue averaging

Three independent pieces of the sieve's divisor-sum endgame: the modulus a divisor tuple generates
lies in the support's family; one sample of residues detects every tuple residue at an exact
density; and the weighted discrepancy has a crude moment bound with no distribution input at all.

These are assembled into the weighted error bound by `Gap212.Sieve.weighted_error_negligible`,
over squarefree moduli: every input below — the tuple multiplicity, the weight bound by a power of
`τ`, `Gap212.Sieve.crude_discrepancy_moment`, and the equidistribution clause of
`Gap212.Defs.RhoHypotheses` — is available only for squarefree `q = W(x)∏ᵢ[dᵢ,d'ᵢ]`.

## The generated moduli

A divisor tuple supported in the retreat and marginal regions generates a modulus of the family
`Gap212.Qstar`. The mechanism is a sorting: a divisor reaching `x^δ` is kept as a rough factor of
`Gap212.Qgen`, every smaller one is `x^δ`-smooth and is swept into the smooth part, and `W(x)` —
which is only `log x` — is swept in with them. The `x^{ε₀/2}` that absorbing `W(x)` costs is paid
out of half the retreat, which is why the conclusion is at `ε₀/2`, and why the hypothesis
`ε < A_j` cannot be dropped: with `A_j ≤ ε` the first mixed bound of `Gap212.Qgen` has a
non-positive exponent and forces `e·∏fᵢ = 1`, which `W(x) > 1` already violates.

## The averaging sample

One finite set `𝓑` of residues, all coprime below `x`, hitting the residue class of *every* divisor
tuple with the exact density `(k-1)^{-ω(q/W(x))}`. This is what lets a theorem about one common
residue class serve the many classes the divisor expansion produces. The set is built by the
Chinese remainder theorem from a free choice, at each prime `ℓ ≤ x` not dividing `W(x)`, of one of
the `k-1` residues `h_{i₀} - h_i`; the exact count is then a count of choice functions, the
constrained ones being those pinned at the `ω(q/W(x))` primes of `q/W(x)`.

## Main results

* `Gap212.Sieve.generated_modulus_mem_Qstar`: the modulus a divisor tuple generates lies in `Q*`.
* `Gap212.Sieve.exists_averaging_sample`: the averaging sample and its counting identity.
* `Gap212.Sieve.crude_discrepancy_moment`: the crude weighted discrepancy moment bound.
* `Gap212.Sieve.norm_sumErrorDyadic_le_sample_average`: the averaging step the sample buys.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.Defs Gap212.GPY

/-! ## Sorting a divisor family into rough and smooth -/

/-- `[a,b] = a·(b/(a,b))`: the least common multiple splits off the part of `b` not already in `a`.
This is the factorization the generated moduli ask for, read one coordinate at a time. -/
theorem lcm_eq_mul_div_gcd {a b : ℕ} (ha : 0 < a) : a.lcm b = a * (b / a.gcd b) := by
  refine Nat.eq_of_mul_eq_mul_right (Nat.gcd_pos_of_pos_left b ha) ?_
  rw [mul_assoc, Nat.div_mul_cancel (Nat.gcd_dvd_right a b), Nat.lcm_mul_gcd]

/-- A positive natural is `x` to its own logarithmic size. -/
theorem cast_eq_rpow_logScale {x : ℝ} (hx : 1 < x) {d : ℕ} (hd : 0 < d) :
    (d : ℝ) = x ^ logScale x (d : ℝ) :=
  (Gap212.rpow_logScale hx (by exact_mod_cast hd)).symm

/-- A product of positive naturals is `x` to the sum of their logarithmic sizes. -/
theorem prod_cast_eq_rpow_sum {x : ℝ} (hx : 1 < x) {n : ℕ} {D : Fin n → ℕ} (hD : ∀ i, 0 < D i)
    (A : Finset (Fin n)) : ∏ i ∈ A, (D i : ℝ) = x ^ (∑ i ∈ A, logScale x (D i)) := by
  rw [Real.rpow_sum_of_pos (by linarith) _ A]
  exact prod_congr rfl fun i _ ↦ cast_eq_rpow_logScale hx (hD i)

/-- Logarithmic size is monotone in the integer, at a base above `1`. -/
theorem logScale_le_logScale {x : ℝ} (hx : 1 < x) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    logScale x (a : ℝ) ≤ logScale x (b : ℝ) := by
  unfold Gap212.logScale
  gcongr
  exact (Real.log_pos hx).le

variable {p : SupportParams}

/-- **One side of the sorting.** Let `E` be a family of positive integers dominated by a family `F`
whose logarithmic sizes are non-negative, sum to at most `M ≤ 1`, and obey the rough-mass cap of
band `j` at scale `c`. Write `J` for the rough indices of `E` — those with `x^δ ≤ Eᵢ`. Then

* the rough product `∏_{i ∈ J} Eᵢ` obeys the same cap at `J`'s own cardinality;
* `#J` is at most `⌊1/δ⌋`, so `J` is one of the rough-factor counts `Q*` unions over;
* the whole product `∏ᵢEᵢ` is at most `x^M`;
* each retained factor reaches `x^δ` and each discarded one falls strictly below it.

Both sides of the generated modulus are instances: the unprimed one at `E = F = (dᵢ)`, the primed
one at `E = (d'ᵢ/(dᵢ,d'ᵢ))` and `F = (d'ᵢ)`, where the passage to the quotient only shrinks the
coordinates and so preserves both the cap and the total. -/
theorem rough_smooth_split {n : ℕ} {x c M : ℝ} (hx : 1 < x) (j : Fin p.n)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hM : M ≤ 1) {E F : Fin n → ℕ}
    (hE : ∀ i, 0 < E i) (hEF : ∀ i, E i ≤ F i)
    (hnn : ∀ i, 0 ≤ logScale x (F i))
    (hcap : ∑ i ∈ p.roughIdx n (fun i ↦ logScale x (F i)), logScale x (F i)
      ≤ c * p.B j (p.roughIdx n fun i ↦ logScale x (F i)).card)
    (htot : ∑ i, logScale x (F i) ≤ M)
    {J : Finset (Fin n)} (hJ : J = p.roughIdx n fun i ↦ logScale x (E i)) :
    (∏ i ∈ J, (E i : ℝ)) ≤ x ^ (c * p.B j J.card) ∧ J.card ≤ ⌊1 / p.δ⌋₊ ∧
      (∏ i, (E i : ℝ)) ≤ x ^ M ∧ (∀ i ∈ J, x ^ p.δ ≤ (E i : ℝ)) ∧
      (∀ i, i ∉ J → (E i : ℝ) < x ^ p.δ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hF : ∀ i, 0 < F i := fun i ↦ lt_of_lt_of_le (hE i) (hEF i)
  -- Passing from `E` to `F` only increases each logarithmic size.
  have hmono : ∀ i, logScale x (E i) ≤ logScale x (F i) := fun i ↦
    logScale_le_logScale hx (hE i) (hEF i)
  subst hJ
  set J := p.roughIdx n (fun i ↦ logScale x (E i)) with hJ
  set K := p.roughIdx n (fun i ↦ logScale x (F i)) with hK
  have hsub : J ⊆ K := fun i hi ↦
    SupportParams.mem_roughIdx_iff.mpr
      ((SupportParams.mem_roughIdx_iff.mp hi).trans (hmono i))
  -- The rough mass of `J`, measured with `E`, is below the cap at `#J`.
  have hJcap : ∑ i ∈ J, logScale x (E i) ≤ c * p.B j J.card := by
    refine le_trans (sum_le_sum fun i _ ↦ hmono i) ?_
    exact p.sum_le_B_of_subset_rough hc0 hc1
      (fun i hi ↦ SupportParams.mem_roughIdx_iff.mp hi) hcap hsub
  -- The rough mass of `J` is also below the global total, hence below `1`.
  have hJtot : ∑ i ∈ J, logScale x (E i) ≤ M :=
    le_trans (le_trans (sum_le_sum fun i _ ↦ hmono i)
      (sum_le_sum_of_subset_of_nonneg (subset_univ J) fun i _ _ ↦ hnn i)) htot
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [prod_cast_eq_rpow_sum hx hE]
    exact Real.rpow_le_rpow_of_exponent_le hx.le hJcap
  · -- `#J · δ ≤ ∑_{i ∈ J} logScale Eᵢ ≤ M ≤ 1`, so `#J ≤ 1/δ`.
    have hlow := card_nsmul_le_sum J _ _ fun i hi ↦ SupportParams.mem_roughIdx_iff.mp hi
    rw [nsmul_eq_mul] at hlow
    refine Nat.le_floor ?_
    rw [le_div_iff₀ p.δ_pos]
    linarith
  · rw [prod_cast_eq_rpow_sum hx hE]
    exact Real.rpow_le_rpow_of_exponent_le hx.le (le_trans (sum_le_sum fun i _ ↦ hmono i) htot)
  · intro i hi
    rw [cast_eq_rpow_logScale hx (hE i)]
    exact Real.rpow_le_rpow_of_exponent_le hx.le (SupportParams.mem_roughIdx_iff.mp hi)
  · intro i hi
    rw [cast_eq_rpow_logScale hx (hE i)]
    exact Real.rpow_lt_rpow_left_iff hx |>.mpr
      (not_le.mp fun h ↦ hi (SupportParams.mem_roughIdx_iff.mpr h))

/-! ## The generated modulus lies in the support's family -/

/-- **A divisor tuple generates a modulus of the support.** Fix a band pair `(j, j')` with
`ε < A_j`, a retreat `ε₀ ∈ (0,1)` and a removed coordinate `i₀`. Let `(dᵢ)` and `(d'ᵢ)` be positive
integers whose logarithmic sizes, extended by `0` at `i₀`, lie in the retreat region of `j` and of
`j'` respectively, the unprimed vector lying in addition in the marginal region of `j`. Then for
all large `x`,
`W(x)·∏ᵢ[dᵢ,d'ᵢ] ∈ Q*(p, x, ε₀/2)`.

The factorization is `q = (W(x)∏ᵢdᵢ)·∏ᵢ(d'ᵢ/(dᵢ,d'ᵢ))`, sorted by
`Gap212.Sieve.rough_smooth_split` into the rough factors reaching `x^δ` and an `x^δ`-smooth
remainder; `W(x) ≤ log x < x^δ` joins the smooth remainder, at the cost of `x^{(ε₀/2)(A_j - ε)}`
against the first mixed bound. That cost is payable only because `A_j - ε > 0`, which is the
hypothesis `hA`.

Pairwise coprimality of the `[dᵢ,d'ᵢ]`, and their coprimality to `W(x)`, are not used: the
factorization is coordinatewise and the bounds are multiplicative, so the statement here drops
both. -/
@[gap212 "lem_generated_modulus_in_qstar"]
theorem generated_modulus_mem_Qstar (p : SupportParams) (m : ℕ) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) (j j' : Fin p.n) (hA : p.ε < p.A j.succ)
    (i₀ : Fin (m + 1)) :
    ∀ᶠ x : ℝ in atTop, ∀ d d' : Fin m → ℕ, (∀ i, 0 < d i) → (∀ i, 0 < d' i) →
      i₀.insertNth 0 (fun i ↦ logScale x (d i)) ∈ retreatRegion p (m + 1) j ε₀ →
      (fun i ↦ logScale x (d i)) ∈ marginalRegion p m j ε₀ →
      i₀.insertNth 0 (fun i ↦ logScale x (d' i)) ∈ retreatRegion p (m + 1) j' ε₀ →
      W x * ∏ i, (d i).lcm (d' i) ∈ Qstar p x (ε₀ / 2) := by
  -- Each band's node, shifted by `ε`, is below `1/2`.
  have node (b : Fin p.n) : 0 < p.A b.succ + p.ε ∧ p.A b.succ + p.ε < 1 / 2 := by
    have := p.A_mono (Fin.succ_pos b)
    have := p.A_mono.monotone (Fin.le_last b.succ)
    constructor <;> linarith [p.A_zero, p.A_last, p.ε_pos]
  have hApos : 0 < p.A j.succ - p.ε := by linarith
  -- The two powers of `x` the smooth part is absorbed into.
  have hpow (r : ℝ) (hr : 0 < r) : ∀ᶠ x : ℝ in atTop, Real.log x < x ^ r := by
    have hb := (isLittleO_log_rpow_atTop (r := r) hr).bound (c := 1 / 2) (by norm_num)
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hp : (0 : ℝ) < x ^ r := Real.rpow_pos_of_pos (by linarith) _
    have hhalf : Real.log x ≤ 1 / 2 * x ^ r := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1), abs_of_pos hp] using hx
    linarith
  filter_upwards [W_le_log, hpow ((ε₀ / 2) * (p.A j.succ - p.ε)) (by positivity),
    hpow p.δ p.δ_pos, eventually_gt_atTop (1 : ℝ)] with x hWL hmixpow hsmpow hx1
    d d' hd hd' hmem hmarg hmem'
  have hx0 : (0 : ℝ) < x := by linarith
  have hWpos : 0 < W x := primorial_pos _
  -- The three families: the unprimed divisors, the primed ones, and the primed quotients, all
  -- extended by `1` at the removed coordinate so that they live on `Fin (m+1)`.
  set D : Fin (m + 1) → ℕ := i₀.insertNth 1 d with hDdef
  set D₂ : Fin (m + 1) → ℕ := i₀.insertNth 1 d' with hD₂def
  set D₁ : Fin (m + 1) → ℕ := fun i ↦ D₂ i / (D i).gcd (D₂ i) with hD₁def
  have hDpos : ∀ i, 0 < D i := by
    refine Fin.succAboveCases i₀ ?_ ?_ <;> simp [hDdef, hd]
  have hD₂pos : ∀ i, 0 < D₂ i := by
    refine Fin.succAboveCases i₀ ?_ ?_ <;> simp [hD₂def, hd']
  have hgpos : ∀ i, 0 < (D i).gcd (D₂ i) := fun i ↦ Nat.gcd_pos_of_pos_left _ (hDpos i)
  have hD₁le : ∀ i, D₁ i ≤ D₂ i := fun i ↦ Nat.div_le_self _ _
  have hD₁pos : ∀ i, 0 < D₁ i := fun i ↦
    Nat.div_pos (Nat.le_of_dvd (hD₂pos i) (Nat.gcd_dvd_right _ _)) (hgpos i)
  -- The extension by `1` is the extension by `0` of the logarithmic sizes.
  have hTD : (i₀.insertNth 0 (fun i ↦ logScale x (d i)) : Fin (m + 1) → ℝ)
      = fun i ↦ logScale x (D i) := by
    funext i
    refine Fin.succAboveCases i₀ ?_ ?_ i <;> simp [hDdef, Gap212.logScale]
  have hTD₂ : (i₀.insertNth 0 (fun i ↦ logScale x (d' i)) : Fin (m + 1) → ℝ)
      = fun i ↦ logScale x (D₂ i) := by
    funext i
    refine Fin.succAboveCases i₀ ?_ ?_ i <;> simp [hD₂def, Gap212.logScale]
  rw [hTD] at hmem
  rw [hTD₂] at hmem'
  -- The marginal bound, read on `Fin (m+1)`.
  have hsumD : ∑ i, logScale x (D i) = ∑ i : Fin m, logScale x (d i) := by
    rw [Fin.sum_univ_succAbove (fun i ↦ logScale x (D i)) i₀]
    simp [hDdef, Gap212.logScale]
  have hmargD : ∑ i, logScale x (D i) ≤ (1 - ε₀) * (p.A j.succ - p.ε) := hsumD ▸ hmarg.le
  -- Both sides of the sorting.
  set J := p.roughIdx (m + 1) (fun i ↦ logScale x (D i)) with hJdef
  set J' := p.roughIdx (m + 1) (fun i ↦ logScale x (D₁ i)) with hJ'def
  have hc0 : (0 : ℝ) ≤ 1 - ε₀ := by linarith
  have hc1 : (1 : ℝ) - ε₀ ≤ 1 := by linarith
  obtain ⟨hcapJ, hcardJ, htotJ, hroughJ, hsmoothJ⟩ :=
    rough_smooth_split hx1 j hc0 hc1
      (M := (1 - ε₀) * (p.A j.succ - p.ε))
      (by nlinarith [(node j).2, mul_nonneg hε₀.le hApos.le, p.ε_pos]) hDpos (fun i ↦ le_refl _)
      (fun i ↦ (hmem.1 i).1) hmem.2.2 hmargD hJdef
  obtain ⟨hcapJ', hcardJ', htotJ', hroughJ', hsmoothJ'⟩ :=
    rough_smooth_split hx1 j' hc0 hc1
      (M := (1 - ε₀) * (p.A j'.succ + p.ε))
      (by nlinarith [(node j').2, mul_nonneg hε₀.le (node j').1.le]) hD₁pos hD₁le
      (fun i ↦ (hmem'.1 i).1) hmem'.2.2 (le_of_lt hmem'.2.1) hJ'def
  -- The two rough-factor families, reindexed by `Fin #J` and `Fin #J'`.
  set f : Fin J.card → ℕ := fun a ↦ D (J.orderIsoOfFin rfl a) with hfdef
  set f' : Fin J'.card → ℕ := fun a ↦ D₁ (J'.orderIsoOfFin rfl a) with hf'def
  have hfprod : ∏ a, f a = ∏ i ∈ J, D i := by
    rw [← Finset.prod_coe_sort J D]
    exact Fintype.prod_equiv (J.orderIsoOfFin rfl).toEquiv _ _ fun _ ↦ rfl
  have hf'prod : ∏ a, f' a = ∏ i ∈ J', D₁ i := by
    rw [← Finset.prod_coe_sort J' D₁]
    exact Fintype.prod_equiv (J'.orderIsoOfFin rfl).toEquiv _ _ fun _ ↦ rfl
  -- The two smooth parts.
  set e : ℕ := W x * ∏ i ∈ Jᶜ, D i with hedef
  set e' : ℕ := ∏ i ∈ J'ᶜ, D₁ i with he'def
  have hefull : e * ∏ a, f a = W x * ∏ i, D i := by
    rw [hedef, hfprod, ← Finset.prod_mul_prod_compl J D]; ring
  have he'full : e' * ∏ a, f' a = ∏ i, D₁ i := by
    rw [he'def, hf'prod, ← Finset.prod_mul_prod_compl J' D₁]; ring
  -- The modulus factors as the product of the four pieces.
  have hprodD : ∏ i, D i = ∏ i : Fin m, d i := by
    rw [Fin.prod_univ_succAbove D i₀]; simp [hDdef]
  have hprodD₁ : ∏ i, D₁ i = ∏ i : Fin m, d' i / (d i).gcd (d' i) := by
    rw [Fin.prod_univ_succAbove D₁ i₀]
    simp [hD₁def, hDdef, hD₂def]
  have hq : W x * ∏ i, (d i).lcm (d' i) = e * e' * (∏ a, f a) * (∏ a, f' a) := by
    rw [show e * e' * (∏ a, f a) * (∏ a, f' a) = (e * ∏ a, f a) * (e' * ∏ a, f' a) by ring,
      hefull, he'full, hprodD, hprodD₁, mul_assoc, ← Finset.prod_mul_distrib]
    exact congrArg _ (prod_congr rfl fun i _ ↦ lcm_eq_mul_div_gcd (hd i))
  -- The four size bounds.
  have hweak (b : Fin p.n) (r : ℕ) : (1 - ε₀) * p.B b r ≤ (1 - ε₀ / 2) * p.B b r := by
    nlinarith [p.B_nonneg b r]
  have hcapf : ((∏ a, f a : ℕ) : ℝ) ≤ x ^ ((1 - ε₀ / 2) * p.B j J.card) := by
    rw [hfprod, Nat.cast_prod]
    exact hcapJ.trans (Real.rpow_le_rpow_of_exponent_le hx1.le (hweak j J.card))
  have hcapf' : ((∏ a, f' a : ℕ) : ℝ) ≤ x ^ ((1 - ε₀ / 2) * p.B j' J'.card) := by
    rw [hf'prod, Nat.cast_prod]
    exact hcapJ'.trans (Real.rpow_le_rpow_of_exponent_le hx1.le (hweak j' J'.card))
  have hmix : ((e * ∏ a, f a : ℕ) : ℝ) ≤ x ^ ((1 - ε₀ / 2) * (p.A j.succ - p.ε)) := by
    rw [hefull, Nat.cast_mul, Nat.cast_prod]
    calc (W x : ℝ) * ∏ i, (D i : ℝ)
        ≤ x ^ ((ε₀ / 2) * (p.A j.succ - p.ε)) * x ^ ((1 - ε₀) * (p.A j.succ - p.ε)) :=
          mul_le_mul (hWL.trans hmixpow.le) htotJ (prod_nonneg fun i _ ↦ by positivity)
            (le_trans (by positivity) (hWL.trans hmixpow.le))
      _ = x ^ ((1 - ε₀ / 2) * (p.A j.succ - p.ε)) := by
          rw [← Real.rpow_add hx0]; ring_nf
  have hmix' : ((e' * ∏ a, f' a : ℕ) : ℝ) ≤ x ^ ((1 - ε₀ / 2) * (p.A j'.succ + p.ε)) := by
    rw [he'full, Nat.cast_prod]
    refine htotJ'.trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_)
    nlinarith [(node j').1]
  -- The whole modulus is at most `x`.
  have hqx : ((e * e' * (∏ a, f a) * (∏ a, f' a) : ℕ) : ℝ) ≤ x := by
    calc ((e * e' * (∏ a, f a) * (∏ a, f' a) : ℕ) : ℝ)
        = ((e * ∏ a, f a : ℕ) : ℝ) * ((e' * ∏ a, f' a : ℕ) : ℝ) := by push_cast; ring
      _ ≤ x ^ ((1 - ε₀ / 2) * (p.A j.succ - p.ε)) * x ^ ((1 - ε₀ / 2) * (p.A j'.succ + p.ε)) :=
          mul_le_mul hmix hmix' (by positivity) (by positivity)
      _ = x ^ ((1 - ε₀ / 2) * (p.A j.succ + p.A j'.succ)) := by
          rw [← Real.rpow_add hx0]; ring_nf
      _ ≤ x ^ (1 : ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le hx1.le ?_
          nlinarith [(node j).2, (node j').2, p.ε_pos]
      _ = x := Real.rpow_one x
  -- The smooth part is `x^δ`-smooth.
  have hsmooth : ∀ r : ℕ, r.Prime → r ∣ e * e' → (r : ℝ) < x ^ p.δ := by
    intro r hr hrd
    have hWsm : (W x : ℝ) < x ^ p.δ := lt_of_le_of_lt hWL hsmpow
    rcases (Nat.Prime.dvd_mul hr).mp hrd with hre | hre'
    · rcases (Nat.Prime.dvd_mul hr).mp hre with hrW | hrp
      · exact lt_of_le_of_lt (by exact_mod_cast Nat.le_of_dvd hWpos hrW) hWsm
      · obtain ⟨i, hi, hri⟩ := (Prime.dvd_finsetProd_iff hr.prime D).mp hrp
        exact lt_of_le_of_lt (by exact_mod_cast Nat.le_of_dvd (hDpos i) hri)
          (hsmoothJ i (Finset.mem_compl.mp hi))
    · obtain ⟨i, hi, hri⟩ := (Prime.dvd_finsetProd_iff hr.prime D₁).mp hre'
      exact lt_of_le_of_lt (by exact_mod_cast Nat.le_of_dvd (hD₁pos i) hri)
        (hsmoothJ' i (Finset.mem_compl.mp hi))
  -- Assemble the membership.
  have hQgen : W x * ∏ i, (d i).lcm (d' i) ∈ Qgen p x j j' J.card J'.card (ε₀ / 2) := by
    refine ⟨e, e', f, f', hq, ?_, ?_, hcapf, hcapf', hmix, hmix', hsmooth, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hWpos.ne'
        (Finset.prod_ne_zero_iff.mpr fun i _ ↦ Nat.lcm_ne_zero (hd i).ne' (hd' i).ne'))
    · exact hq ▸ hqx
    · exact fun a ↦ hroughJ _ (J.orderIsoOfFin rfl a).2
    · exact fun a ↦ hroughJ' _ (J'.orderIsoOfFin rfl a).2
  simp only [Qstar, Set.mem_iUnion, exists_prop]
  exact ⟨j, j', J.card, Finset.mem_Iic.mpr hcardJ, J'.card, Finset.mem_Iic.mpr hcardJ', hQgen⟩

/-! ## Counting a dyadic block in a residue class -/

/-- The integers of `Icc A B` in a fixed class modulo `q` number at most `(B-A)/q + 1`: the map
`n ↦ (n-A)/q` is injective on them, since two members of one class landing in one block of length
`q` differ by less than `q`. -/
theorem card_filter_modEq_le {A B q a : ℕ} :
    #{n ∈ Finset.Icc A B | n ≡ a [MOD q]} ≤ (B - A) / q + 1 := by
  rw [← Finset.card_range ((B - A) / q + 1)]
  refine Finset.card_le_card_of_injOn (fun n ↦ (n - A) / q) (fun n hn ↦ ?_) fun n hn n' hn' heq ↦ ?_
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn hn' heq
    have h₁ := Nat.div_add_mod (n - A) q
    have h₂ := Nat.div_add_mod (n' - A) q
    have hmod : (n - A) % q = (n' - A) % q := Nat.ModEq.add_right_cancel' A (by
      rw [Nat.sub_add_cancel hn.1.1, Nat.sub_add_cancel hn'.1.1]; exact hn.2.trans hn'.2.symm)
    rw [heq] at h₁
    omega

/-- The dyadic block `[x, 2x]` has at most `x + 1` members. -/
theorem card_dyadic_le {x : ℝ} (hx : 0 ≤ x) : (#(dyadic x) : ℝ) ≤ x + 1 := by
  have hfl := Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * x)
  have hce := Nat.le_ceil x
  rw [Gap212.dyadic, Nat.card_Icc]
  rcases le_or_gt ⌈x⌉₊ (⌊2 * x⌋₊ + 1) with h | h
  · rw [Nat.cast_sub h]; push_cast; linarith
  · rw [Nat.sub_eq_zero_of_le h.le]; push_cast; linarith

/-- The members of the dyadic block in a fixed class modulo `q` number at most `x/q + 1`. -/
theorem card_dyadic_filter_modEq_le {x : ℝ} (hx : 0 ≤ x) {q a : ℕ} (hq : 0 < q) :
    (#{n ∈ dyadic x | n ≡ a [MOD q]} : ℝ) ≤ x / q + 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hfl := Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * x)
  have hce := Nat.le_ceil x
  have hsub : ((⌊2 * x⌋₊ - ⌈x⌉₊ : ℕ) : ℝ) ≤ x := by
    rcases le_or_gt ⌈x⌉₊ ⌊2 * x⌋₊ with h | h
    · rw [Nat.cast_sub h]; linarith
    · rw [Nat.sub_eq_zero_of_le h.le]; push_cast; linarith
  have h1 : (#{n ∈ dyadic x | n ≡ a [MOD q]} : ℝ)
      ≤ (((⌊2 * x⌋₊ - ⌈x⌉₊) / q + 1 : ℕ) : ℝ) := by
    rw [Gap212.dyadic]
    exact_mod_cast card_filter_modEq_le (A := ⌈x⌉₊) (B := ⌊2 * x⌋₊) (a := a) (q := q)
  refine h1.trans ?_
  push_cast
  gcongr
  exact Nat.cast_div_le.trans (by gcongr)

/-! ## The averaging sample -/

/-- **The Chinese remainder theorem as a prescription of residues.** Given pairwise coprime
positive moduli and one residue modulo each, some natural number realizes all of them at once. -/
theorem exists_natCast_eq {ι : Type*} [Finite ι] (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hcop : Pairwise (Function.onFun Nat.Coprime a)) (R : ∀ i, ZMod (a i)) :
    ∃ n : ℕ, ∀ i, ((n : ℕ) : ZMod (a i)) = R i := by
  haveI := Fintype.ofFinite ι
  haveI : NeZero (∏ i, a i) := ⟨(Finset.prod_pos fun i _ ↦ ha i).ne'⟩
  refine ⟨((ZMod.prodEquivPi a hcop).symm R).val, fun i ↦ ?_⟩
  rw [← map_natCast (ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) (ZMod (a i))),
    ZMod.natCast_zmod_val, ← ZMod.prodEquivPi_apply, RingEquiv.apply_symm_apply]
  exact hcop

/-- A congruence modulo each member of a pairwise coprime finset of moduli is a congruence modulo
their product. -/
theorem modEq_prod {t : Finset ℕ} {u v : ℕ}
    (hcop : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Nat.Coprime i j)
    (hmod : ∀ i ∈ t, u ≡ v [MOD i]) : u ≡ v [MOD ∏ i ∈ t, i] := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Nat.modEq_one]
  | insert p s hp ih =>
      rw [Finset.prod_insert hp]
      refine (Nat.modEq_and_modEq_iff_modEq_mul ?_).mp
        ⟨hmod p (by simp), ih (fun i hi j hj hij ↦ hcop i (by simp [hi]) j (by simp [hj]) hij)
          (fun i hi ↦ hmod i (by simp [hi]))⟩
      exact Nat.Coprime.prod_right fun j hj ↦ hcop p (by simp) j (by simp [hj])
        (fun hEq ↦ hp (hEq ▸ hj))

/-- **Distinct shifts stay distinct modulo a prime outside `W(x)`.** Two entries of a strictly
increasing tuple differ by a non-zero amount at most the diameter, and every prime up to the
diameter divides `W(x)`; so a prime that does not divide `W(x)` exceeds the diameter and cannot
identify them. -/
theorem shift_natCast_ne {k : ℕ} {h : Fin k → ℕ} (hmono : StrictMono h) {x : ℝ}
    (hD : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ (Finset.image h Finset.univ).diameter → ℓ ∣ W x)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓW : ¬ℓ ∣ W x) {i i' : Fin k} (hii : i ≠ i') :
    ((h i : ℕ) : ZMod ℓ) ≠ ((h i' : ℕ) : ZMod ℓ) := by
  wlog hlt : h i < h i' generalizing i i'
  · exact fun hEq ↦ this hii.symm ((not_lt.mp hlt).lt_of_ne (hmono.injective.ne hii.symm)) hEq.symm
  intro hEq
  have hne : (Finset.image h Finset.univ).Nonempty := ⟨h i, Finset.mem_image_of_mem h (mem_univ i)⟩
  have hdvd : ℓ ∣ h i' - h i :=
    (Nat.modEq_iff_dvd' hlt.le).mp ((ZMod.natCast_eq_natCast_iff _ _ _).mp hEq)
  have hmax := Finset.le_max' _ _ (Finset.mem_image_of_mem h (Finset.mem_univ i'))
  have hmin := Finset.min'_le _ _ (Finset.mem_image_of_mem h (Finset.mem_univ i))
  have hle : h i' - h i ≤ (Finset.image h Finset.univ).diameter := by
    rw [Finset.diameter_eq_max_sub_min hne]
    omega
  exact hℓW (hD ℓ hℓ ((Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdvd).trans hle))

/-- **A sample of residues detecting every tuple residue.** For a strictly increasing tuple `h` of
dimension `k = m + 1` with `m ≥ 1`, a pre-sieved residue `b`, a removed coordinate `i₀`, and an `x`
large enough that every prime up to the tuple's diameter divides `W(x)`, there is a finite
non-empty set `𝓑` of residues, every one of them coprime below `x`, such that every tuple residue
is hit with the exact density `m^{-ω(q/W(x))}`:
`#{a ∈ 𝓑 : a ≡ a(d) (q)} · m^{ω(q/W(x))} = #𝓑`.

`𝓑` is the image of the choice space `(primes ℓ ≤ x not dividing W(x)) → Fin m` under the Chinese
remainder map sending a choice `c` to the residue `b + h_{i₀}` modulo `W(x)` and
`h_{i₀} - h_{i₀.succAbove(c ℓ)}` modulo each such `ℓ`. That map is injective because the `m`
residues `h_{i₀} - h_i` are pairwise distinct modulo every `ℓ` exceeding the diameter, which is
also why every member of `𝓑` is coprime below `x`. A tuple residue modulo `q = W(x)∏[dᵢ,d'ᵢ]`
prescribes the choice at exactly the `ω(q/W(x))` primes of `q/W(x)` and nothing else, so its fibre
is a product of
`m`-element choices over the remaining primes — which is the counting identity.

Admissibility of `𝓗`, and pairwise coprimality of the `[dᵢ,d'ᵢ]`, are not used: strict monotonicity
of `h` carries the distinctness, and the index attached to a prime of `q/W(x)` need only exist, not
be unique. -/
@[gap212 "lem_averaging_sample"]
theorem exists_averaging_sample {m : ℕ} (hm : 0 < m) {h : Fin (m + 1) → ℕ}
    (hmono : StrictMono h) (i₀ : Fin (m + 1)) (b : ℕ) {x : ℝ}
    (hb : IsPreSieved b (W x) h)
    (hD : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ (Finset.image h Finset.univ).diameter → ℓ ∣ W x) :
    ∃ 𝓑 : Finset ℕ, 𝓑.Nonempty ∧ (∀ a ∈ 𝓑, CoprimeBelow a x) ∧
      ∀ (q : ℕ) (d d' : Fin m → ℕ) (a₀ : ℕ), (q : ℝ) ≤ x →
        q = W x * ∏ i, (d i).lcm (d' i) → Squarefree (q / W x) →
        Nat.Coprime (q / W x) (W x) → IsTupleResidue x b h i₀ d d' a₀ →
        #{a ∈ 𝓑 | a ≡ a₀ [MOD q]} * m ^ (q / W x).primeFactors.card = 𝓑.card := by
  classical
  haveI hne : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hWpos : 0 < W x := primorial_pos _
  -- The primes at most `x` that do not divide `W(x)`: the coordinates of the choice space.
  set S : Finset ℕ := {ℓ ∈ Finset.range (⌊x⌋₊ + 1) | ℓ.Prime ∧ ¬ℓ ∣ W x} with hSdef
  have hSmem : ∀ ℓ : ℕ, ℓ ∈ S ↔ ℓ ≤ ⌊x⌋₊ ∧ ℓ.Prime ∧ ¬ℓ ∣ W x := fun ℓ ↦ by
    simp [hSdef]
  have hSprime : ∀ v : S, ((v : ℕ)).Prime := fun v ↦ ((hSmem v).mp v.2).2.1
  have hSW : ∀ v : S, ¬((v : ℕ)) ∣ W x := fun v ↦ ((hSmem v).mp v.2).2.2
  have hcopWS : Nat.Coprime (W x) (∏ ℓ ∈ S, ℓ) :=
    Nat.Coprime.prod_right fun ℓ hℓ ↦
      ((Nat.Prime.coprime_iff_not_dvd ((hSmem ℓ).mp hℓ).2.1).mpr ((hSmem ℓ).mp hℓ).2.2).symm
  -- The prescribed residues, one per coordinate.
  set R : (S → Fin m) → ∀ v : S, ZMod (v : ℕ) := fun c v ↦
    (((h i₀ : ℤ) - (h (i₀.succAbove (c v)) : ℤ) : ℤ) : ZMod (v : ℕ)) with hRdef
  have hexΨ : ∀ c : S → Fin m, ∃ n : ℕ, ∀ v : S, ((n : ℕ) : ZMod (v : ℕ)) = R c v := fun c ↦
    exists_natCast_eq (fun v : S ↦ (v : ℕ)) (fun v ↦ (hSprime v).pos)
      (fun i j hij ↦ (Nat.coprime_primes (hSprime i) (hSprime j)).mpr
        fun hEq ↦ hij (Subtype.ext hEq)) (R c)
  choose Ψ hΨ using hexΨ
  set Φ : (S → Fin m) → ℕ := fun c ↦ (Nat.chineseRemainder hcopWS (b + h i₀) (Ψ c) : ℕ)
    with hΦdef
  have hΦW : ∀ c, Φ c ≡ b + h i₀ [MOD W x] := fun c ↦
    (Nat.chineseRemainder hcopWS (b + h i₀) (Ψ c)).2.1
  have hΦS : ∀ (c : S → Fin m) (v : S), ((Φ c : ℕ) : ZMod (v : ℕ)) = R c v := by
    intro c v
    rw [← hΨ c v]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem (fun ℓ : ℕ ↦ ℓ) v.2)
        (Nat.chineseRemainder hcopWS (b + h i₀) (Ψ c)).2.2)
  -- Distinct choices prescribe distinct residues, hence give distinct representatives.
  have hRinj : ∀ (c c' : S → Fin m) (v : S), R c v = R c' v → c v = c' v := by
    intro c c' v h1
    simp only [hRdef, Int.cast_sub, Int.cast_natCast, sub_right_inj] at h1
    by_contra hcon
    exact shift_natCast_ne hmono hD (hSprime v) (hSW v) (Fin.succAbove_right_injective.ne hcon) h1
  have hΦinj : Function.Injective Φ := fun c c' hEq ↦
    funext fun v ↦ hRinj c c' v (by rw [← hΦS c v, ← hΦS c' v, hEq])
  refine ⟨Finset.image Φ Finset.univ, Finset.univ_nonempty.image Φ, ?_, ?_⟩
  · -- Every representative is coprime below `x`.
    intro a ha r hr hrx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp ha
    haveI : NeZero r := ⟨hr.ne_zero⟩
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hr).mpr fun hdvd ↦ ?_)
    have hzero : ((Φ c : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    by_cases hrW : r ∣ W x
    · have hcast : ((Φ c : ℕ) : ZMod r) = ((b + h i₀ : ℕ) : ZMod r) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.of_dvd hrW (hΦW c))
      have hd2 : r ∣ b + h i₀ :=
        (ZMod.natCast_eq_zero_iff _ _).mp (hcast ▸ hzero)
      exact hr.one_lt.ne' (Nat.eq_one_of_dvd_one ((hb i₀) ▸ Nat.dvd_gcd hd2 hrW))
    · have hrS : r ∈ S := (hSmem r).mpr ⟨Nat.le_floor hrx, hr, hrW⟩
      have hcast := hΦS c ⟨r, hrS⟩
      simp only [hRdef, Int.cast_sub, Int.cast_natCast] at hcast
      rw [hzero, eq_comm, sub_eq_zero] at hcast
      exact shift_natCast_ne hmono hD hr hrW
        (Ne.symm (Fin.succAbove_ne i₀ (c ⟨r, hrS⟩))) hcast
  · -- The counting identity.
    intro q d d' a₀ hqx hq hsfN hcopN hres
    have hNdef : q / W x = ∏ i, (d i).lcm (d' i) := by
      rw [hq, Nat.mul_div_cancel_left _ hWpos]
    have hqN : q = W x * (q / W x) := by rw [hNdef, hq]
    have hqpos : 0 < q := by rw [hqN]; exact Nat.mul_pos hWpos (Nat.pos_of_ne_zero hsfN.ne_zero)
    -- Every prime of `q/W(x)` is a coordinate of the choice space.
    have hUS : ∀ ℓ ∈ (q / W x).primeFactors, ℓ ∈ S := by
      intro ℓ hℓ
      have hp := Nat.prime_of_mem_primeFactors hℓ
      have hdvd := Nat.dvd_of_mem_primeFactors hℓ
      have hℓq : ℓ ∣ q := hqN ▸ Dvd.dvd.mul_left hdvd (W x)
      refine (hSmem ℓ).mpr ⟨Nat.le_floor ((Nat.cast_le.mpr (Nat.le_of_dvd hqpos hℓq)).trans hqx),
        hp, fun hW ↦ ?_⟩
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one (hcopN ▸ Nat.dvd_gcd hdvd hW))
    -- The coordinate each prime of `q/W(x)` is pinned by.
    have hex : ∀ v : S, ∃ i : Fin m,
        ((v : ℕ) ∈ (q / W x).primeFactors → (v : ℕ) ∣ (d i).lcm (d' i)) := by
      intro v
      by_cases hv : (v : ℕ) ∈ (q / W x).primeFactors
      · obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff
          (Nat.prime_of_mem_primeFactors hv).prime _).mp
            (hNdef ▸ Nat.dvd_of_mem_primeFactors hv)
        exact ⟨i, fun _ ↦ hi⟩
      · exact ⟨Classical.arbitrary (Fin m), fun hc ↦ absurd hc hv⟩
    choose g hg using hex
    set V : Finset S := {v ∈ Finset.univ | (v : ℕ) ∈ (q / W x).primeFactors} with hVdef
    have hVmem : ∀ v : S, v ∈ V ↔ (v : ℕ) ∈ (q / W x).primeFactors := fun v ↦ by simp [hVdef]
    -- At a pinned prime, the tuple residue and the representative agree exactly when the choice
    -- matches the pinned index.
    have hres' : ∀ (v : S) (i : Fin m), (v : ℕ) ∣ (d i).lcm (d' i) →
        ((a₀ : ℕ) : ZMod (v : ℕ)) = (((h i₀ : ℤ) - (h (i₀.succAbove i) : ℤ) : ℤ) :
          ZMod (v : ℕ)) := by
      intro v i hdvd
      simpa using (ZMod.intCast_eq_intCast_iff _ _ _).mpr
        (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hdvd) (hres.2 i))
    have hchar : ∀ c : S → Fin m, Φ c ≡ a₀ [MOD q] ↔ ∀ v ∈ V, c v = g v := by
      refine fun c ↦ ⟨fun hmod v hv ↦ ?_, fun hc ↦ ?_⟩
      · have hvU := (hVmem v).mp hv
        have hvq : (v : ℕ) ∣ q := hqN ▸ Dvd.dvd.mul_left (Nat.dvd_of_mem_primeFactors hvU) (W x)
        have h1 : ((Φ c : ℕ) : ZMod (v : ℕ)) = ((a₀ : ℕ) : ZMod (v : ℕ)) :=
          (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.of_dvd hvq hmod)
        rw [hΦS c v, hres' v (g v) (hg v hvU)] at h1
        exact hRinj c (fun _ ↦ g v) v h1
      · refine hqN ▸ (Nat.modEq_and_modEq_iff_modEq_mul hcopN.symm).mp ⟨?_, ?_⟩
        · exact (hΦW c).trans hres.1.symm
        · rw [← Nat.prod_primeFactors_of_squarefree hsfN]
          refine modEq_prod (fun i hi j hj hij ↦ (Nat.coprime_primes
            (Nat.prime_of_mem_primeFactors hi) (Nat.prime_of_mem_primeFactors hj)).mpr hij) ?_
          intro ℓ hℓ
          refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
          rw [hΦS c ⟨ℓ, hUS ℓ hℓ⟩, hres' _ _ (hg ⟨ℓ, hUS ℓ hℓ⟩ hℓ)]
          simp only [hRdef, hc ⟨ℓ, hUS ℓ hℓ⟩ ((hVmem _).mpr hℓ)]
    -- The class is the image of the pinned choices, and the pinned choices are a product.
    have himg : {a ∈ Finset.image Φ Finset.univ | a ≡ a₀ [MOD q]}
        = Finset.image Φ {c ∈ Finset.univ | ∀ v ∈ V, c v = g v} := by
      rw [Finset.filter_image]
      exact congrArg _ (Finset.filter_congr fun c _ ↦ by rw [hchar c])
    have hpi : {c ∈ (Finset.univ : Finset (S → Fin m)) | ∀ v ∈ V, c v = g v}
        = Fintype.piFinset fun v ↦ if v ∈ V then {g v} else Finset.univ := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      exact ⟨fun hc v ↦ by split_ifs with hv <;> simp [hc v, hv],
        fun hc v hv ↦ by simpa [hv] using hc v⟩
    have hcardV : V.card = (q / W x).primeFactors.card :=
      Finset.card_bij (fun v _ ↦ (v : ℕ)) (fun v hv ↦ (hVmem v).mp hv)
        (fun v _ v' _ ↦ Subtype.ext) fun ℓ hℓ ↦ ⟨⟨ℓ, hUS ℓ hℓ⟩, (hVmem _).mpr hℓ, rfl⟩
    rw [himg, Finset.card_image_of_injective _ hΦinj, Finset.card_image_of_injective _ hΦinj,
      hpi, Fintype.card_piFinset, ← hcardV, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    simp only [apply_ite Finset.card, Finset.card_singleton, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, ← pow_add,
      Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ V), Finset.card_univ]

/-! ## The averaging step

The two facts through which `Gap212.Sieve.weighted_error_negligible` uses the sample of
`Gap212.Sieve.exists_averaging_sample`: the dyadic discrepancy
sees a residue only through its class, and a sample that hits every class with a fixed density
therefore dominates the discrepancy at any one class by its own average. -/

/-- **The dyadic discrepancy sees the residue only through its class.** -/
theorem sumErrorDyadic_congr {x : ℝ} {f : ℕ → ℂ} {q a a' : ℕ} (hmod : a ≡ a' [MOD q]) :
    sumErrorDyadic x f q a = sumErrorDyadic x f q a' := by
  rw [Gap212.sumErrorDyadic, Gap212.sumErrorDyadic, Finset.filter_congr fun n _ ↦
    ⟨fun hn ↦ hn.trans hmod, fun hn ↦ hn.trans hmod.symm⟩]

/-- **A sample hitting every class with a fixed density dominates the discrepancy at one class.**
If `#{a ∈ 𝓑 : a ≡ a₀ (q)} · w = #𝓑` with `𝓑` non-empty, then
`‖Δ_𝒟(f;x,q,a₀)‖ ≤ (w/#𝓑)·∑_{a ∈ 𝓑}‖Δ_𝒟(f;x,q,a)‖`.

The inner sum over the class is `#{a ∈ 𝓑 : a ≡ a₀ (q)}` copies of one term, by
`Gap212.Sieve.sumErrorDyadic_congr`; enlarging the range to all of `𝓑` can only increase it. This
is the step that lets a hypothesis about one common residue serve the many residues a divisor
expansion produces, and `w` is the `(k-1)^{ω(q/W(x))}` that
`Gap212.Sieve.exists_averaging_sample` supplies. -/
theorem norm_sumErrorDyadic_le_sample_average {𝓑 : Finset ℕ} (hne : 𝓑.Nonempty) {q a₀ w : ℕ}
    (hcount : #{a ∈ 𝓑 | a ≡ a₀ [MOD q]} * w = 𝓑.card) {x : ℝ} {f : ℕ → ℂ} :
    ‖sumErrorDyadic x f q a₀‖ ≤ (w / (𝓑.card : ℝ)) * ∑ a ∈ 𝓑, ‖sumErrorDyadic x f q a‖ := by
  have hBpos : 0 < 𝓑.card := Finset.card_pos.mpr hne
  have hNR : (0 : ℝ) < (#{a ∈ 𝓑 | a ≡ a₀ [MOD q]} : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero fun hz ↦ by rw [hz, zero_mul] at hcount; omega)
  -- On the class every term is the same.
  have hconst : ∑ a ∈ {a ∈ 𝓑 | a ≡ a₀ [MOD q]}, ‖sumErrorDyadic x f q a‖
      = (#{a ∈ 𝓑 | a ≡ a₀ [MOD q]} : ℝ) * ‖sumErrorDyadic x f q a₀‖ := by
    rw [Finset.sum_congr rfl fun a ha ↦ by
      rw [sumErrorDyadic_congr (Finset.mem_filter.mp ha).2], Finset.sum_const, nsmul_eq_mul]
  have hmono : ∑ a ∈ {a ∈ 𝓑 | a ≡ a₀ [MOD q]}, ‖sumErrorDyadic x f q a‖
      ≤ ∑ a ∈ 𝓑, ‖sumErrorDyadic x f q a‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun a _ _ ↦ norm_nonneg _
  have hw : (w : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr fun hw ↦ by rw [hw, mul_zero] at hcount; omega
  rw [← hcount, Nat.cast_mul, div_mul_cancel_right₀ hw, inv_mul_eq_div, le_div_iff₀ hNR]
  linarith

/-! ## The crude weighted discrepancy moment -/

section DivisorMoment

open ArithmeticFunction Nat
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-- On a squarefree number the `r`-fold divisor function is `r^{ω}`: it is multiplicative and takes
the value `r` at every prime. -/
theorem tau_eq_pow_card_primeFactors (r : ℕ) {n : ℕ} (hn : Squarefree n) :
    τ r n = r ^ n.primeFactors.card := by
  rw [← isMultiplicative_tau.prod_primeFactors hn,
    Finset.prod_congr rfl fun q hq ↦ tau_prime (r := r) (Nat.prime_of_mem_primeFactors hq),
    Finset.prod_const]

/-- On a squarefree number the twenty-seventh power of the divisor count is the `2^27`-fold divisor
function: both are `2^{27ω}`. This is the shape the Mertens-type bound is stated at, and `27` is
`2·13 + 1` — twice the exponent `v(q) ≤ τ(q)^13` costs, plus the one the `q/φ(q)` loss costs. -/
theorem card_divisors_pow_eq_tau {n : ℕ} (hn : Squarefree n) :
    n.divisors.card ^ 27 = τ (2 ^ 27) n := by
  rw [card_divisors_of_squarefree hn, tau_eq_pow_card_primeFactors _ hn, ← pow_mul, ← pow_mul,
    Nat.mul_comm]

/-- **The crude weighted discrepancy moment.** For every `S < 1` there are a `C'` and an `X` such
that for every `x ≥ X` and every residue `a`,
`∑_{q ≤ x^S, W(x) ∣ q, q squarefree} v(q)²‖Δ_𝒟(ρ(·;x);x,q,a)‖ ≤ x(log x)^{C'}`.

Three inputs, and no distribution hypothesis at all — that is what makes the bound *crude*. The
trivial count of a residue class gives `‖Δ_𝒟‖ ≪ xτ(q)/q` (the `+1` of `x/q+1` is absorbed because
`q ≤ x^S ≤ x`, and `1/φ(q) ≤ τ(q)/q` on every `q`); `v(q)² ≤ τ(q)^{26}` is
`Gap212.Sieve.residueWeight_bounds`; and `τ(q)^{27} = τ_{2^27}(q)` on squarefree `q` turns the
remaining sum into the Mertens-type bound `∑_{q ≤ z}μ(q)²τ_k(q)/φ(q) ≤ e^{1+3k}(log z)^k`. So
`C' = 2^27 + 1` serves, the extra `1` absorbing the constant `4e^{1+3·2^27}` into one more
logarithm.

Of `ρ` only `0 ≤ ρ(·;x) ≤ 1` on the block, for all large `x`, is used — weaker than
`0 ≤ ρ(·;x) ≤ 1_ℙ`, and the support clause is not needed at all since the dyadic discrepancy sums
over the block only. -/
@[gap212 "lem_crude_discrepancy_moment"]
theorem crude_discrepancy_moment {ρ : ℕ → ℝ → ℝ} {S : ℝ} (hS : S < 1)
    (hρ : ∀ᶠ x : ℝ in atTop, ∀ n ∈ dyadic x, 0 ≤ ρ n x ∧ ρ n x ≤ 1) :
    ∃ (C' : ℕ) (X : ℝ), ∀ x ≥ X, ∀ a : ℕ,
      ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x ^ S⌋₊ | W x ∣ q ∧ Squarefree q},
          (residueWeight x q : ℝ) ^ 2 * ‖sumErrorDyadic x (fun n ↦ (ρ n x : ℂ)) q a‖
        ≤ x * Real.log x ^ C' := by
  classical
  have hev : ∀ᶠ x : ℝ in atTop, (2 ≤ W x ∧ 1 < x ∧
      4 * Real.exp (1 + 3 * ((2 ^ 27 : ℕ) : ℝ)) ≤ Real.log x) ∧
      ∀ n ∈ dyadic x, 0 ≤ ρ n x ∧ ρ n x ≤ 1 := by
    filter_upwards [eventually_dvd_W_of_prime_le 2, eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop
        (4 * Real.exp (1 + 3 * ((2 ^ 27 : ℕ) : ℝ))), hρ] with x h1 h2 h3 h4
    exact ⟨⟨Nat.le_of_dvd (primorial_pos _) (h1 2 Nat.prime_two le_rfl), h2, h3⟩, h4⟩
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hev
  refine ⟨2 ^ 27 + 1, X, fun x hx a ↦ ?_⟩
  obtain ⟨⟨hW2, hx1, hlogK⟩, hρx⟩ := hX x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogpos : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hzx : ((⌊x ^ S⌋₊ : ℕ) : ℝ) ≤ x := (Nat.floor_le (Real.rpow_nonneg hx0.le S)).trans
    (by simpa using Real.rpow_le_rpow_of_exponent_le hx1.le hS.le)
  rcases le_or_gt 2 ⌊x ^ S⌋₊ with hz2 | hz2
  · -- Every modulus in range contributes at most `4x·μ(q)²τ_{2^27}(q)/φ(q)`.
    have hterm : ∀ q ∈ {q ∈ Finset.Icc 1 ⌊x ^ S⌋₊ | W x ∣ q ∧ Squarefree q},
        (residueWeight x q : ℝ) ^ 2 * ‖sumErrorDyadic x (fun n ↦ (ρ n x : ℂ)) q a‖
          ≤ 4 * x * ((μ q : ℝ) ^ 2 * (τ (2 ^ 27) q : ℝ) / (φ q : ℝ)) := by
      intro q hq
      obtain ⟨hqI, hWq, hsf⟩ := Finset.mem_filter.mp hq
      obtain ⟨hq1, hqz⟩ := Finset.mem_Icc.mp hqI
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
      have hqx : (q : ℝ) ≤ x := le_trans (by exact_mod_cast hqz) hzx
      have hφpos : (0 : ℝ) < (φ q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq1
      have hT1 : (1 : ℝ) ≤ (q.divisors.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
      -- The trivial bound on the dyadic discrepancy: `|ρ| ≤ 1` on the block.
      have hbound : ∀ s : Finset ℕ, s ⊆ dyadic x →
          ‖∑ n ∈ s, ((ρ n x : ℝ) : ℂ)‖ ≤ (s.card : ℝ) := by
        intro s hs
        refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ 1 fun n hn ↦ ?_).trans_eq
          (by simp))
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρx n (hs hn)).1]
        exact (hρx n (hs hn)).2
      have hnorm1 : ‖∑ n ∈ dyadic x with n ≡ a [MOD q], ((ρ n x : ℝ) : ℂ)‖
          ≤ x / q + 1 :=
        (hbound _ (Finset.filter_subset _ _)).trans
          (card_dyadic_filter_modEq_le hx0.le (q := q) (a := a) hq1)
      have hnorm2 : ‖∑ n ∈ dyadic x with Nat.Coprime n q, ((ρ n x : ℝ) : ℂ)‖ ≤ x + 1 :=
        (hbound _ (Finset.filter_subset _ _)).trans
          ((Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (card_dyadic_le hx0.le))
      have hΔ : ‖sumErrorDyadic x (fun n ↦ ((ρ n x : ℝ) : ℂ)) q a‖
          ≤ (x / q + 1) + (x + 1) / (φ q : ℝ) := by
        rw [Gap212.sumErrorDyadic]
        refine (norm_sub_le _ _).trans (add_le_add hnorm1 ?_)
        rw [norm_mul, norm_div, norm_one, Complex.norm_natCast, one_div_mul_eq_div]
        gcongr
      -- `q ≤ τ(q)φ(q)` turns the `1/φ(q)` into `τ(q)/q`.
      have hinv : 1 / (φ q : ℝ) ≤ (q.divisors.card : ℝ) / q := by
        rw [div_le_div_iff₀ hφpos hqR, one_mul]
        have h := le_tau₂_mul_totient (n := q)
        rw [tau_eq_pow_card_primeFactors 2 hsf, ← card_divisors_of_squarefree hsf] at h
        exact_mod_cast h
      have hΔ2 : ‖sumErrorDyadic x (fun n ↦ ((ρ n x : ℝ) : ℂ)) q a‖
          ≤ 4 * x * (q.divisors.card : ℝ) / q := by
        refine hΔ.trans ?_
        have h1 : (1 : ℝ) ≤ x / q := (one_le_div hqR).mpr hqx
        have h2 : (x + 1) / (φ q : ℝ) ≤ (x + 1) * ((q.divisors.card : ℝ) / q) := by
          rw [div_eq_mul_one_div]; gcongr
        have h3 : x / q ≤ x * ((q.divisors.card : ℝ) / q) := by
          rw [mul_div_assoc']; gcongr; nlinarith
        rw [mul_div_assoc]
        nlinarith [mul_nonneg (sub_nonneg.mpr hx1.le)
          (by positivity : (0 : ℝ) ≤ (q.divisors.card : ℝ) / q)]
      -- The weight is a fixed power of the divisor count.
      have hv : (residueWeight x q : ℝ) ^ 2 ≤ (q.divisors.card : ℝ) ^ 26 := by
        have hc : (residueWeight x q : ℝ) ≤ (q.divisors.card : ℝ) ^ 13 := by
          exact_mod_cast (residueWeight_bounds (k := 45) rfl hsf hWq).2
        exact (pow_le_pow_left₀ (by positivity) hc 2).trans_eq (by ring)
      have hμ : (μ q : ℝ) ^ 2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hsf
      rw [hμ, one_mul]
      calc (residueWeight x q : ℝ) ^ 2 * ‖sumErrorDyadic x (fun n ↦ ((ρ n x : ℝ) : ℂ)) q a‖
          ≤ (q.divisors.card : ℝ) ^ 26 * (4 * x * (q.divisors.card : ℝ) / q) :=
            mul_le_mul hv hΔ2 (norm_nonneg _) (by positivity)
        _ = 4 * x * ((τ (2 ^ 27) q : ℝ) / q) := by
            rw [← card_divisors_pow_eq_tau hsf]; push_cast; ring
        _ ≤ 4 * x * ((τ (2 ^ 27) q : ℝ) / (φ q : ℝ)) := by
            have : (φ q : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
            gcongr
    -- Sum, and feed the Mertens-type bound.
    have hlogz : (0 : ℝ) ≤ Real.log ((⌊x ^ S⌋₊ : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hz2)
    calc ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x ^ S⌋₊ | W x ∣ q ∧ Squarefree q},
          (residueWeight x q : ℝ) ^ 2 * ‖sumErrorDyadic x (fun n ↦ (ρ n x : ℂ)) q a‖
        ≤ ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x ^ S⌋₊ | W x ∣ q ∧ Squarefree q},
            4 * x * ((μ q : ℝ) ^ 2 * (τ (2 ^ 27) q : ℝ) / (φ q : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = 4 * x * ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x ^ S⌋₊ | W x ∣ q ∧ Squarefree q},
            ((μ q : ℝ) ^ 2 * (τ (2 ^ 27) q : ℝ) / (φ q : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ 4 * x * ∑ u ∈ Finset.range (⌊x ^ S⌋₊ + 1),
            ((μ u : ℝ) ^ 2 * (τ (2 ^ 27) u : ℝ) / (φ u : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (fun q hq ↦ Finset.mem_range.mpr
              (Nat.lt_succ_of_le (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2))
              fun u _ _ ↦ by positivity) (by positivity)
      _ ≤ 4 * x * (Real.exp (1 + 3 * ((2 ^ 27 : ℕ) : ℝ)) *
            Real.log ((⌊x ^ S⌋₊ : ℕ) : ℝ) ^ (2 ^ 27 : ℕ)) :=
          mul_le_mul_of_nonneg_left
            (sum_moebius_sq_mul_tau_div_totient_le (2 ^ 27) hz2) (by positivity)
      _ ≤ 4 * x * (Real.exp (1 + 3 * ((2 ^ 27 : ℕ) : ℝ)) * Real.log x ^ (2 ^ 27 : ℕ)) := by
          gcongr
      _ = (4 * Real.exp (1 + 3 * ((2 ^ 27 : ℕ) : ℝ))) * x * Real.log x ^ (2 ^ 27 : ℕ) := by ring
      _ ≤ Real.log x * x * Real.log x ^ (2 ^ 27 : ℕ) := by
          gcongr
      _ = x * Real.log x ^ (2 ^ 27 + 1 : ℕ) := by ring
  · -- Below `x^S ≤ 2` the index set is empty: only `q = 1` survives, and `W(x) ≥ 2`.
    have hempty : {q ∈ Finset.Icc 1 ⌊x ^ S⌋₊ | W x ∣ q ∧ Squarefree q} = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun q hq ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_Icc] at hq
      obtain rfl : q = 1 := by omega
      have := Nat.le_of_dvd one_pos hq.2.1
      omega
    rw [hempty, Finset.sum_empty]
    exact mul_nonneg hx0.le (pow_nonneg hlogpos.le _)

end DivisorMoment

end Gap212.Sieve
