/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.DivisorSumDefs
public import Gap212.Sieve.WSieve
public import Gap212.Parameters.Challenge
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.GCD.Prime
public meta import Gap212.Attr

/-!
# The divisor sums: the size of the normalization, of the moduli, and of the residue weight

The elementary estimates the two divisor-sum evaluations rest on. Each is arithmetic or algebra;
none of them sees a sieve.

* The normalization `𝓒_x` is bounded below by `x/(log x)^{k+1}`, so an error term of size
  `𝓒_x/(log x)^2` is `o(𝓒_x)` and a quantity of size `x/(log x)^{k+3}` is too.
* A modulus the denominator's divisor pair generates has exponent below `1`, which is what puts it
  inside the range where an equidistribution hypothesis is available.
* At most `(3(k-1))^{ω(q/W(x))}` divisor tuples generate a given squarefree modulus `q`.
* The residue weight is at most a *fixed* power of the divisor function, the thirteenth, because
  `5808 < 8192 = 2^13`.

* The pointwise inequality `w(P² + 2PQ) ≤ w(P+Q)²` that makes the numerator evaluation a lower
  bound rather than an equality.

## Why the exponent of `𝓒_x` is a literal

`Gap212.GPY.calC` is parameterised by `m = k - 1`, so `k = m + 1` and the exponent
`(log x)^{k+1}` is `(log x)^{m+2}` — a literal exponent, never a truncated `ℕ` subtraction. The
same convention is why the lower bound below reads `m + 2`.

## Main results

* `Gap212.Sieve.calC_lower_bound`: `𝓒_x ≥ x/(log x)^{k+1} > 0` for large `x`.
* `Gap212.Sieve.denominator_modulus_exponent`: `W(x)∏[dᵢ,d'ᵢ] ≤ x^S` with `S < 1`.
* `Gap212.Sieve.residueWeight_bounds`: `(3(k-1)(k-1))^{ω} ≤ v(q) ≤ τ(q)^13`.
* `Gap212.Sieve.card_tuple_multiplicity`: at most `(3(k-1))^{ω(q/W(x))}` divisor tuples generate
  a given squarefree modulus `q`.
* `Gap212.Sieve.omit_square_le`: `w(P² + 2PQ) ≤ w(P+Q)²` for `w ≥ 0`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY

/-! ## The normalization -/

/-- **The normalization is not too small**: `𝓒_x ≥ x/(log x)^{k+1} > 0` for every large `x`, at
`k = m + 1`.

`φ(W) ≤ W` turns `W^{k-1}/φ(W)^k` into at least `1/W`, and `W(x) ≤ log x`
(`Gap212.Sieve.W_le_log`) turns the remaining `1/W` into `1/log x`. -/
@[gap212 "lem_calC_lower_bound"]
theorem calC_lower_bound (m : ℕ) : ∀ᶠ x : ℝ in atTop,
    x / Real.log x ^ (m + 2) ≤ calC m x ∧ 0 < x / Real.log x ^ (m + 2) := by
  filter_upwards [W_le_log, eventually_gt_atTop (1 : ℝ)] with x hWL hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hL : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hφpos : (0 : ℝ) < ((W x).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (primorial_pos _)
  have hφW : ((W x).totient : ℝ) ≤ (W x : ℝ) := by exact_mod_cast Nat.totient_le _
  refine ⟨?_, by positivity⟩
  rw [calC, div_le_div_iff₀ (by positivity) (by positivity)]
  calc x * (((W x).totient : ℝ) ^ (m + 1) * Real.log x ^ (m + 1))
      ≤ x * ((W x : ℝ) ^ m * (W x : ℝ) * Real.log x ^ (m + 1)) := by rw [← pow_succ]; gcongr
    _ ≤ x * ((W x : ℝ) ^ m * Real.log x * Real.log x ^ (m + 1)) := by gcongr
    _ = x * (W x : ℝ) ^ m * Real.log x ^ (m + 2) := by ring

/-! ## The moduli the denominator generates -/

/-- **The denominator moduli have exponent below one.** For a support datum `p`, bands `j, j'` and
`ε₀ ∈ (0,1)`, write `S = (A_j + ε) + (A_{j'} + ε)`. Then `S < 1`, and for every large `x` and every
pair of positive divisor tuples whose logarithmic sizes lie in the two retreat regions,
`W(x)∏ᵢ[dᵢ,d'ᵢ] ≤ x^S`.

Three inputs. `[dᵢ,d'ᵢ] ≤ dᵢd'ᵢ` and `dᵢ = x^{log_x dᵢ}` turn the product into `x` to the sum of
the two coordinate sums, which the retreat regions cap by `(1-ε₀)S`. `W(x) ≤ log x ≤ x^{ε₀S}`
supplies the missing `x^{ε₀S}`, and this is where `S > 0` — itself `A_j + ε > A_0 + ε = 0` — is
spent. The bound `S < 1` is `A_j + ε ≤ A_n + ε < 1/2` on each side. -/
@[gap212 "lem_denominator_modulus_exponent"]
theorem denominator_modulus_exponent (p : SupportParams) (k : ℕ) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) (j j' : Fin p.n) :
    (p.A j.succ + p.ε) + (p.A j'.succ + p.ε) < 1 ∧
      ∀ᶠ x : ℝ in atTop, ∀ d d' : Fin k → ℕ, (∀ i, 0 < d i) → (∀ i, 0 < d' i) →
        (fun i ↦ logScale x (d i)) ∈ retreatRegion p k j ε₀ →
        (fun i ↦ logScale x (d' i)) ∈ retreatRegion p k j' ε₀ →
        (W x : ℝ) * ∏ i, ((d i).lcm (d' i) : ℝ)
          ≤ x ^ ((p.A j.succ + p.ε) + (p.A j'.succ + p.ε)) := by
  -- Each band's node, shifted by `ε`, is positive and below `1/2`.
  have node (b : Fin p.n) : 0 < p.A b.succ + p.ε ∧ p.A b.succ + p.ε < 1 / 2 := by
    constructor <;> linarith [p.A_mono (Fin.succ_pos b), p.A_mono.monotone (Fin.le_last b.succ),
      p.A_zero, p.A_last]
  set S := (p.A j.succ + p.ε) + (p.A j'.succ + p.ε)
  have hSpos : 0 < S := by linarith [(node j).1, (node j').1]
  refine ⟨by linarith [(node j).2, (node j').2], ?_⟩
  -- `log x ≤ x^{ε₀ S}` for large `x`.
  have hsmall : ∀ᶠ x : ℝ in atTop, Real.log x ≤ x ^ (ε₀ * S) := by
    filter_upwards [(isLittleO_log_rpow_atTop (r := ε₀ * S) (by positivity)).bound one_pos,
      eventually_ge_atTop (1 : ℝ)] with x hx hx1
    simpa [abs_of_nonneg (Real.log_nonneg hx1), abs_of_pos (by positivity : 0 < x ^ (ε₀ * S))]
      using hx
  filter_upwards [W_le_log, hsmall, eventually_gt_atTop (1 : ℝ)] with x hWL hlog hx1
    d d' hd hd' hmem hmem'
  have hx0 : (0 : ℝ) < x := by linarith
  -- The two coordinate sums are capped by the two retreat regions.
  have hsum : (∑ i, logScale x (d i)) + (∑ i, logScale x (d' i)) ≤ (1 - ε₀) * S := by
    linarith [hmem.2.1, hmem'.2.1]
  -- Each tuple's product is `x` to its coordinate sum.
  have hprod (e : Fin k → ℕ) (he : ∀ i, 0 < e i) :
      ∏ i, ((e i : ℝ)) = x ^ (∑ i, logScale x (e i)) := by
    rw [Real.rpow_sum_of_pos hx0]
    exact prod_congr rfl fun i _ ↦ (Gap212.rpow_logScale hx1 (by exact_mod_cast he i)).symm
  calc (W x : ℝ) * ∏ i, ((d i).lcm (d' i) : ℝ)
      ≤ x ^ (ε₀ * S) * ∏ i, ((d i : ℝ) * (d' i : ℝ)) := by
        gcongr with i
        · exact hWL.trans hlog
        · exact_mod_cast Nat.lcm_le_mul (hd i) (hd' i)
    _ = x ^ (ε₀ * S) * x ^ ((∑ i, logScale x (d i)) + (∑ i, logScale x (d' i))) := by
        rw [prod_mul_distrib, hprod d hd, hprod d' hd', Real.rpow_add hx0]
    _ ≤ x ^ (ε₀ * S) * x ^ ((1 - ε₀) * S) := by gcongr; exact hx1.le
    _ = x ^ S := by rw [← Real.rpow_add hx0]; ring_nf

/-! ## How many divisor tuples generate a modulus -/

/-- A prime divides the lcm of at most one coordinate of a pair of tuples whose coordinatewise lcms
multiply to a squarefree number. -/
theorem eq_of_prime_dvd_lcm {m r : ℕ} (hr : Squarefree r) {dd : (Fin m → ℕ) × (Fin m → ℕ)}
    (hdd : ∏ i, Nat.lcm (dd.1 i) (dd.2 i) = r) {ℓ : ℕ} (hℓ : ℓ.Prime) {i j : Fin m}
    (hi : ℓ ∣ Nat.lcm (dd.1 i) (dd.2 i)) (hj : ℓ ∣ Nat.lcm (dd.1 j) (dd.2 j)) : i = j := by
  classical
  by_contra hij
  have hsq := prod_dvd_prod_of_subset {i, j} univ (fun i ↦ Nat.lcm (dd.1 i) (dd.2 i))
    (subset_univ _)
  rw [prod_pair hij, hdd] at hsq
  exact hℓ.not_isUnit (hr ℓ ((mul_dvd_mul hi hj).trans hsq))

/-- Every prime factor of `∏ᵢ[dᵢ,d'ᵢ]` divides some coordinate's lcm. -/
theorem exists_dvd_lcm_of_mem_primeFactors {m ℓ : ℕ} {dd : (Fin m → ℕ) × (Fin m → ℕ)}
    (hℓ : ℓ ∈ (∏ i, Nat.lcm (dd.1 i) (dd.2 i)).primeFactors) :
    ∃ i : Fin m, ℓ ∣ Nat.lcm (dd.1 i) (dd.2 i) := by
  obtain ⟨i, -, hi⟩ := (Nat.prime_of_mem_primeFactors hℓ).prime.exists_mem_finset_dvd
    (Nat.dvd_of_mem_primeFactors hℓ)
  exact ⟨i, hi⟩

open Classical in
/-- The encoding of a prime `ℓ` against a pair of tuples: the coordinate whose lcm `ℓ` divides,
tagged `0` if `ℓ` divides only `dᵢ`, `1` if only `d'ᵢ`, and `2` if both. -/
private noncomputable def lcmCode {m : ℕ} (hm : 0 < m) (dd : (Fin m → ℕ) × (Fin m → ℕ))
    (ℓ : ℕ) : Fin m × Fin 3 :=
  if h : ∃ i : Fin m, ℓ ∣ Nat.lcm (dd.1 i) (dd.2 i) then
    (h.choose, if ℓ ∣ dd.1 h.choose then (if ℓ ∣ dd.2 h.choose then 2 else 0) else 1)
  else (⟨0, hm⟩, 0)

private theorem primeFactors_fst_eq_filter {m r : ℕ} (hm : 0 < m) (hr : Squarefree r)
    {dd : (Fin m → ℕ) × (Fin m → ℕ)} (hdd : ∏ i, Nat.lcm (dd.1 i) (dd.2 i) = r) (i : Fin m) :
    (dd.1 i).primeFactors
      = {ℓ ∈ r.primeFactors | (lcmCode hm dd ℓ).1 = i ∧ (lcmCode hm dd ℓ).2 ≠ 1} := by
  have hdvd : dd.1 i ∣ r :=
    (Nat.dvd_lcm_left _ _).trans (hdd ▸ Finset.dvd_prod_of_mem _ (mem_univ i))
  ext ℓ
  simp only [mem_filter, Nat.mem_primeFactors, ne_eq]
  constructor
  · rintro ⟨hℓp, hℓd, -⟩
    have hlcm := hℓd.trans (Nat.dvd_lcm_left (dd.1 i) (dd.2 i))
    have h : ∃ i : Fin m, ℓ ∣ Nat.lcm (dd.1 i) (dd.2 i) := ⟨i, hlcm⟩
    have hch : h.choose = i := eq_of_prime_dvd_lcm hr hdd hℓp h.choose_spec hlcm
    refine ⟨⟨hℓp, hℓd.trans hdvd, hr.ne_zero⟩, ?_⟩
    simp only [lcmCode, dif_pos h, hch, if_pos hℓd, true_and]
    split_ifs <;> decide
  · rintro ⟨hℓr, h1, h2⟩
    have h := exists_dvd_lcm_of_mem_primeFactors (hdd ▸ Nat.mem_primeFactors.2 hℓr)
    have hch : h.choose = i := by simpa only [lcmCode, dif_pos h] using h1
    have hdv : ℓ ∣ dd.1 h.choose := by
      by_contra hnd
      exact h2 (by simp only [lcmCode, dif_pos h, if_neg hnd])
    exact ⟨hℓr.1, hch ▸ hdv, ne_zero_of_dvd_ne_zero hr.ne_zero hdvd⟩

private theorem primeFactors_snd_eq_filter {m r : ℕ} (hm : 0 < m) (hr : Squarefree r)
    {dd : (Fin m → ℕ) × (Fin m → ℕ)} (hdd : ∏ i, Nat.lcm (dd.1 i) (dd.2 i) = r) (i : Fin m) :
    (dd.2 i).primeFactors
      = {ℓ ∈ r.primeFactors | (lcmCode hm dd ℓ).1 = i ∧ (lcmCode hm dd ℓ).2 ≠ 0} := by
  have hdvd : dd.2 i ∣ r :=
    (Nat.dvd_lcm_right _ _).trans (hdd ▸ Finset.dvd_prod_of_mem _ (mem_univ i))
  ext ℓ
  simp only [mem_filter, Nat.mem_primeFactors, ne_eq]
  constructor
  · rintro ⟨hℓp, hℓd, -⟩
    have hlcm := hℓd.trans (Nat.dvd_lcm_right (dd.1 i) (dd.2 i))
    have h : ∃ i : Fin m, ℓ ∣ Nat.lcm (dd.1 i) (dd.2 i) := ⟨i, hlcm⟩
    have hch : h.choose = i := eq_of_prime_dvd_lcm hr hdd hℓp h.choose_spec hlcm
    refine ⟨⟨hℓp, hℓd.trans hdvd, hr.ne_zero⟩, ?_⟩
    simp only [lcmCode, dif_pos h, hch, if_pos hℓd, true_and]
    split_ifs <;> decide
  · rintro ⟨hℓr, h1, h2⟩
    have h := exists_dvd_lcm_of_mem_primeFactors (hdd ▸ Nat.mem_primeFactors.2 hℓr)
    have hch : h.choose = i := by simpa only [lcmCode, dif_pos h] using h1
    have hdv : ℓ ∣ dd.2 h.choose := by
      by_cases hnd : ℓ ∣ dd.1 h.choose
      · by_contra hnd2
        exact h2 (by simp only [lcmCode, dif_pos h, if_pos hnd, if_neg hnd2])
      · exact (Nat.Prime.dvd_or_dvd_of_dvd_lcm hℓr.1 h.choose_spec).resolve_left hnd
    exact ⟨hℓr.1, hch ▸ hdv, ne_zero_of_dvd_ne_zero hr.ne_zero hdvd⟩

/-- **The multiplicity bound at a squarefree modulus.** For squarefree `r` and `m ≥ 1`, the set of
pairs of `m`-tuples whose coordinatewise lcms multiply to `r` is finite, of size at most
`(3m)^{ω(r)}`.

Each prime `ℓ ∣ r` divides exactly one `[dᵢ,d'ᵢ]` — two would put `ℓ²` into the squarefree `r` —
and then falls into one of three cases: `ℓ ∣ dᵢ` only, `ℓ ∣ d'ᵢ` only, or both. Sending `ℓ` to that
coordinate and that case is an injection into `ω(r)`-tuples over a `3m`-element set, and it *is*
injective because every `dᵢ` divides `r`, hence is squarefree, hence is the product of its prime
factors — which the encoding determines. -/
theorem card_lcm_tuples_le {m : ℕ} (hm : 0 < m) {r : ℕ} (hr : Squarefree r) :
    {dd : (Fin m → ℕ) × (Fin m → ℕ) | ∏ i, Nat.lcm (dd.1 i) (dd.2 i) = r}.Finite ∧
      {dd : (Fin m → ℕ) × (Fin m → ℕ) | ∏ i, Nat.lcm (dd.1 i) (dd.2 i) = r}.ncard
        ≤ (3 * m) ^ r.primeFactors.card := by
  classical
  set S := {dd : (Fin m → ℕ) × (Fin m → ℕ) | ∏ i, Nat.lcm (dd.1 i) (dd.2 i) = r}
  -- The encoding is injective: each coordinate is the product of the primes assigned to it.
  have hinj : Set.InjOn (fun dd ↦ (fun ℓ : ↥r.primeFactors ↦ lcmCode hm dd ℓ.1)) S := by
    intro dd (hdd : _ = r) ee (hee : _ = r) heq
    have hpe : ∀ ℓ ∈ r.primeFactors, lcmCode hm dd ℓ = lcmCode hm ee ℓ :=
      fun ℓ hℓ ↦ congrFun heq ⟨ℓ, hℓ⟩
    have hsf : ∀ {ff : (Fin m → ℕ) × (Fin m → ℕ)}, ∏ i, Nat.lcm (ff.1 i) (ff.2 i) = r →
        ∀ i, Squarefree (ff.1 i) ∧ Squarefree (ff.2 i) := fun hff i ↦
      ⟨hr.squarefree_of_dvd ((Nat.dvd_lcm_left _ _).trans (hff ▸ dvd_prod_of_mem _ (mem_univ i))),
        hr.squarefree_of_dvd ((Nat.dvd_lcm_right _ _).trans (hff ▸ dvd_prod_of_mem _ (mem_univ i)))⟩
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)
    · rw [← Nat.prod_primeFactors_of_squarefree (hsf hdd i).1,
        ← Nat.prod_primeFactors_of_squarefree (hsf hee i).1,
        primeFactors_fst_eq_filter hm hr hdd i, primeFactors_fst_eq_filter hm hr hee i]
      exact prod_congr (filter_congr fun ℓ hℓ ↦ by rw [hpe ℓ hℓ]) fun _ _ ↦ rfl
    · rw [← Nat.prod_primeFactors_of_squarefree (hsf hdd i).2,
        ← Nat.prod_primeFactors_of_squarefree (hsf hee i).2,
        primeFactors_snd_eq_filter hm hr hdd i, primeFactors_snd_eq_filter hm hr hee i]
      exact prod_congr (filter_congr fun ℓ hℓ ↦ by rw [hpe ℓ hℓ]) fun _ _ ↦ rfl
  refine ⟨.of_finite_image (Set.toFinite _) hinj, ?_⟩
  calc S.ncard ≤ (Set.univ : Set (↥r.primeFactors → Fin m × Fin 3)).ncard :=
        Set.ncard_le_ncard_of_injOn _ (fun _ _ ↦ Set.mem_univ _) hinj Set.finite_univ
    _ = (3 * m) ^ r.primeFactors.card := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fin, Fintype.card_coe, Nat.mul_comm]

/-- **The number of divisor tuples generating a modulus.** At `k = m + 1 ≥ 2` and for squarefree
`q` divisible by `W(x)`, the tuples `((dᵢ), (d'ᵢ))` of positive integers with
`W(x)∏ᵢ[dᵢ,d'ᵢ] = q` are finite in number, and there are at most `(3(k-1))^{ω(q/W(x))}` of them.

The removed coordinate `i₀` does not appear: the remaining `k - 1` coordinates are indexed by
`Fin m`, and the count depends on nothing but how many of them there are. Dividing out `W(x)` turns
the condition into `∏ᵢ[dᵢ,d'ᵢ] = q/W(x)`, and positivity of the entries is then automatic, so this
is `Gap212.Sieve.card_lcm_tuples_le` at `r = q/W(x)`. -/
@[gap212 "lem_tuple_multiplicity"]
theorem card_tuple_multiplicity {m : ℕ} (hm : 0 < m) {x : ℝ} {q : ℕ} (hq : Squarefree q)
    (hWq : W x ∣ q) :
    {dd : (Fin m → ℕ) × (Fin m → ℕ) | (∀ i, 0 < dd.1 i) ∧ (∀ i, 0 < dd.2 i) ∧
        W x * ∏ i, Nat.lcm (dd.1 i) (dd.2 i) = q}.Finite ∧
      {dd : (Fin m → ℕ) × (Fin m → ℕ) | (∀ i, 0 < dd.1 i) ∧ (∀ i, 0 < dd.2 i) ∧
          W x * ∏ i, Nat.lcm (dd.1 i) (dd.2 i) = q}.ncard
        ≤ (3 * m) ^ (q / W x).primeFactors.card := by
  have hr : Squarefree (q / W x) := hq.squarefree_of_dvd (Nat.div_dvd_of_dvd hWq)
  -- The condition on a tuple is exactly `∏ᵢ[dᵢ,d'ᵢ] = q/W(x)`; positivity comes for free.
  have hpos : ∀ dd : (Fin m → ℕ) × (Fin m → ℕ),
      ∏ i, Nat.lcm (dd.1 i) (dd.2 i) = q / W x → (∀ i, 0 < dd.1 i) ∧ (∀ i, 0 < dd.2 i) := by
    intro dd h
    constructor <;> intro i <;> refine Nat.pos_of_ne_zero fun h0 ↦ ?_ <;>
      exact hr.ne_zero (h ▸ Finset.prod_eq_zero (mem_univ i) (by simp [h0]))
  have hset : {dd : (Fin m → ℕ) × (Fin m → ℕ) | (∀ i, 0 < dd.1 i) ∧ (∀ i, 0 < dd.2 i) ∧
      W x * ∏ i, Nat.lcm (dd.1 i) (dd.2 i) = q}
      = {dd : (Fin m → ℕ) × (Fin m → ℕ) | ∏ i, Nat.lcm (dd.1 i) (dd.2 i) = q / W x} := by
    ext dd
    exact ⟨fun h ↦ Nat.eq_div_of_mul_eq_right (primorial_pos _).ne' h.2.2,
      fun h ↦ ⟨(hpos dd h).1, (hpos dd h).2, by rw [h, Nat.mul_div_cancel' hWq]⟩⟩
  exact hset ▸ card_lcm_tuples_le hm hr

/-! ## The residue weight -/

/-- The number of divisors of a squarefree number is `2^{ω(q)}`: every exponent in its
factorization is exactly `1`, so `Nat.card_divisors`' product is a product of twos. -/
theorem card_divisors_of_squarefree {q : ℕ} (hq : Squarefree q) :
    q.divisors.card = 2 ^ q.primeFactors.card := by
  rw [Nat.card_divisors hq.ne_zero, Finset.prod_congr rfl
    (fun p hp ↦ show q.factorization p + 1 = 2 by
      have h1 : q.factorization p ≤ 1 := hq.natFactorization_le_one p
      have h2 : 1 ≤ q.factorization p := Nat.Prime.factorization_pos_of_dvd
        (Nat.prime_of_mem_primeFactors hp) hq.ne_zero (Nat.dvd_of_mem_primeFactors hp)
      lia), Finset.prod_const]

/-- **The residue weight is a fixed divisor power.** At `k = 45` and for squarefree `q` divisible
by `W(x)`, the combined multiplicity `(3(k-1))^{ω(q/W(x))}·(k-1)^{ω(q/W(x))}` is exactly `v(q)`,
and `v(q) ≤ τ(q)^13`.

The first half is the arithmetic `3·44·44 = 5808`, which is `v`'s base by definition. The second is
`5808 < 8192 = 2^13` together with `τ(q) = 2^{ω(q)}` for squarefree `q` and `ω(q/W(x)) ≤ ω(q)`,
which holds because `q/W(x)` divides `q`. Had the base exceeded `8192` the exponent would have
risen, and with it the logarithmic saving the endpoint has to supply.

Nothing here looks at the size of `x`, so no hypothesis `x > 1` is needed. -/
@[gap212 "lem_weight_tau_power"]
theorem residueWeight_bounds {k : ℕ} (hk : k = 45) {x : ℝ} {q : ℕ}
    (hq : Squarefree q) (hWq : W x ∣ q) :
    (3 * (k - 1)) ^ (q / W x).primeFactors.card * (k - 1) ^ (q / W x).primeFactors.card
        ≤ residueWeight x q ∧
      residueWeight x q ≤ q.divisors.card ^ 13 := by
  rw [residueWeight]
  refine ⟨by subst hk; rw [← mul_pow]; norm_num, ?_⟩
  rw [card_divisors_of_squarefree hq, ← pow_mul, mul_comm, pow_mul]
  calc 5808 ^ (q / W x).primeFactors.card ≤ 5808 ^ q.primeFactors.card :=
        Nat.pow_le_pow_right (by norm_num)
          (card_le_card (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hWq) hq.ne_zero))
    _ ≤ (2 ^ 13) ^ q.primeFactors.card := Nat.pow_le_pow_left (by norm_num) _

/-! ## The omitted square -/

/-- **Omitting a weighted square gives a lower bound**: `w(P² + 2PQ) ≤ w(P+Q)²` for `w ≥ 0`.

The difference is `wQ²`, a non-negative number times a square. This is the step that makes the
numerator evaluation a lower bound rather than an equality: `P` collects the tensor indices in
`𝓛(i)` and `Q` those in `𝓤(i)`, and the omitted `wQ²` is of the same order as the main term
whenever `𝓤(i)` is non-empty, so no equality is available and none is needed. -/
@[gap212 "lem_omit_square_lower_bound"]
theorem omit_square_le {w : ℝ} (hw : 0 ≤ w) (P Q : ℝ) :
    w * (P ^ 2 + 2 * P * Q) ≤ w * (P + Q) ^ 2 := by
  nlinarith [mul_nonneg hw (sq_nonneg Q)]

/-- **The lcm of two squarefree numbers is squarefree.** -/
theorem squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (a.lcm b) := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have hb0 : b ≠ 0 := hb.ne_zero
  rw [Nat.squarefree_iff_factorization_le_one (Nat.lcm_ne_zero ha0 hb0),
    Nat.factorization_lcm ha0 hb0]
  exact fun p ↦ sup_le ((Nat.squarefree_iff_factorization_le_one ha0).mp ha p)
    ((Nat.squarefree_iff_factorization_le_one hb0).mp hb p)

end Gap212.Sieve
