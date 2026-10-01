/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Asymptotics
public import Gap212.Sieve.Certificate
public import Gap212.Sieve.SelbergErrorTerm
public import Gap212.Sieve.WSieve

/-!
# `Gap212.Sieve.NuDenominatorUnrestricted` is false

The unrestricted form `Gap212.Sieve.NuDenominatorUnrestricted` of the denominator asymptotic
quantifies over the profile families with **no regularity at all**: no `ContDiff`, no compact
support, no constraint on `ε₀`, and no monotonicity of the shift tuple. The theorem it is derived
from, `Gap212.Sieve.selberg_progression_sum`, carries all four. That is not a conservative
difference — an asymptotic identifying `∑ν` with an integral of `F'G'` cannot hold for an `F` whose
derivative the integral cannot see, and this module exhibits the failure.

## The witness

`Gap212.Sieve.spike` is the indicator of `{0}`. It is a legitimate value of
`NuDenominatorUnrestricted`'s `F` binder, and its support clause holds at **every** support datum,
band and `ε₀ < 1`, because the product `∏ᵢ spike (tᵢ)` is non-zero only at the origin, which every
retreat region contains (`Gap212.Sieve.zero_mem_retreatRegion`). At that witness:

* `λ_spike(n) = 1` for every `n ≥ 1` (`Gap212.Sieve.lambdaF_spike`) — only the divisor `d = 1` has
  `log_x d = 0` — so `ν ≡ 1` and `∑_{n ≡ b (W x)} ν(n)` is the **size of the residue class**,
  which is `x/W(x) + O(1)`;
* `deriv spike` vanishes on `(0,∞)`, so every Gram entry is `0` and the claimed main term
  `𝓘 = formI c (gramInner F)` is `0` (`Gap212.Sieve.formI_gramInner_spike`).

So `NuDenominatorUnrestricted 45` asserts `x/W(x) + O(1) ≤ η·𝓒_x` for every `η > 0`, and `𝓒_x` is
smaller than `x/W(x)` by `((W/φ(W))/\log x)^{45}`. `Gap212.Sieve.W_le_log` and `φ(W(x)) ≥ 2` make
that explicit enough to close: `Gap212.Sieve.not_nuDenominatorUnrestricted`.

## The restricted form

`Gap212.Sieve.NuDenominator` is stated at a `Gap212.GPY.TensorDatum`, and the spike is not such a
factor (`Gap212.Sieve.tensorDatum_f_ne_spike`). At `45` it is a theorem,
`Gap212.Sieve.nuDenominator_45`.

The intended statement is about the tensor weight of a **tensor datum**, whose factors are
smooth.

## Main results

* `Gap212.Sieve.zero_mem_retreatRegion`: every retreat region at `ε₀ < 1` contains the origin.
* `Gap212.Sieve.not_nuDenominatorUnrestricted`: `¬ Gap212.Sieve.NuDenominatorUnrestricted 45`.
  **Not** `¬ Gap212.Sieve.NuDenominator 45` — that is a different `Prop`, and it is a
  **theorem**, `Gap212.Sieve.nuDenominator_45`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.Defs Gap212.GPY

/-! ## Every retreat region contains the origin -/

/-- **The origin is retreated at every band.** `(1 - ε₀)(A_{j+1} + ε) > 0` because `A₀ = -ε` and
`A` is strictly increasing, and the rough index set of the origin is empty because `δ > 0`, where
the cap clause reads `0 ≤ (1 - ε₀)·B_{j,0} = 0`.

This is what makes the witness of `Gap212.Sieve.not_nuDenominatorUnrestricted` admissible at every
support datum rather than at a contrived one. -/
theorem zero_mem_retreatRegion (p : SupportParams) (k : ℕ) (j : Fin p.n) {ε₀ : ℝ} (hε₀ : ε₀ < 1) :
    (fun _ ↦ (0 : ℝ)) ∈ retreatRegion p k j ε₀ := by
  have hA : -p.ε < p.A j.succ := p.A_zero ▸ p.A_mono (Fin.succ_pos j)
  have hrough : p.roughIdx k (fun _ ↦ (0 : ℝ)) = ∅ :=
    Finset.filter_false_of_mem fun _ _ ↦ not_le.2 p.δ_pos
  refine ⟨fun i ↦ ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩
  · rw [Finset.sum_const_zero]
    exact mul_pos (by linarith) (by linarith)
  · rw [hrough, Finset.sum_empty, Finset.card_empty, p.B_zero j, mul_zero]

/-! ## The witness -/

/-- **The indicator of `{0}`**, a legitimate value of the profile binder of
`Gap212.Sieve.NuDenominatorUnrestricted`, which asks nothing of its profiles. Its divisor weight is
identically `1` and its derivative vanishes off the origin, which is the contradiction. -/
noncomputable def spike : ℝ → ℝ := fun t ↦ if t = 0 then 1 else 0

/-- **The spike has divisor weight `1`.** `λ_F(n) = ∑_{d ∣ n} μ(d) F(log_x d)`, and `log_x d = 0`
exactly at `d = 1`, so only that divisor contributes and it contributes `μ(1) = 1`. -/
theorem lambdaF_spike {x : ℝ} (hx : 1 < x) {n : ℕ} (hn : n ≠ 0) : lambdaF spike x n = 1 := by
  rw [lambdaF, Finset.sum_eq_single_of_mem 1 (Nat.one_mem_divisors.mpr hn)]
  · simp [spike, Gap212.Notation.logx]
  · intro d hd hd1
    have hd2 : 2 ≤ d := by have := Nat.pos_of_mem_divisors hd; omega
    have hlogd : 0 < Real.log d := Real.log_pos (by exact_mod_cast hd2)
    simp [spike, Gap212.Notation.logx, (div_pos hlogd (Real.log_pos hx)).ne']

/-- **The spike's derivative vanishes off the origin**, being locally constant there. -/
theorem deriv_spike {t : ℝ} (ht : t ≠ 0) : deriv spike t = 0 := by
  have hev : spike =ᶠ[nhds t] fun _ ↦ (0 : ℝ) := by
    filter_upwards [isOpen_ne.mem_nhds ht] with u hu
    simp [spike, hu]
  rw [hev.deriv_eq, deriv_const]

/-- **The spike's Gram data vanish**, the integral running over `(0,∞)` where the derivative is
`0`. -/
theorem gramInner_spike {L k : ℕ} (l l' : Fin L) (s : Fin k) :
    gramInner (fun (_ : Fin L) (_ : Fin k) ↦ spike) l l' s = 0 :=
  MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ by
    rw [deriv_spike (ne_of_gt ht), mul_zero]

/-- **The spike's discrete energy is `0`.** Each `𝓘`-summand is a product over the `k ≥ 1`
coordinates of vanishing Gram entries. -/
theorem formI_gramInner_spike {L k : ℕ} (hk : k ≠ 0) (c : Fin L → ℝ) :
    formI c (gramInner (fun (_ : Fin L) (_ : Fin k) ↦ spike)) = 0 :=
  Finset.sum_eq_zero fun l _ ↦ Finset.sum_eq_zero fun l' _ ↦ mul_eq_zero_of_right _ <|
    Finset.prod_eq_zero (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero hk⟩) (gramInner_spike l l' _)

/-! ## The refutation -/

/-- **`Gap212.Sieve.NuDenominatorUnrestricted 45` is false.**

This refutes the **unrestricted** form, which quantifies over data that
`Gap212.Sieve.selberg_progression_sum` never supplies. The restricted
`Gap212.Sieve.NuDenominator 45` is a **theorem**, `Gap212.Sieve.nuDenominator_45`; the two
`Prop`s are distinct.

At the spike witness the statement asserts that the pre-sieved class `{n ∈ [x,2x] : n ≡ 1 (W(x))}`
has at most `η·𝓒_x` members for every `η > 0`. The class has `x/W(x) + O(1)` members
(`Gap212.Sieve.abs_card_dyadic_filter_modEq_sub_le`), while `W(x) ≤ \log x`
(`Gap212.Sieve.W_le_log`) and `φ(W(x)) ≥ 2` give `𝓒_x ≤ x/(2\log x)`. Taking `η = 1` and any `x`
with `5\log x ≤ x` closes it.

See `Gap212.Sieve.nuDenominator_of_obligations` for the statement that does follow. -/
theorem not_nuDenominatorUnrestricted : ¬ NuDenominatorUnrestricted 45 := by
  intro hden
  -- The witness data: one tensor term, the spike in every coordinate, no shifts.
  have hsupp : ∀ l : Fin 1, ∀ t : Fin 45 → ℝ, (∀ i, 0 ≤ t i) →
      (∏ i, (fun (_ : Fin 1) (_ : Fin 45) ↦ spike) l i (t i)) ≠ 0 →
      t ∈ retreatRegion gap212Params 45 ⟨0, gap212Params.n_pos⟩ (1 / 2 : ℝ) := by
    intro l t _ hne
    obtain rfl : t = fun _ ↦ 0 := funext fun i ↦ by_contra fun hi ↦
      Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i) (if_neg hi)
    exact zero_mem_retreatRegion _ _ _ (by norm_num)
  obtain ⟨X, hX⟩ := hden gap212Params (1 / 2) ⟨0, gap212Params.n_pos⟩ 1 (fun _ ↦ 1)
    (fun _ _ ↦ spike) (fun _ ↦ 0) hsupp 1 one_pos
  -- A single `x` large enough for all four facts.
  have hsmall : ∀ᶠ x : ℝ in atTop, 5 * Real.log x ≤ x := by
    filter_upwards [Real.isLittleO_log_id_atTop.bound (c := 1 / 5) (by norm_num),
      eventually_ge_atTop (1 : ℝ)] with u hu hu1
    rw [id, Real.norm_of_nonneg (Real.log_nonneg hu1), Real.norm_of_nonneg (by linarith : 0 ≤ u)]
      at hu
    linarith
  obtain ⟨x, ⟨⟨⟨hWL, hdvd⟩, hlog5⟩, hx1⟩, hxX⟩ :=
    ((((W_le_log.and (eventually_dvd_W_of_prime_le 3)).and hsmall).and
      (eventually_gt_atTop (1 : ℝ))).and (eventually_gt_atTop X)).exists
  -- The arithmetic of the pre-sieving modulus at that `x`.
  have hWpos : 0 < W x := primorial_pos _
  have hW6 : 6 ≤ W x := Nat.le_of_dvd hWpos (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    (hdvd 2 Nat.prime_two (by norm_num)) (hdvd 3 Nat.prime_three (by norm_num)))
  have hφ : 2 ≤ (W x).totient := by
    have := Nat.totient_pos.mpr hWpos
    have : (W x).totient ≠ 1 := fun h ↦ by rcases Nat.totient_eq_one_iff.mp h with h | h <;> omega
    omega
  have hW1 : (1 : ℝ) ≤ (W x : ℝ) := by exact_mod_cast hWpos
  have hLpos : 0 < Real.log x := zero_lt_one.trans_le (hW1.trans hWL)
  have hφR : (2 : ℝ) ≤ ((W x).totient : ℝ) := by exact_mod_cast hφ
  have hx0 : 0 < x := zero_lt_one.trans hx1
  -- The asserted bound at the witness: the class is at most `𝓒_x`.
  have hcard : (#{n ∈ dyadic x | n ≡ 1 [MOD W x]} : ℝ) ≤ scale 45 x := by
    have hb : Defs.IsPreSieved 1 (W x) (fun _ : Fin 45 ↦ 0) := fun i ↦ by simp
    have hnu : ∀ n ∈ {n ∈ dyadic x | n ≡ 1 [MOD W x]},
        nu 1 (fun _ ↦ 1) (fun (_ : Fin 1) (_ : Fin 45) ↦ spike) (fun (_ : Fin 45) ↦ 0) x n = 1 := by
      intro n hn
      have hn0 : n ≠ 0 := by
        have hmem := (Finset.mem_filter.mp hn).1
        rw [Gap212.dyadic, Finset.mem_Icc] at hmem
        have : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr hx0
        omega
      simp [nu, lambdaF_spike hx1 hn0]
    have hset : {n ∈ dyadic x | n ≡ 1 [MOD W x]}
        = {n ∈ dyadic x | n % W x = 1 % W x} := rfl
    have := hX x hxX 1 hb
    rw [formI_gramInner_spike (by norm_num), zero_mul, sub_zero, one_mul, ← hset,
      Finset.sum_congr rfl hnu, Finset.sum_const, nsmul_eq_mul, mul_one] at this
    exact le_of_abs_le this
  -- The class is large, and the scale is small.
  have hlow : x / (W x : ℝ) - 2 ≤ (#{n ∈ dyadic x | n ≡ 1 [MOD W x]} : ℝ) := by
    linarith [(abs_le.mp (abs_card_dyadic_filter_modEq_sub_le (a := 1) hx1.le hWpos)).1]
  have hxW : x / Real.log x ≤ x / (W x : ℝ) :=
    div_le_div_of_nonneg_left hx0.le (by linarith) hWL
  have hscale : scale 45 x ≤ x / Real.log x / 2 := by
    have hφ45 : (2 : ℝ) ≤ ((W x).totient : ℝ) ^ 45 :=
      hφR.trans (le_self_pow₀ (by linarith) (by norm_num))
    rw [scale]
    calc x * (W x : ℝ) ^ (45 - 1) / (((W x).totient : ℝ) ^ 45 * Real.log x ^ 45)
        ≤ x * Real.log x ^ 44 / (2 * Real.log x ^ 45) := by
          norm_num only
          gcongr
      _ = x / Real.log x / 2 := by
          rw [pow_succ]
          field_simp
  -- `x/\log x ≥ 5` is more than the two bounds can both survive.
  have hu5 : (5 : ℝ) ≤ x / Real.log x := (le_div_iff₀ hLpos).2 (by linarith)
  linarith

/-! ## Why the restatement escapes the witness -/

/-- **The witness is not `C¹`**, being discontinuous at the origin: it is `1` there and `0` on
every punctured neighbourhood. -/
theorem not_contDiff_spike : ¬ ContDiff ℝ 1 spike := by
  intro hcd
  have h1 : Filter.Tendsto spike (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds 1) := by
    simpa [spike] using (hcd.continuous.continuousAt (x := (0 : ℝ))).continuousWithinAt.tendsto
  have h2 : Filter.Tendsto spike (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds 0) :=
    tendsto_const_nhds.congr' <| by
      filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ 0)
      simp [spike, hu]
  exact one_ne_zero (tendsto_nhds_unique h1 h2)

/-- **No tensor datum has the witness as a factor.** `Gap212.GPY.TensorDatum.smooth` is the clause
that blocks it — not `compactSupport`, which the witness satisfies (it vanishes above `0`), and not
`supp_subset`, which it satisfies at every band (`Gap212.Sieve.zero_mem_retreatRegion`).

Hence `Gap212.Sieve.NuDenominator`, quantified over a tensor datum, is not refuted by the
witness. The proof is the step `C^∞ ⇒ C¹` against `Gap212.Sieve.not_contDiff_spike`. -/
theorem tensorDatum_f_ne_spike (p : SupportParams) {k : ℕ} {j : Fin p.n} {ε₀ : ℝ}
    (D : TensorDatum p k j ε₀) (l : Fin D.L) (i : Fin k) : D.f l i ≠ spike :=
  fun heq ↦ not_contDiff_spike (heq ▸ (D.smooth l i).of_le (by exact_mod_cast le_top))

/-! ## Why the same witness does NOT refute the numerator asymptotic -/

/-- **`𝓙ᵢ` vanishes when the skipped Gram data do.** Both of its groups carry `∏_{s≠i} inner`, so a
family whose skipped inner products all vanish has `𝓙ᵢ = 0` — in any positive number of remaining
coordinates, and whatever the boundary values and the index sets are. -/
theorem formJMarginal_eq_zero_of_gramInnerSkip_zero {L m : ℕ} (hm : m ≠ 0) (c bdry : Fin L → ℝ)
    {inner : Fin L → Fin L → Fin m → ℝ} (hinner : ∀ l l' s, inner l l' s = 0)
    (𝓛 𝓤 : Finset (Fin L)) : formJMarginal c bdry inner 𝓛 𝓤 = 0 := by
  have hz : ∀ l l' : Fin L, ∏ s, inner l l' s = 0 := fun l l' ↦
    Finset.prod_eq_zero (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero hm⟩) (hinner _ _ _)
  simp only [formJMarginal, formJLowLow, hz, mul_zero, Finset.sum_const_zero, add_zero]

/-- **The witness's skipped Gram data vanish**, for the same reason as
`Gap212.Sieve.gramInner_spike`. -/
theorem gramInnerSkip_spike {L m : ℕ} (i : Fin (m + 1)) (l l' : Fin L) (s : Fin m) :
    gramInnerSkip (fun (_ : Fin L) (_ : Fin (m + 1)) ↦ spike) i l l' s = 0 :=
  MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ by
    rw [deriv_spike (ne_of_gt ht), mul_zero]

/-- **The witness does not refute the numerator asymptotic**: at the spike family the conclusion of
`Gap212.Sieve.NumeratorAsymptoticUnrestricted` holds outright, for every `η ≥ 0`.

(`Gap212.Sieve.NumeratorAsymptotic` is stated at a tensor datum, of which the spike is not a
factor by `Gap212.Sieve.tensorDatum_f_ne_spike`.) So the refutation of the denominator's
unrestricted form does not transfer to the numerator's, even though the latter omits exactly the
same regularity. The numerator's claim is a
**lower** bound, and junk profiles do not only spoil `𝓘` — they send every `𝓙ᵢ` to `0` as well,
because `𝓙ᵢ` reads the same derivatives through `Gap212.Sieve.gramInnerSkip`
(`Gap212.Sieve.formJMarginal_eq_zero_of_gramInnerSkip_zero`). The bound then reads
`0 ≤ ∑ᵢ∑_n ν(n)ρ(n+hᵢ) + η·𝓒_x`, which holds because `ν ≥ 0` and `ρ ≥ 0`.

`ρ ≥ 0` everywhere is what `Gap212.Defs.RhoHypotheses` gives: `minorant` on the block and `support`
off it. -/
theorem le_numerator_at_spike {L m : ℕ} (hm : m ≠ 0) (c : Fin L → ℝ) (h : Fin (m + 1) → ℕ)
    (𝓛 𝓤 : Fin (m + 1) → Finset (Fin L)) {ρ : ℕ → ℝ → ℝ} {x η : ℝ}
    (hρ : ∀ n : ℕ, 0 ≤ ρ n x) (hη : 0 ≤ η) (hsc : 0 ≤ scale (m + 1) x) (b : ℕ) :
    (∑ i : Fin (m + 1), formJMarginal c (gramBdry (fun (_ : Fin L) (_ : Fin (m + 1)) ↦ spike) i)
          (gramInnerSkip (fun (_ : Fin L) (_ : Fin (m + 1)) ↦ spike) i) (𝓛 i) (𝓤 i)) *
        scale (m + 1) x - η * scale (m + 1) x ≤
      ∑ i : Fin (m + 1), ∑ n ∈ dyadic x with n % W x = b % W x,
        nu L c (fun (_ : Fin L) (_ : Fin (m + 1)) ↦ spike) h x n * ρ (n + h i) x := by
  rw [Finset.sum_eq_zero fun i _ ↦
    formJMarginal_eq_zero_of_gramInnerSkip_zero hm _ _ (gramInnerSkip_spike i) _ _, zero_mul,
    zero_sub]
  exact (neg_nonpos.2 (mul_nonneg hη hsc)).trans <| Finset.sum_nonneg fun i _ ↦
    Finset.sum_nonneg fun n _ ↦ mul_nonneg (nu_nonneg _ _ _ _ _ _) (hρ _)

end Gap212.Sieve
