/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Consequences.BundleNormalization
public import Gap212.Consequences.DconvCoefficientSequence
public import Gap212.Consequences.PointwiseFromEventual
public import Gap212.Equidistribution.Estimates.Assumed
public import Gap212.Harman.Challenge
public meta import Gap212.Attr

/-!
# The Bombieri–Vinogradov range, at one `x`

Every member of the Harman class equidistributes over the genuinely sub-half moduli
`𝒬_BV(x; B) = {q : 1 ≤ q ≤ x^{1/2}(log x)^{-B}}`, with the saving `A` asked for first and the
cutoff `B = B(A)` chosen after it. This is the half of the routing that the bilinear
Bombieri–Vinogradov input pays for; the positive-level range is the five Type estimates' business.

## No exponent in the statement

The hypotheses are `ξ₁ - ϵ > 0`, `ξ₂ - ϵ > 0` and `1 - 2ξ₃ - ϵ > 0`, and **no** exponent `ξ`
appears. The proof needs one, and chooses it:
`ξ = ½ min{ξ₁ - ϵ, ξ₂ - ϵ, 1 - 2ξ₃ - ϵ, ½}`, which is positive, strictly below each of the three
class exponents, and strictly below `½`. All four are needed, the last to leave room for the level
`ω_† = 1/100` of the Type I split; and none would follow from a hypothesis merely bounding `ξ` by
the other three, since `ξ₃` small with `ξ₁, ξ₂` near `1` admits `ξ > ½`. Quantifying `ξ` in the
statement and discharging `ξ < ½` from whatever the caller supplies would leave the statement
false, so it is chosen here.

## The four cases

Three of the four present the member as a *two*-factor convolution with both declared scales at
least `x^ξ` and Siegel–Walfisz on one of them, which is what `Gap212.BilinearBombieriVinogradov`
asks; the fourth does not go through that assumption at all. The three invocations are at three
different bundles — `K♭`, `Σ(Ψ(Ψ(K♭)))` and `Σ(K♭)`, where `K♭` is the normalization of
`Gap212.constantBundle_flat_transfer`, `Ψ` the convolution bundle `ConstantBundle.conv` and `Σ` the
Siegel–Walfisz update of `Gap212.exists_hasSiegelWalfisz_of_isSmoothAtScale` — so each returns its
own `B_i` and `C_i`. Taking `B = max B_i` is the safe direction: `log x > 1` for `x ≥ 3`, so the
range at `B` sits inside the range at each `B_i`.

* **Type II.** The witnesses are already two factors and `β` has Siegel–Walfisz at `N`. Both scales
  are large: `N ≥ x^{ξ₂-ϵ} ≥ x^ξ` directly, and the two-sided window `N ≤ x^{1-ξ₂+ϵ}` gives
  `M ≥ a₋ x / N ≥ a₋ x^{ξ₂-ϵ}`, which exceeds `x^ξ` beyond a threshold. The bound on `M` is
  available only because the Type II window is two-sided.
* **Type III.** The fourfold convolution is already left-associated, so `(α ⋆ ψ₁ ⋆ ψ₂) ⋆ ψ₃` needs
  no regrouping: `Gap212.isCoefficientSequence_and_locatedAtScale_dconv`, applied twice, makes the
  first factor a coefficient sequence located at `M N₁ N₂` for `Ψ(Ψ(K♭))`, the location of each
  `ψᵢ` coming from its smoothness; and `ψ₃` is smooth at `N₃ ≥ x^{1-2ξ₃-ϵ} ≥ x^ξ`, so it has the
  `Σ(Ψ(Ψ(K♭)))`-Siegel–Walfisz property there. The first scale is large with no threshold at all,
  since `M, N₂ ≥ 1` already give `M N₁ N₂ ≥ N₁ ≥ x^{1-2ξ₃-ϵ} ≥ x^ξ` — a route that, unlike
  `M N₁ N₂ ≥ a₋ x / N₃ ≥ a₋ x^{1-ξ₃-ϵ}`, needs neither a constant nor the sign of `ξ₃`.
* **Type I, and the case split the symmetric scale demand forces.** Here there is no upper bound on
  `N`, so `M ≍ x / N` may be bounded and `x^ξ ≤ M` can fail; those members are reached through
  `Gap212.TypeIBakerIrving` instead, at `ω_† = 1/100`, `θ = 1`, `δ = 1` and the window
  `γ₁ = ξ₁ - ϵ`, `γ₂ = max(γ₁, 1 + log a₊ / log 3)`, whose `max` is what makes `γ₁ ≤ γ₂` hold with
  no bound on `ξ₁` assumed, and which contains every member's `N` because `M ≥ 1` and
  `M N ≤ a₊ x` give `N ≤ a₊ x`. With `ε_†` a loss below the `ε₀` that estimate returns, the split
  is on `N ≤ x^{1/2+2ω_†+ε_†}` or not. Below, `M ≥ a₋ x^{1/2-2ω_†-ε_†}` exceeds `x^ξ` beyond a
  threshold and `β`'s smoothness supplies the property the class withholds, so the bilinear input
  applies at `Σ(K♭)`. Above, no bound on `M` is available and none is needed: that is the third
  branch of `Gap212.moduliI`, where both exponent inequalities are vacuous and the modulus family
  is all of `Gap212.moduliRange x ω_†`, which contains `𝒬_BV(x; B)`.

The split is on `N` alone, so it splits the class and not the sequence: each member is treated
whole, by whichever branch applies to it, and at least one always does — not exactly one.

## Two remarks that apply throughout

All but the Type III case need a threshold in `x`, because the bundle constants stand between a
scale bound `a₋ x^η` and the bound `x^ξ` the bilinear input asks; the three inequalities on `ξ` are
strict exactly so that such a threshold exists, and
`Gap212.hasEquidistribution_of_forall_ge` absorbs the bounded range at the end. And the scale
bounds on the first factor come from commensurability, `M N ≍_K x` giving `M ≥ a₋ x / N`: an
*upper* bound on `N` is what bounds `M` below, which is why the Type I split is needed at all.

In the three cases routed through the bilinear input, its conclusion carries a maximum over
primitive residue classes inside the sum, while what is wanted is one class `a`. That is a
weakening: `a` is coprime to every prime up to `x`, hence to `q`, and the discrepancy depends on
`a` only modulo `q`, so the term at `a` is one of the terms the maximum ranges over. Dropping the
non-squarefree moduli is a further weakening. The fourth case needs neither step.

## Main results

* `Gap212.exists_hasEquidistribution_subhalf_of_harmanClass`: the bound over `𝒬_BV(x; B)`.
-/

@[expose] public section

namespace Gap212

open Real Finset

/-! ## Scalar preliminaries -/

/-- `log x > 1` for `x ≥ 3`, since `e < 3`. This is what makes enlarging the cutoff `B` the safe
direction: `(log x)^B` is then increasing in `B`, so the range shrinks. -/
private theorem one_lt_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 < Real.log x := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  linarith [Real.exp_one_lt_d9]

/-- **A threshold beyond which a constant is absorbed by a gap in the exponent.** For `c > 0` and
`t < η` there is an `X ≥ 3` with `x^t ≤ c x^η` for every `x ≥ X`. This is the only use the three
strict inequalities on `ξ` are put to, and the reason they must be strict. -/
private theorem exists_threshold {c η t : ℝ} (hc : 0 < c) (h : t < η) :
    ∃ X ≥ (3 : ℝ), ∀ x ≥ X, x ^ t ≤ c * x ^ η := by
  refine ⟨max 3 ((1 / c) ^ (1 / (η - t))), le_max_left _ _, fun x hx ↦ ?_⟩
  have hxpos : (0 : ℝ) < x := by linarith [le_max_left 3 ((1 / c) ^ (1 / (η - t)))]
  have hd : 0 < η - t := by linarith
  have hkey : 1 / c ≤ x ^ (η - t) := calc
    1 / c = ((1 / c) ^ (1 / (η - t))) ^ (η - t) := by
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hd.ne', Real.rpow_one]
    _ ≤ x ^ (η - t) := Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hx) hd.le
  rw [div_le_iff₀ hc] at hkey
  rw [show η = t + (η - t) by ring, Real.rpow_add hxpos]
  nlinarith [Real.rpow_pos_of_pos hxpos t]

/-- **A bundle constant is absorbed at `x ≥ 3` by the exponent `log c / log 3`.** For `c ≥ 1` one
has `c ≤ x^{log c / log 3}`, which is what puts every member's `N` inside the Type I exponent
window `[x^{γ₁}, x^{γ₂}]` with no threshold in `x`. -/
private theorem le_rpow_log_div_log_three {c x : ℝ} (hc : 1 ≤ c) (hx : 3 ≤ x) :
    c ≤ x ^ (Real.log c / Real.log 3) := by
  calc c = (3 : ℝ) ^ (Real.log c / Real.log 3) := by
        rw [Real.rpow_def_of_pos (by norm_num), mul_div_assoc',
          mul_div_cancel_left₀ _ (Real.log_pos (by norm_num)).ne', Real.exp_log (by linarith)]
    _ ≤ x ^ (Real.log c / Real.log 3) := Real.rpow_le_rpow (by norm_num) hx
        (div_nonneg (Real.log_nonneg hc) (Real.log_nonneg (by norm_num)))

/-- **An upper bound on the second scale bounds the first below.** From `c x ≤ M N`, `0 < N` and
`N ≤ x^t` one gets `c x^{1-t} ≤ M`. This is the commensurability step the argument turns on: a
class that does not bound `N` above does not bound `M` below. -/
private theorem le_of_asympEq_of_le_rpow {c M N x t : ℝ} (hc : 0 ≤ c) (hxpos : 0 < x)
    (hN : 0 < N) (hNu : N ≤ x ^ t) (h : c * x ≤ M * N) : c * x ^ (1 - t) ≤ M := by
  refine le_of_mul_le_mul_right (le_trans ?_ h) hN
  calc c * x ^ (1 - t) * N ≤ c * x ^ (1 - t) * x ^ t := by gcongr
    _ = c * x := by rw [mul_assoc, ← Real.rpow_add hxpos, sub_add_cancel, Real.rpow_one]

/-- The cutoff `x^{1/2}(log x)^{-B}` is non-negative and at most `x`, for `x ≥ 3` and `B ≥ 0`. So
every modulus of `𝒬_BV(x; B)` is at most `x`, which is what the coprimality of the fixed residue
class to the modulus is read off. -/
private theorem subhalf_cutoff_bounds {x B : ℝ} (hx : 3 ≤ x) (hB : 0 ≤ B) :
    0 ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ B ∧ x ^ (1 / 2 : ℝ) / Real.log x ^ B ≤ x := by
  have hlog := one_lt_log_of_three_le hx
  have hx0 : 0 < x := by linarith
  refine ⟨by positivity, (div_le_self (by positivity) (Real.one_le_rpow (by linarith) hB)).trans ?_⟩
  exact (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)).trans_eq (Real.rpow_one x)

/-! ## Monotonicity of the four clauses in their constants -/

/-- The coefficient bound is monotone in its three constants, at `n ≥ 1` where `τ(n) ≥ 1` and
`1 + log n ≥ 1`. -/
private theorem isCoefficientSequence_mono {C C' : ℝ} {k k' l l' : ℕ} {α : ℕ → ℂ} (hC : 0 ≤ C)
    (hCC : C ≤ C') (hk : k ≤ k') (hl : l ≤ l') (h : IsCoefficientSequence C k l α) :
    IsCoefficientSequence C' k' l' α := by
  intro n hn
  refine (h n hn).trans ?_
  have hτ : (1 : ℝ) ≤ (n.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨n, Nat.mem_divisors_self n (by omega)⟩
  have hL : (1 : ℝ) ≤ 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
  have := hC.trans hCC
  gcongr

/-- The location clause is monotone in its two endpoints: widening the support window preserves it.
The sign of the scale that the move needs comes from the hypothesis itself, which is vacuous at a
non-positive scale. -/
private theorem locatedAtScale_mono {c₀ c₁ c₀' c₁' : ℝ} {α : ℕ → ℂ} {N : ℝ} (hc₁ : 0 < c₁)
    (h₀ : c₀' ≤ c₀) (h₁ : c₁ ≤ c₁') (h : LocatedAtScale c₀ c₁ α N) :
    LocatedAtScale c₀' c₁' α N := by
  intro n hn hne
  have hN : (0 : ℝ) ≤ N := (pos_of_locatedAtScale hc₁ h hn hne).le
  obtain ⟨hlo, hhi⟩ := h n hn hne
  exact ⟨(mul_le_mul_of_nonneg_right h₀ hN).trans hlo,
    hhi.trans (mul_le_mul_of_nonneg_right h₁ hN)⟩

/-- Smoothness is monotone in the two support endpoints, the derivative data being untouched. -/
private theorem isSmoothAtScale_mono {c C c' C' : ℝ} {b : ℕ → ℝ} {w : ℕ → ℕ} {α : ℕ → ℂ} {N : ℝ}
    (h₀ : c' ≤ c) (h₁ : C ≤ C') (h : IsSmoothAtScale c C b w α N) :
    IsSmoothAtScale c' C' b w α N := by
  obtain ⟨ψ, hψ, hsupp, hderiv, heq⟩ := h
  exact ⟨ψ, hψ, fun t ht ↦ ⟨h₀.trans (hsupp t ht).1, (hsupp t ht).2.trans h₁⟩, hderiv, heq⟩

/-- **A sequence smooth at a positive scale is located there.** By `Gap212.IsSmoothAtScale` the
profile vanishes off `[c₋, c₊]`, so a nonzero term has `n / N ∈ [c₋, c₊]`. This is what supplies the
location `Type III` declares only smoothness of. -/
private theorem locatedAtScale_of_isSmoothAtScale (K : ConstantBundle) {α : ℕ → ℂ} {N : ℝ}
    (hN : 0 < N) (h : K.IsSmoothAtScale α N) : K.LocatedAtScale α N := by
  obtain ⟨ψ, -, hsupp, -, hval⟩ := h
  intro n _ hne
  obtain ⟨h1, h2⟩ := hsupp ((n : ℝ) / N) (by rwa [← hval n])
  exact ⟨(le_div_iff₀ hN).mp h1, (div_le_iff₀ hN).mp h2⟩

/-- **The convolution bundle `Ψ` only widens, at a normalized bundle.** `Ψ K` squares the
coefficient constant and the two support endpoints and enlarges the two exponents, so at a bundle
with `c₋ ≤ 1 ≤ c₊` and `1 ≤ C` every clause a datum satisfies at `K` it satisfies at `Ψ K`, and
`Ψ K` is normalized again — which is what lets `Ψ` be iterated. The commensurability constants are
untouched, so that clause transfers with no condition at all.

This is what makes one bundle, `Ψ(Ψ(Ψ(K♭)))`, serve the members of all three classes at once: the
threshold argument needs a single coefficient bound and a single support window for the member,
whatever shape its witnesses have. -/
private theorem conv_transfer {K : ConstantBundle} (hlo : K.scaleLo ≤ 1) (hhi : 1 ≤ K.scaleHi)
    (hC : 1 ≤ K.coeffConst) :
    K.conv.scaleLo ≤ 1 ∧ 1 ≤ K.conv.scaleHi ∧ 1 ≤ K.conv.coeffConst ∧
      (∀ α : ℕ → ℂ, K.IsCoefficientSequence α → K.conv.IsCoefficientSequence α) ∧
      (∀ (α : ℕ → ℂ) (N : ℝ), K.LocatedAtScale α N → K.conv.LocatedAtScale α N) ∧
      (∀ (α : ℕ → ℂ) (N : ℝ), K.IsSmoothAtScale α N → K.conv.IsSmoothAtScale α N) ∧
      (∀ z y : ℝ, K.asympEq z y → K.conv.asympEq z y) := by
  have elo : K.conv.scaleLo = K.scaleLo ^ 2 := rfl
  have ehi : K.conv.scaleHi = K.scaleHi ^ 2 := rfl
  have eC : K.conv.coeffConst = K.coeffConst ^ 2 := rfl
  have ek : K.conv.coeffFstPow = 2 * K.coeffFstPow + 1 := rfl
  have el : K.conv.coeffSndPow = 2 * K.coeffSndPow := rfl
  have hlo0 := K.scaleLo_pos
  refine ⟨by rw [elo]; nlinarith, by rw [ehi]; nlinarith, by rw [eC]; nlinarith,
    fun α h ↦ ?_, fun α N h ↦ ?_, fun α N h ↦ ?_, fun z y h ↦ ?_⟩
  · refine isCoefficientSequence_mono (by linarith) ?_ ?_ ?_ h
    · rw [eC]; nlinarith
    · rw [ek]; omega
    · rw [el]; omega
  · refine locatedAtScale_mono (lt_of_lt_of_le hlo0 K.scaleLo_lt_scaleHi.le) ?_ ?_ h
    · rw [elo]; nlinarith
    · rw [ehi]; nlinarith
  · refine isSmoothAtScale_mono ?_ ?_ h
    · rw [elo]; nlinarith
    · rw [ehi]; nlinarith
  · exact h

/-- **The Siegel–Walfisz update `Σ K`.** There is a bundle differing from `K` only in the two
Siegel–Walfisz components, at which every sequence `K`-smooth at a scale `N ≥ 1` has the
Siegel–Walfisz property. Since the five clauses read pairwise disjoint groups of components, each
other transfer is `rfl`. The uniformity is the content: a bundle chosen after the sequence would be
no statement at all. -/
private theorem exists_sigma_bundle (K : ConstantBundle) :
    ∃ K' : ConstantBundle,
      (∀ α : ℕ → ℂ, K.IsCoefficientSequence α → K'.IsCoefficientSequence α) ∧
      (∀ (α : ℕ → ℂ) (N : ℝ), K.LocatedAtScale α N → K'.LocatedAtScale α N) ∧
      (∀ z y : ℝ, K.asympEq z y → K'.asympEq z y) ∧
      (∀ (α : ℕ → ℂ) (N : ℝ), 1 ≤ N → K.IsSmoothAtScale α N → K'.HasSiegelWalfisz α N) := by
  obtain ⟨S, E, hSE⟩ := exists_hasSiegelWalfisz_of_isSmoothAtScale K.scaleLo K.scaleHi
    K.scaleLo_pos K.smoothConst K.smoothPow
  exact ⟨{ K with siegelWalfiszConst := S, siegelWalfiszPow := E },
    fun _ h ↦ h, fun _ _ h ↦ h, fun _ _ h ↦ h, fun α N hN h ↦ hSE α N hN h⟩

/-! ## Two weakenings of the bilinear conclusion -/

/-- **The discrepancy depends on the residue class only modulo the modulus**, since the class
`{n : n ≡ a (d)}` does. This is one of the two steps that take the bilinear input's maximum over
primitive classes down to the single class the routing fixes. -/
private theorem sumError_mod_right (f : ℕ → ℂ) (d a : ℕ) :
    sumError f d (a % d) = sumError f d a := by
  simp only [sumError, Nat.ModEq, Nat.mod_mod]

/-- **A class coprime to every prime below `x` is coprime to every positive modulus below `x`**: a
prime factor of the gcd divides the modulus, hence is at most `x`. -/
private theorem coprime_of_coprimeBelow {a q : ℕ} {x : ℝ} (h : CoprimeBelow a x) (hq : 1 ≤ q)
    (hqx : (q : ℝ) ≤ x) : Nat.Coprime a q := by
  refine Nat.coprime_of_dvd fun p hp hpa hpq ↦ hp.ne_one (Nat.dvd_one.mp ?_)
  have hcop : Nat.gcd a p = 1 := h p hp ((Nat.cast_le.mpr (Nat.le_of_dvd hq hpq)).trans hqx)
  exact hcop ▸ Nat.dvd_gcd hpa dvd_rfl

/-- **From the bilinear conclusion to one residue class and the squarefree moduli.** The maximum is
inside the sum, so the term at `a mod q` is one of the terms it ranges over, and dropping the
non-squarefree moduli only decreases a sum of norms. Both comparisons would fail with the maximum
outside the sum, which is why the cited input keeps it inside. -/
private theorem sum_norm_sumError_le_of_sup_le {f : ℕ → ℂ} {a : ℕ} {Y c : ℝ} {D : Finset ℕ}
    (hD : D ⊆ Finset.Icc 1 ⌊Y⌋₊) (hcop : ∀ q ∈ Finset.Icc 1 ⌊Y⌋₊, Nat.Coprime a q)
    (hsup : ∑ q ∈ Finset.Icc 1 ⌊Y⌋₊,
        (({b ∈ Finset.range q | Nat.Coprime b q}.sup fun b ↦ ‖sumError f q b‖₊ : NNReal) : ℝ)
      ≤ c) :
    ∑ d ∈ D with Squarefree d, ‖sumError f d a‖ ≤ c := by
  refine ((Finset.sum_le_sum_of_subset_of_nonneg ((Finset.filter_subset _ _).trans hD)
    fun _ _ _ ↦ norm_nonneg _).trans (Finset.sum_le_sum fun q hq ↦ ?_)).trans hsup
  have hmem : a % q ∈ {b ∈ Finset.range q | Nat.Coprime b q} := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (Finset.mem_Icc.mp hq).1), ?_⟩
    change Nat.gcd (a % q) q = 1
    rw [← Nat.gcd_rec]
    exact (hcop q hq).symm
  rw [← sumError_mod_right f q a, ← coe_nnnorm]
  exact NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun b ↦ ‖sumError f q b‖₊) hmem)

/-- **Equidistribution is monotone in the modulus family and in the constant**, every term of the
sum being a norm. -/
private theorem hasEquidistribution_of_subset {x : ℝ} {D' D : Finset ℕ} {f : ℕ → ℂ} {a : ℕ}
    {A C C' : ℝ} (hx : 0 ≤ x) (hlog : 0 < Real.log x) (hD : D' ⊆ D) (hCC : C ≤ C')
    (h : HasEquidistribution x D f a A C) : HasEquidistribution x D' f a A C' := by
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hD)
    fun _ _ _ ↦ norm_nonneg _).trans (h.trans ?_)
  gcongr

/-! ## The class at the normalized bundle, and the scale of a member -/

/-- **The Harman class transfers to the normalized bundle.** Each clause of each of the three types
transfers by `Gap212.constantBundle_flat_transfer`, and the exponent inequalities mention no
bundle. So the whole proof below may be run at `K♭`, where `a₋ ≤ 1 ≤ a₊`, `c₋ ≤ 1 ≤ c₊` and
`1 ≤ C`. -/
private theorem harmanClass_flat {K : ConstantBundle} {x ξ₁ ξ₂ ξ₃ : ℝ} {f : ℕ → ℂ}
    (h : HarmanClass K x ξ₁ ξ₂ ξ₃ f) : HarmanClass K.flat x ξ₁ ξ₂ ξ₃ f := by
  obtain ⟨-, -, -, -, -, htC, htL, htS, htSW, htA⟩ := constantBundle_flat_transfer K
  rcases h with h | h | h
  · obtain ⟨α, β, M, hM, N, hN, hfe, hα, hβ, hαM, hβN, hasymp, hsm, hNlo⟩ := h
    exact Or.inl ⟨α, β, M, hM, N, hN, hfe, htC _ hα, htC _ hβ, htL _ _ hαM, htL _ _ hβN,
      htA _ _ hasymp, htS _ _ hsm, hNlo⟩
  · obtain ⟨α, β, M, hM, N, hN, hfe, hα, hβ, hαM, hβN, hasymp, hSα, hSβ, hNlo, hNhi⟩ := h
    exact Or.inr (Or.inl ⟨α, β, M, hM, N, hN, hfe, htC _ hα, htC _ hβ, htL _ _ hαM, htL _ _ hβN,
      htA _ _ hasymp, htSW _ _ hSα, htSW _ _ hSβ, hNlo, hNhi⟩)
  · obtain ⟨α, ψ₁, ψ₂, ψ₃, M, hM, N₁, hN₁, N₂, hN₂, N₃, hN₃, hfe, hα, hp₁, hp₂, hp₃, hαM,
      hs₁, hs₂, hs₃, hasymp, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ := h
    exact Or.inr (Or.inr ⟨α, ψ₁, ψ₂, ψ₃, M, hM, N₁, hN₁, N₂, hN₂, N₃, hN₃, hfe, htC _ hα,
      htC _ hp₁, htC _ hp₂, htC _ hp₃, htL _ _ hαM, htS _ _ hs₁, htS _ _ hs₂, htS _ _ hs₃,
      htA _ _ hasymp, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩)

/-- **A member of the class is a coefficient sequence located at a scale below `a₊ x`**, at the
thrice-convolved bundle `Ψ(Ψ(Ψ(K)))`, which covers all three types at once: a two-factor witness
lands at `Ψ K` and is carried up, a fourfold one at `Ψ(Ψ(Ψ K))` directly. The scale is the product
of the declared scales, at least `1` because each factor's is, and at most `a₊ x` by
commensurability. `f 0 = 0` because a Dirichlet convolution sums over the positive divisors.

These are exactly the hypotheses `Gap212.hasEquidistribution_of_forall_ge` asks in order to absorb
a bounded range of `x` into the constant. -/
private theorem exists_scale_of_harmanClass {K : ConstantBundle} {x ξ₁ ξ₂ ξ₃ : ℝ} {f : ℕ → ℂ}
    (hlo : K.scaleLo ≤ 1) (hhi : 1 ≤ K.scaleHi) (hC : 1 ≤ K.coeffConst)
    (h : HarmanClass K x ξ₁ ξ₂ ξ₃ f) :
    ∃ Nf : ℝ, 1 ≤ Nf ∧ Nf ≤ K.asympHi * x ∧
      K.conv.conv.conv.IsCoefficientSequence f ∧
      K.conv.conv.conv.LocatedAtScale f Nf ∧ f 0 = 0 := by
  obtain ⟨hlo1, hhi1, hC1, -, -, -, -⟩ := conv_transfer hlo hhi hC
  obtain ⟨hlo2, hhi2, hC2, c2C, c2L, c2S, -⟩ := conv_transfer hlo1 hhi1 hC1
  obtain ⟨-, -, -, c3C, c3L, -, -⟩ := conv_transfer hlo2 hhi2 hC2
  obtain ⟨-, -, -, c1C, c1L, c1S, -⟩ := conv_transfer hlo hhi hC
  -- the two-factor cases, which land at `Ψ K` and are carried up two steps
  have two : ∀ α β : ℕ → ℂ, ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      K.IsCoefficientSequence α → K.IsCoefficientSequence β →
      K.LocatedAtScale α M → K.LocatedAtScale β N → K.asympEq (M * N) x →
      ∃ Nf : ℝ, 1 ≤ Nf ∧ Nf ≤ K.asympHi * x ∧
        K.conv.conv.conv.IsCoefficientSequence (dconv α β) ∧
        K.conv.conv.conv.LocatedAtScale (dconv α β) Nf ∧ dconv α β 0 = 0 := by
    intro α β M N hM hN hα hβ hαM hβN hasymp
    obtain ⟨hd, hl⟩ := isCoefficientSequence_and_locatedAtScale_dconv hα hβ hαM hβN
    exact ⟨M * N, one_le_mul_of_one_le_of_one_le hM hN, hasymp.2, c3C _ (c2C _ hd),
      c3L _ _ (c2L _ _ hl), by simp [dconv]⟩
  rcases h with ⟨α, β, M, hM, N, hN, rfl, hα, hβ, hαM, hβN, hasymp, -⟩ |
    ⟨α, β, M, hM, N, hN, rfl, hα, hβ, hαM, hβN, hasymp, -⟩ |
    ⟨α, ψ₁, ψ₂, ψ₃, M, hM, N₁, hN₁, N₂, hN₂, N₃, hN₃, rfl, hα, hp₁, hp₂, hp₃, hαM,
      hs₁, hs₂, hs₃, hasymp, -⟩
  · exact two α β M N hM hN hα hβ hαM hβN hasymp
  · exact two α β M N hM hN hα hβ hαM hβN hasymp
  · have hl₁ := locatedAtScale_of_isSmoothAtScale K (by linarith) hs₁
    have hl₂ := locatedAtScale_of_isSmoothAtScale K (by linarith) hs₂
    have hl₃ := locatedAtScale_of_isSmoothAtScale K (by linarith) hs₃
    obtain ⟨d₁, l₁⟩ := isCoefficientSequence_and_locatedAtScale_dconv hα hp₁ hαM hl₁
    obtain ⟨d₂, l₂⟩ :=
      isCoefficientSequence_and_locatedAtScale_dconv d₁ (c1C _ hp₂) l₁ (c1L _ _ hl₂)
    obtain ⟨d₃, l₃⟩ := isCoefficientSequence_and_locatedAtScale_dconv d₂ (c2C _ (c1C _ hp₃)) l₂
      (c2L _ _ (c1L _ _ hl₃))
    exact ⟨M * N₁ * N₂ * N₃, one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hM hN₁) hN₂) hN₃, hasymp.2, d₃, l₃, by simp [dconv]⟩

/-! ## The choice of the exponent -/

/-- **The exponent the proof chooses.** `ξ = ½ min{ξ₁ - ϵ, ξ₂ - ϵ, 1 - 2ξ₃ - ϵ, ½}` is positive,
strictly below each of the three class exponents, and at most `¼`. The last of these is what leaves
room for the level `ω_† = 1/100` and the loss `ε_† ≤ 1/100` of the Type I split, since then
`½ - 2ω_† - ε_† ≥ 47/100 > ¼ ≥ ξ`.

Only these five facts are used below, so the value is packaged as an existential: what must *not*
happen is for a consumer to supply its own `ξ`, which is exactly what would make the lemma
false. -/
private theorem exists_choice_of_xi {ξ₁ ξ₂ ξ₃ : ℝ} (h₁ : 0 < ξ₁ - slack) (h₂ : 0 < ξ₂ - slack)
    (h₃ : 0 < 1 - 2 * ξ₃ - slack) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ < ξ₁ - slack ∧ ξ < ξ₂ - slack ∧ ξ < 1 - 2 * ξ₃ - slack ∧ ξ ≤ 1 / 4 := by
  obtain ⟨m, hm1, hm2, hm3, hm4, hmpos⟩ :
      ∃ m : ℝ, m ≤ ξ₁ - slack ∧ m ≤ ξ₂ - slack ∧ m ≤ 1 - 2 * ξ₃ - slack ∧ m ≤ 1 / 2 ∧ 0 < m :=
    ⟨min (min (ξ₁ - slack) (ξ₂ - slack)) (min (1 - 2 * ξ₃ - slack) (1 / 2)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _),
      lt_min (lt_min h₁ h₂) (lt_min h₃ (by norm_num))⟩
  exact ⟨m / 2, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-! ## The Bombieri–Vinogradov range -/

/-- The content of the lemma at a **normalized** bundle, one with `c₋ ≤ 1 ≤ c₊`, `1 ≤ C` and
`1 ≤ a₊`, which is what `Gap212.constantBundle_flat_transfer` produces. Every step of the argument
uses one of those four: `1 ≤ C` and `c₋ ≤ 1 ≤ c₊` to iterate the convolution bundle `Ψ`, and
`1 ≤ a₊` to place a member's declared scale inside the Type I exponent window. -/
private theorem exists_subhalf_bound_of_normalized (hbv : BilinearBombieriVinogradov)
    (hti : TypeIBakerIrving) {ξ₁ ξ₂ ξ₃ : ℝ} (hx₁ : 0 < ξ₁ - slack) (hx₂ : 0 < ξ₂ - slack)
    (hx₃ : 0 < 1 - 2 * ξ₃ - slack) (K : ConstantBundle) (hlo : K.scaleLo ≤ 1)
    (hhi : 1 ≤ K.scaleHi) (hCc : 1 ≤ K.coeffConst) (hahi : 1 ≤ K.asympHi) {A : ℝ} (hA : 0 < A) :
    ∃ B > (0 : ℝ), ∃ C : ℝ, ∀ x ≥ (3 : ℝ), ∀ f : ℕ → ℂ, ∀ a : ℕ,
      HarmanClass K x ξ₁ ξ₂ ξ₃ f → CoprimeBelow a x →
        HasEquidistribution x (Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / Real.log x ^ B⌋₊) f a A C := by
  obtain ⟨ξ, hξpos, hξ1, hξ2, hξ3, hξq⟩ := exists_choice_of_xi hx₁ hx₂ hx₃
  obtain ⟨hlo1, hhi1, hCc1, c1C, c1L, c1S, c1A⟩ := conv_transfer hlo hhi hCc
  obtain ⟨hlo2, hhi2, hCc2, c2C, c2L, c2S, c2A⟩ := conv_transfer hlo1 hhi1 hCc1
  obtain ⟨Kσ, sC, sL, sA, sW⟩ := exists_sigma_bundle K
  obtain ⟨Kτ, tC, tL, tA, tW⟩ := exists_sigma_bundle K.conv.conv
  -- the Baker--Irving estimate, the loss it returns, and the level the Type I split cuts at
  obtain ⟨ε₀, hε₀, hti1⟩ := hti K (1 / 100) ⟨by norm_num, by norm_num⟩ 1 (by norm_num)
    (ξ₁ - slack) (max (ξ₁ - slack) (1 + Real.log K.asympHi / Real.log 3)) hx₁ (le_max_left _ _)
  obtain ⟨εd, hεd0, hεdlt, hεdle⟩ : ∃ e : ℝ, 0 < e ∧ e < ε₀ ∧ e ≤ 1 / 100 :=
    ⟨min (ε₀ / 2) (1 / 100), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_left _ _) (by linarith), min_le_right _ _⟩
  obtain ⟨Cd, htiC⟩ := hti1 εd ⟨hεd0, hεdlt⟩ A hA
  have hgap : ξ < 1 / 2 - 2 * (1 / 100) - εd := by linarith
  -- the three invocations of the bilinear input, at three different bundles
  obtain ⟨B₁, hB₁, C₁, hbv₁⟩ := hbv K ξ hξpos A hA
  obtain ⟨B₂, hB₂, C₂, hbv₂⟩ := hbv Kτ ξ hξpos A hA
  obtain ⟨B₃, hB₃, C₃, hbv₃⟩ := hbv Kσ ξ hξpos A hA
  -- the two thresholds in `x`, for Type II and for the low Type I branch
  obtain ⟨X₂, hX₂3, hX₂⟩ := exists_threshold K.asympLo_pos hξ2
  obtain ⟨X₁, hX₁3, hX₁⟩ := exists_threshold K.asympLo_pos hgap
  obtain ⟨x₀, hx₀3, hx₀1, hx₀2⟩ : ∃ X : ℝ, 3 ≤ X ∧ X₁ ≤ X ∧ X₂ ≤ X :=
    ⟨max X₁ X₂, le_trans hX₁3 (le_max_left _ _), le_max_left _ _, le_max_right _ _⟩
  -- the common cutoff and the common constant
  obtain ⟨B, hBpos, hBB₁, hBB₂, hBB₃⟩ : ∃ B : ℝ, 0 < B ∧ B₁ ≤ B ∧ B₂ ≤ B ∧ B₃ ≤ B :=
    ⟨max B₁ (max B₂ B₃), lt_of_lt_of_le hB₁ (le_max_left _ _), le_max_left _ _,
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  obtain ⟨Ct, hCt0, hCt1, hCt2, hCt3, hCtd⟩ :
      ∃ C : ℝ, 0 ≤ C ∧ C₁ ≤ C ∧ C₂ ≤ C ∧ C₃ ≤ C ∧ Cd ≤ C := by
    refine ⟨max C₁ 0 + max C₂ 0 + max C₃ 0 + max Cd 0, ?_, ?_, ?_, ?_, ?_⟩ <;>
      linarith [le_max_left C₁ (0 : ℝ), le_max_right C₁ (0 : ℝ), le_max_left C₂ (0 : ℝ),
        le_max_right C₂ (0 : ℝ), le_max_left C₃ (0 : ℝ), le_max_right C₃ (0 : ℝ),
        le_max_left Cd (0 : ℝ), le_max_right Cd (0 : ℝ)]
  -- the four cases, beyond the threshold
  have key : ∀ x ≥ x₀, ∀ D ⊆ moduliRange x (1 / 100), ∀ f : ℕ → ℂ, ∀ a : ℕ,
      (HarmanClass K x ξ₁ ξ₂ ξ₃ f ∧ CoprimeBelow a x ∧
          D ⊆ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / Real.log x ^ B⌋₊) →
      ∀ Nf : ℝ, 1 ≤ Nf → Nf ≤ K.asympHi * x →
        IsCoefficientSequence K.conv.conv.conv.coeffConst K.conv.conv.conv.coeffFstPow
            K.conv.conv.conv.coeffSndPow f →
          LocatedAtScale K.conv.conv.conv.scaleLo K.conv.conv.conv.scaleHi f Nf → f 0 = 0 →
            HasEquidistribution x D f a A Ct := by
    intro x hx D hDrange f a ⟨hclass, ha, hD⟩ Nf _ _ _ _ _
    have hx3 : (3 : ℝ) ≤ x := hx₀3.trans hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hlogx : 1 < Real.log x := one_lt_log_of_three_le hx3
    have hlogpos : (0 : ℝ) < Real.log x := by linarith
    -- the fixed class is coprime to every modulus of the range, which is below `x`
    have hcopB : ∀ B' : ℝ, 0 ≤ B' →
        ∀ q ∈ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / Real.log x ^ B'⌋₊, Nat.Coprime a q := by
      intro B' hB' q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_Icc.mp hq
      obtain ⟨hY0, hYx⟩ := subhalf_cutoff_bounds hx3 hB'
      exact coprime_of_coprimeBelow ha hq1
        (((Nat.cast_le.mpr hq2).trans (Nat.floor_le hY0)).trans hYx)
    -- enlarging the cutoff shrinks the range, since `log x > 1`
    have hsubB : ∀ B' : ℝ, 0 ≤ B' → B' ≤ B →
        D ⊆ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / Real.log x ^ B'⌋₊ := by
      intro B' hB' hBB
      exact hD.trans (Finset.Icc_subset_Icc_right (Nat.floor_mono (div_le_div_of_nonneg_left
        (by positivity) (by positivity) (Real.rpow_le_rpow_of_exponent_le hlogx.le hBB))))
    -- the two weakenings the bilinear conclusion needs, packaged once
    have fin : ∀ B' C' : ℝ, 0 ≤ B' → B' ≤ B → C' ≤ Ct →
        ∑ q ∈ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / Real.log x ^ B'⌋₊,
            (({b ∈ Finset.range q | Nat.Coprime b q}.sup
              fun b ↦ ‖sumError f q b‖₊ : NNReal) : ℝ) ≤ C' * x / Real.log x ^ A →
        HasEquidistribution x D f a A Ct := by
      intro B' C' hB' hBB hCC hbound
      refine (sum_norm_sumError_le_of_sup_le (hsubB B' hB' hBB) (hcopB B' hB') hbound).trans ?_
      gcongr
    rcases hclass with hI | hII | hIII
    · -- **Type I.** No upper bound on `N`, so the level `ω_† = 1/100` splits the class.
      obtain ⟨α, β, M, hM, N, hN, rfl, hα, hβ, hαM, hβN, hasymp, hsm, hNlo⟩ := hI
      -- the exponent window contains `N`, with no threshold in `x`
      have hNwin : N ≤ x ^ max (ξ₁ - slack) (1 + Real.log K.asympHi / Real.log 3) := by
        refine (le_mul_of_one_le_left (zero_le_one.trans hN) hM).trans (hasymp.2.trans
          (le_trans ?_ (Real.rpow_le_rpow_of_exponent_le hx1 (le_max_right _ _))))
        rw [Real.rpow_add hxpos, Real.rpow_one, mul_comm x]
        exact mul_le_mul_of_nonneg_right (le_rpow_log_div_log_three hahi hx3) hxpos.le
      rcases le_or_gt N (x ^ (1 / 2 + 2 * (1 / 100) + εd)) with hlow | hhigh
      · -- the low branch: both scales are large, and `β`'s smoothness supplies Siegel--Walfisz
        have hxN : x ^ ξ ≤ N := le_trans (Real.rpow_le_rpow_of_exponent_le hx1 hξ1.le) hNlo
        have hMlo : K.asympLo * x ^ (1 / 2 - 2 * (1 / 100) - εd) ≤ M := by
          have h := le_of_asympEq_of_le_rpow K.asympLo_pos.le hxpos
            (lt_of_lt_of_le zero_lt_one hN) hlow hasymp.1
          rwa [show (1 : ℝ) - (1 / 2 + 2 * (1 / 100) + εd) = 1 / 2 - 2 * (1 / 100) - εd by ring]
            at h
        have hxM : x ^ ξ ≤ M := le_trans (hX₁ x (le_trans hx₀1 hx)) hMlo
        exact fin B₃ C₃ hB₃.le hBB₃ hCt3
          (hbv₃ x hx3 α β M hM N hN (sC _ hα) (sC _ hβ) (sL _ _ hαM) (sL _ _ hβN)
            (sA _ _ hasymp) hxM hxN (Or.inr (sW _ _ hN hsm)))
      · -- the high branch: the third branch of `moduliI`, where both inequalities are vacuous
        have hsqrt : Real.sqrt x < N := lt_of_le_of_lt (by
          rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)) hhigh
        have hres := htiC 1 (by norm_num) x hx3 α β M hM N hN a hα hβ hαM hβN hasymp hsm
          hNlo hNwin (fun h ↦ absurd h (not_le.mpr hsqrt))
          (fun _ h ↦ absurd h (not_le.mpr hhigh)) ha
        rw [moduliI, if_neg (not_le.mpr hsqrt), if_neg (not_le.mpr hhigh)] at hres
        exact hasEquidistribution_of_subset hxpos.le hlogpos hDrange hCtd hres
    · -- **Type II.** The two-sided window is what bounds the first scale below.
      obtain ⟨α, β, M, hM, N, hN, rfl, hα, hβ, hαM, hβN, hasymp, hSα, hSβ, hNlo, hNhi⟩ := hII
      have hxN : x ^ ξ ≤ N := le_trans (Real.rpow_le_rpow_of_exponent_le hx1 hξ2.le) hNlo
      have hMlo : K.asympLo * x ^ (ξ₂ - slack) ≤ M := by
        have h := le_of_asympEq_of_le_rpow K.asympLo_pos.le hxpos
          (lt_of_lt_of_le zero_lt_one hN) hNhi hasymp.1
        rwa [show (1 : ℝ) - (1 - ξ₂ + slack) = ξ₂ - slack by ring] at h
      have hxM : x ^ ξ ≤ M := le_trans (hX₂ x (le_trans hx₀2 hx)) hMlo
      exact fin B₁ C₁ hB₁.le hBB₁ hCt1
        (hbv₁ x hx3 α β M hM N hN hα hβ hαM hβN hasymp hxM hxN (Or.inr hSβ))
    · -- **Type III.** Already left-associated, so no regrouping; and no threshold is needed.
      obtain ⟨α, ψ₁, ψ₂, ψ₃, M, hM, N₁, hN₁, N₂, hN₂, N₃, hN₃, rfl, hα, hp₁, hp₂, hp₃, hαM,
        hs₁, hs₂, hs₃, hasymp, hN₁lo, -, -, -, hN₃lo, -⟩ := hIII
      have hl₂ := locatedAtScale_of_isSmoothAtScale K (lt_of_lt_of_le zero_lt_one hN₂) hs₂
      have hl₃ := locatedAtScale_of_isSmoothAtScale K (lt_of_lt_of_le zero_lt_one hN₃) hs₃
      obtain ⟨d₁, l₁⟩ := isCoefficientSequence_and_locatedAtScale_dconv hα hp₁ hαM
        (locatedAtScale_of_isSmoothAtScale K (lt_of_lt_of_le zero_lt_one hN₁) hs₁)
      obtain ⟨d₂, l₂⟩ :=
        isCoefficientSequence_and_locatedAtScale_dconv d₁ (c1C _ hp₂) l₁ (c1L _ _ hl₂)
      have a1 : N₁ ≤ M * N₁ := le_mul_of_one_le_left (zero_le_one.trans hN₁) hM
      have a2 : M * N₁ ≤ M * N₁ * N₂ :=
        le_mul_of_one_le_right (le_trans (zero_le_one.trans hN₁) a1) hN₂
      have hprod : (1 : ℝ) ≤ M * N₁ * N₂ := hN₁.trans (a1.trans a2)
      have hxN₃ : x ^ ξ ≤ N₃ := le_trans (Real.rpow_le_rpow_of_exponent_le hx1 hξ3.le) hN₃lo
      have hxG : x ^ ξ ≤ M * N₁ * N₂ :=
        le_trans (le_trans (Real.rpow_le_rpow_of_exponent_le hx1 hξ3.le) hN₁lo) (a1.trans a2)
      exact fin B₂ C₂ hB₂.le hBB₂ hCt2
        (hbv₂ x hx3 (dconv (dconv α ψ₁) ψ₂) ψ₃ (M * N₁ * N₂) hprod N₃ hN₃ (tC _ d₂)
          (tC _ (c2C _ (c1C _ hp₃))) (tL _ _ l₂) (tL _ _ (c2L _ _ (c1L _ _ hl₃)))
          (tA _ _ (c2A _ _ (c1A _ _ hasymp))) hxG hxN₃
          (Or.inr (tW _ _ hN₃ (c2S _ _ (c1S _ _ hs₃)))))
  -- the sub-half range sits inside the ambient range of the moduli
  have hsub : ∀ x ≥ (3 : ℝ),
      Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / Real.log x ^ B⌋₊ ⊆ moduliRange x (1 / 100) := by
    intro x hx
    have hlogx := one_lt_log_of_three_le hx
    have hxpos : (0 : ℝ) < x := by linarith
    exact Finset.Icc_subset_Icc_right (Nat.floor_mono ((div_le_self (by positivity)
      (Real.one_le_rpow hlogx.le hBpos.le)).trans
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))))
  -- the bounded range `3 ≤ x ≤ x₀` is absorbed into the constant
  have hCfin := hasEquidistribution_of_forall_ge
    (P := fun (x : ℝ) (D : Finset ℕ) (f : ℕ → ℂ) (a : ℕ) ↦
      HarmanClass K x ξ₁ ξ₂ ξ₃ f ∧ CoprimeBelow a x ∧
        D ⊆ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / Real.log x ^ B⌋₊)
    (by norm_num) hA.le hx₀3 hCt0 key
  exact ⟨B, hBpos, _, fun x hx f a hf ha ↦ (exists_scale_of_harmanClass hlo hhi hCc hf).elim
    fun Nf ⟨hNf1, hNfb, hcoef, hloc, hf0⟩ ↦
      hCfin x hx _ (hsub x hx) f a ⟨hf, ha, subset_rfl⟩ Nf hNf1 hNfb hcoef hloc hf0⟩

/-- **The Bombieri–Vinogradov range.** If `ξ₁ - ϵ > 0`, `ξ₂ - ϵ > 0` and `1 - 2ξ₃ - ϵ > 0`, then
for every bundle `K` and every `A > 0` there are a `B > 0` and a `C` such that for every `x ≥ 3`,
every `f ∈ ℋ_K(x; ξ₁, ξ₂, ξ₃)` and every `a` coprime below `x`, the squarefree moduli of
`𝒬_BV(x; B) = {q : 1 ≤ q ≤ x^{1/2}(log x)^{-B}}` carry `∑ |Δ(f; q, a)| ≤ C x (log x)^{-A}`.

The modulus family is `Finset.Icc 1 ⌊x^{1/2}(log x)^{-B}⌋₊`, which is `Gap212.Inputs.subhalfModuli`
restricted to the positive integers: `𝒬_BV(x; B)` on the nose, and the same range
`Gap212.BilinearBombieriVinogradov` sums over; the squarefree restriction and the shape of the sum
come from `Gap212.HasEquidistribution`.

**No exponent `ξ` occurs in the statement.** The proof needs one and chooses it,
`ξ = ½ min{ξ₁ - ϵ, ξ₂ - ϵ, 1 - 2ξ₃ - ϵ, ½}`; quantifying it here and asking the caller for
`ξ < 1/2` would leave the statement false, since `ξ₃` small with `ξ₁, ξ₂` near `1` admits
`ξ > 1/2`. The module docstring gives the four cases and where each threshold in `x` comes from. -/
@[gap212 "lem_qbv_bound"]
theorem exists_hasEquidistribution_subhalf_of_harmanClass (hbv : BilinearBombieriVinogradov)
    (hti : TypeIBakerIrving) {ξ₁ ξ₂ ξ₃ : ℝ} (hx₁ : 0 < ξ₁ - slack) (hx₂ : 0 < ξ₂ - slack)
    (hx₃ : 0 < 1 - 2 * ξ₃ - slack) (K : ConstantBundle) {A : ℝ} (hA : 0 < A) :
    ∃ B > (0 : ℝ), ∃ C : ℝ, ∀ x ≥ (3 : ℝ), ∀ f : ℕ → ℂ, ∀ a : ℕ,
      HarmanClass K x ξ₁ ξ₂ ξ₃ f → CoprimeBelow a x →
        HasEquidistribution x (Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / Real.log x ^ B⌋₊) f a A C := by
  obtain ⟨hlo, hhi, -, hahi, hCc, -, -, -, -, -⟩ := constantBundle_flat_transfer K
  obtain ⟨B, hB, C, hmain⟩ :=
    exists_subhalf_bound_of_normalized hbv hti hx₁ hx₂ hx₃ K.flat hlo hhi hCc hahi hA
  exact ⟨B, hB, C, fun x hx f a hf ha ↦ hmain x hx f a (harmanClass_flat hf) ha⟩

end Gap212
