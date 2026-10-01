/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.SelbergMainTerm

/-!
# The uniform-in-modulus input: what shape it cannot have, and the form the Gram sum needs

The statements `Gap212.Sieve.LcmGramSumLimitOfSupport`,
`Gap212.Sieve.TotientGramSumLimitOfSupport`, `Gap212.Sieve.SelbergSievingError` and
`Gap212.Sieve.TotientSievingError` all rest on Möbius cancellation uniform in a growing modulus.
This file shows one shape that estimate **cannot** have, and gives the shape the reciprocal Gram
sum uses.

All four statements are proved. `Gap212.Sieve.SelbergSievingError` and
`Gap212.Sieve.TotientSievingError` are `Gap212.Sieve.selbergSievingError` and
`Gap212.Sieve.totientSievingError`, whose uniform estimate is obtained by removing the modulus
*before* the integration in the summation by parts (modules `Gap212.Sieve.SmoothMoebiusInner` and
`Gap212.Sieve.SmoothTotientInner`). The two Gram limits are equivalent to
`Gap212.Sieve.Polymath41Recip` and `Gap212.Sieve.Polymath41Totient`
(`Gap212.Sieve.lcmGramSumLimitOfSupport_iff_polymath41Recip`,
`Gap212.Sieve.totientGramSumLimitOfSupport_iff_polymath41Totient`), which
`Gap212.Sieve.polymath41Recip` and `Gap212.Sieve.polymath41Totient` prove.

## The naive uniform reading is false

`Gap212.Sieve.MoebiusPartialSumDecay` is `∃ ε > 0, ∀ q ≥ 1, ∃ C, |S_q(w)| ≤ C(1+\log w)^{-1-ε}`,
with the constant quantified **after** the modulus; it is proved
(`Gap212.Sieve.moebiusPartialSumDecay`). The obvious way to read "uniform in the modulus" is to
move `C` out in front, and `Gap212.Sieve.not_uniformMoebiusPartialSumDecay` shows that statement is
**false**.

The witness is the primorial itself. If every prime up to `⌊w⌋` divides `q` then the only `f ≤ w`
coprime to `q` is `f = 1`, so `S_q(w) = 1` exactly
(`Gap212.Sieve.moebiusReciprocalBelow_eq_one_of_primes_dvd`); taking `q = P(⌊w⌋)` and `w` large
beats any fixed `C(1+\log w)^{-1-ε}`. There is no cancellation at all in that regime, because there
is nothing to cancel: the sum has one term.

`W(x)` *is* a primorial, so the refuting configuration is exactly the one the Gram sums meet at
the top of their `e`-range: at `e` with `B/e` below the largest prime dividing `W(x)`, the inner sum
`Gap212.Sieve.innerRecip` is a single term (`Gap212.Sieve.innerRecip_eq_of_primes_dvd`). Any uniform
statement that is to be true has to be modulus-aware — a bound in `\log w` alone cannot hold — and
the Gram limit therefore cannot be proved by feeding a uniform `S_q` bound to the argument of
`Gap212.Sieve.InnerSumReciprocal` at each `e`. What carries the top of the range instead is
the support hypothesis: `F` vanishes on `[β,∞)` and is `C¹`, so `F' (β) = 0` and both the inner sum
and its predicted main term are small there for reasons having nothing to do with cancellation.

## The form the reciprocal Gram sum consumes

`Gap212.Sieve.gramSumRecip` is `∑_{e≤B,(e,W)=1}φ(e)(μ(e)/e)^2Z_F(e)Z_G(e)`, and the Gram limit
normalizes it by `B_x = (φ(W)/W)\log x`. Writing each inner sum in its **normalized** form

  `r_F(e) = \log x·Z_F(e)·φ(eW)/(eW)`   (`Gap212.Sieve.innerRecipRatio`),

whose predicted limit is the bare `-F'(\log_xe)` with no arithmetic factor left in it, the
normalization collapses exactly:

  `(φ(W)/W)\log x·𝓖_x(F,G) = (W/φ(W))/\log x·∑_{e≤B,(e,W)=1}(μ^2(e)/φ(e))·r_F(e)r_G(e)`

(`Gap212.Sieve.gramSumRecip_eq_mertensWeightedSum`). This is an identity, not an estimate — the
arithmetic is `φ(eW) = φ(e)φ(W)` on `(e,W)=1` and nothing else — and it separates the two inputs of
the Gram limit:

* the weight is now `μ^2(e)/φ(e)`, whose partial sums are the Mertens ingredient
  `∑_{e≤y,(e,W)=1}μ^2(e)/φ(e) ∼ (φ(W)/W)\log y`
  (`Gap212.Sieve.sum_moebiusSq_div_totient_coprime`). Under that asymptotic `(W/φ(W))/\log x` times
  the weight is precisely the normalized counting measure of `\log_xe` on `[0,\log_xB]`, whose
  limit is Lebesgue measure;
* the integrand is now `r_F(e)r_G(e)`, and the analytic input is `r_F(e) → -F'(\log_xe)` uniformly
  enough in `e` to pass to the limit against that measure.

So the Gram limit is a Riemann sum, and `Gap212.Sieve.lcmGramSumLimitOfSupport_iff` shows that
this reformulation is *equivalent* to it.

## Main definitions

* `Gap212.Sieve.UniformMoebiusPartialSumDecay`: the decay of `S_q` with the constant moved in front
  of the modulus.
* `Gap212.Sieve.innerRecipRatio`: the inner sum normalized so that its predicted limit is
  `-F'(\log_xe)`.
* `Gap212.Sieve.MertensWeightedGramLimit`: the reciprocal Gram limit as a Riemann sum against
  the weight `μ^2(e)/φ(e)`.

## Main results

* `Gap212.Sieve.moebiusReciprocalBelow_eq_one_of_primes_dvd`: `S_q(w) = 1` when every prime up to
  `w` divides `q`.
* `Gap212.Sieve.innerRecip_eq_of_primes_dvd`: the Gram sum's own inner sum is a single term at the
  top of its `e`-range, so that regime is the refuting one, and
  `Gap212.Sieve.innerRecip_eq_of_lt_primorial_bound` discharges its hypothesis at `W(x)`: every
  `e ∈ (B/(z+1),B]` is in that regime.
* `Gap212.Sieve.not_uniformMoebiusPartialSumDecay`: the uniform-constant reading is false.
* `Gap212.Sieve.gramSumRecip_eq_mertensWeightedSum`: the normalization collapses to the
  `μ^2/φ`-weighted Riemann sum.
* `Gap212.Sieve.lcmGramSumLimitOfSupport_iff`: the Gram limit and its Riemann-sum form are
  equivalent.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY MeasureTheory
open scoped ArithmeticFunction.Moebius

/-! ## The naive uniform reading, refuted -/

/-- **Nothing below `w` is coprime to a modulus divisible by every prime below `w`.** The coprime
range `Gap212.Sieve.coprimeBelow` collapses to `{1}`: any `f > 1` has a prime factor, that prime is
at most `f ≤ ⌊w⌋`, hence divides `q`, contradicting `(f,q) = 1`. -/
theorem coprimeBelow_eq_singleton_one {q : ℕ} {w : ℝ} (hw : 1 ≤ w)
    (hq : ∀ p : ℕ, p.Prime → p ≤ ⌊w⌋₊ → p ∣ q) : coprimeBelow q w = {1} := by
  ext f
  simp only [coprimeBelow, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
  refine ⟨fun ⟨⟨hf1, hfw⟩, hcop⟩ ↦ ?_, ?_⟩
  · by_contra hne
    obtain ⟨p, hp, hpf⟩ := Nat.exists_prime_and_dvd hne
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hcop hpf
      (hq p hp ((Nat.le_of_dvd (by omega) hpf).trans hfw)))
  · rintro rfl
    exact ⟨⟨le_rfl, Nat.le_floor (by exact_mod_cast hw)⟩, Nat.coprime_one_left q⟩

/-- **The truncated Möbius sum is exactly `1` when the modulus swallows every prime in range.**
`Gap212.Sieve.moebiusReciprocalBelow` has a single term, the `f = 1` one. There is no cancellation
in this regime because there is nothing to cancel. -/
theorem moebiusReciprocalBelow_eq_one_of_primes_dvd {q : ℕ} {w : ℝ} (hw : 1 ≤ w)
    (hq : ∀ p : ℕ, p.Prime → p ≤ ⌊w⌋₊ → p ∣ q) : moebiusReciprocalBelow q w = 1 := by
  simp [moebiusReciprocalBelow, coprimeBelow_eq_singleton_one hw hq]

/-- **The primorial instance**: at `q = P(⌊w⌋)` the truncated Möbius sum is `1` for every `w ≥ 1`,
every prime up to `⌊w⌋` dividing the primorial. -/
theorem moebiusReciprocalBelow_primorial_eq_one {w : ℝ} (hw : 1 ≤ w) :
    moebiusReciprocalBelow (primorial ⌊w⌋₊) w = 1 :=
  moebiusReciprocalBelow_eq_one_of_primes_dvd hw fun _ hp hple ↦ hp.dvd_primorial_iff.2 hple

/-- **The Gram sum's inner sum degenerates to a single term at the top of the `e`-range.** If every
prime up to `B/e` divides `eW` then `Gap212.Sieve.innerRecip` is just its `f = 1` term,
`F(\log_xe)`: no cancellation is available there, for the same reason as in
`Gap212.Sieve.moebiusReciprocalBelow_eq_one_of_primes_dvd`.

The hypothesis is met in the Gram sum, and not marginally. `W(x)` is the primorial of
`z = ⌊\log\log\log x⌋`, so every prime not dividing `eW(x)` exceeds `z`; hence *every* `e` in
`(B/(z+1), B]` — and the sum runs to `B` — has a one-term inner sum. -/
theorem innerRecip_eq_of_primes_dvd {W e B : ℕ} {x : ℝ} (he : 0 < e) (heB : e ≤ B)
    (hq : ∀ p : ℕ, p.Prime → p ≤ ⌊(B : ℝ) / (e : ℝ)⌋₊ → p ∣ e * W) (F : ℝ → ℝ) :
    innerRecip W e F x B = F (Notation.logx x e) := by
  rw [innerRecip, coprimeBelow_eq_singleton_one
    ((one_le_div (Nat.cast_pos.mpr he)).mpr (by exact_mod_cast heB)) hq]
  simp

/-- **The decay of `S_q` with the constant uniform in the modulus.** This is
`Gap212.Sieve.MoebiusPartialSumDecay` with `C` quantified *before* `q` instead of after it — the
literal reading of "Möbius cancellation uniform in the modulus".

It is false: `Gap212.Sieve.not_uniformMoebiusPartialSumDecay`. -/
def UniformMoebiusPartialSumDecay : Prop :=
  ∃ ε > (0 : ℝ), ∃ C : ℝ, ∀ q : ℕ, 1 ≤ q → ∀ w : ℝ, 2 ≤ w →
    |moebiusReciprocalBelow q w| ≤ C / (1 + Real.log w) ^ (1 + ε)

/-- **The uniform-constant reading is false.** At `q = P(⌊w⌋)` the sum is exactly `1`
(`Gap212.Sieve.moebiusReciprocalBelow_primorial_eq_one`) while the asserted bound tends to `0`, so
any fixed `C` is beaten by taking `w` with `1 + \log w > C`.

Hence the constant of `Gap212.Sieve.moebiusPartialSumDecay` cannot be made independent of the
modulus. -/
theorem not_uniformMoebiusPartialSumDecay : ¬ UniformMoebiusPartialSumDecay := by
  rintro ⟨ε, hε, C, hbd⟩
  set w : ℝ := max 2 (Real.exp C)
  have hw2 : (2 : ℝ) ≤ w := le_max_left _ _
  have hCw : C ≤ Real.log w := by
    simpa using Real.log_le_log (Real.exp_pos C) (le_max_right 2 (Real.exp C))
  have hlog : 0 ≤ Real.log w := Real.log_nonneg (by linarith)
  have h := hbd (primorial ⌊w⌋₊) (primorial_pos _) w hw2
  rw [moebiusReciprocalBelow_primorial_eq_one (by linarith), abs_one,
    le_div_iff₀ (Real.rpow_pos_of_pos (by linarith) _), one_mul] at h
  -- the denominator is at least `1 + log w`, so the bound is below `1`
  have hden : 1 + Real.log w ≤ (1 + Real.log w) ^ (1 + ε) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (x := 1 + Real.log w) (by linarith)
      (by linarith : (1 : ℝ) ≤ 1 + ε)
  linarith

/-- **The top of the Gram sum's own `e`-range is the one-term regime, named.** At `W = W(x)`, the
primorial of `z = ⌊\log\log\log x⌋`, every `e` with `B/e < z+1` — that is, every
`e ∈ (B/(z+1), B]` — has a one-term inner sum, because a prime `p ≤ B/e` is then `≤ z` and so
divides the primorial. This is `Gap212.Sieve.innerRecip_eq_of_primes_dvd` with its hypothesis
discharged at the modulus `W(x)` of `Gap212.Sieve.gramSumRecip`.

On this range
`\log x·Z_F(e) = \log x·F(\log_xe)`, which the support hypothesis makes small only because
`\log_xe ≥ \log_xB - \log(z+1)/\log x ≥ β - \log(z+1)/\log x` forces
`|F(\log_xe)| ≤ ‖F'‖_∞·\log(z+1)/\log x`; so the analytic input is an average over `e`
(module `Gap212.Sieve.GramRiemannSum`). -/
theorem innerRecip_eq_of_lt_primorial_bound {x : ℝ} {e B : ℕ} (he : 0 < e) (heB : e ≤ B)
    (hz : (B : ℝ) / (e : ℝ) < (⌊Real.log (Real.log (Real.log x))⌋₊ : ℝ) + 1) (F : ℝ → ℝ) :
    innerRecip (W x) e F x B = F (Notation.logx x e) := by
  refine innerRecip_eq_of_primes_dvd he heB (fun p hp hple ↦
    (hp.dvd_primorial_iff.2 (hple.trans (Nat.le_of_lt_succ ?_))).mul_left e) F
  exact (Nat.floor_lt (by positivity)).mpr (by exact_mod_cast hz)

/-! ## The Gram sum as a Riemann sum -/

/-- **The inner sum, normalized so that its predicted limit carries no arithmetic factor.**
`r_F(e) = \log x·Z_F(e)·φ(eW)/(eW)`, with `Z_F` the `Gap212.Sieve.innerRecip` of the reciprocal
kernel. The fixed-modulus `Gap212.Sieve.tendsto_logx_mul_innerSumReciprocal` evaluates
`\log x·Z_F(q)` to `-F'(0)·q/φ(q)`, so dividing out `q/φ(q)` at `q = eW` is what leaves the bare
`-F'(\log_xe)` as the shape to aim at. -/
noncomputable def innerRecipRatio (W e : ℕ) (F : ℝ → ℝ) (x : ℝ) (B : ℕ) : ℝ :=
  Real.log x * innerRecip W e F x B * (((e * W).totient : ℝ) / ((e * W : ℕ) : ℝ))

/-- **The Gram weight against the square of the normalized inner sums.** For `e ≥ 1` coprime to
`W ≥ 1`,

  `(φ(W)/W)·φ(e)(μ(e)/e)^2 = (W/φ(W))·(μ^2(e)/φ(e))·(φ(eW)/(eW))^2`,

which is the whole arithmetic of the collapse below: `φ(eW) = φ(e)φ(W)` and nothing else. Both
sides vanish when `e` is not squarefree, so no squarefreeness hypothesis is needed. -/
theorem totient_ratio_mul_lcmGramWeight {e W : ℕ} (hcop : Nat.Coprime e W) :
    ((W.totient : ℝ) / (W : ℝ)) * lcmGramWeight e
      = ((W : ℝ) / (W.totient : ℝ)) * ((μ e : ℝ) ^ 2 / (e.totient : ℝ))
          * (((e * W).totient : ℝ) / ((e * W : ℕ) : ℝ)) ^ 2 := by
  rw [lcmGramWeight, Nat.totient_mul hcop]
  push_cast
  field_simp

/-- **The normalized Gram sum is a `μ^2/φ`-weighted sum of the normalized inner sums.** For `x > 1`
and `W ≥ 1`,

  `(φ(W)/W)\log x·𝓖_x(F,G) = (W/φ(W))/\log x·∑_{e≤B,(e,W)=1}(μ^2(e)/φ(e))·r_F(e)r_G(e)`,

with `r_F` the `Gap212.Sieve.innerRecipRatio`. An exact identity, term by term: the two factors of
`\log x` in the `r`'s pay for the `\log x` on the left and the `1/\log x` on the right, and the
arithmetic is `Gap212.Sieve.totient_ratio_mul_lcmGramWeight`.

This change of variables separates the two inputs of the Gram limit: the Mertens asymptotic for
`∑μ^2(e)/φ(e)` and the uniform evaluation of `r_F`. -/
theorem gramSumRecip_eq_mertensWeightedSum {x : ℝ} (hx : 1 < x) {W B : ℕ} (hW : 0 < W)
    (F G : ℝ → ℝ) :
    ((W.totient : ℝ) / (W : ℝ)) * Real.log x * gramSumRecip W B x F G
      = ((W : ℝ) / (W.totient : ℝ)) / Real.log x *
          ∑ e ∈ Icc 1 B with Nat.Coprime W e,
            ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
              (innerRecipRatio W e F x B * innerRecipRatio W e G x B) := by
  rw [gramSumRecip, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  obtain ⟨hmem, hcop⟩ := Finset.mem_filter.mp he
  have hL : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [innerRecipRatio, innerRecipRatio]
  calc _ = ((W.totient : ℝ) / (W : ℝ) * lcmGramWeight e)
        * (Real.log x * (innerRecip W e F x B * innerRecip W e G x B)) := by ring
    _ = _ := by
      rw [totient_ratio_mul_lcmGramWeight hcop.symm]
      field_simp

/-- **The reciprocal Gram limit as a Riemann sum.** `Gap212.Sieve.LcmGramSumLimitOfSupport`
rewritten through `Gap212.Sieve.gramSumRecip_eq_mertensWeightedSum`: the weight is `μ^2(e)/φ(e)`,
the normalization `(W/φ(W))/\log x`, and the summand the product of the two normalized inner sums
`Gap212.Sieve.innerRecipRatio`, whose predicted values are `-F'(\log_xe)` and `-G'(\log_xe)`.

`Gap212.Sieve.lcmGramSumLimitOfSupport_iff` proves the two equivalent. In this form the two
ingredients are separate statements: the Mertens
asymptotic `∑_{e≤y,(e,W)=1}μ^2(e)/φ(e) ∼ (φ(W)/W)\log y`, which turns the normalization into the
counting measure of `\log_xe`; and the uniform evaluation of `r_F(e)`.

The profiles are `C^∞`, as in `Gap212.Sieve.LcmGramSumLimitOfSupport`. -/
def MertensWeightedGramLimit : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → ContDiff ℝ (⊤ : ℕ∞) G →
    HasCompactSupport G →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) → (∀ t, β ≤ t → G t = 0) →
      ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
        Filter.Tendsto (fun x : ℝ ↦ ((W x : ℝ) / ((W x).totient : ℝ)) / Real.log x *
            ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
              ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
                (innerRecipRatio (W x) e F x (B x) *
                  innerRecipRatio (W x) e G x (B x))) Filter.atTop
          (nhds (∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t))

/-- **The Gram limit and its Riemann-sum form are the same statement.** The two normalized
quantities agree for every `x > 1` by `Gap212.Sieve.gramSumRecip_eq_mertensWeightedSum`, and both
limits are taken at `atTop`. -/
theorem lcmGramSumLimitOfSupport_iff :
    LcmGramSumLimitOfSupport ↔ MertensWeightedGramLimit := by
  have key : ∀ (F G : ℝ → ℝ) (B : ℝ → ℕ),
      (fun x : ℝ ↦ ((W x).totient : ℝ) / (W x : ℝ) * Real.log x *
          gramSumRecip (W x) (B x) x F G)
        =ᶠ[atTop] fun x : ℝ ↦ ((W x : ℝ) / ((W x).totient : ℝ)) / Real.log x *
          ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
            ((μ e : ℝ) ^ 2 / (e.totient : ℝ)) *
              (innerRecipRatio (W x) e F x (B x) * innerRecipRatio (W x) e G x (B x)) := by
    intro F G B
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact gramSumRecip_eq_mertensWeightedSum hx (primorial_pos _) F G
  exact ⟨fun h F G hF hFc hG hGc β hβ hFv hGv B hB ↦
      (h F G hF hFc hG hGc β hβ hFv hGv B hB).congr' (key F G B),
    fun h F G hF hFc hG hGc β hβ hFv hGv B hB ↦
      (h F G hF hFc hG hGc β hβ hFv hGv B hB).congr' (key F G B).symm⟩

end Gap212.Sieve
