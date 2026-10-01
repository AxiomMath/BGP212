/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.DivisorSumOverQstar
public import Gap212.Sieve.GramDatum
public import Gap212.Sieve.InnerSumTotient
public import Gap212.Sieve.MoebiusTotientAsymptotic
public import Gap212.Sieve.PrimeTailProduct
public import Gap212.Sieve.WSieve

/-!
# The totient Gram-sum limit as a Riemann sum, and the correction factor it carries

`Gap212.Sieve.lcmGramSumLimitOfSupport_iff` (`Gap212.Sieve.UniformModulusInput`) proves the
*reciprocal* Gram-sum limit equivalent to a Riemann sum against the weight `μ²(e)/φ(e)`. This file
is the totient analogue: `Gap212.Sieve.totientGramSumLimitOfSupport_iff` proves
`Gap212.Sieve.TotientGramSumLimitOfSupport` equivalent to a Riemann sum, and then treats the one
structural asymmetry between the two kernels.

## The normalization is forced, and it is *not* the reciprocal one

Writing `Y_F(e) = Gap212.Sieve.innerTotient` and `g(e) = (μ*φ)(e)(μ(e)/φ(e))²` for the Gram weight
`Gap212.Sieve.gramWeight`, a normalized inner sum `ρ_F(e) = \log x·Y_F(e)·A(e)` turns the
Gram-sum limit into a weighted sum against `w(e) = (φ(W)/W)²g(e)/A(e)²`. Only one choice of `A`
makes the predicted value of `ρ_F(e)` independent of `e`, and it is

  `A(e) = ((μ*φ)(e)/φ(e))·(φ(W)/W)`,  hence  `w(e) = μ²(e)/(μ*φ)(e)`

(`Gap212.Sieve.innerTotientRatio`, `Gap212.Sieve.totient_ratio_mul_gramWeight`). The identity
`Gap212.Sieve.gramSumTotient_eq_muPhiWeightedSum` is then exact, term by term, with the *same*
normalization `κ_x = (W/φ(W))/\log x` the reciprocal kernel uses:

  `(φ(W)/W)\log x·𝓖_x(F,G) = κ_x·∑_{e≤B,(e,W)=1}(μ²(e)/(μ*φ)(e))·ρ_F(e)ρ_G(e)`.

**The weight is `μ²(e)/(μ*φ)(e)` and not `μ²(e)/φ(e)`**, so this kernel does not use the Mertens
asymptotic `Gap212.Sieve.sum_moebiusSq_div_totient_coprime`: forcing the weight to be `μ²/φ`
forces `A(e) = \sqrt{(μ*φ)(e)/φ(e)}`, whose predicted value `-F'(\log_xe)·c_{eW}·A(e)` carries the
`e`-dependent factor `∏_{p∣e}\sqrt{(p-1)/(p-2)}` and is therefore not a Riemann sum at all. The two
kernels share `κ_x`, the shape of the argument, and the analytic difficulty; they do **not** share
the arithmetic input.

What the totient kernel needs instead is
`∑_{e≤y,(e,W)=1}μ²(e)/(μ*φ)(e) ∼ (φ(W)/W)(∏_{p∤W}(1-1/(p-1)²))^{-1}\log y`, with error uniform in
`W`: this is `Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime` (`Gap212.Sieve.MertensMuPhi`).
Its constant differs from that of `∑μ²(e)/φ(e)`, which is `φ(W)/W`, by exactly the correction
factor below.

## Where the correction factor lives, and that it is removable

`Gap212.Sieve.TotientGramSumLimitOfSupport` asserts the clean limit `∫₀^∞F'G'`, while at **fixed**
`W` the normalized Gram sum tends to `(∏_{p∤W}(1-1/(p-1)²))·∫₀^∞F'G'` — the twin-prime constant
`0.660162` at `W = 2`. The Riemann form above locates that factor precisely, and it arrives in two
pieces that do not cancel:

* the predicted value of `ρ_F(e)` is `-F'(\log_xe)·∏_{p∤W}(1-1/(p-1)²)`, carrying **two** powers of
  the product — `c_{eW}·A(e) = (e(μ*φ)(e)/φ(e)²)·∏_{p∤eW}(1-1/(p-1)²)`, and the first factor is
  `∏_{p∣e}(1-1/(p-1)²)`, so the `e`-dependence cancels and what is left is the product over
  `p ∤ W`;
* the weight's Mertens constant carries **one inverse** power
  (`Gap212.Sieve.sum_moebiusSq_div_moebiusTotient_coprime`).

Two and one inverse leave one. So the clean limit holds only jointly in `W`, and the single step
that removes the factor is the convergence of that prime
product. That step is `Gap212.Sieve.exists_threshold_prod_one_sub_ge`
(`Gap212.Sieve.PrimeTailProduct`), and it is wired in here:
`Gap212.Sieve.tendsto_tprod_corr_W` is `∏_{p∤W(x)}(1-1/(p-1)²) → 1`, and
`Gap212.Sieve.tendsto_inv_tprod_corr_W` the inverse form the weight's constant needs. The
uniformity in the finite set is what makes this work — the set of primes not dividing `W(x)` varies
with `x`, and `W(x)` being the primorial of `⌊\log\log\log x⌋` every such prime exceeds a threshold
tending to infinity (`Gap212.Sieve.eventually_dvd_W_of_prime_le`).

Nothing here touches the analytic content, that `ρ_F(e)` is on average its predicted value; that
statement does not hold pointwise. `Gap212.Sieve.TotientGramMeasure` spends the arithmetic and
restates the rest as the equivalent `Gap212.Sieve.TotientGramRatioDefectVanishes`.

That content is of the **same kind** as the reciprocal kernel's and is **not the same statement**.
`Gap212.Sieve.innerRecip` weights its Möbius sum by `1/f` while `Gap212.Sieve.innerTotient` weights
it by `1/φ(f)`; the two normalizations differ by `∏_{p∣e}(1-1/(p-1)²)` on a squarefree `e` coprime
to `W` (`Gap212.Sieve.mul_moebiusTotient_div_totient_sq`); and the averaging weights differ by
`∏_{p∣e}(p-1)/(p-2)`. What is shared is the mechanism — Möbius cancellation uniform in the growing
modulus `eW(x)`, on average over `e` — and the fact that the top of the `e`-range carries no
cancellation at all (`Gap212.Sieve.innerTotient_eq_of_lt_primorial_bound`). Neither kernel's defect
statement is available from the other.

## Main definitions

* `Gap212.Sieve.innerTotientRatio`: the inner sum normalized so that its predicted value is
  `-F'(\log_xe)` times a factor independent of `e`.
* `Gap212.Sieve.TotientMuPhiWeightedGramLimit`: the Gram-sum limit as a Riemann sum against
  `μ²(e)/(μ*φ)(e)`.

## Main results

* `Gap212.Sieve.totient_ratio_mul_gramWeight`: the arithmetic of the collapse.
* `Gap212.Sieve.gramSumTotient_eq_muPhiWeightedSum`: the exact identity.
* `Gap212.Sieve.totientGramSumLimitOfSupport_iff`: the Gram-sum limit and its Riemann form are
  equivalent.
* `Gap212.Sieve.mul_moebiusTotient_div_totient_sq`,
  `Gap212.Sieve.innerSumTotientConst_mul_normalization`: the predicted value of the normalized
  inner sum is `-F'(\log_xe)` times a factor independent of `e` — so the correction is one
  `W`-limit.
* `Gap212.Sieve.tendsto_tprod_corr_W`, `Gap212.Sieve.tendsto_inv_tprod_corr_W`: the correction
  factor and its inverse tend to `1` along the pre-sieving primorials — spent in
  `Gap212.Sieve.TotientGramMeasure`.
-/

@[expose] public section

namespace Gap212.Sieve

open Filter Finset Gap212.GPY MeasureTheory
open scoped ArithmeticFunction.Moebius

/-! ## The totient Gram sum as a Riemann sum -/

/-- **The inner sum, normalized so that its predicted value carries no `e`-dependent factor.**
`ρ_F(e) = \log x·Y_F(e)·((μ*φ)(e)/φ(e))·(φ(W)/W)`, with `Y_F` the `Gap212.Sieve.innerTotient` of
the totient kernel.

The fixed-modulus asymptotic `Gap212.Sieve.tendsto_logx_mul_innerSumTotient` evaluates
`\log x·Y_F(q)` to `-F'(0)·c_q` with `c_q = (q/φ(q))∏_{p∤q}(1-1/(p-1)²)`
(`Gap212.Sieve.innerSumTotientConst`), so at `q = eW` this normalization predicts

  `ρ_F(e) → -F'(\log_xe)·(e(μ*φ)(e)/φ(e)²)·∏_{p∤eW}(1-1/(p-1)²)
          = -F'(\log_xe)·∏_{p∤W}(1-1/(p-1)²)`,

the first factor being `∏_{p∣e}(1-1/(p-1)²)` on a squarefree `e`. The `e`-dependence cancels
exactly, which is what makes the remaining correction a single `W`-limit
(`Gap212.Sieve.tendsto_tprod_corr_W`). -/
noncomputable def innerTotientRatio (W e : ℕ) (F : ℝ → ℝ) (x : ℝ) (B : ℕ) : ℝ :=
  Real.log x * innerTotient W e F x B *
    (moebiusTotient e / (e.totient : ℝ)) * ((W.totient : ℝ) / (W : ℝ))

/-- **The Gram weight against the square of the normalized inner sums.** For `e ≥ 1` and `W ≥ 1`,

  `(φ(W)/W)·(μ*φ)(e)(μ(e)/φ(e))² = (W/φ(W))·(μ²(e)/(μ*φ)(e))·(((μ*φ)(e)/φ(e))(φ(W)/W))²`,

which is the whole arithmetic of the collapse below. No coprimality is needed — unlike the
reciprocal kernel's `Gap212.Sieve.totient_ratio_mul_lcmGramWeight`, which has to know
`φ(eW) = φ(e)φ(W)`, this identity is pure algebra in `(μ*φ)(e)`, `φ(e)`, `μ(e)` and `φ(W)/W`. Both
sides vanish when `(μ*φ)(e) = 0` — in particular on every even `e`, where `p = 2` contributes the
factor `p - 2` — so no hypothesis excludes that case either. -/
theorem totient_ratio_mul_gramWeight {e W : ℕ} (he : 0 < e) (hW : 0 < W) :
    ((W.totient : ℝ) / (W : ℝ)) * gramWeight e
      = ((W : ℝ) / (W.totient : ℝ)) * ((μ e : ℝ) ^ 2 / moebiusTotient e)
          * (moebiusTotient e / (e.totient : ℝ) * ((W.totient : ℝ) / (W : ℝ))) ^ 2 := by
  have hpe : (0 : ℝ) < (e.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr he
  have hWR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hpW : (0 : ℝ) < (W.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hW
  rw [gramWeight]
  rcases eq_or_ne (moebiusTotient e) 0 with hm | hm
  · simp [hm]
  · field_simp

/-- **The normalized totient Gram sum is a `μ²/(μ*φ)`-weighted sum of normalized inner sums.** For
`x > 1` and `W ≥ 1`,

  `(φ(W)/W)\log x·𝓖_x(F,G) = (W/φ(W))/\log x·∑_{e≤B,(e,W)=1}(μ²(e)/(μ*φ)(e))·ρ_F(e)ρ_G(e)`,

with `ρ_F` the `Gap212.Sieve.innerTotientRatio`. An exact identity, term by term: the two factors
of `\log x` in the `ρ`'s pay for the `\log x` on the left and the `1/\log x` on the right, and the
arithmetic is `Gap212.Sieve.totient_ratio_mul_gramWeight`. The normalization `(W/φ(W))/\log x` is
literally the reciprocal kernel's `Gap212.Sieve.mertensKappa`; only the weight differs.

This change of variables separates the two inputs of the Gram-sum limit — a Mertens asymptotic
for `∑μ²(e)/(μ*φ)(e)`, whose constant carries the correction factor, and the uniform evaluation of
`ρ_F`; see the module docstring. -/
theorem gramSumTotient_eq_muPhiWeightedSum {x : ℝ} (hx : 1 < x) {W B : ℕ} (hW : 0 < W)
    (F G : ℝ → ℝ) :
    ((W.totient : ℝ) / (W : ℝ)) * Real.log x * gramSumTotient W B x F G
      = ((W : ℝ) / (W.totient : ℝ)) / Real.log x *
          ∑ e ∈ Icc 1 B with Nat.Coprime W e,
            ((μ e : ℝ) ^ 2 / moebiusTotient e) *
              (innerTotientRatio W e F x B * innerTotientRatio W e G x B) := by
  classical
  rw [gramSumTotient, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  have h := totient_ratio_mul_gramWeight (Finset.mem_Icc.1 (Finset.mem_filter.1 he).1).1 hW
  rw [innerTotientRatio, innerTotientRatio, div_mul_eq_mul_div _ (Real.log x),
    eq_div_iff (Real.log_pos hx).ne']
  linear_combination (Real.log x ^ 2 * (innerTotient W e F x B * innerTotient W e G x B)) * h

/-- **The totient Gram-sum limit as a Riemann sum.** `Gap212.Sieve.TotientGramSumLimitOfSupport`
rewritten through `Gap212.Sieve.gramSumTotient_eq_muPhiWeightedSum`: the weight is
`μ²(e)/(μ*φ)(e)`, the normalization `(W/φ(W))/\log x`, and the summand the product of the two
normalized inner sums `Gap212.Sieve.innerTotientRatio`, whose predicted values are
`-F'(\log_xe)·∏_{p∤W}(1-1/(p-1)²)` and `-G'(\log_xe)·∏_{p∤W}(1-1/(p-1)²)`.

`Gap212.Sieve.totientGramSumLimitOfSupport_iff` proves the two equivalent. In this form the two
ingredients are separate statements: the Mertens asymptotic for the weight, which is *not* the one
the reciprocal kernel uses, and the uniform evaluation of `ρ_F(e)`. The profiles are `C^∞`, as in
`Gap212.Sieve.TotientGramSumLimitOfSupport`. -/
def TotientMuPhiWeightedGramLimit : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → ContDiff ℝ (⊤ : ℕ∞) G →
    HasCompactSupport G →
    ∀ β : ℝ, 0 < β → (∀ t, β ≤ t → F t = 0) → (∀ t, β ≤ t → G t = 0) →
      ∀ B : ℝ → ℕ, (∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ)) →
        Filter.Tendsto (fun x : ℝ ↦ ((W x : ℝ) / ((W x).totient : ℝ)) / Real.log x *
            ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
              ((μ e : ℝ) ^ 2 / moebiusTotient e) *
                (innerTotientRatio (W x) e F x (B x) *
                  innerTotientRatio (W x) e G x (B x))) Filter.atTop
          (nhds (∫ t in Set.Ioi (0 : ℝ), deriv F t * deriv G t))

/-- **The Gram-sum limit and its Riemann-sum form are the same statement.** The two normalized
quantities agree for every `x > 1` by `Gap212.Sieve.gramSumTotient_eq_muPhiWeightedSum`, and both
limits are taken at `atTop`. -/
theorem totientGramSumLimitOfSupport_iff :
    TotientGramSumLimitOfSupport ↔ TotientMuPhiWeightedGramLimit := by
  have key : ∀ (F G : ℝ → ℝ) (B : ℝ → ℕ),
      (fun x : ℝ ↦ ((W x).totient : ℝ) / (W x : ℝ) * Real.log x *
          gramSumTotient (W x) (B x) x F G)
        =ᶠ[atTop] fun x : ℝ ↦ ((W x : ℝ) / ((W x).totient : ℝ)) / Real.log x *
          ∑ e ∈ Icc 1 (B x) with Nat.Coprime (W x) e,
            ((μ e : ℝ) ^ 2 / moebiusTotient e) *
              (innerTotientRatio (W x) e F x (B x) * innerTotientRatio (W x) e G x (B x)) :=
    fun F G B ↦ by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
        using gramSumTotient_eq_muPhiWeightedSum hx (primorial_pos _) F G
  exact ⟨fun h F G hF hFc hG hGc β hβ hFv hGv B hB ↦
      (h F G hF hFc hG hGc β hβ hFv hGv B hB).congr' (key F G B),
    fun h F G hF hFc hG hGc β hβ hFv hGv B hB ↦
      (h F G hF hFc hG hGc β hβ hFv hGv B hB).congr' (key F G B).symm⟩

/-! ## The correction factor is independent of `e` -/

/-- **The local factor of the correction product, written out.** `1 - 1/(p-1)² = p(p-2)/(p-1)²` for
`p ≥ 2`, which is what identifies `e(μ*φ)(e)/φ(e)²` with the partial product over `p ∣ e`. At
`p = 2` both sides are `0`, which is why no evenness hypothesis appears below. -/
theorem one_sub_inv_sub_one_sq_eq {p : ℕ} (hp : 2 ≤ p) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 = (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
  have hne : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.2 (by norm_cast; omega)
  field_simp
  ring

/-- **`e(μ*φ)(e)/φ(e)² = ∏_{p ∣ e}(1 - 1/(p-1)²)` on a squarefree `e`.** Each side is a product of
local factors: `e = ∏p`, `(μ*φ)(e) = ∏(p-2)` and `φ(e) = ∏(p-1)`, and
`Gap212.Sieve.one_sub_inv_sub_one_sq_eq` matches them term by term. -/
theorem mul_moebiusTotient_div_totient_sq {e : ℕ} (he : Squarefree e) :
    (e : ℝ) * moebiusTotient e / (e.totient : ℝ) ^ 2
      = ∏ p ∈ e.primeFactors, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have hloc : ∀ p ∈ e.primeFactors, 1 - 1 / ((p : ℝ) - 1) ^ 2
      = (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := fun p hp ↦
    one_sub_inv_sub_one_sq_eq (Nat.prime_of_mem_primeFactors hp).two_le
  rw [Finset.prod_congr rfl hloc, Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow, moebiusTotient_of_squarefree he, totient_of_squarefree he, ← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree he]

/-- **The predicted value of `Gap212.Sieve.innerTotientRatio` carries no `e`-dependent factor.**
For `e` squarefree and coprime to `W ≥ 1`,

  `c_{eW}·((μ*φ)(e)/φ(e))·(φ(W)/W) = ∏_{p∤W}(1 - 1/(p-1)²)`,

with `c_q = Gap212.Sieve.innerSumTotientConst q` the constant of
`Gap212.Sieve.tendsto_logx_mul_innerSumTotient`. So the fixed-modulus asymptotic predicts
`ρ_F(e) → -F'(\log_xe)·∏_{p∤W}(1-1/(p-1)²)` with the **same** factor at every `e`, and the
correction the totient kernel carries is a single `W`-limit rather than a family of them.

The cancellation is `c_{eW} = (eW/φ(eW))∏_{p∤eW}(1-1/(p-1)²)` against
`e(μ*φ)(e)/φ(e)² = ∏_{p∣e}(1-1/(p-1)²)`
(`Gap212.Sieve.mul_moebiusTotient_div_totient_sq`): restoring the primes dividing `e` to a product
taken over `p ∤ eW` gives the product over `p ∤ W`, `e` and `W` being coprime. No evenness is
assumed and none is needed — on an even `e` both sides vanish, the left because `(μ*φ)(e) = 0` and
the right because `2 ∤ W` puts the vanishing factor at `p = 2` into the product. -/
theorem innerSumTotientConst_mul_normalization {e W : ℕ} (he : Squarefree e) (hW : 0 < W)
    (hcop : Nat.Coprime e W) :
    innerSumTotientConst (e * W) * (moebiusTotient e / (e.totient : ℝ))
        * ((W.totient : ℝ) / (W : ℝ))
      = ∏' p : ℕ, if p.Prime ∧ ¬ p ∣ W then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 := by
  classical
  have he0 : 0 < e := Nat.pos_of_ne_zero he.ne_zero
  have hWR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hφW : (0 : ℝ) < (W.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hW
  have hg1 : ∀ p ∉ e.primeFactors,
      (if p.Prime ∧ p ∣ e then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) = 1 := fun p hp ↦
    if_neg fun h ↦ hp (Nat.mem_primeFactors.mpr ⟨h.1, h.2, he0.ne'⟩)
  -- the correction product at `W` factors as the one at `eW` times the primes dividing `e`
  have hsplit : ∀ p : ℕ, (if p.Prime ∧ ¬ p ∣ W then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)
      = (if p.Prime ∧ ¬ p ∣ e * W then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)
        * (if p.Prime ∧ p ∣ e then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) := by
    intro p
    by_cases hp : p.Prime
    · have := Nat.eq_one_of_dvd_coprimes (k := p) hcop
      by_cases hpW : p ∣ W <;> by_cases hpe : p ∣ e <;> simp_all [Nat.Prime.dvd_mul]
    · simp [hp]
  have hprod : (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ W then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)
      = (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ e * W then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)
        * ∏ p ∈ e.primeFactors, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    rw [tprod_congr hsplit,
      Multipliable.tprod_mul (multipliable_corr (e * W)) (multipliable_of_ne_finset_one hg1),
      tprod_eq_prod hg1]
    exact congrArg _ (Finset.prod_congr rfl fun p hp ↦
      if_pos ⟨Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩)
  -- the arithmetic prefactor
  rw [hprod, innerSumTotientConst, Nat.totient_mul hcop, ← mul_moebiusTotient_div_totient_sq he]
  push_cast
  field_simp

/-! ## The correction factor, and that it tends to one -/

/-- **The threshold bound, read over a finite set of natural numbers.**
`Gap212.Sieve.exists_threshold_prod_one_sub_ge` is stated over `Finset Nat.Primes`, while the
consumers meet a `Finset ℕ` — the primes dividing one of their moduli. The transfer is by
`Finset.attach` and `Finset.prod_image`, the map `n ↦ ⟨n, prime⟩` being injective. -/
theorem prod_one_sub_of_prime_gt {z : ℕ} {ε : ℝ}
    (hthr : ∀ s : Finset Nat.Primes, (∀ p ∈ s, z < (p : ℕ)) →
      1 - ε ≤ ∏ p ∈ s, (1 - primeTailWeight p) ∧ ∏ p ∈ s, (1 - primeTailWeight p) ≤ 1)
    (t : Finset ℕ) (htp : ∀ p ∈ t, p.Prime) (htz : ∀ p ∈ t, z < p) :
    1 - ε ≤ ∏ p ∈ t, (1 - 1 / ((p : ℝ) - 1) ^ 2)
      ∧ ∏ p ∈ t, (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ 1 := by
  classical
  set φp : {n // n ∈ t} → Nat.Primes := fun a ↦ ⟨a.1, htp a.1 a.2⟩
  have hkey : ∏ p ∈ t.attach.image φp, (1 - primeTailWeight p)
      = ∏ p ∈ t, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    rw [Finset.prod_image (g := φp) fun a _ b _ h ↦
      Subtype.ext (congrArg (fun p : Nat.Primes ↦ (p : ℕ)) h)]
    exact Finset.prod_attach t fun n ↦ 1 - 1 / ((n : ℝ) - 1) ^ 2
  rw [← hkey]
  refine hthr _ fun p hp ↦ ?_
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hp
  exact htz a.1 a.2

/-- **The correction factor of a modulus absorbing every prime below the threshold lies in
`[1-ε, 1]`.** The infinite product `∏_{p∤V}(1-1/(p-1)²)` is the limit of its finite partial
products (`Gap212.Sieve.multipliable_corr`), each of which is a product over primes not dividing
`V` — hence, `V` absorbing every prime up to `z`, over primes exceeding `z`, where
`Gap212.Sieve.exists_threshold_prod_one_sub_ge` bounds it uniformly. Uniformity in the finite set
is exactly what lets the bound pass to the limit. -/
theorem tprod_corr_mem_of_primes_dvd {V z : ℕ} {ε : ℝ}
    (hthr : ∀ s : Finset Nat.Primes, (∀ p ∈ s, z < (p : ℕ)) →
      1 - ε ≤ ∏ p ∈ s, (1 - primeTailWeight p) ∧ ∏ p ∈ s, (1 - primeTailWeight p) ≤ 1)
    (hV : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ V) :
    1 - ε ≤ (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)
      ∧ (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) ≤ 1 := by
  classical
  have hfin : ∀ s : Finset ℕ,
      1 - ε ≤ ∏ p ∈ s, (if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)
        ∧ (∏ p ∈ s, if p.Prime ∧ ¬ p ∣ V then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) ≤ 1 := by
    intro s
    rw [← Finset.prod_filter]
    refine prod_one_sub_of_prime_gt hthr _ (fun p hp ↦ (Finset.mem_filter.mp hp).2.1)
      fun p hp ↦ ?_
    obtain ⟨-, hprime, hnd⟩ := Finset.mem_filter.mp hp
    exact not_le.1 fun h ↦ hnd (hV p hprime h)
  have hHP := (multipliable_corr V).hasProd
  exact ⟨ge_of_tendsto' hHP fun s ↦ (hfin s).1, le_of_tendsto' hHP fun s ↦ (hfin s).2⟩

/-- **The correction factor tends to `1` along the pre-sieving primorials.**

  `∏_{p ∤ W(x)}(1 - 1/(p-1)²) ⟶ 1`   (`x → ∞`).

This removes the correction factor between the fixed-`W` limit
`(∏_{p∤W}(1-1/(p-1)²))·∫₀^∞F'G'` and the clean limit asserted by
`Gap212.Sieve.TotientGramSumLimitOfSupport`.

`W(x)` is the primorial of `⌊\log\log\log x⌋`, so a prime fails to divide it only by exceeding
that bound (`Gap212.Sieve.eventually_dvd_W_of_prime_le`), and the tail of `∑_p 1/(p-1)²` is small
uniformly in which primes of the tail are taken (`Gap212.Sieve.PrimeTailProduct`). The reciprocal
kernel needs none of this: its fixed-`W` statement is already the joint one. -/
theorem tendsto_tprod_corr_W :
    Tendsto (fun x : ℝ ↦
        ∏' p : ℕ, if p.Prime ∧ ¬ p ∣ W x then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)
      atTop (nhds 1) := by
  refine Metric.tendsto_nhds.2 fun η hη ↦ ?_
  obtain ⟨z, -, hthr⟩ := exists_threshold_prod_one_sub_ge (ε := η / 2) (by linarith)
  filter_upwards [eventually_dvd_W_of_prime_le z] with x hx
  obtain ⟨hlo, hhi⟩ := tprod_corr_mem_of_primes_dvd hthr hx
  exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩

/-- **The inverse correction factor tends to `1`.** The form the weight of
`Gap212.Sieve.TotientMuPhiWeightedGramLimit` needs: its Mertens constant is
`(φ(W)/W)·(∏_{p∤W}(1-1/(p-1)²))^{-1}`, so it is the *inverse* product that has to be driven to `1`
there, against the two direct powers carried by the predicted values of the inner sums. -/
theorem tendsto_inv_tprod_corr_W :
    Tendsto (fun x : ℝ ↦
        (∏' p : ℕ, if p.Prime ∧ ¬ p ∣ W x then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)⁻¹)
      atTop (nhds 1) := by
  simpa using tendsto_tprod_corr_W.inv₀ one_ne_zero

end Gap212.Sieve
