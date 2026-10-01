/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Totient
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.PrimeCounting

/-!
# The vocabulary the formal challenge states

Every definition the challenge file `Gap212Challenge/Basic.lean` writes out, in that file's order
and under the same names, with the same imports. The rest of the library takes these
definitions from here.

## Sources

1. Polymath, *New equidistribution estimates of Zhang type*, https://arxiv.org/abs/1402.0811
2. Julia Stadlmann, *Bounded gaps between primes*, https://arxiv.org/abs/2608.31126
-/

@[expose] public section
namespace Gap212

open Real Finset MeasureTheory Asymptotics Filter

section type_estimates

/-- The constants controlling coefficient growth, support, scale products, smoothness and
Siegel–Walfisz bounds. The scale and product intervals have positive, strictly ordered endpoints;
no positivity conditions are imposed on the other constants. -/
structure ConstantBundle : Type where
  coeffConst : ℝ
  coeffFstPow : ℕ
  coeffSndPow : ℕ
  scaleLo : ℝ
  scaleHi : ℝ
  asympLo : ℝ
  asympHi : ℝ
  smoothConst (j : ℕ) : ℝ
  smoothPow (j : ℕ) : ℕ
  siegelWalfiszConst (B : ℝ) : ℝ
  siegelWalfiszPow (B : ℝ) : ℕ
  scaleLo_pos : 0 < scaleLo := by norm_num
  scaleLo_lt_scaleHi : scaleLo < scaleHi := by norm_num
  asympLo_pos : 0 < asympLo := by norm_num
  asympLo_lt_asympHi : asympLo < asympHi := by norm_num

/-- The pointwise comparison `K.asympLo * y ≤ x ≤ K.asympHi * y`. -/
def ConstantBundle.asympEq (K : ConstantBundle) (x y : ℝ) : Prop :=
  K.asympLo * y ≤ x ∧ x ≤ K.asympHi * y

/-! ## Coefficient sequences

[1, Definition 2.5] and [2, Definition 6], expressed at a single scale. Coefficients have type
`ℕ → ℂ`, and scales are real numbers, not functions of `x`. The estimates quantify over the
coefficients and scales after choosing their constants, so the data may vary with `x` without
changing those constants. Every analytic estimate below is stated for `x ≥ 3`. -/

/-- The coefficient bound of [1, Definition 2.5]. The sequence has no scale argument and the
bound uses `1 + log n`, not `log x`; the constants `C`, `k`, `l` are independent of `n`. It is
required only for `n ≥ 1`, so `α 0` is unrestricted, and finite support is not part of it. -/
def IsCoefficientSequence (C : ℝ) (k l : ℕ) (α : ℕ → ℂ) : Prop :=
  ∀ n ≥ (1 : ℕ), ‖α n‖ ≤ C * (n.divisors.card : ℝ) ^ k * (1 + log n) ^ l

/-- The coefficient bound with constants supplied by `K`. -/
def ConstantBundle.IsCoefficientSequence (K : ConstantBundle) (α : ℕ → ℂ) : Prop :=
  Gap212.IsCoefficientSequence K.coeffConst K.coeffFstPow K.coeffSndPow α

/-- The support condition of [1, Definition 2.5 (i)] and [2, Definition 6 (i)], at one scale:
every nonzero term with `n ≥ 1` lies in `[c₀ * N, c₁ * N]`. The value at `0` is unrestricted. -/
def LocatedAtScale (c₀ c₁ : ℝ) (α : ℕ → ℂ) (N : ℝ) : Prop :=
  ∀ n ≥ (1 : ℕ), α n ≠ 0 → c₀ * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ c₁ * N

/-- The support condition with endpoints supplied by `K`. -/
def ConstantBundle.LocatedAtScale (K : ConstantBundle) (α : ℕ → ℂ) (N : ℝ) : Prop :=
  Gap212.LocatedAtScale K.scaleLo K.scaleHi α N

/-- Smooth coefficients, following [1, Definition 2.5 (iii)] and [2, Definition 6 (iii)].
There is a smooth complex-valued `ψ` supported in `[c, C]` with `α n = ψ (n / N)` for every
`n`, including `0`. Its `j`-th derivative is bounded by `b j * (log N) ^ m j` at every real
point. The logarithm here is exactly `log N`, not `log x` or `1 + log N`. -/
def IsSmoothAtScale (c C : ℝ) (b : ℕ → ℝ) (m : ℕ → ℕ) (α : ℕ → ℂ) (N : ℝ) : Prop :=
  ∃ ψ : ℝ → ℂ, open scoped ContDiff in ContDiff ℝ (∞ : ℕ∞ω) ψ ∧
  (∀ t : ℝ, ψ t ≠ 0 → t ∈ Set.Icc c C) ∧
  (∀ (j : ℕ) (t : ℝ), ‖iteratedDeriv j ψ t‖ ≤ b j * (log N) ^ m j) ∧
  ∀ n : ℕ, α n = ψ ((n : ℝ) / N)

/-- Smoothness with support endpoints and derivative bounds supplied by `K`. -/
def ConstantBundle.IsSmoothAtScale (K : ConstantBundle) (α : ℕ → ℂ) (N : ℝ) : Prop :=
  Gap212.IsSmoothAtScale K.scaleLo K.scaleHi K.smoothConst K.smoothPow α N

/-- [2, below Definition 6]: the Dirichlet convolution in the arithmetic variable. -/
def dconv (α β : ℕ → ℂ) : ℕ → ℂ :=
  fun n ↦ ∑ d ∈ n.divisors, α d * β (n / d)

/-- The natural numbers between `⌈x⌉₊` and `⌊2 * x⌋₊`; for `x ≥ 3`, precisely the natural
numbers of `[x, 2x]` used in the discrepancy. -/
noncomputable def dyadic (x : ℝ) : Finset ℕ := Finset.Icc ⌈x⌉₊ ⌊2 * x⌋₊

/-- `a` is coprime to every prime up to `x`; the `(a, p) = 1` for all primes `p ≤ x` of
[2, Definition 3], written `(a, P(x)) = 1` in [2, Notation] and `a (P_I)` primitive in
[1, Definition 2.2]. -/
def CoprimeBelow (a : ℕ) (x : ℝ) : Prop := ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime a p

/-- The Siegel–Walfisz bound, following [1, Definition 2.5 (ii)] and [2, Definition 6 (ii)].
For every `B > 0`, positive `q, r` and natural `a` coprime to `q`, the discrepancy with the
additional condition `Coprime n r` is at most `S B * τ(qr)^(E B) * N / (1 + log N)^B`.
These are unrestricted `finsum`s in `n`, not dyadic sums; located sequences have finite support.
The value at `0`, when admitted by the coprimality and congruence conditions, is included. -/
def HasSiegelWalfisz (S : ℝ → ℝ) (E : ℝ → ℕ) (α : ℕ → ℂ) (N : ℝ) : Prop :=
  ∀ B > (0 : ℝ), ∀ q ≥ (1 : ℕ), ∀ r ≥ (1 : ℕ), ∀ a : ℕ, Nat.Coprime a q →
    ‖(∑ᶠ n ∈ {n : ℕ | n ≡ a [MOD q] ∧ Nat.Coprime n r}, α n) -
      (1 / (Nat.totient q : ℂ)) * ∑ᶠ n ∈ {n : ℕ | Nat.Coprime n (q * r)}, α n‖ ≤
    S B * ((q * r).divisors.card : ℝ) ^ E B * N / (1 + log N) ^ B

/-- The Siegel–Walfisz bound with both functions of `B` supplied by `K`. -/
def ConstantBundle.HasSiegelWalfisz (K : ConstantBundle) (α : ℕ → ℂ) (N : ℝ) : Prop :=
  Gap212.HasSiegelWalfisz K.siegelWalfiszConst K.siegelWalfiszPow α N

/-- The dyadic discrepancy: the sum in the class `a mod d`, minus the coprime sum divided by
`φ(d)`. The definition itself imposes no coprimality hypothesis on `a`. -/
noncomputable def sumErrorDyadic (x : ℝ) (f : ℕ → ℂ) (d a : ℕ) : ℂ :=
  ∑ n ∈ dyadic x with n ≡ a [MOD d], f n -
  (1 / (Nat.totient d : ℂ)) * ∑ n ∈ dyadic x with Nat.Coprime n d, f n

/-- The unrestricted discrepancy of [1, (1.1)]: the sum in the class `a mod d`, minus the
coprime sum divided by `φ(d)`. Applied to finitely supported sequences, as in bilinear
Bombieri–Vinogradov; the support of the sequence supplies the summation range. -/
noncomputable def sumError (f : ℕ → ℂ) (d a : ℕ) : ℂ :=
  (∑ᶠ n ∈ {n : ℕ | n ≡ a [MOD d]}, f n) -
  (1 / (Nat.totient d : ℂ)) * ∑ᶠ n ∈ {n : ℕ | Nat.Coprime n d}, f n

/-- The sum of unrestricted discrepancy norms, using [1, (1.1)], over the squarefree members
of `D` is at most `C * x / (log x)^A`. The support of the sequence supplies the summation range.
All parameters are explicit; their quantifiers belong to the estimates. -/
def HasEquidistribution (x : ℝ) (D : Finset ℕ) (f : ℕ → ℂ) (a : ℕ) (A C : ℝ) : Prop :=
  ∑ d ∈ D with Squarefree d, ‖sumError f d a‖ ≤ C * x / (log x) ^ A

/-! ## The five sets of moduli

The five finite modulus families used in the analytic assumptions, following [2, Lemmas 3–7].
Each lies in `[1, x^{1/2+2ω}]`; additional divisor conditions are recorded below. -/

/-- The ambient range `[1, x^{1/2+2ω}] ∩ ℕ` shared by all five modulus sets of
[2, Lemmas 3–7]. -/
noncomputable def moduliRange (x ω : ℝ) : Finset ℕ := Finset.Icc 1 ⌊x ^ (1 / 2 + 2 * ω)⌋₊

open Classical in
/-- `D_{IIa}` of [2, Lemma 3]: a divisor `r ∣ d` with
`N * x^(-δ-3ε) < r < N * x^(-3ε)`. -/
noncomputable def moduliIIa (x ω N δ ε : ℝ) : Finset ℕ :=
  {d ∈ moduliRange x ω | ∃ r : ℕ, r ∣ d ∧ N * x ^ (- δ - 3 * ε) < r ∧ r < N * x ^ (-3 * ε)}

open Classical in
/-- `D_{IIb}` of [2, Lemma 4]: divisors `r ∣ d` and `u ∣ d/r` with
`N * x^(-3ε-δ) < r < N * x^(-3ε)` and
`N⁻¹ * x^(1/2-2ω-6ε-δ) < u < N⁻¹ * x^(1/2-2ω-6ε)`. -/
noncomputable def moduliIIb (x ω N δ ε : ℝ) : Finset ℕ :=
  {d ∈ moduliRange x ω | ∃ r u : ℕ, r ∣ d ∧ u ∣ d / r ∧
    N * x ^ (- 3 * ε - δ) < (r : ℝ) ∧ (r : ℝ) < N * x ^ (- 3 * ε) ∧
    N⁻¹ * x ^ (1 / 2 - 2 * ω - 6 * ε - δ) < u ∧ u < N⁻¹ * x ^ (1 / 2 - 2 * ω - 6 * ε)}

open Classical in
/-- `D_I` of [2, Lemma 5], piecewise in `N`: the divisor window is
`(N * x^(-δ-3ε), N * x^(-3ε))` when `N ≤ √x`, and
`(N⁻¹ * x^(1-δ-3ε), N⁻¹ * x^(1-3ε))` when `√x < N ≤ x^(1/2+2ω+ε)`.
Above that range there is no condition beyond membership in `moduliRange`. -/
noncomputable def moduliI (x ω N δ ε : ℝ) : Finset ℕ :=
  if N ≤ √x then
    {d ∈ moduliRange x ω | ∃ r : ℕ, r ∣ d ∧ N * x ^ (- δ - 3 * ε) < r ∧ r < N * x ^ (- 3 * ε)}
  else if N ≤ x ^ (1 / 2 + 2 * ω + ε) then
    {d ∈ moduliRange x ω |
      ∃ r : ℕ, r ∣ d ∧ N⁻¹ * x ^ (1 - δ - 3 * ε) < r ∧ r < N⁻¹ * x ^ (1 - 3 * ε)}
  else
    moduliRange x ω

open Classical in
/-- `D_{IIc}` of [2, Lemma 6]: divisors `r ∣ d`, `u ∣ d/r` and `d₁ ∣ r` with
`N * x^(-3ε-δ) < r < N * x^(-3ε)`,
`N⁻¹ * x^(1-6ε-δ) / d < u < N⁻¹ * x^(1-6ε) / d`, and
`r² * N⁻¹ * x^(2-52ε-δ) / d⁴ < d₁ < r² * N⁻¹ * x^(2-52ε) / d⁴`. -/
noncomputable def moduliIIc (x ω N δ ε : ℝ) : Finset ℕ :=
  {d ∈ moduliRange x ω | ∃ r u d₁ : ℕ, r ∣ d ∧ u ∣ d / r ∧ d₁ ∣ r ∧
    N * x ^ (- 3 * ε - δ) < (r : ℝ) ∧ (r : ℝ) < N * x ^ (- 3 * ε) ∧
    N⁻¹ * x ^ (1 - 6 * ε - δ) / (d : ℝ) < (u : ℝ) ∧ (u : ℝ) < N⁻¹ * x ^ (1 - 6 * ε) / (d : ℝ) ∧
    (r : ℝ) ^ 2 * N⁻¹ * x ^ (2 - 52 * ε - δ) / (d : ℝ) ^ 4 < (d₁ : ℝ) ∧
      (d₁ : ℝ) < (r : ℝ) ^ 2 * N⁻¹ * x ^ (2 - 52 * ε) / (d : ℝ) ^ 4}

open Classical in
/-- `D_{III}` of [2, Lemma 7]: a divisor `r` with
`x^{1/3+4δ/3-4ω/3-δ} < r < x^{1/3+4δ/3-4ω/3}`. Its only parameters are `x`, `ω` and `δ`. -/
noncomputable def moduliIII (x ω δ : ℝ) : Finset ℕ :=
  {d ∈ moduliRange x ω | ∃ r : ℕ, r ∣ d ∧
    x ^ (1 / 3 + 4 * δ / 3 - 4 * ω / 3 - δ) < r ∧ r < x ^ (1 / 3 + 4 * δ / 3 - 4 * ω / 3)}

/-! ## The five analytic estimates

The assumptions corresponding to [2, Lemmas 3–7], with explicit constants and quantifiers.
In the four bilinear estimates, `γ` in the descriptions abbreviates `log N / log x`; it is not
a parameter or a function. The fixed bounds `γ₁, γ₂` require `x^γ₁ ≤ N ≤ x^γ₂`.

The positive `θ` is the uniform slack in the inequalities, distinct from the divisor-window
width `δ` and the analytic loss `ε`. The threshold `ε₀` is chosen before `ε` and `A`; then
`C : ℝ` is chosen before `δ`, `x`, the sequences, the scales and the residue class. Thus the
bilinear estimates are uniform over those data. Type III instead fixes `κ` and `δ` before
choosing the threshold and constant. In every estimate `x ≥ 3`, all scales are at least `1`,
and the residue class satisfies `CoprimeBelow a x`. No positivity hypothesis on `C` is imposed. -/

/-- **Polymath Type II**, corresponding to [2, Lemma 3] and [1, Theorem 2.8(iv)]. Both factors
are coefficient sequences at scales `M, N`, with `K.asympEq (M * N) x` and SW on `β`.
Here `0 < γ₁ ≤ γ₂ ≤ 1/2`, `24ω + 7δ - 5γ + θ ≤ -2` and `8ω + 3δ - γ + θ ≤ 0`.
The conclusion is equidistribution over `moduliIIa`. -/
def TypeIIPolymath : Prop :=
  ∀ K : ConstantBundle, ∀ ω ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ θ > (0 : ℝ),
  ∀ γ₁ γ₂ : ℝ, 0 < γ₁ → γ₁ ≤ γ₂ → γ₂ ≤ 1 / 2 →
  ∃ ε₀ > (0 : ℝ), ∀ ε ∈ Set.Ioo 0 ε₀, ∀ A > (0 : ℝ), ∃ C : ℝ,
  ∀ δ > (0 : ℝ), ∀ x ≥ (3 : ℝ), ∀ α β : ℕ → ℂ, ∀ M ≥ (1 : ℝ), ∀ N ≥ (1 : ℝ), ∀ a : ℕ,
  K.IsCoefficientSequence α → K.IsCoefficientSequence β →
  K.LocatedAtScale α M → K.LocatedAtScale β N →
  K.asympEq (M * N) x → K.HasSiegelWalfisz β N →
  x ^ γ₁ ≤ N → N ≤ x ^ γ₂ →
  24 * ω + 7 * δ - 5 * (log N / log x) + θ ≤ -2 →
  8 * ω + 3 * δ - (log N / log x) + θ ≤ 0 →
  CoprimeBelow a x →
  HasEquidistribution x (moduliIIa x ω N δ ε) (dconv α β) a A C

/-- **[2, Lemma 4] (Polymath Type I(ii))**, a variant of [1, Theorem 2.8(ii)]. The coefficient,
scale and SW hypotheses are as in `TypeIIPolymath`, with `0 < γ₁ ≤ γ₂ ≤ 1/2`.
The inequalities are `24ω + 7δ - 3γ + θ ≤ -1` and `8ω + 3δ - γ + θ ≤ 0`, and the conclusion
is equidistribution over `moduliIIb`. -/
def TypeIbPolymath : Prop :=
  ∀ K : ConstantBundle, ∀ ω ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ θ > (0 : ℝ),
  ∀ γ₁ γ₂ : ℝ, 0 < γ₁ → γ₁ ≤ γ₂ → γ₂ ≤ 1 / 2 →
  ∃ ε₀ > (0 : ℝ), ∀ ε ∈ Set.Ioo 0 ε₀, ∀ A > (0 : ℝ), ∃ C : ℝ,
  ∀ δ > (0 : ℝ), ∀ x ≥ (3 : ℝ), ∀ α β : ℕ → ℂ, ∀ M ≥ (1 : ℝ), ∀ N ≥ (1 : ℝ), ∀ a : ℕ,
  K.IsCoefficientSequence α → K.IsCoefficientSequence β →
  K.LocatedAtScale α M → K.LocatedAtScale β N →
  K.asympEq (M * N) x → K.HasSiegelWalfisz β N →
  x ^ γ₁ ≤ N → N ≤ x ^ γ₂ →
  24 * ω + 7 * δ - 3 * (log N / log x) + θ ≤ -1 →
  8 * ω + 3 * δ - (log N / log x) + θ ≤ 0 →
  CoprimeBelow a x →
  HasEquidistribution x (moduliIIb x ω N δ ε) (dconv α β) a A C

/-- **[2, Lemma 5] (Baker–Irving Type I)**. Both factors are located coefficient sequences,
`K.asympEq (M * N) x` holds, and `β` is smooth; no SW hypothesis is imposed on either, and
`0 < γ₁ ≤ γ₂` with no upper restriction on `γ₂`. When `N ≤ √x`, require `3γ - 12ω - 3δ ≥ 1 + θ`;
when `√x < N ≤ x^(1/2+2ω+ε)`, require `68ω + 14δ ≤ 1 - θ`; above that range neither is
required. The conclusion uses the corresponding branch of `moduliI`. -/
def TypeIBakerIrving : Prop :=
  ∀ K : ConstantBundle, ∀ ω ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ θ > (0 : ℝ),
  ∀ γ₁ γ₂ : ℝ, 0 < γ₁ → γ₁ ≤ γ₂ →
  ∃ ε₀ > (0 : ℝ), ∀ ε ∈ Set.Ioo 0 ε₀, ∀ A > (0 : ℝ), ∃ C : ℝ,
  ∀ δ > (0 : ℝ), ∀ x ≥ (3 : ℝ), ∀ α β : ℕ → ℂ, ∀ M ≥ (1 : ℝ), ∀ N ≥ (1 : ℝ), ∀ a : ℕ,
  K.IsCoefficientSequence α → K.IsCoefficientSequence β →
  K.LocatedAtScale α M → K.LocatedAtScale β N →
  K.asympEq (M * N) x → K.IsSmoothAtScale β N →
  x ^ γ₁ ≤ N → N ≤ x ^ γ₂ →
  (N ≤ √x → 3 * (log N / log x) - 12 * ω - 3 * δ ≥ 1 + θ) →
  (√x < N → N ≤ x ^ (1 / 2 + 2 * ω + ε) → 68 * ω + 14 * δ ≤ 1 - θ) →
  CoprimeBelow a x →
  HasEquidistribution x (moduliI x ω N δ ε) (dconv α β) a A C

/-- **Stadlmann Type I**, corresponding to [2, Lemma 6]. The coefficient, scale and SW
hypotheses are as in `TypeIIPolymath`, with `0 < γ₁ ≤ γ₂ ≤ 1/2`. The inequalities here are
`8ω + 4δ + 2γ + θ ≤ 1`, `32ω + 10δ - γ + θ ≤ 0` and `48ω + 16δ - 4γ + θ ≤ -1`.
The conclusion is equidistribution over `moduliIIc`. -/
def TypeIStadlmann : Prop :=
  ∀ K : ConstantBundle, ∀ ω ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ θ > (0 : ℝ),
  ∀ γ₁ γ₂ : ℝ, 0 < γ₁ → γ₁ ≤ γ₂ → γ₂ ≤ 1 / 2 →
  ∃ ε₀ > (0 : ℝ), ∀ ε ∈ Set.Ioo 0 ε₀, ∀ A > (0 : ℝ), ∃ C : ℝ,
  ∀ δ > (0 : ℝ), ∀ x ≥ (3 : ℝ), ∀ α β : ℕ → ℂ, ∀ M ≥ (1 : ℝ), ∀ N ≥ (1 : ℝ), ∀ a : ℕ,
  K.IsCoefficientSequence α → K.IsCoefficientSequence β →
  K.LocatedAtScale α M → K.LocatedAtScale β N →
  K.asympEq (M * N) x → K.HasSiegelWalfisz β N →
  x ^ γ₁ ≤ N → N ≤ x ^ γ₂ →
  8 * ω + 4 * δ + 2 * (log N / log x) + θ ≤ 1 →
  32 * ω + 10 * δ - (log N / log x) + θ ≤ 0 →
  48 * ω + 16 * δ - 4 * (log N / log x) + θ ≤ -1 →
  CoprimeBelow a x →
  HasEquidistribution x (moduliIIc x ω N δ ε) (dconv α β) a A C

/-- **[2, Lemma 7] (Polymath Type III)**, following [1, Theorem 2.8(v)]. All four factors are
coefficient sequences controlled by `K`; `α` is located at `M`, each `ψᵢ` is smooth at `Nᵢ`, and
their scale product is comparable to `x`. The parameters satisfy `0 < ω < 1/12`, `0 < κ < 1/2`,
`0 < δ < 1/4 + ω`, `θ > 0`, with `K.asympLo * x^(1-κ) ≤ Nᵢ Nⱼ` for distinct indices,
`K.asympLo * x^(1-2κ) ≤ Nᵢ ≤ K.asympHi * x^κ` and `28ω + 9κ + 8δ + θ ≤ 4`. The conclusion uses
the left-associated convolution and `moduliIII x ω δ`. -/
def TypeIIIPolymath : Prop :=
  ∀ K : ConstantBundle,
  ∀ ω ∈ Set.Ioo (0 : ℝ) (1 / 12), ∀ κ ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ δ ∈ Set.Ioo 0 (1 / 4 + ω),
  ∀ θ > (0 : ℝ),
  ∃ ε₀ > (0 : ℝ), ∀ ε ∈ Set.Ioo 0 ε₀, ∀ A > (0 : ℝ), ∃ C : ℝ,
  ∀ x ≥ (3 : ℝ), ∀ α ψ₁ ψ₂ ψ₃ : ℕ → ℂ,
  ∀ M ≥ (1 : ℝ), ∀ N₁ ≥ (1 : ℝ), ∀ N₂ ≥ (1 : ℝ), ∀ N₃ ≥ (1 : ℝ), ∀ a : ℕ,
  K.IsCoefficientSequence α →
  K.IsCoefficientSequence ψ₁ → K.IsCoefficientSequence ψ₂ → K.IsCoefficientSequence ψ₃ →
  K.LocatedAtScale α M →
  K.IsSmoothAtScale ψ₁ N₁ → K.IsSmoothAtScale ψ₂ N₂ → K.IsSmoothAtScale ψ₃ N₃ →
  K.asympEq (M * N₁ * N₂ * N₃) x →
  K.asympLo * x ^ (1 - κ) ≤ N₁ * N₂ →
  K.asympLo * x ^ (1 - κ) ≤ N₁ * N₃ →
  K.asympLo * x ^ (1 - κ) ≤ N₂ * N₃ →
  K.asympLo * x ^ (1 - 2 * κ) ≤ N₁ → N₁ ≤ K.asympHi * x ^ κ →
  K.asympLo * x ^ (1 - 2 * κ) ≤ N₂ → N₂ ≤ K.asympHi * x ^ κ →
  K.asympLo * x ^ (1 - 2 * κ) ≤ N₃ → N₃ ≤ K.asympHi * x ^ κ →
  28 * ω + 9 * κ + 8 * δ + θ ≤ 4 →
  CoprimeBelow a x →
  HasEquidistribution x (moduliIII x ω δ) (dconv (dconv (dconv α ψ₁) ψ₂) ψ₃) a A C

end type_estimates

section support

/-! ## The support and the key integrals

[2, Definitions 1 and 5]. -/

/-- The parameters of [2, Definition 1]: a threshold `δ`, an enlargement `ε`, and `n` strata cut
by `-ε = A₀ < ⋯ < Aₙ < 1/2 - ε`, with a cap function `B : Fin n → ℕ → ℝ` satisfying `B_{j,0} = 0`
and `δ < B_{j,m} ≤ B_{j,m+1} ≤ B_{j,m} + δ` for `m ≥ 1`. The chain is guarded by `1 ≤ m` because
the source's "for any `m ≥ 1`" excludes `m = 0`: `B_{j,1} ≤ B_{j,0} + δ = δ` would contradict
`δ < B_{j,1}`. -/
structure SupportParams where
  δ : ℝ
  ε : ℝ
  n : ℕ
  A : Fin (n + 1) → ℝ
  B : Fin n → ℕ → ℝ
  δ_pos : 0 < δ
  ε_pos : 0 < ε
  n_pos : 0 < n
  A_zero : A 0 = -ε
  A_mono : StrictMono A
  A_last : A (Fin.last n) < 1 / 2 - ε
  B_zero : ∀ j : Fin n, B j 0 = 0
  B_lt : ∀ (j : Fin n) (m : ℕ), 1 ≤ m → δ < B j m
  B_mono : ∀ (j : Fin n) (m : ℕ), 1 ≤ m → B j m ≤ B j (m + 1)
  B_step : ∀ (j : Fin n) (m : ℕ), 1 ≤ m → B j (m + 1) ≤ B j m + δ

namespace SupportParams

variable (p : SupportParams)

open Classical in
/-- The set `I = {i : tᵢ > δ}` of large coordinates, of [2, Definition 1]. -/
noncomputable def large (k : ℕ) (t : Fin k → ℝ) : Finset (Fin k) :=
  {i ∈ Finset.univ | p.δ < t i}

open Classical in
/-- The stratum indexed by `j : Fin p.n`: every coordinate lies in `[0, 1]`, the total lies in
`[p.A j.castSucc + ε, p.A j.succ + ε)`, and the large coordinates sum to at most `p.B j |I|`.
The `A` indices are zero-based; `j.succ` is the upper endpoint of this stratum. -/
noncomputable def stratum (k : ℕ) (j : Fin p.n) : Set (Fin k → ℝ) :=
  {t | (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) ∧
    (∑ i, t i) ∈ Set.Ico (p.A j.castSucc + p.ε) (p.A j.succ + p.ε) ∧
    ∑ i ∈ p.large k t, t i ≤ p.B j (p.large k t).card}

end SupportParams

/-- The support `T_k(δ, A, B, ε)` of [2, Definition 1]: the union of the strata. -/
noncomputable def T (p : SupportParams) (k : ℕ) : Set (Fin k → ℝ) :=
  ⋃ j : Fin p.n, p.stratum k j

variable (p : SupportParams)

/-- `I(F) = ∫_{T_k} F(t)² dt`, of [2, Definition 5]. -/
noncomputable def Iint (k : ℕ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ t in T p k, F t ^ 2

/-- The region of the `(j, j')` summand of `J`, following [2, Definition 5]. The common `m`
coordinates sum to at most `max(p.A j.succ - ε, p.A j'.succ - ε)`. Adjoining the two last
coordinates separately lands in the corresponding closed total-mass windows. Unlike the strata,
these windows include both endpoints. No coordinate bounds are imposed by this region itself. -/
def Jregion (m : ℕ) (j j' : Fin p.n) : Set ((Fin m → ℝ) × ℝ × ℝ) :=
  {q | (∑ i, q.1 i) ≤ max (p.A j.succ - p.ε) (p.A j'.succ - p.ε) ∧
    (∑ i, q.1 i) + q.2.1 ∈ Set.Icc (p.A j.castSucc + p.ε) (p.A j.succ + p.ε) ∧
    (∑ i, q.1 i) + q.2.2 ∈ Set.Icc (p.A j'.castSucc + p.ε) (p.A j'.succ + p.ε)}

/-- `J(F)` of [2, Definition 5]: the two last coordinates are integrated separately against
`F(t, t_k) · F(t, t'_k)`. -/
noncomputable def Jint (m : ℕ) (F : (Fin (m + 1) → ℝ) → ℝ) : ℝ :=
  ∑ j : Fin p.n, ∑ j' : Fin p.n,
    ∫ q in Jregion p m j j', F (Fin.snoc q.1 q.2.1) * F (Fin.snoc q.1 q.2.2)

/-- The region used for the `(j, j')` summand of `K`. The first `m` coordinates sum to more
than `max(p.A j.succ - ε, p.A j'.succ - ε)`, and the total lies in the closed `j`-th window.

Only `m + 1` coordinates occur here: there is no extra coordinate `t'_k` and no condition on a
second total, unlike the printed region in [2, Definition 5]. -/
def Kregion (m : ℕ) (j j' : Fin p.n) : Set (Fin (m + 1) → ℝ) :=
  {t | max (p.A j.succ - p.ε) (p.A j'.succ - p.ε) < ∑ i, Fin.init t i ∧
    (∑ i, t i) ∈ Set.Icc (p.A j.castSucc + p.ε) (p.A j.succ + p.ε)}

/-- The double sum of integrals of `F²` over `Kregion`, indexed by both strata. -/
noncomputable def Kint (m : ℕ) (F : (Fin (m + 1) → ℝ) → ℝ) : ℝ :=
  ∑ j : Fin p.n, ∑ j' : Fin p.n, ∫ t in Kregion p m j j', F t ^ 2

/-- `F` is symmetric: invariant under permuting its coordinates, as [2, Definition 5] asks. -/
def Symmetric {k : ℕ} (F : (Fin k → ℝ) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin k)) (t : Fin k → ℝ), F (t ∘ σ) = F t

end support

section numerical_certificate

/-! ## The numerical certificate

The certificate is an existential version of inequality (2.1) of [2, Proposition 1]. It asks
for a real-valued symmetric function with the support, integrability and integral bounds below;
it does not require that function to be a polynomial or specify its coefficients. The rational
support data are defined here, while existence of a certificate is a hypothesis of the objectives.
-/

/-- Inequality (2.1) of [2, Proposition 1]: a symmetric, square-integrable `F` supported on
`T_{m+1}` with `0 < I(F) < k(1-c₁) J(F) - k c₂ K(F)`, where `k = m + 1`.
The predicate itself places no sign restrictions on `c₁` and `c₂`. -/
def Certificate (p : SupportParams) (m : ℕ) (c₁ c₂ : ℝ) : Prop :=
  ∃ F : (Fin (m + 1) → ℝ) → ℝ,
    Symmetric F ∧
    MemLp F 2 (volume.restrict (T p (m + 1))) ∧
    (∀ t, t ∉ T p (m + 1) → F t = 0) ∧
    0 < Iint p (m + 1) F ∧
    Iint p (m + 1) F <
      (m + 1 : ℝ) * (1 - c₁) * Jint p m F - (m + 1 : ℝ) * c₂ * Kint p m F

/-- The cap row `B_{1,·}`: `B_{1,0} = 0`, then the ten rungs
`(777, 794, 875, 917, 953, 983, 1016, 1042, 1063, 1081)/5000`, constant at `1081/5000` from
`m = 10` on, which defines the cap at every index including those beyond `10`. It satisfies the
conditions on `B` in [2, Definition 1]. These values are specific to this datum; [2] instead
takes `B_{1,1} = B_{1,2} = 0.15` and `B_{1,m} = 0.17` for `m ≥ 3` at `δ = 0.028`, `ε = 0.0075` and
`k = 49`. -/
noncomputable def gap212Cap (m : ℕ) : ℝ :=
  if m = 0 then 0
  else if m = 1 then 777 / 5000
  else if m = 2 then 794 / 5000
  else if m = 3 then 875 / 5000
  else if m = 4 then 917 / 5000
  else if m = 5 then 953 / 5000
  else if m = 6 then 983 / 5000
  else if m = 7 then 1016 / 5000
  else if m = 8 then 1042 / 5000
  else if m = 9 then 1063 / 5000
  else 1081 / 5000

/-- From index `10` onward the cap row equals `1081/5000`. -/
theorem gap212Cap_of_ten_le {m : ℕ} (hm : 10 ≤ m) : gap212Cap m = 1081 / 5000 := by
  unfold gap212Cap
  split_ifs <;> first | (exfalso; subst_vars; simp at hm) | rfl

/-- The parameter datum, in the physical scale of [2, Definition 1]: one band, with
`δ = 41/2500`, `ε = 1/125`, `(A₀, A₁) = (-1/125, 257/1000)`, and the cap row
`gap212Cap`. The two ends of the total-mass window are `A₀ + ε = 0` and
`A₁ + ε = 53/200`, and the marginal cutoff is `A₁ - ε = 249/1000`.

The numerical values differ from those of [2]; see `gap212Cap`. -/
noncomputable def gap212Params : SupportParams where
  δ := 41 / 2500
  ε := 1 / 125
  n := 1
  A := fun i ↦ (i.val : ℝ) * (53 / 200) - 1 / 125
  B := fun _ ↦ gap212Cap
  δ_pos := by norm_num
  ε_pos := by norm_num
  n_pos := by norm_num
  A_zero := by norm_num
  A_mono := by
    intro i j hij
    have : (i.val : ℝ) < (j.val : ℝ) := Nat.cast_lt.mpr hij
    simp only
    linarith
  A_last := by norm_num [Fin.last]
  B_zero := fun _ ↦ by unfold gap212Cap; norm_num
  B_lt := by
    intro _ m hm
    show (41 / 2500 : ℝ) < gap212Cap m
    unfold gap212Cap
    rw [if_neg (Nat.one_le_iff_ne_zero.mp hm)]
    split_ifs <;> norm_num
  B_mono := by
    intro _ m hm
    show gap212Cap m ≤ gap212Cap (m + 1)
    by_cases h : 10 ≤ m
    · exact le_of_eq ((gap212Cap_of_ten_le h).trans
        (gap212Cap_of_ten_le (h.trans (Nat.le_succ m))).symm)
    · have h' : m < 10 := not_le.mp h
      interval_cases m <;> norm_num [gap212Cap]
  B_step := by
    intro _ m hm
    show gap212Cap (m + 1) ≤ gap212Cap m + 41 / 2500
    by_cases h : 10 ≤ m
    · rw [gap212Cap_of_ten_le h, gap212Cap_of_ten_le (h.trans (Nat.le_succ m))]
      norm_num
    · have h' : m < 10 := not_le.mp h
      interval_cases m <;> norm_num [gap212Cap]

/-- Inequality (2.1) of [2, Proposition 1] at the parameter datum, in dimension `k = 45`, with
`c₁ = c₂ = 0`. Both vanish because at `ξ₂ = 2/5` the prime minorant of [2, Proposition 2]
degenerates to `1_ℙ`: every term of the two exceptional Buchstab sums would need five prime-factor
exponents each exceeding `1 - 2ξ₂ = 1/5`, totalling more than `1`, so both sums are empty.
The dimension `k = 45` is specific to this certificate; [2, Theorem 1] is proved at `k = 49`. -/
def Gap212Certificate : Prop := Certificate gap212Params 44 0 0

end numerical_certificate

section harman

/-! ## The Harman decomposition class, and the reduction of `1_ℙ` to it

[2, Definition 9] and the prime-indicator endpoint of [2, Proposition 2]. The five analytic
assumptions concern specified convolution classes. The reduction transfers a bound uniform over
those classes to the prime indicator; it is carried as a separate hypothesis, not proved here.

Each class below is a predicate at one `x`, with witnesses `α, β, M, N` or their Type III
counterparts. The witnesses have no `x` argument. `HarmanReduction` quantifies over every
`ConstantBundle`, choosing a common constant before `x` and the member of the class.
Its antecedent is not a separate hypothesis of the objectives: it is derived from the analytic
assumptions and the support data. -/

/-- The fixed slack `ϵ = 10⁻¹⁰` of [2, Definition 9]. Distinct from the support enlargement `ε`
of `SupportParams`, the uniform analytic slack `θ`, and the modulus retreat `ε₀` of
[2, Definition 2]. -/
noncomputable def slack : ℝ := 1 / 10 ^ 10

/-- **Type I** of [2, Definition 9], at one `x`, with constants in `K` and no
Siegel–Walfisz hypothesis on `α`, as in `TypeIBakerIrving`. -/
def TypeI (K : ConstantBundle) (x ξ₁ : ℝ) (f : ℕ → ℂ) : Prop :=
  ∃ α β : ℕ → ℂ, ∃ M ≥ (1 : ℝ), ∃ N ≥ (1 : ℝ),
    f = dconv α β ∧
    K.IsCoefficientSequence α ∧ K.IsCoefficientSequence β ∧
    K.LocatedAtScale α M ∧ K.LocatedAtScale β N ∧
    K.asympEq (M * N) x ∧ K.IsSmoothAtScale β N ∧
    x ^ (ξ₁ - slack) ≤ N

/-- **Type II** of [2, Definition 9], at one `x`: `f = α ⋆ β`, with both factors located
coefficient sequences having SW, all controlled by `K`. Require `M, N ≥ 1`,
`K.asympEq (M * N) x`, and `x^(ξ₂-slack) ≤ N ≤ x^(1-ξ₂+slack)`.
SW on both factors allows either factor to play the second role in a bilinear estimate. -/
def TypeII (K : ConstantBundle) (x ξ₂ : ℝ) (f : ℕ → ℂ) : Prop :=
  ∃ α β : ℕ → ℂ, ∃ M ≥ (1 : ℝ), ∃ N ≥ (1 : ℝ),
    f = dconv α β ∧
    K.IsCoefficientSequence α ∧ K.IsCoefficientSequence β ∧
    K.LocatedAtScale α M ∧ K.LocatedAtScale β N ∧
    K.asympEq (M * N) x ∧ K.HasSiegelWalfisz α M ∧ K.HasSiegelWalfisz β N ∧
    x ^ (ξ₂ - slack) ≤ N ∧ N ≤ x ^ (1 - ξ₂ + slack)

/-- **Type III** of [2, Definition 9]: `f = α ⋆ ψ₁ ⋆ ψ₂ ⋆ ψ₃` with three smooth factors at scales
`N₁, N₂, N₃` satisfying `M N₁ N₂ N₃ ≍ x`, `x^{1-2ξ₃-ϵ} ≤ Nᵢ ≤ x^{ξ₃+ϵ}`, and
`Nᵢ Nⱼ ≥ x^{1-ξ₃-ϵ}` for `i ≠ j`, where `ϵ = slack`. All scales are at least `1`, all four
factors satisfy `K.IsCoefficientSequence`, and `α` is located at `M`. The product comparison
uses `K.asympEq`; the individual and pairwise scale bounds have no additional constants.
The convolution is left-associated, as in `TypeIIIPolymath`. -/
def TypeIII (K : ConstantBundle) (x ξ₃ : ℝ) (f : ℕ → ℂ) : Prop :=
  ∃ α ψ₁ ψ₂ ψ₃ : ℕ → ℂ,
    ∃ M ≥ (1 : ℝ), ∃ N₁ ≥ (1 : ℝ), ∃ N₂ ≥ (1 : ℝ), ∃ N₃ ≥ (1 : ℝ),
    f = dconv (dconv (dconv α ψ₁) ψ₂) ψ₃ ∧
    K.IsCoefficientSequence α ∧ K.IsCoefficientSequence ψ₁ ∧
    K.IsCoefficientSequence ψ₂ ∧ K.IsCoefficientSequence ψ₃ ∧
    K.LocatedAtScale α M ∧
    K.IsSmoothAtScale ψ₁ N₁ ∧ K.IsSmoothAtScale ψ₂ N₂ ∧ K.IsSmoothAtScale ψ₃ N₃ ∧
    K.asympEq (M * N₁ * N₂ * N₃) x ∧
    x ^ (1 - 2 * ξ₃ - slack) ≤ N₁ ∧ N₁ ≤ x ^ (ξ₃ + slack) ∧
    x ^ (1 - 2 * ξ₃ - slack) ≤ N₂ ∧ N₂ ≤ x ^ (ξ₃ + slack) ∧
    x ^ (1 - 2 * ξ₃ - slack) ≤ N₃ ∧ N₃ ≤ x ^ (ξ₃ + slack) ∧
    x ^ (1 - ξ₃ - slack) ≤ N₁ * N₂ ∧
    x ^ (1 - ξ₃ - slack) ≤ N₁ * N₃ ∧
    x ^ (1 - ξ₃ - slack) ≤ N₂ * N₃

/-- **`ℋ(ξ₁, ξ₂, ξ₃)`** of [2, Definition 9], at one `x` with one bundle `K`: membership
in at least one of the three convolution classes. -/
def HarmanClass (K : ConstantBundle) (x ξ₁ ξ₂ ξ₃ : ℝ) (f : ℕ → ℂ) : Prop :=
  TypeI K x ξ₁ f ∨ TypeII K x ξ₂ f ∨ TypeIII K x ξ₃ f

/-! ### The moduli a support generates

[2, Definitions 2 and 3], needed to say over *which* moduli the reduction transfers
equidistribution. -/

/-- **[2, Definition 2], the generated moduli.** The set of `q ≤ x` admitting a factorization
`q = e e' ∏ fᵢ ∏ f'ᵢ` with `e e'` `x^δ`-smooth — every prime factor *strictly* below `x^δ`, per
[2, Notation] — every rough factor at least `x^δ`, the rough products capped by the support's `B`
row, and the mixed products capped by its `A` node — asymmetrically, `A_j - ε` against
`A_{j'} + ε`. Strata are indexed by `Fin p.n`, so the `A_j` of [2, Definition 2] is
`p.A j.succ`. -/
def Qgen (p : SupportParams) (x : ℝ) (j j' : Fin p.n) (m m' : ℕ) (ε₀ : ℝ) : Set ℕ :=
  {q | ∃ (e e' : ℕ) (f : Fin m → ℕ) (f' : Fin m' → ℕ),
    q = e * e' * (∏ i, f i) * (∏ i, f' i) ∧ 1 ≤ q ∧ (q : ℝ) ≤ x ∧
    ((∏ i, f i : ℕ) : ℝ) ≤ x ^ ((1 - ε₀) * p.B j m) ∧
    ((∏ i, f' i : ℕ) : ℝ) ≤ x ^ ((1 - ε₀) * p.B j' m') ∧
    ((e * ∏ i, f i : ℕ) : ℝ) ≤ x ^ ((1 - ε₀) * (p.A j.succ - p.ε)) ∧
    ((e' * ∏ i, f' i : ℕ) : ℝ) ≤ x ^ ((1 - ε₀) * (p.A j'.succ + p.ε)) ∧
    (∀ r : ℕ, r.Prime → r ∣ e * e' → (r : ℝ) < x ^ p.δ) ∧
    (∀ i, x ^ p.δ ≤ (f i : ℝ)) ∧ (∀ i, x ^ p.δ ≤ (f' i : ℝ))}

/-- **The moduli corresponding to a support**, the `Q*` of [2, Definition 2]: the union of the
`Qgen` over both stratum indices and both rough-factor counts `0 ≤ m, m' ≤ ⌊1/δ⌋₊`.
The empty rough products are included through the zero counts. -/
def Qstar (p : SupportParams) (x ε₀ : ℝ) : Set ℕ :=
  ⋃ j : Fin p.n, ⋃ j' : Fin p.n,
    ⋃ m ∈ Finset.Iic ⌊1 / p.δ⌋₊, ⋃ m' ∈ Finset.Iic ⌊1 / p.δ⌋₊, Qgen p x j j' m m' ε₀

open Classical in
/-- **[2, Definition 3]**, at one `x`, using the same discrepancy and squarefree restriction
as `HasEquidistribution`. -/
def HasEquidistributionOverQstar (p : SupportParams) (x ε₀ : ℝ) (f : ℕ → ℂ)
    (a : ℕ) (A C : ℝ) : Prop :=
  HasEquidistribution x {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀} f a A C

/-- The complex-valued prime indicator: `1` at prime natural numbers and `0` elsewhere. -/
def primeIndicator : ℕ → ℂ := fun n ↦ if n.Prime then 1 else 0

/-- The prime indicator on `[x, 2x]` used in the discrepancy of [2, Definition 3].
Restriction to `dyadic x` gives a finitely supported sequence, so its unrestricted discrepancy
is the dyadic prime discrepancy in the conclusion of `HarmanReduction`. -/
noncomputable def primeInterval (x : ℝ) (n : ℕ) : ℂ :=
  if n ∈ dyadic x then primeIndicator n else 0

/-- **The prime-indicator endpoint of [2, Proposition 2].** The antecedent is uniform over
the single-scale class for each `K`, with `C` chosen before `x`, `f` and `a`. The conclusion uses
the finite sequence `primeInterval x` and has its own `C`, chosen after `ε₀ > 0` and `A > 0` and
before `x ≥ 3` and `a`. -/
def HarmanReduction (p : SupportParams) (ξ₁ ξ₂ ξ₃ : ℝ) : Prop :=
  (∀ K : ConstantBundle, ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ,
    ∀ x ≥ (3 : ℝ), ∀ f : ℕ → ℂ, ∀ a : ℕ,
    HarmanClass K x ξ₁ ξ₂ ξ₃ f → CoprimeBelow a x →
    HasEquidistributionOverQstar p x ε₀ f a A C) →
  ∀ ε₀ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ C : ℝ,
  ∀ x ≥ (3 : ℝ), ∀ a : ℕ, CoprimeBelow a x →
  HasEquidistributionOverQstar p x ε₀ (primeInterval x) a A C

/-- [2, Proposition 2] at the chosen parameters: the support of `gap212Params`, and the
Harman parameters `(ξ₁, ξ₂, ξ₃) = (19/50, 2/5, 2/5)`. These satisfy the five scalar inequalities
[2, Proposition 2] requires: `2ξ₁ + 3ξ₂ = 49/25 < 2`, `ξ₂ ≤ ξ₃`, `ξ₁ + 9ξ₂ = 199/50 < 4`,
`2ξ₁ + ξ₂ = 29/25 > 1`, and `17ξ₂ = 34/5 < 7`. These are the exact rational forms of
`(0.38, 0.4, 0.4)`; the support datum is the one defined in this file. -/
def Gap212HarmanReduction : Prop :=
  HarmanReduction gap212Params (19 / 50) (2 / 5) (2 / 5)

end harman

section bilinear_bv

/-! ## Bilinear Bombieri–Vinogradov

The second external reduction input, alongside Harman: the bilinear form of Bombieri–Vinogradov,
following [1, Theorem 2.9], with the unrestricted discrepancy. It concerns convolutions,
not just the von Mangoldt function, and covers all positive moduli up to
`x^(1/2) / (log x)^B`. No modulus-range decomposition or coverage of the remaining moduli is
proved by this declaration. It is carried as a hypothesis of the objectives. -/

/-- **Bilinear Bombieri–Vinogradov, [1, Theorem 2.9], with unrestricted discrepancy.**
Both factor scales must be at least `x^ξ`, and at least one factor must have Siegel–Walfisz.
The bound is uniform over the coefficients and scales controlled by `K`. All positive moduli
up to the cutoff are included, with the maximum over primitive residue classes — a finite
supremum over `a < q` with `Coprime a q` — inside the sum. There is no squarefree filter and no
`CoprimeBelow` hypothesis. -/
def BilinearBombieriVinogradov : Prop :=
  ∀ K : ConstantBundle, ∀ ξ > (0 : ℝ), ∀ A > (0 : ℝ), ∃ B > (0 : ℝ), ∃ C : ℝ,
  ∀ x ≥ (3 : ℝ), ∀ α β : ℕ → ℂ, ∀ M ≥ (1 : ℝ), ∀ N ≥ (1 : ℝ),
  K.IsCoefficientSequence α → K.IsCoefficientSequence β →
  K.LocatedAtScale α M → K.LocatedAtScale β N → K.asympEq (M * N) x →
  x ^ ξ ≤ M → x ^ ξ ≤ N →
  (K.HasSiegelWalfisz α M ∨ K.HasSiegelWalfisz β N) →
  ∑ q ∈ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / (log x) ^ B⌋₊,
    (({a ∈ Finset.range q | Nat.Coprime a q}.sup
      fun a ↦ ‖sumError (dconv α β) q a‖₊ : NNReal) : ℝ) ≤ C * x / (log x) ^ A

end bilinear_bv

end Gap212
