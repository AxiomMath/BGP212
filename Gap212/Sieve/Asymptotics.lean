/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Criterion
public import Gap212.Sieve.EndgameDefs
public import Gap212.Sieve.GPYDefs
public meta import Gap212.Attr

/-!
# The analytic inputs of the GPY sieve

The statements into which the proof of `Gap212.Sieve.GPYSieve` (§3 of Stadlmann's paper)
decomposes: tensor density, the sieve asymptotic, the denominator asymptotic, the numerator lower
bound and the realization of the variational inequality by sieve weights.

* `Gap212.Sieve.TensorDensity`: smooth compactly supported functions are approximated, in a
  controlling seminorm, by finite sums of products of short-support factors. Proved as
  `Gap212.Sieve.exists_tensor_partition_approx`, in a form with nonnegative coefficients and
  factors and with sup-norm closeness.
* `Gap212.Sieve.SieveAsymptotic`: the evaluation of the weighted count of `ρ(n + h_{i₀})` for one
  pair of profile families, over a pre-sieved residue class. Proved at `m = 44` from the divisor
  sum over `Q⋆` by `Gap212.Sieve.sieveAsymptotic_of_obligations`.
* `Gap212.Sieve.NuDenominator`: the denominator `∑ ν(n)` is `(𝓘 + o(1))` times the scale, for the
  tensor sieve weight of a tensor datum. Proved at `45` as `Gap212.Sieve.nuDenominator_45`.
* `Gap212.Sieve.NumeratorAsymptotic`: the numerator `∑ᵢ ∑ ν(n) ρ(n + hᵢ)` is at least
  `(∑𝓙ᵢ - o(1))` times the scale. Proved at `44` as `Gap212.Sieve.numeratorAsymptotic_44`, and
  derived from `SieveAsymptotic` by `Gap212.Sieve.numeratorAsymptotic_of_sieveAsymptotic`.
* `Gap212.Sieve.SieveWeights`: the continuum inequality is realized by finite tensor data with the
  same strict discrete inequality. Proved as `Gap212.Sieve.sieveWeights`.

From these, `Gap212.Sieve.gpySieve_of_obligations` gives `GPYSieve`.

The module also states the unrestricted forms `Gap212.Sieve.SieveAsymptoticUnrestricted`,
`Gap212.Sieve.NuDenominatorUnrestricted` and `Gap212.Sieve.NumeratorAsymptoticUnrestricted`, in
which the residue class or the profiles are not restricted; the first two are false
(`Gap212.Sieve.not_sieveAsymptotic_one`, `Gap212.Sieve.not_nuDenominatorUnrestricted`).

## The scale

Both asymptotics are against `𝓒ₓ = x W^{k-1} / (φ(W)^k (log x)^k)`. Only its positivity,
`Gap212.Sieve.scale_pos`, is used: the sieve compares numerator with denominator, so the scale
divides out.

## The controlling seminorm

The density statement is made in the Sobolev norm controlling `∂_{t_1}⋯∂_{t_k}` and each
`∏_{s≠i} ∂_{t_s}(·,0)`. `Gap212.Sieve.ControllingSeminorm` records the two properties of it that
are used — it is a seminorm, and it dominates the two functionals — and the density statement is
made relative to any such seminorm.

## Main definitions

* `Gap212.Sieve.scale`, `Gap212.Sieve.ControllingSeminorm`.
* `Gap212.Sieve.gramInner`, `Gap212.Sieve.gramInnerSkip`, `Gap212.Sieve.gramBdry`: the Gram data
  of a tensor datum.
* `Gap212.Sieve.TensorDensity`, `Gap212.Sieve.SieveAsymptotic`, `Gap212.Sieve.NuDenominator`,
  `Gap212.Sieve.NumeratorAsymptotic`, `Gap212.Sieve.SieveWeights`.

## Main results

* `Gap212.Sieve.scale_pos`: the scale is positive.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset Real Gap212.Defs Gap212.GPY

/-! ## The scale -/

/-- **The sieve's scale** `x W(x)^{k-1} / (φ(W(x))^k (log x)^k)`, against which both the numerator
and the denominator are measured. -/
noncomputable def scale (k : ℕ) (x : ℝ) : ℝ :=
  x * (W x : ℝ) ^ (k - 1) / ((Nat.totient (W x) : ℝ) ^ k * (Real.log x) ^ k)

/-- **The scale is positive** once `x` is large enough that the pre-sieving modulus is nontrivial.
-/
theorem scale_pos {k : ℕ} {x : ℝ} (hx : 1 < x) (hW : 1 ≤ W x) : 0 < scale k x := by
  have := Real.log_pos hx
  unfold scale
  positivity

/-! ## The controlling seminorm -/

/-- **A seminorm controlling the evaluation's two functionals.** The tensor-density statement is
made relative to such a datum rather than to a constructed Sobolev norm.

The two functionals are the ones the asymptotic evaluation reads off a test function: the full
mixed derivative, and — for each singled-out coordinate — the boundary value of the mixed
derivative in the remaining ones. Requiring the seminorm to dominate both is what makes "close in
this norm" imply "close in the forms `𝓘` and `𝓙`". -/
structure ControllingSeminorm (k : ℕ) where
  /-- The seminorm itself. -/
  norm : ((Fin k → ℝ) → ℝ) → ℝ
  /-- It is nonnegative. -/
  nonneg : ∀ g, 0 ≤ norm g
  /-- It is subadditive. -/
  add_le : ∀ g g', norm (g + g') ≤ norm g + norm g'
  /-- It is absolutely homogeneous. -/
  smul : ∀ (a : ℝ) (g), norm (fun t ↦ a * g t) = |a| * norm g
  /-- The mixed-derivative functional it controls. -/
  mixed : ((Fin k → ℝ) → ℝ) → ℝ
  /-- For each singled-out coordinate, the boundary functional it controls. -/
  boundary : Fin k → ((Fin k → ℝ) → ℝ) → ℝ
  /-- Both functionals are dominated by the seminorm. -/
  dominates : ∀ g, |mixed g| ≤ norm g ∧ ∀ i, |boundary i g| ≤ norm g

/-! ## Support clauses relative to the orthant

`NuDenominator`, `NumeratorAsymptotic` and `SieveWeights` constrain where a tensor term's product
may be non-zero only among the points of the orthant. Without that restriction the clause
`(∏ i, F l i (t i)) ≠ 0 → t ∈ retreatRegion p k j ε₀` would force the product to vanish wherever a
coordinate is negative, since `Gap212.GPY.retreatRegion` lies in `[0,1]^k`. The tensor data of the
sieve are tails `f = 𝒯g`, and `(𝒯g)(t) = ∫_t^∞ g` equals the total mass of `g` for every `t` below
`supp g`, so such a product is non-zero at points outside the orthant. -/

/-! ## The Gram data of a tensor datum

`𝓘` and `𝓙ᵢ` are evaluated at the inner products and boundary values of the tensor datum itself:
for `ν` the tensor sieve weight of a tensor datum, `∑ν(n) = (𝓘 + o(1))𝓒ₓ` with `𝓘` the discrete
energy of that datum. The three definitions below are these data, matching what
`Gap212.GPY.formI_of_tensor` and `Gap212.GPY.formJ_of_tensor` produce. -/

/-- **The Gram data of a tensor datum**: `inner l l' s = ∫₀^∞ F'_{l,s} F'_{l',s}`, the data `𝓘` is
evaluated at. -/
noncomputable def gramInner {L k : ℕ} (F : Fin L → Fin k → ℝ → ℝ) :
    Fin L → Fin L → Fin k → ℝ :=
  fun l l' s ↦ ∫ t in Set.Ioi (0 : ℝ), deriv (F l s) t * deriv (F l' s) t

/-- **The Gram data with coordinate `i` omitted**, which is what `𝓙ᵢ`'s product runs over: `𝓙ᵢ`
multiplies `∏_{s ≠ i}`, not `∏_s`. -/
noncomputable def gramInnerSkip {L m : ℕ} (F : Fin L → Fin (m + 1) → ℝ → ℝ) (i : Fin (m + 1)) :
    Fin L → Fin L → Fin m → ℝ :=
  fun l l' s ↦ ∫ t in Set.Ioi (0 : ℝ),
    deriv (F l (i.succAbove s)) t * deriv (F l' (i.succAbove s)) t

/-- **The boundary values of the singled-out coordinate**, `bdry l = f_{l,i}(0)` — the factor `𝓙ᵢ`
carries in both of its groups. -/
def gramBdry {L k : ℕ} (F : Fin L → Fin k → ℝ → ℝ) (i : Fin k) : Fin L → ℝ :=
  fun l ↦ F l i 0

/-! ## The shape of the hypotheses

* The numerator lower bound carries the equidistribution hypothesis
  `HasEquidistributionOverQstarFamily p`; the denominator needs none.
* The residue `b` is quantified inside `∃ X`, guarded by `Defs.IsPreSieved b (W x) h`:
  `Gap212.Sieve.exists_isPreSieved` produces a pre-sieved `b` for each `x`, and at a residue not
  coprime to `W(x)` the main term `𝓘·𝓒ₓ`, which carries a factor `φ(W)^{-k}`, is wrong.
* `𝓙ᵢ` is evaluated at the low and high index sets `𝓛(i)` and `𝓤(i) = 𝓛(i)ᶜ`, with the marginal
  clause on `𝓛(i)`. At `𝓛 i = 𝓤 i = univ`, `formJMarginal` would be three times the full Gram form
  `∑_{l,l'} c_l c_{l'} f_{l,i}(0) f_{l',i}(0) ∏_{s≠i} ∫₀^∞ f'_{l,s} f'_{l',s}`, at which the sieve
  asymptotic evaluates the numerator. `Gap212.GPY.exists_tensorDatum_forms_gap` builds `𝓛`, `𝓤` as
  `Gap212.Defs.LSet`, `USet` of `∑_{s≠i} β_{l,s} < (1-ε₀)(A_{j+1} - ε)`; since the datum's factors
  are tails vanishing above their endpoints, this is the cutoff of `Gap212.GPY.marginalRegion`. -/

/-! ## The five statements -/

/-- **Tensor density in the controlling seminorm.**

A smooth compactly supported `g` is approximated to any accuracy `η` by a finite sum
`∑_l c_l ∏_i f_{l,i}` in which every factor is supported on an interval of length at most `ε₃` and
the product's support stays inside the `ε₃`-neighbourhood of `supp g`. The support control keeps
the resulting sieve weights supported in the retreat region, hence the generated moduli in `Q*`.

`Gap212.Sieve.exists_tensor_partition_approx` proves a version with nonnegative coefficients and
factors and closeness in the sup norm. -/
def TensorDensity (k : ℕ) : Prop :=
  ∀ (S : ControllingSeminorm k) (g : (Fin k → ℝ) → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
    ∀ η > (0 : ℝ), ∀ ε₃ > (0 : ℝ),
      ∃ (L : ℕ) (c : Fin L → ℝ) (f : Fin L → Fin k → ℝ → ℝ) (a : Fin L → Fin k → ℝ),
        (∀ l i, ∀ t : ℝ, f l i t ≠ 0 → t ∈ Set.Icc (a l i) (a l i + ε₃)) ∧
        (∀ l, ∀ t : Fin k → ℝ, (∏ i, f l i (t i)) ≠ 0 →
          ∃ s ∈ Function.support g, ∀ i, |t i - s i| ≤ ε₃) ∧
        S.norm (g - fun t ↦ ∑ l, c l * ∏ i, f l i (t i)) < η

/-- **The sieve asymptotic for one pair of profile families at an unrestricted residue**: the
form of `Gap212.Sieve.SieveAsymptotic` in which the residue `b` is quantified before `∃ X`, with no
`Gap212.Defs.IsPreSieved` guard, and the Gram data `inner` are existentially quantified.

It is false at `k = 1` (`Gap212.Sieve.not_sieveAsymptotic_one`): taking `b = 0`, the class consists
of multiples of `W(x)`, none of them prime, so `ρ` annihilates the sum while the main term does not
vanish. -/
def SieveAsymptoticUnrestricted (k : ℕ) : Prop :=
  ∀ (p : SupportParams) (ρ : ℕ → ℝ → ℝ) (β : ℝ), RhoHypotheses p ρ β →
    ∀ (h : Fin k → ℕ) (i₀ : Fin k) (F G : Fin k → ℝ → ℝ) (b : ℕ),
      ∃ inner : Fin k → ℝ, ∀ η > (0 : ℝ), ∃ X : ℝ, ∀ x > X,
        |(∑ n ∈ dyadic x with n % W x = b % W x,
            ρ (n + h i₀) x * ∏ i, lambdaF (F i) x (n + h i) * lambdaF (G i) x (n + h i)) -
          (F i₀ 0 * G i₀ 0 * ∏ i ∈ Finset.univ.erase i₀, inner i) * scale k x| ≤
        η * scale k x

/-- **The sieve asymptotic for one pair of profile families.**

Singling out a coordinate `i₀`, the weighted count of `ρ(n + h_{i₀})` against a product of divisor
weights is `(F_{i₀}(0)G_{i₀}(0)∏_{i≠i₀}∫₀^∞F'ᵢG'ᵢ + o(1))` times the scale, over a pre-sieved
class of the dyadic block.

The hypotheses: `p` a support datum with `A_j > ε`, `ε₀ ∈ (0,1)`, `ρ` satisfying
`Gap212.Defs.RhoHypotheses p ρ β` and equidistributed over `Q⋆`, `h` strictly increasing, `Fᵢ, Gᵢ`
smooth and vanishing above some `B`, with `supp ∏ᵢFᵢ ⊆ R⁺_k(j,ε₀)`, `supp ∏ᵢGᵢ ⊆ R⁺_k(j',ε₀)` and
`supp ∏_{i≠i₀}Fᵢ ⊆ M⁻_k(j,i₀,ε₀)` (all relative to the orthant), and `b` pre-sieved.

* Compact support is one-sided, as in `Gap212.GPY.TensorDatum.compactSupport`: the profiles are
  tails `𝒯g`, and a tail with compact support on `ℝ` vanishes identically.
* The marginal clause `supp ∏_{i≠i₀}Fᵢ ⊆ M⁻_k(j,i₀,ε₀)` is a hypothesis; the numerator lower bound
  discharges it from `𝓛`-membership after the low/high split of `ν` by
  `Gap212.Sieve.omit_square_le`.
* `RhoHypotheses p ρ β` includes `RhoHypotheses.rough_exceeds_cap`, i.e. `p.B j 1 < β`.

`Gap212.Sieve.sieveAsymptotic_of_obligations` proves `SieveAsymptotic 44` from
`Gap212.Sieve.divisor_sum_over_qstar` and `Gap212.Sieve.weighted_error_negligible`, given
`Gap212.Sieve.TotientGramSumLimitOfSupport`; `Gap212.Sieve.numeratorLowerBound_of_sieveAsymptotic`
derives the numerator lower bound from it. -/
def SieveAsymptotic (m : ℕ) : Prop :=
  ∀ (p : SupportParams) (ε₀ : ℝ), 0 < ε₀ → ε₀ < 1 → ∀ j j' : Fin p.n, p.ε < p.A j.succ →
    ∀ (ρ : ℕ → ℝ → ℝ) (β : ℝ), RhoHypotheses p ρ β →
    HasEquidistributionOverQstarFamily p (fun n x ↦ ((ρ n x : ℝ) : ℂ)) →
    ∀ (h : Fin (m + 1) → ℕ), StrictMono h →
    ∀ (i₀ : Fin (m + 1)) (F G : Fin (m + 1) → ℝ → ℝ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) → (∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) →
      (∃ B : ℝ, ∀ i, ∀ t : ℝ, B < t → F i t = 0) →
      (∃ B : ℝ, ∀ i, ∀ t : ℝ, B < t → G i t = 0) →
      (∀ t : Fin (m + 1) → ℝ, (∀ i, 0 ≤ t i) → (∏ i, F i (t i)) ≠ 0 →
        t ∈ retreatRegion p (m + 1) j ε₀) →
      (∀ t : Fin (m + 1) → ℝ, (∀ i, 0 ≤ t i) → (∏ i, G i (t i)) ≠ 0 →
        t ∈ retreatRegion p (m + 1) j' ε₀) →
      (∀ t : Fin m → ℝ, (∀ s, 0 ≤ t s) → (∏ s, F (i₀.succAbove s) (t s)) ≠ 0 →
        t ∈ marginalRegion p m j ε₀) →
      ∀ η > (0 : ℝ), ∃ X : ℝ, ∀ x > X, ∀ b : ℕ, Defs.IsPreSieved b (W x) h →
        |(∑ n ∈ dyadic x with n % W x = b % W x,
              ρ (n + h i₀) x * ∏ i, lambdaF (F i) x (n + h i) * lambdaF (G i) x (n + h i)) -
            (F i₀ 0 * G i₀ 0 * ∏ s : Fin m, ∫ t in Set.Ioi (0 : ℝ),
                deriv (F (i₀.succAbove s)) t * deriv (G (i₀.succAbove s)) t) * scale (m + 1) x|
          ≤ η * scale (m + 1) x

/-- **The denominator asymptotic at an unrestricted family of profiles**: the form of
`Gap212.Sieve.NuDenominator` for arbitrary `F : Fin L → Fin k → ℝ → ℝ`, with no regularity, an
arbitrary `ε₀` and a not necessarily monotone `h`.

It is false (`Gap212.Sieve.not_nuDenominatorUnrestricted`): at `F l i = 1_{\{0\}}` every `λ_F` is
`1`, so `∑ν` counts the residue class, while every `gramInner` entry is `0`, so the asserted main
term is `0`. -/
def NuDenominatorUnrestricted (k : ℕ) : Prop :=
  ∀ (p : SupportParams) (ε₀ : ℝ) (j : Fin p.n) (L : ℕ) (c : Fin L → ℝ)
      (F : Fin L → Fin k → ℝ → ℝ) (h : Fin k → ℕ),
    (∀ l, ∀ t : Fin k → ℝ, (∀ i, 0 ≤ t i) → (∏ i, F l i (t i)) ≠ 0 →
      t ∈ retreatRegion p k j ε₀) →
    ∀ η > (0 : ℝ), ∃ X : ℝ, ∀ x > X, ∀ b : ℕ, Defs.IsPreSieved b (W x) h →
      |(∑ n ∈ dyadic x with n % W x = b % W x, nu L c F h x n) -
        formI c (gramInner F) * scale k x| ≤ η * scale k x

/-- **The denominator asymptotic**: for the tensor sieve weight `ν` of a tensor datum at level
`ε₀ ∈ (0,1)` and a strictly increasing shift tuple, the total weight over a pre-sieved class of the
dyadic block is `(𝓘 + o(1))` times the scale, with `𝓘` the discrete energy of that datum's Gram
data.

The datum is a `Gap212.GPY.TensorDatum`, carrying smoothness, compact support on `[0,∞)` and the
retreat clause on each term's product; compact support on all of `ℝ` is not assumed, since the
datum's factors are tails. Without the datum, the statement is the false
`Gap212.Sieve.NuDenominatorUnrestricted`. `Gap212.Sieve.nuDenominator_of_tensorDatum` proves it from
`Gap212.Sieve.LcmGramSumLimitOfSupport` and `Gap212.Sieve.SelbergSievingError`, using
`Gap212.Sieve.exists_truncation`. -/
@[gap212 "lem_nu_denominator"]
def NuDenominator (k : ℕ) : Prop :=
  ∀ (p : SupportParams) (ε₀ : ℝ), 0 < ε₀ → ε₀ < 1 → ∀ (j : Fin p.n)
      (D : TensorDatum p k j ε₀) (h : Fin k → ℕ), StrictMono h →
    ∀ η > (0 : ℝ), ∃ X : ℝ, ∀ x > X, ∀ b : ℕ, Defs.IsPreSieved b (W x) h →
      |(∑ n ∈ dyadic x with n % W x = b % W x, nu D.L D.c D.f h x n) -
        formI D.c (gramInner D.f) * scale k x| ≤ η * scale k x

/-- **The numerator lower bound**: the weighted count of prime translates is at least
`(∑ᵢ𝓙ᵢ - o(1))` times the same scale, i.e. `liminf_{x→∞} (1/𝓒ₓ) ∑ᵢ ∑_n ν(n)ρ(n + hᵢ) ≥ ∑ᵢ 𝓙ᵢ`,
written out in `ε`-form.

The inequality is one-sided. In each coordinate the omitted contribution is `ρ(n + hᵢ) Q(n)²`,
with `Q` collecting the tensor indices in `𝓤(i)`; it is non-negative since `ρ ≥ 0`, and of the same
order as the main term whenever `𝓤(i)` is non-empty, so the two-sided asymptotic is false.

`Gap212.Defs.formJMarginal` is `𝓙ᵢ`, the low–low group plus twice the high–low group. The index
sets `𝓛ᵢ`, `𝓤ᵢ` are the low and high parts of `Gap212.Defs.LSet` / `USet` at the singled-out
coordinate; they and the Gram data are universally quantified, alongside the tensor datum.

The equidistribution hypothesis is needed here and not for the denominator, which is Polymath8b's
Lemma 4.1: only the numerator's error term sees the moduli. The bare-family form is
`Gap212.Sieve.NumeratorAsymptoticUnrestricted`. -/
@[gap212 "lem_numerator_asymptotic"]
def NumeratorAsymptotic (m : ℕ) : Prop :=
  ∀ (p : SupportParams) (ε₀ : ℝ), 0 < ε₀ → ε₀ < 1 → ∀ j : Fin p.n, p.ε < p.A j.succ →
    ∀ (D : TensorDatum p (m + 1) j ε₀) (ρ : ℕ → ℝ → ℝ) (β : ℝ),
    RhoHypotheses p ρ β →
    HasEquidistributionOverQstarFamily p (fun n x ↦ ((ρ n x : ℝ) : ℂ)) →
    ∀ (h : Fin (m + 1) → ℕ), StrictMono h →
    ∀ 𝓛 𝓤 : Fin (m + 1) → Finset (Fin D.L), (∀ i, 𝓤 i = (𝓛 i)ᶜ) →
      (∀ i : Fin (m + 1), ∀ l ∈ 𝓛 i, ∀ t : Fin m → ℝ, (∀ s, 0 ≤ t s) →
        (∏ s, D.f l (i.succAbove s) (t s)) ≠ 0 → t ∈ marginalRegion p m j ε₀) →
      ∀ η > (0 : ℝ), ∃ X : ℝ, ∀ x > X, ∀ b : ℕ, Defs.IsPreSieved b (W x) h →
        (∑ i : Fin (m + 1), ∑ n ∈ dyadic x with n % W x = b % W x,
            nu D.L D.c D.f h x n * ρ (n + h i) x) ≥
          (∑ i : Fin (m + 1),
              formJMarginal D.c (gramBdry D.f i) (gramInnerSkip D.f i) (𝓛 i) (𝓤 i)) *
            scale (m + 1) x - η * scale (m + 1) x

/-- **The numerator lower bound at an unrestricted family of profiles**, the bare-family form of
`Gap212.Sieve.NumeratorAsymptotic`.

The witness refuting `Gap212.Sieve.NuDenominatorUnrestricted` does not refute it
(`Gap212.Sieve.le_numerator_at_spike`): at those profiles `∑ᵢ𝓙ᵢ` also collapses to `0`, since `𝓙ᵢ`
reads the same derivatives through `Gap212.Sieve.gramInnerSkip`, and a lower bound against a main
term of `0` holds trivially. -/
def NumeratorAsymptoticUnrestricted (m : ℕ) : Prop :=
  ∀ (p : SupportParams) (ε₀ : ℝ) (j : Fin p.n) (ρ : ℕ → ℝ → ℝ) (β : ℝ),
    RhoHypotheses p ρ β →
    HasEquidistributionOverQstarFamily p (fun n x ↦ ((ρ n x : ℝ) : ℂ)) →
    ∀ (L : ℕ) (c : Fin L → ℝ) (F : Fin L → Fin (m + 1) → ℝ → ℝ) (h : Fin (m + 1) → ℕ),
    (∀ l, ∀ t : Fin (m + 1) → ℝ, (∀ i, 0 ≤ t i) → (∏ i, F l i (t i)) ≠ 0 →
      t ∈ retreatRegion p (m + 1) j ε₀) →
    ∀ 𝓛 𝓤 : Fin (m + 1) → Finset (Fin L),
      ∀ η > (0 : ℝ), ∃ X : ℝ, ∀ x > X, ∀ b : ℕ, Defs.IsPreSieved b (W x) h →
        (∑ i : Fin (m + 1), ∑ n ∈ dyadic x with n % W x = b % W x,
            nu L c F h x n * ρ (n + h i) x) ≥
          (∑ i : Fin (m + 1),
              formJMarginal c (gramBdry F i) (gramInnerSkip F i) (𝓛 i) (𝓤 i)) *
            scale (m + 1) x - η * scale (m + 1) x

/-- **The sieve weights realize the variational inequality.**

Given the continuum certificate on the support — `p = p_⋆`, `k = 45`, and `F` symmetric,
square-integrable, vanishing off `T₄₅(p_⋆)`, with `0 < I_T(F) < 45 J_T(F)`, which is
`Gap212.Certificate p m 0 0` — there is a `Gap212.GPY.TensorDatum` at some level `ε₀ ∈ (0,1)` for
the band `1`, supported in the retreat region, with nonnegative coefficients, whose discrete forms
satisfy `0 < 𝓘 < ∑ᵢ 𝓙ᵢ`.

The low/high split is part of the conclusion: `𝓤(i)` is the complement of `𝓛(i)`, and a low
term's `i`-omitted marginal is supported in `M⁻_k(j,i,ε₀)`.

Proved as `Gap212.Sieve.sieveWeights`, from `Gap212.GPY.exists_retreat_gap` and
`Gap212.GPY.exists_tensorDatum_forms_gap`. -/
def SieveWeights : Prop :=
  Certificate gap212Params 44 0 0 →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
      ∃ (D : TensorDatum gap212Params 45 ⟨0, gap212Params.n_pos⟩ ε₀)
        (𝓛 𝓤 : Fin 45 → Finset (Fin D.L)),
        (∀ i, 𝓤 i = (𝓛 i)ᶜ) ∧
        (∀ i : Fin 45, ∀ l ∈ 𝓛 i, ∀ t : Fin 44 → ℝ, (∀ s, 0 ≤ t s) →
          (∏ s, D.f l (i.succAbove s) (t s)) ≠ 0 →
            t ∈ marginalRegion gap212Params 44 ⟨0, gap212Params.n_pos⟩ ε₀) ∧
        (∀ l, 0 ≤ D.c l) ∧
        0 < formI D.c (gramInner D.f) ∧
        formI D.c (gramInner D.f) <
          ∑ i : Fin 45, formJMarginal D.c (gramBdry D.f i) (gramInnerSkip D.f i) (𝓛 i) (𝓤 i)

end Gap212.Sieve
