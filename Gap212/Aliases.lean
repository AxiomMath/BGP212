/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Equidistribution.Basic
public import Gap212.Equidistribution.CoefficientSequence
public import Gap212.Equidistribution.Estimates
public import Gap212.Equidistribution.Moduli
public import Gap212.Sieve.Certificate
public import Gap212.Sieve.Integrals
public import Gap212.Sieve.Support
public import Gap212.Tuple.H45
public meta import Gap212.Attr

/-!
# Tagged aliases of existing declarations

Each entry is an `abbrev` aliasing a declaration of the `Gap212` namespace, most of them carrying
a `gap212` tag; an alias is reducible and elaborates to the same constant.

## Contents

Aliases for the coefficient-sequence vocabulary, the five modulus families, the support and its
integrals, the certificate and the chosen datum, the admissible 45-tuple, and the five assumed
equidistribution estimates.
-/

@[expose] public section

namespace Gap212.Aliases

/-! ### Coefficient sequences and equidistribution -/

/-- Alias of `Gap212.IsCoefficientSequenceFamily`: `α` is a coefficient sequence. -/
abbrev IsCoefficientSequenceFamily := Gap212.IsCoefficientSequenceFamily

/-- Alias of `Gap212.LocatedAtScaleFamily`, the predicate that `α` is located at scale `N`. -/
abbrev LocatedAtScaleFamily := Gap212.LocatedAtScaleFamily

/-- Alias of `Gap212.dconvFamily`, the Dirichlet convolution in the arithmetic variable. -/
abbrev dconvFamily := Gap212.dconvFamily

/-- Alias of `Gap212.dyadic`, the integers of `[x, 2x]` as a `Finset`. -/
@[gap212 "def_dyadic"]
noncomputable abbrev dyadic := Gap212.dyadic

/-- Alias of `Gap212.CoprimeBelow`: `a` is coprime to every prime up to `x`. -/
@[gap212 "def_coprime_below"]
abbrev CoprimeBelow := Gap212.CoprimeBelow

/-- Alias of `Gap212.HasSiegelWalfiszFamily`, the Siegel–Walfisz property at scale `N`. -/
abbrev HasSiegelWalfiszFamily := Gap212.HasSiegelWalfiszFamily

/-- Alias of `Gap212.HasEquidistributionFamily`, equidistribution over a family of moduli sets. -/
abbrev HasEquidistributionFamily := Gap212.HasEquidistributionFamily

/-! ### The five modulus families -/

/-- Alias of `Gap212.moduliRange`, the ambient range `[1, x^{1/2+2ω}] ∩ ℕ` of every moduli set. -/
@[gap212 "def_moduli_range"]
noncomputable abbrev moduliRange := Gap212.moduliRange

/-- Alias of `Gap212.HasDivisorIn`: `d` has a divisor in the open interval `(x^a, x^b)`. -/
@[gap212 "def_has_divisor_in"]
abbrev HasDivisorIn := Gap212.HasDivisorIn

/-- Alias of `Gap212.moduliIIaFamily`, the moduli set `D_{IIa}` of [2, Lemma 3]. -/
noncomputable abbrev moduliIIaFamily := Gap212.moduliIIaFamily

/-- Alias of `Gap212.moduliIIbFamily`, the moduli set `D_{IIb}` of [2, Lemma 4]. -/
noncomputable abbrev moduliIIbFamily := Gap212.moduliIIbFamily

/-- Alias of `Gap212.moduliIFamily`, the moduli set `D_I` of [2, Lemma 5], piecewise in `γ`. -/
noncomputable abbrev moduliIFamily := Gap212.moduliIFamily

/-- Alias of `Gap212.moduliIIcFamily`, the moduli set `D_{IIc}` of [2, Lemma 6]. -/
noncomputable abbrev moduliIIcFamily := Gap212.moduliIIcFamily

/-- Alias of `Gap212.moduliIIIFamily`, the moduli set `D_{III}` of [2, Lemma 7]. -/
noncomputable abbrev moduliIIIFamily := Gap212.moduliIIIFamily

/-! ### The support, its strata, and the variational integrals -/

/-- Alias of `Gap212.SupportParams`, the parameters `(δ, ε, n, A, B)` of the support. -/
@[gap212 "def_support_params"]
abbrev SupportParams := Gap212.SupportParams

/-- Alias of `Gap212.SupportParams.large`, the set `{i : tᵢ > δ}` of large coordinates. -/
@[gap212 "def_large"]
noncomputable abbrev large := Gap212.SupportParams.large

/-- Alias of `Gap212.SupportParams.stratum`, the stratum `j` of the support `T_k`. -/
@[gap212 "def_stratum"]
noncomputable abbrev stratum := Gap212.SupportParams.stratum

/-- Alias of `Gap212.T`, the support `T_k(δ, A, B, ε)`, the union of the strata. -/
@[gap212 "def_support_T"]
noncomputable abbrev T := Gap212.T

/-- Alias of `Gap212.Iint`, the integral `I(F) = ∫_{T_k} F(t)² dt`. -/
@[gap212 "def_iint"]
noncomputable abbrev Iint := Gap212.Iint

/-- Alias of `Gap212.Jregion`, the region of the `(j, j')` summand of `J(F)`. -/
@[gap212 "def_jregion"]
noncomputable abbrev Jregion := Gap212.Jregion

/-- Alias of `Gap212.Jint`, the integral `J(F)` of [2, Definition 5]. -/
@[gap212 "def_jint"]
noncomputable abbrev Jint := Gap212.Jint

/-- Alias of `Gap212.Kregion`, the region of the `(j, j')` summand of `K(F)`. -/
@[gap212 "def_kregion"]
noncomputable abbrev Kregion := Gap212.Kregion

/-- Alias of `Gap212.Kint`, the integral `K(F)` of [2, Definition 5]. -/
@[gap212 "def_kint"]
noncomputable abbrev Kint := Gap212.Kint

/-- Alias of `Gap212.Symmetric`: `F` is invariant under permuting its coordinates. -/
@[gap212 "def_symmetric"]
abbrev Symmetric {k : ℕ} := @Gap212.Symmetric k

/-! ### The certificate and the chosen datum -/

/-- Alias of `Gap212.Certificate`, inequality (2.1) of [2, Proposition 1]. -/
@[gap212 "def_certificate"]
noncomputable abbrev Certificate := Gap212.Certificate

/-- **`p_⋆`, the parameter datum** of the main theorems. It differs from
`Gap212.gap212ParamsPointA`, which has `δ = 0.0179`, `ε = 0.0085` and cap row `0.155/0.17`. -/
@[gap212 "def_point_a_params"]
noncomputable abbrev gap212Params := Gap212.gap212Params

/-- Alias of `Gap212.Gap212Certificate`, the proposition `Certificate gap212Params 44 0 0`. -/
@[gap212 "thm_ext_certificate"]
abbrev Gap212Certificate := Gap212.Gap212Certificate

/-! ### The admissible 45-tuple -/

/-- Alias of `Gap212.H45`, the normalized admissible `45`-tuple of diameter `212`. -/
abbrev H45 := Gap212.H45

/-- The diameter of `H45` is `212`, and its cardinality is `45`. -/
theorem h45_card_and_diameter : H45.card = 45 ∧ Gap212.H45.diameter = 212 :=
  ⟨Gap212.card_H45, Gap212.diameter_H45⟩

/-- The tuple `Gap212.H45` is admissible. -/
theorem h45_admissible : Gap212.H45.Admissible := Gap212.admissible_H45

/-! ### The five assumed equidistribution estimates -/

/-- Alias of `Gap212.TypeIIPolymathFamily`, the Polymath Type II estimate ([2, Lemma 3]). -/
abbrev TypeIIPolymathFamily := Gap212.TypeIIPolymathFamily

/-- Alias of `Gap212.TypeIbPolymathFamily`, the Polymath Type I(ii) estimate ([2, Lemma 4]). -/
abbrev TypeIbPolymathFamily := Gap212.TypeIbPolymathFamily

/-- Alias of `Gap212.TypeIBakerIrvingFamily`, the Baker–Irving Type I estimate ([2, Lemma 5]). -/
abbrev TypeIBakerIrvingFamily := Gap212.TypeIBakerIrvingFamily

/-- Alias of `Gap212.TypeIStadlmannFamily`, the Stadlmann Type I estimate ([2, Lemma 6]). -/
abbrev TypeIStadlmannFamily := Gap212.TypeIStadlmannFamily

/-- Alias of `Gap212.TypeIIIPolymathFamily`, the Polymath Type III estimate ([2, Lemma 7]). -/
abbrev TypeIIIPolymathFamily := Gap212.TypeIIIPolymathFamily

end Gap212.Aliases
