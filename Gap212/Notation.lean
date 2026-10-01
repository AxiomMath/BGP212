/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Primorial
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Order.CompletePartialOrder
public meta import Gap212.Attr

/-!
# Notation

The symbols of the notation index, as definitions: the logarithmic scale
`log_x`, the level parameters `θ`, `κ` and `ω₀` of a modulus, the primorial, smoothness of an
integer, the three Vinogradov relations, the transition retreat, and the slope of an extraction
leaf.

## Conventions

Vinogradov `≪` is rendered as an explicit `∃ c > 0` bound with the quantifier order recording
what the implied constant may depend on, matching
`Gap212.IsCoefficientSequenceFamily`. All three relations are stated for `x > 1`.

## Main definitions

* `Gap212.Notation.logx`: `log_x d = log d / log x`.
* `Gap212.Notation.theta`, `kappa`, `omegaZero`: the level of a modulus, its deficiency below the
  half-level, and the normalized level.
* `Gap212.Notation.primorialP`: `P(z) = ∏_{p ≤ z} p`, Mathlib's `primorial`.
* `Gap212.Notation.IsSmoothInt`: every prime factor below `x^δ`.
* `Gap212.Notation.DomLE`, `DomGE`, `AsympEq`: `≪`, `≫`, `≍`.
* `Gap212.Notation.epsilonT`: the inward retreat `ϵ/100` at the transition.
* `Gap212.Notation.leafSlope`: the maximum absolute slope of a leaf's capacities.
-/

@[expose] public section

namespace Gap212.Notation

open Real Finset

/-- **The logarithmic scale.** `log_x d = log d / log x`, the exponent `e` with `d = x^e`. -/
@[gap212 "not_log_x"]
noncomputable def logx (x d : ℝ) : ℝ := log d / log x

/-- **The level of a modulus**, `θ(q;x) = log_x q`. -/
@[gap212 "not_theta"]
noncomputable def theta (q x : ℝ) : ℝ := logx x q

/-- **The deficiency below the half-level**, `κ(q;x) = 1/2 - log_x q`. Positive strictly below
the half-level, zero at it, negative above. -/
@[gap212 "not_kappa"]
noncomputable def kappa (q x : ℝ) : ℝ := 1 / 2 - logx x q

/-- **The normalized level**, `ω₀(q;x) = -κ(q;x)/2`, so that `θ = 1/2 + 2ω₀`. -/
@[gap212 "not_omega_zero"]
noncomputable def omegaZero (q x : ℝ) : ℝ := -kappa q x / 2

/-- The three level parameters agree: `θ = 1/2 + 2ω₀ = 1/2 - κ`. -/
theorem theta_eq (q x : ℝ) : theta q x = 1 / 2 + 2 * omegaZero q x := by
  simp only [theta, omegaZero, kappa]; ring

/-- **The primorial** `P(z) = ∏_{p ≤ z} p`, an abbreviation for Mathlib's `primorial`. -/
@[gap212 "not_primorial"]
abbrev primorialP (z : ℕ) : ℕ := primorial z

/-- **`x^δ`-smoothness.** An integer is `x^δ`-smooth when every prime dividing it is smaller
than `x^δ`. -/
@[gap212 "not_smooth"]
def IsSmoothInt (n : ℕ) (x δ : ℝ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) < x ^ δ

/-- **`f ≪ g`.** There is an absolute `C > 0` with `f x ≤ C g x` for every `x > 1`. -/
@[gap212 "not_dom_le"]
def DomLE (f g : ℝ → ℝ) : Prop := ∃ C > (0 : ℝ), ∀ x : ℝ, 1 < x → f x ≤ C * g x

/-- **`f ≫ g`.** There is an absolute `c > 0` with `c g x ≤ f x` for every `x > 1`. -/
def DomGE (f g : ℝ → ℝ) : Prop := ∃ c > (0 : ℝ), ∀ x : ℝ, 1 < x → c * g x ≤ f x

/-- **`f ≍ g`.** Both `f ≪ g` and `f ≫ g`, that is `c g x ≤ f x ≤ C g x` for absolute
`0 < c ≤ C`. -/
def AsympEq (f g : ℝ → ℝ) : Prop := DomLE f g ∧ DomGE f g

/-- Commensurability unfolds to the two-sided bound `c g x ≤ f x ≤ C g x`. -/
theorem asympEq_iff {f g : ℝ → ℝ} :
    AsympEq f g ↔ (∃ C > (0 : ℝ), ∀ x : ℝ, 1 < x → f x ≤ C * g x) ∧
      ∃ c > (0 : ℝ), ∀ x : ℝ, 1 < x → c * g x ≤ f x := Iff.rfl

/-- **The inward retreat at the transition**, `ε_t = ϵ/100`, where `ϵ` is the fixed slack of the
Harman class. Small enough that the four transition capacities stay above their endpoint values
throughout the transition range. -/
noncomputable def epsilonT (ϵ : ℝ) : ℝ := ϵ / 100

/-- **The slope of an extraction leaf**, the largest absolute slope among its bin capacities as
affine functions of the level `θ`. It is what converts a reserve into a transport radius: a
partition valid at the half-level survives while `|θ - 1/2| < η / leafSlope`. -/
noncomputable def leafSlope {r : ℕ} (slope : Fin r → ℝ) : ℝ :=
  if h : 0 < r then Finset.univ.sup' (Finset.univ_nonempty_iff.mpr
    (Fin.pos_iff_nonempty.mp h)) (fun i ↦ |slope i|) else 0

end Gap212.Notation
