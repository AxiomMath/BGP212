/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Definitions
public import Gap212.Equidistribution.Basic

/-!
# The five sets of moduli

The moduli sets of [2, Lemmas 3–7], in the `γ`-shaped form. Each is a set of `d ≤ x^{1/2+2ω}`
constrained by the existence of divisors in prescribed ranges; the point of the variants in [2] of
the Polymath and Baker–Irving estimates is that these constraints are far weaker than `i`-tuply
`x^δ`-dense divisibility.

All five are transcribed verbatim from the displays of [2], including exponents that look odd
(see `moduliIIIFamily`).

## Main definitions

* `Gap212.moduliIIaFamily`: `D_{IIa}`, [2, Lemma 3] (Polymath Type II).
* `Gap212.moduliIIbFamily`: `D_{IIb}`, [2, Lemma 4] (Polymath Type I(ii)).
* `Gap212.moduliIFamily`: `D_I`, [2, Lemma 5] (Baker–Irving Type I) — piecewise in `γ`.
* `Gap212.moduliIIcFamily`: `D_{IIc}`, [2, Lemma 6] (Stadlmann Type I).
* `Gap212.moduliIIIFamily`: `D_{III}`, [2, Lemma 7] (Polymath Type III).
-/

@[expose] public section

namespace Gap212

open Real

/-- `d` has a divisor in the open interval `(x^a, x^b)`. The shape of every constraint below. -/
def HasDivisorIn (d : ℕ) (x a b : ℝ) : Prop := ∃ r ∈ d.divisors, x ^ a < (r : ℝ) ∧ (r : ℝ) < x ^ b

open Classical in
/-- `D_{IIa}` of [2, Lemma 3]: a divisor `r` with `x^{γ-3ε-δ} < r < x^{γ-3ε}`. -/
noncomputable def moduliIIaFamily (x ω γ δ ε : ℝ) : Finset ℕ :=
  {d ∈ moduliRange x ω | HasDivisorIn d x (γ - 3 * ε - δ) (γ - 3 * ε)}

open Classical in
/-- `D_{IIb}` of [2, Lemma 4]: a divisor `r` as in `D_{IIa}`, and a divisor `u` of `d/r` with
`x^{1/2-γ-2ω-6ε-δ} < u < x^{1/2-γ-2ω-6ε}`. -/
noncomputable def moduliIIbFamily (x ω γ δ ε : ℝ) : Finset ℕ :=
  {d ∈ moduliRange x ω |
    ∃ r ∈ d.divisors, x ^ (γ - 3 * ε - δ) < (r : ℝ) ∧ (r : ℝ) < x ^ (γ - 3 * ε) ∧
      HasDivisorIn (d / r) x (1 / 2 - γ - 2 * ω - 6 * ε - δ) (1 / 2 - γ - 2 * ω - 6 * ε)}

open Classical in
/-- `D_I` of [2, Lemma 5], piecewise in `γ`: for `γ ≤ 1/2` a divisor near `x^γ`; for
`γ ∈ (1/2, 1/2+2ω+ε]` a divisor near `x^{1-γ}`; and for `γ > 1/2+2ω+ε` no constraint at all. -/
noncomputable def moduliIFamily (x ω γ δ ε : ℝ) : Finset ℕ :=
  if γ ≤ 1 / 2 then
    {d ∈ moduliRange x ω | HasDivisorIn d x (γ - δ - 3 * ε) (γ - 3 * ε)}
  else if γ ≤ 1 / 2 + 2 * ω + ε then
    {d ∈ moduliRange x ω | HasDivisorIn d x (1 - γ - δ - 3 * ε) (1 - γ - 3 * ε)}
  else
    moduliRange x ω

open Classical in
/-- `D_{IIc}` of [2, Lemma 6]: a divisor `r` as in `D_{IIa}`, a divisor `u` of `d/r` in a range
scaled by `d⁻¹`, and a divisor `d₁` of `r` in a range scaled by `r² d⁻⁴`. -/
noncomputable def moduliIIcFamily (x ω γ δ ε : ℝ) : Finset ℕ :=
  {d ∈ moduliRange x ω |
    ∃ r ∈ d.divisors, x ^ (γ - 3 * ε - δ) < (r : ℝ) ∧ (r : ℝ) < x ^ (γ - 3 * ε) ∧
      (∃ u ∈ (d / r).divisors,
        x ^ (1 - γ - 6 * ε - δ) / (d : ℝ) < (u : ℝ) ∧ (u : ℝ) < x ^ (1 - γ - 6 * ε) / (d : ℝ)) ∧
      ∃ d₁ ∈ r.divisors,
        (r : ℝ) ^ 2 * x ^ (2 - γ - 52 * ε - δ) / (d : ℝ) ^ 4 < (d₁ : ℝ) ∧
          (d₁ : ℝ) < (r : ℝ) ^ 2 * x ^ (2 - γ - 52 * ε) / (d : ℝ) ^ 4}

open Classical in
/-- `D_{III}` of [2, Lemma 7]: a divisor `r` with `x^{1/3+4δ/3-4ω/3-δ} < r < x^{1/3+4δ/3-4ω/3}`.

Transcribed verbatim, and it is the odd one out twice over.

First, the exponent carries `δ` with both signs: the window is
`(1/3 + δ/3 - 4ω/3, 1/3 + 4δ/3 - 4ω/3)`, of width `δ` like the other four, but where the
neighbouring lemmas put a `γ` this display has `4δ/3`.

Second, and relatedly, `γ` and `ε` do not occur in the constraint at all — every other set here is
cut by an `ε`-shifted window (`3ε`, `6ε`, `52ε`) around a `γ`-dependent exponent. Both parameters
are retained in the signature only so that all five sets share the shape
`ℝ → ℝ → ℝ → ℝ → ℝ → Finset ℕ` that `HasEquidistributionFamily` consumes.

The `4δ/3` is as [2] displays it, twice; its proof substitutes `S = x^{1/3+4δ/3-4ω/3}` for the
upper endpoint, so the parameter there is the width `δ` and not the exponent of a scale. -/
noncomputable def moduliIIIFamily (x ω _γ δ _ε : ℝ) : Finset ℕ :=
  {d ∈ moduliRange x ω |
    HasDivisorIn d x (1 / 3 + 4 * δ / 3 - 4 * ω / 3 - δ) (1 / 3 + 4 * δ / 3 - 4 * ω / 3)}

end Gap212
