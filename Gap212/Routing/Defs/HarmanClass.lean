/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Harman

/-!
# The uniform slack of the routing argument

Each of the five equidistribution estimates the routing argument invokes asks its conditions on the
exponent `γ = log_x N` non-strictly, with a slack `θ > 0` quantified before the admissible loss and
before the implied constant, which is what makes that constant uniform in the exponent. The source
states the same inequalities strictly and remarks that restricting to triples which meet them with
a fixed margin makes both uniform, so `θ` is that remark promoted into the statements. All five are
invoked at one and the same value of it,

`θ = 3ϵ`,

where `ϵ = 10⁻¹⁰` is the fixed slack `Gap212.Harman.slack` with which the Harman class
`ℋ(ξ₁, ξ₂, ξ₃)` is itself cut.

One value serves all five because the margins the levels `δ*` leave at the walls the routes must
clear are multiples of `ϵ` — `3ϵ` at the low Type I wall, `14ϵ` at the high one, `7ϵ` at each of
the Type IIa and Type IIb walls, `4ϵ` at the first Type IIc wall, `7ϵ` at the Type III wall — and
constants rather than functions of `γ`, so their minimum can be taken in advance and no uniformity
has to be manufactured over the continuum of exponents. That minimum is `3ϵ`, and the low Type I
wall attains it: there `3γ - 12ω - 3δ*` is `1 + θ` exactly where the wall asks for `≥ 1 + θ`, so no
larger `θ` is admissible, while every other wall keeps room — `11ϵ` of it at the high Type I wall.

## Main definitions

* `Gap212.Harman.uniformSlack`: the slack `θ = 3ϵ` at which the routing argument invokes each of
  the five equidistribution estimates.

## Implementation notes

The value is pinned rather than asserted to exist: "some positive slack clearing every wall" is
weaker, and would leave each of the five applications free to choose its own, whereas at this one
value the wall comparisons are arithmetic in `ϵ` — an identity at the low Type I wall, non-strict
inequalities elsewhere. And it is positive, `θ = 3/10¹⁰`, as the estimates ask of their slack.

It is not parametrised by the slack either: `fun ϵ ↦ 3 * ϵ` is multiplication by three, whereas the
content here is that `θ` is three times *the* `ϵ` the Harman class is cut with, so it is a closed
constant in the namespace of that class, unlike the transition retreat
`Gap212.Notation.epsilonT`, which is a genuine function of a slack. Being an `abbrev`, it satisfies
`θ = 3 * ϵ` by `rfl`, so a wall comparison is reached from the value of `ϵ` with no rewriting step
for `θ`.

Distinct from the level `ϑ(q; x) = log_x q` of a modulus, the source's other theta, which is
`Gap212.Notation.theta`; and from the support enlargement `ε` and the modulus retreat `ε₀`, which
are parameters of the sieve datum rather than slacks in an exponent.

## References

* [2, Lemmas 3–7] and the note following the first of them, where the exponent inequalities are
  strict and a fixed margin in them is what makes the admissible loss, and with it the implied
  constant, uniform in the triple.
* [2, Definition 9], where `ϵ = 10⁻¹⁰` is fixed.
-/

@[expose] public section

namespace Gap212.Harman

/-- **The uniform slack at the datum**, `θ = 3ϵ`: the one value of the exponent slack at which the
routing argument invokes each of the five equidistribution estimates, `ϵ` being the fixed slack
`Gap212.Harman.slack` of the Harman class.

It is the smallest margin the levels leave at the walls of those five, attained at the low Type I
wall, so this one `θ` clears all of them and no larger value would. Distinct from the level
`Gap212.Notation.theta` of a modulus, the source's other theta. -/
@[gap212 "def_theta"]
noncomputable abbrev uniformSlack : ℝ := 3 * slack

end Gap212.Harman
