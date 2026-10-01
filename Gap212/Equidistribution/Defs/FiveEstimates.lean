/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Gap212.Attr
public import Gap212.Definitions
public import Gap212.Equidistribution.Moduli

/-!
# The families of moduli of the five equidistribution estimates

Each of the five equidistribution estimates the routing argument invokes — Baker–Irving Type I,
the three Type II estimates IIa, IIb and IIc, and Polymath Type III — gives equidistribution not
over the whole ambient range

`𝓡(x, ω) = [1, x^{1/2+2ω}] ∩ ℕ = Gap212.moduliRange x ω`

of moduli, but over a subfamily of it, cut out by the existence of divisors of the modulus in
prescribed windows. This file defines those five subfamilies. Their point is that the divisor
conditions are far weaker than the `i`-tuply `x^δ`-dense divisibility that the estimates of
Polymath and of Baker–Irving ask of their moduli, so many more moduli survive; that weakening is
what the variants of those estimates in [2] buy.

A window is an open interval of multiplicative width `x^δ`, placed just below a scale and pushed
down by a further multiple of the analytic loss `ε` that the estimate pays for its
Fourier-analytic input. Writing `N` for the scale of the second factor of the convolution being
estimated and `d` for the modulus being tested:

* `D_I` asks for one divisor `r` of `d`, in a window below `N` when `N ≤ √x` and below the
  conjugate scale `x / N` when `√x < N ≤ x^{1/2+2ω+ε}`, since the argument splits `d = r ⬝ (d / r)`
  with `r` close to whichever of the two scales lies below `√x`; above `x^{1/2+2ω+ε}` it asks for
  no divisor at all. That third branch is the largest of the three, not the smallest: over it the
  estimate asserts equidistribution for every modulus up to `x^{1/2+2ω}` with no factorisation to
  check, which is why it covers the Type I moduli the bilinear input cannot reach. The trichotomy
  is one in the scale `N` alone; the other four parameters move no branch, except that `ω` and `ε`
  widen the second threshold.
* `D_IIa` asks for one divisor `r` of `d` in the window `(N x^{-δ-3ε}, N x^{-3ε})` below `N`.
* `D_IIb` asks for that `r`, and for a divisor `u` of `d / r` in a window below `N⁻¹ x^{1/2-2ω}`.
* `D_IIc` asks for that `r`, for a divisor `u` of `d / r` in a window below `N⁻¹ x / d` — the
  length of the progressions the estimate averages over — and for a divisor `d₁` of `r` in a
  window below `r² N⁻¹ x² / d⁴`, the scale at which the argument splits `r` before its dispersion
  estimate. Near the top of the range, `d` about `√x`, the three are barely compatible: `u` about
  `√x / N` forces `d² ≥ x` and `d₁` about `N x² / d⁴` forces `d⁴ ≤ N x²`, which is why the family
  is thin where it is used.
* `D_III` asks for one divisor `r` of `d` in a window whose position is absolute. It is the odd
  one out: the exponent `1/3` carries no scale and no `ε`, the only displacement is by the width
  `δ` and the level `ω`, and the four smooth scales `N₁, N₂, N₃, M` of the Type III convolution
  enter the estimate's hypotheses but not its family of moduli. So `D_III` is a function of `x`,
  `ω` and `δ` alone, and a containment proved into it needs no retreat in `ε`.

## Main definitions

Declared in `Gap212.Definitions`, which carries the challenge file's own text.

* `Gap212.moduliI`: `D_I(x, ω, N, δ, ε)`, piecewise in `N`.
* `Gap212.moduliIIa`: `D_IIa(x, ω, N, δ, ε)`.
* `Gap212.moduliIIb`: `D_IIb(x, ω, N, δ, ε)`.
* `Gap212.moduliIIc`: `D_IIc(x, ω, N, δ, ε)`.
* `Gap212.moduliIII`: `D_III(x, ω, δ)`.

## Implementation notes

*The scale, not its exponent, is the parameter.* [2] fixes `γ` by `N = x^γ` and displays
every window as powers of `x` alone — `(x^{γ-δ-3ε}, x^{γ-3ε})` for `D_IIa`, and so on. Here each
endpoint is instead a product of the real scale `N` (or of `N⁻¹`) with a real power `x ^ (·)`,
`Real.rpow` as in `Gap212.moduliRange`, the scale never absorbed into an exponent. The two
readings are the same condition whenever `N = x^γ`, which for `1 < x` and `0 < N` is
`γ = Real.log N / Real.log x`, and the scale is what the estimates quantify over
(`x^{γ₁} ≤ N ≤ x^{γ₂}`), so carrying it asks for no relation between `N` and `x`. The `γ`-shaped
`Gap212.moduliIFamily`, `moduliIIaFamily`, `moduliIIbFamily` and `moduliIIcFamily` are these
families at `N = x^γ`; only `D_III`, whose window has no scale in it, agrees with its `γ`-shaped
form `Gap212.moduliIIIFamily x ω γ δ ε` for every `γ`, once `r ∈ d.divisors` is read as `r ∣ d`
on the ambient range (see below).

*The `D_III` window is that of [2].* `4δ/3` and not `4γ/3`: [2] displays it twice with
`4δ/3`, and its proof substitutes `S = x^{1/3+4δ/3-4ω/3}` for the upper endpoint, so the parameter
occurring there is the width and not the exponent of a scale. [2] nevertheless carries `γ`
and `ε` in the notation `D_III(x; ω, γ, δ; ε)`, for uniformity with its other four displays; since
neither occurs in the condition, neither is an argument here.

*The divisor conditions are pinned, not characterised.* Every window is open at both ends, as
[2] displays it, so a divisor sitting on an endpoint witnesses nothing; and each divisor is
pinned by its own window rather than asserted to lie in *some* window of width `x^δ` below the
scale, which is strictly weaker and would not compose with the `δ` that the estimates' linear
inequalities in `(ω, γ, δ)` constrain. In the two chains, `u` divides `d / r` and `d₁` divides
`r`, neither dividing `d`, with `d / r` natural-number division, exact because `r ∣ d`.
Divisibility is written `r ∣ d` throughout, as in [2]. `Gap212.moduliIIIFamily` is cut by
`Gap212.HasDivisorIn`, that is by `∃ r ∈ d.divisors`, and `r ∈ d.divisors` is `r ∣ d ∧ d ≠ 0`; the
two readings agree on the ambient range, where `1 ≤ d`, so `d ≠ 0` and `Nat.mem_divisors`
applies.

*Totality.* No hypothesis is imposed: no positivity of `x`, `N`, `δ` or `ε`, no bound on `ω`, and
no order between the endpoints of a window. For `δ ≤ 0` every window is empty, and with it every
family except the third branch of `D_I`; that is the honest reading, and the estimates that
consume these families supply `0 < δ` and their own ranges themselves. Each family is a
`Finset ℕ`, since `Gap212.HasEquidistribution` sums a discrepancy over it after filtering by
`Squarefree`, and each is `noncomputable` because `Gap212.moduliRange` is; the divisor conditions
are made decidable classically rather than by a decision procedure, no consumer computing with
them. Membership needs no unfolding beyond `Finset.mem_filter`.

*None of the five is degenerate.* `moduliI 16 (1/8) 4 (1/2) 0 = {2, 3, 4, 6, 8}`: the first branch
applies, `N = √x`, with window `(1, 4)` inside the range `Finset.Icc 1 8`, so the family is the
multiples of `2` or of `3` there — neither empty nor all of the range, which a large `δ` would
make it, `1` then lying in the window. At the same parameters with `ω = 0`, where the range is
`Finset.Icc 1 4`, one has `2 ∈ D_IIa` and `1 ∉ D_IIa`. Deeper in, with every parameter in the
regime the estimates use — `ω ∈ (0, 1/4)`, `0 < δ`, `0 < ε`, `N ≤ √x` —
`4 ∈ D_IIb(2^16, 1/16, 8, 1, 1/100)` by `r = u = 2`, and
`256 ∈ D_IIc(2^16, 1/16, 32, 1/10, 1/1000)` by `r = 16`, `u = 4` and `d₁ = 4`, whose three windows
`(10.21, 30.95)`, `(2.46, 7.48)` and `(1.48, 4.49)` pin each divisor to finitely many values. For
`D_III`, `r = d` puts any `d` of the range lying in the window into the family, so
`2 ^ 21 ∈ D_III(2^36, 1/24, 1/4)`, whose window is `(2^13, 2^22)` and whose range is `[1, 2^21]`;
there the window's lower endpoint stays below the top of the range, which happens exactly when
`δ < 1/2 + 10ω`, as the estimate's `δ < 1/4 + ω` forces.

## References

* R. C. Baker and A. J. Irving, *Bounded intervals containing many primes*: the Type I estimate
  whose family of moduli `D_I` is.
* [1, Theorem 2.8]: (iv) for `D_IIa`, (ii) for `D_IIb`, (v) for `D_III`, and the Type II estimates
  that `D_IIc` improves on.
* [2, Lemmas 3–7], where all five families are displayed in the piecewise form transcribed here;
  `D_IIc` retains the factorization requirements of Stadlmann's earlier Type I estimate.
-/

@[expose] public section

namespace Gap212

attribute [gap212 "def_moduli_i"] moduliI
attribute [gap212 "def_moduli_iia"] moduliIIa
attribute [gap212 "def_moduli_iib"] moduliIIb
attribute [gap212 "def_moduli_iic"] moduliIIc
attribute [gap212 "def_moduli_iii"] moduliIII

end Gap212
