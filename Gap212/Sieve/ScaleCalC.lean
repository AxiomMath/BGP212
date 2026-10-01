/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Asymptotics
public import Gap212.Sieve.DivisorSumDefs

/-!
# The sieve's scale and `𝓒_x` are one quantity

`Gap212.Sieve.scale` and `Gap212.GPY.calC` are the same number under two names in two namespaces:

  `scale k x  = x · W(x)^(k-1) / (φ(W(x))^k · (log x)^k)`
  `calC m x   = x · W(x)^m / (φ(W(x))^(m+1) · (log x)^(m+1))`

so `scale (m+1) x = calC m x`, and by `rfl` — the two definitions are the same term once `k` is
`m + 1`, since `(m+1) - 1` reduces to `m`.

The divisor-sum asymptotics are stated against `𝓒_x`, which is `calC`, while
`Gap212.Sieve.NuDenominator` and `Gap212.Sieve.NumeratorAsymptotic` are stated against `scale`;
this identity converts between the two. Note the index shift: `scale` is indexed by the number of
coordinates `k` and `calC` by `k - 1`.

## Main results

* `Gap212.Sieve.scale_succ_eq_calC`: `scale (m+1) x = calC m x`.
* `Gap212.Sieve.calC_eq_scale_succ`: the same, the other way round.
-/

@[expose] public section

namespace Gap212.Sieve

/-- **The scale at `m + 1` coordinates is `𝓒_x` at `m`.** True by `rfl`: the two definitions are
the same term, `(m+1) - 1` reducing to `m`.

`Gap212.Sieve.scale` counts coordinates, while `Gap212.GPY.calC` counts one fewer; in dimension
`k = 45` this reads `scale 45 x = calC 44 x`. -/
theorem scale_succ_eq_calC (m : ℕ) (x : ℝ) : scale (m + 1) x = Gap212.GPY.calC m x := rfl

/-- **`𝓒_x` at `m` is the scale at `m + 1` coordinates**, the reverse direction of
`Gap212.Sieve.scale_succ_eq_calC`, for rewriting a conclusion stated with `calC` into the `scale`
spelling. -/
theorem calC_eq_scale_succ (m : ℕ) (x : ℝ) : Gap212.GPY.calC m x = scale (m + 1) x := rfl

end Gap212.Sieve
