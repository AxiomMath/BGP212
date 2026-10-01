/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.Containment
public import Gap212.Routing.PointABridge

/-!
# Windows scaled by a power of the modulus

The Type IIc moduli set is the only one whose windows depend on the modulus itself: `u` is sought
in a range scaled by `d⁻¹` and `d₁` in one scaled by `r² d⁻⁴`. Accordingly
`Gap212.Routing.mem_moduliIIc_of_qgen` states those two window conditions with `(q : ℝ)` appearing
explicitly, deliberately leaving how `log_x q` relates to the level for the caller to supply.

This module supplies it. Given a dyadic localization `x^s ≤ q ≤ x^t`, a window scaled by `q^{-k}`
becomes a window in pure exponents:

    x^u / q^k ≤ x^{u - sk},        x^{u - tk} ≤ x^u / q^k.

So the four hypotheses `hlo₂`, `hhi₂`, `hlo₃`, `hhi₃` of the Type IIc containment reduce to four
inequalities between exponents, at `k = 1` and `k = 4`. That is the last structural obstruction in
the Type IIc route; what remains after it is the same trivial-partition arithmetic as the others.

## Why the localization is needed at all, and where it comes from

`Qgen` bounds a modulus only by `q ≤ x`. The upper bound the Type IIc windows need is sharper:
`Gap212.Extraction.qgen_le` gives `q ≤ x^{(1-ε₀)(A_j + A_{j'})}`, and at Point A
`A_j + A_{j'} = ϑ = 513/1000`, so `q ≤ x^{513/1000}` — exactly `x^{1/2 + 2ω}` at the maximal level.
The lower bound is the `hqbig` hypothesis every route already carries. So both ends are available;
they just have to be converted, and `k = 4` means a slack of `ε` in the exponent costs `4ε` in the
window.

## Main results

* `Gap212.Routing.rpow_pow_le`: `x^{sk} ≤ q^k` from `x^s ≤ q`.
* `Gap212.Routing.div_pow_lt_rpow`, `rpow_lt_div_pow`: the two window conversions, in the strict
  form the containment asks for.
* `Gap212.Routing.qgen_le_pointA`: `q ≤ x^{513/1000}` for a Point A generated modulus.
-/

@[expose] public section

namespace Gap212.Routing

open Real Gap212.PointA Gap212.Packing Gap212.Extraction

/-! ## Powers of a localized modulus -/

/-- From `x^s ≤ q` follows `x^{sk} ≤ q^k`. -/
theorem rpow_pow_le {x s : ℝ} (hx0 : 0 < x) (q : ℕ) (k : ℕ) (hq : x ^ s ≤ (q : ℝ)) :
    x ^ (s * k) ≤ (q : ℝ) ^ k := by
  rw [Real.rpow_mul_natCast hx0.le]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hx0.le s) hq k

/-- From `q ≤ x^t` follows `q^k ≤ x^{tk}`. -/
theorem pow_le_rpow {x t : ℝ} (hx0 : 0 < x) (q : ℕ) (k : ℕ) (hq : (q : ℝ) ≤ x ^ t) :
    (q : ℝ) ^ k ≤ x ^ (t * k) := by
  rw [Real.rpow_mul_natCast hx0.le]
  exact pow_le_pow_left₀ q.cast_nonneg hq k

/-! ## The two window conversions -/

/-- **Upper conversion.** A window scaled by `q^{-k}` sits below `x^a` as soon as the exponent
does, where the modulus is localized from below by `x^s ≤ q`. -/
theorem div_pow_lt_rpow {x u s a : ℝ} (hx : 1 < x) {q : ℕ} (k : ℕ)
    (hq : x ^ s ≤ (q : ℝ)) (hlt : u - s * k < a) :
    x ^ u / (q : ℝ) ^ k < x ^ a := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  refine lt_of_le_of_lt ?_ ((Real.rpow_lt_rpow_left_iff hx).mpr hlt)
  rw [Real.rpow_sub hx0]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) (Real.rpow_pos_of_pos hx0 _)
    (rpow_pow_le hx0 q k hq)

/-- **Lower conversion.** A window scaled by `q^{-k}` sits above `x^b` as soon as the exponent
does, where the modulus is localized from above by `q ≤ x^t`. -/
theorem rpow_lt_div_pow {x u t b : ℝ} (hx : 1 < x) {q : ℕ} (k : ℕ)
    (hq : (q : ℝ) ≤ x ^ t) (hqpos : 0 < (q : ℝ)) (hlt : b < u - t * k) :
    x ^ b < x ^ u / (q : ℝ) ^ k := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  refine ((Real.rpow_lt_rpow_left_iff hx).mpr hlt).trans_le ?_
  rw [Real.rpow_sub hx0]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) (pow_pos hqpos k)
    (pow_le_rpow hx0 q k hq)

/-- The `k = 1` case, with the `Nat`-cast exponent already simplified away. -/
theorem div_lt_rpow {x u s a : ℝ} (hx : 1 < x) {q : ℕ}
    (hq : x ^ s ≤ (q : ℝ)) (hlt : u - s < a) :
    x ^ u / (q : ℝ) < x ^ a := by
  simpa using div_pow_lt_rpow hx 1 hq (by simpa using hlt)

/-- The `k = 1` case of the lower conversion. -/
theorem rpow_lt_div {x u t b : ℝ} (hx : 1 < x) {q : ℕ}
    (hq : (q : ℝ) ≤ x ^ t) (hqpos : 0 < (q : ℝ)) (hlt : b < u - t) :
    x ^ b < x ^ u / (q : ℝ) := by
  simpa using rpow_lt_div_pow hx 1 hq hqpos (by simpa using hlt)

/-- The `k = 4` case, as the third Type IIc window needs it. -/
theorem div_pow4_lt_rpow {x u s a : ℝ} (hx : 1 < x) {q : ℕ}
    (hq : x ^ s ≤ (q : ℝ)) (hlt : u - 4 * s < a) :
    x ^ u / (q : ℝ) ^ 4 < x ^ a :=
  div_pow_lt_rpow hx 4 hq (by push_cast; linarith)

/-- The `k = 4` case of the lower conversion. -/
theorem rpow_lt_div_pow4 {x u t b : ℝ} (hx : 1 < x) {q : ℕ}
    (hq : (q : ℝ) ≤ x ^ t) (hqpos : 0 < (q : ℝ)) (hlt : b < u - 4 * t) :
    x ^ b < x ^ u / (q : ℝ) ^ 4 :=
  rpow_lt_div_pow hx 4 hq hqpos (by push_cast; linarith)

/-! ## The localization available at Point A -/

/-- **A Point A generated modulus is at most `x^{513/1000}`.** That exponent is `ϑ`, and it is
exactly `1/2 + 2ω` at the maximal level — so the upper end of the dyadic localization the Type IIc
windows need is already implied by membership in `Qgen`. -/
theorem qgen_le_pointA {x ε₀ : ℝ} {j j' : Fin gap212ParamsPointA.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 ≤ ε₀) (hq : q ∈ Qgen gap212ParamsPointA x j j' m m' ε₀) :
    (q : ℝ) ≤ x ^ (513 / 1000 : ℝ) := by
  refine (qgen_le hx hq).trans ((Real.rpow_le_rpow_left_iff hx).mpr ?_)
  rw [gap212Params_A_succ j, gap212Params_A_succ j']
  nlinarith [hε₀]

/-- `1/2 + 2ω = 513/1000`: the level and the cap agree. -/
theorem half_add_two_ω : 1 / 2 + 2 * ((ω : ℚ) : ℝ) = 513 / 1000 := by
  rw [cast_ω]; norm_num

end Gap212.Routing
