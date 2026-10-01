/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.MoebiusReciprocalAbel
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Log-power decay of the truncated Möbius partial sum

`Gap212.Sieve.MoebiusReciprocalAbel` evaluates the *damped* integral
`∫_1^∞ S_q(w) w^{-s-1} dw = g_q(s)/s → q/φ(q)` as `s → 0⁺`, with
`S_q(w) = ∑_{f ≤ w, (f,q)=1} μ(f)/f`. Passing from there to the *undamped*
`∫_0^∞ S_q(exp u) du`, which is what the inner-sum asymptotics need, requires an `L¹` majorant for
`u ↦ S_q(exp u)` on `[0, ∞)`, and the elementary bounds do not supply one.

`Gap212.Sieve.MoebiusPartialSumDecay` is the majorant: an absolute `ε > 0` and a per-`q` constant
with `|S_q(w)| ≤ C_q (1 + log w)^{-1-ε}` for `w ≥ 2`. Then `|S_q(exp u)| ≤ C_q (1 + u)^{-1-ε}`,
which is integrable on `(0, ∞)`, so dominated convergence applies with no further work.

## How the decay is used

Both inner-sum asymptotics — at the weights `μ(f)/f` and `μ(f)/φ(f)` — use the decay in two
places, and each asks for a summability in `u = log w` rather than a rate:

* **the `L¹` majorant** for `u ↦ S_q(exp u)` on `(0, ∞)`, for the two dominated-convergence
  passages (`Gap212.Sieve.integral_moebiusReciprocalBelow_exp` here and
  `Gap212.Sieve.tendsto_integral_deriv_mul_moebiusReciprocalBelow_exp`). Here `|S_q| ≤ 1` is not
  integrable over a `u`-range of length
  `Θ(log x)`, `|S_q(exp u)| = O(1/u)` gives the divergent `∫_1^{T log x} du/u = log(T log x)`, and
  even `|S_q(exp u)| = o(1/u)` gives `o(log(T log x))`, which still diverges. Any `1/u^{1+ε}` is
  integrable, and that is all this step needs.
* **the truncation term**, `Gap212.Sieve.tendsto_integral_truncation_error`, whose bound is the
  decay evaluated at `w = B/q ≥ x^{β/2}` times the length `T log x` of the `u`-range. It needs
  `log x · D(x^{β/2}) → 0` for the bound `D`, i.e. `(log w) · D(w) → 0` — so `O(1/log w)` fails
  here too, by a bounded-but-not-vanishing margin.

A decreasing `L¹` majorant `h` satisfies `u h(u) → 0` automatically (`(u/2) h(u) ≤ ∫_{u/2}^u h`),
so the first requirement implies the second. `(1 + log w)^{-1-ε}` is the concrete decreasing
integrable bound stated here; `Gap212.Sieve.moebiusPartialSumDecay_of_subexp` shows that the bound
`exp(-c√(log w))` implies it.

## The proof

`Gap212.Sieve.moebiusPartialSumDecay` (`Gap212.Sieve.MoebiusDecay`) proves it at `ε = 1`.

By partial summation `S_q(w) = M_q(w)/w + ∫_1^w M_q(t) t^{-2} dt`, so `|S_q(w)| ≪ (log w)^{-1-ε}`
asks for `M_q(t) ≪ t (log t)^{-2-ε}`, a saving in the Möbius summatory function. The rate comes
from the error-term prime number theorem `PrimeNumberTheoremAnd.MediumPNT`,
`∃ c > 0, (Chebyshev.psi - id) =O[atTop] fun x => x * exp (-c * log x ^ (1/10))`, and
`exp(-c (log x)^{1/10})` beats every power of the logarithm. It is transferred from `ψ` to `μ`
without contour integration:

* Mertens' first theorem with a log-power rate,
  `∑_{k ≤ y, (k,q)=1} Λ(k)/k = log y + c_q + O_m((1 + log y)^{-m})` for every `m`, follows from
  `MediumPNT` by discrete Abel summation (`Gap212.Sieve.MertensVonMangoldtRate`,
  `Gap212.Sieve.MertensCoprimeCorrection`).
* The renewal identity
  `S_q(x) log x = -∑_{n ≤ x} (μ(n)/n) (W_q(x/n) - log(x/n))`
  (`Gap212.Sieve.summatory_mul_log`) reduces the Möbius rate to the `Λ` rate in the same
  coprimality class. It comes from `μ * Λ = -(μ ⬝ log)` and the two ways of summing over the
  hyperbola `mn ≤ x`.
* Summation by parts over a short range. Bounding the renewal sum absolutely gives only
  `S_q(w) = O(1/log w)`, because the terms with `n` close to `x` see `W_q` at a bounded argument,
  where the deviation is only `O(1)`. Over that range the partial sums of `μ(n)/n` are differences
  of `S_q` at arguments of size `x`, hence small by induction, while the deviation has total
  variation only `O(√(log x))`. That gains `√(log x)` per step, and six steps carry the exponent
  from `-1` to `-2` (`Gap212.Sieve.RenewalBootstrap`).

## Main definitions

* `Gap212.Sieve.MoebiusPartialSumDecay`: the log-power decay of `S_q`.

## Main results

* `Gap212.Sieve.integrableOn_const_div_one_add_rpow`: `u ↦ C (1 + u)^{-1-ε}` is integrable on
  `(0, ∞)` — the majorant, and the reason the exponent must exceed `1`.
* `Gap212.Sieve.tendsto_mul_one_div_one_add_rpow`: `L (1 + aL)^{-1-ε} → 0` as `L → ∞`, the
  truncation term's rate.
* `Gap212.Sieve.moebiusPartialSumDecay_of_subexp`: the error-term prime number theorem implies this
  decay.
* `Gap212.Sieve.measurable_moebiusReciprocalBelow`: `S_q` is measurable, being a function of
  `⌊·⌋₊`.
* `Gap212.Sieve.exists_moebiusReciprocalBelow_decay`: the decay valid from `w ≥ 1` rather than
  `w ≥ 2`, with a positive constant.
* `Gap212.Sieve.integral_moebiusReciprocalBelow_exp`: the undamped Abel integral,
  `∫_0^∞ S_q(exp u) du = q/φ(q)`.
-/

@[expose] public section

open ArithmeticFunction Filter MeasureTheory Real Set Topology
open scoped ArithmeticFunction.Moebius

namespace Gap212.Sieve

/-- **Log-power decay of the truncated Möbius partial sum.** There are an absolute `ε > 0` and a
constant `C_q` with `|S_q(w)| ≤ C_q (1 + log w)^{-1-ε}` for `w ≥ 2`, where
`S_q(w) = ∑_{f ≤ w, (f,q)=1} μ(f)/f`.

It is proved at `ε = 1` as `Gap212.Sieve.moebiusPartialSumDecay` in `Gap212.Sieve.MoebiusDecay`; the
two inner-sum asymptotics take it as a hypothesis.

The `1 +` in the denominator keeps the bound finite at `w = 1`; for `w ≥ 2` the form is
`(log w)^{-1-ε}` up to the constant `(1 + 1/log 2)^{1+ε}`. It is weaker than the bound
`exp(-c√(log w))` (`Gap212.Sieve.moebiusPartialSumDecay_of_subexp`) and stronger than `O(1/log w)`
and `o(1/log w)`, neither of which suffices for the inner-sum asymptotics. -/
@[gap212 "lem_moebius_partial_sum_decay"]
def MoebiusPartialSumDecay : Prop :=
  ∃ ε > (0 : ℝ), ∀ q : ℕ, 1 ≤ q → ∃ C : ℝ, ∀ w : ℝ, 2 ≤ w →
    |moebiusReciprocalBelow q w| ≤ C / (1 + Real.log w) ^ (1 + ε)

/-! ### The log-power majorant -/

/-- `(1 + u)^{1+ε} > 0` for `u ≥ 0`: the denominators below are positive, which `positivity` cannot
see on its own because an `rpow` with a negative base can be negative. -/
theorem one_add_rpow_pos {ε u : ℝ} (hu : 0 ≤ u) : (0 : ℝ) < (1 + u) ^ (1 + ε) :=
  Real.rpow_pos_of_pos (by linarith) _

/-- `(1 + u)^{-1-ε} ≤ 1` for `u ≥ 0`: the majorant is bounded, which is what turns the decay into
the crude bound `|S_q| ≤ C_q` used on the truncated range. -/
theorem one_div_one_add_rpow_le_one {ε u : ℝ} (hε : 0 < ε) (hu : 0 ≤ u) :
    1 / (1 + u) ^ (1 + ε) ≤ 1 :=
  div_le_one_of_le₀ (Real.one_le_rpow (by linarith) (by linarith)) (one_add_rpow_pos hu).le

/-- `(1 + u)^{-1-ε} ≤ u^{-1-ε}` for `u > 1`. -/
theorem one_div_one_add_rpow_le_rpow {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : 1 < u) :
    1 / (1 + u) ^ (1 + ε) ≤ u ^ (-(1 + ε)) := by
  have h0 : (0 : ℝ) < u := by linarith
  rw [Real.rpow_neg h0.le, ← one_div]
  gcongr
  linarith

/-- **`u ↦ C (1 + u)^{-1-ε}` is integrable on `(0, ∞)`**, for `ε > 0`: bounded near `0`, and
dominated by `u^{-1-ε}` beyond `1`, where `-1-ε < -1`. At `ε = 0` the comparison function is
`1/u`, whose integral over the `u`-range `[1, T log x]` is `log(T log x)`. -/
theorem integrableOn_const_div_one_add_rpow {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    IntegrableOn (fun u : ℝ => C / (1 + u) ^ (1 + ε)) (Ioi (0 : ℝ)) := by
  have hmeas : Measurable fun u : ℝ => 1 / (1 + u) ^ (1 + ε) := by fun_prop
  have h1 : IntegrableOn (fun u : ℝ => 1 / (1 + u) ^ (1 + ε)) (Ioc (0 : ℝ) 1) := by
    refine Integrable.mono' (g := fun _ : ℝ => (1 : ℝ))
      (integrableOn_const (by simp [Real.volume_Ioc])) hmeas.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one (one_add_rpow_pos hu.1.le).le)]
    exact one_div_one_add_rpow_le_one hε hu.1.le
  have h2 : IntegrableOn (fun u : ℝ => 1 / (1 + u) ^ (1 + ε)) (Ioi (1 : ℝ)) := by
    refine Integrable.mono' (g := fun u : ℝ => u ^ (-(1 + ε)))
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos) hmeas.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg zero_le_one (one_add_rpow_pos (zero_lt_one.trans hu).le).le)]
    exact one_div_one_add_rpow_le_rpow hε hu
  have h : IntegrableOn (fun u : ℝ => C * (1 / (1 + u) ^ (1 + ε))) (Ioc 0 1 ∪ Ioi 1) :=
    (h1.union h2).const_mul C
  simpa only [mul_one_div, Ioc_union_Ioi_eq_Ioi zero_le_one] using h

/-- `L (1 + aL)^{-1-ε} → 0` as `L → ∞`, for `a, ε > 0`: the rate at which the truncation error of
the inner sum dies, the factor `L = log x` coming from the length of the `u`-range and the
denominator from the decay at `w = B/q ≥ x^{β/2}`. The limit is `0` because `ε > 0`; at `ε = 0` it
would be the nonzero constant `1/a`. -/
theorem tendsto_mul_one_div_one_add_rpow {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    Tendsto (fun L : ℝ => L * (1 / (1 + a * L) ^ (1 + ε))) atTop (nhds 0) := by
  have hbd : Tendsto (fun L : ℝ => a ^ (-(1 + ε)) * L ^ (-ε)) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop hε).const_mul (a ^ (-(1 + ε)))
  refine squeeze_zero' ?_ ?_ hbd
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    have := one_add_rpow_pos (ε := ε) (u := a * L) (by positivity)
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    calc L * (1 / (1 + a * L) ^ (1 + ε)) ≤ L * (1 / (a * L) ^ (1 + ε)) := by gcongr; linarith
      _ = a ^ (-(1 + ε)) * L ^ (-ε) := by
        rw [Real.mul_rpow ha.le hL.le, Real.rpow_neg ha.le, Real.rpow_neg hL.le,
          Real.rpow_add hL, Real.rpow_one]
        field_simp

/-! ### The error-term prime number theorem implies this decay -/

/-- `exp(-t) ≤ 256/t⁴` for `t > 0`, from the Taylor bound `t⁴/4! ≤ exp t`. -/
theorem exp_neg_le_of_pos {t : ℝ} (ht : 0 < t) : exp (-t) ≤ 256 / t ^ 4 := by
  have h := Real.pow_div_factorial_le_exp t ht.le 4
  rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (exp_pos t) (by positivity)]
  norm_num [Nat.factorial] at h
  linarith [exp_pos t]

/-- `exp(-c√t) ≤ K (1 + t)^{-2}` on `t ≥ 0`, for one `K > 0` depending only on `c`: the
sub-exponential rate dominates the log-power one at `ε = 1`. Beyond `t = 1` this is
`exp(-c√t) ≤ 256/(c⁴t²)` and `(1 + t)² ≤ 4t²`; below it, `exp(-c√t) ≤ 1` and `(1 + t)² ≤ 4`. -/
theorem exists_const_exp_neg_mul_sqrt_le {c : ℝ} (hc : 0 < c) :
    ∃ K > (0 : ℝ), ∀ t : ℝ, 0 ≤ t → exp (-(c * √t)) ≤ K / (1 + t) ^ (1 + (1 : ℝ)) := by
  refine ⟨max 4 (1024 / c ^ 4), by positivity, fun t ht => ?_⟩
  rw [one_add_one_eq_two, Real.rpow_two, le_div_iff₀ (by positivity)]
  rcases le_or_gt t 1 with hle | hgt
  · have h1 : exp (-(c * √t)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.2 (by positivity))
    exact le_max_of_le_left <|
      (mul_le_mul h1 (by nlinarith) (by positivity) zero_le_one).trans_eq (one_mul 4)
  · have ht0 : (0 : ℝ) < t := by linarith
    have h1 := exp_neg_le_of_pos (mul_pos hc (Real.sqrt_pos.mpr ht0))
    rw [mul_pow, show √t ^ 4 = (√t ^ 2) ^ 2 by ring, Real.sq_sqrt ht0.le] at h1
    refine le_max_of_le_right ?_
    calc exp (-(c * √t)) * (1 + t) ^ 2 ≤ 256 / (c ^ 4 * t ^ 2) * (4 * t ^ 2) :=
          mul_le_mul h1 (by nlinarith) (by positivity) (by positivity)
      _ = 1024 / c ^ 4 := by field_simp; ring

/-- **The error-term prime number theorem implies this decay**, at `ε = 1`: the hypothesis stated
here is *weaker* than `|S_q(w)| ≤ C_q exp(-c√(log w))`. -/
theorem moebiusPartialSumDecay_of_subexp
    (h : ∃ c > (0 : ℝ), ∀ q : ℕ, 1 ≤ q → ∃ C : ℝ, ∀ w : ℝ, 2 ≤ w →
      |moebiusReciprocalBelow q w| ≤ C * exp (-(c * √(Real.log w)))) :
    MoebiusPartialSumDecay := by
  obtain ⟨c, hc, hq⟩ := h
  obtain ⟨K, hK, hKbd⟩ := exists_const_exp_neg_mul_sqrt_le hc
  refine ⟨1, one_pos, fun q hq1 => ?_⟩
  obtain ⟨C, hC⟩ := hq q hq1
  refine ⟨max C 0 * K, fun w hw => ?_⟩
  rw [mul_div_assoc]
  exact (hC w hw).trans <| mul_le_mul (le_max_left _ _)
    (hKbd _ (Real.log_nonneg (by linarith))) (exp_pos _).le (le_max_right _ _)

/-! ### Measurability and the elementary bound below `2` -/

/-- `S_q` is measurable: it depends on its real argument only through `⌊·⌋₊`. -/
theorem measurable_moebiusReciprocalBelow (q : ℕ) :
    Measurable (moebiusReciprocalBelow q) :=
  (measurable_from_top (f := fun n : ℕ => ∑ f ∈ (Finset.Icc 1 n).filter (Nat.Coprime · q),
    (μ f : ℝ) / f)).comp Nat.measurable_floor

/-- `|S_q(t)| ≤ 1` for `t < 2`: the only index in range is `f = 1`. -/
theorem abs_moebiusReciprocalBelow_le_one (q : ℕ) {t : ℝ} (ht : t < 2) :
    |moebiusReciprocalBelow q t| ≤ 1 := by
  have hsub : coprimeBelow q t ⊆ {1} := fun f hf => by
    obtain ⟨hf0, hle, -⟩ := mem_coprimeBelow.mp hf
    have : f < 2 := by exact_mod_cast hle.trans_lt ht
    exact Finset.mem_singleton.2 (by lia)
  calc |moebiusReciprocalBelow q t| ≤ ∑ f ∈ coprimeBelow q t, |(μ f : ℝ) / (f : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f ∈ ({1} : Finset ℕ), |(μ f : ℝ) / (f : ℝ)| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _
    _ = 1 := by simp

/-! ### The decay from `w ≥ 1` -/

/-- **The decay, normalised.** From `Gap212.Sieve.MoebiusPartialSumDecay` one gets a positive
constant and the bound from `w ≥ 1` rather than `w ≥ 2`: below `2` the sum is `μ(1)/1 = 1`, which
the constant `(1 + log 2)^{1+ε}` absorbs. -/
theorem exists_moebiusReciprocalBelow_decay (hdecay : MoebiusPartialSumDecay) {q : ℕ}
    (hq : 1 ≤ q) : ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ w : ℝ, 1 ≤ w →
      |moebiusReciprocalBelow q w| ≤ C / (1 + Real.log w) ^ (1 + ε) := by
  obtain ⟨ε, hε, hq'⟩ := hdecay
  obtain ⟨C, hC⟩ := hq' q hq
  refine ⟨ε, hε, max C ((1 + Real.log 2) ^ (1 + ε)),
    lt_max_of_lt_right (one_add_rpow_pos (Real.log_nonneg one_le_two)), fun w hw => ?_⟩
  have hlw : 0 ≤ Real.log w := Real.log_nonneg hw
  have hwpos : (0 : ℝ) < (1 + Real.log w) ^ (1 + ε) := one_add_rpow_pos hlw
  rcases le_or_gt 2 w with h2 | h2
  · refine (hC w h2).trans ?_
    gcongr
    exact le_max_left _ _
  · refine (abs_moebiusReciprocalBelow_le_one q h2).trans ?_
    rw [le_div_iff₀ hwpos, one_mul]
    exact le_max_of_le_right <| Real.rpow_le_rpow (by linarith)
      (by linarith [Real.log_le_log (by linarith) h2.le]) (by linarith)

/-- The decay at `w = exp u`, the form the `u`-integral uses:
`|S_q(exp u)| ≤ C (1 + u)^{-1-ε}`. -/
theorem abs_moebiusReciprocalBelow_exp_le {q : ℕ} {ε C : ℝ}
    (h : ∀ w : ℝ, 1 ≤ w → |moebiusReciprocalBelow q w| ≤ C / (1 + Real.log w) ^ (1 + ε))
    {u : ℝ} (hu : 0 ≤ u) : |moebiusReciprocalBelow q (exp u)| ≤ C / (1 + u) ^ (1 + ε) := by
  simpa only [Real.log_exp] using h (exp u) (Real.one_le_exp hu)

/-! ### The undamped Abel integral -/

/-- The change of variables `w = exp u` on the Mellin integral: for `s > 0`,
`∫_1^∞ S_q(w) w^{-s-1} dw = ∫_0^∞ S_q(exp u) e^{-su} du`. -/
theorem integral_moebiusReciprocalBelow_exp_rpow (q : ℕ) (s : ℝ) :
    (∫ u in Ioi (0 : ℝ), moebiusReciprocalBelow q (exp u) * exp (-(s * u)))
      = ∫ w in Ioi (1 : ℝ), moebiusReciprocalBelow q w * w ^ (-s - 1) := by
  rw [← Real.exp_zero, ← integral_comp_exp_Ioi]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [Real.exp_zero, smul_eq_mul, Real.rpow_def_of_pos (exp_pos u), Real.log_exp, mul_left_comm,
    ← Real.exp_add]
  ring_nf

/-- **The undamped Abel integral**: `∫_0^∞ S_q(exp u) du = q/φ(q)`, for every `q ≥ 1`.

`Gap212.Sieve.tendsto_integral_moebiusReciprocalBelow_rpow` gives the *damped* integral's limit,
which is Abel summability and strictly weaker. The decay supplies the majorant `C (1 + u)^{-1-ε}`,
integrable on `(0, ∞)`, so dominated convergence as `s → 0⁺` identifies the two. -/
theorem integral_moebiusReciprocalBelow_exp (hdecay : MoebiusPartialSumDecay) {q : ℕ}
    (hq : 1 ≤ q) :
    (∫ u in Ioi (0 : ℝ), moebiusReciprocalBelow q (exp u)) = (q : ℝ) / (q.totient : ℝ) := by
  obtain ⟨ε, hε, C, hC, hbd⟩ := exists_moebiusReciprocalBelow_decay hdecay hq
  have hmeas (s : ℝ) : AEStronglyMeasurable
      (fun u : ℝ => moebiusReciprocalBelow q (exp u) * exp (-(s * u)))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (((measurable_moebiusReciprocalBelow q).comp measurable_exp).mul
      (by fun_prop)).aestronglyMeasurable
  have hlim : Tendsto (fun s : ℝ => ∫ u in Ioi (0 : ℝ),
      moebiusReciprocalBelow q (exp u) * exp (-(s * u))) (𝓝[>] (0 : ℝ))
      (nhds (∫ u in Ioi (0 : ℝ), moebiusReciprocalBelow q (exp u))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => C / (1 + u) ^ (1 + ε)) (Eventually.of_forall hmeas) ?_
      (integrableOn_const_div_one_add_rpow hε C) ?_
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (exp_pos _).le]
      exact (mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.mpr
        (neg_nonpos.2 (by positivity)))).trans (abs_moebiusReciprocalBelow_exp_le hbd hu.le)
    · refine ae_of_all _ fun u => ?_
      have : Continuous fun s : ℝ => moebiusReciprocalBelow q (exp u) * exp (-(s * u)) := by
        fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hlim <| (tendsto_integral_moebiusReciprocalBelow_rpow hq).congr
    fun s => (integral_moebiusReciprocalBelow_exp_rpow q s).symm

end Gap212.Sieve
