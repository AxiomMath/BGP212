/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Notation
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Compact
public meta import Gap212.Attr

/-!
# Logarithmic bookkeeping, and uniformity on a chamber

Two kinds of step the assembly leans on repeatedly. The first is that `log_x` is additive on
products, which is what lets a modulus's logarithmic size be split across its factorization. The
second is that a strict inequality holding pointwise on a compact set holds with a uniform margin,
which is what makes the positive-level estimates apply on a whole chamber rather than one point at
a time.

## Main results

* `Gap212.Auxiliary.logx_mul`: `log_x` is additive on products of nonzero reals.
* `Gap212.Auxiliary.logx_le_of_le_rpow`: a factor below `x^δ` has `log_x` below `δ`.
* `Gap212.Auxiliary.uniform_margin_on_compact`: a continuous function strictly negative on a
  compact set is bounded away from zero there.
-/

@[expose] public section

namespace Gap212.Auxiliary

open Real Gap212.Notation

/-- **`log_x` is additive on products.** This is what splits a generated modulus's logarithmic size
into the contributions of its rough factors and the primes of its smooth part: applied along the
factorization `q = e e' ∏ fᵢ ∏ f'ᵢ`, it gives the decomposition the extraction lemmas start
from. -/
@[gap212 "lem_modulus_log_decomposition"]
theorem logx_mul {x a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    logx x (a * b) = logx x a + logx x b := by
  unfold logx
  rw [Real.log_mul ha hb]
  ring

/-- **A factor below `x^δ` has logarithmic size below `δ`.** For `x > 1` the map `log_x` is
monotone, so the smooth part's primes — each smaller than `x^δ` by definition of smoothness —
contribute less than `δ` each. That is precisely what makes them usable as small change: inserting
one moves a partial product by less than the width of any target window. -/
@[gap212 "lem_smooth_prime_logs"]
theorem logx_le_of_le_rpow {x p δ : ℝ} (hx : 1 < x) (hp : 0 < p) (h : p ≤ x ^ δ) :
    logx x p ≤ δ := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hle : Real.log p ≤ δ * Real.log x := by
    calc Real.log p ≤ Real.log (x ^ δ) := Real.log_le_log hp h
      _ = δ * Real.log x := Real.log_rpow (by linarith) δ
  unfold logx
  rw [div_le_iff₀ hlogx]
  exact hle

/-- **A uniform margin on a compact chamber.** A continuous function strictly negative at every
point of a nonempty compact set is bounded above by some `-ε` with `ε > 0` throughout.

This is what turns the positive-level estimates' strict parameter inequalities into the uniform
slack their implied constants need: the inequalities are affine, hence continuous, and each chamber
is compact by construction, so one `ε` serves the whole chamber rather than one point. -/
theorem uniform_margin_on_compact {α : Type*} [TopologicalSpace α] {K : Set α} {g : α → ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (hg : ContinuousOn g K)
    (hneg : ∀ p ∈ K, g p < 0) :
    ∃ ε > (0 : ℝ), ∀ p ∈ K, g p ≤ -ε := by
  obtain ⟨p₀, hp₀K, hp₀max⟩ := hK.exists_isMaxOn hne hg
  refine ⟨-g p₀, by simpa using hneg p₀ hp₀K, ?_⟩
  intro p hp
  have := hp₀max hp
  simpa using this

end Gap212.Auxiliary
