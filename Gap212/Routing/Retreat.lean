/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Routing.Union

/-!
# The modulus retreat `ε₀`, and why small values suffice

`Gap212.HasEquidistributionOverQstarFamily` asks for its bound at **every** `ε₀ >
0`. The five estimates
supply theirs only for sufficiently small `ε`: `Gap212.HasEquidistributionFamily` opens with
`∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀`. That is the quantifier mismatch standing between the estimates and the
arithmetic certificate, and it is resolved here rather than inside any one route.

## The retreat shrinks the family

`ε₀` enters `Qgen` only through caps of the form `x^{(1-ε₀)C}`. Increasing it therefore *tightens*
every cap, so the generated family gets **smaller**:

    ε₀ ≤ ε₀'  ⟹  Qgen(ε₀') ⊆ Qgen(ε₀).

So the statement is hardest at small `ε₀` and free at large ones. Given any `ε₀`, either it is
already small enough to use the estimates directly, or it exceeds the threshold — and then the
family it generates is contained in the one at the threshold, where the bound is available. That is
`Gap212.Routing.hasEquidistributionOverQstar_of_small`.

The direction is worth pinning down, being the opposite of the naive guess: a *larger* retreat
sounds like a weaker hypothesis on the moduli and hence a bigger family, but `1 - ε₀` multiplies
the exponent, so it is the other way round.

## What the antitonicity needs

Only that the four capped quantities are nonnegative: the two rough-product caps `B_{j,m}`,
`B_{j',m'}` and the two mixed caps `A_j - ε`, `A_{j'} + ε`. For a general `SupportParams` the `B`
row is unconstrained at `m = 0`, so these are taken as hypotheses; at Point A all four are numerals
and `Gap212.Routing.gap212Params_caps_nonneg` discharges them.

## Main results

* `Gap212.Routing.qgen_antitone`, `qstar_antitone`: the family shrinks as the retreat grows.
* `Gap212.Routing.hasEquidistributionOverQstar_of_small`: small `ε₀` suffices.
* `Gap212.Routing.gap212Params_caps_nonneg`: the four caps at Point A.
-/

@[expose] public section

namespace Gap212.Routing

open Finset Real

/-! ## The generated family shrinks as the retreat grows -/

/-- **`Qgen` is antitone in the retreat.** A larger `ε₀` tightens every cap `x^{(1-ε₀)C}`, so it
generates fewer moduli. -/
theorem qgen_antitone {p : SupportParams} {x ε₀ ε₀' : ℝ} {j j' : Fin p.n} {m m' : ℕ}
    (hx : 1 < x) (hle : ε₀ ≤ ε₀')
    (hB : 0 ≤ p.B j m) (hB' : 0 ≤ p.B j' m')
    (hA : 0 ≤ p.A j.succ - p.ε) (hA' : 0 ≤ p.A j'.succ + p.ε) :
    Qgen p x j j' m m' ε₀' ⊆ Qgen p x j j' m m' ε₀ := by
  intro q hq
  obtain ⟨e, e', f, f', hqeq, hq1, hqx, hf, hf', hef, hef', hsm, hlo, hlo'⟩ := hq
  have hstep : ∀ C : ℝ, 0 ≤ C → x ^ ((1 - ε₀') * C) ≤ x ^ ((1 - ε₀) * C) := by
    intro C hC
    refine (Real.rpow_le_rpow_left_iff hx).mpr ?_
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) hC]
  exact ⟨e, e', f, f', hqeq, hq1, hqx,
    le_trans hf (hstep _ hB), le_trans hf' (hstep _ hB'),
    le_trans hef (hstep _ hA), le_trans hef' (hstep _ hA'), hsm, hlo, hlo'⟩

/-- **`Qstar` is antitone in the retreat**, being a union of the `Qgen`. -/
theorem qstar_antitone {p : SupportParams} {x ε₀ ε₀' : ℝ}
    (hx : 1 < x) (hle : ε₀ ≤ ε₀')
    (hcaps : ∀ (j j' : Fin p.n) (m m' : ℕ),
      0 ≤ p.B j m ∧ 0 ≤ p.B j' m' ∧ 0 ≤ p.A j.succ - p.ε ∧ 0 ≤ p.A j'.succ + p.ε) :
    Qstar p x ε₀' ⊆ Qstar p x ε₀ := by
  intro q hq
  rw [Qstar, Set.mem_iUnion] at hq
  obtain ⟨j, hj⟩ := hq
  rw [Set.mem_iUnion] at hj
  obtain ⟨j', hj'⟩ := hj
  rw [Set.mem_iUnion₂] at hj'
  obtain ⟨m, hmK, hm⟩ := hj'
  rw [Set.mem_iUnion₂] at hm
  obtain ⟨m', hm'K, hm'⟩ := hm
  obtain ⟨hB, hB', hA, hA'⟩ := hcaps j j' m m'
  refine Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨j', Set.mem_iUnion₂.mpr ⟨m, hmK, ?_⟩⟩⟩
  exact Set.mem_iUnion₂.mpr ⟨m', hm'K, qgen_antitone hx hle hB hB' hA hA' hm'⟩

/-! ## Small retreats suffice -/

open Classical in
/-- **The quantifier bridge.** `HasEquidistributionOverQstarFamily` demands its
bound at every `ε₀ > 0`,
while the estimates deliver only at small `ε`. It is enough to have it below some positive
threshold: above the threshold the generated family is *contained* in the one at the threshold, by
`qstar_antitone`, and the discrepancy sum only shrinks.

This is the step that lets a route quote `Gap212.HasEquidistributionFamily`, whose leading
`∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀` is exactly the hypothesis below. -/
theorem hasEquidistributionOverQstar_of_small {p : SupportParams} {f : ℕ → ℝ → ℂ} {t : ℝ}
    (ht : 0 < t)
    (hcaps : ∀ (j j' : Fin p.n) (m m' : ℕ),
      0 ≤ p.B j m ∧ 0 ≤ p.B j' m' ∧ 0 ≤ p.A j.succ - p.ε ∧ 0 ≤ p.A j'.succ + p.ε)
    (h : ∀ ε₀ ∈ Set.Ioo (0 : ℝ) t, ∀ A > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ x : ℝ, 1 < x → ∀ a : ℕ, CoprimeBelow a x →
        ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar p x ε₀ ∧ Squarefree q}, discrepancy f x a q
          ≤ c * x / (Real.log x) ^ A) :
    HasEquidistributionOverQstarFamily p f := by
  classical
  intro ε₀ hε₀ A hA
  by_cases hsmall : ε₀ < t
  · -- Already below the threshold: quote the hypothesis directly.
    exact h ε₀ ⟨hε₀, hsmall⟩ A hA
  · -- At or above it: the family is contained in the one at `t/2`.
    obtain ⟨c, hc, hbound⟩ := h (t / 2) ⟨by linarith, by linarith⟩ A hA
    refine ⟨c, hc, fun x hx a ha ↦ le_trans ?_ (hbound x hx a ha)⟩
    refine discrepancySum_le_of_subset ?_
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, qstar_antitone hx (by linarith) hcaps hq.2.1, hq.2.2⟩

/-! ## The four caps at Point A -/

/-- At Point A all four capped quantities are nonnegative: the `B` row is `31/200` or `17/100`, and
the mixed caps are `A₁ - ε = 0.248` and `A₁ + ε = 0.265`. -/
theorem gap212Params_caps_nonneg (j j' : Fin gap212ParamsPointA.n) (m m' : ℕ) :
    0 ≤ gap212ParamsPointA.B j m ∧ 0 ≤ gap212ParamsPointA.B j' m' ∧
      0 ≤ gap212ParamsPointA.A j.succ - gap212ParamsPointA.ε ∧
      0 ≤ gap212ParamsPointA.A j'.succ + gap212ParamsPointA.ε := by
  -- Only `1 ≤ (i.succ).val` is needed, which holds for any stratum count.
  have hval : ∀ i : Fin gap212ParamsPointA.n, (1 : ℝ) ≤ ((i.succ).val : ℝ) := by
    intro i
    have h : 1 ≤ (i.succ).val := by rw [Fin.val_succ]; omega
    exact_mod_cast h
  have hB : ∀ (i : Fin gap212ParamsPointA.n) (k : ℕ), 0 ≤ gap212ParamsPointA.B i k := by
    intro i k
    change (0 : ℝ) ≤ (if k = 0 then 0 else if k ≤ 2 then 0.155 else 0.17)
    split_ifs <;> norm_num
  have hAsub : ∀ i : Fin gap212ParamsPointA.n,
      0 ≤ gap212ParamsPointA.A i.succ - gap212ParamsPointA.ε := by
    intro i
    have h := hval i
    have hrfl : gap212ParamsPointA.A i.succ - gap212ParamsPointA.ε
        = ((i.succ).val : ℝ) * 0.265 - 0.0085 - 0.0085 := rfl
    rw [hrfl]
    nlinarith
  have hAadd : ∀ i : Fin gap212ParamsPointA.n,
      0 ≤ gap212ParamsPointA.A i.succ + gap212ParamsPointA.ε := by
    intro i
    have h := hval i
    have hrfl : gap212ParamsPointA.A i.succ + gap212ParamsPointA.ε
        = ((i.succ).val : ℝ) * 0.265 - 0.0085 + 0.0085 := rfl
    rw [hrfl]
    nlinarith
  exact ⟨hB j m, hB j' m', hAsub j, hAadd j'⟩

open Classical in
/-- The bridge, specialized to Point A: no cap hypotheses to supply. -/
theorem hasEquidistributionOverQstar_of_small_pointA {f : ℕ → ℝ → ℂ} {t : ℝ} (ht : 0 < t)
    (h : ∀ ε₀ ∈ Set.Ioo (0 : ℝ) t, ∀ A > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ x : ℝ, 1 < x → ∀ a : ℕ, CoprimeBelow a x →
        ∑ q ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar gap212ParamsPointA x ε₀ ∧ Squarefree q},
          discrepancy f x a q ≤ c * x / (Real.log x) ^ A) :
    HasEquidistributionOverQstarFamily gap212ParamsPointA f :=
  hasEquidistributionOverQstar_of_small ht gap212Params_caps_nonneg h

end Gap212.Routing
