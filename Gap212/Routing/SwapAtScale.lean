/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Consequences.BundleNormalization
public import Gap212.Consequences.Basic
public import Gap212.Harman.Challenge
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public meta import Gap212.Attr

/-!
# Swapping the two convolution factors reflects the exponent

The source reduces Type II to `γ ≤ 1/2` in one sentence: "Interchanging the two convolution factors
replaces `γ` by `1-γ`, so it is enough to treat `γ ≤ 1/2`." Three things make that a step, and the
statement of the step is a *bundle-level transfer*: the reflected data are Type II data again, but
at a wider bundle `K'` depending on `K` alone.

## Commutativity

`Gap212.dconv_comm`, by the divisor involution `d ↦ n/d` — the two forms of
`Nat.sum_divisorsAntidiagonal`. It is one ingredient, not the step: it rewrites `f = α ⋆ β` as
`f = β ⋆ α` and says nothing about the scales.

## The swapped scale is not an exact power

`Gap212.TypeII` pins the exponent window on the *second* declared scale, and pins `M` only through
`M * N ≍_K x`. So the swapped pair `(N, M)` has a second scale `M` whose exponent is
`1 - γ + log_x(M N / x)`, which may exceed the window by a bounded amount. The reflected second
scale must therefore be the exact quotient `x / N`, whose exponent is `1 - γ` on the nose, and `M`
must be replaced by it. That replacement is the scale transfer
`Gap212.ConstantBundle.exists_transfer_at_comparable_scale`, at the ratio window
`(lo, hi) = (min a₋ 1, max a₊ 1)` — the commensurability endpoints of `K`, widened to straddle `1`:

* widened downwards and upwards so that the *unswapped* factor `β` also transfers, at the **same**
  scale `N` — a same-scale transfer needs `lo ≤ 1 ≤ hi`, which `K`'s own `a₋, a₊` need not satisfy;
* and `a₋ x ≤ M N ≤ a₊ x` is exactly `lo (x/N) ≤ M ≤ hi (x/N)` after dividing by `N`, which is what
  the replacement asks of the old and new scales.

This is where Type II's Siegel–Walfisz hypothesis on **both** factors is spent: after the swap the
second factor is `α`, and the estimates ask the property of whichever sequence sits second. A class
carrying it on one side only could not be swapped, which is why `Gap212.TypeII` carries it on both.

## Normalization, for the product of the new scales

The new declared scales multiply to `N * (x / N) = x` exactly, so the commensurability clause reads
`x ≍_{K'} x` — true precisely when `K'` has `a₋ ≤ 1 ≤ a₊`. That is what the normalization
`Gap212.constantBundle_flat_transfer` supplies, and it is why `K'` is the normalization of the
replacement bundle rather than the replacement bundle itself.

## The one hypothesis the source leaves implicit

`slack ≤ ξ₂`. The reflected scale `x / N` must be at least `1`, i.e. `N ≤ x`, and the only upper
bound on `N` is the window `N ≤ x^{1-ξ₂+ϵ}`; that gives `N ≤ x` exactly when `1-ξ₂+ϵ ≤ 1`. The
source's proof appeals to `γ ≤ 1-ξ₂+ϵ < 1`, which is the same assumption. It is harmless: the
development runs at `ξ₂ = 2/5` and `ϵ = 10⁻¹⁰`.

## Main results

* `Gap212.dconv_comm`: `dconv α β = dconv β α`.
* `Gap212.exists_bundle_typeII_swap_witnesses`: the reflection, with the witnesses named — from
  Type II data `(α, β, M, N)` at `K` to Type II data `(β, α, N, x/N)` at `K'`.
* `Gap212.exists_bundle_typeII_swap`: its class-level reading,
  `TypeII K x ξ₂ f → TypeII K' x ξ₂ f`.
-/

@[expose] public section

namespace Gap212

/-- **Dirichlet convolution is commutative**, by the involution `d ↦ n/d` on the divisors of `n`.

This is one ingredient of the Type II reduction `γ ↔ 1 - γ`: the hypotheses of `Gap212.TypeII` are
symmetric in the two factors, so once `f = α ⋆ β` is rewritten as `f = β ⋆ α` only the declared
scale of the first factor is left to move. It is also why `Gap212.TypeII` asks Siegel–Walfisz of
both factors and not only of the second: after the swap the second factor is `α`. -/
theorem dconv_comm (α β : ℕ → ℂ) : dconv α β = dconv β α := by
  funext n
  rw [dconv, dconv, ← Nat.sum_divisorsAntidiagonal (fun a b ↦ α a * β b),
    ← Nat.sum_divisorsAntidiagonal' (fun a b ↦ β b * α a)]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- **Swapping the factors reflects `γ`.** There is a bundle `K'` depending on `K` alone such that
Type II data `(α, β, M, N)` for `f` at `(K, x)` and `ξ₂` become Type II data `(β, α, N, x/N)` for
`f` at `(K', x)` and the same `ξ₂`. In particular the exponent of the reflected second scale is
`1 - γ` exactly, where `γ = log_x N`: that is the clause `x / N = x ^ (1 - Real.logb x N)`.

The hypotheses are the clauses of `Gap212.TypeII` at the witnesses `(α, β, M, N)` and the
conclusion is its clauses at `(β, α, N, x/N)`, the two `≥ 1` clauses on the scales included. The
witnesses are named rather than left inside the existential because the reflection's whole point is
*which* scale the swapped datum is declared at — `x / N`, not `M` — and the class-level reading
`Gap212.exists_bundle_typeII_swap` cannot say that.

`K'` is the normalization of the scale replacement at the ratio window `(min a₋ 1, max a₊ 1)`. It
depends on `K` alone: not on `x`, not on `f`, and not on `M`, `N` or `ξ₂`, all of which are
quantified after it. -/
@[gap212 "lem_typeII_symmetry_reduction"]
theorem exists_bundle_typeII_swap_witnesses (K : ConstantBundle) :
    ∃ K' : ConstantBundle, ∀ (ξ₂ x : ℝ) (f α β : ℕ → ℂ) (M N : ℝ),
      slack ≤ ξ₂ → 1 < x → 1 ≤ M → 1 ≤ N → f = dconv α β →
      K.IsCoefficientSequence α → K.IsCoefficientSequence β →
      K.LocatedAtScale α M → K.LocatedAtScale β N → K.asympEq (M * N) x →
      K.HasSiegelWalfisz α M → K.HasSiegelWalfisz β N →
      x ^ (ξ₂ - slack) ≤ N → N ≤ x ^ (1 - ξ₂ + slack) →
      1 ≤ N ∧ 1 ≤ x / N ∧ x / N = x ^ (1 - Real.logb x N) ∧ f = dconv β α ∧
        K'.IsCoefficientSequence β ∧ K'.IsCoefficientSequence α ∧
        K'.LocatedAtScale β N ∧ K'.LocatedAtScale α (x / N) ∧
        K'.asympEq (N * (x / N)) x ∧
        K'.HasSiegelWalfisz β N ∧ K'.HasSiegelWalfisz α (x / N) ∧
        x ^ (ξ₂ - slack) ≤ x / N ∧ x / N ≤ x ^ (1 - ξ₂ + slack) := by
  -- The scale replacement, at the commensurability window of `K` widened to straddle `1`.
  obtain ⟨K₁, hc₁, hl₁, hs₁⟩ :=
    K.exists_transfer_at_comparable_scale (lo := min K.asympLo 1) (hi := max K.asympHi 1)
      (lt_min K.asympLo_pos zero_lt_one) ((min_le_right _ _).trans (le_max_right _ _))
  -- Its normalization, which is what makes `N * (x / N) = x` commensurable with `x`.
  obtain ⟨-, -, hAL, hAH, -, hfc, hfl, -, hfs, -⟩ := constantBundle_flat_transfer K₁
  refine ⟨K₁.flat, fun ξ₂ x f α β M N hξ hx hM hN hfeq hαc hβc hαM hβN hprod hαSW hβSW
    hlow hhigh ↦ ?_⟩
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN
  -- `N ≤ x`, the only place `slack ≤ ξ₂` is used, and what makes the reflected scale at least `1`.
  have hNx : N ≤ x := by
    refine hhigh.trans ?_
    calc x ^ (1 - ξ₂ + slack) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
      _ = x := Real.rpow_one x
  have hxN1 : (1 : ℝ) ≤ x / N := (one_le_div hN0).mpr hNx
  have hxN0 : (0 : ℝ) < x / N := zero_lt_one.trans_le hxN1
  -- `a₋ x ≤ M N ≤ a₊ x`, divided by `N`, is the ratio window at the old and new scales of `α`.
  have hloM : min K.asympLo 1 * (x / N) ≤ M := by
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hxN0.le) ?_
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hN0).mpr hprod.1
  have hMhi : M ≤ max K.asympHi 1 * (x / N) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) hxN0.le)
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hN0).mpr hprod.2
  -- The unswapped factor `β` transfers at the same scale, the window straddling `1`.
  have hloN : min K.asympLo 1 * N ≤ N := by
    have h := mul_le_mul_of_nonneg_right (min_le_right K.asympLo 1) hN0.le
    linarith
  have hNhi : N ≤ max K.asympHi 1 * N := by
    have h := mul_le_mul_of_nonneg_right (le_max_right K.asympHi 1) hN0.le
    linarith
  -- The exponent window is symmetric: `x^{ξ₂-ϵ} ≤ N ≤ x^{1-ξ₂+ϵ}` reflects to the same bounds
  -- on `x / N`, because the two exponents sum to `1`.
  have hpowlo : (0 : ℝ) < x ^ (ξ₂ - slack) := Real.rpow_pos_of_pos hx0 _
  have hpowhi : (0 : ℝ) < x ^ (1 - ξ₂ + slack) := Real.rpow_pos_of_pos hx0 _
  have hsplit : x ^ (ξ₂ - slack) * x ^ (1 - ξ₂ + slack) = x := by
    rw [← Real.rpow_add hx0, show ξ₂ - slack + (1 - ξ₂ + slack) = 1 by ring, Real.rpow_one]
  have hlow' : x ^ (ξ₂ - slack) ≤ x / N := by
    rw [le_div_iff₀ hN0]
    calc x ^ (ξ₂ - slack) * N ≤ x ^ (ξ₂ - slack) * x ^ (1 - ξ₂ + slack) :=
          mul_le_mul_of_nonneg_left hhigh hpowlo.le
      _ = x := hsplit
  have hhigh' : x / N ≤ x ^ (1 - ξ₂ + slack) := by
    rw [div_le_iff₀ hN0]
    calc x = x ^ (ξ₂ - slack) * x ^ (1 - ξ₂ + slack) := hsplit.symm
      _ ≤ N * x ^ (1 - ξ₂ + slack) := mul_le_mul_of_nonneg_right hlow hpowhi.le
      _ = x ^ (1 - ξ₂ + slack) * N := mul_comm _ _
  -- The reflected exponent is `1 - γ` on the nose.
  have hlogb : x / N = x ^ (1 - Real.logb x N) := by
    rw [Real.rpow_sub hx0, Real.rpow_one, Real.rpow_logb hx0 hx.ne' hN0]
  -- The new scales multiply to `x` exactly, so only `a₋ ≤ 1 ≤ a₊` at `K'` is needed.
  have hasymp : K₁.flat.asympEq (N * (x / N)) x := by
    have hcancel : N * (x / N) = x := by field_simp
    rw [hcancel]
    refine ConstantBundle.asympEq_iff.mpr ⟨?_, ?_⟩ <;> nlinarith
  exact ⟨hN, hxN1, hlogb, hfeq.trans (dconv_comm α β), hfc β (hc₁ β hβc), hfc α (hc₁ α hαc),
    hfl β N (hl₁ β N N hloN hNhi hβN), hfl α (x / N) (hl₁ α M (x / N) hloM hMhi hαM),
    hasymp, hfs β N (hs₁ β N N hN hN hloN hNhi hβSW),
    hfs α (x / N) (hs₁ α M (x / N) hM hxN1 hloM hMhi hαSW), hlow', hhigh'⟩

/-- **The reflection, read at the class.** There is a bundle `K'` depending on `K` alone with
`TypeII K x ξ₂ f → TypeII K' x ξ₂ f` for every `x > 1` and every `f`.

This is the sentence the routing quotes, but it is strictly weaker than
`Gap212.exists_bundle_typeII_swap_witnesses`: it hides the reflected scale, so it cannot be used to
conclude that the exponent has fallen below `1/2`. Use it only where the bundle, and not the
exponent, is what moves. -/
theorem exists_bundle_typeII_swap (K : ConstantBundle) :
    ∃ K' : ConstantBundle, ∀ ξ₂ x : ℝ, slack ≤ ξ₂ → 1 < x →
      ∀ f : ℕ → ℂ, TypeII K x ξ₂ f → TypeII K' x ξ₂ f := by
  obtain ⟨K', h⟩ := exists_bundle_typeII_swap_witnesses K
  refine ⟨K', fun ξ₂ x hξ hx f hf ↦ ?_⟩
  obtain ⟨α, β, M, hM, N, hN, hfeq, hαc, hβc, hαM, hβN, hprod, hαSW, hβSW, hlow, hhigh⟩ := hf
  obtain ⟨hN1, hxN1, -, hfeq', hβc', hαc', hβN', hαN', hprod', hβSW', hαSW', hlow', hhigh'⟩ :=
    h ξ₂ x f α β M N hξ hx hM hN hfeq hαc hβc hαM hβN hprod hαSW hβSW hlow hhigh
  exact ⟨β, α, N, hN1, x / N, hxN1, hfeq', hβc', hαc', hβN', hαN', hprod', hβSW', hαSW',
    hlow', hhigh'⟩

end Gap212
