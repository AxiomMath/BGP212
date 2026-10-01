/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Gap212.Attr
public import Gap212.Routing.Defs.Equidistribution
public import Gap212.Routing.Consequences
public import Gap212.Equidistribution.Moduli
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Consequences of the definitions

Three facts about coefficient sequences that need no harmonic analysis of the modulus, only the
definitions of the four clauses — the coefficient bound, location at a scale, smoothness at a scale
and the Siegel–Walfisz property — and the record `Gap212.ConstantBundle` of constants they are
stated with.

**A scale may be replaced by a commensurable one.** The source pins a scale only up to a bounded
factor: it is produced as a product of scales, or as `x / N` for some other scale `N`. So a
sequence declared at `N` must be usable at any `N'` with `λ₋ N' ≤ N ≤ λ₊ N'`, at the cost of
enlarging the constants once. Here the constants are data, so that cost is a map on bundles:
widening the support window from `[c₋, c₊]` to `[c₋λ₋, c₊λ₊]` carries the location clause, and
enlarging the Siegel–Walfisz constant by `λ₊ (1 + log Λ)^B`, where `Λ = max(1, λ₊, λ₋⁻¹)`, carries
the saving `(1 + log N)^{-B}` across to `(1 + log N')^{-B}`; the divisor exponent is untouched.

**A smooth sequence has the Siegel–Walfisz property.** A sequence smooth at a scale is a sampled
bump, `α n = ψ (n / N)` with `ψ` vanishing off `[c, C]` and `‖ψ⁽ʲ⁾‖∞ ≤ bⱼ (log N)^{wⱼ}`, and such a
sequence is equidistributed in residue classes to every power of the logarithm, uniformly in the
modulus. Möbius removes the coprimality to `r` from both sums of the discrepancy; splitting the
naturals coprime to `q` into the `φ(q)` classes mod `q` makes the second sum an average of sums of
the shape of the first; and the main terms then cancel with no arithmetic identity, because for
each divisor `d` of `r` the `φ(q)` classes in play share one modulus `Q = q d` and
`φ(q)⁻¹ ∑_x 1 = 1`. What is left is `τ(r)` differences of two sums over classes of that one
modulus, which the pairing `n = y₀ + Q j`, `n' = y₀' + Q j` bounds by `1 + (C - c) N / Q`
differences `ψ t - ψ s` with `|t - s| ≤ Q / N`; the mean value inequality for `Q ≤ N`, and `2 ‖ψ‖∞`
above it, give `O_{c,C,b,w}(τ(r) (1 + log N)^{w_0 + w_1})` either way. Since
`(1 + log N)^k ≤ k^k N`, a constant depending on the saving absorbs it, so the divisor exponent may
be taken to be `1`.

**A located coefficient sequence has a discrepancy bounded by its constants.** Location confines
the support to `c₀ N ≤ n ≤ c₁ N`, where the coefficient bound applies term by term, so both sums of
the discrepancy are at most
`Λ(y) / 2 = C (1 + log (1 + c₁ y))^l ∑_{1 ≤ n ≤ c₁ y} τ(n)^k`
for any `y ≥ N`, the normalising factor `1 / φ(d)` having modulus at most one. Summed over a family
of moduli inside `Gap212.moduliRange x ω` this gives `x^{1/2 + 2ω} Λ(y)`, which is the form in
which a bounded range of `x` is absorbed into the constant of an estimate proved beyond a
threshold.

## Main results

* `Gap212.ConstantBundle.exists_transfer_at_comparable_scale`: the bundle `Φ(K, λ₋, λ₊)`, together
  with the three transfers it effects.
* `Gap212.exists_hasSiegelWalfisz_of_isSmoothAtScale`: from the four smoothness components
  `(c, C, b, w)` alone there are a Siegel–Walfisz constant `S` and a divisor exponent `E`,
  functions of the saving, serving every sequence smooth at every scale `N ≥ 1` with those
  components.
* `Gap212.norm_sumError_le_and_sum_norm_sumError_le_of_located`: the pointwise bound `Λ(y)`,
  uniform in the modulus and the residue class, and the bound `x^{1/2 + 2ω} Λ(y)` on the sum over a
  family of moduli.

## Implementation notes

In the first result the *placement* of the existential is the whole of the source's "depending on
nothing else": `K'` is quantified before the sequence and before both scales, so one bundle serves
every sequence and every pair of commensurable scales in the window. A bundle chosen after the data
would be no statement at all, since a single sequence at a single scale satisfies every clause of
some bundle. Smoothness is not claimed to transfer, following the source: a smooth profile at `N`
is a shifted-and-rescaled profile at `N'`, and the routes that move a declared scale use their
factors through location and Siegel–Walfisz alone. The coefficient clause is quantified outside
both scales, the coefficient bound mentioning no scale; the location clause carries only the
commensurability, the support inequalities scaling by the window with no lower bound on either
scale; and `1 ≤ N`, `1 ≤ N'` appear only on the Siegel–Walfisz clause, which needs `1 + log N ≥ 1`
to compare the two savings.

The second result is bundle-free where the source speaks of bundles. It asserts a bundle
`K♯ = Σ K` differing from `K` only in the two Siegel–Walfisz components; since
`Gap212.ConstantBundle.IsSmoothAtScale` reads only `(scaleLo, scaleHi, smoothConst, smoothPow)` and
`Gap212.ConstantBundle.HasSiegelWalfisz` only `(siegelWalfiszConst, siegelWalfiszPow)`, that
assertion is this statement applied to the first four with `Σ K` the structure update of `K` in the
last two. Its closing clause — every other clause a datum satisfies at `K` it satisfies at `K♯` —
then needs no statement, the five clauses reading pairwise disjoint groups of components, so the
transfer is `rfl`. The uniformity, not the existence of a pair for each sequence, is the content:
the sequence-by-sequence reading is vacuous, a finitely supported sequence satisfying any such
bound once the constant is large enough.

The route of the second proof is not the source's. The source argues by Poisson summation for
`[q, r] ≤ N^{1/2}` and by a trivial bound above it, and that trivial branch is false as displayed:
after the Möbius step the moduli in play are `[q, d]` for `d ∣ r`, and `[q, 1] = q` can be tiny
even when `[q, r]` is large, so the left-hand side there can be of size `N`. Comparing classes of
one modulus to each other avoids both the case distinction and the Fourier transform, because total
variation is scale invariant, which is why `norm_sum_progression_sub_le` does not see `Q`. The one
hypothesis the statement places on the smoothness data, `0 < c`, is therefore never used: it is
what the Poisson route needs, keeping the sampled profile away from the left edge of `ℕ` so that
the sum over a class in `ℕ` is the sum over that class in `ℤ`, and the pairing forms no Fourier
transform. It is kept because at a bundle it costs nothing, being `K.scaleLo_pos`. No ordering of
the two endpoints is imposed either: for `C < c` the profile vanishes identically and the bound is
trivial.

The third result is stated at an arbitrary `y ≥ N` rather than at `N`, which is how the source's
separate assertion that `Λ` is non-decreasing on `[1, ∞)` is delivered: its only use is to
transport the bound from the scale of the sequence to a larger quantity fixed in advance. Its
constants are the five explicit reals and naturals rather than a bundle, the bundle's
commensurability, smoothness and Siegel–Walfisz components playing no part; a consumer holding `K`
applies it to `K.coeffConst`, `K.coeffFstPow`, `K.coeffSndPow`, `K.scaleLo`, `K.scaleHi`. The
source's `d ≥ 1` is absent, the pointwise bound holding for every modulus: at `d = 0` the factor
`1 / (φ 0 : ℂ)` is `0`, the subtracted sum drops out, `n ≡ a [MOD 0]` is `n = a`, and `‖f a‖` is a
single term of the majorising sum. The source's `N ≥ 1` is weakened to `0 < N` and its `x ≥ 3` to
`0 ≤ x`; no sign condition is imposed on `c₁`, and in the degenerate case `c₁ < 0` the bound is `0`
because `Finset.Icc 1 ⌊c₁ * y⌋₊` is empty. The majorising sum runs over the *positive* integers
`n ≤ c₁ y`: the index `0` would contribute `0 ^ k`, which is `1` when `k = 0` and so would only
inflate the bound, and no index of the support is lost, since `f 0 = 0`.

## References

* [1, Definition 2.5 (i)–(ii)], where the scales carry `≪` constants and commensurable scales are
  interchanged silently.
* [2, Definition 6 (i)–(ii)].
-/

public section

namespace Gap212

/-! ### Replacing a scale by a commensurable one -/

/-- Comparing the two Siegel–Walfisz savings: if `N' ≤ Λ * N` with `1 ≤ Λ` and `1 ≤ N`, then the
logarithm at `N'` is at most `(1 + log Λ)` times the logarithm at `N`. The multiplicative form,
rather than the additive `log N' ≤ log Λ + log N`, is what survives being raised to a power `B`. -/
private lemma one_add_log_le_mul_one_add_log {Λ N N' : ℝ} (hΛ : 1 ≤ Λ) (hN : 1 ≤ N)
    (hN' : 0 < N') (hle : N' ≤ Λ * N) :
    1 + Real.log N' ≤ (1 + Real.log Λ) * (1 + Real.log N) := by
  have h := Real.log_le_log hN' hle
  rw [Real.log_mul (by linarith : Λ ≠ 0) (by linarith : N ≠ 0)] at h
  nlinarith [Real.log_nonneg hΛ, Real.log_nonneg hN]

/-- The saving at `N'` dominates the saving at `N`, after the stated enlargement: this is the whole
of the Siegel–Walfisz transfer, stated on the factor `N * (1 + log N)^{-B}` that the bound carries
and with the enlarging factor `hi * (1 + log Λ)^B` spelled out. -/
private lemma div_rpow_le_mul_div_rpow {B N N' Λ hi : ℝ} (hB : 0 < B) (hΛ : 1 ≤ Λ) (hN : 1 ≤ N)
    (hN' : 1 ≤ N') (hhi : 0 ≤ hi) (hlt : N' ≤ Λ * N) (hup : N ≤ hi * N') :
    N / (1 + Real.log N) ^ B ≤ hi * (1 + Real.log Λ) ^ B * N' / (1 + Real.log N') ^ B := by
  have hL : (1 : ℝ) ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN]
  have hL' : (1 : ℝ) ≤ 1 + Real.log N' := by linarith [Real.log_nonneg hN']
  have hLp : (0 : ℝ) < (1 + Real.log N) ^ B := Real.rpow_pos_of_pos (by linarith) B
  have hL'p : (0 : ℝ) < (1 + Real.log N') ^ B := Real.rpow_pos_of_pos (by linarith) B
  have hsave : (1 + Real.log N') ^ B ≤ (1 + Real.log Λ) ^ B * (1 + Real.log N) ^ B := by
    have h := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ 1 + Real.log N')
      (one_add_log_le_mul_one_add_log hΛ hN (by linarith) hlt) hB.le
    rwa [Real.mul_rpow (by linarith [Real.log_nonneg hΛ]) (by linarith)] at h
  rw [div_le_div_iff₀ hLp hL'p]
  exact (mul_le_mul hup hsave hL'p.le (by positivity)).trans_eq (by ring)

namespace ConstantBundle

/-- **Replacing a scale by a commensurable one.** For a bundle `K` and a ratio window
`0 < λ₋ ≤ λ₊` there is a bundle `K'`, depending on `K`, `λ₋` and `λ₊` alone, such that: every
`K`-coefficient sequence is a `K'`-coefficient sequence; a sequence `K`-located at `N` is
`K'`-located at `N'` whenever `λ₋ * N' ≤ N ≤ λ₊ * N'`; and a sequence with the `K`-Siegel–Walfisz
property at `N` has the `K'`-property at `N'` whenever moreover `1 ≤ N` and `1 ≤ N'`.

Here `lo` and `hi` are the source's `λ₋` and `λ₊`, the endpoints of the *ratio* window `N / N'`;
they are not the support endpoints `K.scaleLo`, `K.scaleHi`, which the new bundle rescales by them.
The bundle is quantified before the sequence and both scales, which is what makes it the source's
`Φ(K, λ₋, λ₊)`; smoothness is not claimed to transfer. -/
@[gap212 "lem_scale_replacement"]
theorem exists_transfer_at_comparable_scale (K : ConstantBundle) {lo hi : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    ∃ K' : ConstantBundle,
      (∀ α : ℕ → ℂ, K.IsCoefficientSequence α → K'.IsCoefficientSequence α) ∧
      (∀ (α : ℕ → ℂ) (N N' : ℝ), lo * N' ≤ N → N ≤ hi * N' →
        K.LocatedAtScale α N → K'.LocatedAtScale α N') ∧
      (∀ (α : ℕ → ℂ) (N N' : ℝ), 1 ≤ N → 1 ≤ N' → lo * N' ≤ N → N ≤ hi * N' →
        K.HasSiegelWalfisz α N → K'.HasSiegelWalfisz α N') := by
  have hhi : 0 < hi := hlo.trans_le hlohi
  set Λ : ℝ := max 1 (max hi lo⁻¹)
  have hΛ : (1 : ℝ) ≤ Λ := le_max_left _ _
  have hinvΛ : lo⁻¹ ≤ Λ := (le_max_right hi lo⁻¹).trans (le_max_right _ _)
  refine ⟨{ K with
      scaleLo := K.scaleLo * lo
      scaleHi := K.scaleHi * hi
      siegelWalfiszConst := fun B => K.siegelWalfiszConst B * hi * (1 + Real.log Λ) ^ B
      scaleLo_pos := mul_pos K.scaleLo_pos hlo
      scaleLo_lt_scaleHi := by
        nlinarith [K.scaleLo_pos, K.scaleLo_lt_scaleHi, K.scaleHi_pos] }, fun α h => h, ?_, ?_⟩
  · intro α N N' hdn hup hloc n hn hne
    obtain ⟨h1, h2⟩ := hloc n hn hne
    exact ⟨by nlinarith [K.scaleLo_pos], by nlinarith [K.scaleHi_pos]⟩
  · intro α N N' hN hN' hdn hup hsw B hB q hq r hr a hcop
    have hlt : N' ≤ Λ * N :=
      ((le_inv_mul_iff₀ hlo).2 hdn).trans (mul_le_mul_of_nonneg_right hinvΛ (by linarith))
    have hbound := hsw B hB q hq r hr a hcop
    set T : ℝ := ((q * r).divisors.card : ℝ) ^ K.siegelWalfiszPow B
    set S : ℝ := K.siegelWalfiszConst B
    have hLp : (0 : ℝ) < (1 + Real.log N) ^ B :=
      Real.rpow_pos_of_pos (by linarith [Real.log_nonneg hN]) B
    -- The saving is positive and `S * T` bounds a norm over it, so `S * T` is itself nonnegative.
    have hST : (0 : ℝ) ≤ S * T :=
      nonneg_of_mul_nonneg_left (by rw [← mul_div_assoc]; exact (norm_nonneg _).trans hbound)
        (div_pos (by linarith) hLp)
    exact hbound.trans (le_of_eq_of_le (by ring) ((mul_le_mul_of_nonneg_left
      (div_rpow_le_mul_div_rpow hB hΛ hN hN' hhi.le hlt hup) hST).trans_eq (by ring)))

end ConstantBundle

/-! ### A smooth sequence has the Siegel–Walfisz property

The three groups below are the three steps of the argument: the Möbius rearrangement that makes the
discrepancy an average of differences of classes of *equal* modulus, the pairing bound on such a
difference, and the absorption of the logarithmic saving by the scale. -/

section Smooth

open Finset

/-! #### Residue classes, and the removal of the coprimality to `r` -/

/-- Coprimality to `q` only depends on the residue mod `q`. -/
private lemma coprime_mod_iff {q n : ℕ} : Nat.Coprime q n ↔ Nat.Coprime q (n % q) := by
  change Nat.gcd q n = 1 ↔ Nat.gcd q (n % q) = 1
  rw [Nat.gcd_rec q n, Nat.gcd_comm (n % q) q]

/-- Two congruences with coprime moduli are one congruence: for `d` coprime to `q`, the multiples
of `d` in a class mod `q` form a class mod `q * d`. -/
private lemma exists_modEq_mul_of_coprime {q d : ℕ} (h : Nat.Coprime q d) (x : ℕ) :
    ∃ y : ℕ, ∀ n : ℕ, (n ≡ x [MOD q] ∧ d ∣ n) ↔ n ≡ y [MOD q * d] := by
  obtain ⟨y, hy₁, hy₂⟩ := Nat.chineseRemainder h x 0
  refine ⟨y, fun n => ?_⟩
  rw [← Nat.modEq_and_modEq_iff_modEq_mul h, ← Nat.modEq_zero_iff_dvd]
  exact and_congr ⟨(·.trans hy₁.symm), (·.trans hy₁)⟩ ⟨(·.trans hy₂.symm), (·.trans hy₂)⟩

/-- A sum over a residue class inside `range M`, reindexed as a sum over `range M`. -/
private lemma sum_modEq_eq_sum_range {M : ℕ} {f : ℕ → ℂ} (hf : ∀ n, M ≤ n → f n = 0)
    {Q : ℕ} (hQ : 0 < Q) (y : ℕ) :
    ∑ n ∈ range M with n ≡ y [MOD Q], f n = ∑ j ∈ range M, f (y % Q + Q * j) := by
  have h₁ : ∑ j ∈ range M, f (y % Q + Q * j)
      = ∑ j ∈ range M with y % Q + Q * j < M, f (y % Q + Q * j) :=
    (Finset.sum_subset (Finset.filter_subset _ _) fun j hj hjA =>
      hf _ (by simpa [hj] using hjA)).symm
  have h₂ : (range M).filter (fun n => n ≡ y [MOD Q])
      = ((range M).filter (fun j => y % Q + Q * j < M)).image (fun j => y % Q + Q * j) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hnM, hmod⟩
      have hid : y % Q + Q * (n / Q) = n := by
        rw [← show n % Q = y % Q from hmod]; exact Nat.mod_add_div n Q
      exact ⟨n / Q, ⟨(Nat.div_le_self n Q).trans_lt hnM, by rw [hid]; exact hnM⟩, hid⟩
    · rintro ⟨j, ⟨-, hlt⟩, rfl⟩
      exact ⟨hlt, by simp [Nat.ModEq]⟩
  rw [h₁, h₂, Finset.sum_image]
  exact fun j _ k _ hjk => Nat.eq_of_mul_eq_mul_left hQ (Nat.add_left_cancel hjk)

/-- The Möbius sum over the divisors of a natural, as a complex number. -/
private lemma sum_divisors_moebius (m : ℕ) :
    ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) = if m = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.one_apply (R := ℂ), ← ArithmeticFunction.coe_moebius_mul_coe_zeta,
    ArithmeticFunction.coe_mul_zeta_apply]
  rfl

/-- `μ` takes the values `0, ±1`, so its complex image lies in the closed unit disc. -/
private lemma norm_moebius_le_one (d : ℕ) : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- **Removing the coprimality to `r`** from a finite sum by Möbius inversion. -/
private lemma sum_filter_coprime {r : ℕ} (hr : r ≠ 0) (G : Finset ℕ) (α : ℕ → ℂ) :
    ∑ n ∈ G with Nat.Coprime n r, α n
      = ∑ d ∈ r.divisors, (ArithmeticFunction.moebius d : ℂ) * ∑ n ∈ G with d ∣ n, α n := by
  have hμ : ∀ n : ℕ, (∑ d ∈ r.divisors with d ∣ n, (ArithmeticFunction.moebius d : ℂ)) * α n
      = if Nat.Coprime n r then α n else 0 := by
    intro n
    have hfe : (r.divisors).filter (fun d => d ∣ n) = (Nat.gcd n r).divisors := by
      ext d
      simp [Nat.dvd_gcd_iff, hr, Nat.gcd_ne_zero_right hr, and_comm]
    rw [hfe, sum_divisors_moebius, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_filter]
  simp_rw [← hμ, Finset.sum_mul, Finset.mul_sum, Finset.sum_filter]
  exact Finset.sum_comm

/-- The naturals coprime to `q` split into the `φ(q)` residue classes coprime to `q`. -/
private lemma sum_coprime_eq_sum_classes {q : ℕ} (hq : 0 < q) (F : Finset ℕ) (d : ℕ) (α : ℕ → ℂ) :
    (∑ n ∈ F with (Nat.Coprime n q ∧ d ∣ n), α n)
      = ∑ x ∈ range q with q.Coprime x, ∑ n ∈ F with (n ≡ x [MOD q] ∧ d ∣ n), α n := by
  refine (Finset.sum_fiberwise_of_maps_to
    (s := F.filter (fun n => Nat.Coprime n q ∧ d ∣ n)) (t := {x ∈ range q | q.Coprime x})
    (g := fun n => n % q) ?_ α).symm.trans ?_
  · exact fun n hn => Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ hq),
      coprime_mod_iff.1 (Finset.mem_filter.1 hn).2.1.symm⟩
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hxq : x < q := Finset.mem_range.1 (Finset.mem_filter.1 hx).1
    have hxc : Nat.Coprime q x := (Finset.mem_filter.1 hx).2
    rw [Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun n _ => ?_) (fun _ _ => rfl)
    rw [Nat.ModEq, Nat.mod_eq_of_lt hxq]
    exact ⟨fun ⟨⟨_, h⟩, h'⟩ => ⟨h', h⟩,
      fun ⟨h', h⟩ => ⟨⟨(coprime_mod_iff.2 (h' ▸ hxc)).symm, h⟩, h'⟩⟩

/-- **The main term cancels.** Subtracting from `z` the average of `u` over a nonempty `T` is
averaging the differences `z - u x`; no property of `z` or of `u` is involved. -/
private lemma sub_average_eq {T : Finset ℕ} (hT : T.Nonempty) (z : ℂ) (u : ℕ → ℂ) :
    z - (1 / (T.card : ℂ)) * ∑ x ∈ T, u x = (1 / (T.card : ℂ)) * ∑ x ∈ T, (z - u x) := by
  have hc : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hT.card_ne_zero
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- The residues mod `q` coprime to `q` form a nonempty set, having `φ(q) > 0` elements. -/
private lemma filter_coprime_range_nonempty {q : ℕ} (hq : 0 < q) :
    ({x ∈ range q | q.Coprime x} : Finset ℕ).Nonempty :=
  Finset.card_pos.1 (Nat.totient_eq_card_coprime q ▸ Nat.totient_pos.2 hq)

/-- **The discrepancy is a Möbius-weighted average of differences of classes of equal modulus.**
Möbius removes the coprimality to `r` from both sums; splitting the naturals coprime to `q` into
the `φ(q)` classes `x` mod `q` makes the second sum an average over `x` of sums of the same shape
as the first; and the main terms cancel by `sub_average_eq`, with no arithmetic identity. For each
divisor `d` of `r` the classes in play share the modulus `q * d`. -/
private lemma discrepancy_eq_moebius_sum {α : ℕ → ℂ} {F : Finset ℕ}
    (hF : Function.support α ⊆ ↑F) {q r : ℕ} (hq : 0 < q) (hr : r ≠ 0) (a : ℕ) :
    (∑ᶠ n ∈ {n : ℕ | n ≡ a [MOD q] ∧ Nat.Coprime n r}, α n)
        - (1 / (q.totient : ℂ)) * ∑ᶠ n ∈ {n : ℕ | Nat.Coprime n (q * r)}, α n
      = ∑ d ∈ r.divisors, (ArithmeticFunction.moebius d : ℂ) *
          ((1 / ((({x ∈ range q | q.Coprime x} : Finset ℕ).card : ℕ) : ℂ)) *
            ∑ x ∈ range q with q.Coprime x,
              ((∑ n ∈ F with (n ≡ a [MOD q] ∧ d ∣ n), α n)
                - ∑ n ∈ F with (n ≡ x [MOD q] ∧ d ∣ n), α n)) := by
  have hcardT : ((({x ∈ range q | q.Coprime x} : Finset ℕ).card : ℕ) : ℂ) = (q.totient : ℂ) := by
    rw [Nat.totient_eq_card_coprime]
  have hfin : ∀ (p : ℕ → Prop) [DecidablePred p], (∑ᶠ n ∈ {n | p n}, α n) = ∑ n ∈ F with p n, α n :=
    fun p _ => finsum_mem_setOf_eq_sum_filter_of_support_subset hF (fun _ _ ↦ rfl) p
  have hX : (∑ᶠ n ∈ {n : ℕ | n ≡ a [MOD q] ∧ Nat.Coprime n r}, α n)
      = ∑ d ∈ r.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ n ∈ F with (n ≡ a [MOD q] ∧ d ∣ n), α n := by
    rw [hfin, ← Finset.filter_filter, sum_filter_coprime hr]
    exact Finset.sum_congr rfl fun d _ => by rw [Finset.filter_filter]
  have hY : (∑ᶠ n ∈ {n : ℕ | Nat.Coprime n (q * r)}, α n)
      = ∑ d ∈ r.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ x ∈ range q with q.Coprime x, ∑ n ∈ F with (n ≡ x [MOD q] ∧ d ∣ n), α n := by
    have hsplit : {n ∈ F | Nat.Coprime n (q * r)}
        = {n ∈ {n ∈ F | Nat.Coprime n q} | Nat.Coprime n r} := by
      rw [Finset.filter_filter]
      exact Finset.filter_congr fun n _ => by simp [Nat.coprime_mul_iff_right]
    rw [hfin, hsplit, sum_filter_coprime hr]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.filter_filter, sum_coprime_eq_sum_classes hq F d α]
  rw [hX, hY, hcardT, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← hcardT, ← sub_average_eq (filter_coprime_range_nonempty hq)]
  ring

/-! #### The pairing bound -/

/-- A set of naturals confined to a real interval of length `L` has at most `1 + L` elements. -/
private lemma card_le_one_add {S : Finset ℕ} {x L : ℝ} (hL : 0 ≤ L)
    (h : ∀ j ∈ S, x ≤ (j : ℝ) ∧ (j : ℝ) ≤ x + L) : (S.card : ℝ) ≤ 1 + L := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨m, hm⟩
  · simpa using by linarith
  have hx0 : 0 ≤ x + L := (Nat.cast_nonneg m).trans (h m hm).2
  have hmle : ⌈x⌉₊ ≤ ⌊x + L⌋₊ := (Nat.ceil_le.2 (h m hm).1).trans (Nat.le_floor (h m hm).2)
  have hsub : S ⊆ Finset.Icc ⌈x⌉₊ ⌊x + L⌋₊ := fun j hj =>
    Finset.mem_Icc.2 ⟨Nat.ceil_le.2 (h j hj).1, Nat.le_floor (h j hj).2⟩
  have h' : (S.card : ℝ) + (⌈x⌉₊ : ℝ) ≤ (⌊x + L⌋₊ : ℝ) + 1 := by
    have h := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h
    exact_mod_cast (by omega : S.card + ⌈x⌉₊ ≤ ⌊x + L⌋₊ + 1)
  linarith [Nat.floor_le hx0, Nat.le_ceil x]

/-- Only `1 + (C - c) N / Q` of the samples `ψ ((u + Q j) / N)` are nonzero, for a profile
supported in `[c, C]`: the sampled points that meet the support lie in an interval of length
`(C - c) N / Q`. -/
private lemma card_filter_ne_zero_le {c C N : ℝ} (hN : 0 < N) {ψ : ℝ → ℂ}
    (hsupp : ∀ t, ψ t ≠ 0 → t ∈ Set.Icc c C) {Q : ℝ} (hQ : 0 < Q) (u : ℝ) (M : ℕ) :
    (((range M).filter (fun j : ℕ => ψ ((u + Q * (j : ℝ)) / N) ≠ 0)).card : ℝ)
      ≤ 1 + max (C - c) 0 * (N / Q) := by
  refine card_le_one_add (x := (c * N - u) / Q) (by positivity) fun j hj => ?_
  obtain ⟨hlo, hhi⟩ := hsupp _ (Finset.mem_filter.1 hj).2
  rw [le_div_iff₀ hN] at hlo
  rw [div_le_iff₀ hN] at hhi
  refine ⟨by rw [div_le_iff₀ hQ]; linarith, ?_⟩
  rw [show (c * N - u) / Q + max (C - c) 0 * (N / Q) = (c * N - u + max (C - c) 0 * N) / Q by
    field_simp, le_div_iff₀ hQ]
  linarith [mul_le_mul_of_nonneg_right (le_max_left (C - c) 0) hN.le]

/-- A difference of two sums over `range M` is at most the number of indices at which the summands
differ, times a uniform bound on each difference. -/
private lemma norm_sum_sub_sum_le (f g : ℕ → ℂ) {M : ℕ} {D E : ℝ} (hD : ∀ j, ‖f j - g j‖ ≤ D)
    (hE : (((range M).filter (fun j => f j - g j ≠ 0)).card : ℝ) ≤ E) :
    ‖(∑ j ∈ range M, f j) - ∑ j ∈ range M, g j‖ ≤ E * D := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  rw [show (∑ j ∈ range M, f j) - ∑ j ∈ range M, g j
      = ∑ j ∈ range M with f j - g j ≠ 0, (f j - g j) by
    rw [Finset.sum_filter_ne_zero, Finset.sum_sub_distrib]]
  refine (norm_sum_le _ _).trans ((?_ : _ ≤ _).trans (mul_le_mul_of_nonneg_right hE hD0))
  simpa [nsmul_eq_mul] using
    Finset.sum_le_card_nsmul _ _ D fun j _ => hD j

/-- **The pairing bound.** Two arithmetic progressions of the same difference `Q`, sampled from a
profile `ψ` supported in `[c, C]` at scale `N`, have sums differing by at most a constant multiple
of `‖ψ‖∞ + ‖ψ'‖∞` — uniformly in `Q`, in the offsets and in the truncation `M`. Pairing the `j`-th
sample of one progression with the `j`-th of the other makes each difference `ψ t - ψ s` with
`|t - s| ≤ Q / N`, and only `1 + (C - c) N / Q` of the `j` contribute: for `Q ≤ N` the mean value
inequality gives `(1 + (C - c) N / Q) (Q / N)` multiples of `‖ψ'‖∞`, and for `Q > N` the same count
against `2 ‖ψ‖∞` does it. Total variation is scale invariant, which is why the bound does not see
`Q`. -/
private lemma norm_sum_progression_sub_le {c C N : ℝ} (hN : 1 ≤ N) {ψ : ℝ → ℂ}
    (hdiff : Differentiable ℝ ψ) (hsupp : ∀ t, ψ t ≠ 0 → t ∈ Set.Icc c C)
    {A₀ A₁ : ℝ} (h₀ : ∀ t, ‖ψ t‖ ≤ A₀) (h₁ : ∀ t, ‖deriv ψ t‖ ≤ A₁)
    {Q u v : ℝ} (hQ : 0 < Q) (huv : |u - v| ≤ Q) (M : ℕ) :
    ‖(∑ j ∈ range M, ψ ((u + Q * j) / N)) - ∑ j ∈ range M, ψ ((v + Q * j) / N)‖
      ≤ 4 * (1 + max (C - c) 0) * (A₀ + A₁) := by
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hA₀ : 0 ≤ A₀ := (norm_nonneg _).trans (h₀ 0)
  have hA₁ : 0 ≤ A₁ := (norm_nonneg _).trans (h₁ 0)
  have hw : (0 : ℝ) ≤ max (C - c) 0 := le_max_right _ _
  have hcount : (((range M).filter
      (fun j : ℕ => ψ ((u + Q * (j : ℝ)) / N) - ψ ((v + Q * (j : ℝ)) / N) ≠ 0)).card : ℝ)
      ≤ 2 * (1 + max (C - c) 0 * (N / Q)) := by
    have hsub : (range M).filter
        (fun j : ℕ => ψ ((u + Q * (j : ℝ)) / N) - ψ ((v + Q * (j : ℝ)) / N) ≠ 0)
        ⊆ ((range M).filter (fun j : ℕ => ψ ((u + Q * (j : ℝ)) / N) ≠ 0))
          ∪ ((range M).filter (fun j : ℕ => ψ ((v + Q * (j : ℝ)) / N) ≠ 0)) := by
      intro j
      simp only [Finset.mem_filter, Finset.mem_union]
      grind
    have h := (Nat.cast_le (α := ℝ)).2 ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
    push_cast at h
    linarith [card_filter_ne_zero_le hN0 hsupp hQ u M, card_filter_ne_zero_le hN0 hsupp hQ v M]
  rcases le_or_gt Q N with hcase | hcase
  · have hterm : ∀ j : ℕ, ‖ψ ((u + Q * j) / N) - ψ ((v + Q * j) / N)‖ ≤ A₁ * (Q / N) := by
      intro j
      refine (Convex.norm_image_sub_le_of_norm_deriv_le (fun t _ => hdiff t) (fun t _ => h₁ t)
        convex_univ (Set.mem_univ _) (Set.mem_univ _)).trans
        (mul_le_mul_of_nonneg_left ?_ hA₁)
      rw [show (u + Q * j) / N - (v + Q * j) / N = (u - v) / N by ring, Real.norm_eq_abs, abs_div,
        abs_of_pos hN0]
      gcongr
    refine (norm_sum_sub_sum_le _ _ hterm hcount).trans ?_
    rw [show 2 * (1 + max (C - c) 0 * (N / Q)) * (A₁ * (Q / N))
        = 2 * A₁ * (Q / N) + 2 * max (C - c) 0 * A₁ * ((N / Q) * (Q / N)) by ring,
      show (N / Q) * (Q / N) = 1 by field_simp, mul_one]
    have hQN : Q / N ≤ 1 := (div_le_one hN0).2 hcase
    nlinarith [mul_le_mul_of_nonneg_left hQN hA₁, mul_nonneg hw hA₀, mul_nonneg hw hA₁]
  · have hterm : ∀ j : ℕ, ‖ψ ((u + Q * j) / N) - ψ ((v + Q * j) / N)‖ ≤ 2 * A₀ := fun j =>
      (norm_sub_le _ _).trans (by linarith [h₀ ((u + Q * j) / N), h₀ ((v + Q * j) / N)])
    refine (norm_sum_sub_sum_le _ _ hterm hcount).trans ?_
    have hNQ : N / Q ≤ 1 := (div_le_one hQ).2 hcase.le
    nlinarith [mul_le_mul_of_nonneg_left hNQ (mul_nonneg hw hA₀), mul_nonneg hw hA₀,
      mul_nonneg hw hA₁]

/-- **Two classes mod `q`, cut down to the multiples of `d`, carry sums of a sampled bump within
`4 (1 + (C - c)) (‖ψ‖∞ + ‖ψ'‖∞)` of each other.** For `d` coprime to `q` the two sets are classes
of the single modulus `q * d`, and the pairing bound applies; if `d` shares a factor with `q` both
sets are empty. -/
private lemma norm_sum_class_sub_le {c C N : ℝ} (hN : 1 ≤ N) {ψ : ℝ → ℂ}
    (hdiff : Differentiable ℝ ψ) (hsupp : ∀ t, ψ t ≠ 0 → t ∈ Set.Icc c C)
    {A₀ A₁ : ℝ} (h₀ : ∀ t, ‖ψ t‖ ≤ A₀) (h₁ : ∀ t, ‖deriv ψ t‖ ≤ A₁)
    {α : ℕ → ℂ} (hα : ∀ n : ℕ, α n = ψ ((n : ℝ) / N)) {M : ℕ} (hzero : ∀ n, M ≤ n → α n = 0)
    {q d x y : ℕ} (hq : 0 < q) (hd : 0 < d) (hx : q.Coprime x) (hy : q.Coprime y) :
    ‖(∑ n ∈ range M with (n ≡ x [MOD q] ∧ d ∣ n), α n)
        - ∑ n ∈ range M with (n ≡ y [MOD q] ∧ d ∣ n), α n‖
      ≤ 4 * (1 + max (C - c) 0) * (A₀ + A₁) := by
  by_cases hcop : q.Coprime d
  · obtain ⟨ux, hux⟩ := exists_modEq_mul_of_coprime hcop x
    obtain ⟨uy, huy⟩ := exists_modEq_mul_of_coprime hcop y
    have hQ : 0 < q * d := Nat.mul_pos hq hd
    have hcast : ∀ z j : ℕ, α (z % (q * d) + q * d * j)
        = ψ ((((z % (q * d) : ℕ) : ℝ) + ((q * d : ℕ) : ℝ) * j) / N) := by
      intro z j; rw [hα]; push_cast; ring_nf
    rw [Finset.filter_congr fun n _ => hux n, Finset.filter_congr fun n _ => huy n,
      sum_modEq_eq_sum_range hzero hQ ux, sum_modEq_eq_sum_range hzero hQ uy]
    simp only [hcast]
    -- Both offsets lie in `[0, q * d)`, so they differ by less than the common modulus.
    exact norm_sum_progression_sub_le hN hdiff hsupp h₀ h₁ (by exact_mod_cast hQ)
      (abs_sub_le_of_nonneg_of_le (Nat.cast_nonneg _) (by exact_mod_cast (Nat.mod_lt _ hQ).le)
        (Nat.cast_nonneg _) (by exact_mod_cast (Nat.mod_lt _ hQ).le)) M
  · have hempty : ∀ z : ℕ, Nat.Coprime q z →
        (range M).filter (fun n => n ≡ z [MOD q] ∧ d ∣ n) = ∅ := fun z hz =>
      Finset.filter_eq_empty_iff.2 fun n _ ⟨hmod, hdn⟩ =>
        hcop (Nat.Coprime.coprime_dvd_right hdn (Nat.Coprime.symm (hmod.gcd_eq.trans hz.symm)))
    have hA₀ : 0 ≤ A₀ := (norm_nonneg _).trans (h₀ 0)
    have hA₁ : 0 ≤ A₁ := (norm_nonneg _).trans (h₁ 0)
    rw [hempty x hx, hempty y hy, Finset.sum_empty, sub_zero, norm_zero]
    positivity

/-! #### Averaging over the divisors, and the logarithmic saving -/

/-- A Möbius-weighted average over a nonempty `T` of terms of norm at most `V` has norm at most
`τ(r) V`. -/
private lemma norm_sum_divisors_moebius_average_le {r : ℕ} {T : Finset ℕ} (hT : T.Nonempty)
    {u : ℕ → ℕ → ℂ} {V : ℝ} (h : ∀ d ∈ r.divisors, ∀ x ∈ T, ‖u d x‖ ≤ V) :
    ‖∑ d ∈ r.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ((1 / (T.card : ℂ)) * ∑ x ∈ T, u d x)‖ ≤ (r.divisors.card : ℝ) * V := by
  have hcard0 : (0 : ℝ) < (T.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hT
  have hterm : ∀ d ∈ r.divisors, ‖(ArithmeticFunction.moebius d : ℂ) *
      ((1 / (T.card : ℂ)) * ∑ x ∈ T, u d x)‖ ≤ V := by
    intro d hd
    rw [norm_mul, norm_mul, norm_div, norm_one, Complex.norm_natCast]
    refine (mul_le_of_le_one_left (by positivity) (norm_moebius_le_one d)).trans ?_
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hcard0]
    refine (norm_sum_le _ _).trans ?_
    simpa [nsmul_eq_mul, mul_comm] using
      Finset.sum_le_card_nsmul T (fun x => ‖u d x‖) V fun x hx => h d hd x hx
  refine (norm_sum_le _ _).trans ?_
  simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul r.divisors _ V hterm

/-- A power of the logarithm is absorbed by the scale: `(1 + log N) ^ k ≤ k ^ k * N`. -/
private lemma one_add_log_pow_le {N : ℝ} (hN : 1 ≤ N) {k : ℕ} (hk : 1 ≤ k) :
    (1 + Real.log N) ^ k ≤ (k : ℝ) ^ k * N := by
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN
  -- `log t ≤ t - 1` at `t = N ^ (1 / k)`, multiplied up by `k`.
  have hroot : 1 + Real.log N ≤ (k : ℝ) * N ^ ((k : ℝ)⁻¹) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hN0 ((k : ℝ)⁻¹))
    rw [Real.log_rpow hN0, inv_mul_eq_div, div_le_iff₀ (by linarith : (0 : ℝ) < (k : ℝ))] at h
    nlinarith
  have hpow : (N ^ ((k : ℝ)⁻¹)) ^ k = N := by
    rw [← Real.rpow_natCast (N ^ ((k : ℝ)⁻¹)) k, ← Real.rpow_mul hN0.le,
      inv_mul_cancel₀ (by positivity), Real.rpow_one]
  calc (1 + Real.log N) ^ k ≤ ((k : ℝ) * N ^ ((k : ℝ)⁻¹)) ^ k :=
        pow_le_pow_left₀ (by linarith) hroot k
    _ = (k : ℝ) ^ k * N := by rw [mul_pow, hpow]

/-- **The saving is free.** A power of the logarithm times the saving `(1 + log N) ^ B` is at most
`K ^ K * N` as soon as `k + B ≤ K`: no threshold `N₀(B)` and no Fourier decay is needed to pay for
`(1 + log N) ^ B`, only a constant depending on `B`. -/
private lemma log_pow_mul_rpow_le {N : ℝ} (hN : 1 ≤ N) {k K : ℕ} {B : ℝ}
    (hK : (k : ℝ) + B ≤ (K : ℝ)) (hK1 : 1 ≤ K) :
    Real.log N ^ k * (1 + Real.log N) ^ B ≤ (K : ℝ) ^ K * N := by
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN
  have hP : (0 : ℝ) < (1 + Real.log N) ^ B := Real.rpow_pos_of_pos (by linarith) _
  calc Real.log N ^ k * (1 + Real.log N) ^ B
      ≤ (1 + Real.log N) ^ (k : ℝ) * (1 + Real.log N) ^ B := by
        rw [Real.rpow_natCast]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlog0 (by linarith) k) hP.le
    _ = (1 + Real.log N) ^ ((k : ℝ) + B) := (Real.rpow_add (by linarith) _ _).symm
    _ ≤ (1 + Real.log N) ^ (K : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hK
    _ = (1 + Real.log N) ^ K := Real.rpow_natCast _ _
    _ ≤ (K : ℝ) ^ K * N := one_add_log_pow_le hN hK1

/-- **A smooth sequence has the Siegel–Walfisz property.** For smoothness data `c`, `C`, `b`, `w`
with `0 < c` there are a constant `S` and a divisor exponent `E`, both functions of the saving `B`
and of those four data alone, such that every sequence smooth at a scale `N ≥ 1` with them has the
Siegel–Walfisz property at `N` with `S` and `E`.

Read at a bundle `K` this is the source's `K♯ = Σ K`: apply it to `K.scaleLo`, `K.scaleHi`,
`K.smoothConst`, `K.smoothPow` and take for `Σ K` the update of `K` whose `siegelWalfiszConst` is
`S` and whose `siegelWalfiszPow` is `E`, a bundle differing from `K` in those two components alone,
so that every other clause a datum satisfies at `K` it satisfies at `Σ K` by `rfl`.

The hypothesis `0 < c` is not used: it is what the source's Poisson-summation route needs, and the
pairing route taken here holds for any `c`. -/
@[gap212 "lem_smooth_has_siegel_walfisz"]
theorem exists_hasSiegelWalfisz_of_isSmoothAtScale (c C : ℝ) (_hc : 0 < c) (b : ℕ → ℝ)
    (w : ℕ → ℕ) :
    ∃ (S : ℝ → ℝ) (E : ℝ → ℕ), ∀ (α : ℕ → ℂ) (N : ℝ), 1 ≤ N →
      IsSmoothAtScale c C b w α N → HasSiegelWalfisz S E α N := by
  refine ⟨fun B => 4 * (1 + max (C - c) 0) * (|b 0| + |b 1|) *
    ((w 0 + w 1 + ⌈B⌉₊ + 1 : ℕ) : ℝ) ^ (w 0 + w 1 + ⌈B⌉₊ + 1), fun _ => 1, ?_⟩
  intro α N hN hsm B hB q hq r hr a hacop
  obtain ⟨ψ, hψc, hψs, hψb, hψα⟩ := hsm
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN
  have hL0 : (0 : ℝ) < (1 + Real.log N) ^ B := Real.rpow_pos_of_pos (by linarith) _
  have hdiff : Differentiable ℝ ψ := hψc.differentiable (by simp)
  have h₀ : ∀ t, ‖ψ t‖ ≤ b 0 * Real.log N ^ w 0 := fun t => by simpa using hψb 0 t
  have h₁ : ∀ t, ‖deriv ψ t‖ ≤ b 1 * Real.log N ^ w 1 := fun t => by simpa using hψb 1 t
  -- The profile vanishes off `[c, C]`, so `α` vanishes from `⌊C N⌋ + 1` on.
  set M := ⌊C * N⌋₊ + 1 with hM
  have hzero : ∀ n : ℕ, M ≤ n → α n = 0 := by
    intro n hn
    by_contra hne
    have := Nat.le_floor ((div_le_iff₀ hN0).1 (hψs _ (by rwa [← hψα n])).2)
    omega
  have hF : Function.support α ⊆ ↑(range M) := fun n hne =>
    Finset.mem_range.2 (not_le.1 fun h => hne (hzero n h))
  rw [discrepancy_eq_moebius_sum hF hq (by omega : r ≠ 0) a, le_div_iff₀ hL0]
  set K := w 0 + w 1 + ⌈B⌉₊ + 1 with hK
  have habs : (b 0 * Real.log N ^ w 0 + b 1 * Real.log N ^ w 1) * (1 + Real.log N) ^ B
      ≤ (|b 0| + |b 1|) * ((K : ℝ) ^ K * N) := by
    have hcB := Nat.le_ceil B
    have e₀ := log_pow_mul_rpow_le hN (k := w 0) (K := K) (B := B) (by rw [hK]; push_cast; linarith)
      (by omega)
    have e₁ := log_pow_mul_rpow_le hN (k := w 1) (K := K) (B := B) (by rw [hK]; push_cast; linarith)
      (by omega)
    linarith [mul_le_mul_of_nonneg_right (le_abs_self (b 0))
        (mul_nonneg (pow_nonneg hlog0 (w 0)) hL0.le),
      mul_le_mul_of_nonneg_right (le_abs_self (b 1)) (mul_nonneg (pow_nonneg hlog0 (w 1)) hL0.le),
      mul_le_mul_of_nonneg_left e₀ (abs_nonneg (b 0)),
      mul_le_mul_of_nonneg_left e₁ (abs_nonneg (b 1))]
  have hdvd : (r.divisors.card : ℝ) ≤ ((q * r).divisors.card : ℝ) := by
    exact_mod_cast Finset.card_le_card
      (Nat.divisors_subset_of_dvd (by positivity) (dvd_mul_left r q))
  simp only [pow_one]
  -- The discrepancy is at most `τ(r)` pairing bounds, and `τ(r) ≤ τ(q r)`.
  refine (mul_le_mul_of_nonneg_right (norm_sum_divisors_moebius_average_le
    (filter_coprime_range_nonempty hq)
    fun d hd x hx => norm_sum_class_sub_le hN hdiff hψs h₀ h₁ hψα hzero hq
      (Nat.pos_of_mem_divisors hd) (Nat.coprime_comm.1 hacop) (Finset.mem_filter.1 hx).2)
    hL0.le).trans ?_
  have hc : (0 : ℝ) ≤ 4 * (1 + max (C - c) 0) := by positivity
  linarith [mul_le_mul_of_nonneg_left habs (mul_nonneg (Nat.cast_nonneg r.divisors.card) hc),
    mul_le_mul_of_nonneg_right hdvd
      (by positivity : (0 : ℝ) ≤ 4 * (1 + max (C - c) 0) * ((|b 0| + |b 1|) * ((K : ℝ) ^ K * N)))]

end Smooth

/-! ### The trivial discrepancy bound -/

/-- Scaling a positive quantity up cannot decrease the truncated floor of its multiple, whatever
the sign of the multiplier: for `0 ≤ c` this is `Nat.floor_le_floor`, and for `c < 0` the left-hand
side is `0` because `c * N < 0`. -/
private lemma floor_mul_le_floor_mul_of_le {c N y : ℝ} (hN : 0 < N) (hNy : N ≤ y) :
    ⌊c * N⌋₊ ≤ ⌊c * y⌋₊ := by
  rcases le_or_gt 0 c with hc | hc
  · exact Nat.floor_le_floor (by nlinarith)
  · exact (Nat.floor_of_nonpos (by nlinarith)).trans_le (Nat.zero_le _)

/-- Every index of `Finset.Icc 1 ⌊c₁ * y⌋₊` is positive and at most `c₁ * y`, so the coefficient
bound applies there and its logarithmic factor may be taken at `1 + c₁ * y`, out of the sum. -/
private lemma norm_le_of_mem_Icc_one_floor {C : ℝ} {k l : ℕ} {c₁ y : ℝ} {f : ℕ → ℂ}
    (hf : IsCoefficientSequence C k l f) {n : ℕ} (hn : n ∈ Finset.Icc 1 ⌊c₁ * y⌋₊) :
    ‖f n‖ ≤ C * (1 + Real.log (1 + c₁ * y)) ^ l * (n.divisors.card : ℝ) ^ k := by
  rw [Finset.mem_Icc] at hn
  have hcy : (1 : ℝ) ≤ c₁ * y := Nat.floor_pos.1 (hn.1.trans hn.2)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
  have hnle : (n : ℝ) ≤ c₁ * y := (Nat.le_floor_iff (by linarith)).1 hn.2
  have hle : Real.log n ≤ Real.log (1 + c₁ * y) := Real.log_le_log (by linarith) (by linarith)
  have hlog : (1 + Real.log n) ^ l ≤ (1 + Real.log (1 + c₁ * y)) ^ l :=
    pow_le_pow_left₀ (by linarith [Real.log_nonneg hn1]) (by linarith) l
  -- At `n = 1` both factors of the coefficient bound are `1`, so `C` is nonnegative.
  have hC : (0 : ℝ) ≤ C := by simpa using (norm_nonneg (f 1)).trans (hf 1 le_rfl)
  refine (hf n hn.1).trans ?_
  rw [mul_right_comm]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hC) (by positivity)

/-- **The majorisation.** A sum of `f` over any subset of the range the location hypothesis
confines its support to is at most `Λ(y) / 2`. Both sums of the discrepancy are of this form, the
subset being the range cut by a congruence and by a coprimality condition. -/
private lemma norm_sum_le_of_subset {C : ℝ} {k l : ℕ} {c₀ c₁ : ℝ} {f : ℕ → ℂ} {N y : ℝ}
    (hf : IsCoefficientSequence C k l f) (hf0 : f 0 = 0) (hN : 0 < N) (hNy : N ≤ y)
    {u : Finset ℕ} (hu : u ⊆ Finset.Icc ⌈c₀ * N⌉₊ ⌊c₁ * N⌋₊) :
    ‖∑ n ∈ u, f n‖ ≤ C * (1 + Real.log (1 + c₁ * y)) ^ l *
      ∑ n ∈ Finset.Icc 1 ⌊c₁ * y⌋₊, (n.divisors.card : ℝ) ^ k := by
  have hsub : u ⊆ insert 0 (Finset.Icc 1 ⌊c₁ * y⌋₊) := fun n hn ↦ by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_Icc.2
        ⟨hn0, (Finset.mem_Icc.1 (hu hn)).2.trans (floor_mul_le_floor_mul_of_le hN hNy)⟩)
  refine (norm_sum_le _ _).trans
    ((Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ norm_nonneg _).trans ?_)
  rw [Finset.sum_insert (by simp), hf0, norm_zero, zero_add, Finset.mul_sum]
  exact Finset.sum_le_sum fun _ hn ↦ norm_le_of_mem_Icc_one_floor hf hn

/-- Subtracting `1 / (m : ℂ)` times one quantity from another doubles a common bound on the two,
for every natural `m`: the factor has modulus `1 / m ≤ 1` for `m ≥ 1`, and is `0` at `m = 0`. This
is the recombination of the discrepancy's two sums, whose factor is `1 / (φ d : ℂ)`. -/
private lemma norm_sub_one_div_natCast_mul_le {A B : ℂ} {t : ℝ} (m : ℕ)
    (hA : ‖A‖ ≤ t) (hB : ‖B‖ ≤ t) : ‖A - 1 / (m : ℂ) * B‖ ≤ 2 * t := by
  have hm : ‖(1 : ℂ) / (m : ℂ)‖ ≤ 1 := by simpa using Nat.cast_inv_le_one (α := ℝ) m
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  nlinarith [norm_nonneg B, norm_nonneg ((1 : ℂ) / (m : ℂ))]

/-- **The trivial discrepancy bound**, pointwise in the modulus and the residue class. -/
private lemma norm_sumError_le_of_located {C : ℝ} {k l : ℕ} {c₀ c₁ : ℝ} {f : ℕ → ℂ} {N y : ℝ}
    (hf : IsCoefficientSequence C k l f) (hloc : LocatedAtScale c₀ c₁ f N) (hf0 : f 0 = 0)
    (hN : 0 < N) (hNy : N ≤ y) (d a : ℕ) :
    ‖sumError f d a‖ ≤ 2 * C * (1 + Real.log (1 + c₁ * y)) ^ l *
      ∑ n ∈ Finset.Icc 1 ⌊c₁ * y⌋₊, (n.divisors.card : ℝ) ^ k := by
  have heq := (support_subset_Icc_and_finsum_mem_eq_sum_filter_of_located hloc hf0).2
  rw [sumError, heq _, heq _]
  exact (norm_sub_one_div_natCast_mul_le _
    (norm_sum_le_of_subset hf hf0 hN hNy (Finset.filter_subset _ _))
    (norm_sum_le_of_subset hf hf0 hN hNy (Finset.filter_subset _ _))).trans_eq (by ring)

/-- The ambient range of moduli has at most `x ^ (1/2 + 2 * ω)` elements, hence so has every family
inside it. -/
private lemma card_le_rpow_of_subset_moduliRange {x ω : ℝ} (hx : 0 ≤ x) {D : Finset ℕ}
    (hD : D ⊆ moduliRange x ω) : (D.card : ℝ) ≤ x ^ (1 / 2 + 2 * ω) :=
  calc (D.card : ℝ) ≤ ((moduliRange x ω).card : ℝ) := by exact_mod_cast Finset.card_le_card hD
    _ = (⌊x ^ (1 / 2 + 2 * ω)⌋₊ : ℝ) := by rw [moduliRange, Nat.card_Icc]; simp
    _ ≤ _ := Nat.floor_le (Real.rpow_nonneg hx _)

/-- **The trivial discrepancy bound.** Let `f` be a coefficient sequence with constants `C`, `k`,
`l` — so `‖f n‖ ≤ C * τ(n) ^ k * (1 + log n) ^ l` for `n ≥ 1` — located between the endpoints `c₀`
and `c₁` at a scale `N > 0`, and vanishing at `0`. Then for every `y ≥ N`, every modulus `d` and
every residue `a`,
`‖Δ(f; d, a)‖ ≤ 2 * C * (1 + log (1 + c₁ * y)) ^ l * ∑_{1 ≤ n ≤ c₁ * y} τ(n) ^ k`,
and consequently the same quantity times `x ^ (1/2 + 2 * ω)` bounds `∑_{d ∈ D} ‖Δ(f; d, a)‖` for
every `x ≥ 0`, every `ω` and every family of moduli `D ⊆ Gap212.moduliRange x ω`.

The bound depends on the sequence only through its constants and an upper bound `y` for its scale,
which is what lets it absorb a bounded range of `x` in an estimate proved beyond a threshold. -/
theorem norm_sumError_le_and_sum_norm_sumError_le_of_located
    {C : ℝ} {k l : ℕ} {c₀ c₁ : ℝ} {f : ℕ → ℂ} {N y : ℝ}
    (hf : IsCoefficientSequence C k l f) (hloc : LocatedAtScale c₀ c₁ f N)
    (hf0 : f 0 = 0) (hN : 0 < N) (hNy : N ≤ y) (a : ℕ) :
    (∀ d : ℕ, ‖sumError f d a‖ ≤
        2 * C * (1 + Real.log (1 + c₁ * y)) ^ l *
          ∑ n ∈ Finset.Icc 1 ⌊c₁ * y⌋₊, (n.divisors.card : ℝ) ^ k) ∧
      ∀ (x ω : ℝ), 0 ≤ x → ∀ D ⊆ moduliRange x ω,
        ∑ d ∈ D, ‖sumError f d a‖ ≤
          x ^ (1 / 2 + 2 * ω) * (2 * C * (1 + Real.log (1 + c₁ * y)) ^ l *
            ∑ n ∈ Finset.Icc 1 ⌊c₁ * y⌋₊, (n.divisors.card : ℝ) ^ k) := by
  have key : ∀ d : ℕ, ‖sumError f d a‖ ≤ 2 * C * (1 + Real.log (1 + c₁ * y)) ^ l *
      ∑ n ∈ Finset.Icc 1 ⌊c₁ * y⌋₊, (n.divisors.card : ℝ) ^ k :=
    fun d ↦ norm_sumError_le_of_located hf hloc hf0 hN hNy d a
  refine ⟨key, fun x ω hx D hD ↦ (Finset.sum_le_card_nsmul _ _ _ fun d _ ↦ key d).trans ?_⟩
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (card_le_rpow_of_subset_moduliRange hx hD)
    ((norm_nonneg _).trans (key 0))

end Gap212
