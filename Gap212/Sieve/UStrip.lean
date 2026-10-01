/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.SimplexVolume
public import Gap212.Defs
public meta import Gap212.Attr

/-!
# The discarded strip is thin

The computable numerator of the tensor sieve is `∫ (Γᵢ² - Γ_{i,𝒰}²)` over the part of the orthant
below the retreated cutoff `c`, so what has to be thrown away is `∫ Γ_{i,𝒰}²` there. This file
bounds it by a fixed multiple of the mesh `ε₃`: below the cutoff the high part of the marginal can
only be non-zero inside a strip of width `(k-1)ε₃`, and such a strip inside the corner simplex of
size `c` has volume at most `(k-1)ε₃c^{k-2}/(k-2)!`.

## Why the high indices are confined to a strip

`𝓛(i)` is a condition on the *upper support endpoints* of the other factors,
`∑_{s≠i} β_{l,s} < c`, so `l ∉ 𝓛(i)` says immediately that `∑_{s≠i} β_{l,s} ≥ c`. If
`Γ_{i,𝒰}(u) ≠ 0` then some high `l` has all its other factors non-zero at `u`, so each `u_s` lies
in `[α_{l,s}, β_{l,s}]`, an interval of length at most `ε₃`, whence `u_s ≥ β_{l,s} - ε₃` and
`∑_{s≠i} u_s ≥ c - (k-1)ε₃`.

## Three departures from the inequality as usually stated

Two are generalizations; the third is an added hypothesis, and it is not optional.

* The sup norm `‖Γᵢ‖_∞` is replaced by *any* bound `M` on `|Γᵢ|`. At `M = ‖Γᵢ‖_∞` this is the
  usual inequality, so the statement here implies it.
* The support datum, the band `j` and the level `ε₀` are dropped: they enter only through
  `c = (1-ε₀)(A_j-ε)`, so the statement is made about an arbitrary real `c`.
* `0 ≤ c` is **added**. At `c < 0` the region of integration is empty, so the left side is `0`,
  while the right side is `(k-1)ε₃c^{k-2}/(k-2)!·M²`, which for odd `k-2` and positive `ε₃, M` is
  *negative*: the inequality is false there. In context `c ≥ 0` does hold —
  `Gap212.GPY.exists_tensorDatum_forms_gap` supplies a `c` at which `J̃_c` is positive, forcing the
  region to be non-empty — but it is not derivable from `Gap212.SupportParams`, which places no
  lower bound on `A_j - ε` at all. Likewise `0 ≤ ε₃` is asked for: with every `g_{l,i}` zero the
  support intervals are empty and an `ε₃ < 0` satisfies the length condition vacuously.

## Main results

* `Gap212.GPY.tensorMarginalHigh_vanishing`: below the cutoff, `Γ_{i,𝒰}` vanishes off the strip.
* `Gap212.GPY.setIntegral_sq_le_of_vanishes_off_strip`: the measure-theoretic half, for an
  arbitrary function vanishing off the strip.
* `Gap212.GPY.setIntegral_tensorMarginalHigh_sq_le`: the strip estimate.
-/

@[expose] public section

namespace Gap212.GPY

open MeasureTheory Set
open scoped Nat

variable {L r : ℕ}

/-! ### The measure-theoretic half -/

/-- **A bounded function vanishing off the strip has a small integral over the simplex.** If
`Ψ² ≤ M²` everywhere and `Ψ` vanishes at every non-negative point of coordinate sum in `[0, c]`
whose sum is below `d`, then `∫_{u ≥ 0, ∑ u_s ≤ c} Ψ² ≤ M²(c-d)c^n/n!`.

Restricting the region to the strip changes nothing, since the integrand vanishes on the
difference; and on the strip the integrand is at most `M²`, so the integral is at most `M²` times
the strip's volume, which `Gap212.GPY.volumeReal_strip_le` bounds. No measurability of `Ψ` is
needed: the constant bound on a set of finite measure suffices. -/
theorem setIntegral_sq_le_of_vanishes_off_strip {n : ℕ} {c d M : ℝ} (hd : 0 ≤ d) (hdc : d ≤ c)
    {Ψ : (Fin (n + 1) → ℝ) → ℝ} (hM : ∀ u, Ψ u ^ 2 ≤ M ^ 2)
    (hvan : ∀ u, (∀ s, 0 ≤ u s) → ∑ s, u s ≤ c → ¬ d ≤ ∑ s, u s → Ψ u = 0) :
    (∫ u in {u : Fin (n + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c}, Ψ u ^ 2)
      ≤ M ^ 2 * ((c - d) * c ^ n / (n ! : ℝ)) := by
  have hc : (0 : ℝ) ≤ c := le_trans hd hdc
  have hsub : {u : Fin (n + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c ∧ d ≤ ∑ s, u s}
      ⊆ {u : Fin (n + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c} := fun u hu ↦ ⟨hu.1, hu.2.1⟩
  have heq : (∫ u in {u : Fin (n + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c}, Ψ u ^ 2)
      = ∫ u in {u : Fin (n + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c ∧ d ≤ ∑ s, u s},
          Ψ u ^ 2 := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_cornerSimplex _ _) hsub ?_
    intro u hu
    obtain ⟨⟨h0, hle⟩, hnot⟩ := hu
    rw [hvan u h0 hle fun h ↦ hnot ⟨h0, hle, h⟩]
    ring
  have hfin : volume {u : Fin (n + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c ∧ d ≤ ∑ s, u s}
      < ⊤ := by
    refine lt_of_le_of_lt (measure_mono hsub) ?_
    rw [volume_cornerSimplex (n + 1) c hc]
    exact ENNReal.ofReal_lt_top
  have hbdd : ∀ u ∈ {u : Fin (n + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c ∧ d ≤ ∑ s, u s},
      ‖Ψ u ^ 2‖ ≤ M ^ 2 := by
    intro u _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hM u
  rw [heq]
  calc (∫ u in {u : Fin (n + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c ∧ d ≤ ∑ s, u s}, Ψ u ^ 2)
      ≤ ‖∫ u in {u : Fin (n + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c ∧ d ≤ ∑ s, u s},
          Ψ u ^ 2‖ := Real.le_norm_self _
    _ ≤ M ^ 2 * volume.real {u : Fin (n + 1) → ℝ |
          (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c ∧ d ≤ ∑ s, u s} :=
        norm_setIntegral_le_of_norm_le_const hfin hbdd
    _ ≤ M ^ 2 * ((c - d) * c ^ n / (n ! : ℝ)) :=
        mul_le_mul_of_nonneg_left (volumeReal_strip_le n hd hdc) (sq_nonneg M)

/-! ### The support of the high part of the marginal -/

/-- **Below the cutoff the high part of the marginal is confined to a strip.** If
`Γ_{i,𝒰}(u) ≠ 0` then `∑_{s≠i} u_s ≥ c - (k-1)ε₃`, at `k = r + 2`.

The witness is a high index `l` all of whose other factors are non-zero at `u`: each `u_s` then
lies in `[α_{l,s}, β_{l,s}]`, so `u_s ≥ β_{l,s} - ε₃`, and `l ∉ 𝓛(i)` gives `∑_{s≠i} β_{l,s} ≥ c`.
-/
theorem tensorMarginalHigh_vanishing {c ε₃ : ℝ} {cf : Fin L → ℝ}
    {g : Fin L → Fin (r + 2) → ℝ → ℝ} {α β : Fin L → Fin (r + 2) → ℝ} {i : Fin (r + 2)}
    (hsupp : ∀ l s, Function.support (g l s) ⊆ Set.Icc (α l s) (β l s))
    (hlen : ∀ l s, β l s - α l s ≤ ε₃) (inMarg : Fin L → Prop) [DecidablePred inMarg]
    (hinMarg : ∀ l, inMarg l ↔ ∑ s : Fin (r + 1), β l (i.succAbove s) < c)
    {u : Fin (r + 1) → ℝ}
    (hne : tensorMarginalHigh cf g (Gap212.Defs.USet inMarg) i u ≠ 0) :
    c - ((r : ℝ) + 1) * ε₃ ≤ ∑ s, u s := by
  simp only [tensorMarginalHigh] at hne
  obtain ⟨l, hl, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  -- The product of the other factors is non-zero at `u`, hence every factor is.
  have hprod : (∏ s : Fin (r + 1), g l (i.succAbove s) (u s)) ≠ 0 := fun h ↦ hterm (by
    rw [h]; ring)
  have hfac : ∀ s : Fin (r + 1), g l (i.succAbove s) (u s) ≠ 0 :=
    fun s ↦ Finset.prod_ne_zero_iff.mp hprod s (Finset.mem_univ s)
  -- Each coordinate is within `ε₃` of the upper endpoint of its factor's support.
  have hcoord : ∀ s : Fin (r + 1), β l (i.succAbove s) - ε₃ ≤ u s := by
    intro s
    have hmem : u s ∈ Set.Icc (α l (i.succAbove s)) (β l (i.succAbove s)) :=
      hsupp l (i.succAbove s) (hfac s)
    have h1 := hlen l (i.succAbove s)
    have h2 := hmem.1
    linarith
  -- The index is high, so its endpoint sum reaches the cutoff.
  have hhigh : c ≤ ∑ s : Fin (r + 1), β l (i.succAbove s) := by
    have hmem := hl
    simp only [Gap212.Defs.USet, Finset.mem_filter] at hmem
    exact not_lt.mp fun h ↦ hmem.2 ((hinMarg l).mpr h)
  have hcard : (∑ _s : Fin (r + 1), ε₃) = ((r : ℝ) + 1) * ε₃ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hsum : (∑ s : Fin (r + 1), β l (i.succAbove s)) - ((r : ℝ) + 1) * ε₃ ≤ ∑ s, u s := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (r + 1))))
      (f := fun s ↦ β l (i.succAbove s) - ε₃) (g := u) fun s _ ↦ hcoord s
    rwa [Finset.sum_sub_distrib, hcard] at h
  linarith

/-! ### The strip estimate -/

/-- **The discarded strip is thin.** For a tensor datum with non-negative coefficients whose
factors are the tails of non-negative `g_{l,i}` supported in intervals `[α_{l,i}, β_{l,i}]` of
length at most `ε₃`, and for any bound `M` on `|Γᵢ|`,
`∫_{u ≥ 0, ∑ u_s ≤ c} Γ_{i,𝒰}² ≤ (k-1)ε₃c^{k-2}/(k-2)! · M²`, at `k = r + 2`.

All the coefficients and all the `g`'s are non-negative, so `0 ≤ Γ_{i,𝒰} ≤ Γᵢ ≤ M` pointwise — `Γᵢ`
is the same sum over the larger index set. Below the cutoff `Γ_{i,𝒰}` vanishes off the strip
`c - (k-1)ε₃ ≤ ∑ u_s ≤ c` by `Gap212.GPY.tensorMarginalHigh_vanishing`, and that strip has volume
at most `(k-1)ε₃c^{k-2}/(k-2)!` by `Gap212.GPY.volumeReal_strip_le`, which rests on the
corner-simplex volume `Gap212.GPY.volume_cornerSimplex`.

The strip is cut off from below at `max(c - (k-1)ε₃, 0)` rather than at `c - (k-1)ε₃`: a coarse
mesh can put the latter below the origin, where the volume formula would read the wrong way round,
and the region's own non-negativity gives the floor for free.

See the module docstring for the three departures from the usual display: an arbitrary bound
`M` in place of the sup norm, the support datum dropped in favour of a bare cutoff `c`, and the
added `0 ≤ c`, without which the display is false. -/
@[gap212 "lem_U_strip"]
theorem setIntegral_tensorMarginalHigh_sq_le {c ε₃ M : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε₃)
    {cf : Fin L → ℝ} {g : Fin L → Fin (r + 2) → ℝ → ℝ} {α β : Fin L → Fin (r + 2) → ℝ}
    {i : Fin (r + 2)} (hcf : ∀ l, 0 ≤ cf l) (hg : ∀ l s t, 0 ≤ g l s t)
    (hsupp : ∀ l s, Function.support (g l s) ⊆ Set.Icc (α l s) (β l s))
    (hlen : ∀ l s, β l s - α l s ≤ ε₃) (hM : ∀ u, |tensorMarginal cf g i u| ≤ M)
    (inMarg : Fin L → Prop) [DecidablePred inMarg]
    (hinMarg : ∀ l, inMarg l ↔ ∑ s : Fin (r + 1), β l (i.succAbove s) < c) :
    (∫ u in {u : Fin (r + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c},
        tensorMarginalHigh cf g (Gap212.Defs.USet inMarg) i u ^ 2)
      ≤ ((r : ℝ) + 1) * ε₃ * c ^ r / (r ! : ℝ) * M ^ 2 := by
  set d : ℝ := max (c - ((r : ℝ) + 1) * ε₃) 0 with hd_def
  have hd0 : 0 ≤ d := le_max_right _ _
  have hdc : d ≤ c := max_le (sub_le_self c (by positivity)) hc
  have hcd : c - d ≤ ((r : ℝ) + 1) * ε₃ := by
    have h := le_max_left (c - ((r : ℝ) + 1) * ε₃) (0 : ℝ)
    rw [← hd_def] at h
    linarith
  -- Every term of the marginal is non-negative.
  have hterm : ∀ (l : Fin L) (u : Fin (r + 1) → ℝ),
      0 ≤ cf l * (∫ t in Set.Ioi (0 : ℝ), g l i t) *
        ∏ s : Fin (r + 1), g l (i.succAbove s) (u s) :=
    fun l u ↦ mul_nonneg (mul_nonneg (hcf l)
      (setIntegral_nonneg measurableSet_Ioi fun t _ ↦ hg l i t))
      (Finset.prod_nonneg fun s _ ↦ hg _ _ _)
  -- Hence `0 ≤ Γ_{i,𝒰} ≤ Γᵢ ≤ M` pointwise, and `Γ_{i,𝒰}² ≤ M²`.
  have hΨ0 : ∀ u : Fin (r + 1) → ℝ,
      0 ≤ tensorMarginalHigh cf g (Gap212.Defs.USet inMarg) i u := by
    intro u
    simp only [tensorMarginalHigh]
    exact Finset.sum_nonneg fun l _ ↦ hterm l u
  have hΨΓ : ∀ u : Fin (r + 1) → ℝ,
      tensorMarginalHigh cf g (Gap212.Defs.USet inMarg) i u ≤ tensorMarginal cf g i u := by
    intro u
    simp only [tensorMarginal, tensorMarginalHigh]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun l _ _ ↦ hterm l u
  have hsq : ∀ u : Fin (r + 1) → ℝ,
      tensorMarginalHigh cf g (Gap212.Defs.USet inMarg) i u ^ 2 ≤ M ^ 2 := fun u ↦
    pow_le_pow_left₀ (hΨ0 u) (le_trans (hΨΓ u) (le_trans (le_abs_self _) (hM u))) 2
  -- Below the cutoff the high part vanishes off the strip.
  have hvan : ∀ u : Fin (r + 1) → ℝ, (∀ s, 0 ≤ u s) → ∑ s, u s ≤ c → ¬ d ≤ ∑ s, u s →
      tensorMarginalHigh cf g (Gap212.Defs.USet inMarg) i u = 0 := by
    intro u h0 _ hnot
    by_contra hne
    refine hnot ?_
    rw [hd_def]
    exact max_le (tensorMarginalHigh_vanishing hsupp hlen inMarg hinMarg hne)
      (Finset.sum_nonneg fun s _ ↦ h0 s)
  calc (∫ u in {u : Fin (r + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c},
        tensorMarginalHigh cf g (Gap212.Defs.USet inMarg) i u ^ 2)
      ≤ M ^ 2 * ((c - d) * c ^ r / (r ! : ℝ)) :=
        setIntegral_sq_le_of_vanishes_off_strip hd0 hdc hsq hvan
    _ ≤ M ^ 2 * (((r : ℝ) + 1) * ε₃ * (c ^ r / (r ! : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg M)
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hcd
          (div_nonneg (pow_nonneg hc r) (Nat.cast_nonneg _))
    _ = ((r : ℝ) + 1) * ε₃ * c ^ r / (r ! : ℝ) * M ^ 2 := by ring

end Gap212.GPY
