/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Equidistribution.Moduli
public import Gap212.Extraction.TwoFactor
public import Gap212.Extraction.ThreeFactor
public import Gap212.Extraction.FourFactor
public import Gap212.Packing.LogBridge

/-!
# From extraction to membership in a moduli set

The routing argument needs containments `Q ⊆ D_type`: every modulus the support generates lies in
the moduli set of whichever estimate is being applied. This module builds that bridge for the
one-divisor sets — `D_{IIa}` and `D_{III}`, and the first two branches of `D_I` — all of which are
cut by a single condition `HasDivisorIn d x a' b'`.

## Closed windows against open ones

The extraction lemmas produce a divisor in a **closed** window `[x^a, x^b]`; the moduli sets demand
an **open** one, `x^{a'} < r < x^{b'}`. So the extraction has to be run on a window strictly inside
the target, and since the extraction also needs its own window to be at least `δ` wide, the target
must be *strictly* wider than `δ`.

That is exactly what the conditions (I), (II), (III) of [2, Proposition 3] supply: each is a strict
inequality `min{…} - 2ϵ > δ`, so the `δ*(γ)` it licenses satisfies `δ < δ*(γ)`. Taking
`η = (δ* - δ)/2 > 0` and running the extraction on `[a' + η, b' - η]` leaves a window of width
exactly `δ` — the minimum the extraction accepts — strictly inside the target. Nothing is wasted,
and the strictness of the conditions is load-bearing rather than cosmetic.

**But the inset is not the right way to pay for it, and is not needed.** Running the extraction on
a retreated window forces the packing condition to be met at the retreated capacities `b' - η` and
`1/2 - a' - η`, and that inset is slack Conditions A and E do not have. It is also avoidable: the
extraction produces its divisor strictly inside the *bare* window already, the top end because the
selected rough part has logarithm `(1 - ε₀) ∑_{I₁} y ≤ (1 - ε₀) b < b`, and the bottom end because
the modulus threshold `ε₁` may be chosen strictly below `ε₀(1/2 - a)`. That is
`Gap212.Routing.hasDivisorIn_of_qgen_strict`, and it is the bridge to prefer; the inset form is
`Gap212.Routing.hasDivisorIn_of_qgen`.

## The level `ω` comes out symmetric

`Gap212.Extraction.qgen_le` bounds a generated modulus by `x^{(1-ε₀)(A_j + A_{j'})}`, and the
moduli sets live in `moduliRange x ω = [1, x^{1/2+2ω}]`. Setting `ω = (A_j + A_{j'})/2 - 1/4` makes
`1/2 + 2ω = A_j + A_{j'}`, so the containment holds with room to spare — the `(1-ε₀)` is slack.
This `ω` is the `ω_max` of [2].

## Main results

* `Gap212.Routing.hasDivisorIn_of_qgen`: the closed-to-open bridge, paid for with an inset.
* `Gap212.Routing.hasDivisorIn_of_qgen_strict`: the same bridge at the **bare** capacities, the
  strictness coming from the retreat `1 - ε₀` and from the threshold `ε₁`.
* `Gap212.Routing.mem_moduliRange_of_qgen`: generated moduli lie in the ambient range.
* `Gap212.Routing.mem_moduliIIa_of_qgen`, `mem_moduliIII_of_qgen`: the one-divisor containments.
* `Gap212.Routing.mem_moduliIIb_of_qgen`: the nested two-divisor containment.
* `Gap212.Routing.mem_moduliIIc_of_qgen`: the triply-nested containment.
-/

@[expose] public section

namespace Gap212.Routing

open Finset Real Gap212.Packing Gap212.Extraction

/-- A generated modulus is at least `1`. -/
private lemma one_le_of_mem_Qgen {p : SupportParams} {x ε₀ : ℝ} {j j' : Fin p.n} {m m' q : ℕ}
    (hq : q ∈ Qgen p x j j' m m' ε₀) : 1 ≤ q := by
  obtain ⟨-, -, -, -, -, h, -⟩ := hq
  exact h

/-- **The closed-to-open bridge.** If the two-block packing condition holds at capacities `b` and
`1/2 - a` for a window `[a, b]` strictly inside `(a', b')`, then every large enough generated
modulus has a divisor strictly inside `(x^{a'}, x^{b'})`. -/
theorem hasDivisorIn_of_qgen {p : SupportParams} {x ε₀ a b a' b' : ℝ}
    {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hδ : 0 < p.δ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (ha : 0 < a) (hab : a + p.δ ≤ b)
    (hlo : a' < a) (hhi : b < b')
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hpack : ∀ y ∈ Xi (p.B j m) (p.B j' m') m m' p.δ, AdmitsPartition₂ y b (1 / 2 - a))
    (hq : q ∈ Qgen p x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ * (1 / 2 - a)) ≤ (q : ℝ)) :
    HasDivisorIn q x a' b' := by
  obtain ⟨r, hrq, hr1, hr2⟩ := two_factor hx hδ hε₀ hε₀1 ha hab hB hB' hpack hq hqbig
  exact ⟨r, Nat.mem_divisors.mpr ⟨hrq, by grind [one_le_of_mem_Qgen hq]⟩,
    (rpow_lt_rpow_of_exponent_lt hx hlo).trans_le hr1,
    hr2.trans_lt (rpow_lt_rpow_of_exponent_lt hx hhi)⟩

/-- **The bridge at the bare capacities.** If the two-block packing condition holds at the window's
own capacities `b` and `1/2 - a`, then every generated modulus above `x^{1/2 - ε₁}` has a divisor
strictly inside `(x^a, x^b)` — the target window itself, with no retreated copy of it and no inward
inset on either capacity.

This is what `Gap212.HasDivisorIn` is cut by, so it is the form the containments `Q ⊆ D_type`
consume, and it supersedes `Gap212.Routing.hasDivisorIn_of_qgen` wherever the caller can meet its
one extra demand: the threshold `ε₁` must sit *strictly* below `ε₀(1/2 - a)`, rather than at it.
`ε₁ = ε₀ p.δ / 2` qualifies whenever `p.δ ≤ 1/2 - a`, which is the hypothesis of [2] on the
window, and it depends only on `ε₀` and `δ` as the extraction lemma requires.

The strictness of the two ends is produced by `Gap212.Extraction.two_factor_strict`, from the
retreat `1 - ε₀` at the top and from `ε₁` at the bottom. `Gap212.Routing.hasDivisorIn_of_qgen`
instead asks the caller for a window `[a, b]` strictly inside `(a', b')`, and pays for that inset
out of the packing capacities — slack that Conditions A and E do not have. -/
theorem hasDivisorIn_of_qgen_strict {p : SupportParams} {x ε₀ ε₁ a b : ℝ}
    {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hδ : 0 < p.δ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (ha : 0 < a) (hab : a + p.δ ≤ b) (hε₁ : ε₁ < ε₀ * (1 / 2 - a))
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hpack : ∀ y ∈ Xi (p.B j m) (p.B j' m') m m' p.δ, AdmitsPartition₂ y b (1 / 2 - a))
    (hq : q ∈ Qgen p x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₁) ≤ (q : ℝ)) :
    HasDivisorIn q x a b := by
  obtain ⟨r, hrq, hr1, hr2⟩ :=
    two_factor_strict hx hδ hε₀ hε₀1 ha hab hε₁ hB hB' hpack hq hqbig
  exact ⟨r, Nat.mem_divisors.mpr ⟨hrq, by grind [one_le_of_mem_Qgen hq]⟩, hr1, hr2⟩

/-- **Generated moduli lie in the ambient range.** At `ω = (A_j + A_{j'})/2 - 1/4`, a modulus
generated at `(j, j')` lies in `moduliRange x ω`. -/
theorem mem_moduliRange_of_qgen {p : SupportParams} {x ε₀ : ℝ} {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hε₀ : 0 < ε₀)
    (hApos : 0 ≤ p.A j.succ + p.A j'.succ)
    (hq : q ∈ Qgen p x j j' m m' ε₀) :
    q ∈ moduliRange x ((p.A j.succ + p.A j'.succ) / 2 - 1 / 4) := by
  have hmono : x ^ ((1 - ε₀) * (p.A j.succ + p.A j'.succ))
      ≤ x ^ (p.A j.succ + p.A j'.succ) :=
    rpow_le_rpow_of_exponent_le hx.le (by nlinarith [mul_nonneg hε₀.le hApos])
  -- `1/2 + 2ω = A_j + A_{j'}`, and the `(1-ε₀)` factor is slack.
  rw [moduliRange, Finset.mem_Icc]
  exact ⟨one_le_of_mem_Qgen hq,
    Nat.le_floor (((qgen_le hx hq).trans hmono).trans_eq (by congr 1; ring))⟩

/-- **`Q ⊆ D_{IIa}`.** With the Type IIa window of width `δ*` strictly wider than `δ`, every large
enough generated modulus lies in the Polymath Type IIa moduli set at level `ω_max`. -/
theorem mem_moduliIIa_of_qgen {p : SupportParams} {x ε₀ γ δstar ε' : ℝ}
    {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hδ : 0 < p.δ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hδstar : p.δ < δstar)
    (hApos : 0 ≤ p.A j.succ + p.A j'.succ)
    (hlow : 0 < γ - 3 * ε' - δstar + (δstar - p.δ) / 2)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hpack : ∀ y ∈ Xi (p.B j m) (p.B j' m') m m' p.δ,
      AdmitsPartition₂ y (γ - 3 * ε' - (δstar - p.δ) / 2)
        (1 / 2 - (γ - 3 * ε' - δstar + (δstar - p.δ) / 2)))
    (hq : q ∈ Qgen p x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ * (1 / 2 - (γ - 3 * ε' - δstar + (δstar - p.δ) / 2))) ≤ (q : ℝ)) :
    q ∈ moduliIIaFamily x ((p.A j.succ + p.A j'.succ) / 2 - 1 / 4) γ δstar ε' := by
  classical
  rw [moduliIIaFamily, Finset.mem_filter]
  exact ⟨mem_moduliRange_of_qgen hx hε₀ hApos hq, hasDivisorIn_of_qgen hx hδ hε₀ hε₀1 hlow
    (by linarith) (by linarith) (by linarith) hB hB' hpack hq hqbig⟩

/-- **`Q ⊆ D_{III}`.** The Polymath Type III set is cut by the same shape of condition, with window
`[c - δ*, c]` at `c = 1/3 + 4δ*/3 - 4ω/3`. -/
theorem mem_moduliIII_of_qgen {p : SupportParams} {x ε₀ γ δstar ε' : ℝ}
    {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hδ : 0 < p.δ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hδstar : p.δ < δstar)
    (hApos : 0 ≤ p.A j.succ + p.A j'.succ)
    (hlow : 0 < 1 / 3 + 4 * δstar / 3
      - 4 * ((p.A j.succ + p.A j'.succ) / 2 - 1 / 4) / 3 - δstar + (δstar - p.δ) / 2)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hpack : ∀ y ∈ Xi (p.B j m) (p.B j' m') m m' p.δ,
      AdmitsPartition₂ y
        (1 / 3 + 4 * δstar / 3 - 4 * ((p.A j.succ + p.A j'.succ) / 2 - 1 / 4) / 3
          - (δstar - p.δ) / 2)
        (1 / 2 - (1 / 3 + 4 * δstar / 3
          - 4 * ((p.A j.succ + p.A j'.succ) / 2 - 1 / 4) / 3 - δstar + (δstar - p.δ) / 2)))
    (hq : q ∈ Qgen p x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ * (1 / 2 - (1 / 3 + 4 * δstar / 3
      - 4 * ((p.A j.succ + p.A j'.succ) / 2 - 1 / 4) / 3 - δstar + (δstar - p.δ) / 2)))
      ≤ (q : ℝ)) :
    q ∈ moduliIIIFamily x ((p.A j.succ + p.A j'.succ) / 2 - 1 / 4) γ δstar ε' := by
  classical
  rw [moduliIIIFamily, Finset.mem_filter]
  exact ⟨mem_moduliRange_of_qgen hx hε₀ hApos hq, hasDivisorIn_of_qgen hx hδ hε₀ hε₀1 hlow
    (by linarith) (by linarith) (by linarith) hB hB' hpack hq hqbig⟩

/-! ## The nested containment `Q ⊆ D_{IIb}`

`D_{IIb}` asks for two divisors in a *nested* pattern: `r ∣ d`, and then `u` dividing the cofactor
`d / r`. Three-factor extraction delivers `u · r ∣ q`, which is exactly the right shape — that one
divisibility gives both `r ∣ q` and `u ∣ q / r`, by `Nat.dvd_div_iff_mul_dvd`. Had the lemma only
concluded `u ∣ q` and `r ∣ q` separately this containment would not follow, since the two divisors
could then overlap.

Both windows have width exactly `δ` after the strict-to-closed shrink, so the three-factor
hypothesis `b₁ - b₂ ≥ a₁ - a₂` holds with equality and the caller has nothing to check there. -/

/-- **`Q ⊆ D_{IIb}`.** With the two windows sitting strictly inside the Type IIb targets, every
large enough generated modulus lies in the Polymath Type IIb moduli set at level `ω_max`. -/
theorem mem_moduliIIb_of_qgen {p : SupportParams} {x ε₀ γ δstar ε' a₁ b₁ a₂ b₂ : ℝ}
    {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hδ : 0 < p.δ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hApos : 0 ≤ p.A j.succ + p.A j'.succ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hw₁ : a₁ + p.δ ≤ b₁) (hw₂ : a₂ + p.δ ≤ b₂)
    (hstep : a₁ - a₂ ≤ b₁ - b₂)
    (hlo₁ : γ - 3 * ε' - δstar < a₁) (hhi₁ : b₁ < γ - 3 * ε')
    (hlo₂ : 1 / 2 - γ - 2 * ((p.A j.succ + p.A j'.succ) / 2 - 1 / 4) - 6 * ε' - δstar < a₂)
    (hhi₂ : b₂ < 1 / 2 - γ - 2 * ((p.A j.succ + p.A j'.succ) / 2 - 1 / 4) - 6 * ε')
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hpack : ∀ y ∈ Xi (p.B j m) (p.B j' m') m m' p.δ,
      AdmitsPartition₃ y b₁ b₂ (1 / 2 - b₁ - a₂))
    (hq : q ∈ Qgen p x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 - ε₀ * (1 / 2 - b₁ - a₂)) ≤ (q : ℝ)) :
    q ∈ moduliIIbFamily x ((p.A j.succ + p.A j'.succ) / 2 - 1 / 4) γ δstar ε' := by
  classical
  obtain ⟨u, r, hur, hu1, hu2, hr1, hr2⟩ :=
    three_factor hx hδ hε₀ hε₀1 ha₁ ha₂ hw₁ hw₂ hstep hB hB' hpack hq hqbig
  have hq1 := one_le_of_mem_Qgen hq
  -- `r ∣ q` and `u ∣ q / r`, both from the single divisibility `u · r ∣ q`.
  have hrq : r ∣ q := dvd_trans (Dvd.intro_left u rfl) hur
  have hudiv : u ∣ q / r := (Nat.dvd_div_iff_mul_dvd hrq).mpr (by rwa [mul_comm] at hur)
  -- `r` is positive, since it already exceeds `x^{a₁} > 1`.
  have hr0 : 0 < r := by exact_mod_cast (zero_lt_one.trans (one_lt_rpow hx ha₁)).trans_le hr1
  rw [moduliIIbFamily, Finset.mem_filter]
  exact ⟨mem_moduliRange_of_qgen hx hε₀ hApos hq, r, Nat.mem_divisors.mpr ⟨hrq, by lia⟩,
    (rpow_lt_rpow_of_exponent_lt hx hlo₁).trans_le hr1,
    hr2.trans_lt (rpow_lt_rpow_of_exponent_lt hx hhi₁),
    u, Nat.mem_divisors.mpr ⟨hudiv, (Nat.div_pos (Nat.le_of_dvd hq1 hrq) hr0).ne'⟩,
    (rpow_lt_rpow_of_exponent_lt hx hlo₂).trans_le hu1,
    hu2.trans_lt (rpow_lt_rpow_of_exponent_lt hx hhi₂)⟩

/-! ## The triply-nested containment `Q ⊆ D_{IIc}`

`D_{IIc}` is the elaborate one. Beyond `r ∣ d` and `u ∣ d / r` it asks for `d₁ ∣ r` in a window
that depends on **both** `d` and `r`: `(r² x^{2-γ-52ε-δ}/d⁴, r² x^{2-γ-52ε}/d⁴)`.

Two features of that window are worth naming. The `d^{-4}` makes it depend on the size of the
modulus, which is why four-factor extraction is stated on a dyadic block rather than at a global
level. And the `r²` is why that lemma concludes its nested clause for **every** `c ∈ [a₁, b₁]`
rather than for one: the window slides with `r`, so the extraction cannot know in advance which `c`
will be needed. Here it is instantiated at `c = log_x r`, and `r² = x^{2c}` exactly, so the `r²`
cancels against the `x^{2c}` of the extraction's window and what remains is a condition on `a₃` and
`b₃` alone.

The `u`- and `d₁`-window hypotheses below therefore mention `q` directly. That is deliberate: the
routing argument discharges them from the dyadic bound on `q`, and stating them this way keeps this
lemma free of any assumption about how `log_x q` relates to `1/2 + 2ω₀`. -/

set_option maxHeartbeats 800000 in
-- The three nested divisor conditions and their window conversions in one proof.
/-- **`Q ⊆ D_{IIc}`.** Every large enough generated modulus lies in the Stadlmann Type IIc moduli
set at level `ω_max`. -/
theorem mem_moduliIIc_of_qgen {p : SupportParams} {x ε₀ γ δstar ε' a₁ b₁ a₂ b₂ a₃ b₃ ω₀ : ℝ}
    {j j' : Fin p.n} {m m' : ℕ} {q : ℕ}
    (hx : 1 < x) (hδ : 0 < p.δ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hApos : 0 ≤ p.A j.succ + p.A j'.succ)
    (ha₁ : 0 < a₁)
    (hw₁ : a₁ + p.δ ≤ b₁) (hw₂ : a₂ + p.δ ≤ b₂) (hw₃ : a₃ + p.δ ≤ b₃)
    (hstep : a₁ - a₂ ≤ b₁ - b₂) (hnest : 0 ≤ 3 * (b₁ - a₁) + (a₃ - b₃))
    (hlo₁ : γ - 3 * ε' - δstar < a₁) (hhi₁ : b₁ < γ - 3 * ε')
    (hlo₂ : x ^ (1 - γ - 6 * ε' - δstar) / (q : ℝ) < x ^ a₂)
    (hhi₂ : x ^ b₂ < x ^ (1 - γ - 6 * ε') / (q : ℝ))
    (hlo₃ : x ^ (2 - γ - 52 * ε' - δstar) / (q : ℝ) ^ 4 < x ^ a₃)
    (hhi₃ : x ^ b₃ < x ^ (2 - γ - 52 * ε') / (q : ℝ) ^ 4)
    (hB : p.B j m ≤ 1) (hB' : p.B j' m' ≤ 1)
    (hpack : ∀ y ∈ Xi (p.B j m) (p.B j' m') m m' p.δ,
      AdmitsPartition₄ y (2 * a₁ + b₃) b₂ (1 / 2 + 2 * ω₀ - b₁ - a₂) (a₁ - 2 * b₁ - a₃))
    (hq : q ∈ Qgen p x j j' m m' ε₀)
    (hqbig : x ^ (1 / 2 + 2 * ω₀ - ε₀ * (1 / 2 + 2 * ω₀ - b₁ - a₂)) ≤ (q : ℝ)) :
    q ∈ moduliIIcFamily x ((p.A j.succ + p.A j'.succ) / 2 - 1 / 4) γ δstar ε' := by
  classical
  obtain ⟨u, r, hur, hu1, hu2, hr1, hr2, hnested⟩ :=
    four_factor hx hδ hε₀ hε₀1 hw₁ hw₂ hw₃ hstep hnest hB hB' hpack hq hqbig
  have hx0 : (0 : ℝ) < x := by linarith
  have hq1 := one_le_of_mem_Qgen hq
  have hrq : r ∣ q := dvd_trans (Dvd.intro_left u rfl) hur
  have hudiv : u ∣ q / r := (Nat.dvd_div_iff_mul_dvd hrq).mpr (by rwa [mul_comm] at hur)
  -- `r > 1`, since it exceeds `x^{a₁} > 1`.
  have hr1' : 1 ≤ r := by exact_mod_cast (one_lt_rpow hx ha₁).le.trans hr1
  -- Instantiate the nested clause at `c = log_x r`, which lies in the first window.
  set c : ℝ := logb x (r : ℝ)
  obtain ⟨d₁, hd₁r, hd₁lo, hd₁hi⟩ :=
    hnested c (le_logb_of_rpow_le hx hr1' hr1) (logb_le_of_le_rpow hx hr1' hr2)
  -- `r² = x^{2c}` exactly, which is what cancels the `r²` in the target window.
  have hrsq : (r : ℝ) ^ 2 = x ^ (2 * c) := by
    rw [two_mul, Real.rpow_add hx0, Real.rpow_logb hx0 hx.ne' (by positivity)]; ring
  have hx2c : (0 : ℝ) < x ^ (2 * c) := Real.rpow_pos_of_pos hx0 _
  rw [moduliIIcFamily, Finset.mem_filter]
  refine ⟨mem_moduliRange_of_qgen hx hε₀ hApos hq, r, Nat.mem_divisors.mpr ⟨hrq, by lia⟩,
    (rpow_lt_rpow_of_exponent_lt hx hlo₁).trans_le hr1,
    hr2.trans_lt (rpow_lt_rpow_of_exponent_lt hx hhi₁),
    ⟨u, Nat.mem_divisors.mpr ⟨hudiv, (Nat.div_pos (Nat.le_of_dvd hq1 hrq) hr1').ne'⟩,
      hlo₂.trans_le hu1, hu2.trans_lt hhi₂⟩,
    ⟨d₁, Nat.mem_divisors.mpr ⟨hd₁r, by lia⟩, ?_, ?_⟩⟩
  · -- `r² x^{2-γ-52ε-δ}/q⁴ < d₁`, after cancelling `r² = x^{2c}`.
    calc (r : ℝ) ^ 2 * x ^ (2 - γ - 52 * ε' - δstar) / (q : ℝ) ^ 4
        = x ^ (2 * c) * (x ^ (2 - γ - 52 * ε' - δstar) / (q : ℝ) ^ 4) := by rw [hrsq]; ring
      _ < x ^ (2 * c) * x ^ a₃ := mul_lt_mul_of_pos_left hlo₃ hx2c
      _ = x ^ (2 * c + a₃) := (Real.rpow_add hx0 _ _).symm
      _ ≤ (d₁ : ℝ) := hd₁lo
  · -- `d₁ < r² x^{2-γ-52ε}/q⁴`, likewise.
    calc (d₁ : ℝ) ≤ x ^ (2 * c + b₃) := hd₁hi
      _ = x ^ (2 * c) * x ^ b₃ := Real.rpow_add hx0 _ _
      _ < x ^ (2 * c) * (x ^ (2 - γ - 52 * ε') / (q : ℝ) ^ 4) :=
          mul_lt_mul_of_pos_left hhi₃ hx2c
      _ = (r : ℝ) ^ 2 * x ^ (2 - γ - 52 * ε') / (q : ℝ) ^ 4 := by rw [hrsq]; ring

end Gap212.Routing
