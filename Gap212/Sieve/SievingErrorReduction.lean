/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.DivisorSumAssembly
public import Gap212.Sieve.PairwiseCoprimeMoebius
public import Gap212.Sieve.SelbergAssembly
public import Gap212.Sieve.WSieve

/-!
# The two sieving errors, reduced to a one-coordinate estimate

`Gap212.Sieve.SelbergSievingError` and `Gap212.Sieve.TotientSievingError` compare a pair sum over a
full box of divisor tuples with its restriction to the tuples whose least common multiples are
pairwise coprime. `Gap212.Sieve.PairwiseCoprimeMoebius` expands that restriction exactly, at
every number of coordinates, and bounds the resulting configuration sum prime-wise. This file
reduces each of the two sieving errors to one statement about a single coordinate.

## The reduction

Both sums are sums of a product over the coordinates: writing `a_i = (d_i,d'_i)`,

  `Σ(𝓑) = ∏_i (∑_{a∈X} w_i(a))`,  `Σ(𝓢) = ∑_{a : ∀i, a_i∈X, pairwise coprime} ∏_i w_i(a_i)`,

with `X` the box of pairs coprime to `W(x)` and `w_i` the one-coordinate weight —
`Gap212.Sieve.pairWeight` for `Gap212.Sieve.SelbergSievingError` and
`Gap212.Sieve.pairWeightTotient` for `Gap212.Sieve.TotientSievingError`. So
`Gap212.Sieve.exists_threshold_abs_prod_sub_sum_pairwise_coprime_le_rpow` applies verbatim, and
what it needs is a bound on the *one-coordinate* restricted sums.

## The one-coordinate estimate, and why it carries an exponent

The shape one would write first is

  `|A(e)| = O(1/(e·B_x))`  uniformly in `e ≥ 1`,  `B_x = (φ(W)/W)\log x`,

and **that is false**: at the very top of the range the sum degenerates. Take two distinct primes
`P ∈ (B/2,B]` and `Q ∈ (B/4,B/2]` (Bertrand
twice) and `e = PQ`. A pair `(u,v)` in the box with `e ∣ [u,v]` cannot have `PQ ∣ u`, since
`PQ > B`; so `P` divides one coordinate and `Q` the other, and `u ≤ B < 2P` forces that coordinate
to be exactly `P`, while `v = mQ` with `m < 4` and `m` coprime to `W(x)` forces `m = 1`. **Two
pairs survive**, `(P,Q)` and `(Q,P)`, so

  `A(PQ) = (F(\log_xP)G(\log_xQ) + F(\log_xQ)G(\log_xP))/(PQ)`,

which is `≍ 1/e` with a constant `2F(β)G(β) ≠ 0` for profiles not vanishing at `β = \log_xB` —
while the asserted bound `K/(e·B_x)` tends to `0` faster by a factor `B_x`. This is the same
failure mode as `Gap212.Sieve.not_uniformMoebiusPartialSumDecay`: a modulus large enough that the
inner Möbius sum has a single term, and a single term has no cancellation to offer. There the free
modulus was the coprimality condition's; here it is the divisibility condition's, and `B` supplies
the room.

**Weakening the power of `e` handles that witness.**
`|A(e)| ≤ K/(B_x·e^s)` at a fixed `s ∈ (1/2,1)` the modulus `e = PQ ≳ B^2 ≥ x^{2β}` is harmless,
since `B_x/e^{1-s} ≍ \log x/x^{2β(1-s)} → 0`, and the prime-wise regrouping still pays: the fibre
count `τ(M)^{k^2}` is beaten by `M^η` for every `η > 0` once the primes in play are large enough,
so `∑_M M^{η-2s}` converges for every `s > 1/2` — which is exactly
`Gap212.Sieve.exists_threshold_sum_one_div_prod_incLcm_rpow_lt`. The `1/2` is sharp for this
argument: the prime-wise saving is `M^{-2}` per configuration and nothing better, an edge having
two endpoints and no more.

## The truncation

`Gap212.Sieve.OneCoordLcmDecay s` and `Gap212.Sieve.OneCoordTotientDecay s` are the forms just
described, and **both are false for every `s`** — `Gap212.Sieve.not_oneCoordLcmDecay`,
`Gap212.Sieve.not_oneCoordTotientDecay`. The witness is the truncation, not the modulus. They bound
`B` from neither side, and at `B = 1` the one-coordinate box is `{1}` (`Gap212.Sieve.wBox_one`), so
the sum at `e = 1` is the single term `F(0)G(0)` (`Gap212.Sieve.restrictedSum_wBox_one`) with no
cancellation in it at all, while the asserted bound `K/B_x` tends to `0`. Any `C¹` compactly
supported `F` with `F(0) = 1` refutes both, and Mathlib's `exists_contDiff_tsupport_subset`
supplies one. The only analytic input is `B_x ⟶ ∞` (`Gap212.Sieve.eventually_lt_normalization`,
from `Gap212.Sieve.W_sq_le_log`: `W(x)^2 ≤ \log x`, hence `B_x ≥ \log x/W(x) ≥ √{\log x}`).

The witness is not an artefact of `B = 1`: the box is `{1}` for every `B` below the least prime not
dividing `W(x)`, so a whole initial range of truncations carries the same single uncancelled term.
`K/B_x` is the size of this sum only once `B` reaches a fixed power of `x`.

## The truncated forms

`Gap212.Sieve.OneCoordLcmDecayAtLevel s` and `Gap212.Sieve.OneCoordTotientDecayAtLevel s` assert
the bound only for `B ≥ x^β`, and let `K` depend on `β`. That is what
`Gap212.Sieve.SelbergSievingError` and `Gap212.Sieve.TotientSievingError` provide: each supplies
its `β` (with `1 ≤ β`) and then a truncation `B` with `x^β ≤ B(x)` eventually, *before* any
constant is chosen.

**Both truncated forms are false too** (`Gap212.Sieve.not_oneCoordLcmDecayAtLevel` in
`Gap212.Sieve.OneCoordLcmRefutation`, `Gap212.Sieve.not_oneCoordTotientDecayAtLevel` in
`Gap212.Sieve.OneCoordTotientRefutation`), so the hypotheses of the two reductions below are never
satisfied. The witness is the *top of the box*: read the statement at `β = 1`, `B = ⌈x⌉`, `e = 1`
with a profile that does not vanish at `\log_xB = 1`. The Selberg diagonalisation makes the sum at
`F = G` a sum of squares, `∑_{r ≤ B}φ(r)(∑_{r ∣ d}μ(d)F(\log_xd)/d)^2`, and the moduli
`r ∈ (B/2,B]` see a single multiple, so they contribute `≍φ(W)/W` with no cancellation at all —
against an asserted `K/B_x ≤ KW/\log x`. The statement needs the clause
`Gap212.Sieve.LcmGramSumLimitOfSupport` carries: the profiles must vanish from `β` on, so the
truncation does not cut their support. `Gap212.Sieve.OneCoordLcmDecayAtLevelOfSupport` is that
form, and `Gap212.Sieve.tendsto_boxPairSum_sub_sievedPairSum_of_support` is the reduction it
supports, at `β ≥ 1`. The totient denominator changes the diagonalisation's weight from `φ(r)` to
`(μ*φ)(r) = ∏_{p ∣ r}(p-2)` and nothing about that block, so the same reading refutes the totient
form; the corresponding pair there is `Gap212.Sieve.OneCoordTotientDecayAtLevelOfSupport` and
`Gap212.Sieve.tendsto_boxDivisorSum_sub_sievedDivisorSum_of_support`.

`Gap212.Sieve.OneCoordLcmDecayAtLevelOfSupport (3/4)` and
`Gap212.Sieve.OneCoordTotientDecayAtLevelOfSupport (3/4)` are theorems
(`Gap212.Sieve.oneCoordLcmDecayAtLevelOfSupport_three_quarters`,
`Gap212.Sieve.oneCoordTotientDecayAtLevelOfSupport_three_quarters`), and through
`Gap212.Sieve.tendsto_boxPairSum_sub_sievedPairSum_of_support` and
`Gap212.Sieve.tendsto_boxDivisorSum_sub_sievedDivisorSum_of_support` they give
`Gap212.Sieve.selbergSievingError` and `Gap212.Sieve.totientSievingError` at every `m`.

## Main results

* `Gap212.Sieve.boxPairSum_eq_prod`, `Gap212.Sieve.sievedPairSum_eq_sum_guard`: the two Selberg
  sums in the shape the `k`-coordinate identity is stated at.
* `Gap212.Sieve.not_oneCoordLcmDecay`, `Gap212.Sieve.not_oneCoordTotientDecay`: the truncation-free
  one-coordinate estimates are false at every exponent.
* `Gap212.Sieve.OneCoordLcmDecayAtLevel`, `Gap212.Sieve.OneCoordTotientDecayAtLevel`: the truncated
  one-coordinate estimates — also false, by `Gap212.Sieve.not_oneCoordLcmDecayAtLevel` and
  `Gap212.Sieve.not_oneCoordTotientDecayAtLevel`.
* `Gap212.Sieve.selbergSievingError_of_oneCoordLcmDecayAtLevel`,
  `Gap212.Sieve.totientSievingError_of_oneCoordTotientDecayAtLevel`: the reductions to the truncated
  one-coordinate estimates, at every `m`.
-/

@[expose] public section

namespace Gap212.Sieve

open Asymptotics Filter Finset Gap212.Defs Gap212.GPY
open scoped ArithmeticFunction.Moebius

/-! ## The one-coordinate box, modulus and weight -/

/-- **The one-coordinate box**: the divisors in `[1,B]` coprime to `W(x)`, which is what each
coordinate of `Gap212.Sieve.boxPairSum` ranges over. -/
noncomputable def wBox (x : ℝ) (B : ℕ) : Finset ℕ := {d ∈ Icc 1 B | Nat.Coprime (W x) d}

/-- `d ∈ wBox x B` iff `1 ≤ d ≤ B` and `d` is coprime to `W(x)`. -/
theorem mem_wBox {x : ℝ} {B d : ℕ} : d ∈ wBox x B ↔ (1 ≤ d ∧ d ≤ B) ∧ Nat.Coprime (W x) d := by
  simp only [wBox, Finset.mem_filter, Finset.mem_Icc]

/-- **The one-coordinate modulus** `[d,d']` of a pair. -/
def lcmPair (q : ℕ × ℕ) : ℕ := Nat.lcm q.1 q.2

/-- The modulus `lcmPair q` is positive when both coordinates of `q` are. -/
theorem lcmPair_pos {q : ℕ × ℕ} (h1 : 0 < q.1) (h2 : 0 < q.2) : 0 < lcmPair q :=
  Nat.lcm_pos h1 h2

/-- **The one-coordinate weight of `Gap212.Sieve.boxPairSum`**,
`μ(d)F(\log_xd)μ(d')G(\log_xd')/[d,d']`. -/
noncomputable def pairWeight (x : ℝ) (F G : ℝ → ℝ) (q : ℕ × ℕ) : ℝ :=
  (μ q.1 : ℝ) * F (Notation.logx x q.1) * ((μ q.2 : ℝ) * G (Notation.logx x q.2)) / (lcmPair q : ℝ)

/-- **The one-coordinate weight of `Gap212.Sieve.boxDivisorSum`**, the same with the totient
denominator `φ([d,d'])`. -/
noncomputable def pairWeightTotient (x : ℝ) (F G : ℝ → ℝ) (q : ℕ × ℕ) : ℝ :=
  (μ q.1 : ℝ) * F (Notation.logx x q.1) * ((μ q.2 : ℝ) * G (Notation.logx x q.2)) /
    ((lcmPair q).totient : ℝ)

/-! ## The box at the smallest truncation, where there is nothing to cancel -/

/-- **At `B = 1` the one-coordinate box is `{1}`.** `1` is coprime to everything, so the truncation
admits exactly one divisor and the pair sum below has exactly one term. -/
theorem wBox_one (x : ℝ) : wBox x 1 = {1} := by
  ext d
  rw [mem_wBox, Finset.mem_singleton]
  exact ⟨fun ⟨_, _⟩ ↦ by omega, by rintro rfl; simp⟩

/-- **The one-coordinate sum at `B = 1` and `e = 1` is `F(0)G(0)`.** One term, `μ(1) = 1`,
`\log_x1 = 0`, `[1,1] = 1`: no Möbius cancellation is available, so nothing about `x` can make this
small. This is what refutes `Gap212.Sieve.OneCoordLcmDecay`. -/
theorem restrictedSum_wBox_one (x : ℝ) (F G : ℝ → ℝ) :
    restrictedSum (wBox x 1 ×ˢ wBox x 1) lcmPair (pairWeight x F G) 1 = F 0 * G 0 := by
  simp [wBox_one, restrictedSum, pairWeight, lcmPair, Notation.logx]

/-- **The totient-weight companion of `Gap212.Sieve.restrictedSum_wBox_one`**: `φ(1) = 1`, so the
single surviving term is the same. -/
theorem restrictedSum_wBox_one_totient (x : ℝ) (F G : ℝ → ℝ) :
    restrictedSum (wBox x 1 ×ˢ wBox x 1) lcmPair (pairWeightTotient x F G) 1 = F 0 * G 0 := by
  simp [wBox_one, restrictedSum, pairWeightTotient, lcmPair, Notation.logx]

/-! ## The normalization `B_x` grows -/

/-- **The pre-sieving modulus is smaller than `√{\log x}`**: `W(x)^2 ≤ \log x` for every large `x`.

`Gap212.Sieve.W_le_log` with one more factor of room in the same estimate:
`W(x) ≤ 4^{⌊w₀⌋} ≤ \exp(w₀\log 4)` with `w₀ = \log\log\log x`, so `W(x)^2 ≤ \exp(2w₀\log 4)`, and
`2(\log 4)(\log u) ≤ u` at `u = \log\log x` is `Real.isLittleO_log_id_atTop` with the constant
`1/(2\log 4)`. -/
theorem W_sq_le_log : ∀ᶠ x : ℝ in atTop, ((W x : ℝ)) ^ 2 ≤ Real.log x := by
  have hl4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have key : ∀ᶠ u : ℝ in atTop, 2 * Real.log 4 * Real.log u ≤ u ∧ 1 ≤ u := by
    have hb := Real.isLittleO_log_id_atTop.bound (c := 1 / (2 * Real.log 4)) (by positivity)
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with u hu hu1
    refine ⟨?_, hu1⟩
    simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u),
      abs_of_nonneg (Real.log_nonneg hu1)] at hu
    rwa [← le_div_iff₀' (by positivity), div_eq_inv_mul, ← one_div]
  have hcomp : ∀ᶠ x : ℝ in atTop, 2 * Real.log 4 * Real.log (Real.log (Real.log x))
      ≤ Real.log (Real.log x) ∧ 1 ≤ Real.log (Real.log x) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually key
  filter_upwards [hcomp, eventually_gt_atTop (1 : ℝ)] with x ⟨hkey, hu1⟩ hx1
  set u := Real.log (Real.log x)
  have hW : (W x : ℝ) ≤ (4 : ℝ) ^ Real.log u := calc
    (W x : ℝ) ≤ (4 : ℝ) ^ ⌊Real.log u⌋₊ := mod_cast primorial_le_four_pow _
    _ = (4 : ℝ) ^ (⌊Real.log u⌋₊ : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le (Real.log_nonneg hu1))
  calc ((W x : ℝ)) ^ 2 ≤ ((4 : ℝ) ^ Real.log u) ^ 2 := by gcongr
    _ = Real.exp (2 * Real.log 4 * Real.log u) := by
        rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp u := Real.exp_le_exp.mpr hkey
    _ = Real.log x := Real.exp_log (Real.log_pos hx1)

/-- **The normalization `B_x = (φ(W)/W)\log x` tends to infinity**, in the form: it
eventually exceeds any constant.

`φ(W(x)) ≥ 1` gives `B_x ≥ \log x/W(x)`, and `Gap212.Sieve.W_sq_le_log` gives
`W(x) ≤ √{\log x}`, so `B_x ≥ √{\log x}`. -/
theorem eventually_lt_normalization (K : ℝ) :
    ∀ᶠ x : ℝ in atTop, K < ((W x).totient : ℝ) / (W x : ℝ) * Real.log x := by
  filter_upwards [W_sq_le_log, Real.tendsto_log_atTop.eventually_ge_atTop ((|K| + 1) ^ 2),
    eventually_gt_atTop (1 : ℝ)] with x hWsq hlogge hx1
  have hW0 : 0 < W x := primorial_pos _
  have hW1 : (1 : ℝ) ≤ (W x : ℝ) := mod_cast hW0
  have hφ1 : (1 : ℝ) ≤ ((W x).totient : ℝ) := mod_cast Nat.totient_pos.mpr hW0
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hmain : K * (W x : ℝ) < Real.log x := by
    nlinarith [sq_nonneg ((W x : ℝ) - (|K| + 1)), le_abs_self K, abs_nonneg K]
  refine ((lt_div_iff₀ (by linarith)).mpr hmain).trans_le ?_
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by linarith)]
  nlinarith

/-! ## The two Selberg sums in the shape the identity is stated at -/

/-- The full-box summand is a product of one-coordinate weights. -/
theorem coeffProd_mul_div_eq_prod_pairWeight {k : ℕ} (x : ℝ) (F G : Fin k → ℝ → ℝ)
    (d d' : Fin k → ℕ) :
    coeffProd x F d * coeffProd x G d' / ∏ i, ((d i).lcm (d' i) : ℝ)
      = ∏ i, pairWeight x (F i) (G i) (d i, d' i) := by
  simp only [pairWeight, lcmPair]
  rw [Finset.prod_div_distrib, coeffProd, coeffProd, ← Finset.prod_mul_distrib]

/-- **`Gap212.Sieve.boxPairSum` is the product of the `k` one-coordinate pair sums.** -/
theorem boxPairSum_eq_prod {k : ℕ} (x : ℝ) (B : ℕ) (F G : Fin k → ℝ → ℝ) :
    boxPairSum x B F G = ∏ i, ∑ q ∈ wBox x B ×ˢ wBox x B, pairWeight x (F i) (G i) q := by
  rw [prod_univ_sum (fun _ : Fin k ↦ wBox x B ×ˢ wBox x B)
    fun i q ↦ pairWeight x (F i) (G i) q, boxPairSum,
    ← sum_pair_tuples_eq (ι := Fin k) (wBox x B) (wBox x B)
      fun a ↦ ∏ i, pairWeight x (F i) (G i) (a i)]
  exact Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun d' _ ↦
    coeffProd_mul_div_eq_prod_pairWeight x F G d d'

/-- **`Gap212.Sieve.sievedPairSum` is the pairwise-coprime restriction of the coupled sum.** -/
theorem sievedPairSum_eq_sum_guard {k : ℕ} (x : ℝ) (B : ℕ) (F G : Fin k → ℝ → ℝ) :
    sievedPairSum x B F G
      = ∑ a ∈ Fintype.piFinset fun _ : Fin k ↦ wBox x B ×ˢ wBox x B,
          (if ∀ i i' : Fin k, i ≠ i' → Nat.Coprime (lcmPair (a i)) (lcmPair (a i'))
            then ∏ i, pairWeight x (F i) (G i) (a i) else 0) := by
  rw [sievedPairSum, ← sum_pair_tuples_eq (ι := Fin k) (wBox x B) (wBox x B)
    fun a ↦ if ∀ i i' : Fin k, i ≠ i' → Nat.Coprime (lcmPair (a i)) (lcmPair (a i'))
      then ∏ i, pairWeight x (F i) (G i) (a i) else 0]
  exact Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun d' _ ↦
    if_congr Iff.rfl (coeffProd_mul_div_eq_prod_pairWeight x F G d d') rfl

/-! ## The one-coordinate estimate, and the Selberg reduction -/

/-- **The shared refutation of the truncation-free estimates**: any one-coordinate weight whose
restricted sum at `B = e = 1` is `F(0)G(0)` violates a bound `K/(B_x·e^s)`, because `B_x ⟶ ∞`. -/
private theorem not_decay_of_restrictedSum_one (s : ℝ)
    (w : ℝ → (ℝ → ℝ) → (ℝ → ℝ) → ℕ × ℕ → ℝ)
    (hw : ∀ x F G, restrictedSum (wBox x 1 ×ˢ wBox x 1) lcmPair (w x F G) 1 = F 0 * G 0) :
    ¬ ∀ F G : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F → ContDiff ℝ 1 G →
      HasCompactSupport G → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop, ∀ B e : ℕ, 0 < e →
        |restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (w x F G) e|
          ≤ K / ((((W x).totient : ℝ) / (W x : ℝ) * Real.log x) * (e : ℝ) ^ s) := by
  intro h
  obtain ⟨F, -, hFc, hFd, -, hF0⟩ := exists_contDiff_tsupport_subset
    (E := ℝ) (s := Set.univ) (x := (0 : ℝ)) (n := 1) Filter.univ_mem
  obtain ⟨K, hK, hev⟩ := h F F (mod_cast hFd) hFc (mod_cast hFd) hFc
  obtain ⟨x, hx, hxK⟩ := (hev.and (eventually_lt_normalization K)).exists
  have hb := hx 1 1 one_pos
  norm_num [hw, hF0, le_div_iff₀ (hK.trans_lt hxK)] at hb
  linarith

/-- **The truncation-free one-coordinate estimate — and it is false at every exponent.** For every
pair of `C¹` compactly supported profiles there is a constant `K` such that, for all large `x`,
every truncation `B` and every modulus `e ≥ 1`,

  `|∑_{(d,d') ∈ [1,B]^2, (dd',W)=1, e ∣ [d,d']} μ(d)F(\log_xd)μ(d')G(\log_xd')/[d,d']|
      ≤ K/(B_x·e^s)`,  `B_x = (φ(W)/W)\log x`.

The exponent `s < 1` handles the modulus witness (two large primes whose product leaves the sum a
single pair of terms), and with `s > 1/2` the prime-wise regrouping of
`Gap212.Sieve.PairwiseCoprimeMoebius` still applies. The truncation, however, is quantified with
no lower bound, and `Gap212.Sieve.not_oneCoordLcmDecay` refutes the statement at `B = 1` for every
`s`. `Gap212.Sieve.OneCoordLcmDecayAtLevel` adds the truncation hypothesis. -/
def OneCoordLcmDecay (s : ℝ) : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F → ContDiff ℝ 1 G → HasCompactSupport G →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop, ∀ B e : ℕ, 0 < e →
      |restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeight x F G) e|
        ≤ K / ((((W x).totient : ℝ) / (W x : ℝ) * Real.log x) * (e : ℝ) ^ s)

/-- **`Gap212.Sieve.OneCoordLcmDecay s` is false, for every `s`.**

The witness is the truncation, not the modulus, and it needs no analysis of the pair sum at all.
Take any `C¹` compactly supported `F` with `F(0) = 1` — Mathlib's
`exists_contDiff_tsupport_subset` at `s = univ`, `x = 0` supplies one — and read the asserted bound
at `B = 1`, `e = 1`. The box is `{1}` (`Gap212.Sieve.wBox_one`), so the left side is the single
uncancelled term `F(0)^2 = 1` (`Gap212.Sieve.restrictedSum_wBox_one`), while the right side is
`K/B_x` with `B_x ⟶ ∞` (`Gap212.Sieve.eventually_lt_normalization`). So the bound fails at every
large `x`, not merely at some.

Nothing here is special to `F(0) = 1`: any pair of profiles with `F(0)G(0) ≠ 0` does it, and the
same reading at any `B` below the least prime not dividing `W(x)` gives the same single term. -/
theorem not_oneCoordLcmDecay (s : ℝ) : ¬ OneCoordLcmDecay s :=
  not_decay_of_restrictedSum_one s pairWeight restrictedSum_wBox_one

/-- **The truncated one-coordinate estimate for the reciprocal kernel.** The bound

  `|∑_{(d,d') ∈ [1,B]^2, (dd',W)=1, e ∣ [d,d']} μ(d)F(\log_xd)μ(d')G(\log_xd')/[d,d']|
      ≤ K/(B_x·e^s)`,  `B_x = (φ(W)/W)\log x`,

asked for only at truncations `B ≥ x^β`, with `K` allowed to depend on `β` as well as on the
profiles. Without the truncation hypothesis the statement is false
(`Gap212.Sieve.not_oneCoordLcmDecay`): at `B = 1` the box is a single point and the sum is
`F(0)G(0)`, which no growth of `x` touches. The order `β`-then-`K` matches
`Gap212.Sieve.SelbergSievingError`, which supplies `β` (with `1 ≤ β`) and the truncation `B` with
`x^β ≤ B(x)` before anything else is chosen; the sum depends on `β`, since the profiles are read
at `\log_xd` with `d ≤ B`.

At `s = 1` the statement is false for a second, independent reason — two large primes whose
product leaves the sum a single pair of terms; see the module docstring — and `s > 1/2` is what the
prime-wise regrouping needs.

This form is also false, by `Gap212.Sieve.not_oneCoordLcmDecayAtLevel`: nothing here bounds the
profiles' support by the truncation, so the top block of moduli `r ∈ (B/2,B]`, where the inner
Möbius sum is a single term, survives uncancelled and is `≍φ(W)/W ≫ 1/B_x`. The form with the
profiles vanishing from `β` on is `Gap212.Sieve.OneCoordLcmDecayAtLevelOfSupport`. -/
def OneCoordLcmDecayAtLevel (s : ℝ) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ F G : ℝ → ℝ,
    ContDiff ℝ 1 F → HasCompactSupport F → ContDiff ℝ 1 G → HasCompactSupport G →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop, ∀ B e : ℕ, x ^ β ≤ (B : ℝ) → 0 < e →
      |restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeight x F G) e|
        ≤ K / ((((W x).totient : ℝ) / (W x : ℝ) * Real.log x) * (e : ℝ) ^ s)

/-- **Every divisor of a modulus in the box lies in the box's divisor set.** -/
theorem mem_divisorSet_of_dvd_lcmPair {x : ℝ} {B : ℕ} {q : ℕ × ℕ} (hq : q ∈ wBox x B ×ˢ wBox x B)
    {e : ℕ} (he : e ∣ lcmPair q) :
    e ∈ {e ∈ Icc 1 (B ^ 2) | Nat.Coprime (W x) e} := by
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
  obtain ⟨⟨hu1, hu2⟩, hucop⟩ := mem_wBox.mp h1
  obtain ⟨⟨hv1, hv2⟩, hvcop⟩ := mem_wBox.mp h2
  have hlpos : 0 < lcmPair q := lcmPair_pos hu1 hv1
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos he hlpos,
    (Nat.le_of_dvd hlpos he).trans ?_⟩,
    ((hucop.mul_right hvcop).coprime_dvd_right (Nat.lcm_dvd_mul q.1 q.2)).coprime_dvd_right he⟩
  exact (Nat.le_of_dvd (by positivity) (Nat.lcm_dvd_mul _ _)).trans
    ((Nat.mul_le_mul hu2 hv2).trans_eq (sq B).symm)

/-- **The shared core of the two reductions.** If every coordinate's restricted sums obey the
one-coordinate bound `K/(B_x·e^s)` at the truncations `B ≥ x^β`, then the full-box product minus
its pairwise-coprime restriction, times `B_x` per coordinate, tends to `0`. -/
private theorem tendsto_pow_mul_prod_sub_sum_guard {ι : Type*} [Fintype ι] [DecidableEq ι]
    [DecidablePred fun a : ι → ℕ × ℕ ↦
      ∀ i i' : ι, i ≠ i' → (lcmPair (a i)).Coprime (lcmPair (a i'))]
    {s β : ℝ} (hs : 1 / 2 < s) (hβ : 0 < β) (w : ℝ → ι → ℕ × ℕ → ℝ) (B : ℝ → ℕ)
    (hB : ∀ᶠ x : ℝ in atTop, x ^ β ≤ (B x : ℝ))
    (hdec : ∀ i, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop, ∀ B e : ℕ, x ^ β ≤ (B : ℝ) → 0 < e →
      |restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (w x i) e|
        ≤ K / ((((W x).totient : ℝ) / (W x : ℝ) * Real.log x) * (e : ℝ) ^ s)) :
    Tendsto (fun x : ℝ ↦ (((W x).totient : ℝ) / (W x : ℝ) * Real.log x) ^ Fintype.card ι *
      ((∏ i, ∑ q ∈ wBox x (B x) ×ˢ wBox x (B x), w x i q) -
        ∑ a ∈ Fintype.piFinset fun _ : ι ↦ wBox x (B x) ×ˢ wBox x (B x),
          if ∀ i i' : ι, i ≠ i' → Nat.Coprime (lcmPair (a i)) (lcmPair (a i'))
            then ∏ i, w x i (a i) else 0)) atTop (nhds 0) := by
  refine Metric.tendsto_nhds.mpr fun ε' hε' ↦ ?_
  choose K hK hKev using hdec
  set n := Fintype.card ι
  set KK : ℝ := ∑ i, K i
  have hKK0 : 0 ≤ KK := Finset.sum_nonneg fun i _ ↦ hK i
  have hε : 0 < ε' / (2 * (KK ^ n + 1)) := by positivity
  obtain ⟨z, hz⟩ := exists_threshold_abs_prod_sub_sum_pairwise_coprime_le_rpow ι hs hε
  filter_upwards [eventually_all.mpr hKev, eventually_dvd_W_of_prime_le z,
    eventually_gt_atTop (1 : ℝ), hB] with x hxK hxW hx1 hxB
  set Bx : ℝ := ((W x).totient : ℝ) / (W x : ℝ) * Real.log x
  have hW0 : 0 < W x := primorial_pos _
  have hBx : 0 < Bx := by
    have : (0 : ℝ) < ((W x).totient : ℝ) := mod_cast Nat.totient_pos.mpr hW0
    have := Real.log_pos hx1
    positivity
  have hB1 : 1 ≤ B x := by
    exact_mod_cast ((Real.one_lt_rpow_iff_of_pos (by linarith)).mpr (Or.inl ⟨hx1, hβ⟩)).le.trans hxB
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (by positivity)]
  calc _ ≤ Bx ^ n * ((KK / Bx) ^ n * (ε' / (2 * (KK ^ n + 1)))) := by
        refine mul_le_mul_of_nonneg_left (Eq.trans_le (by congr!) <| hz _ lcmPair (w x)
          {e ∈ Icc 1 (B x ^ 2) | (W x).Coprime e} _ (fun a ha ↦ ?_)
          (fun a ha e he ↦ mem_divisorSet_of_dvd_lcmPair ha he) ?_
          (fun e he ↦ (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1) ?_ (by positivity) ?_)
          (by positivity)
        · obtain ⟨h1, h2⟩ := Finset.mem_product.mp ha
          exact lcmPair_pos (mem_wBox.mp h1).1.1 (mem_wBox.mp h2).1.1
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨le_rfl, Nat.one_le_pow _ _ hB1⟩, Nat.coprime_one_right _⟩
        · exact fun e he P hP hPe ↦ lt_of_not_ge fun hPz ↦ hP.ne_one
            (Nat.eq_one_of_dvd_coprimes (Finset.mem_filter.mp he).2 (hxW P hP hPz) hPe)
        · intro i e he
          have : (0 : ℝ) < (e : ℝ) ^ s := Real.rpow_pos_of_pos (mod_cast he) _
          refine (hxK i (B x) e hxB he).trans ?_
          rw [div_div]
          exact div_le_div_of_nonneg_right
            (Finset.single_le_sum (fun j _ ↦ hK j) (Finset.mem_univ i)) (by positivity)
    _ = KK ^ n * ε' / (2 * (KK ^ n + 1)) := by rw [div_pow]; field_simp
    _ < ε' := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [pow_nonneg hKK0 n]

/-- **The reduction of `Gap212.Sieve.SelbergSievingError` to
`Gap212.Sieve.OneCoordLcmDecayAtLevel`, at every `m`.** The `k`-coordinate pairwise-coprimality
coupling is discharged by `Gap212.Sieve.exists_threshold_abs_prod_sub_sum_pairwise_coprime_le_rpow`.

The hypothesis is false for every `s` (`Gap212.Sieve.not_oneCoordLcmDecayAtLevel`), so this
theorem has no instances; `Gap212.Sieve.SelbergSievingError` is proved by
`Gap212.Sieve.selbergSievingError` through
`Gap212.Sieve.tendsto_boxPairSum_sub_sievedPairSum_of_support`, which assumes instead
`Gap212.Sieve.OneCoordLcmDecayAtLevelOfSupport s`, the bound for profiles vanishing from `β` on,
and concludes at `β ≥ 1`. -/
theorem selbergSievingError_of_oneCoordLcmDecayAtLevel {s : ℝ} (hs : 1 / 2 < s)
    (hdec : OneCoordLcmDecayAtLevel s) (m : ℕ) : SelbergSievingError m := by
  intro p ε₀ hε₀ hε₀' j j' F G hF hFc hG hGc hsupp β hβ1 B hB
  have hβ : 0 < β := by linarith
  refine (tendsto_pow_mul_prod_sub_sum_guard hs hβ (fun x i ↦ pairWeight x (F i) (G i)) B hB
    fun i ↦ hdec β hβ (F i) (G i) (hF i) (hFc i) (hG i) (hGc i)).congr fun x ↦ ?_
  rw [boxPairSum_eq_prod, sievedPairSum_eq_sum_guard, Fintype.card_fin]

/-! ## The totient sum, and the divisor-sum reduction -/

/-- The separated summand is a product of one-coordinate totient weights, up to the modulus's own
`φ(W(x))`. -/
theorem sepSummand_eq_prod_pairWeightTotient {m : ℕ} (x : ℝ) (F G : Fin m → ℝ → ℝ)
    (d d' : Fin m → ℕ) :
    sepSummand x F G (d, d')
      = (((W x).totient : ℝ))⁻¹ * ∏ i, pairWeightTotient x (F i) (G i) (d i, d' i) := by
  simp only [sepSummand, pairWeightTotient, lcmPair, divisorNumerator]
  rw [Finset.prod_div_distrib]
  field_simp

/-- **`Gap212.Sieve.boxDivisorSum` is `φ(W)^{-1}` times the product of the `m` one-coordinate pair
sums.** -/
theorem boxDivisorSum_eq_prod {m : ℕ} (x : ℝ) (B : ℕ) (F G : Fin m → ℝ → ℝ) :
    boxDivisorSum x B F G
      = (((W x).totient : ℝ))⁻¹ *
          ∏ i, ∑ q ∈ wBox x B ×ˢ wBox x B, pairWeightTotient x (F i) (G i) q := by
  rw [prod_univ_sum (fun _ : Fin m ↦ wBox x B ×ˢ wBox x B)
      fun i q ↦ pairWeightTotient x (F i) (G i) q,
    ← sum_pair_tuples_eq (ι := Fin m) (wBox x B) (wBox x B)
      fun a ↦ ∏ i, pairWeightTotient x (F i) (G i) (a i),
    boxDivisorSum, boxPairs, Finset.sum_product]
  simp_rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun d' _ ↦
    sepSummand_eq_prod_pairWeightTotient x F G d d'

/-- **`Gap212.Sieve.sievedDivisorSum` is `φ(W)^{-1}` times the pairwise-coprime restriction.** -/
theorem sievedDivisorSum_eq_sum_guard {m : ℕ} (x : ℝ) (B : ℕ) (F G : Fin m → ℝ → ℝ) :
    sievedDivisorSum x B F G
      = (((W x).totient : ℝ))⁻¹ *
          ∑ a ∈ Fintype.piFinset fun _ : Fin m ↦ wBox x B ×ˢ wBox x B,
            (if ∀ i i' : Fin m, i ≠ i' → Nat.Coprime (lcmPair (a i)) (lcmPair (a i'))
              then ∏ i, pairWeightTotient x (F i) (G i) (a i) else 0) := by
  classical
  rw [← sum_pair_tuples_eq (ι := Fin m) (wBox x B) (wBox x B)
      fun a ↦ if ∀ i i' : Fin m, i ≠ i' → Nat.Coprime (lcmPair (a i)) (lcmPair (a i'))
        then ∏ i, pairWeightTotient x (F i) (G i) (a i) else 0,
    sievedDivisorSum, sievedPairs, Finset.sum_filter, boxPairs, Finset.sum_product]
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  exact Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun d' _ ↦
    if_congr Iff.rfl (sepSummand_eq_prod_pairWeightTotient x F G d d') rfl

/-- **The truncation-free totient-weight estimate**, the analogue of
`Gap212.Sieve.OneCoordLcmDecay` with `φ([d,d'])` for `[d,d']`. It is false at every exponent
(`Gap212.Sieve.not_oneCoordTotientDecay`): `φ(1) = 1`, so the `B = 1` witness reads the same single
term. -/
def OneCoordTotientDecay (s : ℝ) : Prop :=
  ∀ F G : ℝ → ℝ, ContDiff ℝ 1 F → HasCompactSupport F → ContDiff ℝ 1 G → HasCompactSupport G →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop, ∀ B e : ℕ, 0 < e →
      |restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeightTotient x F G) e|
        ≤ K / ((((W x).totient : ℝ) / (W x : ℝ) * Real.log x) * (e : ℝ) ^ s)

/-- **`Gap212.Sieve.OneCoordTotientDecay s` is false, for every `s`.** The proof of
`Gap212.Sieve.not_oneCoordLcmDecay` verbatim: `φ([1,1]) = φ(1) = 1`, so
`Gap212.Sieve.restrictedSum_wBox_one_totient` gives the same uncancelled `F(0)G(0)` at `B = e = 1`
against a bound tending to `0`. -/
theorem not_oneCoordTotientDecay (s : ℝ) : ¬ OneCoordTotientDecay s :=
  not_decay_of_restrictedSum_one s pairWeightTotient restrictedSum_wBox_one_totient

/-- **The truncated one-coordinate estimate for the totient kernel**, the analogue of
`Gap212.Sieve.OneCoordLcmDecayAtLevel` with `φ([d,d'])` for `[d,d']`; the local cost at a prime is
`≍1/(q-2)` instead of `≍1/(q-1)`. The truncation hypothesis `B ≥ x^β` and the exponent
`s ∈ (1/2,1)` are there for the same two reasons.

This form is also false, by `Gap212.Sieve.not_oneCoordTotientDecayAtLevel`: the diagonalisation
`Gap212.Sieve.sum_pairs_div_totient_lcm_eq_sum_moebiusTotient_mul_sq` is a sum of squares with the
weight `(μ*φ)(r)`, which is `∏_{p ∣ r}(p-2)` on a squarefree `r` and of size `φ(r)^2/r` there
(`Gap212.Sieve.totient_sq_le_two_mul_moebiusTotient`), so the top block `r ∈ (B/2,B]` contributes
uncancelled as for the reciprocal kernel. The form with the profiles vanishing from `β` on is
`Gap212.Sieve.OneCoordTotientDecayAtLevelOfSupport`. -/
def OneCoordTotientDecayAtLevel (s : ℝ) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ F G : ℝ → ℝ,
    ContDiff ℝ 1 F → HasCompactSupport F → ContDiff ℝ 1 G → HasCompactSupport G →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop, ∀ B e : ℕ, x ^ β ≤ (B : ℝ) → 0 < e →
      |restrictedSum (wBox x B ×ˢ wBox x B) lcmPair (pairWeightTotient x F G) e|
        ≤ K / ((((W x).totient : ℝ) / (W x : ℝ) * Real.log x) * (e : ℝ) ^ s)

/-- **The reduction of `Gap212.Sieve.TotientSievingError` to
`Gap212.Sieve.OneCoordTotientDecayAtLevel`, at every `m`.** The analogue of
`Gap212.Sieve.selbergSievingError_of_oneCoordLcmDecayAtLevel` with `φ([d,d'])` for `[d,d']`; the
normalisation `Gap212.Sieve.divisorSumNorm` absorbs the modulus's own `φ(W(x))` and leaves `B_x^m`,
one factor per coordinate.

The hypothesis is false for every `s` (`Gap212.Sieve.not_oneCoordTotientDecayAtLevel`), so this
theorem has no instances; `Gap212.Sieve.TotientSievingError` is proved by
`Gap212.Sieve.totientSievingError` through
`Gap212.Sieve.tendsto_boxDivisorSum_sub_sievedDivisorSum_of_support`, which assumes instead
`Gap212.Sieve.OneCoordTotientDecayAtLevelOfSupport s` (a theorem at `s = 3/4`,
`Gap212.Sieve.oneCoordTotientDecayAtLevelOfSupport_three_quarters`) and concludes at `β ≥ 1`. -/
theorem totientSievingError_of_oneCoordTotientDecayAtLevel {s : ℝ} (hs : 1 / 2 < s)
    (hdec : OneCoordTotientDecayAtLevel s) (m : ℕ) : TotientSievingError m := by
  intro p ε₀ hε₀ hε₀' j j' i₀ F G hF hFc hG hGc hsupp β hβ1 B hB
  have hβ : 0 < β := by linarith
  refine (tendsto_pow_mul_prod_sub_sum_guard hs hβ (fun x i ↦ pairWeightTotient x (F i) (G i)) B
    hB fun i ↦ hdec β hβ (F i) (G i) (hF i) (hFc i) (hG i) (hGc i)).congr' ?_
  -- the normalisation absorbs `φ(W(x))` and leaves `B_x^m`
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx1
  have hW : (0 : ℝ) < (W x : ℝ) := mod_cast primorial_pos _
  have hφ : (0 : ℝ) < ((W x).totient : ℝ) := mod_cast Nat.totient_pos.mpr (primorial_pos _)
  have := Real.log_pos hx1
  rw [boxDivisorSum_eq_prod, sievedDivisorSum_eq_sum_guard, divisorSumNorm, Fintype.card_fin,
    mul_pow, div_pow]
  field_simp
  ring

end Gap212.Sieve
