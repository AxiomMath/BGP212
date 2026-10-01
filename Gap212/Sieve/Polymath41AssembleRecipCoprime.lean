/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Polymath41AssembleEuler

/-!
# The sieve's coprimality condition, put back into the Euler product

`Gap212.Sieve.Polymath41AssembleEuler` factorises the *unrestricted* kernel of
`Gap212.Sieve.Polymath41Fubini` over **all** primes. The source's kernel carries the condition
"`[d,d'], W, N` coprime", and so do the two `Prop`s of `Gap212.Sieve.Polymath41`: they sum over
`d, d'` coprime to `W(x)`. This file restores the condition.

## The condition is a condition on `n = [d,d']`

That is the whole reason no re-derivation is needed. `Nat.Coprime W [d,d']` holds exactly when `W`
is coprime to both `d` and `d'` (`Gap212.Sieve.coprime_lcm_iff`), so restricting the *pair* sum is
the same as restricting the *Dirichlet series*: the fibres of `(d,d') ↦ [d,d']` are kept whole or
discarded whole (`Gap212.Sieve.sum_lcmFibre_pairKernelTerm_coprimeWeight`). Hence:

* the restricted weight's majorant is dominated by the unrestricted one, so step 2's summability
  transfers with no new estimate (`Gap212.Sieve.summable_weightMajorant_coprimeWeight`);
* the restricted coefficient is the unrestricted one cut down by `Nat.Coprime W n`, and *that*
  operation preserves multiplicativity for any arithmetic function
  (`Gap212.Sieve.isMultiplicative_restrictCoprime`);
* the local factor at `p ∣ W` becomes `1`, because every `p^e` with `e ≥ 1` is discarded and only
  `e = 0` survives (`Gap212.Sieve.tsum_restrictCoprime_prime_pow`). This turns `∏_p` into the
  source's `∏_{p ∤ W}`.

## Generic where the mathematics is generic, separate where it is not

The restriction is a generic operation — on weights and on arithmetic functions — and is proved
generically here, exactly as the interchange of `Gap212.Sieve.Polymath41Fubini` is. Only the
*last* step of this file is specialised: identifying a restricted fibre sum with the **named**
coefficient `Gap212.Sieve.kernelCoeff`, which divides the fibre by `n`. The totient kernel
divides by `φ(n)` and draws its summability from a different majorant, which the reciprocal one
does not dominate — so its instantiation is a separate derivation, in
`Gap212.Sieve.Polymath41AssembleTotientCoprime` and `Gap212.Sieve.Polymath41AssembleTotientSum`,
which consume `Gap212.Sieve.coprimeWeight`, `Gap212.Sieve.restrictCoprime` and the four generic
theorems below unchanged. Nothing about this file's generic layer mentions a denominator.

## Main definitions

* `Gap212.Sieve.coprimeWeight`: a weight restricted to pairs whose least common multiple is coprime
  to the modulus.
* `Gap212.Sieve.restrictCoprime`: an arithmetic function restricted to arguments coprime to the
  modulus.
* `Gap212.Sieve.coprimeRecipKernel`: the source's `K` *with* its coprimality condition, which is
  what `Gap212.Sieve.Polymath41Recip` actually contains.

## Main results

* `Gap212.Sieve.coprime_lcm_iff`: the condition on the pair is a condition on `[d,d']`.
* `Gap212.Sieve.isMultiplicative_restrictCoprime`: restriction preserves multiplicativity.
* `Gap212.Sieve.tsum_restrictCoprime_prime_pow`: the local factor at `p ∣ W` is `1`.
* `Gap212.Sieve.tprod_localFactorRecip_eq_coprimeRecipKernel`: **the source's `∏_{p ∤ W} K_p`**
  for the reciprocal kernel at `N = 1`.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset
open scoped ArithmeticFunction.Moebius

/-! ## The coprimality condition is a condition on the least common multiple -/

/-- **`W` is coprime to `[m,n]` exactly when it is coprime to `m` and to `n`.** This is why the
sieve's coprimality condition survives the regrouping of
`Gap212.Sieve.Polymath41AssembleDirichlet` untouched: it is a condition on the fibre's
*label*, so each fibre is kept whole or discarded whole. -/
theorem coprime_lcm_iff (W m n : ℕ) :
    Nat.Coprime W (Nat.lcm m n) ↔ Nat.Coprime W m ∧ Nat.Coprime W n := by
  refine ⟨fun h ↦ ⟨h.coprime_dvd_right (Nat.dvd_lcm_left m n),
    h.coprime_dvd_right (Nat.dvd_lcm_right m n)⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  exact (h₁.mul_right h₂).coprime_dvd_right (Nat.lcm_dvd_mul m n)

/-! ## Restricting a weight -/

/-- **A weight restricted to the pairs the sieve sums over**: `c(d,d')` when `[d,d']` is coprime to
`W`, and `0` otherwise. By `Gap212.Sieve.coprime_lcm_iff` this is the source's "`[d,d'], W`
coprime" (at `N = 1`), and it is the condition the pair sums of
`Gap212.Sieve.pairSumRecip` and `Gap212.Sieve.pairSumTotient` carry. -/
noncomputable def coprimeWeight (W : ℕ) (c : ℕ × ℕ → ℂ) (p : ℕ × ℕ) : ℂ :=
  if Nat.Coprime W (Nat.lcm p.1 p.2) then c p else 0

/-- The restriction of a weight vanishing on the degenerate pairs still vanishes there. -/
theorem coprimeWeight_eq_zero {c : ℕ × ℕ → ℂ} (hc : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → c p = 0)
    (W : ℕ) : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → coprimeWeight W c p = 0 :=
  fun p hp ↦ by simp [coprimeWeight, hc p hp]

/-- **The restricted majorant is dominated by the unrestricted one**, term by term: the restriction
either keeps a term or replaces it by `0`. So step 2 licenses the restricted interchange with no
new estimate. -/
theorem weightMajorant_coprimeWeight_le (W : ℕ) (c : ℕ × ℕ → ℂ) (σ : ℝ) (p : ℕ × ℕ) :
    weightMajorant (coprimeWeight W c) σ p ≤ weightMajorant c σ p := by
  have hnorm : ‖coprimeWeight W c p‖ ≤ ‖c p‖ := by
    rw [coprimeWeight]
    split <;> simp
  rw [weightMajorant, weightMajorant]
  gcongr

/-- Step 2's summability, transferred to the restricted weight. -/
theorem summable_weightMajorant_coprimeWeight (W : ℕ) {c : ℕ × ℕ → ℂ} {σ : ℝ}
    (hsum : Summable (weightMajorant c σ)) : Summable (weightMajorant (coprimeWeight W c) σ) :=
  Summable.of_nonneg_of_le (fun p ↦ weightMajorant_nonneg _ σ p)
    (fun p ↦ weightMajorant_coprimeWeight_le W c σ p) hsum

/-- **The restriction acts on whole fibres.** The fibre over `n` is kept if `n` is coprime to `W`
and discarded otherwise, because every pair in it has `[d,d'] = n`. No case on `n = 0` is needed:
`Gap212.Sieve.lcmFibre 0` is empty, so both sides are `0` there. -/
theorem sum_lcmFibre_pairKernelTerm_coprimeWeight (W : ℕ) (c : ℕ × ℕ → ℂ) (s s' : ℂ) (n : ℕ) :
    ∑ q ∈ lcmFibre n, pairKernelTerm (coprimeWeight W c) s s' q
      = if Nat.Coprime W n then ∑ q ∈ lcmFibre n, pairKernelTerm c s s' q else 0 := by
  split_ifs with hc
  · refine Finset.sum_congr rfl fun q hq ↦ ?_
    rw [pairKernelTerm, pairKernelTerm, coprimeWeight, if_pos ((mem_lcmFibre.1 hq).2 ▸ hc)]
  · refine Finset.sum_eq_zero fun q hq ↦ ?_
    rw [pairKernelTerm, coprimeWeight, if_neg ((mem_lcmFibre.1 hq).2 ▸ hc), zero_mul, zero_mul]

/-! ## Restricting an arithmetic function -/

/-- **An arithmetic function restricted to arguments coprime to `W`.** At `n = 0` the value is `0`
either way, so this really is an `ArithmeticFunction`. -/
def restrictCoprime {R : Type*} [Zero R] (W : ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨fun n ↦ if Nat.Coprime W n then f n else 0, by
    split
    · exact f.map_zero
    · rfl⟩

/-- `restrictCoprime W f n` is `f n` if `Nat.Coprime W n`, and `0` otherwise. -/
@[simp] theorem restrictCoprime_apply {R : Type*} [Zero R] (W : ℕ) (f : ArithmeticFunction R)
    (n : ℕ) : restrictCoprime W f n = if Nat.Coprime W n then f n else 0 := rfl

/-- **Restriction preserves multiplicativity.** `Nat.Coprime W ·` is itself multiplicative in the
sense that matters — `Nat.Coprime W (mn)` iff `Nat.Coprime W m` and `Nat.Coprime W n`
(`Nat.coprime_mul_iff_right`), with no coprimality of `m, n` needed — so the four cases of the
product all agree. Stated for a general `ArithmeticFunction` over a `CommMonoidWithZero`; the sieve
uses it at `R = ℂ`. -/
theorem isMultiplicative_restrictCoprime {R : Type*} [CommMonoidWithZero R] (W : ℕ)
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) :
    (restrictCoprime W f).IsMultiplicative := by
  refine ⟨by simp [hf.1], fun {m n} hmn ↦ ?_⟩
  simp only [restrictCoprime_apply, Nat.coprime_mul_iff_right]
  split_ifs <;> simp_all [hf.2 hmn]

/-- **The local factor of a restricted function at a prime dividing the modulus is `1`.** Only
`e = 0` survives the restriction — `Nat.Coprime W (p^e)` fails for every `e ≥ 1` when `p ∣ W` — and
`f 1 = 1`. At `p ∤ W` nothing is discarded and the local sum is unchanged. Together these turn a
product over all primes into the source's `∏_{p ∤ W}`. -/
theorem tsum_restrictCoprime_prime_pow (W : ℕ) {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) {p : ℕ} (hp : p.Prime) :
    ∑' e : ℕ, restrictCoprime W f (p ^ e) = if p ∣ W then 1 else ∑' e : ℕ, f (p ^ e) := by
  have hcop : ∀ e : ℕ, 1 ≤ e → (Nat.Coprime W (p ^ e) ↔ ¬ p ∣ W) := by
    intro e he
    rw [Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd
  split_ifs with hdvd
  · refine (tsum_eq_single 0 fun e he ↦ ?_).trans (by simp [hf.1])
    rw [restrictCoprime_apply, if_neg (fun h ↦ (hcop e (by omega)).1 h hdvd)]
  · refine tsum_congr fun e ↦ ?_
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp
    · rw [restrictCoprime_apply, if_pos ((hcop e he).2 hdvd)]

/-! ## The reciprocal kernel with the sieve's coprimality condition -/

/-- **The source's kernel `K` at `N = 1`, with its coprimality condition**:
`K_W = ∑_{d,d' : ([d,d'],W)=1} μ(d)μ(d')/([d,d'] d^s (d')^{s'})`. This — not
`Gap212.Sieve.recipKernel` — is the kernel of the interchange applied to
`Gap212.Sieve.pairSumRecip`. -/
noncomputable def coprimeRecipKernel (W : ℕ) (s s' : ℂ) : ℂ :=
  pairKernel (coprimeWeight W recipPairWeight) s s'

/-- **`K_W` is the Dirichlet series of `Gap212.Sieve.kernelCoeff` restricted to `n` coprime to
`W`.** The regrouping of `Gap212.Sieve.Polymath41AssembleDirichlet` with the restriction
riding along on the fibre labels. -/
theorem coprimeRecipKernel_eq_tsum {W : ℕ} {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ} (hs : s.re = σ)
    (hs' : s'.re = σ) :
    coprimeRecipKernel W s s' = ∑' n : ℕ, restrictCoprime W (kernelArith s s') n := by
  rw [coprimeRecipKernel, pairKernel_eq_tsum_sum_lcmFibre
    (coprimeWeight_eq_zero recipPairWeight_eq_zero W)
    (summable_weightMajorant_coprimeWeight W (summable_weightMajorant_recipPairWeight hσ)) hs hs']
  refine tsum_congr fun n ↦ ?_
  rw [sum_lcmFibre_pairKernelTerm_coprimeWeight, sum_lcmFibre_pairKernelTerm_recip,
    restrictCoprime_apply, kernelArith_apply]

/-- `∑_n ‖a(n)·1_{(n,W)=1}‖ < ∞`, dominated by the unrestricted
`Gap212.Sieve.summable_norm_kernelCoeff`. -/
theorem summable_norm_restrictCoprime_kernelArith (W : ℕ) {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ}
    (hs : s.re = σ) (hs' : s'.re = σ) :
    Summable (‖restrictCoprime W (kernelArith s s') ·‖) := by
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (summable_norm_kernelCoeff hσ hs hs')
  rw [restrictCoprime_apply]
  split <;> simp [kernelArith_apply]

/-- **The source's Euler product `K_W = ∏_{p ∤ W} K_p`** (at `N = 1`), as a product
over all primes whose factors at `p ∣ W` are `1`:

  `∏_p (if p ∣ W then 1 else Gap212.Sieve.localFactorRecip p (p^{-s}) (p^{-s'})) = K_W(s,s')`.

Every ingredient is derived: multiplicativity from
`Gap212.Sieve.isMultiplicative_restrictCoprime` on `Gap212.Sieve.isMultiplicative_kernelArith`, the
local factor from `Gap212.Sieve.tsum_restrictCoprime_prime_pow` and
`Gap212.Sieve.tsum_kernelArith_prime_pow`, and the summability from step 2. -/
theorem tprod_localFactorRecip_eq_coprimeRecipKernel (W : ℕ) {σ : ℝ} (hσ : 0 < σ) {s s' : ℂ}
    (hs : s.re = σ) (hs' : s'.re = σ) :
    ∏' p : Nat.Primes, (if (p : ℕ) ∣ W then 1 else
        localFactorRecip ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)) (((p : ℕ) : ℂ) ^ (-s')))
      = coprimeRecipKernel W s s' := by
  have hmul := isMultiplicative_restrictCoprime W (isMultiplicative_kernelArith s s')
  rw [coprimeRecipKernel_eq_tsum hσ hs hs',
    ← hmul.eulerProduct_tprod (summable_norm_restrictCoprime_kernelArith W hσ hs hs')]
  refine tprod_congr fun p ↦ ?_
  rw [tsum_restrictCoprime_prime_pow W (isMultiplicative_kernelArith s s') p.2,
    tsum_kernelArith_prime_pow p.2]

end Gap212.Sieve
