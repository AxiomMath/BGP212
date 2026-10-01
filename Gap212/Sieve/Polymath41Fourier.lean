/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Notation
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Step 1 of Polymath8b Lemma 4.1: the Fourier expansion of the profiles

The proof of Polymath8b Lemma 4.1 opens with this sentence:

> the functions `t ↦ e^t F_j(t)`, `t ↦ e^t G_j(t)` may be extended to smooth compactly supported
> functions on all of `ℝ`, and so we have Fourier expansions `e^t F_j(t) = ∫_ℝ e^{-itξ} f_j(ξ) dξ`
> … for some fixed functions `f_j, g_j : ℝ → ℂ` that are smooth and rapidly decreasing

and then converts that into the form the sieve sum needs:

> `F_j(log_x d_j) = ∫_ℝ f_j(ξ_j) / d_j^{(1+iξ_j)/log x} dξ_j`.

Both displays are theorems here: `Gap212.Sieve.ofReal_eq_integral_profileFourier` and
`Gap212.Sieve.ofReal_logx_eq_integral_profileFourier`.

## Why the profiles are `C^∞` and not merely `C¹`

Mathlib's Fourier inversion theorem `MeasureTheory.Integrable.fourierInv_fourier_eq` carries
`Integrable (𝓕 f)` as a hypothesis, and that hypothesis is *not* available from `C¹` plus compact
support: the transform of a `C¹` compactly supported function decays only like `o(1/|ξ|)`, which
need not be integrable. It **is** available from `C^∞` plus compact support, because a smooth
compactly supported function is a Schwartz function (`HasCompactSupport.toSchwartzMap`) and the
Schwartz space is stable under the Fourier transform. `Gap212.Sieve.integrable_fourier_of_contDiff`
is that deduction, and it is all this step needs: the two `Prop`s
`Gap212.Sieve.Polymath41Recip` and `Gap212.Sieve.Polymath41Totient` are quantified over
`ContDiff ℝ (⊤ : ℕ∞)` profiles, which is exactly the class in which this step runs.

## Normalization

Mathlib's transform is `𝓕 f ξ = ∫ t, e^{-2πitξ} f t dt` and its inverse is
`𝓕⁻ f ξ = ∫ t, e^{2πitξ} f t dt`. The source writes `e^{-itξ}` with no `2π` and inverts with no
`1/2π`. So the source's `f_j` is this file's `Gap212.Sieve.profileFourier F` with `ξ` rescaled by
`2π`; taking `f := 𝓕⁻ (t ↦ e^t F t)` rather than `𝓕` of it puts the sign of the exponent where the
source puts it, so that the displays above read as the source's with `ξ_source = 2πξ`. Nothing
downstream depends on the choice, because every use integrates over all of `ℝ`.

## Relation to step 2

It does not interchange the `d`-sum with the `ξ`-integral. That is step 2 of the proof; its
arithmetic-side hypothesis — the majorant `∑_{d,d'}|μ(d)μ(d')|/([d,d']d^σ(d')^σ) ≤ ζ(1+σ)³` — is
`Gap212.Sieve.tsum_pairMajorant_le` in `Gap212.Sieve.Polymath41Majorant`, and what this file
supplies towards the same step is its integral side: the per-divisor integrability
`Gap212.Sieve.integrable_profileFourier_mul_cpow` and the rapid decay
`Gap212.Sieve.profileFourier_decay`. The interchange itself is
`Gap212.Sieve.tsum_weightPairSum_eq_integral` in `Gap212.Sieve.Polymath41Fubini`.
Nothing here is specific to either kernel: `1/[d,d']` and `1/φ([d,d'])` are untouched, so this file
is shared by `Gap212.Sieve.Polymath41Recip` and `Gap212.Sieve.Polymath41Totient` without conflating
them.

## Main definitions

* `Gap212.Sieve.expProfile`: `t ↦ e^t F t`, complexified — the function the source extends.
* `Gap212.Sieve.profileFourier`: the source's `f_j`, namely `𝓕⁻ (expProfile F)`.

## Main results

* `Gap212.Sieve.integrable_fourier_of_contDiff`: `Integrable (𝓕 h)` for `h` smooth with compact
  support. The hypothesis of Mathlib's inversion theorem that `C¹` does not give.
* `Gap212.Sieve.profileFourier_decay`: the source's "rapidly decreasing", at every polynomial
  order.
* `Gap212.Sieve.ofReal_eq_integral_profileFourier`: the source's Fourier expansion of `e^tF(t)`,
  solved for `F`.
* `Gap212.Sieve.ofReal_logx_eq_integral_profileFourier`: the same at `t = log_x d`, which is the
  display the sieve sum is expanded with.
-/

@[expose] public section

namespace Gap212.Sieve

open MeasureTheory Real
open scoped FourierTransform ContDiff SchwartzMap

/-! ## Smooth compactly supported functions are Schwartz functions -/

/-- **A smooth compactly supported function on `ℝ` is a Schwartz function**, packaged as an
existential so that the Schwartz-space API can be used on a bare function without carrying a
bundled `𝓢(ℝ, ℂ)` through the statements. This is `HasCompactSupport.toSchwartzMap`, whose exponent
`∞` is `((⊤ : ℕ∞) : WithTop ℕ∞)` — the same index the two `Prop`s of `Gap212.Sieve.Polymath41`
use, and **not** `ω`, which would be analyticity and would make them vacuous. -/
theorem exists_schwartzMap_coe_eq {h : ℝ → ℂ} (hs : ContDiff ℝ (⊤ : ℕ∞) h)
    (hc : HasCompactSupport h) : ∃ S : 𝓢(ℝ, ℂ), ⇑S = h :=
  ⟨hc.toSchwartzMap (by exact_mod_cast hs), rfl⟩

/-- **The hypothesis of Fourier inversion that smoothness supplies.** For `h` smooth with compact
support, `𝓕 h` is integrable. At `C¹` this fails: the
transform is only `o(1/|ξ|)`, while `MeasureTheory.Integrable.fourierInv_fourier_eq` and
`Continuous.fourier_fourierInv_eq` both ask for `Integrable (𝓕 h)`. -/
theorem integrable_fourier_of_contDiff {h : ℝ → ℂ} (hs : ContDiff ℝ (⊤ : ℕ∞) h)
    (hc : HasCompactSupport h) : Integrable (𝓕 h) := by
  obtain ⟨S, hS⟩ := exists_schwartzMap_coe_eq hs hc
  have := (𝓕 S).integrable (μ := volume)
  rwa [SchwartzMap.fourier_coe, hS] at this

/-- **The inverse transform of a smooth compactly supported function is integrable**, by
`Gap212.Sieve.integrable_fourier_of_contDiff` and `Real.fourierInv_eq_fourier_neg`. -/
theorem integrable_fourierInv_of_contDiff {h : ℝ → ℂ} (hs : ContDiff ℝ (⊤ : ℕ∞) h)
    (hc : HasCompactSupport h) : Integrable (𝓕⁻ h) := by
  have e : 𝓕⁻ h = fun w ↦ 𝓕 h (-w) := funext (Real.fourierInv_eq_fourier_neg h)
  rw [e]
  exact (integrable_fourier_of_contDiff hs hc).comp_neg

/-- **The inverse transform of a smooth compactly supported function is smooth** — the first half
of the source's "smooth and rapidly decreasing". -/
theorem contDiff_fourierInv_of_contDiff {h : ℝ → ℂ} (hs : ContDiff ℝ (⊤ : ℕ∞) h)
    (hc : HasCompactSupport h) : ContDiff ℝ (⊤ : ℕ∞) (𝓕⁻ h) := by
  obtain ⟨S, hS⟩ := exists_schwartzMap_coe_eq hs hc
  have h1 : ContDiff ℝ ∞ ((𝓕⁻ S : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := (𝓕⁻ S : 𝓢(ℝ, ℂ)).smooth'
  rw [SchwartzMap.fourierInv_coe, hS] at h1
  exact_mod_cast h1

/-- **The inverse transform of a smooth compactly supported function is rapidly decreasing** — the
second half of the source's "smooth and rapidly decreasing", `f_j(ξ) = O((1+|ξ|)^{-A})` for every
fixed `A`, with the constant independent of `ξ`. Here `A` is a natural number, which is all the
source's use of it needs; the bound is the Schwartz seminorm estimate
`SchwartzMap.one_add_le_sup_seminorm_apply`. -/ theorem fourierInv_decay {h : ℝ → ℂ} (hs : ContDiff
ℝ (⊤ : ℕ∞) h) (hc : HasCompactSupport h)
    (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, (1 + |ξ|) ^ k * ‖𝓕⁻ h ξ‖ ≤ C := by
  obtain ⟨S, hS⟩ := exists_schwartzMap_coe_eq hs hc
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup
    (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) (𝓕⁻ S), by positivity, fun ξ ↦ ?_⟩
  have key := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl (𝓕⁻ S) ξ
  simpa [SchwartzMap.fourierInv_coe, hS, Real.norm_eq_abs] using key

/-- **Fourier inversion for a smooth compactly supported function on `ℝ`.** The source's Fourier
expansion read as a definition: `h` is recovered from `𝓕⁻ h` by `𝓕`. Both integrability hypotheses
of `Continuous.fourier_fourierInv_eq` are discharged from smoothness and compact support. -/ theorem
fourier_fourierInv_eq_of_contDiff {h : ℝ → ℂ} (hs : ContDiff ℝ (⊤ : ℕ∞) h)
    (hc : HasCompactSupport h) : 𝓕 (𝓕⁻ h) = h :=
  hs.continuous.fourier_fourierInv_eq
    (hs.continuous.integrable_of_hasCompactSupport hc) (integrable_fourier_of_contDiff hs hc)

/-! ## `t ↦ e^t F t` and its transform -/

/-- **The function the source extends to all of `ℝ`**: `t ↦ e^t F(t)`, complexified. The source's
profiles are `[0,+∞) → ℝ` and the extension is the content of its first sentence; here the profiles
are already `ℝ → ℝ` with compact support on all of `ℝ`, which is the class the source's own proof
works in, so no extension is needed and this is literally `e^t F t`. -/
noncomputable def expProfile (F : ℝ → ℝ) : ℝ → ℂ := fun t ↦ ((Real.exp t * F t : ℝ) : ℂ)

/-- **The source's `f_j`**: the inverse Fourier transform of `t ↦ e^t F(t)`. With Mathlib's
normalization `𝓕⁻ g ξ = ∫ t, e^{2πitξ} g t dt`, inverting with `𝓕⁻` rather than `𝓕` is what makes
`Gap212.Sieve.ofReal_eq_integral_profileFourier` carry the source's sign, `e^{-itξ}`; the source's
variable is `2πξ`. -/
noncomputable def profileFourier (F : ℝ → ℝ) : ℝ → ℂ := 𝓕⁻ (expProfile F)

/-- `Gap212.Sieve.profileFourier` unfolded, so that Mathlib's Fourier lemmas — which are stated at
`𝓕⁻` — can be rewritten into statements about it. -/
theorem profileFourier_def (F : ℝ → ℝ) : profileFourier F = 𝓕⁻ (expProfile F) := rfl

/-- `e^t F t` is smooth when `F` is. -/
theorem contDiff_expProfile {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (expProfile F) :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.mul hF)

/-- `e^t F t` has compact support when `F` does: multiplying by `e^t` and coercing to `ℂ` cannot
enlarge the support. -/
theorem hasCompactSupport_expProfile {F : ℝ → ℝ} (hFc : HasCompactSupport F) :
    HasCompactSupport (expProfile F) :=
  (hFc.mul_left (f := Real.exp)).comp_left (g := Complex.ofReal) Complex.ofReal_zero

/-- `Gap212.Sieve.profileFourier F` is integrable. -/
theorem integrable_profileFourier {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) : Integrable (profileFourier F) :=
  integrable_fourierInv_of_contDiff (contDiff_expProfile hF) (hasCompactSupport_expProfile hFc)

/-- `Gap212.Sieve.profileFourier F` is smooth. -/
theorem contDiff_profileFourier {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) : ContDiff ℝ (⊤ : ℕ∞) (profileFourier F) :=
  contDiff_fourierInv_of_contDiff (contDiff_expProfile hF) (hasCompactSupport_expProfile hFc)

/-- **`Gap212.Sieve.profileFourier F` is rapidly decreasing**: for every `k` there is a `C` with
`(1+|ξ|)^k‖f(ξ)‖ ≤ C` for all `ξ`. This is the source's "rapidly decreasing", and it is what makes
the truncation `|ξ| ≤ √(log x)` and the Fubini step of step 2 legitimate. -/
theorem profileFourier_decay {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, (1 + |ξ|) ^ k * ‖profileFourier F ξ‖ ≤ C :=
  fourierInv_decay (contDiff_expProfile hF) (hasCompactSupport_expProfile hFc) k

/-! ## The two displays of the source's first step -/

/-- **A positive natural number's complex power is an exponential of its real logarithm**:
`d^w = e^{w·log d}`. This is what turns the source's `e^{-t(1+iξ)}` at `t = log_x d` into its
`d^{-(1+iξ)/log x}`. -/
theorem natCast_cpow_eq_exp {d : ℕ} (hd : 1 ≤ d) (w : ℂ) :
    (d : ℂ) ^ w = Complex.exp ((Real.log d : ℂ) * w) := by
  have hdne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [Complex.cpow_def_of_ne_zero hdne]
  congr 2
  rw [← Complex.ofReal_natCast]
  exact (Complex.ofReal_log (Nat.cast_nonneg d)).symm

/-- **The source's Fourier expansion, solved for `F`.** For `F` smooth with compact support,

  `F(t) = ∫_ℝ f(ξ)·e^{-t(1+2πiξ)} dξ`,

with `f = Gap212.Sieve.profileFourier F`. This is the source's `e^tF(t) = ∫ e^{-itξ}f(ξ)dξ`
divided by `e^t`, at `ξ_source = 2πξ`. -/
theorem ofReal_eq_integral_profileFourier {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (t : ℝ) :
    (F t : ℂ) = ∫ ξ : ℝ, profileFourier F ξ *
      Complex.exp (-((t : ℂ) * (1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ)))) := by
  have key : 𝓕 (𝓕⁻ (expProfile F)) t = expProfile F t :=
    congrFun (fourier_fourierInv_eq_of_contDiff (contDiff_expProfile hF)
      (hasCompactSupport_expProfile hFc)) t
  rw [Real.fourier_real_eq_integral_exp_smul, ← profileFourier_def] at key
  have hexp : ∀ ξ : ℝ, Complex.exp ((((-2 : ℝ) * π * ξ * t : ℝ) : ℂ) * Complex.I) •
      profileFourier F ξ
      = Complex.exp (t : ℂ) * (profileFourier F ξ *
        Complex.exp (-((t : ℂ) * (1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ))))) := by
    intro ξ
    have e : Complex.exp (t : ℂ) *
        Complex.exp (-((t : ℂ) * (1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ))))
        = Complex.exp ((((-2 : ℝ) * π * ξ * t : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [smul_eq_mul, ← e]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexp),
    MeasureTheory.integral_const_mul] at key
  have hne : Complex.exp (t : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have hval : expProfile F t = Complex.exp (t : ℂ) * (F t : ℂ) := by
    simp [expProfile, Complex.ofReal_exp]
  rw [hval] at key
  exact (mul_left_cancel₀ hne key).symm

/-- **The display the sieve sum is expanded with**: at `t = log_x d` with `1 < x` and
`1 ≤ d`,

  `F(log_x d) = ∫_ℝ f(ξ)·d^{-(1+2πiξ)/log x} dξ`.

This is `Gap212.Sieve.ofReal_eq_integral_profileFourier` with `e^{-t(1+2πiξ)}` rewritten as a
complex power of `d`, using `log_x d = log d / log x`. -/
theorem ofReal_logx_eq_integral_profileFourier {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) {x : ℝ} (hx : 1 < x) {d : ℕ} (hd : 1 ≤ d) :
    (F (Notation.logx x d) : ℂ) = ∫ ξ : ℝ, profileFourier F ξ *
      (d : ℂ) ^ (-(1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ)) / (Real.log x : ℂ)) := by
  have hlx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  rw [ofReal_eq_integral_profileFourier hF hFc (Notation.logx x d)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ ?_)
  dsimp only
  rw [natCast_cpow_eq_exp hd]
  congr 1
  rw [Notation.logx]
  push_cast
  field_simp

/-! ## The integral side of step 2 -/

/-- **The modulus of the source's kernel factor.** `‖d^{-(1+2πiξ)/log x}‖ = d^{-1/log x}`,
independent of `ξ` — the reason the majorant of step 2 has `d^{1/log x}` in its denominator and
no `ξ` at all. -/
theorem norm_natCast_cpow_profileExponent {d : ℕ} (hd : 1 ≤ d) {x : ℝ} (hx : 1 < x) (ξ : ℝ) :
    ‖(d : ℂ) ^ (-(1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ)) / (Real.log x : ℂ))‖
      = (d : ℝ) ^ (-(1 / Real.log x)) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  congr 1
  have hlx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re]
  simp

/-- **The integrand of the expansion is integrable, divisor by divisor.** The factor
`d^{-(1+2πiξ)/log x}` has modulus `d^{-1/log x} ≤ 1` for `d ≥ 1` and `x > 1`
(`Gap212.Sieve.norm_natCast_cpow_profileExponent`), so it multiplies the integrable
`Gap212.Sieve.profileFourier F` into an integrable function. This is the per-term half of what
Fubini needs at step 2; the other half — summability of the `d`-sum of the moduli, i.e. the
`ζ(1+σ)³` majorant — is `Gap212.Sieve.summable_pairMajorant`. -/
theorem integrable_profileFourier_mul_cpow {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) {x : ℝ} (hx : 1 < x) {d : ℕ} (hd : 1 ≤ d) :
    Integrable (fun ξ : ℝ ↦ profileFourier F ξ *
      (d : ℂ) ^ (-(1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ)) / (Real.log x : ℂ))) := by
  have hcont : Continuous fun ξ : ℝ ↦
      (d : ℂ) ^ (-(1 + 2 * (π : ℂ) * Complex.I * (ξ : ℂ)) / (Real.log x : ℂ)) := by
    refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
    exact Nat.cast_ne_zero.2 (by omega)
  refine (integrable_profileFourier hF hFc).mul_bdd (c := 1) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ ↦ ?_)
  rw [norm_natCast_cpow_profileExponent hd hx]
  refine Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) ?_
  have : 0 < Real.log x := Real.log_pos hx
  simp only [neg_nonpos]
  positivity

end Gap212.Sieve
