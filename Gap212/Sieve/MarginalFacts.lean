/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.EndgameDefs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Prod
public meta import Gap212.Attr

/-!
# The restricted marginal form, and the `|F|` step

The certificate's `J` is, at a one-band datum, a *restricted square of a marginal*: the last
coordinate is integrated out, the result squared, and the square integrated over a bounded piece of
the remaining orthant. This file proves that replacing `F` by `|F|` leaves `I` alone and cannot
decrease `J`, so the functions the sieve is run with may be taken non-negative.

## Why the step needs analysis at all

Pointwise `|∫ F(u,t) dt| ≤ ∫ |F(u,t)| dt` is free. Turning that into an inequality between the
*outer* integrals is not: Bochner integration assigns `0` to a non-integrable integrand, so
monotonicity of the outer integral needs the majorant to be integrable.

Integrability comes from the support. A function vanishing off `T_k(p)` vanishes off the unit cube,
so each of its `t`-fibres lives in an interval of length `1`, and Cauchy–Schwarz on that fibre
bounds the squared marginal by the fibre integral of the square — which is integrable in `u` by
Fubini, `F` being square-integrable. `Gap212.GPY.sq_setIntegral_abs_le` is the fibre
Cauchy–Schwarz and `Gap212.GPY.measurePreserving_snoc` is the Fubini splitting.

## The `Fin.snoc` splitting

`marginalForm` singles out the last coordinate through `Fin.snoc`, so every Fubini step needs
Lebesgue measure on `ℝ^{m+1}` identified with the product of Lebesgue measure on `ℝ` (the
singled-out coordinate) and on `ℝ^m`. Mathlib's `MeasureTheory.volume_preserving_piFinSuccAbove`
provides this at `Fin.insertNth`, and `Gap212.GPY.snoc_eq_insertNth` is the — purely
combinatorial — identification of `Fin.insertNth (Fin.last m)` with `Fin.snoc`.

## Main results

* `Gap212.GPY.sq_setIntegral_abs_le`: Cauchy–Schwarz on a set of finite measure.
* `Gap212.GPY.measurePreserving_snoc`, `Gap212.GPY.integrable_comp_snoc`: the Fubini splitting.
* `Gap212.GPY.abs_sqrt_sub_sqrt_le`: the reverse triangle inequality for `E ↦ (∫ E²)^{1/2}`,
  proved elementarily rather than through the `Lp` space.
* `Gap212.GPY.marginalForm_le`: `J̃_c(E) ≤ σ ‖E‖₂²` — the marginal operator's squared norm is at
  most the fibre length.
* `Gap212.GPY.abs_sqrt_marginalForm_sub_le`: the marginal form is Lipschitz in `L²`.
* `Gap212.GPY.marginalForm_nonneg`: the marginal form is non-negative, being an integral of a
  square.
* `Gap212.GPY.hasVariationalGap_abs`: the gap survives replacement by the absolute value.
-/

@[expose] public section

namespace Gap212.GPY

open MeasureTheory Set

/-! ### Cauchy–Schwarz on a fibre -/

/-- Hölder's inequality at the conjugate pair `(2,2)`, for the absolute values, in square-root
form. -/
private theorem integral_abs_mul_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, |f x| * |g x| ∂μ ≤ √(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ) := by
  have h2e : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (by norm_num [Real.holderConjugate_iff])
    (.of_forall fun _ ↦ abs_nonneg (f _)) (.of_forall fun _ ↦ abs_nonneg (g _))
    (h2e ▸ hf.abs) (h2e ▸ hg.abs)
  simp only [Real.rpow_two, sq_abs] at h
  rwa [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h

/-- **Cauchy–Schwarz on a set of finite measure**: the square of the integral of `|f|` over `A` is
at most `volume A` times the integral of `f²`.

Hölder's inequality at the conjugate pair `(2,2)` against the constant `1`. -/
theorem sq_setIntegral_abs_le {A : Set ℝ} (hA : volume A ≠ ⊤) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict A)) :
    (∫ t in A, |f t|) ^ 2 ≤ volume.real A * ∫ t in A, f t ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict A) :=
    ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩
  have h := integral_abs_mul_abs_le hf (memLp_const (μ := volume.restrict A) (1 : ℝ))
  simp only [abs_one, mul_one, one_pow, integral_const, smul_eq_mul,
    measureReal_restrict_apply_univ] at h
  calc (∫ t in A, |f t|) ^ 2 ≤ (√(∫ t in A, f t ^ 2) * √(volume.real A)) ^ 2 :=
        pow_le_pow_left₀ (integral_nonneg fun _ ↦ abs_nonneg _) h 2
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
        Real.sq_sqrt measureReal_nonneg, mul_comm]

/-! ### Two reductions of a half-line integral -/

/-- A function vanishing on the negatives has the same integral over `(0,∞)` as over `ℝ`. The point
`0` itself is not constrained: it is Lebesgue-null. -/
theorem setIntegral_Ioi_eq_integral {f : ℝ → ℝ} (hf : ∀ t : ℝ, t < 0 → f t = 0) :
    (∫ t in Set.Ioi (0 : ℝ), f t) = ∫ t, f t := by
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.univ \ Set.Ioi (0 : ℝ) → f x = 0 := by
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with x hx hmem
    exact hf x ((not_lt.mp hmem.2).lt_of_ne hx)
  rw [← setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_univ
    (Set.subset_univ _) hae]
  exact setIntegral_univ

/-- A function vanishing above `b` has the same integral over `(0,b]` as over `(0,∞)`. -/
theorem setIntegral_Ioc_eq_Ioi {f : ℝ → ℝ} {b : ℝ} (hf : ∀ t : ℝ, b < t → f t = 0) :
    (∫ t in Set.Ioc (0 : ℝ) b, f t) = ∫ t in Set.Ioi (0 : ℝ), f t :=
  (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioc_subset_Ioi_self
    fun x hx ↦ hf x (not_le.mp fun h ↦ hx.2 ⟨hx.1, h⟩)).symm

/-! ### The `Fin.snoc` splitting of Lebesgue measure -/

/-- Adjoining a coordinate at the end is inserting it at `Fin.last`. -/
theorem snoc_eq_insertNth (m : ℕ) (x : ℝ) (u : Fin m → ℝ) :
    (Fin.insertNth (Fin.last m) x u : Fin (m + 1) → ℝ) = Fin.snoc u x := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc, show j.castSucc = (Fin.last m).succAbove j by simp,
      Fin.insertNth_apply_succAbove]
  · rw [Fin.snoc_last, Fin.insertNth_apply_same]

/-- `Fin.snoc` as a function on the product, spelled through Mathlib's measurable equivalence. -/
theorem snocFun_eq (m : ℕ) :
    (fun q : ℝ × (Fin m → ℝ) ↦ (Fin.snoc q.2 q.1 : Fin (m + 1) → ℝ))
      = ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)).symm := by
  funext q
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  exact (snoc_eq_insertNth m q.1 q.2).symm

/-- **The `Fin.snoc` splitting of Lebesgue measure.** `(t, u) ↦ Fin.snoc u t` carries the product
of Lebesgue measure on `ℝ` and on `ℝ^m` to Lebesgue measure on `ℝ^{m+1}`. -/
theorem measurePreserving_snoc (m : ℕ) :
    MeasurePreserving (fun q : ℝ × (Fin m → ℝ) ↦ (Fin.snoc q.2 q.1 : Fin (m + 1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))
      (volume : Measure (Fin (m + 1) → ℝ)) := by
  rw [snocFun_eq, (Measure.volume_eq_prod ℝ (Fin m → ℝ)).symm]
  exact (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ)
    (Fin.last m)).symm _

/-- The same map is a measurable embedding, which is what transports integrability. -/
theorem measurableEmbedding_snoc (m : ℕ) :
    MeasurableEmbedding (fun q : ℝ × (Fin m → ℝ) ↦ (Fin.snoc q.2 q.1 : Fin (m + 1) → ℝ)) := by
  rw [snocFun_eq]
  exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)).symm
    |>.measurableEmbedding

/-- Integrability transports along the splitting. -/
theorem integrable_comp_snoc {m : ℕ} {H : (Fin (m + 1) → ℝ) → ℝ} (hH : Integrable H) :
    Integrable (fun q : ℝ × (Fin m → ℝ) ↦ H (Fin.snoc q.2 q.1))
      ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
  ((measurePreserving_snoc m).integrable_comp_emb (measurableEmbedding_snoc m)).mpr hH

/-! ### The reverse triangle inequality for the `L²` seminorm -/

/-- **Cauchy–Schwarz**, in the square-root form the reverse triangle inequality needs. -/
theorem abs_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ √(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ) :=
  abs_integral_le_integral_abs.trans (by simpa only [abs_mul] using integral_abs_mul_abs_le hf hg)

/-- **The reverse triangle inequality** for `E ↦ (∫ E²)^{1/2}`, proved from Cauchy–Schwarz by
expanding `∫ (f - g)²` rather than through the `Lp` space. -/
theorem abs_sqrt_sub_sqrt_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |√(∫ x, f x ^ 2 ∂μ) - √(∫ x, g x ^ 2 ∂μ)| ≤ √(∫ x, (f x - g x) ^ 2 ∂μ) := by
  have hfs := hf.integrable_sq
  have hfg : Integrable (fun x ↦ 2 * (f x * g x)) μ := (hf.integrable_mul hg).const_mul 2
  have hA : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun _ ↦ sq_nonneg _
  have hB : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun _ ↦ sq_nonneg _
  have hexp : (∫ x, (f x - g x) ^ 2 ∂μ)
      = (∫ x, f x ^ 2 ∂μ) - 2 * (∫ x, f x * g x ∂μ) + ∫ x, g x ^ 2 ∂μ := by
    rw [← integral_const_mul, ← integral_sub hfs hfg, ← integral_add (g := fun x ↦ g x ^ 2)
      (f := fun x ↦ f x ^ 2 - 2 * (f x * g x)) (hfs.sub hfg) hg.integrable_sq]
    exact integral_congr_ae (.of_forall fun x ↦ by ring)
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [(abs_le.mp (abs_integral_mul_le hf hg)).2, Real.sq_sqrt hA, Real.sq_sqrt hB,
    Real.sqrt_nonneg (∫ x, f x ^ 2 ∂μ), Real.sqrt_nonneg (∫ x, g x ^ 2 ∂μ)]

/-! ### The marginal operator on the bounded orthant -/

/-- A coordinate of a non-negative vector is at most the total mass. -/
theorem coord_le_of_sum_le {k : ℕ} {σ : ℝ} {t : Fin k → ℝ} (h0 : ∀ i, 0 ≤ t i)
    (hs : ∑ i, t i ≤ σ) (i : Fin k) : t i ≤ σ :=
  le_trans (Finset.single_le_sum (fun j _ ↦ h0 j) (Finset.mem_univ i)) hs

/-- A function vanishing off the bounded orthant has fibres vanishing off `[0, σ]`. -/
theorem snoc_eq_zero_of_vanishing {m : ℕ} {σ : ℝ} {E : (Fin (m + 1) → ℝ) → ℝ}
    (hoff : ∀ t, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ σ) → E t = 0) (u : Fin m → ℝ) {s : ℝ}
    (hs : s < 0 ∨ σ < s) : E (Fin.snoc u s) = 0 := by
  refine hoff _ ?_
  rintro ⟨h0, hsum⟩
  have h₁ := h0 (Fin.last m)
  have h₂ := coord_le_of_sum_le h0 hsum (Fin.last m)
  rw [Fin.snoc_last] at h₁ h₂
  rcases hs with h | h <;> linarith

/-- A square-integrable function vanishing off the bounded orthant is integrable: the orthant sits
inside a cube of finite measure. -/
theorem integrable_of_vanishing {m : ℕ} {σ : ℝ} {E : (Fin (m + 1) → ℝ) → ℝ}
    (hE : MemLp E 2 volume) (hoff : ∀ t, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ σ) → E t = 0) :
    Integrable E := by
  have hvol : (volume : Measure (Fin (m + 1) → ℝ))
      (Set.univ.pi fun _ ↦ Set.Icc (0 : ℝ) σ) ≠ ⊤ := by
    rw [volume_pi, Measure.pi_pi]
    simp
  exact memLp_one_iff_integrable.mp (hE.mono_exponent_of_measure_support_ne_top
    (fun t ht ↦ hoff t fun h ↦ ht fun i _ ↦ ⟨h.1 i, coord_le_of_sum_le h.1 h.2 i⟩) hvol one_le_two)

/-- **The fibre bound.** Almost every fibre of a function vanishing off the bounded orthant lives
in an interval of length `σ`, so Cauchy–Schwarz bounds the square of its marginal by `σ` times the
fibre integral of its square. -/
theorem sq_marginal_le_ae {m : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) {E : (Fin (m + 1) → ℝ) → ℝ}
    (hE : MemLp E 2 volume) (hoff : ∀ t, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ σ) → E t = 0) :
    ∀ᵐ u : Fin m → ℝ ∂(volume : Measure (Fin m → ℝ)),
      (∫ t in Set.Ioi (0 : ℝ), E (Fin.snoc u t)) ^ 2
        ≤ σ * ∫ t in Set.Ioi (0 : ℝ), E (Fin.snoc u t) ^ 2 := by
  have hE1 := integrable_of_vanishing hE hoff
  filter_upwards [(integrable_comp_snoc hE.integrable_sq).prod_left_ae,
    (integrable_comp_snoc hE1).prod_left_ae] with u hu2 hu1
  have hLp : MemLp (fun t ↦ E (Fin.snoc u t)) 2 (volume.restrict (Set.Ioc (0 : ℝ) σ)) :=
    (memLp_two_iff_integrable_sq hu1.aestronglyMeasurable.restrict).mpr hu2.restrict
  have hCS := sq_setIntegral_abs_le (A := Set.Ioc (0 : ℝ) σ) (by simp) hLp
  rw [setIntegral_Ioc_eq_Ioi fun s hs ↦ by rw [snoc_eq_zero_of_vanishing hoff u (Or.inr hs),
      abs_zero], setIntegral_Ioc_eq_Ioi fun s hs ↦ by
      rw [snoc_eq_zero_of_vanishing hoff u (Or.inr hs), zero_pow two_ne_zero],
    Real.volume_real_Ioc_of_le hσ, sub_zero] at hCS
  exact (sq_le_sq.mpr (abs_integral_le_integral_abs.trans (le_abs_self _))).trans hCS

/-- The fibre integral of the square is integrable in `u`, and integrates to the full square. -/
theorem integral_fibre_sq {m : ℕ} {σ : ℝ} {E : (Fin (m + 1) → ℝ) → ℝ} (hE : MemLp E 2 volume)
    (hoff : ∀ t, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ σ) → E t = 0) :
    Integrable (fun u : Fin m → ℝ ↦ ∫ t in Set.Ioi (0 : ℝ), E (Fin.snoc u t) ^ 2) ∧
      (∫ u : Fin m → ℝ, ∫ t in Set.Ioi (0 : ℝ), E (Fin.snoc u t) ^ 2) = ∫ t, E t ^ 2 := by
  have hEsq := hE.integrable_sq
  rw [funext fun u ↦ setIntegral_Ioi_eq_integral fun s hs ↦ by
    simp [snoc_eq_zero_of_vanishing hoff u (Or.inl hs)]]
  refine ⟨(integrable_comp_snoc hEsq).integral_prod_right, ?_⟩
  rw [← integral_prod_symm _ (integrable_comp_snoc hEsq)]
  exact (measurePreserving_snoc m).integral_comp (measurableEmbedding_snoc m) fun t ↦ E t ^ 2

/-- The marginal of a function vanishing off the bounded orthant is square-integrable. -/
theorem memLp_marginal {m : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) {E : (Fin (m + 1) → ℝ) → ℝ}
    (hE : MemLp E 2 volume) (hoff : ∀ t, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ σ) → E t = 0) :
    MemLp (fun u : Fin m → ℝ ↦ ∫ t in Set.Ioi (0 : ℝ), E (Fin.snoc u t)) 2 volume := by
  have hmeas : AEStronglyMeasurable
      (fun u : Fin m → ℝ ↦ ∫ t in Set.Ioi (0 : ℝ), E (Fin.snoc u t)) volume := by
    rw [funext fun u ↦ setIntegral_Ioi_eq_integral fun s hs ↦
      snoc_eq_zero_of_vanishing hoff u (Or.inl hs)]
    exact (integrable_comp_snoc (integrable_of_vanishing hE hoff)).integral_prod_right
      |>.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hmeas).mpr ?_
  refine Integrable.mono' (((integral_fibre_sq hE hoff).1).const_mul σ) (hmeas.pow 2) ?_
  filter_upwards [sq_marginal_le_ae hσ hE hoff] with u hu
  rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

/-- **The marginal form is bounded by the fibre length.** For `E` square-integrable and vanishing
off the bounded orthant, `J̃_c(E) ≤ σ ‖E‖₂²` at every cutoff `c`.

This is the "squared norm at most the fibre length" bound: the cutoff only shrinks the region of
integration, so it plays no part. -/
theorem marginalForm_le {m : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) (c : ℝ) {E : (Fin (m + 1) → ℝ) → ℝ}
    (hE : MemLp E 2 volume) (hoff : ∀ t, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ σ) → E t = 0) :
    marginalForm c E ≤ σ * ∫ t, E t ^ 2 := by
  obtain ⟨hint, hval⟩ := integral_fibre_sq hE hoff
  simp only [marginalForm]
  calc (∫ u in {u : Fin m → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c},
        (∫ t in Set.Ioi (0 : ℝ), E (Fin.snoc u t)) ^ 2)
      ≤ ∫ u : Fin m → ℝ, (∫ t in Set.Ioi (0 : ℝ), E (Fin.snoc u t)) ^ 2 :=
        setIntegral_le_integral (memLp_marginal hσ hE hoff).integrable_sq
          (.of_forall fun _ ↦ sq_nonneg _)
    _ ≤ ∫ u : Fin m → ℝ, σ * ∫ t in Set.Ioi (0 : ℝ), E (Fin.snoc u t) ^ 2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
          (hint.const_mul σ) (sq_marginal_le_ae hσ hE hoff)
    _ = σ * ∫ t, E t ^ 2 := by rw [integral_const_mul, hval]

/-- The marginal is additive, for almost every `u`: the fibres are integrable. -/
theorem marginal_sub_ae {m : ℕ} {σ : ℝ} {G H : (Fin (m + 1) → ℝ) → ℝ} (hG : MemLp G 2 volume)
    (hH : MemLp H 2 volume) (hGoff : ∀ t, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ σ) → G t = 0)
    (hHoff : ∀ t, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ σ) → H t = 0) :
    ∀ᵐ u : Fin m → ℝ ∂(volume : Measure (Fin m → ℝ)),
      (∫ t in Set.Ioi (0 : ℝ), (G (Fin.snoc u t) - H (Fin.snoc u t)))
        = (∫ t in Set.Ioi (0 : ℝ), G (Fin.snoc u t))
          - ∫ t in Set.Ioi (0 : ℝ), H (Fin.snoc u t) := by
  filter_upwards [(integrable_comp_snoc (integrable_of_vanishing hG hGoff)).prod_left_ae,
    (integrable_comp_snoc (integrable_of_vanishing hH hHoff)).prod_left_ae] with u hGu hHu
  exact integral_sub hGu.restrict hHu.restrict

/-- **The marginal form is Lipschitz in `L²`.** For `G` and `H` square-integrable and vanishing off
the part of the closed orthant of total mass at most `σ`,
`|J̃_c(G)^{1/2} - J̃_c(H)^{1/2}| ≤ σ^{1/2} ‖G - H‖₂`.

The square root of the marginal form is a seminorm — it is the `L²` norm of the marginal, which
depends linearly on the function — so the reverse triangle inequality applies; and the seminorm of
`G - H` is bounded by the fibre length times its `L²` norm. So `J̃` is continuous in `L²`. -/
@[gap212 "lem_marginal_form_lipschitz"]
theorem abs_sqrt_marginalForm_sub_le {m : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) (c : ℝ)
    {G H : (Fin (m + 1) → ℝ) → ℝ} (hG : MemLp G 2 volume) (hH : MemLp H 2 volume)
    (hGoff : ∀ t, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ σ) → G t = 0)
    (hHoff : ∀ t, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ σ) → H t = 0) :
    |√(marginalForm c G) - √(marginalForm c H)| ≤ √σ * √(∫ t, (G t - H t) ^ 2) := by
  set S : Set (Fin m → ℝ) := {u : Fin m → ℝ | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c} with hS
  -- The two marginals, square-integrable on the region.
  have hGm : MemLp (fun u : Fin m → ℝ ↦ ∫ t in Set.Ioi (0 : ℝ), G (Fin.snoc u t)) 2
      (volume.restrict S) := (memLp_marginal hσ hG hGoff).restrict S
  have hHm : MemLp (fun u : Fin m → ℝ ↦ ∫ t in Set.Ioi (0 : ℝ), H (Fin.snoc u t)) 2
      (volume.restrict S) := (memLp_marginal hσ hH hHoff).restrict S
  have hoffD : ∀ t, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ σ) → (fun t ↦ G t - H t) t = 0 :=
    fun t ht ↦ by simp only [hGoff t ht, hHoff t ht, sub_zero]
  calc |√(marginalForm c G) - √(marginalForm c H)|
      ≤ √(∫ u in S, ((∫ t in Set.Ioi (0 : ℝ), G (Fin.snoc u t))
          - ∫ t in Set.Ioi (0 : ℝ), H (Fin.snoc u t)) ^ 2) :=
        abs_sqrt_sub_sqrt_le hGm hHm
    _ = √(marginalForm c fun t ↦ G t - H t) := by
        simp only [marginalForm, ← hS]
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (marginal_sub_ae hG hH hGoff hHoff)] with u hu
        rw [hu]
    _ ≤ √(σ * ∫ t, (G t - H t) ^ 2) :=
        Real.sqrt_le_sqrt (marginalForm_le hσ c (hG.sub hH) hoffD)
    _ = √σ * √(∫ t, (G t - H t) ^ 2) := Real.sqrt_mul hσ _

/-! ### The `|F|` step -/

/-- The marginal form is non-negative: its integrand is a square. -/
theorem marginalForm_nonneg {m : ℕ} (c : ℝ) (G : (Fin (m + 1) → ℝ) → ℝ) :
    0 ≤ marginalForm c G :=
  integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)

/-- **The gap survives replacement by the absolute value.** If `G` is square-integrable,
vanishes off `T_{m+1}(p)` and has the variational gap at cutoff `c`, then so does `|G|`.

`I_T` is untouched, being an integral of `G²`; and `J̃_c` cannot decrease, because it is a
restricted square of a *marginal* — the inequality `|∫G| ≤ ∫|G|` survives squaring. For a
multi-band `J` the inner double integral is not a square. -/
@[gap212 "lem_abs_gap"]
theorem hasVariationalGap_abs {p : SupportParams} {m : ℕ} {c : ℝ}
    {G : (Fin (m + 1) → ℝ) → ℝ} (hG : MemLp G 2 volume)
    (hoff : ∀ t, t ∉ T p (m + 1) → G t = 0) (hgap : HasVariationalGap p m c G) :
    HasVariationalGap p m c fun t ↦ |G t| := by
  -- `I_T` does not see the absolute value.
  have hI : Iint p (m + 1) (fun t ↦ |G t|) = Iint p (m + 1) G := by
    simp only [Iint, sq_abs]
  -- The support lies in the orthant, at total mass below `1/2`.
  have hoff' : ∀ t, ¬((∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1) → |G t| = 0 := fun t ht ↦ by
    refine abs_eq_zero.mpr (hoff t fun hmem ↦ ht ?_)
    obtain ⟨j, hcube, hwin, -⟩ := Set.mem_iUnion.mp hmem
    have := p.A_mono.monotone (Fin.le_last j.succ)
    exact ⟨fun i ↦ (hcube i).1, by linarith [hwin.2, p.A_last, p.ε_pos]⟩
  -- The marginal of `|G|` is square-integrable, and dominates that of `G` pointwise.
  have hmono : marginalForm c G ≤ marginalForm c fun t ↦ |G t| :=
    integral_mono_of_nonneg (.of_forall fun _ ↦ sq_nonneg _)
      (memLp_marginal zero_le_one hG.abs hoff').integrable_sq.restrict
      (.of_forall fun _ ↦ sq_le_sq.mpr (abs_integral_le_integral_abs.trans (le_abs_self _)))
  refine ⟨hI ▸ hgap.1, ?_⟩
  rw [hI]
  exact hgap.2.trans_le (mul_le_mul_of_nonneg_left hmono (by positivity))

end Gap212.GPY
