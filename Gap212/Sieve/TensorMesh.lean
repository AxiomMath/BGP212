/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.TensorFacts
public import Gap212.Sieve.UStrip
public import Gap212.Sieve.TensorDensity
public import Gap212.Sieve.RetreatFacts
public import Gap212.Sieve.BufferedFacts
public import Gap212.Sieve.Asymptotics
public meta import Gap212.Attr

/-!
# The tensor mesh transfers the gap

A smooth symmetric `F₀` with the variational gap on the
buffered region is replaced by a finite tensor datum whose *discrete* forms still have the gap.

## How the mesh is chosen

The argument needs `ε₃` "small enough". Everything the choice has to beat is quantified here
in terms of `(F₀, ζ₁)` alone, and every constraint takes the shape `ε₃(P + ε₃Q) < ρ`, so one
application of `Gap212.GPY.exists_mesh_quadratic` with the summed constants discharges all of them.
The two moduli are `Gap212.GPY.abs_setIntegral_sq_sub_Iint_le` for the denominator and
`Gap212.GPY.abs_marginalForm_moveLastTo_sub_le` for each numerator; both are stated over the unit
box, whose volume is `1` (`Gap212.GPY.volumeReal_unitBox`), which is why no volume factor survives.

## Reading a coordinate as the last one

`Gap212.GPY.marginalForm` integrates out the *last* coordinate, while `𝓙ᵢ` is about the `i`-th. The
two are joined by `Gap212.GPY.moveLastTo`, the coordinate permutation putting slot `i` last, and
this is the one place the *symmetry of `F₀`* is spent: `F₀` is invariant under it, so all `k`
numerators converge to the same `J̃_c(F₀)`. `F_{ε₃}` is **not** symmetric, and no step assumes it
is.

## Main results

* `Gap212.GPY.setIntegral_orthant_sq_eq_Iint`: `∫_{[0,∞)^k} F² = I_T(F)` for `F` vanishing off
  `T_k(p)`.
* `Gap212.GPY.setIntegral_tensorMarginal_sq_eq_marginalForm`: the restricted integral of `Γᵢ²` is
  the marginal form of the tensor sum read with slot `i` last.
* `Gap212.GPY.formJMarginal_tensor_eq_sub`: `𝓙ᵢ` is that marginal form minus the thin strip.
* `Gap212.GPY.exists_tensorDatum_forms_gap`: the transfer itself.
-/

@[expose] public section

namespace Gap212.GPY

open Finset MeasureTheory Set
open scoped Nat

/-! ### The closed orthant -/

/-- The closed orthant `[0,∞)^k`, the region both discrete forms are integrals over. -/
theorem measurableSet_orthant (k : ℕ) :
    MeasurableSet (Set.univ.pi fun _ : Fin k ↦ Set.Ici (0 : ℝ)) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ici

/-- The support sits inside the closed orthant: every coordinate of a point of `T_k(p)` is in
`[0,1]`. -/
theorem T_subset_orthant (p : SupportParams) (k : ℕ) :
    T p k ⊆ Set.univ.pi fun _ : Fin k ↦ Set.Ici (0 : ℝ) := fun _ ht ↦
  Set.mem_univ_pi.mpr fun i ↦ (mem_unitCube_of_mem_T ht i).1

/-- **The denominator is the orthant integral.** For `F` vanishing off `T_k(p)`,
`∫_{[0,∞)^k} F² = I_T(F)`.

This is the first of the three steps the transfer needs: `Gap212.GPY.formI_of_tensor` computes
`𝓘` as an integral over the orthant, while the certificate's `I_T` is an integral over `T_k(p)`,
and the two agree as soon as `F` vanishes off the smaller region. Only the *larger* region has to
be measurable, which is why no measurability of `T_k(p)` is needed. -/
theorem setIntegral_orthant_sq_eq_Iint {p : SupportParams} {k : ℕ} {F : (Fin k → ℝ) → ℝ}
    (hF : ∀ t, t ∉ T p k → F t = 0) :
    (∫ t in Set.univ.pi fun _ : Fin k ↦ Set.Ici (0 : ℝ), F t ^ 2) = Iint p k F :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_orthant k)
    (T_subset_orthant p k) fun t ht ↦ by rw [hF t ht.2]; ring

/-- **The buffered region sits inside the retreat region**: the case `η = 0` of
`Gap212.GPY.mem_retreatRegion_of_mem_bufferedRegion`. -/
theorem bufferedRegion_subset_retreatRegion {p : SupportParams} {k : ℕ} {j : Fin p.n}
    {ε₀ ζ₁ κ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ ≤ 1) (hζ₁ : 0 < ζ₁) (hκ : 0 < κ)
    (hκk : (k : ℝ) * ζ₁ ≤ κ) :
    bufferedRegion p k j ε₀ ζ₁ κ ⊆ retreatRegion p k j ε₀ := fun _ ht ↦
  mem_retreatRegion_of_mem_bufferedRegion hε₀ hε₀' hζ₁ hκ hζ₁.le (by simpa using hκk) ht
    fun _ ↦ by simp

/-! ### Reading one coordinate as the last -/

/-- The map `Fin (m+1) → Fin (m+1)` sending the last slot to `i` and `s.castSucc` to
`i.succAbove s`. -/
def slotMap {m : ℕ} (i : Fin (m + 1)) : Fin (m + 1) → Fin (m + 1) :=
  Fin.lastCases i i.succAbove

/-- `slotMap i` sends `Fin.last m` to `i`. -/
@[simp] theorem slotMap_last {m : ℕ} (i : Fin (m + 1)) : slotMap i (Fin.last m) = i := by
  simp [slotMap]

/-- `slotMap i` sends `s.castSucc` to `i.succAbove s`. -/
@[simp] theorem slotMap_castSucc {m : ℕ} (i : Fin (m + 1)) (s : Fin m) :
    slotMap i s.castSucc = i.succAbove s := by
  simp [slotMap]

/-- `slotMap i` is injective. -/
theorem slotMap_injective {m : ℕ} (i : Fin (m + 1)) : Function.Injective (slotMap i) := by
  intro a b hab
  cases a using Fin.lastCases <;> cases b using Fin.lastCases <;>
    simp_all [Fin.succAbove_ne, (Fin.succAbove_ne _ _).symm]

/-- **The permutation that puts slot `i` last.** It sends `Fin.last m` to `i` and `s.castSucc` to
`i.succAbove s`, so precomposing a tuple with it turns `Fin.insertNth i t u` into
`Fin.snoc u t`. -/
noncomputable def slotPerm {m : ℕ} (i : Fin (m + 1)) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.ofBijective (slotMap i) (Finite.injective_iff_bijective.mp (slotMap_injective i))

/-- `slotPerm i j = slotMap i j`. -/
@[simp] theorem slotPerm_apply {m : ℕ} (i : Fin (m + 1)) (j : Fin (m + 1)) :
    slotPerm i j = slotMap i j := rfl

/-- Precomposing `Fin.insertNth i t u` with `slotPerm i` gives `Fin.snoc u t`. -/
theorem insertNth_comp_slotPerm {m : ℕ} (i : Fin (m + 1)) (t : ℝ) (u : Fin m → ℝ) :
    (i.insertNth t u : Fin (m + 1) → ℝ) ∘ slotPerm i = Fin.snoc u t := by
  funext j
  cases j using Fin.lastCases <;> simp

/-- **A symmetric function does not see which slot is singled out.** For `F` symmetric,
`F (Fin.insertNth i t u) = F (Fin.snoc u t)`.

This is where the symmetry of `F₀` is spent: the `i`-th marginal form of a
symmetric function is its last-coordinate marginal form, so all `k` numerators converge to the same
`J̃_c(F₀)`. -/
theorem apply_insertNth_of_symmetric {m : ℕ} {F : (Fin (m + 1) → ℝ) → ℝ} (hF : Symmetric F)
    (i : Fin (m + 1)) (t : ℝ) (u : Fin m → ℝ) :
    F (i.insertNth t u) = F (Fin.snoc u t) := by
  rw [← insertNth_comp_slotPerm i t u, hF (slotPerm i) (i.insertNth t u)]

/-- **Slot `i` moved to the last place**: `(moveLastTo i v)` is `v` with its last entry put in slot
`i` and the rest spread over the others. It is the substitution that turns the last-coordinate
marginal form into the `i`-th one. -/
def moveLastTo {m : ℕ} (i : Fin (m + 1)) (v : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  i.insertNth (v (Fin.last m)) (Fin.init v)

/-- `moveLastTo i (Fin.snoc u t) = Fin.insertNth i t u`. -/
theorem moveLastTo_snoc {m : ℕ} (i : Fin (m + 1)) (t : ℝ) (u : Fin m → ℝ) :
    moveLastTo i (Fin.snoc u t) = i.insertNth t u := by
  simp [moveLastTo]

/-- For a symmetric `F` the substitution is invisible. -/
theorem moveLastTo_of_symmetric {m : ℕ} {F : (Fin (m + 1) → ℝ) → ℝ} (hF : Symmetric F)
    (i : Fin (m + 1)) : (fun v ↦ F (moveLastTo i v)) = F := by
  funext v
  rw [moveLastTo, apply_insertNth_of_symmetric hF, Fin.snoc_init_self]

/-! ### The `i`-th tensor marginal as a fibre integral -/

/-- The tensor sum `∑_l cₗ ∏_i g_{l,i}(tᵢ)` of a family of one-variable factors. -/
noncomputable def tensorSum {L k : ℕ} (cf : Fin L → ℝ) (g : Fin L → Fin k → ℝ → ℝ)
    (t : Fin k → ℝ) : ℝ :=
  ∑ l, cf l * ∏ j, g l j (t j)

/-- The tensor sum factors at slot `i`. -/
theorem tensorSum_insertNth {L m : ℕ} (cf : Fin L → ℝ) (g : Fin L → Fin (m + 1) → ℝ → ℝ)
    (i : Fin (m + 1)) (t : ℝ) (u : Fin m → ℝ) :
    tensorSum cf g (i.insertNth t u)
      = ∑ l, cf l * g l i t * ∏ s : Fin m, g l (i.succAbove s) (u s) := by
  simp only [tensorSum, Fin.prod_univ_succAbove _ i, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove, mul_assoc]

/-- **The `i`-th tensor marginal is the slot-`i` fibre integral of the tensor sum.**
`Γᵢ(u) = ∫_0^∞ (∑_l cₗ ∏_j g_{l,j}) (Fin.insertNth i t u) dt`.

Each term of the tensor sum is a product, so the slot-`i` factor contributes its total mass and the
others are untouched; the exchange of the finite sum with the integral needs only that each factor
is continuous with compact support. -/
theorem tensorMarginal_eq_fibreIntegral {L m : ℕ} (cf : Fin L → ℝ)
    (g : Fin L → Fin (m + 1) → ℝ → ℝ) (hg : ∀ l s, Continuous (g l s))
    (hgc : ∀ l s, HasCompactSupport (g l s)) (i : Fin (m + 1)) (u : Fin m → ℝ) :
    (∫ t in Set.Ioi (0 : ℝ), tensorSum cf g (i.insertNth t u)) = tensorMarginal cf g i u := by
  simp_rw [tensorSum_insertNth]
  rw [integral_finsetSum _ fun l _ ↦
    ((((hg l i).integrable_of_hasCompactSupport (hgc l i)).restrict.const_mul _).mul_const _)]
  simp only [tensorMarginal, integral_mul_const, integral_const_mul]

/-- **The restricted integral of `Γᵢ²` is a marginal form.** It is `J̃_c` of the tensor sum read
with slot `i` in the last place.

This is the identity "`Γᵢ` is the `i`-th marginal of `F_{ε₃}`": the outer
region of `Gap212.GPY.marginalForm` is the same corner simplex in either reading, and the inner
fibre integral is `Gap212.GPY.tensorMarginal_eq_fibreIntegral`. -/
theorem setIntegral_tensorMarginal_sq_eq_marginalForm {L m : ℕ} (cf : Fin L → ℝ)
    (g : Fin L → Fin (m + 1) → ℝ → ℝ) (hg : ∀ l s, Continuous (g l s))
    (hgc : ∀ l s, HasCompactSupport (g l s)) (i : Fin (m + 1)) (c : ℝ) :
    (∫ u in {u : Fin m → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c}, tensorMarginal cf g i u ^ 2)
      = marginalForm c fun v ↦ tensorSum cf g (moveLastTo i v) := by
  simp only [marginalForm, moveLastTo_snoc, tensorMarginal_eq_fibreIntegral cf g hg hgc]

/-! ### The substitution is a coordinate permutation -/

/-- `moveLastTo i v` is `v` precomposed with the inverse of `slotPerm i`. -/
theorem moveLastTo_eq_comp {m : ℕ} (i : Fin (m + 1)) (v : Fin (m + 1) → ℝ) :
    moveLastTo i v = v ∘ (slotPerm i).symm := by
  rw [Equiv.eq_comp_symm, moveLastTo, insertNth_comp_slotPerm, Fin.snoc_init_self]

/-- `moveLastTo i` preserves the sum of the coordinates. -/
theorem sum_moveLastTo {m : ℕ} (i : Fin (m + 1)) (v : Fin (m + 1) → ℝ) :
    ∑ j, moveLastTo i v j = ∑ j, v j := by
  rw [moveLastTo_eq_comp]
  exact Equiv.sum_comp _ _

/-- `moveLastTo i` preserves coordinatewise nonnegativity. -/
theorem moveLastTo_nonneg {m : ℕ} (i : Fin (m + 1)) {v : Fin (m + 1) → ℝ}
    (hv : ∀ j, 0 ≤ v j) (j : Fin (m + 1)) : 0 ≤ moveLastTo i v j := by
  rw [moveLastTo_eq_comp]; exact hv _

/-- `moveLastTo i` is continuous. -/
theorem continuous_moveLastTo {m : ℕ} (i : Fin (m + 1)) :
    Continuous (moveLastTo i : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ) := by
  rw [funext (moveLastTo_eq_comp i)]
  fun_prop

/-! ### Two elementary bounds -/

/-- A function vanishing outside a coordinate box has compact support. -/
theorem hasCompactSupport_of_box {k : ℕ} {a b : ℝ} {h : (Fin k → ℝ) → ℝ}
    (hs : ∀ v, h v ≠ 0 → ∀ i, v i ∈ Set.Icc a b) : HasCompactSupport h := by
  refine .intro (isCompact_univ_pi fun _ ↦ isCompact_Icc (a := a) (b := b)) fun v hv ↦ ?_
  by_contra h
  exact hv (Set.mem_univ_pi.mpr (hs v h))

/-- `|a² - b²| ≤ 2Db + D²` when `|a - b| ≤ D` and `a`, `b`, `D` are non-negative. This is how the
`L²`-Lipschitz bound on `√J̃` becomes a bound on `J̃`. -/
theorem abs_sq_sub_sq_le {a b D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hD : 0 ≤ D)
    (h : |a - b| ≤ D) : |a ^ 2 - b ^ 2| ≤ 2 * D * b + D ^ 2 := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp h
  rw [abs_le]
  constructor <;> nlinarith

/-- **A mesh small enough for a quadratic bound.** For `P, Q ≥ 0`, `ρ > 0` and `B > 0` there is an
`ε ∈ (0, min(B,1)]` with `ε(P + εQ) < ρ`.

This is the modulus that "choose `ε₃` small enough" needs: every constraint the mesh has
to satisfy is of this shape, with `P` and `Q` determined by `F₀` alone, and one application with
the summed constants discharges all of them at once, because `ε(P + εQ)` is monotone in `ε ≥ 0`. -/
theorem exists_mesh_quadratic {P Q ρ B : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hρ : 0 < ρ) (hB : 0 < B) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ B ∧ ε ≤ 1 ∧ ε * (P + ε * Q) < ρ := by
  have hD : (0 : ℝ) < P + Q + 1 := by linarith
  set ε := min B (min 1 (ρ / (2 * (P + Q + 1))))
  have hε0 : 0 < ε := lt_min hB (lt_min one_pos (by positivity))
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hεr : ε * (2 * (P + Q + 1)) ≤ ρ :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε, hε0, min_le_left _ _, hε1, ?_⟩
  linarith [mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hQ hε1) hε0.le, mul_pos hε0 hD]

/-! ### The unit box -/

/-- The unit box `[0,1]^k` has volume `1`. It is the fixed bounded set both `F₀` and every tensor
approximation of it are supported in, so it is the volume factor in every mesh estimate. -/
theorem volumeReal_unitBox (k : ℕ) :
    volume.real (Set.univ.pi fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1) = 1 := by
  simp [Measure.real, Set.pi_univ_Icc, Real.volume_Icc_pi]

/-- A property of every coordinate of `moveLastTo i v` is a property of every coordinate of `v`:
the substitution permutes the coordinates. -/
theorem moveLastTo_forall {m : ℕ} (i : Fin (m + 1)) {P : ℝ → Prop} {v : Fin (m + 1) → ℝ}
    (h : ∀ j, P (moveLastTo i v j)) (j : Fin (m + 1)) : P (v j) := by
  simpa [moveLastTo_eq_comp, -slotPerm_apply] using h (slotPerm i j)

/-! ### Where the tensor sum can be non-zero -/

/-- A point at which the tensor sum is non-zero lies in one of the mesh boxes. -/
theorem exists_box_of_tensorSum_ne_zero {L k : ℕ} {cf : Fin L → ℝ} {g : Fin L → Fin k → ℝ → ℝ}
    {α β : Fin L → Fin k → ℝ}
    (hsupp : ∀ l s, Function.support (g l s) ⊆ Set.Icc (α l s) (β l s))
    {v : Fin k → ℝ} (hv : tensorSum cf g v ≠ 0) :
    ∃ l, ∀ j, v j ∈ Set.Icc (α l j) (β l j) := by
  simp only [tensorSum] at hv
  obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  refine ⟨l, fun j ↦ hsupp l j fun h ↦ hl ?_⟩
  rw [Finset.prod_eq_zero (Finset.mem_univ j) h, mul_zero]

/-- **A mesh box lies in the retreat region.** Every point of a box that meets the
`ε₃`-neighbourhood of `supp F₀` is within `ε₃` of a point of the buffered region, hence in the
retreat region by `Gap212.GPY.mem_retreatRegion_of_mem_bufferedRegion`. -/
theorem mem_retreatRegion_of_mem_box {p : SupportParams} {k : ℕ} {j : Fin p.n} {ε₀ ζ₁ κ ε₃ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀' : ε₀ ≤ 1) (hζ₁ : 0 < ζ₁) (hκ : 0 < κ) (hε₃ζ : ε₃ ≤ ζ₁)
    (hκk : (k : ℝ) * (ζ₁ + ε₃) ≤ κ) {F₀ : (Fin k → ℝ) → ℝ}
    (hoff : ∀ t, t ∉ bufferedRegion p k j ε₀ ζ₁ κ → F₀ t = 0) {α β : Fin k → ℝ}
    (hnbhd : ∀ t : Fin k → ℝ, (∀ i, t i ∈ Set.Icc (α i) (β i)) →
      ∃ s ∈ Function.support F₀, ∀ i, |t i - s i| ≤ ε₃)
    {w : Fin k → ℝ} (hw : ∀ i, w i ∈ Set.Icc (α i) (β i)) :
    w ∈ retreatRegion p k j ε₀ := by
  obtain ⟨s, hs, hd⟩ := hnbhd w hw
  exact mem_retreatRegion_of_mem_bufferedRegion hε₀ hε₀' hζ₁ hκ hε₃ζ hκk
    (Function.support_subset_iff'.mpr hoff hs) hd

/-! ### The denominator is close to `I_T(F₀)` -/

/-- A real square vanishes only where the real does. -/
theorem ne_zero_of_sq_ne_zero {x : ℝ} (h : x ^ 2 ≠ 0) : x ≠ 0 := fun h0 ↦ h (by rw [h0]; ring)

private theorem norm_sq_le_sq {x M : ℝ} (h : |x| ≤ M) : ‖x ^ 2‖ ≤ M ^ 2 := by
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- **The denominator moves by at most `ε₃(2‖F₀‖_∞ + ε₃)·vol`.** Both `F₀` and its tensor
approximation vanish off the unit box, so their squares differ by at most `ε₃(2‖F₀‖_∞+ε₃)` on a set
of fixed finite volume and by nothing elsewhere.

This is the quantitative form of "`𝓘 → I_T(F₀)`": the modulus is explicit in the
data `(F₀, ζ₁)`, which is what lets the mesh be chosen against it. -/
theorem abs_setIntegral_sq_sub_Iint_le {p : SupportParams} {k : ℕ} {ε₃ M₀ : ℝ} (hε₃ : 0 ≤ ε₃)
    {F₀ Fε : (Fin k → ℝ) → ℝ} (hcε : Continuous Fε) (hc₀ : Continuous F₀)
    (hM₀ : ∀ v, |F₀ v| ≤ M₀) (happ : ∀ v, |F₀ v - Fε v| ≤ ε₃)
    (hbε : ∀ v, Fε v ≠ 0 → ∀ i, v i ∈ Set.Icc (0 : ℝ) 1)
    (hb₀ : ∀ v, F₀ v ≠ 0 → ∀ i, v i ∈ Set.Icc (0 : ℝ) 1)
    (hT : ∀ t, t ∉ T p k → F₀ t = 0) :
    |(∫ v in Set.univ.pi fun _ : Fin k ↦ Set.Ici (0 : ℝ), Fε v ^ 2) - Iint p k F₀|
      ≤ ε₃ * (2 * M₀ + ε₃) *
        volume.real (Set.univ.pi fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1) := by
  have hBoxfin : volume (Set.univ.pi fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1) < ⊤ :=
    (isCompact_univ_pi fun _ ↦ isCompact_Icc).measure_lt_top
  have hsub : (Set.univ.pi fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1)
      ⊆ Set.univ.pi fun _ : Fin k ↦ Set.Ici (0 : ℝ) := fun v hv ↦
    Set.mem_univ_pi.mpr fun i ↦ (Set.mem_univ_pi.mp hv i).1
  have hres : ∀ G : (Fin k → ℝ) → ℝ, (∀ v, G v ≠ 0 → ∀ i, v i ∈ Set.Icc (0 : ℝ) 1) →
      (∫ v in Set.univ.pi fun _ : Fin k ↦ Set.Ici (0 : ℝ), G v ^ 2)
        = ∫ v in Set.univ.pi fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1, G v ^ 2 := fun G hG ↦
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_orthant k) hsub
      fun v hv ↦ by_contra fun h ↦ hv.2 (Set.mem_univ_pi.mpr (hG v (ne_zero_of_sq_ne_zero h)))
  have hiε : Integrable fun v : Fin k → ℝ ↦ Fε v ^ 2 :=
    (hcε.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_of_box fun v hv i ↦ hbε v (ne_zero_of_sq_ne_zero hv) i)
  have hi₀ : Integrable fun v : Fin k → ℝ ↦ F₀ v ^ 2 :=
    (hc₀.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_of_box fun v hv i ↦ hb₀ v (ne_zero_of_sq_ne_zero hv) i)
  rw [hres _ hbε, ← setIntegral_orthant_sq_eq_Iint hT, hres _ hb₀,
    ← integral_sub hiε.integrableOn hi₀.integrableOn, ← Real.norm_eq_abs]
  refine norm_setIntegral_le_of_norm_le_const hBoxfin fun v _ ↦ ?_
  have h₁ : |Fε v - F₀ v| ≤ ε₃ := abs_sub_comm (F₀ v) (Fε v) ▸ happ v
  rw [Real.norm_eq_abs, sq_sub_sq, abs_mul, mul_comm |Fε v + F₀ v|]
  exact mul_le_mul h₁ ((abs_add_le _ _).trans
    (by linarith [hM₀ v, abs_sub_abs_le_abs_sub (Fε v) (F₀ v)])) (abs_nonneg _) hε₃

/-! ### The numerator of one coordinate -/

/-- **The numerator of coordinate `i` is the `i`-th marginal form minus a thin-strip error.**
`𝓙ᵢ = J̃_c(F_{ε₃} read at slot `i`) - A` with `0 ≤ A ≤ (k-1)ε₃c^{k-2}/(k-2)!·M²`, at `k = r+2`.

Three steps: the low index set makes the integrand vanish above the cutoff, so the orthant integral
of `Gap212.GPY.formJ_of_tensor` restricts to the corner simplex; there the `Γᵢ²` part is a marginal
form by `Gap212.GPY.setIntegral_tensorMarginal_sq_eq_marginalForm`; and the `Γ_{i,𝒰}²` part is the
discarded strip, bounded by `Gap212.GPY.setIntegral_tensorMarginalHigh_sq_le`. -/
theorem formJMarginal_tensor_eq_sub {L r : ℕ} {c ε₃ M : ℝ} (hc : 0 ≤ c) (hε₃ : 0 ≤ ε₃)
    {cf : Fin L → ℝ} {g : Fin L → Fin (r + 2) → ℝ → ℝ} {α β : Fin L → Fin (r + 2) → ℝ}
    (hcf : ∀ l, 0 ≤ cf l) (hgnn : ∀ l s t, 0 ≤ g l s t)
    (hgcont : ∀ l s, Continuous (g l s)) (hgc : ∀ l s, HasCompactSupport (g l s))
    (hsupp : ∀ l s, Function.support (g l s) ⊆ Set.Icc (α l s) (β l s))
    (hlen : ∀ l s, β l s - α l s ≤ ε₃) (i : Fin (r + 2))
    (hM : ∀ u, |tensorMarginal cf g i u| ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧ A ≤ ((r : ℝ) + 1) * ε₃ * c ^ r / (r ! : ℝ) * M ^ 2 ∧
      Defs.formJMarginal cf (fun l ↦ tailTransform (g l i) 0)
          (fun l l' s ↦ ∫ t in Set.Ioi (0 : ℝ),
            deriv (tailTransform (g l (i.succAbove s))) t *
              deriv (tailTransform (g l' (i.succAbove s))) t)
          (Defs.LSet fun l ↦ ∑ s : Fin (r + 1), β l (i.succAbove s) < c)
          (Defs.USet fun l ↦ ∑ s : Fin (r + 1), β l (i.succAbove s) < c)
        = marginalForm c (fun v ↦ tensorSum cf g (moveLastTo i v)) - A := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  -- Every term of the marginal is non-negative, so `0 ≤ Γ_{i,𝒰} ≤ Γᵢ ≤ M`.
  have hterm0 : ∀ (l : Fin L) (u : Fin (r + 1) → ℝ),
      0 ≤ cf l * (∫ t in Set.Ioi (0 : ℝ), g l i t) *
        ∏ s : Fin (r + 1), g l (i.succAbove s) (u s) :=
    fun l u ↦ mul_nonneg (mul_nonneg (hcf l)
      (setIntegral_nonneg measurableSet_Ioi fun t _ ↦ hgnn l i t))
      (Finset.prod_nonneg fun s _ ↦ hgnn _ _ _)
  have hΨ0 : ∀ (𝓥 : Finset (Fin L)) (u : Fin (r + 1) → ℝ),
      0 ≤ tensorMarginalHigh cf g 𝓥 i u := fun 𝓥 u ↦
    Finset.sum_nonneg fun l _ ↦ hterm0 l u
  have hΨM : ∀ (𝓥 : Finset (Fin L)) (u : Fin (r + 1) → ℝ),
      |tensorMarginalHigh cf g 𝓥 i u| ≤ M := by
    intro 𝓥 u
    rw [abs_of_nonneg (hΨ0 𝓥 u)]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun l _ _ ↦
      hterm0 l u).trans ((le_abs_self _).trans (hM u))
  -- Continuity of the two marginals.
  have hΓcont : Continuous (tensorMarginal cf g i) := by
    unfold tensorMarginal
    fun_prop
  have hΨcont : ∀ 𝓥 : Finset (Fin L), Continuous (tensorMarginalHigh cf g 𝓥 i) := by
    unfold tensorMarginalHigh
    fun_prop
  -- The corner simplex has finite volume.
  have hcsfin : volume {u : Fin (r + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c} ≠ ⊤ :=
    volume_cornerSimplex (r + 1) c hc ▸ ENNReal.ofReal_ne_top
  have hΓint : IntegrableOn (fun u ↦ tensorMarginal cf g i u ^ 2)
      {u : Fin (r + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c} :=
    Measure.integrableOn_of_bounded hcsfin (hΓcont.pow 2).aestronglyMeasurable
      (.of_forall fun u ↦ norm_sq_le_sq (hM u))
  have hΨint : ∀ 𝓥 : Finset (Fin L), IntegrableOn (fun u ↦ tensorMarginalHigh cf g 𝓥 i u ^ 2)
      {u : Fin (r + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c} := fun 𝓥 ↦
    Measure.integrableOn_of_bounded hcsfin ((hΨcont 𝓥).pow 2).aestronglyMeasurable
      (.of_forall fun u ↦ norm_sq_le_sq (hΨM 𝓥 u))
  refine ⟨∫ u in {u : Fin (r + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c},
    tensorMarginalHigh cf g (Defs.USet fun l ↦ ∑ s : Fin (r + 1), β l (i.succAbove s) < c) i u ^ 2,
    setIntegral_nonneg (measurableSet_cornerSimplex (r + 1) c) fun u _ ↦ sq_nonneg _,
    setIntegral_tensorMarginalHigh_sq_le hc hε₃ hcf hgnn hsupp hlen hM _ fun l ↦ Iff.rfl, ?_⟩
  -- The low part vanishes above the cutoff, so the orthant integral restricts.
  have hlowvan : ∀ u : Fin (r + 1) → ℝ, (∀ s, 0 ≤ u s) → c < ∑ s, u s →
      tensorMarginalHigh cf g
        (Defs.LSet fun l ↦ ∑ s : Fin (r + 1), β l (i.succAbove s) < c) i u = 0 := by
    intro u _ hlt
    refine Finset.sum_eq_zero fun l hl ↦ ?_
    rw [Finset.prod_eq_zero_iff.mpr ?_, mul_zero]
    by_contra! hne
    linarith [(Finset.mem_filter.mp hl).2, Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) ↦
      (hsupp l (i.succAbove s) (hne s (Finset.mem_univ s))).2]
  have hsplit : ∀ u : Fin (r + 1) → ℝ, tensorMarginal cf g i u
      = tensorMarginalHigh cf g
          (Defs.LSet fun l ↦ ∑ s : Fin (r + 1), β l (i.succAbove s) < c) i u
        + tensorMarginalHigh cf g
          (Defs.USet fun l ↦ ∑ s : Fin (r + 1), β l (i.succAbove s) < c) i u :=
    fun u ↦ (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hrestrict : (∫ u in Set.univ.pi fun _ : Fin (r + 1) ↦ Set.Ici (0 : ℝ),
        (tensorMarginal cf g i u ^ 2 - tensorMarginalHigh cf g
          (Defs.USet fun l ↦ ∑ s : Fin (r + 1), β l (i.succAbove s) < c) i u ^ 2))
      = ∫ u in {u : Fin (r + 1) → ℝ | (∀ s, 0 ≤ u s) ∧ ∑ s, u s ≤ c},
        (tensorMarginal cf g i u ^ 2 - tensorMarginalHigh cf g
          (Defs.USet fun l ↦ ∑ s : Fin (r + 1), β l (i.succAbove s) < c) i u ^ 2) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_orthant (r + 1))
      (fun u hu ↦ Set.mem_univ_pi.mpr fun s ↦ hu.1 s) fun u hu ↦ ?_
    have h0 : ∀ s, 0 ≤ u s := fun s ↦ Set.mem_univ_pi.mp hu.1 s
    rw [hsplit u, hlowvan u h0 (not_le.mp fun h ↦ hu.2 ⟨h0, h⟩), zero_add, sub_self]
  rw [formJ_of_tensor cf g i (fun l ↦ ∑ s : Fin (r + 1), β l (i.succAbove s) < c) hgcont hgc,
    hrestrict, integral_sub hΓint (hΨint _),
    setIntegral_tensorMarginal_sq_eq_marginalForm cf g hgcont hgc i c]

/-! ### The `i`-th marginal form is close to `J̃_c(F₀)` -/

/-- **The `i`-th marginal form of the approximation is within `2√σ ε₃ √(J̃_c(F₀)) + σε₃²` of
`J̃_c(F₀)`.**

`Gap212.GPY.abs_sqrt_marginalForm_sub_le` bounds the difference of the *square roots* by
`√σ ‖F_{ε₃} - F₀‖₂ ≤ √σ ε₃` — the `L²` distance being at most `ε₃` because both functions live in
the unit box, whose volume is `1` — and squaring that turns it into a bound on the forms
themselves.
The symmetry of `F₀` is what lets the same `J̃_c(F₀)` appear for every `i`: it is invariant under
the substitution `Gap212.GPY.moveLastTo`. -/
theorem abs_marginalForm_moveLastTo_sub_le {m : ℕ} {σ c ε₃ : ℝ} (hσ : 0 ≤ σ) (hε₃ : 0 ≤ ε₃)
    {F₀ Fε : (Fin (m + 1) → ℝ) → ℝ} (hsy : Symmetric F₀)
    (hcε : Continuous Fε) (hc₀ : Continuous F₀)
    (happ : ∀ v, |F₀ v - Fε v| ≤ ε₃)
    (hbε : ∀ v, Fε v ≠ 0 → ∀ i, v i ∈ Set.Icc (0 : ℝ) 1)
    (hb₀ : ∀ v, F₀ v ≠ 0 → ∀ i, v i ∈ Set.Icc (0 : ℝ) 1)
    (hoffε : ∀ v, Fε v ≠ 0 → (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ σ)
    (hoff₀ : ∀ v, F₀ v ≠ 0 → (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ σ)
    (i : Fin (m + 1)) :
    |marginalForm c (fun v ↦ Fε (moveLastTo i v)) - marginalForm c F₀|
      ≤ 2 * (√σ * ε₃) * √(marginalForm c F₀) + σ * ε₃ ^ 2 := by
  have hGcont : Continuous fun v ↦ Fε (moveLastTo i v) := hcε.comp (continuous_moveLastTo i)
  have hGbox : ∀ v, Fε (moveLastTo i v) ≠ 0 → ∀ j, v j ∈ Set.Icc (0 : ℝ) 1 := fun v hv ↦
    moveLastTo_forall i (hbε _ hv)
  have hGoff : ∀ v, ¬((∀ j, 0 ≤ v j) ∧ ∑ j, v j ≤ σ) → Fε (moveLastTo i v) = 0 := by
    intro v hv
    by_contra h
    obtain ⟨h₁, h₂⟩ := hoffε _ h
    exact hv ⟨moveLastTo_forall i h₁, sum_moveLastTo i v ▸ h₂⟩
  have hF₀off : ∀ v, ¬((∀ j, 0 ≤ v j) ∧ ∑ j, v j ≤ σ) → F₀ v = 0 := fun v ↦
    not_imp_comm.mp (hoff₀ v)
  have hGLp : MemLp (fun v ↦ Fε (moveLastTo i v)) 2 (volume : Measure (Fin (m + 1) → ℝ)) :=
    hGcont.memLp_of_hasCompactSupport (hasCompactSupport_of_box hGbox)
  have hF₀Lp : MemLp F₀ 2 (volume : Measure (Fin (m + 1) → ℝ)) :=
    hc₀.memLp_of_hasCompactSupport (hasCompactSupport_of_box hb₀)
  -- The pointwise distance, where the symmetry of `F₀` is spent.
  have hpt : ∀ v, |Fε (moveLastTo i v) - F₀ v| ≤ ε₃ := by
    intro v
    have h := happ (moveLastTo i v)
    rwa [show F₀ (moveLastTo i v) = F₀ v from congrFun (moveLastTo_of_symmetric hsy i) v,
      abs_sub_comm] at h
  -- The `L²` distance is at most `ε₃`, the unit box having volume one.
  have hdiffbox : ∀ v : Fin (m + 1) → ℝ, Fε (moveLastTo i v) - F₀ v ≠ 0 →
      ∀ j, v j ∈ Set.Icc (0 : ℝ) 1 := by
    intro v hv j
    by_cases h₁ : Fε (moveLastTo i v) = 0
    · exact hb₀ v (by rwa [h₁, zero_sub, neg_ne_zero] at hv) j
    · exact hGbox v h₁ j
  have hL2 : (∫ v, (Fε (moveLastTo i v) - F₀ v) ^ 2) ≤ ε₃ ^ 2 := by
    rw [← setIntegral_univ, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
      (Set.subset_univ (Set.univ.pi fun _ : Fin (m + 1) ↦ Set.Icc (0 : ℝ) 1)) fun v hv ↦
        by_contra fun h ↦ hv.2 (Set.mem_univ_pi.mpr (hdiffbox v (ne_zero_of_sq_ne_zero h)))]
    have hb := norm_setIntegral_le_of_norm_le_const
      ((isCompact_univ_pi fun _ ↦ isCompact_Icc).measure_lt_top (μ := volume))
      fun v (_ : v ∈ Set.univ.pi fun _ : Fin (m + 1) ↦ Set.Icc (0 : ℝ) 1) ↦ norm_sq_le_sq (hpt v)
    rw [volumeReal_unitBox, mul_one] at hb
    exact (le_abs_self _).trans hb
  -- Squaring the Lipschitz bound.
  have hD : |√(marginalForm c fun v ↦ Fε (moveLastTo i v)) - √(marginalForm c F₀)|
      ≤ √σ * ε₃ :=
    (abs_sqrt_marginalForm_sub_le hσ c hGLp hF₀Lp hGoff hF₀off).trans
      (mul_le_mul_of_nonneg_left ((Real.sqrt_le_sqrt hL2).trans_eq (Real.sqrt_sq hε₃))
        (Real.sqrt_nonneg σ))
  have hkey := abs_sq_sub_sq_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (by positivity) hD
  rwa [Real.sq_sqrt (marginalForm_nonneg _ _), Real.sq_sqrt (marginalForm_nonneg _ _), mul_pow,
    Real.sq_sqrt hσ] at hkey

/-! ### The Gram data of a tail datum -/

/-- The boundary values of a datum whose factors are tails are the total masses of the `g`'s. -/
theorem gramBdry_tailTransform {L k : ℕ} (g : Fin L → Fin k → ℝ → ℝ) (i : Fin k) :
    Sieve.gramBdry (fun l i ↦ tailTransform (g l i)) i = fun l ↦ tailTransform (g l i) 0 := rfl

/-- The skipped Gram data of a datum whose factors are tails. -/
theorem gramInnerSkip_tailTransform {L m : ℕ} (g : Fin L → Fin (m + 1) → ℝ → ℝ)
    (i : Fin (m + 1)) :
    Sieve.gramInnerSkip (fun l i ↦ tailTransform (g l i)) i
      = fun l l' s ↦ ∫ t in Set.Ioi (0 : ℝ),
          deriv (tailTransform (g l (i.succAbove s))) t *
            deriv (tailTransform (g l' (i.succAbove s))) t := rfl

/-! ### The transfer -/

/-- **The tensor mesh transfers the gap**, with the cutoff `c` and the total-mass bound `σ` carried
as data rather than read off the datum.

The whole argument happens here. `Gap212.Sieve.exists_tensor_partition_approx` supplies the mesh at
an accuracy `ε₃` still to be chosen; the tails of its factors are the tensor datum, whose support
lands in the retreat region because each box corner is within `ε₃` of the buffered region
(`Gap212.GPY.mem_retreatRegion_of_mem_bufferedRegion`) and the boxes hang below their corners
(`Gap212.GPY.retreatRegion_downward_closed`); `Gap212.GPY.formI_of_tensor` and
`Gap212.GPY.formJ_of_tensor` turn the two
discrete forms into integrals, `Gap212.GPY.setIntegral_tensorMarginalHigh_sq_le` discards the high
part, and `Gap212.GPY.abs_sqrt_marginalForm_sub_le` with the symmetry of `F₀` identifies all `k`
numerators in the limit.
The mesh is then chosen once, by `Gap212.GPY.exists_mesh_quadratic`, against an explicit modulus in
`(F₀, ζ₁)`.

The natural reading is `σ = 1`. Any bound on the total mass over the retreat region does, which is
what this takes. -/
theorem exists_tensorDatum_forms_gap_aux {p : SupportParams} {r : ℕ} {j : Fin p.n}
    {ε₀ ζ₁ κ c σ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) (hζ₁ : 0 < ζ₁) (hκ : 0 < κ)
    (hmesh : 2 * ((r + 2 : ℕ) : ℝ) * ζ₁ ≤ κ) (hc0 : 0 ≤ c) (hσ0 : 0 ≤ σ)
    {F₀ : (Fin (r + 2) → ℝ) → ℝ}
    (hsm : ContDiff ℝ (⊤ : ℕ∞) F₀) (hnn : ∀ t, 0 ≤ F₀ t) (hsy : Symmetric F₀)
    (hcs : HasCompactSupport F₀)
    (hoff : ∀ t, t ∉ bufferedRegion p (r + 2) j ε₀ ζ₁ κ → F₀ t = 0)
    (hretσ : ∀ t : Fin (r + 2) → ℝ, t ∈ retreatRegion p (r + 2) j ε₀ → ∑ i, t i ≤ σ)
    (hF₀T : ∀ t, t ∉ T p (r + 2) → F₀ t = 0)
    (hI : 0 < Iint p (r + 2) F₀)
    (hgap : Iint p (r + 2) F₀ < ((r + 2 : ℕ) : ℝ) * marginalForm c F₀) :
    ∃ (D : TensorDatum p (r + 2) j ε₀) (𝓛 𝓤 : Fin (r + 2) → Finset (Fin D.L)),
      (∀ i, 𝓤 i = (𝓛 i)ᶜ) ∧
      (∀ i : Fin (r + 2), ∀ l ∈ 𝓛 i, ∀ t : Fin (r + 1) → ℝ, (∀ s, 0 ≤ t s) →
        (∏ s, D.f l (i.succAbove s) (t s)) ≠ 0 → ∑ s, t s < c) ∧
      (∀ l, 0 ≤ D.c l) ∧
      0 < Defs.formI D.c (Sieve.gramInner D.f) ∧
      Defs.formI D.c (Sieve.gramInner D.f) <
        ∑ i, Defs.formJMarginal D.c (Sieve.gramBdry D.f i) (Sieve.gramInnerSkip D.f i)
          (𝓛 i) (𝓤 i) := by
  have hkζ : ((r + 2 : ℕ) : ℝ) * ζ₁ ≤ κ := by nlinarith
  -- The sup norm of `F₀`, and where it may be non-zero.
  obtain ⟨M₀, hM₀'⟩ := hcs.exists_bound_of_continuous hsm.continuous
  have hM₀ : ∀ v, |F₀ v| ≤ M₀ := fun v ↦ by simpa [Real.norm_eq_abs] using hM₀' v
  have hM₀0 : 0 ≤ M₀ := le_trans (abs_nonneg _) (hM₀ 0)
  have hF₀ret : ∀ t, F₀ t ≠ 0 → t ∈ retreatRegion p (r + 2) j ε₀ := fun t ht ↦
    bufferedRegion_subset_retreatRegion hε₀ hε₀'.le hζ₁ hκ hkζ
      (Function.support_subset_iff'.mpr hoff ht)
  have hF₀box : ∀ t, F₀ t ≠ 0 → ∀ i, t i ∈ Set.Icc (0 : ℝ) 1 := fun t ht i ↦ (hF₀ret t ht).1 i
  have hF₀off : ∀ t, F₀ t ≠ 0 → (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ σ := fun t ht ↦
    ⟨fun i ↦ ((hF₀ret t ht).1 i).1, hretσ t (hF₀ret t ht)⟩
  -- Compact support inside the open orthant, which the mesh approximation asks for, is implied:
  -- the buffered region sits in `[ζ₁, ∞)^k`, a closed set, so the *closure* of the support does
  -- too.
  have horth : tsupport F₀ ⊆ {t : Fin (r + 2) → ℝ | ∀ i, 0 < t i} := by
    have hsub : tsupport F₀ ⊆ Set.univ.pi fun _ ↦ Set.Ici ζ₁ :=
      closure_minimal (fun t ht ↦ Set.mem_univ_pi.mpr fun i ↦
        ((Function.support_subset_iff'.mpr hoff ht).1 i).1) (isClosed_set_pi fun _ _ ↦ isClosed_Ici)
    exact fun t ht i ↦ hζ₁.trans_le (Set.mem_univ_pi.mp (hsub ht) i)
  -- The strip constant, kept opaque so the mesh inequalities stay polynomial in it.
  obtain ⟨C₁, hC₁def⟩ : ∃ x : ℝ, x = ((r : ℝ) + 1) * c ^ r / (r ! : ℝ) * (M₀ + 1) ^ 2 := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁def]
    exact mul_nonneg (div_nonneg (mul_nonneg (by positivity) (pow_nonneg hc0 r))
      (Nat.cast_nonneg _)) (by positivity)
  -- The mesh, chosen once against an explicit modulus.
  obtain ⟨ε₃, hε₃0, hε₃ζ, hε₃1, hquad⟩ := exists_mesh_quadratic
    (P := 2 * M₀ + ((r + 2 : ℕ) : ℝ) * (C₁ + 2 * √σ * √(marginalForm c F₀)))
    (Q := 1 + ((r + 2 : ℕ) : ℝ) * σ)
    (ρ := min ((((r + 2 : ℕ) : ℝ) * marginalForm c F₀ - Iint p (r + 2) F₀) / 8)
      (Iint p (r + 2) F₀ / 2)) (B := ζ₁)
    (by positivity) (by positivity) (lt_min (by linarith) (by linarith)) hζ₁
  have hP₂0 : 0 ≤ ((r + 2 : ℕ) : ℝ) * (C₁ + 2 * √σ * √(marginalForm c F₀)) := by positivity
  have hQ₂0 : 0 ≤ ((r + 2 : ℕ) : ℝ) * σ := by positivity
  have hAbound : ε₃ * (2 * M₀ + ε₃ * 1)
      < min ((((r + 2 : ℕ) : ℝ) * marginalForm c F₀ - Iint p (r + 2) F₀) / 8)
        (Iint p (r + 2) F₀ / 2) := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ hε₃0.le) hquad
    linarith [mul_nonneg hε₃0.le hQ₂0]
  have hBbound : ε₃ * (((r + 2 : ℕ) : ℝ) * (C₁ + 2 * √σ * √(marginalForm c F₀))
        + ε₃ * (((r + 2 : ℕ) : ℝ) * σ))
      < (((r + 2 : ℕ) : ℝ) * marginalForm c F₀ - Iint p (r + 2) F₀) / 8 := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ hε₃0.le)
      (lt_of_lt_of_le hquad (min_le_left _ _))
    linarith
  -- The mesh data.
  obtain ⟨L, cf, g, α, β, hcfnn, hgnn, hgsm, hgsupp, hglen, hαpos, hboxmeet, hnbhd, happrox⟩ :=
    Sieve.exists_tensor_partition_approx (k := r + 2) (by omega) hsm hnn hcs horth hε₃0
  have hgcont : ∀ l s, Continuous (g l s) := fun l s ↦ (hgsm l s).continuous
  have hgc : ∀ l s, HasCompactSupport (g l s) := fun l s ↦
    IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
      (closure_minimal (hgsupp l s) isClosed_Icc)
  have hαβ : ∀ l i, α l i ≤ β l i := fun l i ↦ by
    obtain ⟨s, -, hs⟩ := hboxmeet l
    exact (hs i).1.trans (hs i).2
  have hkκ : ((r + 2 : ℕ) : ℝ) * (ζ₁ + ε₃) ≤ κ := by nlinarith
  have hcorner : ∀ l, (fun i ↦ β l i) ∈ retreatRegion p (r + 2) j ε₀ := fun l ↦
    mem_retreatRegion_of_mem_box hε₀ hε₀'.le hζ₁ hκ hε₃ζ hkκ hoff (hnbhd l)
      fun i ↦ ⟨hαβ l i, le_rfl⟩
  have hβ01 : ∀ l i, β l i ≤ 1 := fun l i ↦ ((hcorner l).1 i).2
  -- The datum's two support clauses.
  have hcompB : ∀ (l : Fin L) (i : Fin (r + 2)) (t : ℝ), (1 : ℝ) < t →
      tailTransform (g l i) t = 0 := by
    intro l i t ht
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
    by_contra h
    linarith [(hgsupp l i h).2, hβ01 l i, Set.mem_Ioi.mp hx]
  have hsuppD : ∀ (l : Fin L) (t : Fin (r + 2) → ℝ), (∀ i, 0 ≤ t i) →
      (∏ i, tailTransform (g l i) (t i)) ≠ 0 → t ∈ retreatRegion p (r + 2) j ε₀ := by
    intro l t ht0 hne
    refine retreatRegion_downward_closed hε₀.le hε₀'.le (hcorner l) fun i ↦ ⟨ht0 i, ?_⟩
    by_contra hlt
    exact hne (prod_tailTransform_eq_zero (fun i x hx ↦ (hgsupp l i hx).2) (not_le.mp hlt))
  -- Where the tensor sum can be non-zero, and how big it is.
  have hFεret : ∀ v, tensorSum cf g v ≠ 0 → v ∈ retreatRegion p (r + 2) j ε₀ := by
    intro v hv
    obtain ⟨l, hl⟩ := exists_box_of_tensorSum_ne_zero hgsupp hv
    exact mem_retreatRegion_of_mem_box hε₀ hε₀'.le hζ₁ hκ hε₃ζ hkκ hoff (hnbhd l) hl
  have hFεbox : ∀ v, tensorSum cf g v ≠ 0 → ∀ i, v i ∈ Set.Icc (0 : ℝ) 1 :=
    fun v hv i ↦ (hFεret v hv).1 i
  have hFεoff : ∀ v, tensorSum cf g v ≠ 0 → (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ σ := fun v hv ↦
    ⟨fun i ↦ ((hFεret v hv).1 i).1, hretσ v (hFεret v hv)⟩
  have hFεcont : Continuous (tensorSum cf g) := by
    unfold tensorSum
    fun_prop
  have happ : ∀ v, |F₀ v - tensorSum cf g v| ≤ ε₃ := happrox
  have hFεM : ∀ v, |tensorSum cf g v| ≤ M₀ + ε₃ := fun v ↦ by
    linarith [hM₀ v, happ v, abs_sub_comm (F₀ v) (tensorSum cf g v),
      abs_sub_abs_le_abs_sub (tensorSum cf g v) (F₀ v)]
  -- A uniform bound on the marginals.
  have hΓM : ∀ (i : Fin (r + 2)) (u : Fin (r + 1) → ℝ), |tensorMarginal cf g i u| ≤ M₀ + 1 := by
    intro i u
    rw [← tensorMarginal_eq_fibreIntegral cf g hgcont hgc i u,
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        Set.Ioc_subset_Ioi_self fun t ht ↦ by_contra fun h ↦
          ht.2 ⟨ht.1, by simpa using (hFεbox _ h i).2⟩, ← Real.norm_eq_abs]
    have hb := norm_setIntegral_le_of_norm_le_const (measure_Ioc_lt_top (μ := volume))
      fun t (_ : t ∈ Set.Ioc (0 : ℝ) 1) ↦ (Real.norm_eq_abs _).trans_le (hFεM (i.insertNth t u))
    simp only [Real.volume_real_Ioc_of_le zero_le_one, sub_zero, mul_one] at hb
    linarith
  -- The denominator.
  have hformI : Defs.formI cf (Sieve.gramInner fun l i ↦ tailTransform (g l i))
      = ∫ t in Set.univ.pi fun _ : Fin (r + 2) ↦ Set.Ici (0 : ℝ), tensorSum cf g t ^ 2 :=
    formI_of_tensor cf g hgcont hgc
  have hIclose : |(∫ t in Set.univ.pi fun _ : Fin (r + 2) ↦ Set.Ici (0 : ℝ), tensorSum cf g t ^ 2)
      - Iint p (r + 2) F₀| ≤ ε₃ * (2 * M₀ + ε₃) := by
    have h := abs_setIntegral_sq_sub_Iint_le (p := p) hε₃0.le hFεcont hsm.continuous hM₀ happ
      hFεbox hF₀box hF₀T
    rwa [volumeReal_unitBox, mul_one] at h
  obtain ⟨hI₁, hI₂⟩ := abs_le.mp hIclose
  have hAmin1 := lt_of_lt_of_le hAbound (min_le_left _ _)
  have hAmin2 := lt_of_lt_of_le hAbound (min_le_right _ _)
  -- The numerators.
  have hJlower : ∀ i : Fin (r + 2),
      marginalForm c F₀
          - (2 * √σ * √(marginalForm c F₀) * ε₃ + σ * ε₃ ^ 2 + C₁ * ε₃)
        ≤ Defs.formJMarginal cf (fun l ↦ tailTransform (g l i) 0)
            (fun l l' s ↦ ∫ t in Set.Ioi (0 : ℝ),
              deriv (tailTransform (g l (i.succAbove s))) t *
                deriv (tailTransform (g l' (i.succAbove s))) t)
            (Defs.LSet fun l ↦ ∑ s : Fin (r + 1), β l (i.succAbove s) < c)
            (Defs.USet fun l ↦ ∑ s : Fin (r + 1), β l (i.succAbove s) < c) := by
    intro i
    obtain ⟨A, hA0, hA1, hAeq⟩ := formJMarginal_tensor_eq_sub hc0 hε₃0.le hcfnn hgnn hgcont hgc
      hgsupp hglen i (hΓM i)
    have hA2 : A ≤ C₁ * ε₃ := hA1.trans_eq (by rw [hC₁def]; ring)
    have hcl := abs_le.mp (abs_marginalForm_moveLastTo_sub_le (σ := σ) (c := c) hσ0 hε₃0.le hsy
      hFεcont hsm.continuous happ hFεbox hF₀box hFεoff hF₀off i)
    rw [hAeq]
    linarith [hcl.1]
  have hsum : ((r + 2 : ℕ) : ℝ) * (marginalForm c F₀
        - (2 * √σ * √(marginalForm c F₀) * ε₃ + σ * ε₃ ^ 2 + C₁ * ε₃))
      ≤ ∑ i : Fin (r + 2), Defs.formJMarginal cf (fun l ↦ tailTransform (g l i) 0)
          (fun l l' s ↦ ∫ t in Set.Ioi (0 : ℝ),
            deriv (tailTransform (g l (i.succAbove s))) t *
              deriv (tailTransform (g l' (i.succAbove s))) t)
          (Defs.LSet fun l ↦ ∑ s : Fin (r + 1), β l (i.succAbove s) < c)
          (Defs.USet fun l ↦ ∑ s : Fin (r + 1), β l (i.succAbove s) < c) := by
    have h := Finset.card_nsmul_le_sum Finset.univ _ _ fun i _ ↦ hJlower i
    rwa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  refine ⟨⟨L, cf, fun l i ↦ tailTransform (g l i),
      fun l i ↦ (contDiff_tailTransform (hgsm l i) (hgc l i)).1, ⟨1, hcompB⟩, hsuppD⟩, ?_⟩
  dsimp only
  refine ⟨fun i ↦ Defs.LSet fun l ↦ ∑ s : Fin (r + 1), β l (i.succAbove s) < c,
    fun i ↦ Defs.USet fun l ↦ ∑ s : Fin (r + 1), β l (i.succAbove s) < c,
    fun i ↦ Defs.USet_eq_compl _, ?_, hcfnn, ?_, ?_⟩
  · -- `𝓛`-membership bounds the marginal: the tail factors die above their endpoints, and the
    -- endpoint sum is below the cutoff by the definition of `Gap212.Defs.LSet`.
    intro i l hl t ht0 hne
    refine (Finset.sum_le_sum fun s _ ↦ ?_).trans_lt (Finset.mem_filter.mp hl).2
    by_contra hlt
    exact hne (prod_tailTransform_eq_zero
      (fun s' x hx ↦ (hgsupp l (i.succAbove s') hx).2) (not_le.mp hlt))
  · rw [hformI]
    linarith
  · rw [hformI]
    simp only [gramBdry_tailTransform, gramInnerSkip_tailTransform]
    linarith

/-- **The tensor mesh transfers the gap.**

For a support datum `p`, a smooth non-negative symmetric `F₀` compactly supported in `(0,∞)^k`
vanishing off the buffered region `R⁺⁺_k(1, ε₀, ζ₁, κ)`, with the variational gap
`0 < I_T(F₀) < k J̃_{(1-ε₀)(A₁-ε)}(F₀)` — there is a tensor datum at level `ε₀` for the band `1`,
with non-negative coefficients, whose discrete forms satisfy `0 < 𝓘 < ∑_{i ≤ k} 𝓙ᵢ`.

Two readings the statement makes explicit. `k ≥ 2` is written `k = r + 2`, which is what
`Gap212.GPY.setIntegral_tensorMarginalHigh_sq_le` is stated at. And the index sets `𝓛ᵢ`, `𝓤ᵢ` are
part of what is produced: `𝓙ᵢ` is a function of them (`Gap212.Defs.formJMarginal`), so a datum
alone does not determine the numerator; the ones produced here are the low/high split at the
endpoint sums.

**Two properties of that split are produced as well, and the numerator cannot do without them.**
The first is `𝓤ᵢ = 𝓛ᵢᶜ` (`Gap212.Defs.USet_eq_compl`). The second is what `Gap212.Defs.LSet` is
for: a low term's `i`-omitted marginal
is supported in `M⁻_k(j,i,ε₀)`, because the factors are tails vanishing above their endpoints
`β_{l,s}` and `𝓛ᵢ` puts `∑_{s≠i} β_{l,s}` below `(1-ε₀)(A_{j+1} - ε)`, which is exactly
`Gap212.GPY.marginalRegion`'s cutoff. The sieve asymptotic carries that containment as a hypothesis
and nothing derives it from retreat membership, so the numerator asymptotic discharges it from
`𝓛`-membership — and could not, were the two index sets returned with no property
attached.

"Compactly supported in `(0,∞)^k`" is *not* a hypothesis here, only compact
support: `R⁺⁺_k(1, ε₀, ζ₁, κ)` confines its coordinates to `[ζ₁, 1 - κ]`, a closed set, so
vanishing off it already puts `tsupport F₀` inside the open orthant. This matters because
`Gap212.GPY.exists_retreat_gap` does not produce the orthant clause, and asking
for it would make this statement inapplicable to the `F₀` the retreat actually returns.

`p.n = 1`, `ζ₁ ≤ δ/2` and `κ ≤ 1/2` are **not** hypotheses here. The proof needs
only `2kζ₁ ≤ κ` from the numerical data and works at the bottom band of any `p`, so this states
the stronger result, which implies the one-band form a fortiori. -/
@[gap212 "lem_tensor_gap_transfer"]
theorem exists_tensorDatum_forms_gap {p : SupportParams} {r : ℕ} {ε₀ ζ₁ κ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) (hζ₁ : 0 < ζ₁) (hκ : 0 < κ)
    (hmesh : 2 * ((r + 2 : ℕ) : ℝ) * ζ₁ ≤ κ)
    {F₀ : (Fin (r + 2) → ℝ) → ℝ}
    (hsm : ContDiff ℝ (⊤ : ℕ∞) F₀) (hnn : ∀ t, 0 ≤ F₀ t) (hsy : Symmetric F₀)
    (hcs : HasCompactSupport F₀)
    (hoff : ∀ t, t ∉ bufferedRegion p (r + 2) ⟨0, p.n_pos⟩ ε₀ ζ₁ κ → F₀ t = 0)
    (hI : 0 < Iint p (r + 2) F₀)
    (hgap : Iint p (r + 2) F₀ < ((r + 2 : ℕ) : ℝ) *
      marginalForm ((1 - ε₀) * (p.A (⟨0, p.n_pos⟩ : Fin p.n).succ - p.ε)) F₀) :
    ∃ (D : TensorDatum p (r + 2) ⟨0, p.n_pos⟩ ε₀) (𝓛 𝓤 : Fin (r + 2) → Finset (Fin D.L)),
      (∀ i, 𝓤 i = (𝓛 i)ᶜ) ∧
      (∀ i : Fin (r + 2), ∀ l ∈ 𝓛 i, ∀ t : Fin (r + 1) → ℝ, (∀ s, 0 ≤ t s) →
        (∏ s, D.f l (i.succAbove s) (t s)) ≠ 0 →
          t ∈ marginalRegion p (r + 1) ⟨0, p.n_pos⟩ ε₀) ∧
      (∀ l, 0 ≤ D.c l) ∧
      0 < Defs.formI D.c (Sieve.gramInner D.f) ∧
      Defs.formI D.c (Sieve.gramInner D.f) <
        ∑ i, Defs.formJMarginal D.c (Sieve.gramBdry D.f i) (Sieve.gramInnerSkip D.f i)
          (𝓛 i) (𝓤 i) := by
  have hkζ : ((r + 2 : ℕ) : ℝ) * ζ₁ ≤ κ := by nlinarith
  -- The bottom band's upper node is above the origin, so the total-mass bound is non-negative.
  have hAeps : 0 < p.A (⟨0, p.n_pos⟩ : Fin p.n).succ + p.ε := by
    linarith [p.A_mono (Fin.succ_pos (⟨0, p.n_pos⟩ : Fin p.n)), p.A_zero]
  have hF₀T : ∀ t, t ∉ T p (r + 2) → F₀ t = 0 := Function.support_subset_iff'.mp
    (((Function.support_subset_iff'.mpr hoff).trans
      (bufferedRegion_subset_retreatRegion hε₀ hε₀'.le hζ₁ hκ hkζ)).trans
      (retreatRegion_subset_T hε₀.le hε₀'.le))
  -- The cutoff is non-negative: below the origin the marginal form vanishes and the gap fails.
  have hc0 : 0 ≤ (1 - ε₀) * (p.A (⟨0, p.n_pos⟩ : Fin p.n).succ - p.ε) := by
    by_contra! hneg
    simp only [marginalForm, cornerSimplex_eq_empty (r + 1) hneg, setIntegral_empty,
      mul_zero] at hgap
    linarith
  -- The aux's cutoff is `(1 - ε₀)(A₁ - ε)`, which is what `marginalRegion` asks for.
  exact exists_tensorDatum_forms_gap_aux hε₀ hε₀' hζ₁ hκ hmesh hc0
    (mul_pos (by linarith) hAeps).le hsm hnn hsy hcs hoff (fun _ ht ↦ ht.2.1.le) hF₀T hI hgap

end Gap212.GPY
