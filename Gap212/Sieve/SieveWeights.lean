/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.RetreatGap
public import Gap212.Sieve.TensorMesh
public import Gap212.Sieve.JintMarginal
public meta import Gap212.Attr

/-!
# The sieve weights realize the variational inequality

`Gap212.Sieve.SieveWeights` (`Gap212/Sieve/Asymptotics.lean`) is a theorem, and this module is
its proof: the composition of the two results beneath it.

## The composition

The proof is two steps and one reconciliation.

* `Gap212.GPY.exists_retreat_gap` takes the certificate's `F` with the
  variational gap at cutoff `A₁ - ε` and returns a smooth non-negative symmetric compactly
  supported `F₀`, vanishing off the buffered region, with the gap at the retreated cutoff
  `(1 - ε₀)(A₁ - ε)`.
* `Gap212.GPY.exists_tensorDatum_forms_gap` takes exactly such an
  `F₀` and returns the finite tensor datum whose discrete forms satisfy `0 < 𝓘 < ∑ᵢ 𝓙ᵢ`.

The two meet with nothing between them. `Gap212.GPY.HasVariationalGap p m c G` unfolds to
`0 < I_T(G) ∧ I_T(G) < (m+1) J̃_c(G)`, which is literally the pair of numeric hypotheses the tensor
step asks for, so `hgap₀.1` and `hgap₀.2` are passed straight through; and the two support clauses
are contrapositives of each other, the retreat producing `F₀ t ≠ 0 → t ∈ R⁺⁺` and the mesh asking
for `t ∉ R⁺⁺ → F₀ t = 0`. The mesh constants are the retreat's own: `κ = aδ/(200k)` and
`ζ₁ = κ/(2k)`, which give `2kζ₁ = κ` exactly, and `ζ₁ ≤ δ/2`, `κ ≤ 1/2` from `a < 1/2` and
`δ = 41/2500`. The level is `ε₀ = a/100`, read off `Gap212.GPY.retreatData`, so `0 < ε₀ < 1/200`.

## From the certificate to the variational gap

`Gap212.Certificate p m 0 0` is not stated in terms of the variational gap, and two small facts
carry it there.

* `Gap212.Sieve.memLp_volume_of_memLp_restrict`. The certificate gives
  `MemLp F 2 (volume.restrict (T p k))`, while the retreat and `Gap212.GPY.jint_eq_marginalForm`
  ask for
  `MemLp F 2 volume`. Since `F` vanishes off `T p k` *pointwise*, `F` is its own indicator on
  `T p k`, and `MeasureTheory.memLp_indicator_iff_restrict` at the measurable `T p k` turns one
  into the other. Nothing is lost in either direction; the restricted form is simply the
  weaker-looking one of two equivalent statements here.
* `Gap212.Sieve.last_eq_succ_zero`. `Gap212.GPY.jint_eq_marginalForm` states the cutoff as
  `p.A (Fin.last p.n) - p.ε`; `Gap212.GPY.exists_retreat_gap` states it as
  `p.A ⟨0, p.n_pos⟩.succ - p.ε`. At `p.n = 1` both indices are `⟨1, _⟩ : Fin (p.n + 1)`.

With those, `Jint gap212Params 44 F = J̃_{A₁-ε}(F)` and the certificate's
`I_T(F) < 45(1-0) J_T(F) - 45·0·K_T(F)` is the gap at that cutoff, `c₂ = 0` removing `K_T`.

## Main results

* `Gap212.Sieve.sieveWeights`: the sieve weights realize the variational inequality.
-/

@[expose] public section

namespace Gap212.Sieve

open MeasureTheory Gap212.Defs Gap212.GPY

/-! ## The two reconciliations -/

/-- **A function vanishing off `T_k(p)` is in `L²` of the whole space as soon as it is in `L²` of
the support.** It equals its own indicator on `T_k(p)`, so
`MeasureTheory.memLp_indicator_iff_restrict` applies at the measurable set `T_k(p)`.

`Gap212.Certificate` states square-integrability against `volume.restrict (T p (m+1))`;
`Gap212.GPY.exists_retreat_gap` and `Gap212.GPY.jint_eq_marginalForm` both ask for it against
`volume`. Under the vanishing clause the two are the same assertion. -/
theorem memLp_volume_of_memLp_restrict {p : SupportParams} {k : ℕ} {F : (Fin k → ℝ) → ℝ}
    (hF : MemLp F 2 (volume.restrict (T p k))) (hoff : ∀ t, t ∉ T p k → F t = 0) :
    MemLp F 2 (volume : Measure (Fin k → ℝ)) := by
  have hind : (T p k).indicator F = F :=
    Set.indicator_eq_self.mpr (Function.support_subset_iff'.2 hoff)
  exact hind ▸ (memLp_indicator_iff_restrict (measurableSet_T p k)).mpr hF

/-- **At a one-band datum the last node and the bottom band's upper node are the same index.**
`Fin.last p.n` has value `p.n` and `(⟨0, p.n_pos⟩ : Fin p.n).succ` has value `1`, so at `p.n = 1`
they agree. This is the only difference between the cutoff `Gap212.GPY.jint_eq_marginalForm`
produces and the one `Gap212.GPY.exists_retreat_gap` consumes. -/
theorem last_eq_succ_zero {p : SupportParams} (hn : p.n = 1) :
    Fin.last p.n = (⟨0, p.n_pos⟩ : Fin p.n).succ := by
  ext
  simp [hn]

/-! ## The theorem -/

/-- **The sieve weights realize the variational inequality.**

The certificate's `F` is fed to `Gap212.GPY.exists_retreat_gap` and the resulting `F₀` to
`Gap212.GPY.exists_tensorDatum_forms_gap`.

The statement is `Gap212.Sieve.SieveWeights`, at `p = p_⋆` and `k = 45`. -/
@[gap212 "lem_sieveweights"]
theorem sieveWeights : SieveWeights := by
  rintro ⟨F, hsymm, hmem, hoff, hIpos, hIlt⟩
  have hn : gap212Params.n = 1 := rfl
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  have hFvol : MemLp F 2 (volume : Measure (Fin 45 → ℝ)) :=
    memLp_volume_of_memLp_restrict hmem hoff
  -- The one-band collapse of `J_T`, at the index spelling the retreat uses.
  have hJ : Jint gap212Params 44 F
      = marginalForm (gap212Params.A (⟨0, gap212Params.n_pos⟩ : Fin gap212Params.n).succ
          - gap212Params.ε) F := by
    rw [jint_eq_marginalForm hn hFvol hoff, last_eq_succ_zero hn]
  have hgap : HasVariationalGap gap212Params 44
      (gap212Params.A (⟨0, gap212Params.n_pos⟩ : Fin gap212Params.n).succ - gap212Params.ε) F := by
    refine ⟨hIpos, ?_⟩
    rw [← hJ]
    push_cast at hIlt ⊢
    linarith
  -- The retreat, and the level `ε₀ = a/100` it fixes.
  obtain ⟨a, b₀, ε₀, ζ, ϱ, κ, ζ₁, ha, ha', hrd, hκdef, hζ₁def, F₀,
    hsy, hnn, hsm, hcs, hbuf, hgap₀⟩ := exists_retreat_gap hsymm hFvol hoff hgap
  simp only [retreatData, Prod.mk.injEq] at hrd
  obtain ⟨-, hε₀eq, -, -⟩ := hrd
  have hε₀ : 0 < ε₀ := by rw [← hε₀eq]; linarith
  have hε₀' : ε₀ < 1 := by rw [← hε₀eq]; linarith
  -- The mesh constants are the retreat's own, and `2kζ₁ = κ` holds with equality.
  have hκ : 0 < κ := by rw [hκdef, hδ]; positivity
  have hζ₁ : 0 < ζ₁ := by rw [hζ₁def]; positivity
  have hmesh : 2 * ((43 + 2 : ℕ) : ℝ) * ζ₁ ≤ κ := by rw [hζ₁def]; push_cast; linarith
  -- The support clauses are contrapositives of each other.
  have hoff₀ : ∀ t, t ∉ bufferedRegion gap212Params (43 + 2)
      (⟨0, gap212Params.n_pos⟩ : Fin gap212Params.n) ε₀ ζ₁ κ → F₀ t = 0 :=
    fun t ↦ not_imp_comm.1 (hbuf t)
  exact ⟨ε₀, hε₀, hε₀',
    exists_tensorDatum_forms_gap (p := gap212Params) (r := 43) hε₀ hε₀' hζ₁ hκ
      hmesh hsm hnn hsy hcs hoff₀ hgap₀.1 hgap₀.2⟩

end Gap212.Sieve
