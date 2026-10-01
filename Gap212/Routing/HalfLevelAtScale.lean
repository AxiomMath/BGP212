/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Challenge.Pairing
public import Gap212.Consequences.PointwiseFromEventual
public import Gap212.Inputs.BVRangeAtScale
public import Gap212.Routing.HarmanAtScale
public import Gap212.Routing.RangeCompare
public meta import Gap212.Attr

/-!
# Half-level coverage: the two ranges, and the bounded range below them

The routes reach the generated moduli above `x^{1/2-ε₁}` and bilinear Bombieri–Vinogradov reaches
those up to `x^{1/2}(log x)^{-B}`. The two overlap once `(log x)^B ≤ x^{ε₁}`, which is
`Gap212.Routing.exists_threshold_ranges_compare`, and below that threshold the moduli in between
are absorbed into the constant by `Gap212.hasEquidistribution_of_forall_ge`.

## What the absorption needs of the member

A coefficient bound, a support window and `f 0 = 0` — of `f` itself, not of its factors. A member
of the Harman class is a two- or fourfold Dirichlet convolution, so the bound and the window come
from iterating `Gap212.isCoefficientSequence_and_locatedAtScale_dconv`, which lands at the
convolution bundle `Ψ K`; a twofold member lands at `Ψ K` and is carried up two steps, a fourfold
one at `Ψ(Ψ(Ψ K))` directly. Iterating `Ψ` needs the bundle normalized, which is what `K♭` is for,
so the facts are extracted at `K♭` — they are facts about `f` alone, so the bundle they are read at
does not matter to the two range bounds, which are taken at `K`.

The three smooth factors of a Type III member declare only smoothness, and location is recovered
from it: the profile vanishes off `[c₋, c₊]`, so a nonzero term has `n/N` in that interval.

## Main results

* `Gap212.halfLevelCoverage_of_conditionD`: half-level arithmetic coverage, from
  Condition D at the datum. Its statement is `Gap212.HarmanClassEquidistributes`, quantifier for
  quantifier.
* `Gap212.routingObligation_of_conditionD`: hence `Gap212.RoutingObligation`, from the same one
  hypothesis.
-/

@[expose] public section

namespace Gap212.HalfLevel

open Real Finset

/-! ## The four clauses are monotone in their constants

These are the facts `Gap212.Inputs.BVRangeAtScale` keeps private; they are re-derived here
because the absorption step needs them outside that file. -/

/-- The coefficient bound is monotone in its three constants, at `n ≥ 1`. -/
theorem isCoefficientSequence_mono {C C' : ℝ} {k k' l l' : ℕ} {α : ℕ → ℂ} (hC : 0 ≤ C)
    (hCC : C ≤ C') (hk : k ≤ k') (hl : l ≤ l') (h : IsCoefficientSequence C k l α) :
    IsCoefficientSequence C' k' l' α := by
  intro n hn
  have hτ : (1 : ℝ) ≤ n.divisors.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨n, Nat.mem_divisors_self n (by omega)⟩
  have hL : (1 : ℝ) ≤ 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
  have hC' := hC.trans hCC
  exact (h n hn).trans (by gcongr)

/-- Widening the support window preserves location. -/
theorem locatedAtScale_mono {c₀ c₁ c₀' c₁' : ℝ} {α : ℕ → ℂ} {N : ℝ} (hc₁ : 0 < c₁)
    (h₀ : c₀' ≤ c₀) (h₁ : c₁ ≤ c₁') (h : LocatedAtScale c₀ c₁ α N) :
    LocatedAtScale c₀' c₁' α N := by
  intro n hn hne
  have hN : (0 : ℝ) ≤ N := (pos_of_locatedAtScale hc₁ h hn hne).le
  obtain ⟨hlo, hhi⟩ := h n hn hne
  exact ⟨(mul_le_mul_of_nonneg_right h₀ hN).trans hlo,
    hhi.trans (mul_le_mul_of_nonneg_right h₁ hN)⟩

/-- Widening the support window preserves smoothness, the derivative data being untouched. -/
theorem isSmoothAtScale_mono {c C c' C' : ℝ} {b : ℕ → ℝ} {w : ℕ → ℕ} {α : ℕ → ℂ} {N : ℝ}
    (h₀ : c' ≤ c) (h₁ : C ≤ C') (h : IsSmoothAtScale c C b w α N) :
    IsSmoothAtScale c' C' b w α N := by
  obtain ⟨ψ, hψ, hsupp, hderiv, heq⟩ := h
  exact ⟨ψ, hψ, fun t ht ↦ ⟨h₀.trans (hsupp t ht).1, (hsupp t ht).2.trans h₁⟩, hderiv, heq⟩

/-- **A sequence smooth at a positive scale is located there**: the profile vanishes off
`[c₋, c₊]`, so a nonzero term has `n/N` in that interval. -/
theorem locatedAtScale_of_isSmoothAtScale (K : ConstantBundle) {α : ℕ → ℂ} {N : ℝ}
    (hN : 0 < N) (h : K.IsSmoothAtScale α N) : K.LocatedAtScale α N := by
  obtain ⟨ψ, -, hsupp, -, hval⟩ := h
  intro n _ hne
  obtain ⟨h₁, h₂⟩ := hsupp _ (by rwa [← hval n])
  exact ⟨(le_div_iff₀ hN).1 h₁, (div_le_iff₀ hN).1 h₂⟩

/-- **The convolution bundle only widens, at a normalized bundle**, and is normalized again — which
is what lets it be iterated. -/
theorem conv_transfer {K : ConstantBundle} (hlo : K.scaleLo ≤ 1) (hhi : 1 ≤ K.scaleHi)
    (hC : 1 ≤ K.coeffConst) :
    K.conv.scaleLo ≤ 1 ∧ 1 ≤ K.conv.scaleHi ∧ 1 ≤ K.conv.coeffConst ∧
      (∀ α : ℕ → ℂ, K.IsCoefficientSequence α → K.conv.IsCoefficientSequence α) ∧
      (∀ (α : ℕ → ℂ) (N : ℝ), K.LocatedAtScale α N → K.conv.LocatedAtScale α N) ∧
      (∀ (α : ℕ → ℂ) (N : ℝ), K.IsSmoothAtScale α N → K.conv.IsSmoothAtScale α N) := by
  have hlo0 := K.scaleLo_pos
  refine ⟨?_, ?_, ?_, fun α h ↦ isCoefficientSequence_mono (by linarith) ?_ ?_ ?_ h,
    fun α N h ↦ locatedAtScale_mono (hlo0.trans K.scaleLo_lt_scaleHi) ?_ ?_ h,
    fun α N h ↦ isSmoothAtScale_mono ?_ ?_ h⟩
  all_goals dsimp only [ConstantBundle.conv]; first | omega | nlinarith

/-- **Membership in the Harman class transfers to the normalized bundle.** Each of the three shapes
has every clause widened by `Gap212.constantBundle_flat_transfer`. -/
theorem harmanClass_flat {K : ConstantBundle} {x ξ₁ ξ₂ ξ₃ : ℝ} {f : ℕ → ℂ}
    (h : HarmanClass K x ξ₁ ξ₂ ξ₃ f) : HarmanClass K.flat x ξ₁ ξ₂ ξ₃ f := by
  obtain ⟨-, -, -, -, -, hcoeff, hloc, hsmooth, hSW, hasymp⟩ := constantBundle_flat_transfer K
  rcases h with h | h | h
  · obtain ⟨α, β, M, hM, N, hN, hfe, hα, hβ, hαM, hβN, hasy, hsβ, hNlo⟩ := h
    exact Or.inl ⟨α, β, M, hM, N, hN, hfe, hcoeff _ hα, hcoeff _ hβ, hloc _ _ hαM,
      hloc _ _ hβN, hasymp _ _ hasy, hsmooth _ _ hsβ, hNlo⟩
  · obtain ⟨α, β, M, hM, N, hN, hfe, hα, hβ, hαM, hβN, hasy, hSWα, hSWβ, hNlo, hNhi⟩ := h
    exact Or.inr (Or.inl ⟨α, β, M, hM, N, hN, hfe, hcoeff _ hα, hcoeff _ hβ, hloc _ _ hαM,
      hloc _ _ hβN, hasymp _ _ hasy, hSW _ _ hSWα, hSW _ _ hSWβ, hNlo, hNhi⟩)
  · obtain ⟨α, ψ₁, ψ₂, ψ₃, M, hM, N₁, hN₁, N₂, hN₂, N₃, hN₃, hfe, hα, hp₁, hp₂, hp₃, hαM,
      hs₁, hs₂, hs₃, hasy, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ := h
    exact Or.inr (Or.inr ⟨α, ψ₁, ψ₂, ψ₃, M, hM, N₁, hN₁, N₂, hN₂, N₃, hN₃, hfe, hcoeff _ hα,
      hcoeff _ hp₁, hcoeff _ hp₂, hcoeff _ hp₃, hloc _ _ hαM, hsmooth _ _ hs₁, hsmooth _ _ hs₂,
      hsmooth _ _ hs₃, hasymp _ _ hasy, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩)

/-- **A member of the Harman class is a located coefficient sequence vanishing at `0`.** The scale
is the product of its declared scales: at least `1` because each factor's is, at most `a₊ x` by
commensurability. These are exactly the hypotheses
`Gap212.hasEquidistribution_of_forall_ge` asks in order to absorb a bounded range of `x`. -/
theorem exists_scale_of_harmanClass {K : ConstantBundle} {x ξ₁ ξ₂ ξ₃ : ℝ} {f : ℕ → ℂ}
    (hlo : K.scaleLo ≤ 1) (hhi : 1 ≤ K.scaleHi) (hC : 1 ≤ K.coeffConst)
    (h : HarmanClass K x ξ₁ ξ₂ ξ₃ f) :
    ∃ Nf : ℝ, 1 ≤ Nf ∧ Nf ≤ K.asympHi * x ∧
      K.conv.conv.conv.IsCoefficientSequence f ∧
      K.conv.conv.conv.LocatedAtScale f Nf ∧ f 0 = 0 := by
  obtain ⟨hlo1, hhi1, hC1, c1C, c1L, c1S⟩ := conv_transfer hlo hhi hC
  obtain ⟨hlo2, hhi2, hC2, c2C, c2L, -⟩ := conv_transfer hlo1 hhi1 hC1
  obtain ⟨-, -, -, c3C, c3L, -⟩ := conv_transfer hlo2 hhi2 hC2
  have two : ∀ α β : ℕ → ℂ, ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      K.IsCoefficientSequence α → K.IsCoefficientSequence β →
      K.LocatedAtScale α M → K.LocatedAtScale β N → K.asympEq (M * N) x →
      ∃ Nf : ℝ, 1 ≤ Nf ∧ Nf ≤ K.asympHi * x ∧
        K.conv.conv.conv.IsCoefficientSequence (dconv α β) ∧
        K.conv.conv.conv.LocatedAtScale (dconv α β) Nf ∧ dconv α β 0 = 0 := by
    intro α β M N hM hN hα hβ hαM hβN hasymp
    obtain ⟨hd, hl⟩ := isCoefficientSequence_and_locatedAtScale_dconv hα hβ hαM hβN
    exact ⟨M * N, one_le_mul_of_one_le_of_one_le hM hN, hasymp.2, c3C _ (c2C _ hd),
      c3L _ _ (c2L _ _ hl), by simp [dconv]⟩
  rcases h with ⟨α, β, M, hM, N, hN, rfl, hα, hβ, hαM, hβN, hasymp, -⟩ |
    ⟨α, β, M, hM, N, hN, rfl, hα, hβ, hαM, hβN, hasymp, -⟩ |
    ⟨α, ψ₁, ψ₂, ψ₃, M, hM, N₁, hN₁, N₂, hN₂, N₃, hN₃, rfl, hα, hp₁, hp₂, hp₃, hαM,
      hs₁, hs₂, hs₃, hasymp, -⟩
  · exact two α β M N hM hN hα hβ hαM hβN hasymp
  · exact two α β M N hM hN hα hβ hαM hβN hasymp
  have hl₁ := locatedAtScale_of_isSmoothAtScale K (by linarith) hs₁
  have hl₂ := locatedAtScale_of_isSmoothAtScale K (by linarith) hs₂
  have hl₃ := locatedAtScale_of_isSmoothAtScale K (by linarith) hs₃
  obtain ⟨d₁, l₁⟩ := isCoefficientSequence_and_locatedAtScale_dconv hα hp₁ hαM hl₁
  obtain ⟨d₂, l₂⟩ :=
    isCoefficientSequence_and_locatedAtScale_dconv d₁ (c1C _ hp₂) l₁ (c1L _ _ hl₂)
  obtain ⟨d₃, l₃⟩ := isCoefficientSequence_and_locatedAtScale_dconv d₂ (c2C _ (c1C _ hp₃)) l₂
    (c2L _ _ (c1L _ _ hl₃))
  refine ⟨M * N₁ * N₂ * N₃, ?_, hasymp.2, d₃, l₃, by simp [dconv]⟩
  bound

end Gap212.HalfLevel

namespace Gap212

open Real Finset Gap212.Bridges Gap212.HalfLevel Gap212.Packing

open Classical in
/-- **Half-level arithmetic coverage**, from Condition D at
the datum. The statement is `Gap212.HarmanClassEquidistributes`: at `p_⋆` and
`(ξ₁,ξ₂,ξ₃) = (19/50, 2/5, 2/5)`, for every bundle `K`, every `ε₀ > 0` and every `A > 0` there is a
`C` with `E_⋆(p_⋆,x,ε₀,f,a,A,C)` at every `x ≥ 3`, every member of the class and every `a` coprime
below `x`.

Three inputs: the routes above `x^{1/2-ε₁}` (`Gap212.harmanAntecedent_of_conditionD`), bilinear
Bombieri–Vinogradov below `x^{1/2}(log x)^{-B}`, and the absorption of
`3 ≤ x ≤ x₀(B,ε₁)` into the constant. -/
theorem halfLevelCoverage_of_conditionD (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath)
    (h₃ : TypeIBakerIrving) (h₄ : TypeIStadlmann) (h₅ : TypeIIIPolymath)
    (hbv : BilinearBombieriVinogradov)
    (hcondD : ∀ (j j' : Fin gap212Params.n) (m m' : ℕ),
      Defs.ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
        (capCondD gap212Params)
        (chamberCondD gap212Params (2 / 5) (omegaMax gap212Params j j')
          (omegaMax gap212Params j j'))) :
    HarmanClassEquidistributes := by
  intro K ε₀ hε₀ A hA
  -- the positive-level range
  obtain ⟨ε₁, hε₁, hposA⟩ := harmanAntecedent_of_conditionD h₁ h₂ h₃ h₄ h₅ hcondD K ε₀ hε₀
  obtain ⟨Cpos, hCpos⟩ := hposA A hA
  -- the sub-half range
  obtain ⟨B, hBpos, Cbv, hCbv⟩ := exists_hasEquidistribution_subhalf_of_harmanClass hbv h₃
    (ξ₁ := 19 / 50) (ξ₂ := 2 / 5) (ξ₃ := 2 / 5) (by norm_num [slack]) (by norm_num [slack])
    (by norm_num [slack]) K hA
  obtain ⟨x₀, hx₀1, hx₀⟩ := Routing.exists_threshold_ranges_compare B hε₁
  obtain ⟨hflo, hfhi, -, -, hfC, -, -, -, -, -⟩ := constantBundle_flat_transfer K
  have hx₁3 : (3 : ℝ) ≤ max x₀ 3 := le_max_right _ _
  -- the two ranges cover above the threshold
  have key : ∀ x ≥ max x₀ 3, ∀ D ⊆ moduliRange x (7 / 1000 : ℝ), ∀ f : ℕ → ℂ, ∀ a : ℕ,
      ((HarmanClass K x (19 / 50) (2 / 5) (2 / 5) f ∧ CoprimeBelow a x) ∧
        D = {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar gap212Params x ε₀}) →
      ∀ N : ℝ, 1 ≤ N → N ≤ K.flat.asympHi * x →
        IsCoefficientSequence K.flat.conv.conv.conv.coeffConst
            K.flat.conv.conv.conv.coeffFstPow K.flat.conv.conv.conv.coeffSndPow f →
          LocatedAtScale K.flat.conv.conv.conv.scaleLo K.flat.conv.conv.conv.scaleHi f N →
            f 0 = 0 → HasEquidistribution x D f a A (max (Cpos + Cbv) 0) := by
    rintro x hx D - f a ⟨⟨hf, hcop⟩, rfl⟩ N - - - - -
    have hx3 : (3 : ℝ) ≤ x := hx₁3.trans hx
    -- the cover
    have hcover : {d ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar gap212Params x ε₀} | Squarefree d}
        ⊆ {d ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ |
              q ∈ Qstar gap212Params x ε₀ ∧ x ^ (1 / 2 - ε₁) < (q : ℝ)} | Squarefree d}
          ∪ {d ∈ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / Real.log x ^ B⌋₊ | Squarefree d} := by
      intro d hd
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc] at hd ⊢
      rcases lt_or_ge (x ^ (1 / 2 - ε₁)) (d : ℝ) with hbig | hsmall
      · exact Or.inl ⟨⟨hd.1.1, hd.1.2, hbig⟩, hd.2⟩
      · exact Or.inr ⟨⟨hd.1.1.1, Nat.le_floor (hsmall.trans (hx₀ x ((le_max_left _ _).trans hx)))⟩,
          hd.2⟩
    have hsf : ∀ d : ℕ, (0 : ℝ) ≤ ‖sumError f d a‖ := fun d ↦ norm_nonneg _
    have hbpos := hCpos x hx3 f a hf hcop
    have hbbv := hCbv x hx3 f a hf hcop
    rw [HasEquidistribution] at hbpos hbbv ⊢
    have hstep := Routing.sum_union_le_of_nonneg (f := fun d ↦ ‖sumError f d a‖) hsf
      {d ∈ {q ∈ Finset.Icc 1 ⌊x⌋₊ |
          q ∈ Qstar gap212Params x ε₀ ∧ x ^ (1 / 2 - ε₁) < (q : ℝ)} | Squarefree d}
      {d ∈ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) / Real.log x ^ B⌋₊ | Squarefree d}
    have hfin : Cpos * x / Real.log x ^ A + Cbv * x / Real.log x ^ A
        ≤ max (Cpos + Cbv) 0 * x / Real.log x ^ A := by
      rw [← add_div, ← add_mul]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
        (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) A).le
    linarith [Finset.sum_le_sum_of_subset_of_nonneg hcover fun d _ _ ↦ hsf d]
  -- absorb the bounded range
  have hCfin := hasEquidistribution_of_forall_ge (by norm_num) hA.le hx₁3 (le_max_right _ _) key
  -- the generated moduli below `x` lie in the ambient range at the datum's level
  have hD : ∀ x : ℝ, 3 ≤ x →
      {q ∈ Finset.Icc 1 ⌊x⌋₊ | q ∈ Qstar gap212Params x ε₀} ⊆ moduliRange x (7 / 1000 : ℝ) := by
    intro x hx q hq
    simp only [Finset.mem_filter, Qstar, Set.mem_iUnion] at hq
    obtain ⟨-, j, j', m, -, m', -, hm'⟩ := hq
    have hω := omegaMax_gap212Params j j'
    rw [omegaMax] at hω
    rw [← hω]
    exact Routing.mem_moduliRange_of_qgen (by linarith) hε₀ (by linarith) hm'
  exact ⟨_, fun x hx f a hf hcop ↦
    have ⟨Nf, hNf1, hNfb, hcoef, hloc, hf0⟩ :=
      exists_scale_of_harmanClass hflo hfhi hfC (harmanClass_flat hf)
    hCfin x hx _ (hD x hx) f a ⟨⟨hf, hcop⟩, rfl⟩ Nf hNf1 hNfb hcoef hloc hf0⟩

/-- **The routing obligation, from Condition D at the datum.** The five assumed estimates and
bilinear Bombieri–Vinogradov give `Gap212.HarmanClassEquidistributes`, so
`Gap212.RoutingObligation` reduces to the continuum packing condition and nothing else. -/
theorem routingObligation_of_conditionD
    (hcondD : ∀ (j j' : Fin gap212Params.n) (m m' : ℕ),
      Defs.ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
        (capCondD gap212Params)
        (chamberCondD gap212Params (2 / 5) (omegaMax gap212Params j j')
          (omegaMax gap212Params j j'))) :
    RoutingObligation :=
  fun h₁ h₂ h₃ h₄ h₅ hbv ↦ halfLevelCoverage_of_conditionD h₁ h₂ h₃ h₄ h₅ hbv hcondD

end Gap212
