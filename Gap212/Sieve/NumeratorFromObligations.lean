/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Sieve.Asymptotics
public import Gap212.Sieve.DivisorSumFacts
public meta import Gap212.Attr

/-!
# The numerator lower bound, from the sieve asymptotic

The numerator lower bound is routed through `Gap212.Sieve.SieveAsymptotic`:
> Fix `i ≤ k` and split the inner sum of the tensor weight `ν` as `P(n) + Q(n)`, where `P` collects
> the indices in `𝓛(i)` and `Q` those in `𝓤(i)`. Since `ρ(n + h_i;x) ≥ 0`,
> `Gap212.Sieve.omit_square_le` at `w = ρ(n + h_i;x)` gives the pointwise bound
> `ν(n)ρ(n + h_i;x) ≥ ρ(n + h_i;x)(P(n)² + 2P(n)Q(n))`. Summing over `n` and expanding `P²` and
> `2PQ` into their finitely many tensor pairs, every resulting term is an instance of the sieve
> asymptotic with `i₀ = i`.

`Gap212.Sieve.numeratorLowerBound_of_sieveAsymptotic` is this implication.

## Where the marginal clause comes from

`SieveAsymptotic` carries the clause `supp ∏_{s≠i₀} F_s ⊆ M⁻_k(j,i₀,ε₀)` as a hypothesis, and
nothing derives it from retreat membership. It is discharged from **`𝓛`-membership**: it holds for
the first index of each such pair, which is in `𝓛(i)` by the definition of `𝓛` for the `P²` terms
and, after using the symmetry of the product in `(l,l')`, for the cross terms as well. So the
splitting is what supplies the clause, and the implementation follows that exactly — the pointwise
bound is taken as `P² + 2PQ`, whose first index always lies in `𝓛(i)`, and the cross group is
matched against `Gap212.Defs.formJMarginal`'s `∑_{l ∈ 𝓤} ∑_{l' ∈ 𝓛}` by
`Gap212.Sieve.gramInnerSkip_comm`, the symmetry in question.

## Why the split has to be a hypothesis

Quantified over `𝓛 𝓤 : Fin (m+1) → Finset (Fin D.L)` **freely and independently**,
`Gap212.Sieve.NumeratorAsymptotic` would be strictly stronger than the statement it carries —
strong enough that it should be expected false. `𝓙ᵢ` is `Gap212.Defs.formJMarginal` evaluated at
the *complementary* index sets `𝓛(i)` and `𝓤(i)` cut out by one marginal predicate. At
`𝓛 i = 𝓤 i = univ` `formJMarginal` is three times the full Gram form
`∑_{l,l'} c_l c_{l'} f_{l,i}(0) f_{l',i}(0) ∏_{s≠i} ∫₀^∞ f'_{l,s} f'_{l',s}`, while the asymptotic
evaluates the numerator at exactly that form — so the unsplit `Prop` demands a lower bound three
times the truth, which fails for any datum whose form is positive.

The `Prop` carries the split: `𝓤 i = (𝓛 i)ᶜ`, and the marginal clause for every
`l ∈ 𝓛 i`. Both are supplied where the sieve actually uses them — `Gap212.Sieve.sieveWeights`
exports them, having them from `Gap212.GPY.exists_tensorDatum_forms_gap`, whose datum is built with
`Gap212.Defs.LSet`/`USet` of the endpoint predicate
`∑_{s≠i} β_{l,s} < (1-ε₀)(A_{j+1} - ε)`; the tail factors vanish above their endpoints, so that
cutoff *is* the marginal region's. The two clauses are the content of `Gap212.Defs.LSet`/`USet`
that the numerator's proof consumes, rather than the endpoint predicate itself, which is internal
to the mesh construction; `Gap212.Sieve.numeratorLowerBound_of_lset` is the same statement with
`𝓛`, `𝓤` written literally as `Gap212.Defs.LSet`, `USet` of a marginal predicate.

With the split in place `Gap212.Sieve.numeratorAsymptotic_of_sieveAsymptotic` proves
`Gap212.Sieve.NumeratorAsymptotic` outright from `Gap212.Sieve.SieveAsymptotic`.

## Main results

* `Gap212.Sieve.numeratorLowerBound_of_sieveAsymptotic`: the numerator lower bound, from
  `Gap212.Sieve.SieveAsymptotic` and `Gap212.Sieve.omit_square_le`, at the low/high split.
* `Gap212.Sieve.numeratorAsymptotic_of_sieveAsymptotic`: the same packaged as
  `SieveAsymptotic m → NumeratorAsymptotic m`.
* `Gap212.Sieve.numeratorLowerBound_of_lset`: the split spelled as `Gap212.Defs.LSet`/`USet`.
-/

@[expose] public section

namespace Gap212.Sieve

open Finset Real Gap212.Defs Gap212.GPY

/-! ## Two sums a tensor pair contributes -/

/-- **The weighted count a single tensor pair contributes**, `∑_n ρ(n + h_i;x) ∏_s λ_{f_{l,s}}(n +
h_s) λ_{f_{l',s}}(n + h_s)` over the pre-sieved class of the dyadic block. This is the left-hand
side of `Gap212.Sieve.SieveAsymptotic` at `F = f l`, `G = f l'` and `i₀ = i`. -/
noncomputable def tensorPairCount {L k : ℕ} (ρ : ℕ → ℝ → ℝ) (f : Fin L → Fin k → ℝ → ℝ)
    (hh : Fin k → ℕ) (i : Fin k) (x : ℝ) (b : ℕ) (l l' : Fin L) : ℝ :=
  ∑ n ∈ dyadic x with n % W x = b % W x,
    ρ (n + hh i) x * ∏ s, lambdaF (f l s) x (n + hh s) * lambdaF (f l' s) x (n + hh s)

/-- **The main term of that pair**, `f_{l,i}(0) f_{l',i}(0) ∏_{s≠i} ∫₀^∞ f'_{l,s} f'_{l',s}`: the
right-hand side of `Gap212.Sieve.SieveAsymptotic`, and the summand of
`Gap212.Defs.formJMarginal` once the coefficients are stripped off. -/
noncomputable def tensorPairMain {L m : ℕ} (f : Fin L → Fin (m + 1) → ℝ → ℝ) (i : Fin (m + 1))
    (l l' : Fin L) : ℝ :=
  gramBdry f i l * gramBdry f i l' * ∏ s : Fin m, gramInnerSkip f i l l' s

/-- **The skipped Gram data is symmetric in the pair.** This is the symmetry of the product in
`(l,l')` that puts the first index of a cross term in `𝓛(i)`. -/
theorem gramInnerSkip_comm {L m : ℕ} (F : Fin L → Fin (m + 1) → ℝ → ℝ) (i : Fin (m + 1))
    (l l' : Fin L) (s : Fin m) : gramInnerSkip F i l l' s = gramInnerSkip F i l' l s := by
  simp [gramInnerSkip, mul_comm]

/-- **The pair's main term is symmetric in the pair.** -/
theorem tensorPairMain_comm {L m : ℕ} (f : Fin L → Fin (m + 1) → ℝ → ℝ) (i : Fin (m + 1))
    (l l' : Fin L) : tensorPairMain f i l l' = tensorPairMain f i l' l := by
  simp only [tensorPairMain, gramInnerSkip_comm f i l l']
  ring

/-- **`𝓙ᵢ` is the coefficient-weighted sum of the pair main terms** over its two groups: the
low–low group and twice the high–low one, exactly as `Gap212.Defs.formJMarginal` reads. -/
theorem formJMarginal_eq_tensorPairMain {L m : ℕ} (c : Fin L → ℝ) (f : Fin L → Fin (m + 1) → ℝ → ℝ)
    (i : Fin (m + 1)) (𝓛 𝓤 : Finset (Fin L)) :
    formJMarginal c (gramBdry f i) (gramInnerSkip f i) 𝓛 𝓤 =
      (∑ l ∈ 𝓛, ∑ l' ∈ 𝓛, c l * c l' * tensorPairMain f i l l') +
        2 * ∑ l ∈ 𝓤, ∑ l' ∈ 𝓛, c l * c l' * tensorPairMain f i l l' := by
  simp only [formJMarginal, formJLowLow, tensorPairMain, mul_assoc]

/-! ## The instance of the sieve asymptotic a pair gives -/

/-- **One tensor pair's count is its main term plus `o(1)`**, which is
`Gap212.Sieve.SieveAsymptotic` read at `F = f l`, `G = f l'`, `i₀ = i` and `j' = j`.

Everything `Gap212.Sieve.SieveAsymptotic` asks of the profiles is supplied by the tensor datum —
`C^∞` from `TensorDatum.smooth`, one-sided compact support from `TensorDatum.compactSupport`, both
retreat clauses from `TensorDatum.supp_subset` at the single band `j` — except the marginal clause,
which is the caller's, and which the splitting supplies. -/
theorem exists_tensorPairCount_close {p : SupportParams} {m : ℕ} (hasym : SieveAsymptotic m)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) {j : Fin p.n} (hA : p.ε < p.A j.succ)
    (D : TensorDatum p (m + 1) j ε₀) {ρ : ℕ → ℝ → ℝ} {β : ℝ} (hρ : RhoHypotheses p ρ β)
    (hequi : HasEquidistributionOverQstarFamily p (fun n x ↦ ((ρ n x : ℝ) : ℂ)))
    {hh : Fin (m + 1) → ℕ} (hmono : StrictMono hh) (i : Fin (m + 1)) (l l' : Fin D.L)
    (hmarg : ∀ t : Fin m → ℝ, (∀ s, 0 ≤ t s) →
      (∏ s, D.f l (i.succAbove s) (t s)) ≠ 0 → t ∈ marginalRegion p m j ε₀)
    {η : ℝ} (hη : 0 < η) :
    ∃ X : ℝ, ∀ x > X, ∀ b : ℕ, Defs.IsPreSieved b (W x) hh →
      |tensorPairCount ρ D.f hh i x b l l' - tensorPairMain D.f i l l' * scale (m + 1) x|
        ≤ η * scale (m + 1) x := by
  obtain ⟨B, hB⟩ := D.compactSupport
  exact hasym p ε₀ hε₀ hε₀' j j hA ρ β hρ hequi hh hmono i (D.f l) (D.f l')
    (D.smooth l) (D.smooth l')
    ⟨B, hB l⟩ ⟨B, hB l'⟩
    (D.supp_subset l) (D.supp_subset l') hmarg η hη

/-! ## The algebra of the split -/

/-- **A triple sum may be reordered to bring the innermost index outside.** -/
private theorem sum_comm₃ {α β γ : Type*} (s : Finset α) (t : Finset β) (u : Finset γ)
    (F : α → β → γ → ℝ) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ d ∈ u, F a b d = ∑ d ∈ u, ∑ a ∈ s, ∑ b ∈ t, F a b d :=
  (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm).trans Finset.sum_comm

/-- **The pointwise omitted square, expanded into pairs.** `P` is the `𝓛`-part of the inner sum and
`Q` its complement; the left-hand side is `w(P² + 2PQ)` written out over pairs and the right-hand
side is `w(P + Q)²`, so this is `Gap212.Sieve.omit_square_le` in the shape the tensor expansion
produces. -/
private theorem sum_split_le {L : ℕ} (w : ℝ) (hw : 0 ≤ w) (c A : Fin L → ℝ)
    (𝓛 : Finset (Fin L)) :
    (∑ l ∈ 𝓛, ∑ l' ∈ 𝓛, c l * c l' * (w * (A l * A l'))) +
        2 * ∑ l ∈ 𝓛, ∑ l' ∈ 𝓛ᶜ, c l * c l' * (w * (A l * A l')) ≤
      (∑ l, c l * A l) ^ 2 * w := by
  classical
  have h1 (s t : Finset (Fin L)) : ∑ l ∈ s, ∑ l' ∈ t, c l * c l' * (w * (A l * A l')) =
      w * ((∑ l ∈ s, c l * A l) * ∑ l' ∈ t, c l' * A l') := by
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [h1, h1, ← Finset.sum_add_sum_compl 𝓛 fun l ↦ c l * A l]
  linarith [omit_square_le hw (∑ l ∈ 𝓛, c l * A l) (∑ l ∈ 𝓛ᶜ, c l * A l)]

/-- **The split's pair sums are bounded by the numerator's inner sum**, coordinate by coordinate:
the pointwise bound `ν(n)ρ(n + h_i;x) ≥ ρ(n + h_i;x)(P(n)² + 2P(n)Q(n))`, summed over the
progression and expanded into tensor pairs. -/
theorem pairSum_le_nu_sum {L k : ℕ} {ρ : ℕ → ℝ → ℝ} (c : Fin L → ℝ)
    (f : Fin L → Fin k → ℝ → ℝ) (hh : Fin k → ℕ) (x : ℝ) (b : ℕ) (i : Fin k)
    (hρnn : ∀ n : ℕ, 0 ≤ ρ n x) (𝓛 : Finset (Fin L)) :
    (∑ l ∈ 𝓛, ∑ l' ∈ 𝓛, c l * c l' * tensorPairCount ρ f hh i x b l l') +
        2 * ∑ l ∈ 𝓛, ∑ l' ∈ 𝓛ᶜ, c l * c l' * tensorPairCount ρ f hh i x b l l' ≤
      ∑ n ∈ dyadic x with n % W x = b % W x, nu L c f hh x n * ρ (n + hh i) x := by
  classical
  have hswap (s t : Finset (Fin L)) :
      ∑ l ∈ s, ∑ l' ∈ t, c l * c l' * tensorPairCount ρ f hh i x b l l' =
        ∑ n ∈ dyadic x with n % W x = b % W x, ∑ l ∈ s, ∑ l' ∈ t,
          c l * c l' * (ρ (n + hh i) x *
            ∏ q, lambdaF (f l q) x (n + hh q) * lambdaF (f l' q) x (n + hh q)) := by
    simp only [tensorPairCount, Finset.mul_sum]
    exact sum_comm₃ _ _ _ _
  rw [hswap 𝓛 𝓛, hswap 𝓛 𝓛ᶜ, Finset.mul_sum _ _ (2 : ℝ), ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n _ ↦ ?_
  simp only [Finset.prod_mul_distrib, nu]
  exact sum_split_le (ρ (n + hh i) x) (hρnn _) c
    (fun l ↦ ∏ q, lambdaF (f l q) x (n + hh q)) 𝓛

/-- **The split's pair sums are within `3(∑|c_l|)²ε` of `𝓙ᵢ`** once every pair whose first index is
in `𝓛` is within `ε` of its main term. The cross group of `Gap212.Defs.formJMarginal` runs over
`𝓤 × 𝓛`, so matching it against the `P·Q` group — whose first index must be in `𝓛`, that being
where the marginal clause lives — is where the symmetry of the main term is spent. -/
private theorem abs_split_sub_le {L : ℕ} (c : Fin L → ℝ) (Sg Mn : Fin L → Fin L → ℝ)
    (hsymm : ∀ l l', Mn l l' = Mn l' l) (𝓛 : Finset (Fin L)) (sc e : ℝ)
    (hsc : 0 ≤ sc) (he : 0 ≤ e)
    (hclose : ∀ l ∈ 𝓛, ∀ l', |Sg l l' - Mn l l' * sc| ≤ e * sc) :
    |((∑ l ∈ 𝓛, ∑ l' ∈ 𝓛, c l * c l' * Sg l l') +
          2 * ∑ l ∈ 𝓛, ∑ l' ∈ 𝓛ᶜ, c l * c l' * Sg l l') -
        ((∑ l ∈ 𝓛, ∑ l' ∈ 𝓛, c l * c l' * Mn l l') +
          2 * ∑ l ∈ 𝓛ᶜ, ∑ l' ∈ 𝓛, c l * c l' * Mn l l') * sc| ≤
      3 * (∑ l, |c l|) ^ 2 * e * sc := by
  classical
  have hcross : ∑ l ∈ 𝓛ᶜ, ∑ l' ∈ 𝓛, c l * c l' * Mn l l'
      = ∑ l ∈ 𝓛, ∑ l' ∈ 𝓛ᶜ, c l * c l' * Mn l l' := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun d _ ↦ by rw [hsymm a d]; ring
  have hb (t : Finset (Fin L)) : |(∑ l ∈ 𝓛, ∑ l' ∈ t, c l * c l' * Sg l l') -
      (∑ l ∈ 𝓛, ∑ l' ∈ t, c l * c l' * Mn l l') * sc| ≤ (∑ l, |c l|) ^ 2 * e * sc := by
    simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ l ∈ 𝓛, ∑ l' ∈ t, |c l| * |c l'| * (e * sc) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl ↦ ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l' _ ↦ ?_)
          rw [mul_assoc _ (Mn l l'), ← mul_sub, abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hclose l hl l') (by positivity)
      _ ≤ ∑ l, ∑ l', |c l| * |c l'| * (e * sc) := by
          refine (Finset.sum_le_sum fun l _ ↦ Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ t) fun l' _ _ ↦ by positivity).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ 𝓛) fun l _ _ ↦ by positivity)
      _ = (∑ l, |c l|) ^ 2 * e * sc := by
          rw [sq, Finset.sum_mul_sum]
          simp only [Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hcross]
  have h₁ := abs_le.1 (hb 𝓛)
  have h₂ := abs_le.1 (hb 𝓛ᶜ)
  exact abs_le.2 ⟨by linarith [h₁.1, h₂.1], by linarith [h₁.2, h₂.2]⟩

/-! ## The link -/

/-- **The numerator lower bound from the sieve asymptotic**, at the low/high split of `ν`.

`hsplit` and `hmarg` are what `Gap212.Defs.LSet` and `USet` say: `𝓤(i)` is the complement of
`𝓛(i)`, and a term in `𝓛(i)` has its `i`-omitted marginal supported in `M⁻_k(j,i,ε₀)`. The second
is the hypothesis `Gap212.Sieve.SieveAsymptotic` cannot derive and the splitting supplies; see the
module docstring. `Gap212.Sieve.NumeratorAsymptotic` carries both, so
`Gap212.Sieve.numeratorAsymptotic_of_sieveAsymptotic` is this theorem repackaged.

`p.ε < p.A j.succ` says that `p` is a support datum with `A_j > ε`, and it is a hypothesis of
`Gap212.Sieve.SieveAsymptotic` too. The other clause that statement needs of the minorant — that
its rough exponent `β` clears the cap row — travels inside `Gap212.Defs.RhoHypotheses`. -/
theorem numeratorLowerBound_of_sieveAsymptotic {p : SupportParams} {m : ℕ}
    (hasym : SieveAsymptotic m) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) {j : Fin p.n}
    (hA : p.ε < p.A j.succ) (D : TensorDatum p (m + 1) j ε₀)
    {ρ : ℕ → ℝ → ℝ} {β : ℝ} (hρ : RhoHypotheses p ρ β)
    (hequi : HasEquidistributionOverQstarFamily p (fun n x ↦ ((ρ n x : ℝ) : ℂ)))
    {hh : Fin (m + 1) → ℕ} (hmono : StrictMono hh)
    {𝓛 𝓤 : Fin (m + 1) → Finset (Fin D.L)} (hsplit : ∀ i, 𝓤 i = (𝓛 i)ᶜ)
    (hmarg : ∀ i : Fin (m + 1), ∀ l ∈ 𝓛 i, ∀ t : Fin m → ℝ, (∀ s, 0 ≤ t s) →
      (∏ s, D.f l (i.succAbove s) (t s)) ≠ 0 → t ∈ marginalRegion p m j ε₀)
    {η : ℝ} (hη : 0 < η) :
    ∃ X : ℝ, ∀ x > X, ∀ b : ℕ, Defs.IsPreSieved b (W x) hh →
      (∑ i : Fin (m + 1), ∑ n ∈ dyadic x with n % W x = b % W x,
          nu D.L D.c D.f hh x n * ρ (n + hh i) x) ≥
        (∑ i : Fin (m + 1),
            formJMarginal D.c (gramBdry D.f i) (gramInnerSkip D.f i) (𝓛 i) (𝓤 i)) *
          scale (m + 1) x - η * scale (m + 1) x := by
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ l, |D.c l| := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := hSdef ▸ Finset.sum_nonneg fun l _ ↦ abs_nonneg _
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = 3 * ((m : ℝ) + 1) * S ^ 2 + 1 := ⟨_, rfl⟩
  have hC0 : 0 < C := by rw [hCdef]; positivity
  have he0 : 0 < η / C := div_pos hη hC0
  -- One threshold per coordinate and tensor pair, vacuous off `𝓛`.
  have key : ∀ (i : Fin (m + 1)) (l l' : Fin D.L), ∃ X : ℝ, ∀ x > X, ∀ b : ℕ,
      Defs.IsPreSieved b (W x) hh → l ∈ 𝓛 i →
      |tensorPairCount ρ D.f hh i x b l l' - tensorPairMain D.f i l l' * scale (m + 1) x|
        ≤ η / C * scale (m + 1) x := by
    intro i l l'
    by_cases hl : l ∈ 𝓛 i
    · obtain ⟨X, hX⟩ :=
        exists_tensorPairCount_close hasym hε₀ hε₀' hA D hρ hequi hmono i l l' (hmarg i l hl) he0
      exact ⟨X, fun x hx b hb _ ↦ hX x hx b hb⟩
    · exact ⟨0, fun x _ b _ hl' ↦ absurd hl' hl⟩
  choose XF hXF using key
  obtain ⟨X₀, hX₀⟩ :=
    Finite.exists_le fun z : Fin (m + 1) × Fin D.L × Fin D.L ↦ XF z.1 z.2.1 z.2.2
  refine ⟨max X₀ 1, fun x hx b hb ↦ ?_⟩
  have hx1 : 1 < x := (le_max_right X₀ 1).trans_lt hx
  have hxX : ∀ (i : Fin (m + 1)) (l l' : Fin D.L), XF i l l' < x := fun i l l' ↦
    lt_of_le_of_lt (hX₀ (i, l, l')) (lt_of_le_of_lt (le_max_left X₀ 1) hx)
  have hsc : 0 < scale (m + 1) x := scale_pos hx1 (primorial_pos _)
  have hρnn : ∀ n : ℕ, 0 ≤ ρ n x := fun n ↦ by
    by_cases hn : n ∈ dyadic x
    · exact (hρ.minorant x hx1 n hn).1
    · rw [hρ.support x n hn]
  -- Coordinate by coordinate: the split is below the numerator and above `𝓙ᵢ` up to the error.
  have hstep : ∀ i : Fin (m + 1),
      formJMarginal D.c (gramBdry D.f i) (gramInnerSkip D.f i) (𝓛 i) (𝓤 i) * scale (m + 1) x
          - 3 * S ^ 2 * (η / C) * scale (m + 1) x ≤
        ∑ n ∈ dyadic x with n % W x = b % W x, nu D.L D.c D.f hh x n * ρ (n + hh i) x := by
    intro i
    refine le_trans ?_ (pairSum_le_nu_sum D.c D.f hh x b i hρnn (𝓛 i))
    have habs := abs_split_sub_le D.c (fun l l' ↦ tensorPairCount ρ D.f hh i x b l l')
      (fun l l' ↦ tensorPairMain D.f i l l') (tensorPairMain_comm D.f i) (𝓛 i) (scale (m + 1) x)
      (η / C) hsc.le he0.le fun l hl l' ↦ hXF i l l' x (hxX i l l') b hb hl
    rw [← hSdef] at habs
    rw [hsplit i, formJMarginal_eq_tensorPairMain]
    linarith [(abs_le.mp habs).1]
  have hsum := Finset.sum_le_sum fun (i : Fin (m + 1)) (_ : i ∈ Finset.univ) ↦ hstep i
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.sum_mul] at hsum
  push_cast at hsum
  have hfin : ((m : ℝ) + 1) * (3 * S ^ 2 * (η / C) * scale (m + 1) x) ≤ η * scale (m + 1) x := by
    calc ((m : ℝ) + 1) * (3 * S ^ 2 * (η / C) * scale (m + 1) x)
        = 3 * ((m : ℝ) + 1) * S ^ 2 * (η / C) * scale (m + 1) x := by ring
      _ ≤ C * (η / C) * scale (m + 1) x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) he0.le) hsc.le
      _ = η * scale (m + 1) x := by field_simp
  linarith [hsum, hfin]

/-- **The numerator lower bound with the split spelled out as `Gap212.Defs.LSet` and `USet`.**

`Gap212.Defs.LSet` and `USet` of the marginal predicate — a tensor index is *low* at `i` when its
`i`-omitted marginal is supported in `M⁻_k(j,i,ε₀)` — are the index sets `𝓙ᵢ` is evaluated at, and
with them the marginal clause of `Gap212.Sieve.SieveAsymptotic` is discharged by membership alone.
-/
theorem numeratorLowerBound_of_lset {p : SupportParams} {m : ℕ}
    (hasym : SieveAsymptotic m) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀' : ε₀ < 1) {j : Fin p.n}
    (hA : p.ε < p.A j.succ) (D : TensorDatum p (m + 1) j ε₀)
    {ρ : ℕ → ℝ → ℝ} {β : ℝ} (hρ : RhoHypotheses p ρ β)
    (hequi : HasEquidistributionOverQstarFamily p (fun n x ↦ ((ρ n x : ℝ) : ℂ)))
    {hh : Fin (m + 1) → ℕ} (hmono : StrictMono hh)
    (inMarg : Fin (m + 1) → Fin D.L → Prop) [∀ i, DecidablePred (inMarg i)]
    (hinMarg : ∀ (i : Fin (m + 1)) (l : Fin D.L), inMarg i l →
      ∀ t : Fin m → ℝ, (∀ s, 0 ≤ t s) → (∏ s, D.f l (i.succAbove s) (t s)) ≠ 0 →
        t ∈ marginalRegion p m j ε₀)
    {η : ℝ} (hη : 0 < η) :
    ∃ X : ℝ, ∀ x > X, ∀ b : ℕ, Defs.IsPreSieved b (W x) hh →
      (∑ i : Fin (m + 1), ∑ n ∈ dyadic x with n % W x = b % W x,
          nu D.L D.c D.f hh x n * ρ (n + hh i) x) ≥
        (∑ i : Fin (m + 1),
            formJMarginal D.c (gramBdry D.f i) (gramInnerSkip D.f i)
              (LSet (inMarg i)) (USet (inMarg i))) *
          scale (m + 1) x - η * scale (m + 1) x := by
  classical
  refine numeratorLowerBound_of_sieveAsymptotic hasym hε₀ hε₀' hA D hρ hequi hmono
    (𝓛 := fun i ↦ LSet (inMarg i)) (𝓤 := fun i ↦ USet (inMarg i)) (fun i ↦ ?_) (fun i l hl ↦ ?_) hη
  · ext l
    simp [LSet, USet]
  · exact hinMarg i l (Finset.mem_filter.mp hl).2

/-- **The numerator obligation reduces to the sieve asymptotic**:
`SieveAsymptotic m → NumeratorAsymptotic m`, the numerator obligation being
`Gap212.Sieve.SieveAsymptotic` plus bookkeeping. With `𝓛` and `𝓤` free the `Prop` would be expected
false: see the module docstring. -/
theorem numeratorAsymptotic_of_sieveAsymptotic {m : ℕ} (hasym : SieveAsymptotic m) :
    NumeratorAsymptotic m := fun _ _ hε₀ hε₀' _ hA D _ _ hρ hequi _ hmono _ _ hUc hmarg _ hη ↦
  numeratorLowerBound_of_sieveAsymptotic hasym hε₀ hε₀' hA D hρ hequi hmono hUc hmarg hη

end Gap212.Sieve
