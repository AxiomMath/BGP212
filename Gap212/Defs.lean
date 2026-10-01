/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Equidistribution.Basic
public import Gap212.Equidistribution.CoefficientSequence
public import Gap212.Sieve.Support
public import Gap212.Tuple.H45
public import Gap212.Notation
public import Gap212.Packing.Basic
public meta import Gap212.Attr

/-!
# The remaining vocabulary

The objects the argument introduces: the admissibility notions, the packing conditions as abstract
predicates, the extraction-leaf data, the discrete forms of the sieve weights, the modulus blocks
and chambers, and the minorant's hypothesis block.

Every one is a definition; the lemmas about them live with the arguments that use them.

## Conventions

The packing conditions are stated over an arbitrary linearly ordered field, matching
`Gap212.Packing.Xi`, because the tuples they quantify over are logarithmic sizes. The capacities
themselves are affine in the level and the datum's parameters, so each condition is a
partition-existence statement with explicit bounds.
-/

@[expose] public section

namespace Gap212.Defs

open Finset

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {ℓ : ℕ}

/-! ### Admissibility -/

/-- **An admissible tuple**: for every prime, the reductions omit a residue class. An alias of
the dependency's `Finset.Admissible`. -/
@[gap212 "def_admissible"]
abbrev Admissible (H : Finset ℕ) : Prop := H.Admissible

/-- **The diameter** of a finite set of integers, `max - min`. -/
@[gap212 "def_diameter"]
noncomputable abbrev diameter (H : Finset ℕ) : ℕ := H.diameter

/-- **A pre-sieved residue**: coprime to the pre-sieving modulus after every shift. It is what
makes the sieve's congruence classes primitive. -/
@[gap212 "def_badmissible"]
def IsPreSieved {k : ℕ} (b W : ℕ) (h : Fin k → ℕ) : Prop :=
  ∀ i : Fin k, Nat.Coprime (b + h i) W

/-! ### The four scalar conditions

These are the Type I, Type II and Type III conditions of [2, Proposition 3]: plain
inequalities among the datum's scalars, with no check set and no partition. They are stated here as
predicates in the parameters.

The conditions are discharged at `p_⋆` by `Gap212.scalar_conditions_at_datum`. -/

/-- **The scalar Type I condition**: `min{ξ₁ - 4A + 2/3, 9/7 - (34/7)A} - 2ϵ > δ`. -/
@[gap212 "def_scalar_condition_I"]
def ScalarConditionI (A δ ϵ ξ₁ : 𝕜) : Prop :=
  δ < min (ξ₁ - 4 * A + 2 / 3) (9 / 7 - (34 / 7) * A) - 2 * ϵ

/-- **The scalar Type II condition, first wall**: `19/2 - 36A - 13δ - 15ϵ ≥ 0`.

The `ϵ` enters with a minus sign, so the condition tightens as the slack grows. -/
@[gap212 "def_scalar_condition_II_first"]
def ScalarConditionIIFirst (A δ ϵ : 𝕜) : Prop :=
  0 ≤ 19 / 2 - 36 * A - 13 * δ - 15 * ϵ

/-- **The scalar Type II condition, cap walls**:
`min{ξ₂/10 - 32A/10 + 8/10, ξ₂/4 + 11/16 - 3A} - 2ϵ ≥ δ`. The binding one of the four at both
`Gap212.gap212Params` and Point A, with a slack of order `10⁻⁴`. -/
@[gap212 "def_scalar_condition_II_caps"]
def ScalarConditionIICaps (A δ ϵ ξ₂ : 𝕜) : Prop :=
  δ ≤ min (ξ₂ / 10 - 32 * A / 10 + 8 / 10) (ξ₂ / 4 + 11 / 16 - 3 * A) - 2 * ϵ

/-- **The scalar Type III condition**: `11/8 - (7/2)A - (9/8)ξ₃ - 2ϵ > δ`. -/
@[gap212 "def_scalar_condition_III"]
def ScalarConditionIII (A δ ϵ ξ₃ : 𝕜) : Prop :=
  δ < 11 / 8 - (7 / 2) * A - (9 / 8) * ξ₃ - 2 * ϵ

/-! ### The packing conditions

Each condition asserts that **every** rough profile in the check set admits a partition whose
block sums respect the given capacities. That existential over partitions is the content: a
condition asserting only that individual coordinates are small would be a different, and much
weaker, statement. The partition predicates come from `Gap212.Packing`. -/

/-- **Condition A**, the low-`γ` Type I condition: two blocks, capacities `ξ₁ - 2ε` and
`1/6 - 4ω - 2ε`. -/
@[gap212 "def_condition_A"]
def ConditionA (Ξ : Set (Fin ℓ → 𝕜)) (c₁ c₂ : 𝕜) : Prop :=
  ∀ y ∈ Ξ, Gap212.Packing.AdmitsPartition₂ y c₁ c₂

/-- **Condition A′**, the high-`γ` Type I condition. It is not among the conditions (A)–(E) of
[2, Proposition 3], although their proof uses it. -/
@[gap212 "def_condition_A_high"]
def ConditionAHigh (Ξ : Set (Fin ℓ → 𝕜)) (c₁ c₂ : 𝕜) : Prop :=
  ∀ y ∈ Ξ, Gap212.Packing.AdmitsPartition₂ y c₁ c₂

/-- **Condition B**, the Type IIa condition: two blocks. -/
@[gap212 "def_condition_B"]
def ConditionB (Ξ : Set (Fin ℓ → 𝕜)) (c₁ c₂ : 𝕜) : Prop :=
  ∀ y ∈ Ξ, Gap212.Packing.AdmitsPartition₂ y c₁ c₂

/-- **Condition C**, the Type IIb condition: three blocks. Its third capacity is the value at the
*left* endpoint of the `γ`-range, which is the true worst case since that capacity increases in
`γ`; [2, Proposition 3] states the right endpoint. -/
@[gap212 "def_condition_C"]
def ConditionC (Ξ : Set (Fin ℓ → 𝕜)) (c₁ c₂ c₃ : 𝕜) : Prop :=
  ∀ y ∈ Ξ, Gap212.Packing.AdmitsPartition₃ y c₁ c₂ c₃

/-- **Condition D**, the Type IIc condition: four blocks, quantified over the whole chamber of
levels and exponents. The one condition that cannot be discharged by putting everything in the
first bin, since its fourth capacity `8ω₀` vanishes at the endpoint. -/
@[gap212 "def_condition_D"]
def ConditionD (Ξ : Set (Fin ℓ → 𝕜)) (cap : 𝕜 → 𝕜 → Fin 4 → 𝕜) (chamber : Set (𝕜 × 𝕜)) : Prop :=
  ∀ p ∈ chamber, ∀ y ∈ Ξ,
    Gap212.Packing.AdmitsPartition₄ y (cap p.1 p.2 0) (cap p.1 p.2 1) (cap p.1 p.2 2)
      (cap p.1 p.2 3)

/-- **Condition E**, the Type III condition: two blocks. Its first capacity carries `8ε/3`, not the
`2ε` of [2, Proposition 3], because the Type III width `Gap212.Routing.widthIII` supplies only
that much. -/
@[gap212 "def_condition_E"]
def ConditionE (Ξ : Set (Fin ℓ → 𝕜)) (c₁ c₂ : 𝕜) : Prop :=
  ∀ y ∈ Ξ, Gap212.Packing.AdmitsPartition₂ y c₁ c₂

/-! ### The Type II setup -/

/-- **The Type II setup**: the shared hypothesis block of the Type IIa, IIb and IIc estimates —
both factors coefficient sequences at their scales, the second with Siegel–Walfisz, the product
commensurable with `x`, and the second scale below the half-power. -/
structure TypeIISetup (α β : ℕ → ℝ → ℂ) (M N : ℝ → ℝ) (G : Set ℝ) : Prop where
  alphaCoeff : IsCoefficientSequenceFamily α
  alphaScale : LocatedAtScaleFamily α M
  betaCoeff : IsCoefficientSequenceFamily β
  betaScale : LocatedAtScaleFamily β N
  betaSW : HasSiegelWalfiszFamily β N
  product : Gap212.Notation.AsympEq (fun x ↦ M x * N x) id
  betaSmall : ∀ x : ℝ, 1 < x → N x ≤ x ^ (1 / 2 : ℝ)
  exponent : ∀ x : ℝ, 1 < x → ∃ g ∈ G, N x = x ^ g

/-! ### Extraction leaves and transport -/

/-- **A factor-extraction leaf**: finitely many bin capacities, each affine in the level `θ`, given
by an intercept and a slope. The transport argument moves a partition valid at `θ = 1/2` to nearby
levels using only these two numbers per bin. -/
structure ExtractionLeaf (r : ℕ) where
  /-- The capacity of each bin at the half-level. -/
  intercept : Fin r → ℝ
  /-- The rate at which each capacity moves with the level. -/
  slope : Fin r → ℝ

/-- **The endpoint reserve** of a leaf against an assignment: the least slack in any bin at the
half-level. Positive reserve is what buys a transport radius. -/
noncomputable def endpointReserve {r : ℕ} (leaf : ExtractionLeaf r) (mass : Fin r → ℝ) : ℝ :=
  if h : 0 < r then
    Finset.univ.inf' (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp h))
      (fun i ↦ leaf.intercept i - mass i)
  else 0

/-- **The four endpoint capacities** of the Type IIc leaf at the half-level: `γ - 2d - ε`,
`1/2 - γ - ε`, `d - ε`, and `0`. The fourth being zero is what forces the fourth bin empty at the
endpoint. -/
@[gap212 "def_endpoint_capacities"]
noncomputable def endpointCapacities (γ d ε : ℝ) : Fin 4 → ℝ
  | 0 => γ - 2 * d - ε
  | 1 => 1 / 2 - γ - ε
  | 2 => d - ε
  | 3 => 0

/-! ### Modulus blocks and chambers -/

/-- **A dyadic modulus block** at level `ω₀`: the moduli of size `x^{1/2 + 2ω₀}` up to a factor
of two. The extraction argument is run per block because its windows depend on the level. -/
@[gap212 "def_dyadic_modulus_block"]
def dyadicBlock (x ω₀ : ℝ) : Set ℕ :=
  {q | x ^ (1 / 2 + 2 * ω₀) ≤ (q : ℝ) ∧ (q : ℝ) < 2 * x ^ (1 / 2 + 2 * ω₀)}

/-- **The endpoint range**: the blocks at level exactly `1/2`, where the extraction leaves are
constructed and from which the transition transports them. -/
def endpointRange (x : ℝ) : Set ℕ := dyadicBlock x 0

/-- **A positive-level chamber**: a compact region of parameter space with `ω₀ ≥ 0` on which one
fixed estimate is invoked. Compactness is what turns strict inequalities into a uniform margin. -/
structure PositiveLevelChamber where
  /-- The parameter region. -/
  carrier : Set (ℝ × ℝ × ℝ)
  /-- It is compact, which is what the uniform-margin argument needs. -/
  isCompact : IsCompact carrier
  /-- Its levels are nonnegative. -/
  nonneg : ∀ p ∈ carrier, 0 ≤ p.1

/-- **The decomposition pieces**: the finite index set of convolution pieces a sequence is split
into by the Heath-Brown decomposition, the smooth dyadic partitions, the residue subclasses and
the coprimality subdivisions. Only its cardinality matters, and only polylogarithmically. -/
structure DecompositionPieces (f : ℕ → ℝ → ℂ) (x : ℝ) where
  /-- How many pieces. -/
  card : ℕ
  /-- The pieces. -/
  piece : Fin card → (ℕ → ℝ → ℂ)
  /-- They reconstruct `f` pointwise. -/
  sums : ∀ n : ℕ, ∑ i : Fin card, piece i n x = f n x

/-! ### The discrete forms, and the minorant's hypotheses -/

/-- **The low index set** `𝓛(j,i)`: those tensor terms `l` for which the upper support endpoints of
the other factors sum below the retreated marginal cutoff, `∑_{s≠i} β_{l,s} < (1-ε₀)(A_j-ε)`.
That is what makes the `𝓙`-form's boundary evaluation apply to them: the term vanishes above
the cutoff.

The membership predicate is abstract here. It is **not** a support
containment for the tails `f_{l,s} = 𝒯g_{l,s}`: since `(𝒯g)(t) = ∫_t^∞ g` is the total mass at
every `t` below `supp g`, that support is a downward box unbounded below and no `l` would ever
qualify, making `𝓛(i)` empty and `𝓙ᵢ` zero. -/
@[gap212 "def_Lset"]
def LSet {L : ℕ} (inMarginal : Fin L → Prop) [DecidablePred inMarginal] : Finset (Fin L) :=
  Finset.univ.filter inMarginal

/-- **The high index set** `𝓤(j,i)`: the complement, the terms whose contribution below the
cutoff is discarded and bounded by the thin-strip estimate. -/
@[gap212 "def_Uset"]
def USet {L : ℕ} (inMarginal : Fin L → Prop) [DecidablePred inMarginal] : Finset (Fin L) :=
  Finset.univ.filter (fun l ↦ ¬ inMarginal l)

/-- **The high set really is the complement of the low set**, which is the form the numerator's
low/high split of `ν` consumes: `P + Q` is the *full* inner sum of the tensor weight exactly when
the two index sets partition. -/
theorem USet_eq_compl {L : ℕ} (inMarginal : Fin L → Prop) [DecidablePred inMarginal] :
    USet inMarginal = (LSet inMarginal)ᶜ := by
  ext l
  simp [LSet, USet]

/-- **The discrete energy** `𝓘`: the quadratic form the sieve's denominator evaluates to. -/
@[gap212 "def_form_calI"]
noncomputable def formI {L k : ℕ} (c : Fin L → ℝ) (inner : Fin L → Fin L → Fin k → ℝ) : ℝ :=
  ∑ l : Fin L, ∑ l' : Fin L, c l * c l' * ∏ s : Fin k, inner l l' s

/-- **The low–low group of the discrete marginal form.** One of the two groups of `𝓙ᵢ`, split out
because it is the one that is a quadratic form in its own right; `Gap212.Defs.formJMarginal` is
`𝓙ᵢ` itself, which is this plus twice the high–low group. -/
noncomputable def formJLowLow {L k : ℕ} (c : Fin L → ℝ) (bdry : Fin L → ℝ)
    (inner : Fin L → Fin L → Fin k → ℝ) (𝓛 : Finset (Fin L)) : ℝ :=
  ∑ l ∈ 𝓛, ∑ l' ∈ 𝓛, c l * c l' * bdry l * bdry l' * ∏ s : Fin k, inner l l' s

/-- **The discrete marginal form** `𝓙ᵢ`: the numerator's main term, carrying the boundary values of
the singled-out coordinate. The low–low group **plus twice the high–low group**.

The cross term is not optional, and dropping it is not a weakening but a different quantity. `𝓙ᵢ`
evaluates on a tensor datum as `∫ (Γᵢ² - Γ_{i,𝓤}²)`, and with `Γᵢ = Γ_{i,𝓛} + Γ_{i,𝓤}`
pointwise that integrand is `Γ_{i,𝓛}² + 2Γ_{i,𝓛}Γ_{i,𝓤}` — the low–low group and twice the
high–low one. -/
@[gap212 "def_form_calJ"]
noncomputable def formJMarginal {L k : ℕ} (c : Fin L → ℝ) (bdry : Fin L → ℝ)
    (inner : Fin L → Fin L → Fin k → ℝ) (𝓛 𝓤 : Finset (Fin L)) : ℝ :=
  formJLowLow c bdry inner 𝓛 +
    2 * ∑ l ∈ 𝓤, ∑ l' ∈ 𝓛, c l * c l' * bdry l * bdry l' * ∏ s : Fin k, inner l l' s

/-- **A generated factorization**: the data witnessing that a modulus lies in the generated family
— a smooth part, the rough factors on each side, and the prime list of the smooth part. The
extraction lemmas consume this rather than the bare membership, since they move its pieces. -/
@[gap212 "def_generated_factorization"]
structure GeneratedFactorization (m m' : ℕ) where
  /-- The smooth part contributed by the first side. -/
  e : ℕ
  /-- The smooth part contributed by the second side. -/
  e' : ℕ
  /-- The rough factors of the first side. -/
  f : Fin m → ℕ
  /-- The rough factors of the second side. -/
  f' : Fin m' → ℕ
  /-- The primes of the smooth part, with multiplicity. -/
  smoothPrimes : List ℕ
  /-- They multiply to the smooth part. -/
  smoothPrimes_prod : smoothPrimes.prod = e * e'

/-- **The minorant's hypothesis block**: what the sieve criterion needs of `ρ` beyond being a
minorant — finite support in the block, no small prime factors in that support, and a density
asymptotic.

**There are no deficit parameters.** At `ξ₂ = 2/5` the reduction's minorant is `1_ℙ` itself, and a
density loss or a pointwise floor `-c₂ ≤ ρ` would commit the retreat construction to controlling a
third quadratic form `𝓚` for which it has no argument. The lower bound is `0 ≤ ρ`, which is what
makes the group of tensor pairs the numerator omits non-negative — the one place the sign of the
minorant is used.

**The equidistribution clause is not a field.** The full hypothesis block has five clauses, and
the fourth is equidistribution over `𝒬*` at `ρ(·;x)`. That is
`Gap212.HasEquidistributionOverQstarFamily`, which lives downstream of this file, so it is carried
as a separate hypothesis of `Gap212.Sieve.GPYSieve` rather than inlined here; the conjunction is
the same.

**Admissibility is indexed by the support datum, and that is not decoration.** Admissibility of
`ρ` is for a pair `(β, T)`, with `T = T_k(p)`, and its roughness requirement reads "every prime
factor of `n` exceeds `x^β`, **for some `β > max_j B_{j,1}`**". That inequality is the clause the
asymptotics argument spends: it forces `d_{i₀} = d'_{i₀} = 1` by playing roughness, which gives
`log_x d_{i₀} > β`, against `Gap212.GPY.lt_B_one_of_mem_retreatRegion`, which gives
`log_x d_{i₀} < B_{j,1}`; the two contradict each other only when `B_{j,1} ≤ β`. Nothing else
supplies it: `Gap212.SupportParams` places *no* upper bound on `B` at all — its chain
`δ < B_{j,m} ≤ B_{j,m+1} ≤ B_{j,m} + δ` is unbounded above — so the inequality is a constraint on
the pair `(p, β)` that has to be assumed, and at `Gap212.gap212Params` it holds with room, the
first rung being `777/5000`. Unlike the equidistribution clause there is no import obstruction
here: `Gap212.SupportParams` is upstream of this file, so the clause belongs in the structure. -/
@[gap212 "def_rho_hypotheses"]
structure RhoHypotheses (p : SupportParams) (ρ : ℕ → ℝ → ℝ) (β : ℝ) : Prop where
  /-- Supported in the dyadic block.
  Without this the unrestricted discrepancy the equidistribution clause sums is not a finite sum,
  and the remaining clauses say nothing whatever about `ρ` off the block. -/
  support : ∀ x : ℝ, ∀ n : ℕ, n ∉ dyadic x → ρ n x = 0
  /-- Between `0` and the prime indicator. -/
  minorant : ∀ x : ℝ, 1 < x → ∀ n ∈ dyadic x, 0 ≤ ρ n x ∧ ρ n x ≤ (if n.Prime then 1 else 0)
  /-- Supported, *within the block*, on integers whose prime factors all exceed `x^β`.

  The restriction to `n ∈ dyadic x` is not decoration. Without it the condition quantifies over
  every `n`, and the sequence the paper actually applies the criterion to — the prime indicator —
  fails it outright: `1_ℙ(2) ≠ 0` while `x^β > 2` for every large `x`. Read on the block
  (`1_ℙ(n) ≠ 0` means `n` is prime *and* `n ≥ x`), and the sieve never evaluates `ρ` off the
  block, so this is both the faithful form and the only satisfiable one. -/
  rough : ∀ x : ℝ, 1 < x → ∀ n ∈ dyadic x, ρ n x ≠ 0 → ∀ q : ℕ, q.Prime → q ∣ n → x ^ β < (q : ℝ)
  /-- The rough exponent clears every first rung of the cap row, `β > max_j B_{j,1}`.

  This is the half of the roughness requirement that refers to the support datum, and it is
  what makes the roughness usable: see the structure's docstring. -/
  rough_exceeds_cap : ∀ j : Fin p.n, p.B j 1 < β
  /-- Its density over the block is `(1 + o(1)) x / log x`. -/
  density : ∀ ε > (0 : ℝ), ∃ X : ℝ, ∀ x > X,
    |(∑ n ∈ dyadic x, ρ n x) - x / Real.log x| ≤ ε * x / Real.log x

end Gap212.Defs
