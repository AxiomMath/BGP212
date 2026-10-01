/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Gap212.Attr
public import Gap212.Packing.Basic
public import Mathlib.Data.Rat.BigOperators

/-!
# Rational certificates for the factor-packing conditions

Proposition 3 of Stadlmann's *Bounded gaps between primes* asks, of each of six bin conditions (its
five lettered conditions and the condition (A′) of `Gap212.Packing.conditionA'`) and each pair
`(m, m')` of rough-factor counts, that every tuple `y` of rough logarithms in the check set
`Ξ(B_{j,m}, B_{j',m'}, m, m', δ)` split its coordinates into bins whose sums obey prescribed
capacities. At a fixed datum that is a finite verification, and this file supplies the two facts
that make it finite and exact: what certifies one pair, and which pairs need certifying at all.

Fixing an assignment of coordinates to bins turns each requirement into a single *affine*
inequality in `y`, and the check set is itself cut out by affine inequalities — `δ ≤ y i`,
`y i ≤ 1`, and the two group-sum caps. All of their coefficients are exact rationals, while `y`
ranges over the reals, its coordinates being logarithmic sizes `y i = log_x f i`. So one pair and
one condition present a finite family of affine implications between finite systems of affine
inequalities over `ℚ`, tested at real points. For such data the implication "the system forces the
inequality", tested over an arbitrary linearly ordered field, holds exactly when one of two pieces
of rational data exists: a nonnegative rational vector `lam` exhibiting the target's linear part as
the combination `∑ t, lam t • (linear part of the t-th constraint)` and its constant as at least
`∑ t, lam t * (constant of the t-th constraint)` — a *dual vector*, which proves the inequality
throughout the cell by weak duality; or a nonnegative rational vector whose combination has zero
linear part and negative constant — a *Farkas vector*, which proves the cell empty. These are the
two possible verdicts on a terminal cell of the subdivision, and the rationality is the point: both
certificates live in `ℚ` while the tested tuples live in `ℝ`, so checking a cell is a finite exact
rational computation whose conclusion is valid over `ℝ`.

Both counts may be `0` — the moduli a support generates run over `m, m' ≥ 0`, so the conditions are
demanded at the degenerate pairs too — and those pairs need no separate verification. A tuple with
an empty second side is the restriction of a tuple at the adjacent pair `(m, 1)`: adjoin one
coordinate of size exactly `δ`. The adjoined coordinate lies in `[δ, 1]` as soon as `δ ≤ 1`, and it
is the whole of the second side, so the second cap is respected as soon as `δ ≤ B'_1` — which is
the support datum's own `δ < B_{j,1}`. The first side is untouched, so the first cap carries over
verbatim. Reading back the bins of the enlarged tuple and discarding the adjoined coordinate from
whichever bin received it lowers that bin's sum and leaves the others alone, since the discarded
mass `δ` is nonnegative; so every bin inequality survives. The mirrored argument adjoins the
coordinate to an empty first side, using `δ ≤ B_1`. The doubly degenerate pair `(0, 0)` is covered
as well, and needs no extra hypothesis: its index set is empty, so each of its bin sums is the
empty sum `0`, and each capacity is nonnegative because the check set at `(1, 1)` contains the
constant tuple `δ`.

## Main results

* `Gap212.Packing.forall_affine_nonneg_iff_exists_dual_or_farkas`: a finite rational affine system
  forces a rational affine inequality over a linearly ordered field if and only if the system
  admits a nonnegative rational dual vector for that inequality, or a rational Farkas vector.
* `Gap212.Packing.exists_bins_empty_side_of_exists_bins_one`: the bin condition at every pair with
  an empty rough side — `(m, 0)`, `(0, m')` and `(0, 0)` — follows from the bin condition at the
  pairs `(m, 1)` and `(1, m')` with the other side nonempty.
* `Gap212.Packing.admitsPartition₂_iff_exists_bins` and its three- and four-bin analogues: the bin
  condition at `r = 2, 3, 4` bins is the block-partition predicate of the six conditions.

## Implementation notes

**What of the subdivision procedure is stated.** The verification is a procedure: subdivide
whenever a proposed bin inequality changes sign, obtaining a finite binary tree whose internal
nodes have two children cut out by an affine inequality and its reverse, and certify each terminal
cell. The children cover the parent because `le_total` gives `0 ≤ f y ∨ f y ≤ 0` for every affine
`f` and every `y`; this needs no hypothesis and is not stated here. The tree is finite because the
proposed bin inequalities are finite in number — there are `r ^ (m + m')` assignments of
coordinates to `r` bins, and each subdivision consumes one — so a node's cell is cut out by
finitely many affine inequalities, which is the `Fintype T` below. What is left, and what is
stated, is the verdict on one cell and one inequality.

**The certificate lemma is stated over arbitrary finite index types**, rather than over
`Fin (m + m')` and the particular constraint list of `Gap212.Packing.Xi`. Generality costs nothing
and buys the instantiations the verification needs: the constraints of a cell are those of the
check set *together with* the sign cuts made on the path down to it, the target is a bin inequality
`∑ i ∈ I, y i ≤ cap` — that is `c = cap`, `a i = -1` for `i ∈ I` and `a i = 0` otherwise — and both
lists change from cell to cell and from condition to condition. Condition D's continuous
`(γ, ω₀)`-range is accommodated the same way, by carrying `γ` and `ω₀` as two further coordinates
of `y` with their range as two further constraints. Concretely, at Point A, where
`Gap212.PointA.δ = 179/10000`, with `m = m' = 1` and both cap rows at `B₁ = 31/200`, the dual
vector taking the value `1` on the two group-sum constraints and `0` on the range constraints
certifies `y 0 + y 1 ≤ cap` for every capacity `cap ≥ 31/100`.

**Both directions of the certificate lemma are asserted**, and the reverse is the one the
verification runs on. The forward direction is the affine ("inhomogeneous") Farkas lemma, and it is
what makes the certificate search complete: a cell on which a bin inequality is true and which the
search fails to certify cannot exist. Mathlib has Farkas' lemma only in its geometric form for
proper cones in a topological real vector space (`ProperCone.hyperplane_separation`), from which
the finite rational form with the tested field left free does not follow; the Fourier–Motzkin
elimination is therefore carried out here. The two disjuncts are not exclusive, and are
deliberately not made so: a cell that is empty has both a Farkas vector and, for every target, a
dual vector.

**One statement for all six bin conditions.** Conditions A, A′, B, C, D and E differ only in how
many bins they use and what the capacities are; the count is `2`, `2`, `2`, `3`, `4`, `2`. So the
condition is phrased below for an arbitrary number of bins `r` and an arbitrary capacity vector
`c : Fin r → 𝕜`, as the existence of an assignment `f : Fin ℓ → Fin r` with `∑_{f i = k} y i ≤ c k`
for every bin `k`. At `r = 2, 3, 4` that is `Gap212.Packing.AdmitsPartition₂`, `₃`, `₄`, which is
what `admitsPartition₂_iff_exists_bins` and its analogues prove: the blocks are the fibres of `f`,
and the complement block is the last fibre. So each of the six conditions is an instance, condition
D by fixing a point of its chamber first, its chamber quantifier standing outside the capacities.

**The reduction's hypothesis is at `(m, 1)` and `(1, m')`.** The condition at the pairs `(1, m)`
alone does not give it at every `(m, 0)`: emptying the second side adjoins a coordinate there, so
it is the condition at `(m, 1)` that is consumed, and `Ξ(B_m, B'_1, m, 1, δ)` is not
`Ξ(B_1, B'_m, 1, m, δ)` unless the two cap rows agree. They do agree at the chosen datum, where
`n = 1` forces `j = j' = 1` and hence `B = B'`; for a support datum with `n > 1` and `j ≠ j'` they
need not. Both the hypothesis and its mirror are therefore assumed, and the two sides of the
conclusion are derived one from each.

**The reduction assumes neither nonnegative capacities nor a monotone cap row.** Nonnegativity of
the capacities, which would discharge `(0, 0)` directly, is not assumed: it follows from the
hypothesis at `(1, 1)`, whose check set is nonempty under the same three inequalities on `δ`. The
monotonicity `B_m ≤ B_{m+1} ≤ B_m + δ` of a cap row is not used
either: only the single value `B_1` of each row is compared with `δ`, because the side that grows
is the empty one and the side capped by `B_m` never changes. For the same reason `B' 0` is left
free rather than set to `0`, as the datum has it: with no coordinate above index `m` the second
group sum at `(m, 0)` is `0`, so the second cap is inert there.

## References

* J. Stadlmann, *Bounded gaps between primes*, https://arxiv.org/abs/2608.31126: Definition 10
  for the check set `Ξ(B₁, B₂, m₁, m₂, δ)` and Proposition 3 for the bin conditions, whose pairs
  `(m, m')` range over all counts with `m + m' > 0`.
-/

public section

namespace Gap212.Packing

open Finset

universe u

/-! ## The algebra of the row value `b + ∑ i, g i * y i` -/

/-- A nonnegative combination of rows, evaluated at a point: the linear parts combine. -/
private lemma sum_weighted_rows {R T ι : Type*} [CommSemiring R] [Fintype T] [Fintype ι]
    (lam : T → R) (G : T → ι → R) (y : ι → R) :
    ∑ i, (∑ t, lam t * G t i) * y i = ∑ t, lam t * ∑ i, G t i * y i := by
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- The value of the combination `al • p + be • q` of two rows is the combination of their
values. -/
private lemma affine_combination {ι : Type*} [Fintype ι] (al be bp bq : ℚ) (g h y : ι → ℚ) :
    al * bp + be * bq + ∑ i, (al * g i + be * h i) * y i
      = al * (bp + ∑ i, g i * y i) + be * (bq + ∑ i, h i * y i) := by
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

/-- The value of a row along the line `y + L • u` is affine in `L`. -/
private lemma affine_add_smul {ι : Type*} [Fintype ι] (bt L : ℚ) (g y u : ι → ℚ) :
    bt + ∑ i, g i * (y i + L * u i) = bt + ∑ i, g i * y i + L * ∑ i, g i * u i := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, add_assoc, mul_left_comm]

/-- The value of a row at the rescaled point `s⁻¹ • Y` is `s⁻¹` times its homogenised value. -/
private lemma affine_inv_smul {ι : Type*} [Fintype ι] {s : ℚ} (hs : s ≠ 0) (bt : ℚ) (g Y : ι → ℚ) :
    bt + ∑ i, g i * (s⁻¹ * Y i) = s⁻¹ * (bt * s + ∑ i, g i * Y i) := by
  simp only [mul_add, Finset.mul_sum, mul_comm bt s, inv_mul_cancel_left₀ hs, mul_left_comm s⁻¹]

/-- Pulling a combination of the paired rows back to a combination of the original rows: the weight
on the original row `t` is the total weight the combination puts on the pairs in which `t` occurs,
and pairing it with any row datum `v` gives the same value as before. -/
private lemma sum_pullback_mul {T : Type*} [Fintype T] (al be : T → T → ℚ) (lam : T × T → ℚ)
    (v : T → ℚ) :
    ∑ t, ((∑ q, lam (t, q) * al t q) + ∑ p, lam (p, t) * be p t) * v t
      = ∑ x, lam x * (al x.1 x.2 * v x.1 + be x.1 x.2 * v x.2) := by
  simp only [Fintype.sum_prod_type, add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_add,
    mul_assoc]
  rw [Finset.sum_comm (f := fun p t ↦ lam (p, t) * (be p t * v t))]

/-! ## Fourier–Motzkin elimination -/

/-- The cancelled pair inequality `0 ≤ -v * s + u * w` says precisely that the lower bound `-s / u`
it comes from does not exceed the upper bound `-w / v`. -/
private lemma neg_div_le_neg_div_of_cancel {u v s w : ℚ} (hu : 0 < u) (hv : v < 0)
    (h : 0 ≤ -v * s + u * w) : -s / u ≤ -w / v := by
  rw [le_div_iff_of_neg hv, div_mul_eq_mul_div, le_div_iff₀ hu]
  linarith

/-- A value separating the lower bounds `-F p / d p` from the upper bounds `-F q / d q` exists as
soon as every lower bound is at most every upper bound, which is what the paired rows of the
eliminated system say. Where there is no upper bound at all, any value past every lower bound
serves. -/
private lemma exists_add_mul_nonneg {T : Type u} [Finite T] (F d : T → ℚ)
    (hpair : ∀ p q, 0 < d p → d q < 0 → 0 ≤ -d q * F p + d p * F q)
    (hzero : ∀ t, d t = 0 → 0 ≤ F t) :
    ∃ z : ℚ, ∀ t, 0 ≤ F t + d t * z := by
  obtain ⟨_⟩ := nonempty_fintype T
  suffices h : ∃ z : ℚ, (∀ t, 0 < d t → -F t / d t ≤ z) ∧ ∀ t, d t < 0 → z ≤ -F t / d t by
    obtain ⟨z, hlo, hhi⟩ := h
    refine ⟨z, fun t ↦ ?_⟩
    rcases lt_trichotomy (d t) 0 with h | h | h
    · linarith [(le_div_iff_of_neg h).1 (hhi t h)]
    · simpa [h] using hzero t h
    · linarith [(div_le_iff₀ h).1 (hlo t h)]
  by_cases hU : (univ.filter fun t ↦ d t < 0).Nonempty
  · exact ⟨(univ.filter fun t ↦ d t < 0).inf' hU fun t ↦ -F t / d t,
      fun p hp ↦ Finset.le_inf' _ _ fun q hq ↦
        neg_div_le_neg_div_of_cancel hp (by simpa using hq) (hpair p q hp (by simpa using hq)),
      fun t ht ↦ Finset.inf'_le _ (by simp [ht])⟩
  by_cases hP : (univ.filter fun t ↦ 0 < d t).Nonempty
  · exact ⟨(univ.filter fun t ↦ 0 < d t).sup' hP fun t ↦ -F t / d t,
      fun t ht ↦ Finset.le_sup' (fun t ↦ -F t / d t) (by simp [ht]),
      fun t ht ↦ (hU ⟨t, by simp [ht]⟩).elim⟩
  · exact ⟨0, fun t ht ↦ (hP ⟨t, by simp [ht]⟩).elim, fun t ht ↦ (hU ⟨t, by simp [ht]⟩).elim⟩

/-- The weights of the pair row of Fourier–Motzkin elimination, for two rows whose coefficients at
the variable being eliminated are `u` and `v`: nonnegative weights cancelling that variable, equal
to `(-v, u)` when the pair straddles zero — so that the row becomes "lower bound ≤ upper bound" —
and to `(1, 0)` when `u` vanishes, so that a row not involving the variable survives
elimination. -/
private lemma exists_elim_weights (u v : ℚ) :
    ∃ al be : ℚ, 0 ≤ al ∧ 0 ≤ be ∧ al * u + be * v = 0 ∧ (u = 0 → al = 1 ∧ be = 0) ∧
      (0 < u → v < 0 → al = -v ∧ be = u) := by
  rcases eq_or_ne u 0 with hu | hu
  · exact ⟨1, 0, zero_le_one, le_rfl, by simp [hu], fun _ ↦ ⟨rfl, rfl⟩,
      fun h ↦ absurd h (by simp [hu])⟩
  by_cases h : 0 < u ∧ v < 0
  · exact ⟨-v, u, by linarith [h.2], h.1.le, by ring, fun h₀ ↦ absurd h₀ hu, fun _ _ ↦ ⟨rfl, rfl⟩⟩
  · exact ⟨0, 0, le_rfl, le_rfl, by ring, fun h₀ ↦ absurd h₀ hu, fun h₁ h₂ ↦ absurd ⟨h₁, h₂⟩ h⟩

/-- **Fourier–Motzkin elimination.** A finite system of affine inequalities with rational
coefficients either has a rational solution, or some nonnegative rational combination of its rows
has zero linear part and negative constant.

The induction is on the number of variables. Eliminating the last variable, whose coefficient on
the row `t` is `d t`, the new system has one row for each *pair* `(p, q)` of old rows, namely the
combination `al p q • p + be p q • q` of the weights `exists_elim_weights` provides. A solution of
the new system extends by any value separating the lower bounds from the upper bounds
(`exists_add_mul_nonneg`), and a Farkas combination of the new system pulls back to one of the old
(`sum_pullback_mul`). -/
private lemma exists_solution_or_farkas :
    ∀ (n : ℕ) {T : Type u} [Fintype T] (b : T → ℚ) (G : T → Fin n → ℚ),
      (∃ y : Fin n → ℚ, ∀ t, 0 ≤ b t + ∑ i, G t i * y i) ∨
        ∃ lam : T → ℚ, (∀ t, 0 ≤ lam t) ∧ (∀ i, ∑ t, lam t * G t i = 0) ∧
          ∑ t, lam t * b t < 0 := by
  intro n
  induction n with
  | zero =>
    intro T _ b G
    classical
    by_cases h : ∀ t, 0 ≤ b t
    · exact Or.inl ⟨0, by simpa using h⟩
    obtain ⟨t₀, ht₀⟩ := not_forall.mp h
    refine Or.inr ⟨fun t ↦ if t = t₀ then 1 else 0, fun t ↦ ?_, fun i ↦ i.elim0, ?_⟩
    · by_cases ht : t = t₀ <;> simp [ht]
    · simpa using not_le.mp ht₀
  | succ n ih =>
    intro T _ b G
    choose al be hal hbe hcancel hkeep hstraddle using
      fun p q : T ↦ exists_elim_weights (G p (Fin.last n)) (G q (Fin.last n))
    rcases ih (fun pq : T × T ↦ al pq.1 pq.2 * b pq.1 + be pq.1 pq.2 * b pq.2)
        (fun (pq : T × T) (i : Fin n) ↦
          al pq.1 pq.2 * G pq.1 i.castSucc + be pq.1 pq.2 * G pq.2 i.castSucc) with
      ⟨y, hy⟩ | ⟨lam, hlam0, hlamG, hlamb⟩
    · obtain ⟨z, hz⟩ := exists_add_mul_nonneg (fun t ↦ b t + ∑ i, G t i.castSucc * y i)
        (fun t ↦ G t (Fin.last n))
        (fun p q hp hq ↦ by simpa only [hstraddle p q hp hq, affine_combination] using hy (p, q))
        fun t ht ↦ by simpa [hkeep t t ht, affine_combination] using hy (t, t)
      refine Or.inl ⟨Fin.snoc y z, fun t ↦ ?_⟩
      simpa [Fin.sum_univ_castSucc, add_assoc] using hz t
    · refine Or.inr ⟨fun t ↦ (∑ q, lam (t, q) * al t q) + ∑ p, lam (p, t) * be p t,
        fun t ↦ add_nonneg (Finset.sum_nonneg fun q _ ↦ mul_nonneg (hlam0 _) (hal _ _))
          (Finset.sum_nonneg fun p _ ↦ mul_nonneg (hlam0 _) (hbe _ _)), fun i ↦ ?_, ?_⟩
      · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · exact (sum_pullback_mul al be lam fun t ↦ G t j.castSucc).trans (hlamG j)
        · simp [sum_pullback_mul al be lam fun t ↦ G t (Fin.last n), hcancel]
      · exact (sum_pullback_mul al be lam b).trans_lt hlamb

/-! ## Homogenisation -/

/-- A solution `(Y, s)` of the homogenised system gives a point of a nonempty cell at which the
target is negative: for `s > 0` the rescaled point `s⁻¹ • Y`, and for `s = 0` a point far enough
along the direction `Y` from a point `y₀` of the cell, since `Y` decreases the target and violates
no constraint. -/
private lemma exists_point_neg_of_homogeneous {T : Type u} {n : ℕ} (b : T → ℚ)
    (G : T → Fin n → ℚ) (c : ℚ) (a : Fin n → ℚ) {y₀ Y : Fin n → ℚ} {s : ℚ}
    (hy₀ : ∀ t, 0 ≤ b t + ∑ i, G t i * y₀ i) (hs : 0 ≤ s)
    (hrow : ∀ t, 0 ≤ b t * s + ∑ i, G t i * Y i)
    (htar : c * s + ∑ i, a i * Y i ≤ -1) :
    ∃ y : Fin n → ℚ, (∀ t, 0 ≤ b t + ∑ i, G t i * y i) ∧ c + ∑ i, a i * y i < 0 := by
  rcases eq_or_lt_of_le hs with rfl | hspos
  · have hL : (0 : ℚ) ≤ |c + ∑ i, a i * y₀ i| + 1 := by positivity
    refine ⟨fun i ↦ y₀ i + (|c + ∑ i, a i * y₀ i| + 1) * Y i, fun t ↦ ?_, ?_⟩
    · rw [affine_add_smul]
      linarith [hy₀ t, mul_nonneg hL (by linarith [hrow t] : (0 : ℚ) ≤ ∑ i, G t i * Y i)]
    · rw [affine_add_smul]
      linarith [mul_le_mul_of_nonneg_left (by linarith : ∑ i, a i * Y i ≤ -1) hL,
        le_abs_self (c + ∑ i, a i * y₀ i)]
  · refine ⟨fun i ↦ s⁻¹ * Y i, fun t ↦ ?_, ?_⟩
    · rw [affine_inv_smul hspos.ne']
      exact mul_nonneg (by positivity) (hrow t)
    · rw [affine_inv_smul hspos.ne']
      exact mul_neg_of_pos_of_neg (inv_pos.mpr hspos) (by linarith)

/-- Dividing by the weight on the target row: a nonnegative vector whose combination reproduces
`sig` times the target datum, with `sig > 0`, gives a dual vector. -/
private lemma exists_dual_of_scaled {T : Type u} [Fintype T] {ι : Type*} (b : T → ℚ)
    (G : T → ι → ℚ) (c : ℚ) (a : ι → ℚ) {lam : T → ℚ} {sig : ℚ} (hsig : 0 < sig)
    (h0 : ∀ t, 0 ≤ lam t) (hG : ∀ i, ∑ t, lam t * G t i = sig * a i)
    (hb : ∑ t, lam t * b t ≤ sig * c) :
    ∃ mu : T → ℚ, (∀ t, 0 ≤ mu t) ∧ (∀ i, ∑ t, mu t * G t i = a i) ∧ ∑ t, mu t * b t ≤ c := by
  have key : ∀ v : T → ℚ, ∑ t, sig⁻¹ * lam t * v t = sig⁻¹ * ∑ t, lam t * v t := fun v ↦ by
    simp [Finset.mul_sum, mul_assoc]
  refine ⟨fun t ↦ sig⁻¹ * lam t, fun t ↦ mul_nonneg (by positivity) (h0 t), fun i ↦ ?_, ?_⟩
  · rw [key, hG i, inv_mul_cancel_left₀ hsig.ne']
  · rwa [key, inv_mul_le_iff₀ hsig]

/-- Summing over the rows of the homogenised system: those of the cell, the sign row `0 ≤ s`, and
the negated target. -/
private lemma sum_homogenised {T : Type u} [Fintype T] (f : T ⊕ Unit ⊕ Unit → ℚ) :
    ∑ x, f x = ∑ t, f (Sum.inl t) + f (Sum.inr (Sum.inl ())) + f (Sum.inr (Sum.inr ())) := by
  simp [Fintype.sum_sum_type, ← add_assoc]

/-- The affine Farkas lemma over `ℚ`, for coordinates indexed by `Fin n`: if a finite rational
affine system forces a further rational affine inequality at every rational point, then either a
nonnegative rational dual vector exhibits the inequality as a consequence of the system, or a
nonnegative rational Farkas vector shows the system unsolvable.

If the system is solvable, the system `0 ≤ s`, `0 ≤ b t * s + ∑ i, G t i * y i`,
`0 ≤ -1 - c * s - ∑ i, a i * y i` in the variables `(y, s)` is unsolvable by
`exists_point_neg_of_homogeneous`; a Farkas combination of it has positive weight on the last row,
and dividing by that weight yields the dual vector. -/
private lemma exists_dual_or_farkas_fin {T : Type u} [Fintype T] {n : ℕ} (b : T → ℚ)
    (G : T → Fin n → ℚ) (c : ℚ) (a : Fin n → ℚ)
    (H : ∀ y : Fin n → ℚ, (∀ t, 0 ≤ b t + ∑ i, G t i * y i) → 0 ≤ c + ∑ i, a i * y i) :
    (∃ lam : T → ℚ, (∀ t, 0 ≤ lam t) ∧ (∀ i, ∑ t, lam t * G t i = a i) ∧
        ∑ t, lam t * b t ≤ c) ∨
      ∃ lam : T → ℚ, (∀ t, 0 ≤ lam t) ∧ (∀ i, ∑ t, lam t * G t i = 0) ∧
        ∑ t, lam t * b t < 0 := by
  refine (exists_solution_or_farkas n b G).elim (fun ⟨y₀, hy₀⟩ ↦ ?_) Or.inr
  rcases exists_solution_or_farkas (n + 1)
      (Sum.elim (fun _ : T ↦ (0 : ℚ))
        (Sum.elim (fun _ : Unit ↦ (0 : ℚ)) fun _ : Unit ↦ (-1 : ℚ)))
      (Sum.elim (fun t : T ↦ Fin.snoc (G t) (b t))
        (Sum.elim (fun _ : Unit ↦ Fin.snoc 0 1)
          fun _ : Unit ↦ Fin.snoc (fun i ↦ -a i) (-c))) with ⟨Y, hY⟩ | h
  · -- the cell is nonempty and forces the target, so the homogenised system has no solution
    have hs := hY (Sum.inr (Sum.inl ()))
    have htar := hY (Sum.inr (Sum.inr ()))
    have hrow := fun t ↦ hY (Sum.inl t)
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
      one_mul, neg_mul, Finset.sum_neg_distrib] at hs htar hrow
    obtain ⟨y, hy, hlt⟩ := exists_point_neg_of_homogeneous b G c a hy₀ hs
      (fun t ↦ by linarith [hrow t]) (by linarith)
    linarith [H y hy]
  · obtain ⟨lam, hlam0, hlamG, hlamb⟩ := h
    rw [sum_homogenised] at hlamb
    simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, zero_add,
      mul_neg, mul_one] at hlamb
    have hsig : 0 < lam (Sum.inr (Sum.inr ())) := by linarith
    have hlast := hlamG (Fin.last n)
    rw [sum_homogenised] at hlast
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.snoc_last, mul_one, mul_neg] at hlast
    have hG : ∀ j : Fin n, ∑ t, lam (Sum.inl t) * G t j
        = lam (Sum.inr (Sum.inr ())) * a j := fun j ↦ by
      have h₁ := hlamG j.castSucc
      rw [sum_homogenised] at h₁
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.snoc_castSucc, Pi.zero_apply, mul_zero,
        mul_neg] at h₁
      linarith
    exact Or.inl (exists_dual_of_scaled b G c a hsig (fun t ↦ hlam0 _) hG
      (by linarith [hlam0 (Sum.inr (Sum.inl ()))]))

/-! ## Transfer to an arbitrary finite index type and an arbitrary linearly ordered field -/

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **Weak duality.** At a point of the cell, the combination of the rows with nonnegative rational
weights `lam` is nonnegative. -/
private lemma sum_nonneg_of_mem_cell {ι T : Type*} [Fintype ι] [Fintype T] (b : T → ℚ)
    (G : T → ι → ℚ) (lam : T → ℚ) (h0 : ∀ t, 0 ≤ lam t) {y : ι → 𝕜}
    (hy : ∀ t, 0 ≤ (b t : 𝕜) + ∑ i, (G t i : 𝕜) * y i) :
    0 ≤ ((∑ t, lam t * b t : ℚ) : 𝕜) + ∑ i, ((∑ t, lam t * G t i : ℚ) : 𝕜) * y i := by
  push_cast
  rw [sum_weighted_rows, ← Finset.sum_add_distrib]
  exact Finset.sum_nonneg fun t _ ↦ by
    rw [← mul_add]; exact mul_nonneg (by exact_mod_cast h0 t) (hy t)

/-- **Bin capacities have a rational polyhedral certificate.** Let `b`, `G` present a finite
system of affine inequalities `0 ≤ b t + ∑ i, G t i * y i` with rational coefficients — a cell of
the subdivided check set — and let `c`, `a` present a further rational affine inequality
`0 ≤ c + ∑ i, a i * y i`, a bin inequality. Over any linearly ordered field `𝕜`, the system forces
the inequality if and only if either

* there is a nonnegative rational `lam` with `∑ t, lam t * G t i = a i` for every coordinate `i`
  and `∑ t, lam t * b t ≤ c` — a dual vector, proving the inequality throughout the cell; or
* there is a nonnegative rational `lam` with `∑ t, lam t * G t i = 0` for every `i` and
  `∑ t, lam t * b t < 0` — a Farkas vector, proving the cell empty.

The reverse direction is weak duality,
`c + ∑ a i * y i ≥ ∑ t, lam t * (b t + ∑ i, G t i * y i) ≥ 0`. The forward direction is the affine
Farkas lemma, and the tested field drops out of it: since `ℚ → 𝕜` is an order embedding, a rational
point of the cell is a point of the cell, so an implication tested over `𝕜` is in particular tested
over `ℚ`, where the certificates are found. -/
@[gap212 "lem_packing_cells"]
theorem forall_affine_nonneg_iff_exists_dual_or_farkas {ι T : Type*} [Fintype ι] [Fintype T]
    (b : T → ℚ) (G : T → ι → ℚ) (c : ℚ) (a : ι → ℚ) :
    (∀ y : ι → 𝕜, (∀ t, 0 ≤ (b t : 𝕜) + ∑ i, (G t i : 𝕜) * y i) →
        0 ≤ (c : 𝕜) + ∑ i, (a i : 𝕜) * y i) ↔
      (∃ lam : T → ℚ, (∀ t, 0 ≤ lam t) ∧ (∀ i, ∑ t, lam t * G t i = a i) ∧
          ∑ t, lam t * b t ≤ c) ∨
        ∃ lam : T → ℚ, (∀ t, 0 ≤ lam t) ∧ (∀ i, ∑ t, lam t * G t i = 0) ∧
          ∑ t, lam t * b t < 0 := by
  constructor
  · intro H
    obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
    have hre : ∀ (g : ι → ℚ) (y : Fin (Fintype.card ι) → ℚ),
        ∑ i, g (e.symm i) * y i = ∑ j, g j * y (e j) :=
      fun g y ↦ (Fintype.sum_equiv e (fun j ↦ g j * y (e j))
        (fun i ↦ g (e.symm i) * y i) fun j ↦ by simp).symm
    have H' : ∀ y : Fin (Fintype.card ι) → ℚ, (∀ t, 0 ≤ b t + ∑ i, G t (e.symm i) * y i) →
        0 ≤ c + ∑ i, a (e.symm i) * y i := fun y hy ↦ by
      rw [hre]
      exact mod_cast H (fun j ↦ ((y (e j) : ℚ) : 𝕜)) fun t ↦ by exact_mod_cast hre _ _ ▸ hy t
    rcases exists_dual_or_farkas_fin b (fun t i ↦ G t (e.symm i)) c (fun i ↦ a (e.symm i)) H'
      with ⟨lam, h0, hG, hb⟩ | ⟨lam, h0, hG, hb⟩
    · exact Or.inl ⟨lam, h0, fun j ↦ by simpa using hG (e j), hb⟩
    · exact Or.inr ⟨lam, h0, fun j ↦ by simpa using hG (e j), hb⟩
  · rintro (⟨lam, h0, hGa, hb⟩ | ⟨lam, h0, hG0, hb⟩) y hy
    · have key := sum_nonneg_of_mem_cell b G lam h0 hy
      simp only [hGa] at key
      linarith [show ((∑ t, lam t * b t : ℚ) : 𝕜) ≤ c by exact_mod_cast hb]
    · have key := sum_nonneg_of_mem_cell b G lam h0 hy
      simp only [hG0, Rat.cast_zero, zero_mul, Finset.sum_const_zero, add_zero] at key
      linarith [show ((∑ t, lam t * b t : ℚ) : 𝕜) < 0 by exact_mod_cast hb]

/-! ## The bin condition and the block partitions

The condition below assigns each coordinate a bin, `f : Fin ℓ → Fin r`, and caps the mass of each
fibre; the six conditions of Proposition 3 are stated instead as the existence of two, three or
four blocks with prescribed masses, the last block being the complement of the others. The two are
the same requirement: the blocks are the fibres of `f`, and the complement block is the last fibre.
Both readings are used — a bin assignment read off a partition is what supplies the hypothesis of
`exists_bins_empty_side_of_exists_bins_one`, and a partition read off a bin assignment is what
turns its conclusion back into a condition of Proposition 3. -/

omit [IsStrictOrderedRing 𝕜] in
/-- **Two bins are a two-block partition.** The block `I` is the fibre of the bin `0` and its
complement is the fibre of the bin `1`; conversely `I` and its complement are the fibres of the
assignment sending `I` to `0`. -/
theorem admitsPartition₂_iff_exists_bins {ℓ : ℕ} {y : Fin ℓ → 𝕜} (c : Fin 2 → 𝕜) :
    AdmitsPartition₂ y (c 0) (c 1) ↔
      ∃ f : Fin ℓ → Fin 2, ∀ k, ∑ i ∈ univ.filter (fun i ↦ f i = k), y i ≤ c k := by
  classical
  constructor
  · rintro ⟨I, h₀, h₁⟩
    set f : Fin ℓ → Fin 2 := fun i ↦ if i ∈ I then 0 else 1 with hf
    have e₀ : univ.filter (fun i ↦ f i = 0) = I := by
      ext i; by_cases hi : i ∈ I <;> simp [hf, hi]
    have e₁ : univ.filter (fun i ↦ f i = 1) = univ \ I := by
      ext i; by_cases hi : i ∈ I <;> simp [hf, hi]
    refine ⟨f, fun k ↦ ?_⟩
    rcases (by lia : k = 0 ∨ k = 1) with rfl | rfl
    exacts [e₀ ▸ h₀, e₁ ▸ h₁]
  · rintro ⟨f, hf⟩
    have e : univ \ univ.filter (fun i ↦ f i = 0) = univ.filter (fun i ↦ f i = 1) := by
      ext i; simp only [mem_sdiff, mem_univ, mem_filter, true_and]; lia
    exact ⟨univ.filter (fun i ↦ f i = 0), hf 0, e ▸ hf 1⟩

omit [IsStrictOrderedRing 𝕜] in
/-- **Three bins are a three-block partition.** The blocks `I`, `J` are the fibres of the bins `0`
and `1` — disjoint because a coordinate has one bin — and the complement block is the fibre of
`2`. -/
theorem admitsPartition₃_iff_exists_bins {ℓ : ℕ} {y : Fin ℓ → 𝕜} (c : Fin 3 → 𝕜) :
    AdmitsPartition₃ y (c 0) (c 1) (c 2) ↔
      ∃ f : Fin ℓ → Fin 3, ∀ k, ∑ i ∈ univ.filter (fun i ↦ f i = k), y i ≤ c k := by
  classical
  constructor
  · rintro ⟨I, J, dIJ, h₀, h₁, h₂⟩
    have hIJ : ∀ i ∈ I, i ∉ J := fun i hi ↦ disjoint_left.mp dIJ hi
    set f : Fin ℓ → Fin 3 := fun i ↦ if i ∈ I then 0 else if i ∈ J then 1 else 2 with hf
    have e₀ : univ.filter (fun i ↦ f i = 0) = I := by
      ext i; by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;> simp [hf, hi, hj]
    have e₁ : univ.filter (fun i ↦ f i = 1) = J := by
      ext i; by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;> simp_all
    have e₂ : univ.filter (fun i ↦ f i = 2) = univ \ (I ∪ J) := by
      ext i; by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;> simp [hf, hi, hj]
    refine ⟨f, fun k ↦ ?_⟩
    rcases (by lia : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    exacts [e₀ ▸ h₀, e₁ ▸ h₁, e₂ ▸ h₂]
  · rintro ⟨f, hf⟩
    have e : univ \ (univ.filter (fun i ↦ f i = 0) ∪ univ.filter (fun i ↦ f i = 1))
        = univ.filter (fun i ↦ f i = 2) := by
      ext i; simp only [mem_sdiff, mem_union, mem_univ, mem_filter, true_and]; lia
    exact ⟨univ.filter (fun i ↦ f i = 0), univ.filter (fun i ↦ f i = 1),
      by simp only [disjoint_filter]; lia, hf 0, hf 1, e ▸ hf 2⟩

omit [IsStrictOrderedRing 𝕜] in
/-- **Four bins are a four-block partition.** The blocks `I`, `J`, `K` are the fibres of the bins
`0`, `1`, `2` — pairwise disjoint because a coordinate has one bin — and the complement block is
the fibre of `3`. -/
theorem admitsPartition₄_iff_exists_bins {ℓ : ℕ} {y : Fin ℓ → 𝕜} (c : Fin 4 → 𝕜) :
    AdmitsPartition₄ y (c 0) (c 1) (c 2) (c 3) ↔
      ∃ f : Fin ℓ → Fin 4, ∀ k, ∑ i ∈ univ.filter (fun i ↦ f i = k), y i ≤ c k := by
  classical
  constructor
  · rintro ⟨I, J, K, dIJ, dIK, dJK, h₀, h₁, h₂, h₃⟩
    have hIJ : ∀ i ∈ I, i ∉ J := fun i hi ↦ disjoint_left.mp dIJ hi
    have hIK : ∀ i ∈ I, i ∉ K := fun i hi ↦ disjoint_left.mp dIK hi
    have hJK : ∀ i ∈ J, i ∉ K := fun i hi ↦ disjoint_left.mp dJK hi
    set f : Fin ℓ → Fin 4 :=
      fun i ↦ if i ∈ I then 0 else if i ∈ J then 1 else if i ∈ K then 2 else 3 with hf
    have e₀ : univ.filter (fun i ↦ f i = 0) = I := by
      ext i; by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;> by_cases hk : i ∈ K <;>
        simp [hf, hi, hj, hk]
    have e₁ : univ.filter (fun i ↦ f i = 1) = J := by
      ext i; by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;> by_cases hk : i ∈ K <;> simp_all
    have e₂ : univ.filter (fun i ↦ f i = 2) = K := by
      ext i; by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;> by_cases hk : i ∈ K <;> simp_all
    have e₃ : univ.filter (fun i ↦ f i = 3) = univ \ (I ∪ J ∪ K) := by
      ext i; by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;> by_cases hk : i ∈ K <;>
        simp [hf, hi, hj, hk]
    refine ⟨f, fun k ↦ ?_⟩
    rcases (by lia : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    exacts [e₀ ▸ h₀, e₁ ▸ h₁, e₂ ▸ h₂, e₃ ▸ h₃]
  · rintro ⟨f, hf⟩
    have e : univ \ (univ.filter (fun i ↦ f i = 0) ∪ univ.filter (fun i ↦ f i = 1) ∪
        univ.filter (fun i ↦ f i = 2)) = univ.filter (fun i ↦ f i = 3) := by
      ext i; simp only [mem_sdiff, mem_union, mem_univ, mem_filter, true_and]; lia
    exact ⟨univ.filter (fun i ↦ f i = 0), univ.filter (fun i ↦ f i = 1),
      univ.filter (fun i ↦ f i = 2), by simp only [disjoint_filter]; lia,
      by simp only [disjoint_filter]; lia, by simp only [disjoint_filter]; lia,
      hf 0, hf 1, hf 2, e ▸ hf 3⟩

/-! ## Emptying a rough side -/

/-- A sum over an injective image, for a tuple `z` extending `y` along the injection. -/
private lemma sum_image_eq_sum {M ι κ : Type*} [AddCommMonoid M] [DecidableEq κ] {y : ι → M}
    {z : κ → M} {e : ι → κ} (he : Function.Injective e) (hyz : ∀ i, z (e i) = y i)
    (s : Finset ι) : ∑ j ∈ s.image e, z j = ∑ i ∈ s, y i := by
  rw [Finset.sum_image fun a _ b _ hab ↦ he hab]
  exact Finset.sum_congr rfl fun i _ ↦ hyz i

/-- **Deleting the adjoined coordinates.** If `z` extends `y` along an injection `e` and its
remaining coordinates are nonnegative, then a bin assignment for `z` meeting capacities `c`
restricts along `e` to a bin assignment for `y` meeting the same capacities: each fibre of the
restriction embeds in the corresponding fibre of `z`. -/
private lemma exists_bins_comp_of_injective {M : Type*} [AddCommMonoid M] [PartialOrder M]
    [AddLeftMono M] {ℓ L r : ℕ} {y : Fin ℓ → M} {z : Fin L → M} {c : Fin r → M} {e : Fin ℓ → Fin L}
    (he : Function.Injective e) (hyz : ∀ i, z (e i) = y i) (hz : ∀ j, 0 ≤ z j)
    (hex : ∃ f : Fin L → Fin r, ∀ k, ∑ j ∈ univ.filter (fun j ↦ f j = k), z j ≤ c k) :
    ∃ g : Fin ℓ → Fin r, ∀ k, ∑ i ∈ univ.filter (fun i ↦ g i = k), y i ≤ c k := by
  obtain ⟨f, hf⟩ := hex
  refine ⟨f ∘ e, fun k ↦ ?_⟩
  rw [← sum_image_eq_sum he hyz]
  exact (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.image_subset_iff.2 fun i hi ↦ by simpa using hi) fun j _ _ ↦ hz j).trans (hf k)

/-- On an empty index set every bin sum is the empty sum, so nonnegative capacities are met
outright. This is the doubly degenerate pair `(0, 0)`. -/
private lemma exists_bins_of_fin_zero {M : Type*} [AddCommMonoid M] [PartialOrder M] {r : ℕ}
    (y : Fin 0 → M) {c : Fin r → M} (hc : ∀ k, 0 ≤ c k) :
    ∃ f : Fin 0 → Fin r, ∀ k, ∑ i ∈ univ.filter (fun i ↦ f i = k), y i ≤ c k :=
  ⟨Fin.elim0, fun k ↦ by simpa using hc k⟩

/-- **An empty rough side reduces to a nonempty one.** Fix a number of bins `r`, capacities
`c : Fin r → 𝕜`, a rough threshold `δ` with `0 ≤ δ ≤ 1`, and two cap rows `B`, `B'` whose first
entries exceed `δ`. Suppose the bin condition holds at every pair `(m, 1)` and at every pair
`(1, m')` with the named side nonempty. Then it holds at every pair `(m, 0)` with an empty second
side, at every pair `(0, m')` with an empty first side, and — as the count `0` of either
conclusion — at `(0, 0)`.

The bin condition is stated for an arbitrary bin count: an assignment `f` of the coordinates to
`Fin r` whose fibre sums respect `c`. By `admitsPartition₂_iff_exists_bins` and its three- and
four-bin analogues it is `AdmitsPartition₂`, `₃`, `₄` at `r = 2, 3, 4`, so this covers each of the
six conditions A, A′, B, C, D, E at once. -/
@[gap212 "lem_packing_empty_side"]
theorem exists_bins_empty_side_of_exists_bins_one {r : ℕ} {B B' : ℕ → 𝕜} {δ : 𝕜} {c : Fin r → 𝕜}
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (hB : δ ≤ B 1) (hB' : δ ≤ B' 1)
    (h : ∀ m, 1 ≤ m → ∀ y ∈ Xi (B m) (B' 1) m 1 δ,
      ∃ f : Fin (m + 1) → Fin r, ∀ k, ∑ i ∈ univ.filter (fun i ↦ f i = k), y i ≤ c k)
    (h' : ∀ m', 1 ≤ m' → ∀ y ∈ Xi (B 1) (B' m') 1 m' δ,
      ∃ f : Fin (1 + m') → Fin r, ∀ k, ∑ i ∈ univ.filter (fun i ↦ f i = k), y i ≤ c k) :
    (∀ m, ∀ y ∈ Xi (B m) (B' 0) m 0 δ,
        ∃ f : Fin (m + 0) → Fin r, ∀ k, ∑ i ∈ univ.filter (fun i ↦ f i = k), y i ≤ c k) ∧
      ∀ m', ∀ y ∈ Xi (B 0) (B' m') 0 m' δ,
        ∃ f : Fin (0 + m') → Fin r, ∀ k, ∑ i ∈ univ.filter (fun i ↦ f i = k), y i ≤ c k := by
  -- Every capacity is nonnegative: the check set at `(1, 1)` contains the constant tuple `δ`.
  have hc : ∀ k, 0 ≤ c k := by
    have hmem : (fun _ : Fin (1 + 1) ↦ δ) ∈ Xi (B 1) (B' 1) 1 1 δ := by
      refine ⟨fun _ ↦ ⟨le_rfl, hδ₁⟩, ?_, ?_⟩
      · rwa [show univ.filter (fun j : Fin (1 + 1) ↦ ((j : ℕ) < 1)) = {0} from by decide,
          Finset.sum_singleton]
      · rwa [show univ.filter (fun j : Fin (1 + 1) ↦ ¬ ((j : ℕ) < 1)) = {1} from by decide,
          Finset.sum_singleton]
    obtain ⟨f, hf⟩ := h 1 le_rfl _ hmem
    exact fun k ↦ (Finset.sum_nonneg fun _ _ ↦ hδ₀).trans (hf k)
  refine ⟨fun m y hy ↦ ?_, fun m' y hy ↦ ?_⟩
  · -- An empty second side: adjoin `δ` at the top index.
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact exists_bins_of_fin_zero y hc
    set z : Fin (m + 1) → 𝕜 := Fin.snoc (fun i : Fin m ↦ y i) δ with hz₀
    have hze : ∀ i : Fin m, z i.castSucc = y i := fun i ↦ by simp [hz₀]
    have hzc : ∀ j, z j ∈ Set.Icc δ 1 := by
      intro j
      induction j using Fin.lastCases with
      | last => simpa [hz₀] using hδ₁
      | cast i => rw [hze]; exact hy.1 i
    have hmem : z ∈ Xi (B m) (B' 1) m 1 δ := by
      refine ⟨hzc, ?_, ?_⟩
      · have hset : univ.filter (fun j : Fin (m + 1) ↦ ((j : ℕ) < m))
            = univ.image (Fin.castSucc : Fin m → Fin (m + 1)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          exact ⟨fun hj ↦ ⟨⟨(j : ℕ), hj⟩, Fin.ext rfl⟩, by rintro ⟨i, rfl⟩; simp⟩
        rw [hset, sum_image_eq_sum (Fin.castSucc_injective m) hze]
        simpa using hy.2.1
      · have hset : univ.filter (fun j : Fin (m + 1) ↦ ¬ ((j : ℕ) < m)) = {Fin.last m} := by
          ext j; simp [Fin.ext_iff]; lia
        rw [hset, Finset.sum_singleton]
        simpa [hz₀] using hB'
    exact exists_bins_comp_of_injective (Fin.castSucc_injective m) hze
      (fun j ↦ hδ₀.trans (hzc j).1) (h m hm z hmem)
  · -- An empty first side: adjoin `δ` at the bottom index.
    rcases Nat.eq_zero_or_pos m' with rfl | hm'
    · exact exists_bins_of_fin_zero y hc
    set e : Fin (0 + m') → Fin (1 + m') := fun i ↦ Fin.natAdd 1 (Fin.cast (zero_add m') i) with he₀
    set z : Fin (1 + m') → 𝕜 :=
      Fin.append (fun _ : Fin 1 ↦ δ) (fun j ↦ y (Fin.cast (zero_add m').symm j)) with hz₀
    have hinj : Function.Injective e := fun a b hab ↦ by simpa [he₀, Fin.ext_iff] using hab
    have hze : ∀ i, z (e i) = y i := fun i ↦ by simp [he₀, hz₀]
    have hzc : ∀ j, z j ∈ Set.Icc δ 1 := by
      intro j
      induction j using Fin.addCases with
      | left i => simpa [hz₀] using hδ₁
      | right i =>
        rw [show Fin.natAdd 1 i = e (Fin.cast (zero_add m').symm i) from rfl, hze]
        exact hy.1 _
    have hmem : z ∈ Xi (B 1) (B' m') 1 m' δ := by
      refine ⟨hzc, ?_, ?_⟩
      · have hset : univ.filter (fun j : Fin (1 + m') ↦ ((j : ℕ) < 1))
            = {Fin.castAdd m' (0 : Fin 1)} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
            Fin.ext_iff, Fin.val_castAdd, Fin.val_zero]
          lia
        rw [hset, Finset.sum_singleton]
        simpa [hz₀] using hB
      · have hset : univ.filter (fun j : Fin (1 + m') ↦ ¬ ((j : ℕ) < 1)) = univ.image e := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, he₀]
          refine ⟨fun hj ↦ ⟨Fin.cast (zero_add m').symm ⟨(j : ℕ) - 1, by lia⟩,
            Fin.ext (by simp; lia)⟩, ?_⟩
          rintro ⟨i, rfl⟩
          simp
        rw [hset, sum_image_eq_sum hinj hze]
        simpa using hy.2.2
    exact exists_bins_comp_of_injective hinj hze (fun j ↦ hδ₀.trans (hzc j).1) (h' m' hm' z hmem)

end Gap212.Packing
