/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Gap212.Attr
public import Gap212.Packing.Basic

/-!
# The check set is empty above thirteen

If `B k ≤ 1081/5000` for every `k` and `k·(41/2500) ≤ B k` for every `k ≤ 13`, then the check set
`Ξ(B m, B m', m, m', 41/2500)` is nonempty if and only if `m ≤ 13` and `m' ≤ 13`
(`Gap212.Xi_nonempty_iff_le_thirteen`).
-/

@[expose] public section

namespace Gap212


open Finset Gap212.Packing

/-- The first capped group of `Ξ(·, ·, m, m', ·)` — the indices of `Fin (m + m')` below `m` — has
`m` elements. -/
private theorem card_filter_val_lt' (m m' : ℕ) :
    #{i : Fin (m + m') | (i : ℕ) < m} = m := by
  rw [Fin.card_filter_val_lt]; omega

/-- The second capped group of `Ξ(·, ·, m, m', ·)` — the complement of the first — has `m'`
elements. -/
private theorem card_filter_not_val_lt (m m' : ℕ) :
    #{i : Fin (m + m') | ¬ ((i : ℕ) < m)} = m' := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin (m + m')))) (p := fun i : Fin (m + m') ↦ (i : ℕ) < m)
  rw [Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- The arithmetic of the bound: `82 n ≤ 1081` forces `n ≤ 13`, since `14 · 82 = 1148 > 1081`. -/
private theorem le_thirteen_of_mul_le {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {n : ℕ} (h : (n : 𝕜) * (41 / 2500) ≤ 1081 / 5000) : n ≤ 13 := by
  by_contra hn
  have h14 : (14 : 𝕜) ≤ n := by exact_mod_cast (by omega : 14 ≤ n)
  linarith

/-- **The check set is empty above thirteen.** If `B k ≤ 1081/5000` for every `k` and
`k·(41/2500) ≤ B k` for every `k ≤ 13`, then `Ξ(B m, B m', m, m', 41/2500)` is nonempty if and only
if `m ≤ 13` and `m' ≤ 13`. -/
@[gap212 "lem_check_set_empty_above_thirteen"]
theorem Xi_nonempty_iff_le_thirteen {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {B : ℕ → 𝕜} (hcap : ∀ k, B k ≤ 1081 / 5000)
    (hrung : ∀ k : ℕ, k ≤ 13 → (k : 𝕜) * (41 / 2500) ≤ B k) (m m' : ℕ) :
    (Xi (B m) (B m') m m' (41 / 2500 : 𝕜)).Nonempty ↔ m ≤ 13 ∧ m' ≤ 13 := by
  constructor
  · rintro ⟨y, hy, h₁, h₂⟩
    have key (s : Finset (Fin (m + m'))) : (#s : 𝕜) * (41 / 2500) ≤ ∑ i ∈ s, y i := by
      simpa [nsmul_eq_mul, mul_comm] using card_nsmul_le_sum s y _ fun i _ ↦ (hy i).1
    refine ⟨le_thirteen_of_mul_le (𝕜 := 𝕜) ?_, le_thirteen_of_mul_le (𝕜 := 𝕜) ?_⟩
    · simpa only [card_filter_val_lt'] using (key _).trans (h₁.trans (hcap m))
    · simpa only [card_filter_not_val_lt] using (key _).trans (h₂.trans (hcap m'))
  · rintro ⟨hm, hm'⟩
    refine ⟨fun _ ↦ (41 / 2500 : 𝕜), fun _ ↦ ⟨le_rfl, by norm_num⟩, ?_, ?_⟩
    · rw [Finset.sum_const, card_filter_val_lt', nsmul_eq_mul]; exact hrung m hm
    · rw [Finset.sum_const, card_filter_not_val_lt, nsmul_eq_mul]; exact hrung m' hm'


end Gap212
