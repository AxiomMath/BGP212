/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Defs
public import Gap212.Harman.Challenge
public import Gap212.Packing.ConditionD
public import Gap212.Packing.DatumFacts
public meta import Gap212.Attr

/-!
# Condition D at the chosen datum: the capacity arithmetic, and the bands it closes

Condition D (`Gap212.Defs.ConditionD`) is the four-block packing condition of the Type IIc
estimate. At `Gap212.gap212Params` — `δ = 41/2500`, level `ω(1,1) = 7/1000`
(`Gap212.omegaMax_gap212Params`), cap row `Gap212.gap212Cap`, `ϵ = Gap212.slack = 10⁻¹⁰` — it asks,
for every `ω₀ ∈ [0, ω(1,1)]` and every `γ ∈ [2/5 - ϵ, 1/3 + 8ω(1,1) + 7δ/3 + 3ϵ]`, a partition of
every rough profile into four blocks of masses at most

    c₁ = γ - 2δ - 8ω₀ - ϵ,  c₂ = 1/2 - γ - 2ω₀ - ϵ,  c₃ = 4ω₀ + δ - ϵ,  c₄ = 8ω₀.

## The two facts that shape the argument

**`γ` cancels from the capacity sum.** `Gap212.capD_sum` says

    c₁ + c₂ + c₃ + c₄ = 1209/2500 + 2ω₀ - 3ϵ,

so the sum condition is `γ`-free, and at its worst — `ω₀ = 0` — it reads `0.4836 - 3ϵ` against the
largest pooled rough mass the cap row admits, `1081/2500 = 0.4324` (`Gap212.total_le_datum`). That
is `Gap212.pooled_lt_capD_sum`, with margin `128/2500 - 3ϵ = 0.0512 - 3·10⁻¹⁰`. This is what makes
the "uniformly in `γ`" clause tractable at all.

**No single bin absorbs the profile.** Over the chamber the four capacities are bounded by

    c₁ ≤ 987/2500 = 0.3948   (γ maximal, ω₀ = 0)      c₂ ≤ 1/10      (γ minimal, ω₀ = 0)
    c₃ ≤ 111/2500 = 0.0444   (ω₀ = ω(1,1))            c₄ ≤ 7/125 = 0.056  (ω₀ = ω(1,1))

(`Gap212.capD_zero_le`, `capD_one_le`, `capD_two_le`, `capD_three_le`), every one of them below
`0.4324`. And that mass is attained: `Gap212.flatDatumTuple`, the constant profile `1081/50000` on
`(m, m') = (10, 10)`, lies in the check set with total mass exactly `1081/2500`
(`Gap212.exists_mem_Xi_gt_capD`). So unlike Conditions A′ and B at this datum, Condition D can
never be discharged by `Gap212.Packing.admitsPartition₄_of_total_le`: the trivial partition fails
at every chamber point, and the `ω₀ → 0` corner — where `c₄` vanishes and `c₃ = δ - ϵ` falls below
the floor `δ` on a single coordinate, so blocks three and four must both be *empty* — is the tight
one.

## The bands

Six bands are closed here, all for **every** `m` and `m'` and **every** `γ` in the stated range:
`Gap212.conditionD_at_datum_low_level` on `ω₀ ∈ [0, 7/10000]`,
`Gap212.conditionD_at_datum_mid_band` on `ω₀ ∈ (7/10000, 1/400]`,
`Gap212.conditionD_at_datum_band_2` on `ω₀ ∈ (1/400, 1/250]`,
`Gap212.conditionD_at_datum_band_3` on `ω₀ ∈ (1/250, 43/10000]`,
`Gap212.conditionD_at_datum_band_4` on `ω₀ ∈ (43/10000, 13/2500]` and
`Gap212.conditionD_at_datum_band_5` on `ω₀ ∈ (13/2500, 541/100000]`. Together they give
`[0, 541/100000]`, which is `541/700` of the chamber `[0, 7/1000]`. The rest of the chamber is
`Gap212.conditionD_at_datum_band_6` on `(541/100000, 4/625]` and `Gap212.PackingCertificate` on
`(4/625, 7/1000]`, proved as `Gap212.packingCertificate_at_datum`. The later bands' arguments are
described at `Gap212.conditionD_at_datum_mid_band`, `conditionD_at_datum_band_2`,
`conditionD_at_datum_band_3`, `conditionD_at_datum_band_4` and `conditionD_at_datum_band_5`; the
first is described next.

`Gap212.conditionD_at_datum_low_level` is Condition D at `p_⋆` for `ω₀ ∈ [0, 7/10000]` — the first
tenth of the chamber,
including the tight `ω₀ → 0` corner. Blocks three and four are left empty throughout, so the
content is the two-block statement at capacities `c₁`, `c₂`, whose sum `1/2 - 2δ - 10ω₀ - 2ϵ` is at
least `2301/5000 = 0.4602` on that region, against a pooled mass of at most `0.4324`.

The argument is uniform in the cell — no enumeration of the `91` cells:

* Either the pooled mass already fits in `c₁` and the trivial partition serves, or it does not, and
  then the affine cap bound `B_{1,m} ≤ (773 + 36m)/5000` of `Gap212.gap212Cap_le_affine` (exact at
  `m = 4` and `m = 5`) forces `N = m + m' ≥ 8` rough factors: `N ≤ 7` caps the pooled mass at
  `1798/5000 = 0.3596`, below `c₁ ≥ 904/2500 - 2ϵ = 0.3616 - 2·10⁻¹⁰`.
* The deficit `D = Y - c₁` is then at most `177/2500 + 2ϵ = 0.0708`, hence below `5δ = 0.082`: five
  coordinates always carry it.
* `Gap212.Packing.exists_small_coords` produces five coordinates each at most
  `v = (Y - 4δ)/(N - 4)`, the bound on the fifth smallest, and `v ≤ c₂ - D` is the one numerical
  inequality of the proof (`Gap212.datumD_fifth_le_reserve`). Since
  `c₂ - D = 1/2 - Y - 2δ - 10ω₀ - 2ϵ` is `γ`-free, it reduces via the two mass bounds to two
  polynomial inequalities in `N`: `36N² - 863N + 4238 ≤ 0` for `8 ≤ N ≤ 17` (value `-29` at
  `N = 17`, `-362` at `N = 8`) and `2390 ≤ 139N` for `N ≥ 18` (`139·18 - 2390 = 112`). The
  minimal-cardinality engine `Gap212.Packing.exists_subset_sum_mem_Icc_of_subset` then lands a
  subset of those coordinates in `[D, D + v] ⊆ [D, c₂]`, and its complement carries `Y - D = c₁`.

The proof's tightest constraint is at `N = 17` — realized by cells such as `(m, m') = (8, 9)` —
with `ω₀ = 7/10000`, where `v` falls short of `c₂ - D` by `29/65000 ≈ 0.00045`. The margin is
`γ`-free, `c₂ - D` being `γ`-free; the `γ` endpoints matter only through `c₁ ≥ 904/2500 - 2ϵ` and
`c₂ ≥ 0`. `7/10000` is not arbitrary: the same `N = 17` inequality holds up to
`ω₀ = 121/162500 ≈ 0.000745` and fails past it, so this is the ceiling the two-block argument has,
to within the chosen numeral.

**Why this particular split stops at `7/10000`, and what replaces it.** Past
`ω₀ = 121/162500 ≈ 0.000745` the bound `v` on the fifth smallest coordinate exceeds the reserve
`c₂ - D` at `N = 17`, so the two-block split stops closing. And no two-block argument gets past
`ω₀ = 87/25000 - ϵ/5 = 0.00348`, where the two-block capacity `c₁ + c₂ = 1/2 - 2δ - 10ω₀ - 2ϵ`
drops below the pooled mass `0.4324` outright: blocks three and four must then carry mass. What
`Gap212.conditionD_at_datum_mid_band` does above `7/10000` is put one coordinate into block three,
choosing it by a dichotomy on the profile rather than on the cell, and that reaches `ω₀ = 1/400`.

## Main results

* `Gap212.capD`, `Gap212.chamberD`: the capacity row and the chamber, in the datum's numerals.
* `Gap212.capD_sum`, `Gap212.pooled_lt_capD_sum`: `γ` cancels from the sum, with margin `0.0512`.
* `Gap212.capD_zero_le`–`capD_three_le`, `Gap212.exists_mem_Xi_gt_capD`: no single bin suffices.
* `Gap212.gap212Cap_le_affine`, `gap212Cap_le_affine₂`–`gap212Cap_le_affine₆` and the mass bounds
  `Gap212.total_le_affine_datum`, `total_le_affine_datum₂`–`total_le_affine_datum₆`: six affine
  bounds on the cap row, whose minimum (with the flat bound) is the exact cell maximum of
  `B_{1,m} + B_{1,m'}` at `N = 2, 4, 6, 8, 9, 10` and at every `N` from `14` to `26`, and within
  `3/5000` of it at `N = 11, 12, 13`.
* `Gap212.Packing.exists_small_coords`: `n + 1` coordinates below the `(n+1)`-st smallest's bound.
* `Gap212.Packing.admitsPartition₂_of_small_block`: the engine step, as a two-block partition.
* `Gap212.Packing.admitsPartition₄_of_singleton_block`: the same with one coordinate in block
  three.
* `Gap212.Packing.admitsPartition₄_of_two_singletons`: one in block three and one in block four.
* `Gap212.Packing.exists_nat_mul_le_lt`: the level `n = ⌊D/d⌋` the small-coordinate count uses.
* `Gap212.datumD_fifth_le_reserve`: the one numerical inequality of the low-level theorem.
* `Gap212.datumD_band_low_core`, `datumD_band_low_window`, `datumD_band_high_floor`,
  `datumD_band_high_core`, `datumD_band_high_window`: the two numerical inequalities of the band,
  one per branch, each verified rung by rung for `6 ≤ N ≤ 26`.
* `Gap212.conditionD_at_datum_low_level`: Condition D at `p_⋆` for `0 ≤ ω₀ ≤ 7/10000`.
* `Gap212.conditionD_at_datum_mid_band`: Condition D at `p_⋆` for `7/10000 < ω₀ ≤ 1/400`.
* `Gap212.datumD_band2_low_core`, `band2_mid_reserve`, `datumD_band2_mid_core`, `band2_high_floor`,
  `datumD_band2_high_core`: the three numerical inequalities of the second band, one per branch,
  each verified rung by rung for `5 ≤ N ≤ 26`.
* `Gap212.conditionD_at_datum_band_2`: Condition D at `p_⋆` for `1/400 < ω₀ ≤ 1/250`.
* `Gap212.Packing.card_side_left`, `card_side_right`, `Gap212.side_floor_le_cap`,
  `Gap212.side_le_six`: a floor on every coordinate is a floor on each *side's* mass, which above
  `ω₀ = 1/250` caps each side at six rough factors and so replaces the affine mass bounds by the
  exact cell maximum.
* `Gap212.datumD_band3_low_core`, `band3_mid_reserve`, `datumD_band3_mid_core`, `band3_high_floor`,
  `datumD_band3_high_core`: the three numerical inequalities of the third band. The first two are
  verified rung by rung for `5 ≤ N ≤ 26`; the high branch's two run over the forty-nine pairs of
  side counts `m, m' ∈ [0, 6]` instead.
* `Gap212.conditionD_at_datum_band_3`: Condition D at `p_⋆` for `1/250 < ω₀ ≤ 43/10000`.
* `Gap212.Packing.admitsPartition₄_of_blocks`, `Gap212.Packing.le_window_of_core`: the engine with
  arbitrary contents for the two small blocks, and the elimination of the level `n`, stated once.
* `Gap212.side_le_five`, `Gap212.datumD_band4_pair_core`, `datumD_band4_triple_core`,
  `datumD_band4_pairfloor_core`, `datumD_band4_single_core`, `datumD_band4_high_core`: the five
  numerical inequalities of the fourth band, one per branch — four of them rung by rung for
  `4 ≤ N ≤ 26`, the high branch's over the twenty-five pairs of side counts.
* `Gap212.side_floor_le_cap_except`, `Gap212.side_le_six_except`: the same side reading with one
  coordinate excused, which is what the fourth band's one-parked branch has to work with.
* `Gap212.conditionD_at_datum_band_4`: Condition D at `p_⋆` for `43/10000 < ω₀ ≤ 13/2500`.
* `Gap212.gap212Cap_le_six`, `gap212Cap_le_five`: the two rungs of the cap row the fifth band's
  level bounds are read against.
* `Gap212.datumD_band5_pair_window`, `datumD_band5_single_window`, `datumD_band5_high_window`: the
  three window requirements of the fifth band restated at an *integer* level and verified level by
  level — `155` pairs `(N, n)` for the first, `(m, m', n)` with `m, m' ≤ 6` and `n ≤ 4` for the
  second, `m, m' ≤ 5` and `n ≤ 1` for the third. Together with
  `Gap212.datumD_band5_triple_core`, `datumD_band5_pairfloor_core` and
  `datumD_band5_pairfloor_reserve` — the two branches that never bind, restated only for the new
  level range — these are the whole difference between the fourth band and the fifth.
* `Gap212.conditionD_at_datum_band_5`: Condition D at `p_⋆` for `13/2500 < ω₀ ≤ 541/100000`.
* `Gap212.conditionD_of_band`, `conditionD_of_band_split`: the chamber and band splicings.
-/

@[expose] public section

namespace Gap212.Packing

open Finset

/-! ## Counting the small coordinates

The argument needs the bound on the `(n+1)`-st smallest coordinate, and it needs it without
sorting. Contrapositively: `ℓ - n` coordinates above `v` together with `n` at the floor `d` already
carry more than `(ℓ - n) v + n d`, so if the whole profile carries no more than that, at least
`n + 1` coordinates are at most `v`. -/

/-- **At least `n + 1` coordinates lie below `v`**, provided the total mass does not exceed
`(ℓ - n) v + n d` — the mass of a profile with `ℓ - n` coordinates at `v` and `n` at the floor `d`.

Applied with `v = (Y - n d)/(ℓ - n)`, which turns the hypothesis into an equality, this is exactly
the bound on the `(n+1)`-st smallest coordinate: the `ℓ - n` coordinates from it upwards are all at
least as large, and the `n` below it are at least `d`. It replaces a sort. -/
theorem exists_small_coords {ℓ : ℕ} {y : Fin ℓ → ℝ} {d v : ℝ} {n : ℕ}
    (hd : ∀ i, d ≤ y i) (hdv : d ≤ v) (hn : n < ℓ)
    (hv : ∑ i, y i ≤ ((ℓ : ℝ) - n) * v + n * d) :
    n + 1 ≤ (univ.filter (fun i : Fin ℓ ↦ y i ≤ v)).card := by
  by_contra hcon
  have hcard := card_filter_add_card_filter_not (s := (univ : Finset (Fin ℓ))) (fun i ↦ y i ≤ v)
  rw [card_univ, Fintype.card_fin] at hcard
  set S := univ.filter (fun i : Fin ℓ ↦ y i ≤ v)
  set T := univ.filter (fun i : Fin ℓ ↦ ¬ (y i ≤ v))
  have hTlow : (T.card : ℝ) * v < ∑ i ∈ T, y i := by
    simpa using sum_lt_sum_of_nonempty (card_pos.1 (by omega))
      fun i (hi : i ∈ T) ↦ not_le.mp (mem_filter.mp hi).2
  have hSlow : (S.card : ℝ) * d ≤ ∑ i ∈ S, y i := by
    simpa using S.card_nsmul_le_sum y d fun i _ ↦ hd i
  have hTeq : (T.card : ℝ) = ℓ - S.card := eq_sub_of_add_eq' (by exact_mod_cast hcard)
  have hSn : (S.card : ℝ) ≤ n := by exact_mod_cast (by omega : S.card ≤ n)
  rw [hTeq] at hTlow
  nlinarith [mul_nonneg (sub_nonneg.2 hSn) (sub_nonneg.2 hdv), sum_filter_add_sum_filter_not univ
    (fun i ↦ y i ≤ v) y]

/-- `k` coordinates above the floor `d ≥ 0` carry at least `k d`. -/
private theorem mul_le_sum_of_card_le {ι : Type*} {S : Finset ι} {y : ι → ℝ} {d : ℝ} {k : ℕ}
    (hd0 : 0 ≤ d) (hd : ∀ i, d ≤ y i) (hk : k ≤ S.card) : (k : ℝ) * d ≤ ∑ i ∈ S, y i := by
  have h := S.card_nsmul_le_sum y d fun i _ ↦ hd i
  rw [nsmul_eq_mul] at h
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hd0).trans h

/-- The level-`n` step of every band: the bound `v = (Y - n d)/(ℓ - n)` on the `(n+1)`-st smallest
coordinate, which clears the floor, and the `n + 1` coordinates below it with their mass. -/
private theorem exists_level_coords {ℓ n : ℕ} {y : Fin ℓ → ℝ} {d : ℝ} (hd0 : 0 ≤ d)
    (hd : ∀ i, d ≤ y i) (hn : n < ℓ) :
    ∃ v : ℝ, v * ((ℓ : ℝ) - n) = (∑ i, y i) - n * d ∧ d ≤ v ∧
      n + 1 ≤ (univ.filter (fun i ↦ y i ≤ v)).card ∧
      ((n : ℝ) + 1) * d ≤ ∑ i ∈ univ.filter (fun i ↦ y i ≤ v), y i := by
  have hnℓ : (0 : ℝ) < ℓ - n := sub_pos.2 (by exact_mod_cast hn)
  have hY : (ℓ : ℝ) * d ≤ ∑ i, y i := by simpa using mul_le_sum_of_card_le (S := univ) hd0 hd le_rfl
  have hdv : d ≤ ((∑ i, y i) - n * d) / (ℓ - n) := (le_div_iff₀ hnℓ).2 (by linarith)
  have hv := div_mul_cancel₀ ((∑ i, y i) - n * d) hnℓ.ne'
  have hS := exists_small_coords hd hdv hn (by linarith)
  exact ⟨_, hv, hdv, hS, by exact_mod_cast mul_le_sum_of_card_le hd0 hd hS⟩

/-- A floor `f` on every coordinate outside `T` bounds the total mass below. -/
private theorem floor_off_le_sum {ℓ : ℕ} {y : Fin ℓ → ℝ} {T : Finset (Fin ℓ)} {f : ℝ}
    (hf : ∀ i, i ∉ T → f ≤ y i) : ((ℓ : ℝ) - T.card) * f + ∑ i ∈ T, y i ≤ ∑ i, y i := by
  have h := (univ \ T).card_nsmul_le_sum y f fun i hi ↦ hf i (mem_sdiff.1 hi).2
  rw [nsmul_eq_mul, card_univ_sdiff, Fintype.card_fin,
    Nat.cast_sub (by simpa using T.card_le_univ)] at h
  linarith [sum_sdiff (subset_univ T) (f := y)]

/-- Erasing one nonnegative coordinate from a sum costs at most that coordinate. -/
private theorem sum_le_erase_add {ι : Type*} [DecidableEq ι] (S : Finset ι) {y : ι → ℝ} {a : ι}
    (ha : 0 ≤ y a) : ∑ i ∈ S, y i ≤ ∑ i ∈ S.erase a, y i + y a := by
  by_cases h : a ∈ S
  · rw [sum_erase_add _ _ h]
  · rw [erase_eq_of_notMem h]; linarith

/-- **The engine step, as a two-block partition.** If the coordinates of `S` are all at most `v`
and `S` carries the deficit `Y - c₁`, a minimal-cardinality subset of `S` reaching the deficit
overshoots it by less than `v`, so it fits in `c₂` once `(Y - c₁) + v ≤ c₂`; its complement carries
`Y - (Y - c₁) = c₁`.

This is `Gap212.Packing.exists_subset_sum_mem_Icc_of_subset` packaged for the caller, and it is the
only place the partition predicate is opened. -/
theorem admitsPartition₂_of_small_block {ℓ : ℕ} {y : Fin ℓ → ℝ} {c₁ c₂ v : ℝ}
    {S : Finset (Fin ℓ)} (hS : ∀ i ∈ S, y i ≤ v) (hv0 : 0 ≤ v)
    (hD0 : 0 ≤ (∑ i, y i) - c₁) (hSsum : (∑ i, y i) - c₁ ≤ ∑ i ∈ S, y i)
    (hvc : ((∑ i, y i) - c₁) + v ≤ c₂) :
    AdmitsPartition₂ y c₁ c₂ := by
  classical
  obtain ⟨J, -, hJlo, hJhi⟩ :=
    exists_subset_sum_mem_Icc_of_subset S y v ((∑ i, y i) - c₁) hS hv0 hD0 hSsum
  refine ⟨univ \ J, ?_, ?_⟩
  · have hsp : (∑ i ∈ univ \ J, y i) + ∑ i ∈ J, y i = ∑ i, y i :=
      Finset.sum_sdiff (Finset.subset_univ J)
    linarith
  · rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ J)]
    linarith

/-- **The engine step with block three carrying one coordinate.** The deficit `Y - c₁` is split
between the singleton `{i₀}`, which block three absorbs because `y i₀ ≤ c₃`, and a
minimal-cardinality subset of the small coordinates of `S` reaching what is left of it; that subset
overshoots by less than `v`, so it fits in `c₂` once `(Y - c₁ - y i₀) + v ≤ c₂`. The complement
carries `Y - (Y - c₁) = c₁` and block four is left empty.

This widens the window of `Gap212.Packing.admitsPartition₂_of_small_block` from
`c₂ - (Y - c₁)` to `c₂ - (Y - c₁) + y i₀`: one coordinate placed in the third block buys its own
mass as extra room for the subset-sum step. `i₀` need not lie in `S`, and if the singleton already
covers the deficit the second block is left empty too. -/
theorem admitsPartition₄_of_singleton_block {ℓ : ℕ} {y : Fin ℓ → ℝ} {c₁ c₂ c₃ c₄ v : ℝ}
    {S : Finset (Fin ℓ)} {i₀ : Fin ℓ} (hS : ∀ i ∈ S, y i ≤ v) (hv0 : 0 ≤ v)
    (hc₂ : 0 ≤ c₂) (hc₄ : 0 ≤ c₄) (hi₀ : y i₀ ≤ c₃)
    (hSsum : (∑ i, y i) - c₁ - y i₀ ≤ ∑ i ∈ S.erase i₀, y i)
    (hvc : ((∑ i, y i) - c₁ - y i₀) + v ≤ c₂) :
    AdmitsPartition₄ y c₁ c₂ c₃ c₄ := by
  classical
  have hsing : ∑ i ∈ ({i₀} : Finset (Fin ℓ)), y i = y i₀ := Finset.sum_singleton _ _
  by_cases hle : (∑ i, y i) - c₁ - y i₀ ≤ 0
  · -- the singleton alone carries the deficit; blocks two and four stay empty
    have hsum : (∑ i ∈ univ \ ({i₀} : Finset (Fin ℓ)), y i) + ∑ i ∈ ({i₀} : Finset (Fin ℓ)), y i
        = ∑ i, y i := Finset.sum_sdiff (Finset.subset_univ _)
    rw [hsing] at hsum
    refine ⟨univ \ {i₀}, ∅, {i₀}, Finset.disjoint_empty_right _, Finset.sdiff_disjoint,
      Finset.disjoint_empty_left _, by linarith, by simpa using hc₂, by rw [hsing]; exact hi₀, ?_⟩
    rw [Finset.union_empty, Finset.sdiff_union_of_subset (Finset.subset_univ _), Finset.sdiff_self]
    simpa using hc₄
  · push Not at hle
    obtain ⟨J, hJsub, hJlo, hJhi⟩ :=
      exists_subset_sum_mem_Icc_of_subset (S.erase i₀) y v ((∑ i, y i) - c₁ - y i₀)
        (fun i hi ↦ hS i (Finset.mem_of_mem_erase hi)) hv0 hle.le hSsum
    have hi₀J : i₀ ∉ J := fun h ↦ (Finset.notMem_erase i₀ S) (hJsub h)
    have hsum : (∑ i ∈ univ \ insert i₀ J, y i) + ∑ i ∈ insert i₀ J, y i = ∑ i, y i :=
      Finset.sum_sdiff (Finset.subset_univ _)
    rw [Finset.sum_insert hi₀J] at hsum
    refine ⟨univ \ insert i₀ J, J, {i₀}, ?_, ?_, ?_, by linarith, by linarith,
      by rw [hsing]; exact hi₀, ?_⟩
    · exact Finset.disjoint_left.2 fun a ha haJ ↦
        (Finset.mem_sdiff.1 ha).2 (Finset.mem_insert_of_mem haJ)
    · refine Finset.disjoint_left.2 fun a ha haK ↦ ?_
      rw [Finset.mem_singleton] at haK
      exact (Finset.mem_sdiff.1 ha).2 (haK ▸ Finset.mem_insert_self i₀ J)
    · exact Finset.disjoint_singleton_right.2 hi₀J
    · have hcover : univ \ insert i₀ J ∪ J ∪ ({i₀} : Finset (Fin ℓ)) = univ := by
        rw [Finset.union_assoc, Finset.union_comm J {i₀}, ← Finset.insert_eq,
          Finset.sdiff_union_of_subset (Finset.subset_univ _)]
      rw [hcover, Finset.sdiff_self]
      simpa using hc₄

/-- **The engine step with one coordinate in block three and one in block four.** The deficit
`Y - c₁` is split three ways: the singleton `{i₀}`, which block three absorbs because `y i₀ ≤ c₃`;
the singleton `{j₀}`, which block four absorbs because `y j₀ ≤ c₄`; and a minimal-cardinality
subset of the small coordinates of `S` reaching what is left. That subset overshoots by less than
`v`, so it fits in `c₂` once `(Y - c₁ - y i₀ - y j₀) + v ≤ c₂`.

This widens the window of `Gap212.Packing.admitsPartition₄_of_singleton_block` from
`c₂ - (Y - c₁) + y i₀` to `c₂ - (Y - c₁) + y i₀ + y j₀`: a second coordinate, parked in the block
whose capacity `c₄ = 8ω₀` the first cannot use, buys its own mass as further room for the
subset-sum step. That second `δ` is the whole distance between
`Gap212.conditionD_at_datum_mid_band` and `Gap212.conditionD_at_datum_band_2`.

Neither `i₀` nor `j₀` need lie in `S`, and if the two singletons already cover the deficit the
second block is left empty. -/
theorem admitsPartition₄_of_two_singletons {ℓ : ℕ} {y : Fin ℓ → ℝ} {c₁ c₂ c₃ c₄ v : ℝ}
    {S : Finset (Fin ℓ)} {i₀ j₀ : Fin ℓ} (hij : i₀ ≠ j₀)
    (hS : ∀ i ∈ S, y i ≤ v) (hv0 : 0 ≤ v) (hc₂ : 0 ≤ c₂)
    (hi₀ : y i₀ ≤ c₃) (hj₀ : y j₀ ≤ c₄)
    (hSsum : (∑ i, y i) - c₁ - y i₀ - y j₀ ≤ ∑ i ∈ (S.erase i₀).erase j₀, y i)
    (hvc : ((∑ i, y i) - c₁ - y i₀ - y j₀) + v ≤ c₂) :
    AdmitsPartition₄ y c₁ c₂ c₃ c₄ := by
  classical
  -- One construction serves both the case where the two singletons already carry the deficit
  -- (`J = ∅`) and the case where the subset-sum step is needed.
  have key : ∀ J : Finset (Fin ℓ), i₀ ∉ J → j₀ ∉ J →
      (∑ i, y i) - c₁ - y i₀ - y j₀ ≤ ∑ i ∈ J, y i → (∑ i ∈ J, y i) ≤ c₂ →
      AdmitsPartition₄ y c₁ c₂ c₃ c₄ := by
    intro J hi₀J hj₀J hJlo hJhi
    have hi₀T : i₀ ∉ insert j₀ J := fun h ↦ (Finset.mem_insert.1 h).elim hij hi₀J
    have hsumT : ∑ i ∈ insert i₀ (insert j₀ J), y i = y i₀ + (y j₀ + ∑ i ∈ J, y i) := by
      rw [Finset.sum_insert hi₀T, Finset.sum_insert hj₀J]
    have hsplit : (∑ i ∈ univ \ insert i₀ (insert j₀ J), y i)
        + ∑ i ∈ insert i₀ (insert j₀ J), y i = ∑ i, y i :=
      Finset.sum_sdiff (Finset.subset_univ _)
    rw [hsumT] at hsplit
    refine ⟨univ \ insert i₀ (insert j₀ J), J, {i₀}, ?_, ?_, ?_, by linarith, hJhi,
      by simpa using hi₀, ?_⟩
    · exact Finset.disjoint_left.2 fun a ha haJ ↦ (Finset.mem_sdiff.1 ha).2
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem haJ))
    · refine Finset.disjoint_left.2 fun a ha haK ↦ ?_
      rw [Finset.mem_singleton] at haK
      exact (Finset.mem_sdiff.1 ha).2 (haK ▸ Finset.mem_insert_self _ _)
    · exact Finset.disjoint_singleton_right.2 hi₀J
    · have hset : univ \ ((univ \ insert i₀ (insert j₀ J)) ∪ J ∪ ({i₀} : Finset (Fin ℓ)))
          = {j₀} := by
        ext a
        have h₁ : a = j₀ → ¬ a = i₀ := fun h h' ↦ hij (h' ▸ h)
        have h₂ : a = j₀ → a ∉ J := fun h ↦ h ▸ hj₀J
        simp only [mem_sdiff, mem_univ, true_and, mem_union, mem_insert, mem_singleton]
        tauto
      rwa [hset, Finset.sum_singleton]
  by_cases hle : (∑ i, y i) - c₁ - y i₀ - y j₀ ≤ 0
  · exact key ∅ (by simp) (by simp) (by simpa using hle) (by simpa using hc₂)
  · push Not at hle
    obtain ⟨J, hJsub, hJlo, hJhi⟩ :=
      exists_subset_sum_mem_Icc_of_subset ((S.erase i₀).erase j₀) y v
        ((∑ i, y i) - c₁ - y i₀ - y j₀)
        (fun i hi ↦ hS i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))) hv0 hle.le hSsum
    exact key J
      (fun h ↦ (Finset.notMem_erase i₀ S) (Finset.mem_of_mem_erase (hJsub h)))
      (fun h ↦ (Finset.notMem_erase j₀ (S.erase i₀)) (hJsub h))
      hJlo (by linarith)

/-- **A real number sits in one of the half-open intervals `[n d, (n+1) d)`.** The level `n` the
packing argument uses is `⌊D/d⌋`, and these are the only two facts about it the argument needs:
`n` coordinates at the floor `d` do not exceed the deficit, and `n + 1` of them do. -/
theorem exists_nat_mul_le_lt {D d : ℝ} (hd : 0 < d) (hD : 0 ≤ D) :
    ∃ n : ℕ, (n : ℝ) * d ≤ D ∧ D < ((n : ℝ) + 1) * d := by
  refine ⟨⌊D / d⌋₊, ?_, ?_⟩
  · rw [← le_div_iff₀ hd]; exact Nat.floor_le (div_nonneg hD hd.le)
  · rw [← div_lt_iff₀ hd]; exact Nat.lt_floor_add_one _

/-! ## The two sides, counted

`Gap212.Packing.Xi` caps the two sides separately, and its index set is cut by the numeric value of
the index, so each side is a filter of `univ`. These are the cardinalities of those two filters —
the only thing needed to turn a floor on every coordinate into a floor on a *side's* mass, which is
what the per-side argument of `Gap212.conditionD_at_datum_band_3` runs on. -/

/-- **The first side has `m₁` indices.** -/
theorem card_side_left (m₁ m₂ : ℕ) :
    (univ.filter (fun i : Fin (m₁ + m₂) ↦ (i : ℕ) < m₁)).card = m₁ := by
  rw [Finset.card_filter, Fin.sum_univ_add]
  simp

/-- **The second side has `m₂` indices.** -/
theorem card_side_right (m₁ m₂ : ℕ) :
    (univ.filter (fun i : Fin (m₁ + m₂) ↦ ¬ ((i : ℕ) < m₁))).card = m₂ := by
  rw [Finset.card_filter, Fin.sum_univ_add]
  simp

/-! ## The four-block engine

`Gap212.Packing.admitsPartition₄_of_singleton_block` and `admitsPartition₄_of_two_singletons` place
one named coordinate in block three and one in block four. Once a block may hold *two* coordinates
— which happens above `ω₀ = δ/4 = 41/10000`, where `2δ ≤ 8ω₀` — naming them stops scaling, so the
engine is stated for arbitrary block contents instead. It subsumes both of the singleton lemmas,
and `Gap212.conditionD_at_datum_band_4` runs all five of its branches through it. -/

/-- **The engine step with arbitrary contents for the two small blocks.** Given disjoint `T₃` and
`T₄` that fit in `c₃` and `c₄`, a minimal-cardinality subset of the small coordinates of `S` covers
what is left of the deficit `Y - c₁ - T₃ - T₄` and overshoots it by less than `v`, so it fits in
`c₂` once `(Y - c₁ - T₃ - T₄) + v ≤ c₂`. The complement carries `Y - (Y - c₁) = c₁`.

The window is `c₂ - (Y - c₁) + (T₃ + T₄)`: every unit of mass parked in a small block buys a unit
of room for the subset-sum step, and it is the *parked mass* and not the number of parked
coordinates that the window sees. Neither `T₃` nor `T₄` need meet `S`, and if they already cover
the deficit the second block is left empty. -/
theorem admitsPartition₄_of_blocks {ℓ : ℕ} {y : Fin ℓ → ℝ} {c₁ c₂ c₃ c₄ v : ℝ}
    {S T₃ T₄ : Finset (Fin ℓ)} (hTd : Disjoint T₃ T₄)
    (hT₃ : (∑ i ∈ T₃, y i) ≤ c₃) (hT₄ : (∑ i ∈ T₄, y i) ≤ c₄)
    (hS : ∀ i ∈ S, y i ≤ v) (hv0 : 0 ≤ v) (hc₂ : 0 ≤ c₂)
    (hSsum : (∑ i, y i) - c₁ - (∑ i ∈ T₃, y i) - (∑ i ∈ T₄, y i)
      ≤ ∑ i ∈ S \ (T₃ ∪ T₄), y i)
    (hvc : ((∑ i, y i) - c₁ - (∑ i ∈ T₃, y i) - (∑ i ∈ T₄, y i)) + v ≤ c₂) :
    AdmitsPartition₄ y c₁ c₂ c₃ c₄ := by
  classical
  -- one construction for both the empty-`J` case and the subset-sum case
  have key : ∀ J : Finset (Fin ℓ), Disjoint J T₃ → Disjoint J T₄ →
      (∑ i, y i) - c₁ - (∑ i ∈ T₃, y i) - (∑ i ∈ T₄, y i) ≤ ∑ i ∈ J, y i →
      (∑ i ∈ J, y i) ≤ c₂ → AdmitsPartition₄ y c₁ c₂ c₃ c₄ := by
    intro J hJ₃ hJ₄ hJlo hJhi
    refine ⟨univ \ (J ∪ T₃ ∪ T₄), J, T₃, ?_, ?_, ?_, ?_, hJhi, hT₃, ?_⟩
    · exact Finset.disjoint_left.2 fun a ha haJ ↦ (Finset.mem_sdiff.1 ha).2
        (Finset.mem_union_left _ (Finset.mem_union_left _ haJ))
    · exact Finset.disjoint_left.2 fun a ha ha₃ ↦ (Finset.mem_sdiff.1 ha).2
        (Finset.mem_union_left _ (Finset.mem_union_right _ ha₃))
    · exact hJ₃
    · have hsplit : (∑ i ∈ univ \ (J ∪ T₃ ∪ T₄), y i) + ∑ i ∈ J ∪ T₃ ∪ T₄, y i = ∑ i, y i :=
        Finset.sum_sdiff (Finset.subset_univ _)
      have hun : ∑ i ∈ J ∪ T₃ ∪ T₄, y i
          = (∑ i ∈ J, y i) + (∑ i ∈ T₃, y i) + ∑ i ∈ T₄, y i := by
        rw [Finset.sum_union (disjoint_union_left.2 ⟨hJ₄, hTd⟩), Finset.sum_union hJ₃]
      rw [hun] at hsplit
      linarith
    · have hcover : univ \ (univ \ (J ∪ T₃ ∪ T₄) ∪ J ∪ T₃) = T₄ := by
        ext a
        have h₁ : a ∈ J → a ∉ T₄ := fun h ↦ disjoint_left.1 hJ₄ h
        have h₂ : a ∈ T₃ → a ∉ T₄ := fun h ↦ disjoint_left.1 hTd h
        simp only [mem_sdiff, mem_univ, true_and, mem_union]
        tauto
      rwa [hcover]
  by_cases hle : (∑ i, y i) - c₁ - (∑ i ∈ T₃, y i) - (∑ i ∈ T₄, y i) ≤ 0
  · exact key ∅ (Finset.disjoint_empty_left _) (Finset.disjoint_empty_left _)
      (by simpa using hle) (by simpa using hc₂)
  · push Not at hle
    obtain ⟨J, hJsub, hJlo, hJhi⟩ :=
      exists_subset_sum_mem_Icc_of_subset (S \ (T₃ ∪ T₄)) y v
        ((∑ i, y i) - c₁ - (∑ i ∈ T₃, y i) - (∑ i ∈ T₄, y i))
        (fun i hi ↦ hS i (Finset.mem_sdiff.1 hi).1) hv0 hle.le hSsum
    refine key J ?_ ?_ hJlo (by linarith)
    · exact Finset.disjoint_left.2 fun a ha ha₃ ↦
        (Finset.mem_sdiff.1 (hJsub ha)).2 (Finset.mem_union_left _ ha₃)
    · exact Finset.disjoint_left.2 fun a ha ha₄ ↦
        (Finset.mem_sdiff.1 (hJsub ha)).2 (Finset.mem_union_right _ ha₄)

/-- **Removing a set from a sum costs at most that set's own mass**, when the summand is
nonnegative. This is what lets the engine's hypothesis be stated on all of `S` rather than on
`S \ (T₃ ∪ T₄)`. -/
theorem sum_sdiff_ge {ι : Type*} [DecidableEq ι] {S T : Finset ι} {y : ι → ℝ}
    (hy : ∀ i, 0 ≤ y i) : (∑ i ∈ S, y i) - (∑ i ∈ T, y i) ≤ ∑ i ∈ S \ T, y i := by
  have h1 : ∑ i ∈ S ∩ T, y i ≤ ∑ i ∈ T, y i :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun i _ _ ↦ hy i
  have hdj : Disjoint (S \ T) (S ∩ T) := Finset.disjoint_sdiff_inter S T
  have h2 : (∑ i ∈ S \ T, y i) + ∑ i ∈ S ∩ T, y i = ∑ i ∈ S, y i := by
    rw [← Finset.sum_union hdj]
    congr 1
    ext a
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  linarith

/-- **The elimination of the level `n`.** The bound `v = (Y - n d)/(N - n)` on the `(n+1)`-st
smallest coordinate is at most a window `Wp`, for every level `n` with `n d ≤ Y - c̄₁`, as soon as
`Wp` clears the floor `d` and the `n`-free inequality `(Y - N d) Wp ≤ c̄₁ (Wp - d)` holds.

This is the step each band above repeats by hand: `v ≤ Wp` is `Y - N d ≤ (N - n)(Wp - d)`, and
`n d ≤ Y - c̄₁` gives `(N - n) d ≥ c̄₁ - (Y - N d)`, which may be multiplied through once
`0 ≤ Wp - d`. Stated once here, it serves all five branches of
`Gap212.conditionD_at_datum_band_4`. -/
theorem le_window_of_core {N Y cb Wp d n : ℝ} (hd : 0 < d) (hA : 0 ≤ Wp - d)
    (hn : n * d ≤ Y - cb) (hcore : (Y - N * d) * Wp ≤ cb * (Wp - d)) :
    Y - n * d ≤ Wp * (N - n) := by
  have h1 : cb - (Y - N * d) ≤ (N - n) * d := by nlinarith
  have h2 : (Y - N * d) * d ≤ ((N - n) * (Wp - d)) * d := by
    nlinarith [mul_le_mul_of_nonneg_right h1 hA]
  have h3 : Y - N * d ≤ (N - n) * (Wp - d) := le_of_mul_le_mul_right h2 hd
  nlinarith

end Gap212.Packing

namespace Gap212

open Finset Gap212.Bridges Gap212.Defs Gap212.Packing

/-! ## The capacity row and the chamber

`Gap212.Defs.ConditionD` takes the four capacities as one function of `(γ, ω₀)` and the chamber as
a set of pairs, so the quantifier over the chamber belongs to the condition rather than to the
statement using it. Both are written here in the datum's own numerals: `gap212Params.δ` for the
support's `δ`, `Gap212.slack` for the fixed `ϵ = 10⁻¹⁰`. -/

/-- **The Condition D capacity row at `p_⋆`**: `c₁ = γ - 2δ - 8ω₀ - ϵ`, `c₂ = 1/2 - γ - 2ω₀ - ϵ`,
`c₃ = 4ω₀ + δ - ϵ`, `c₄ = 8ω₀`, indexed by `Fin 4` as `Gap212.Defs.ConditionD` consumes them. -/
noncomputable def capD (γ ω₀ : ℝ) : Fin 4 → ℝ := fun i ↦
  if i = 0 then γ - 2 * gap212Params.δ - 8 * ω₀ - slack
  else if i = 1 then 1 / 2 - γ - 2 * ω₀ - slack
  else if i = 2 then 4 * ω₀ + gap212Params.δ - slack
  else 8 * ω₀

/-- **The Type IIc chamber at `p_⋆`**, cut at a level ceiling `ω₀ᵘᵖ`: the exponent `γ` runs over
`[ξ₂ - ϵ, 1/3 + 8ω + 7δ/3 + 3ϵ]` with `ξ₂ = 2/5`, and the level `ω₀` over `[0, ω₀ᵘᵖ]`.

Condition D at the datum is this with `ω₀ᵘᵖ = ω(1,1)`. The ceiling is a parameter so that the
condition can be proved band by band. -/
def chamberD (ω ω₀up : ℝ) : Set (ℝ × ℝ) :=
  {p | 2 / 5 - slack ≤ p.1 ∧ p.1 ≤ 1 / 3 + 8 * ω + 7 * gap212Params.δ / 3 + 3 * slack ∧
    0 ≤ p.2 ∧ p.2 ≤ ω₀up}

/-- **The same chamber with a level floor**: `ω₀ ∈ (ω₀lo, ω₀up]` instead of `[0, ω₀up]`. -/
def chamberDBand (ω ω₀lo ω₀up : ℝ) : Set (ℝ × ℝ) :=
  {p | 2 / 5 - slack ≤ p.1 ∧ p.1 ≤ 1 / 3 + 8 * ω + 7 * gap212Params.δ / 3 + 3 * slack ∧
    ω₀lo < p.2 ∧ p.2 ≤ ω₀up}

/-- The first capacity: `capD γ ω₀ 0 = γ - 2δ - 8ω₀ - slack`. -/
theorem capD_zero (γ ω₀ : ℝ) : capD γ ω₀ 0 = γ - 2 * gap212Params.δ - 8 * ω₀ - slack := by
  rfl

/-- The second capacity: `capD γ ω₀ 1 = 1/2 - γ - 2ω₀ - slack`. -/
theorem capD_one (γ ω₀ : ℝ) : capD γ ω₀ 1 = 1 / 2 - γ - 2 * ω₀ - slack := by
  rfl

/-- The third capacity: `capD γ ω₀ 2 = 4ω₀ + δ - slack`. -/
theorem capD_two (γ ω₀ : ℝ) : capD γ ω₀ 2 = 4 * ω₀ + gap212Params.δ - slack := by
  rfl

/-- The fourth capacity: `capD γ ω₀ 3 = 8ω₀`. -/
theorem capD_three (γ ω₀ : ℝ) : capD γ ω₀ 3 = 8 * ω₀ := by
  rfl

/-! ## `γ` cancels from the capacity sum

The first capacity rises with `γ` and the second falls with it by the same amount, so the total
capacity depends only on the level. That is what lets one argument serve the whole `γ`-range. -/

/-- **The capacity sum is `γ`-free**: `c₁ + c₂ + c₃ + c₄ = 1209/2500 + 2ω₀ - 3ϵ` at `δ = 41/2500`.

The `γ` of `c₁` cancels against the `-γ` of `c₂`, and the level coefficients are
`-8 - 2 + 4 + 8 = +2`, so the sum *grows* with `ω₀` and its worst case is the endpoint `ω₀ = 0`,
where it is `1209/2500 - 3ϵ = 0.4836 - 3·10⁻¹⁰`. -/
theorem capD_sum (γ ω₀ : ℝ) :
    capD γ ω₀ 0 + capD γ ω₀ 1 + capD γ ω₀ 2 + capD γ ω₀ 3 =
      1209 / 2500 + 2 * ω₀ - 3 * slack := by
  rw [capD_zero, capD_one, capD_two, capD_three, show gap212Params.δ = 41 / 2500 from rfl]
  ring

/-- **The capacity sum beats the largest pooled rough mass**, with room to spare: at any `ω₀ ≥ 0`
the four capacities total at least `1209/2500 - 3ϵ = 0.4836 - 3·10⁻¹⁰`, against the
`1081/2500 = 0.4324` of `Gap212.total_le_datum`. The margin is `128/2500 - 3ϵ = 0.0512 - 3·10⁻¹⁰`,
and it is `γ`-independent by `Gap212.capD_sum`.

So the *sum* condition is comfortable everywhere on the chamber. What is not comfortable is the
distribution: three of the four capacities are small, and `c₄` vanishes at `ω₀ = 0`. -/
theorem pooled_lt_capD_sum {γ ω₀ : ℝ} (hω₀ : 0 ≤ ω₀) :
    (1081 : ℝ) / 2500 < capD γ ω₀ 0 + capD γ ω₀ 1 + capD γ ω₀ 2 + capD γ ω₀ 3 := by
  rw [capD_sum, slack]
  linarith

/-! ## No single bin absorbs the profile

Each capacity is bounded on the chamber by a number below `1081/2500`, and that pooled mass is
attained by a profile of the check set. Together these say that the trivial partition — everything
in the first block — cannot discharge Condition D at any chamber point, which is what separates it
from Conditions A′ and B at this datum. -/

/-- **`c₁ ≤ 987/2500 + 2ϵ = 0.3948 + 2·10⁻¹⁰`** on the chamber, attained at `γ` maximal and
`ω₀ = 0`. Here `1/3 + 8·(7/1000) + 7·(41/2500)/3 = 3207/7500 = 0.4276` and `2δ = 0.0328`. -/
theorem capD_zero_le {γ ω₀ : ℝ}
    (hγ : γ ≤ 1 / 3 + 8 * (7 / 1000 : ℝ) + 7 * gap212Params.δ / 3 + 3 * slack)
    (hω₀ : 0 ≤ ω₀) : capD γ ω₀ 0 ≤ 987 / 2500 + 2 * slack := by
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rw [hδ] at hγ
  rw [capD_zero, hδ]
  linarith

/-- **`c₂ ≤ 1/10`** on the chamber, attained at `γ = ξ₂ - ϵ = 2/5 - ϵ` and `ω₀ = 0`, where the two
copies of `ϵ` cancel exactly. -/
theorem capD_one_le {γ ω₀ : ℝ} (hγ : 2 / 5 - slack ≤ γ) (hω₀ : 0 ≤ ω₀) :
    capD γ ω₀ 1 ≤ 1 / 10 := by
  rw [capD_one]
  linarith

/-- **`c₃ ≤ 111/2500 = 0.0444`** on the chamber, attained at `ω₀ = ω(1,1) = 7/1000`:
`4·(7/1000) + 41/2500 = 111/2500`. -/
theorem capD_two_le {γ ω₀ : ℝ} (hω₀ : ω₀ ≤ (7 / 1000 : ℝ)) : capD γ ω₀ 2 ≤ 111 / 2500 := by
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  have hs : (0 : ℝ) < slack := by rw [slack]; norm_num
  rw [capD_two, hδ]
  linarith

/-- **`c₄ ≤ 7/125 = 0.056`** on the chamber, attained at `ω₀ = ω(1,1) = 7/1000`. -/
theorem capD_three_le {γ ω₀ : ℝ} (hω₀ : ω₀ ≤ (7 / 1000 : ℝ)) : capD γ ω₀ 3 ≤ 7 / 125 := by
  rw [capD_three]
  linarith

/-- **The flat profile at the top rung**, `(m, m') = (10, 10)` with every coordinate equal to
`1081/50000 = 0.02162`: ten coordinates on each side, each side saturating `B_{1,10} = 1081/5000`,
and every coordinate comfortably above the floor `δ = 41/2500 = 0.0164`. -/
noncomputable def flatDatumTuple : Fin (10 + 10) → ℝ := fun _ ↦ 1081 / 50000

/-- The coordinates of `flatDatumTuple` sum to `1081/2500`. -/
theorem sum_flatDatumTuple : ∑ i, flatDatumTuple i = 1081 / 2500 := by
  norm_num [flatDatumTuple]

/-- `flatDatumTuple` lies in `Xi (gap212Cap 10) (gap212Cap 10) 10 10 (41/2500)`. -/
theorem flatDatumTuple_mem_Xi :
    flatDatumTuple ∈ Xi (gap212Cap 10) (gap212Cap 10) 10 10 (41 / 2500 : ℝ) := by
  have hcap : gap212Cap 10 = 1081 / 5000 := gap212Cap_of_ten_le le_rfl
  refine ⟨fun i ↦ ⟨by norm_num [flatDatumTuple], by norm_num [flatDatumTuple]⟩, ?_, ?_⟩ <;>
    simp only [flatDatumTuple, sum_const, card_side_left, card_side_right, hcap] <;> norm_num

/-- **The trivial partition cannot discharge Condition D at `p_⋆`, at any chamber point.** The flat
profile of `Gap212.flatDatumTuple` lies in the check set at `(m, m') = (10, 10)` and carries the
full pooled mass `1081/2500 = 0.4324`, which strictly exceeds every one of the four capacities:
`0.3948`, `0.1`, `0.0444`, `0.056`.

So `Gap212.Packing.admitsPartition₄_of_total_le` — the route that settles Conditions A′ and B at
this datum — is unavailable here for every `(γ, ω₀)`, and all four blocks are genuinely in play.
Compare `Gap212.Packing.conditionD`, the Point A case analysis, where the pooled mass is `17/50`
and the cap row has two rungs. -/
theorem exists_mem_Xi_gt_capD {γ ω₀ : ℝ} (hγ : 2 / 5 - slack ≤ γ)
    (hγ' : γ ≤ 1 / 3 + 8 * (7 / 1000 : ℝ) + 7 * gap212Params.δ / 3 + 3 * slack)
    (hω₀ : 0 ≤ ω₀) (hω₀' : ω₀ ≤ (7 / 1000 : ℝ)) :
    ∃ y ∈ Xi (gap212Cap 10) (gap212Cap 10) 10 10 (41 / 2500 : ℝ),
      capD γ ω₀ 0 < ∑ j, y j ∧ capD γ ω₀ 1 < ∑ j, y j ∧
        capD γ ω₀ 2 < ∑ j, y j ∧ capD γ ω₀ 3 < ∑ j, y j := by
  have h0 := capD_zero_le hγ' hω₀
  rw [slack] at h0
  refine ⟨flatDatumTuple, flatDatumTuple_mem_Xi, ?_, ?_, ?_, ?_⟩ <;> rw [sum_flatDatumTuple] <;>
    linarith [capD_one_le hγ hω₀, capD_two_le (γ := γ) hω₀', capD_three_le (γ := γ) hω₀']

/-! ## The affine mass bounds

The cap row is not affine, but it sits under an affine function of the rung index, exactly at the
fourth and fifth rungs. That one inequality replaces the cell enumeration: it turns a bound on the
*number* of rough factors into a bound on their pooled mass, and conversely. -/

/-- **The cap row lies under `(773 + 36m)/5000`**, with equality at `m = 4` and `m = 5`
(`917/5000` and `953/5000`). Beyond the tenth rung the row is constant at `1081/5000` while the
affine function keeps rising, and `1081 ≤ 773 + 36·10 = 1133` already. -/
theorem gap212Cap_le_affine (m : ℕ) : gap212Cap m ≤ (773 + 36 * (m : ℝ)) / 5000 := by
  rcases le_or_gt 10 m with h | h
  · have hm : (10 : ℝ) ≤ m := by exact_mod_cast h
    rw [gap212Cap_of_ten_le h]; linarith
  · interval_cases m <;> norm_num [gap212Cap]

/-- **The pooled mass under the affine cap bound**: a profile of the check set at `p_⋆` with
`m + m'` rough factors has mass at most `(1546 + 36(m + m'))/5000`.

At `m + m' = 7` this reads `1798/5000 = 0.3596`, and that is the inequality which forces at least
eight rough factors once the mass exceeds the first capacity. -/
theorem total_le_affine_datum {m m' : ℕ} {y : Fin (m + m') → ℝ}
    (hy : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ)) :
    ∑ i, y i ≤ (1546 + 36 * ((m : ℝ) + (m' : ℝ))) / 5000 := by
  linarith [total_le hy, gap212Cap_le_affine m, gap212Cap_le_affine m']

/-- **The cap row lies under `(874 + 21m)/5000`**, with equality at `m = 8` and `m = 9`
(`1042/5000` and `1063/5000`). One affine bound cannot be tight at both ends of the row — the row's
increments run `17, 81, 42, 36, 30, 33, 26, 21, 18`, which is not concave — so the mass bound wants
several of them: this one is what makes `Gap212.total_le_affine_datum₂` exact at `N = 17` and
`N = 18`, where the better of `Gap212.total_le_affine_datum` and the flat bound `1081/2500`
overshoots by `53/5000` and `36/5000`. -/
theorem gap212Cap_le_affine₂ (m : ℕ) : gap212Cap m ≤ (874 + 21 * (m : ℝ)) / 5000 := by
  rcases le_or_gt 10 m with h | h
  · have hm : (10 : ℝ) ≤ m := by exact_mod_cast h
    rw [gap212Cap_of_ten_le h]; linarith
  · interval_cases m <;> norm_num [gap212Cap]

/-- **The cap row lies under `(901 + 18m)/5000`**, with equality at `m = 9` and `m = 10`
(`1063/5000` and `1081/5000`), hence at every rung from the tenth on. This is the bound that is
exact at `N = 19`. -/
theorem gap212Cap_le_affine₃ (m : ℕ) : gap212Cap m ≤ (901 + 18 * (m : ℝ)) / 5000 := by
  rcases le_or_gt 10 m with h | h
  · have hm : (10 : ℝ) ≤ m := by exact_mod_cast h
    rw [gap212Cap_of_ten_le h]; linarith
  · interval_cases m <;> norm_num [gap212Cap]

/-- **The pooled mass under the second affine cap bound**: at most `(1748 + 21(m + m'))/5000`.

Together with `Gap212.total_le_affine_datum`, `total_le_affine_datum₃` and the flat bound
`1081/2500` of `Gap212.total_le_datum`, this pins the pooled mass at the tight cells to the exact
maximum of `B_{1,m} + B_{1,m'}` over the cells of that size — for every `N` from `16` to `26`, in
particular `2105/5000 = 0.421` at `N = 17` (cell `(8, 9)`) and `2126/5000 = 0.4252` at `N = 18`
(cell `(9, 9)`). -/
theorem total_le_affine_datum₂ {m m' : ℕ} {y : Fin (m + m') → ℝ}
    (hy : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ)) :
    ∑ i, y i ≤ (1748 + 21 * ((m : ℝ) + (m' : ℝ))) / 5000 := by
  linarith [total_le hy, gap212Cap_le_affine₂ m, gap212Cap_le_affine₂ m']

/-- **The pooled mass under the third affine cap bound**: at most `(1802 + 18(m + m'))/5000`, exact
at `N = 19` (`2144/5000 = 0.4288`, cell `(9, 10)`). -/
theorem total_le_affine_datum₃ {m m' : ℕ} {y : Fin (m + m') → ℝ}
    (hy : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ)) :
    ∑ i, y i ≤ (1802 + 18 * ((m : ℝ) + (m' : ℝ))) / 5000 := by
  linarith [total_le hy, gap212Cap_le_affine₃ m, gap212Cap_le_affine₃ m']

/-- **The cap row lies under `(728 + 49m)/5000`**, with equality at `m = 1` and `m = 3`
(`777/5000` and `875/5000`). The row's first increment is the whole of `B_{1,1} = 777/5000` and its
second is only `17/5000`, so no affine bound is tight at both `m = 1` and `m = 2`; this one clears
`m = 2` by `32/5000` and is what makes `Gap212.total_le_affine_datum₄` exact at the even sizes
`N = 2, 4, 6`.

`N = 4` is the one that matters: `(1456 + 49·4)/5000 = 1652/5000 = 0.3304` is below the least first
capacity `2/5 - 2δ - 8ω₀ - 2ϵ` on the whole band `ω₀ ≤ 1/250`, where that is `1676/5000 - 2ϵ`. So a
cell with at most four rough factors cannot overflow `c₁`, which is what cuts the rung range of
`Gap212.conditionD_at_datum_band_2` to `5 ≤ N ≤ 26`. -/
theorem gap212Cap_le_affine₄ (m : ℕ) : gap212Cap m ≤ (728 + 49 * (m : ℝ)) / 5000 := by
  rcases le_or_gt 10 m with h | h
  · have hm : (10 : ℝ) ≤ m := by exact_mod_cast h
    rw [gap212Cap_of_ten_le h]; linarith
  · interval_cases m <;> norm_num [gap212Cap]

/-- **The cap row lies under `(799 + 31m)/5000`**, with equality at `m = 7` (`1016/5000`). Together
with the others this pins the pooled mass at `N = 12` to `1970/5000` and at `N = 13` to
`2001/5000`, against exact cell maxima `1969/5000` and `1999/5000` — the two sizes that decide
where the high branch of `Gap212.conditionD_at_datum_band_2` stops. -/
theorem gap212Cap_le_affine₅ (m : ℕ) : gap212Cap m ≤ (799 + 31 * (m : ℝ)) / 5000 := by
  rcases le_or_gt 10 m with h | h
  · have hm : (10 : ℝ) ≤ m := by exact_mod_cast h
    rw [gap212Cap_of_ten_le h]; linarith
  · interval_cases m <;> norm_num [gap212Cap]

/-- **The cap row lies under `(834 + 26m)/5000`**, with equality at `m = 7` and `m = 8`
(`1016/5000` and `1042/5000`). This is the bound that is exact at `N = 14`, `15` and `16`. -/
theorem gap212Cap_le_affine₆ (m : ℕ) : gap212Cap m ≤ (834 + 26 * (m : ℝ)) / 5000 := by
  rcases le_or_gt 10 m with h | h
  · have hm : (10 : ℝ) ≤ m := by exact_mod_cast h
    rw [gap212Cap_of_ten_le h]; linarith
  · interval_cases m <;> norm_num [gap212Cap]

/-- **The pooled mass under the fourth affine cap bound**: at most `(1456 + 49(m + m'))/5000`,
exact at `N = 2`, `4` and `6`. At `N = 4` this reads `1652/5000 = 0.3304`. -/
theorem total_le_affine_datum₄ {m m' : ℕ} {y : Fin (m + m') → ℝ}
    (hy : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ)) :
    ∑ i, y i ≤ (1456 + 49 * ((m : ℝ) + (m' : ℝ))) / 5000 := by
  linarith [total_le hy, gap212Cap_le_affine₄ m, gap212Cap_le_affine₄ m']

/-- **The pooled mass under the fifth affine cap bound**: at most `(1598 + 31(m + m'))/5000`, which
is `1970/5000` at `N = 12` and `2001/5000` at `N = 13`. -/
theorem total_le_affine_datum₅ {m m' : ℕ} {y : Fin (m + m') → ℝ}
    (hy : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ)) :
    ∑ i, y i ≤ (1598 + 31 * ((m : ℝ) + (m' : ℝ))) / 5000 := by
  linarith [total_le hy, gap212Cap_le_affine₅ m, gap212Cap_le_affine₅ m']

/-- **The pooled mass under the sixth affine cap bound**: at most `(1668 + 26(m + m'))/5000`, exact
at `N = 14` (`2032/5000`), `15` (`2058/5000`) and `16` (`2084/5000`). -/
theorem total_le_affine_datum₆ {m m' : ℕ} {y : Fin (m + m') → ℝ}
    (hy : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ)) :
    ∑ i, y i ≤ (1668 + 26 * ((m : ℝ) + (m' : ℝ))) / 5000 := by
  linarith [total_le hy, gap212Cap_le_affine₆ m, gap212Cap_le_affine₆ m']

/-- **The floor on the coordinates, pooled**: `m + m'` coordinates each at least `δ = 41/2500`
carry at least `(m + m')δ`. This is what keeps the bound on the fifth smallest coordinate above the
floor, which the engine needs. -/
theorem card_delta_le_total {m m' : ℕ} {y : Fin (m + m') → ℝ}
    (hy : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ)) :
    ((m : ℝ) + (m' : ℝ)) * (41 / 2500) ≤ ∑ i, y i := by
  simpa using mul_le_sum_of_card_le (S := univ) (by norm_num) (fun i ↦ (hy.1 i).1) le_rfl

/-! ## The floor, read one side at a time

The mass bounds above pool the two sides: they bound `Y = Y₁ + Y₂` by a function of `N = m + m'`
alone, and that is all the two-block and mid-band arguments need. A floor `f` valid for *every*
coordinate says more than that, because each side is capped on its own: `m` coordinates above `f`
on the first side already force `m f ≤ B_{1,m}`, which caps the side's *count* and so, through the
monotone cap row, the side's mass.

This is what closes the third band's high branch, where the floor is `c₃ = 4ω₀ + δ - ϵ`. See
`Gap212.conditionD_at_datum_band_3`. -/

/-- **A floor on every coordinate is a floor on each side's mass.** The first side's `m`
coordinates all exceed `f` and sum to at most `B_{1,m}`, so `m f ≤ B_{1,m}`; likewise for the
second.

Both halves are `Gap212.Packing.card_side_left`/`card_side_right` against the two capped sums of
`Gap212.Packing.Xi`. Nothing about `f` is assumed: the inequality is vacuous when `f ≤ 0`. -/
theorem side_floor_le_cap {m m' : ℕ} {y : Fin (m + m') → ℝ} {f : ℝ}
    (hy : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ))
    (hf : ∀ i, f ≤ y i) :
    (m : ℝ) * f ≤ gap212Cap m ∧ (m' : ℝ) * f ≤ gap212Cap m' := by
  classical
  refine ⟨?_, ?_⟩
  · have h := Finset.card_nsmul_le_sum
      (univ.filter (fun i : Fin (m + m') ↦ (i : ℕ) < m)) y f fun i _ ↦ hf i
    rw [nsmul_eq_mul, card_side_left] at h
    exact h.trans hy.2.1
  · have h := Finset.card_nsmul_le_sum
      (univ.filter (fun i : Fin (m + m') ↦ ¬ ((i : ℕ) < m))) y f fun i _ ↦ hf i
    rw [nsmul_eq_mul, card_side_right] at h
    exact h.trans hy.2.2

/-- **Above `ω₀ = 1/250` a side of seven or more rough factors cannot clear `c₃`.** If every
coordinate of a side of `m` factors exceeds `c₃ = 4ω₀ + δ - ϵ` and `ω₀ > 1/250`, then `m ≤ 6`.

The row never exceeds `1081/5000 = 0.2162` (`Gap212.gap212Cap_le`), while `c₃ > 4/250 + δ - ϵ`
makes `7c₃ > 2268/10000 - 7ϵ = 0.2268 - 7·10⁻¹⁰`. So the seventh factor has nowhere to go.

Both sides being capped at six caps the cell at `N = 12` *and* pins the pooled mass to
`B_{1,m} + B_{1,m'}` with `m, m' ≤ 6` — at worst `2·983/5000 = 1966/5000 = 0.3932`, where the
affine bounds of `Gap212.total_le_affine_datum₅` give only `1970/5000 = 0.394`. Those `4/5000` are
the whole distance between `Gap212.conditionD_at_datum_band_2` and
`Gap212.conditionD_at_datum_band_3`: with the affine bound the high branch's
`(Y - N c₃) W ≤ c̄₁ (W - c₃)` fails at `N = 12` for `ω₀ ∈ (0.004033, 0.004113)`, and with the
per-side bound it does not fail there at all. -/
theorem side_le_six {m : ℕ} {w : ℝ} (hw0 : 1 / 250 < w)
    (h : (m : ℝ) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) ≤ gap212Cap m) : m ≤ 6 := by
  by_contra hcon
  have h7 : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 7 ≤ m)
  have hcap := gap212Cap_le m
  nlinarith

/-- **Above `ω₀ = 43/10000` a side of six or more rough factors cannot clear `c₄`.** If every
coordinate of a side of `m` factors exceeds `c₄ = 8ω₀` and `ω₀ > 43/10000`, then `m ≤ 5`.

The sixth rung is the one that needs the row's own value: `6·8ω₀ > 0.2064` against
`B_{1,6} = 983/5000 = 0.1966`, which is why the bound turns over at
`ω₀ = 983/240000 ≈ 0.0040958` — below this band's floor. From the seventh rung on the flat bound
suffices, `7·8ω₀ > 0.2408` exceeding `1081/5000 = 0.2162`.

This is `Gap212.side_le_six` for the *fourth* block's capacity, which on this band is the larger of
the two small ones. It caps the cell at `N = 10` and the pooled mass at
`2·953/5000 = 1906/5000 = 0.3812`, and that is what
`Gap212.datumD_band4_high_core` is verified against. -/
theorem side_le_five {m : ℕ} {w : ℝ} (hw0 : 43 / 10000 < w)
    (h : (m : ℝ) * (8 * w) ≤ gap212Cap m) : m ≤ 5 := by
  by_contra hcon
  have hcap := gap212Cap_le m
  by_cases hm7 : 7 ≤ m
  · have h7 : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm7
    nlinarith
  · have hm6 : m = 6 := by omega
    subst hm6
    norm_num [gap212Cap] at h
    linarith

/-- **A floor holding off one coordinate is still a floor on each side's mass.** If every
coordinate but `i₀` exceeds `f ≥ δ`, then each side of `m` factors obeys `(m - 1) f + δ ≤ B_{1,m}`:
the exceptional coordinate can sit on only one of the two sides, and there it still carries `δ`.

`Gap212.side_floor_le_cap` with one coordinate excused. It is what the one-parked branch of
`Gap212.conditionD_at_datum_band_4` reads its own branch condition with — that branch knows every
coordinate but the parked one exceeds `c₃`, and nothing else. -/
theorem side_floor_le_cap_except {m m' : ℕ} {y : Fin (m + m') → ℝ} {f : ℝ}
    {i₀ : Fin (m + m')}
    (hy : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ))
    (hδy : ∀ i, (41 / 2500 : ℝ) ≤ y i) (hfδ : (41 / 2500 : ℝ) ≤ f)
    (hf : ∀ i, i ≠ i₀ → f ≤ y i) :
    ((m : ℝ) - 1) * f + 41 / 2500 ≤ gap212Cap m ∧
      ((m' : ℝ) - 1) * f + 41 / 2500 ≤ gap212Cap m' := by
  classical
  have key : ∀ (T : Finset (Fin (m + m'))) (k : ℕ), T.card = k →
      ((k : ℝ) - 1) * f + 41 / 2500 ≤ ∑ i ∈ T, y i := by
    intro T k hk
    by_cases hmem : i₀ ∈ T
    · have hk1 : 1 ≤ k := by
        rw [← hk]
        exact Finset.card_pos.2 ⟨i₀, hmem⟩
      have hcard : ((T.erase i₀).card : ℝ) = (k : ℝ) - 1 := by
        rw [Finset.card_erase_of_mem hmem, hk, Nat.cast_sub hk1]
        norm_num
      have h := Finset.card_nsmul_le_sum (T.erase i₀) y f
        fun a ha ↦ hf a (Finset.mem_erase.1 ha).1
      rw [nsmul_eq_mul, hcard] at h
      have hsum : y i₀ + ∑ i ∈ T.erase i₀, y i = ∑ i ∈ T, y i :=
        Finset.add_sum_erase _ y hmem
      linarith [hδy i₀]
    · have h := Finset.card_nsmul_le_sum T y f fun a ha ↦ hf a (fun hc ↦ hmem (hc ▸ ha))
      rw [nsmul_eq_mul, hk] at h
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
  refine ⟨le_trans (key _ m (card_side_left m m')) hy.2.1,
    le_trans (key _ m' (card_side_right m m')) hy.2.2⟩

/-- **Above `ω₀ = 43/10000` a side of seven or more rough factors cannot clear `c₃` off one
coordinate.** If every coordinate of a side of `m` factors except at most one exceeds
`c₃ = 4ω₀ + δ - ϵ` and `ω₀ > 43/10000`, then `m ≤ 6`.

At `m = 7` the hypothesis reads `6c₃ + δ > 0.218`, above the whole row's `1081/5000 = 0.2162`. So
the one-parked branch's cell is pinned to `N ≤ 12` and its pooled mass to `B_{1,m} + B_{1,m'}` with
`m, m' ≤ 6` — and it is that bound, not the affine ones, that closes the branch above `ω₀ = 1/200`:
the affine bounds allow `1939/5000` at `N = 11` where the cell maximum is `1936/5000`, and the
hypothesis `(m - 1)c₃ + δ ≤ B_{1,m}` kills the surviving cell `(5, 6)` outright above
`ω₀ = 491/100000 + ϵ/4`. -/
theorem side_le_six_except {m : ℕ} {w : ℝ} (hw0 : 43 / 10000 < w)
    (h : ((m : ℝ) - 1) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 41 / 2500 ≤ gap212Cap m) :
    m ≤ 6 := by
  by_contra hcon
  have h7 : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 7 ≤ m)
  have hcap := gap212Cap_le m
  nlinarith

/-! ## The one numerical inequality

Everything about the two-block split at `ω₀ ≤ 7/10000` comes down to this: the bound `v` on the
fifth smallest coordinate is below the reserve `c₂ - D = 1/2 - Y - 2δ - 10ω₀ - 2ϵ`, which is
`γ`-free. -/

/-- **The fifth smallest coordinate fits in the reserve.** With `N` rough factors of pooled mass
`Y` and `v (N - 4) = Y - 4δ`, the bound `v` on the fifth smallest is at most
`1/2 - Y - 2δ - 10ω₀ - 2ϵ` whenever `N ≥ 8`, `N` misses `(17, 18)`, and `ω₀ ≤ 7/10000`.

Two polynomial inequalities in `N` do it, one for each mass bound. Under the affine bound
`Y ≤ (1546 + 36N)/5000` the requirement is `36N² - 863N + 4238 ≤ 0`, which holds on `[8, 17]` — its
value at `N = 17` is `-29`. Under the flat bound `Y ≤ 1081/2500` it is `2390 ≤ 139N`, which holds
from `N = 18` on. The tightest cases are the two endpoints of the gap: `N = 17` under the affine
bound, where `v` falls short of the reserve by `29/65000`, and `N = 18` under the flat bound, where
it falls short by `104/65000`.

`hNgap` is why the level ceiling is `7/10000` rather than the `121/162500 ≈ 0.000745` an
integer-`N` statement allows. The two ranges no longer overlap: at the real crossover
`N = 154/9 ≈ 17.111`, where the two mass bounds agree at `1081/2500`, the requirement is
`ω₀ ≤ 2013/2950000 ≈ 0.000682`, which `7/10000 = 0.0007` exceeds. Only integers are ever passed —
`N = m + m'` — so excluding `(17, 18)` costs nothing and buys the larger ceiling. -/
theorem datumD_fifth_le_reserve {N Y v w : ℝ} (hN : 8 ≤ N) (hNgap : N ≤ 17 ∨ 18 ≤ N)
    (hYcap : Y ≤ 1081 / 2500) (hYaff : Y ≤ (1546 + 36 * N) / 5000)
    (hw : w ≤ 7 / 10000) (hv : v * (N - 4) = Y - 4 * (41 / 2500)) :
    v ≤ 1 / 2 - Y - 82 / 2500 - 10 * w - 2 / 10 ^ 10 := by
  have hn4 : (0 : ℝ) < N - 4 := by linarith
  refine le_of_mul_le_mul_right ?_ hn4
  rw [hv]
  have hWlo : (2301 : ℝ) / 5000 - Y - 2 / 10 ^ 10
      ≤ 1 / 2 - Y - 82 / 2500 - 10 * w - 2 / 10 ^ 10 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hWlo hn4.le
  refine le_trans ?_ hmul
  have h3 : (0 : ℝ) ≤ N - 3 := by linarith
  rcases hNgap with h17 | h18
  · nlinarith [mul_nonneg (sub_nonneg.2 hN) (sub_nonneg.2 h17),
      mul_nonneg (sub_nonneg.2 hYaff) h3]
  · nlinarith [mul_nonneg (sub_nonneg.2 hYcap) h3, h18]

/-! ## Condition D on the low-level chamber -/

/-- **Condition D holds at `p_⋆` for every cell, every `γ`, and every level `ω₀ ≤ 7/10000`.**

The capacities are `Gap212.capD`'s, with `δ = gap212Params.δ = 41/2500` and
`ϵ = Gap212.slack = 10⁻¹⁰`, and the chamber is `Gap212.chamberD` at the datum's level
`ω(1,1) = 7/1000` (`Gap212.omegaMax_gap212Params`) with the level ceiling cut to `7/10000`; the
bands above it are `Gap212.conditionD_at_datum_mid_band` and its successors. The ceiling is the one
this argument has and not a convenience: the `N = 17` case of `Gap212.datumD_fifth_le_reserve`
fails past `ω₀ = 121/162500 ≈ 0.000745`.

Blocks three and four are empty throughout. At `ω₀ = 0` this is forced — `c₄ = 0` and
`c₃ = δ - ϵ` is below the floor `δ` on a single coordinate — and above it, it is merely convenient.
So the content is a two-block split at `c₁ = γ - 2δ - 8ω₀ - ϵ` and `c₂ = 1/2 - γ - 2ω₀ - ϵ`, whose
sum `1/2 - 2δ - 10ω₀ - 2ϵ` is at least `2301/5000 = 0.4602` here, against a pooled mass of at most
`1081/2500 = 0.4324`.

No bound on `m` or `m'` is needed. The condition is usually stated at `m, m' ≤ ⌊1/δ⌋ = 60`, but the
two mass bounds hold at every rung, and `m ≥ 14` empties the check set anyway. -/
theorem conditionD_at_datum_low_level (j j' : Fin gap212Params.n) {m m' : ℕ} :
    ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      capD (chamberD (omegaMax gap212Params j j') (7 / 10000)) := by
  classical
  rw [omegaMax_gap212Params j j']
  rintro ⟨γ, w⟩ ⟨hγ, hγ', hw0, hw⟩ y hy
  have hs : slack = 1 / 10 ^ 10 := by rw [slack]
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rw [hs] at hγ
  rw [hδ, hs] at hγ'
  have hy' : y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ) := hy
  change AdmitsPartition₄ y (capD γ w 0) (capD γ w 1) (capD γ w 2) (capD γ w 3)
  rw [capD_zero, capD_one, capD_two, capD_three, hδ, hs]
  have hc₂ : (0 : ℝ) ≤ 1 / 2 - γ - 2 * w - 1 / 10 ^ 10 := by linarith
  have hc₃ : (0 : ℝ) ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10 := by linarith
  have hc₄ : (0 : ℝ) ≤ 8 * w := by linarith
  by_cases hDle : ∑ i, y i ≤ γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10
  · exact admitsPartition₄_of_total_le hDle hc₂ hc₃ hc₄
  push Not at hDle
  refine admitsPartition₄_of_partition₂ ?_ hc₃ hc₄
  -- The two mass bounds on the profile, and the floor on its coordinates.
  have hYcap := total_le_datum hy'
  have hYaff := total_le_affine_datum hy'
  have hδy : ∀ i, (41 / 2500 : ℝ) ≤ y i := fun i ↦ (hy'.1 i).1
  -- `c₁ ≥ 904/2500 - 2ϵ = 0.3616 - 2·10⁻¹⁰` on the region, and at most seven rough factors
  -- cap the pooled mass at `1798/5000 = 0.3596`.
  have hN8 : 8 ≤ m + m' := by exact_mod_cast (show (7 : ℝ) < m + m' by linarith)
  have hNgap : (m : ℝ) + m' ≤ 17 ∨ 18 ≤ (m : ℝ) + m' := by
    rcases (by omega : m + m' ≤ 17 ∨ 18 ≤ m + m') with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  -- The bound on the fifth smallest coordinate, and five coordinates below it, carrying at least
  -- `5δ = 0.082 ≥ D`.
  obtain ⟨v, hvmul, hdv, -, hSsum⟩ := exists_level_coords (n := 4) (by norm_num) hδy (by omega)
  push_cast at hvmul hSsum
  have hW := datumD_fifth_le_reserve (by exact_mod_cast hN8) hNgap hYcap hYaff hw hvmul
  exact admitsPartition₂_of_small_block (v := v)
    (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v))
    (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) (by linarith) (by linarith)
    (by linarith)

/-- **The chamber splits at the level floor.** Condition D on `[0, ω₀lo]` together with Condition D
on the band `(ω₀lo, ω₀up]` gives it on `[0, ω₀up]`: a chamber point has `ω₀ ≤ ω₀lo` or it does not,
and the two hypotheses cover the cases. The `γ` bounds are the same on both sides, so they carry
across unchanged. -/
theorem conditionD_of_band {ℓ : ℕ} {Ξ : Set (Fin ℓ → ℝ)} {ω ω₀lo ω₀up : ℝ}
    (hlow : Defs.ConditionD Ξ capD (chamberD ω ω₀lo))
    (hband : Defs.ConditionD Ξ capD (chamberDBand ω ω₀lo ω₀up)) :
    Defs.ConditionD Ξ capD (chamberD ω ω₀up) := by
  rintro ⟨γ, w⟩ hp y hy
  by_cases hw : w ≤ ω₀lo
  · exact hlow ⟨γ, w⟩ ⟨hp.1, hp.2.1, hp.2.2.1, hw⟩ y hy
  · exact hband ⟨γ, w⟩ ⟨hp.1, hp.2.1, lt_of_not_ge hw, hp.2.2.2⟩ y hy

/-- **Two consecutive bands splice.** Condition D on `(a, b]` and on `(b, c]` gives it on `(a, c]`:
a level in `(a, c]` either lies at or below `b` or above it, and the `γ` bounds are the same on
both sides. This is what lets the band above the low level be proved in pieces. -/
theorem conditionD_of_band_split {ℓ : ℕ} {Ξ : Set (Fin ℓ → ℝ)} {ω a b c : ℝ}
    (hlow : Defs.ConditionD Ξ capD (chamberDBand ω a b))
    (hhigh : Defs.ConditionD Ξ capD (chamberDBand ω b c)) :
    Defs.ConditionD Ξ capD (chamberDBand ω a c) := by
  rintro ⟨γ, w⟩ hp y hy
  by_cases hw : w ≤ b
  · exact hlow ⟨γ, w⟩ ⟨hp.1, hp.2.1, hp.2.2.1, hw⟩ y hy
  · exact hhigh ⟨γ, w⟩ ⟨hp.1, hp.2.1, lt_of_not_ge hw, hp.2.2.2⟩ y hy

/-- **The opening every band shares.** Unfold the chamber and the capacity row at `p_⋆`, and settle
the profiles whose pooled mass already fits in the first block by the trivial partition; what is
left is a profile overflowing `c₁`, at a level in `(lo, hi]`. -/
private theorem conditionD_band_of {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : hi ≤ 7 / 1000) {m m' : ℕ}
    (j j' : Fin gap212Params.n)
    (h : ∀ (γ w : ℝ) (y : Fin (m + m') → ℝ), 2 / 5 - 1 / 10 ^ 10 ≤ γ →
      γ ≤ 1 / 3 + 8 * (7 / 1000) + 7 * (41 / 2500) / 3 + 3 * (1 / 10 ^ 10) → lo < w → w ≤ hi →
      y ∈ Xi (gap212Cap m) (gap212Cap m') m m' (41 / 2500 : ℝ) →
      γ - 2 * (41 / 2500) - 8 * w - 1 / 10 ^ 10 < ∑ i, y i →
      AdmitsPartition₄ y (γ - 2 * (41 / 2500) - 8 * w - 1 / 10 ^ 10)
        (1 / 2 - γ - 2 * w - 1 / 10 ^ 10) (4 * w + 41 / 2500 - 1 / 10 ^ 10) (8 * w)) :
    ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      capD (chamberDBand (omegaMax gap212Params j j') lo hi) := by
  rw [omegaMax_gap212Params j j']
  rintro ⟨γ, w⟩ ⟨hγ, hγ', hw0, hw⟩ y hy
  have hs : slack = 1 / 10 ^ 10 := by rw [slack]
  have hδ : gap212Params.δ = 41 / 2500 := rfl
  rw [hs] at hγ
  rw [hδ, hs] at hγ'
  change AdmitsPartition₄ y (capD γ w 0) (capD γ w 1) (capD γ w 2) (capD γ w 3)
  rw [capD_zero, capD_one, capD_two, capD_three, hδ, hs]
  by_cases hDle : ∑ i, y i ≤ γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10
  · exact admitsPartition₄_of_total_le hDle (by linarith) (by linarith) (by linarith)
  exact h γ w y hγ hγ' hw0 hw hy (not_le.1 hDle)

/-! ## The band `7/10000 < ω₀ ≤ 1/400`

Above `7/10000` the two-block split of `Gap212.conditionD_at_datum_low_level` stops closing, and
the argument here replaces it by two, chosen by a dichotomy on the profile rather than on the cell.

Write `Y` for the pooled mass, `N = m + m'`, `D = Y - c₁` for the deficit, and

    W = c₂ - D = 1/2 - Y - 2δ - 10ω₀ - 2ϵ

for the reserve, which is `γ`-free because `c₁ + c₂` is. Let `d` be a floor valid for every
coordinate and `n = ⌊D/d⌋`, so that `n d ≤ D < (n+1) d`. Then `Gap212.Packing.exists_small_coords`
supplies `n + 1` coordinates at most

    v = (Y - n d)/(N - n) = d + (Y - N d)/(N - n),

and `n` of them already carry `n d`, which is at least `D` minus one coordinate. The two branches
differ only in `d` and in whether a coordinate is parked in the third block:

* **Some coordinate is at most `c₃`.** Park it there. The floor is `d = δ`, and the subset-sum step
  has the window `[D - y i₀, c₂]`, of width `W + y i₀ ≥ W + δ`, so the requirement is `v ≤ W + δ`.
* **Every coordinate exceeds `c₃`.** The third and fourth blocks must both be empty, so the window
  is only `W` wide — but now `d = c₃ = 4ω₀ + δ - ϵ` is a valid floor, which shrinks `v` and cuts
  the count, and it also forces `N c₃ ≤ Y`, which alone rules out `N ≥ 23` at every level of the
  band.

Since `v = d + (Y - N d)/(N - n)` and `n d ≤ D`, both requirements reduce to a single inequality in
`(N, Y, ω₀)` with no `n` in it:

    (Y - N d)(W + t d) ≤ (2/5 - 2δ - 8ω₀ - 2ϵ)(W + (t - 1) d),   t = 1 or 0.

At `t = 1, d = δ` this is `Gap212.datumD_band_low_core`, and at `t = 0, d = c₃` it is
`Gap212.datumD_band_high_core`. Both are verified rung by rung for `6 ≤ N ≤ 26` — the only sizes a
nonempty check set with `Y > c₁` admits — against the four mass bounds `Gap212.total_le_datum`,
`total_le_affine_datum`, `total_le_affine_datum₂`, `total_le_affine_datum₃`.

**`1/400` is where this pair of branches stops.** The tightest points are `N = 20` for the low
branch, whose slack at `ω₀ = 1/400` is `6.7·10⁻⁴` and vanishes at `ω₀ ≈ 0.0027`, and `N = 20` for
the high branch at `ω₀ = 0.001305`, whose slack is `4.6·10⁻⁵` — there `N c₃ ≤ Y` and `c₃ ≤ W`
overlap in a level window of width `9.3·10⁻⁶`, and above `ω₀ ≈ 0.0027` they separate at `N = 15`.
Above `1/400` a second coordinate can be parked, in the fourth block, and that is
`Gap212.conditionD_at_datum_band_2`. Neither reaches `ω₀ = 7/1000`: there the three-block capacity
`c₁ + c₂ + c₃ = 1/2 - δ - 6ω₀ - 3ϵ = 0.4416` leaves only `0.0092` over the pooled mass `0.4324`,
below the floor `δ`, so no argument that parks a single coordinate in one small block can reach
it. -/

set_option maxHeartbeats 1000000 in
-- The rung-by-rung verification is twenty-one `nlinarith` calls, one per value of `N`.
/-- **The low branch's numerical inequality.** With floor `δ` and one coordinate parked in the
third block, `(Y - Nδ)(W + δ) ≤ c̄₁ W` where `W = 1/2 - Y - 2δ - 10ω₀ - 2ϵ` is the reserve and
`c̄₁ = 2/5 - 2δ - 8ω₀ - 2ϵ` the least first capacity.

This is the whole numerical content of the low branch: it is exactly `v ≤ W + δ` with the level
`n = ⌊D/δ⌋` eliminated, and it is `γ`-free. Verified rung by rung for `6 ≤ N ≤ 26`; the tightest
rung is `N = 20`, where at `ω₀ = 1/400` the two sides are `0.002735` and `0.003403`. -/
theorem datumD_band_low_core {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 6 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000)
    (hw0 : 7 / 10000 < w) (hw : w ≤ 1 / 400) :
    (Y - N * (41 / 2500))
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 41 / 2500)
      ≤ (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
        * (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 <;>
    nlinarith [hYlo, hYcap, h1, h2, h3, hw0, hw]

/-- **The low branch's window bound.** The bound `v = (Y - nδ)/(N - n)` on the `(n+1)`-st smallest
coordinate is at most `W + δ`, for every level `n` with `n δ ≤ D`.

The elimination of `n` is the identity `v = δ + (Y - Nδ)/(N - n)`: the requirement `v ≤ W + δ` is
`Y - Nδ ≤ (N - n) W`, and `n δ ≤ D` gives `(N - n) δ ≥ c̄₁ - (Y - Nδ)`, so
`Gap212.datumD_band_low_core` is what is left. -/
theorem datumD_band_low_window {N Y w n : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 6 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000)
    (hw0 : 7 / 10000 < w) (hw : w ≤ 1 / 400)
    (hn : n * (41 / 2500) ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)) :
    Y - n * (41 / 2500)
      ≤ (1 / 2 - Y - 41 / 2500 - 10 * w - 2 / 10 ^ 10) * (N - n) := by
  have hW : (0 : ℝ) ≤ 1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10 := by linarith
  have hcore := datumD_band_low_core hNk hk1 hk2 hYlo hYcap h1 h2 h3 hw0 hw
  nlinarith [mul_le_mul_of_nonneg_right hn hW, hcore]

set_option maxHeartbeats 1000000 in
-- Twenty-one `linarith` calls, one per value of `N`.
/-- **The high branch's floor is below its reserve**: `c₃ = 4ω₀ + δ - ϵ ≤ W`, whenever every
coordinate exceeds `c₃` — which is what puts `N c₃ ≤ Y` in the hypotheses.

Without `N c₃ ≤ Y` this is false at the top of the band: at `N = 20` and `Y = 1081/2500` it asks
for `ω₀ ≤ 0.0013143`, while `N c₃ ≤ Y` asks for `ω₀ ≤ 0.001305`. That the second is the stronger of
the two, by `9.3·10⁻⁶`, is what makes the high branch close at all. -/
theorem datumD_band_high_floor {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 6 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (4 * w + 41 / 2500 - 1 / 10 ^ 10) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000)
    (hw0 : 7 / 10000 < w) (hw : w ≤ 1 / 400) :
    0 ≤ (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
      - (4 * w + 41 / 2500 - 1 / 10 ^ 10) := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 <;> linarith

set_option maxHeartbeats 1000000 in
-- The rung-by-rung verification is twenty-one `nlinarith` calls, one per value of `N`.
/-- **The high branch's numerical inequality.** With floor `c₃ = 4ω₀ + δ - ϵ` and both small blocks
empty, `(Y - N c₃) W ≤ c̄₁ (W - c₃)`.

Verified rung by rung for `6 ≤ N ≤ 26`. For `N ≥ 23` the hypothesis `N c₃ ≤ Y` is already
contradictory on the band — `23 · (4·(7/10000) + δ - ϵ) = 0.4416 > 0.4324` — and the tightest rung
that survives is `N = 20`, at the level `ω₀ = 0.001305` where `N c₃ ≤ Y` stops holding: there the
two sides differ by `4.6·10⁻⁵`. -/
theorem datumD_band_high_core {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 6 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (4 * w + 41 / 2500 - 1 / 10 ^ 10) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000)
    (hw0 : 7 / 10000 < w) (hw : w ≤ 1 / 400) :
    (Y - N * (4 * w + 41 / 2500 - 1 / 10 ^ 10))
        * (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
      ≤ (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
          - (4 * w + 41 / 2500 - 1 / 10 ^ 10)) := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 <;>
    nlinarith [hYlo, hYcap, h1, h2, h3, hw0, hw]

/-- **The high branch's window bound.** With floor `c₃`, the bound `v = (Y - n c₃)/(N - n)` on the
`(n+1)`-st smallest coordinate is at most the reserve `W` itself, for every `n` with `n c₃ ≤ D`.

Same elimination as in `Gap212.datumD_band_low_window`, one step longer because the factor cleared
is `c₃` rather than the constant `δ`: `v ≤ W` is `Y - N c₃ ≤ (N - n)(W - c₃)`, and `n c₃ ≤ D` gives
`(N - n) c₃ ≥ c̄₁ - (Y - N c₃)`, which needs `0 ≤ W - c₃` — `Gap212.datumD_band_high_floor` —
before it can be multiplied through. -/
theorem datumD_band_high_window {N Y w n : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 6 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (4 * w + 41 / 2500 - 1 / 10 ^ 10) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000)
    (hw0 : 7 / 10000 < w) (hw : w ≤ 1 / 400)
    (hn : n * (4 * w + 41 / 2500 - 1 / 10 ^ 10)
      ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)) :
    Y - n * (4 * w + 41 / 2500 - 1 / 10 ^ 10)
      ≤ (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) * (N - n) := by
  have hG := datumD_band_high_floor hNk hk1 hk2 hYlo hYcap h1 h2 h3 hw0 hw
  have hcore := datumD_band_high_core hNk hk1 hk2 hYlo hYcap h1 h2 h3 hw0 hw
  exact le_window_of_core (by linarith) hG hn hcore

set_option maxHeartbeats 1000000 in
-- Two branches, each running the small-coordinate count, the floor bound and the subset-sum
-- engine, in a single declaration.
/-- **Condition D at `p_⋆` for every cell, every `γ`, and every level `7/10000 < ω₀ ≤ 1/400`.**

The capacities are `Gap212.capD`'s and the chamber is `Gap212.chamberDBand` at the datum's level
`ω(1,1) = 7/1000` with the level banded to `(7/10000, 1/400]`. Composed with
`Gap212.conditionD_at_datum_low_level` through `Gap212.conditionD_of_band` this gives the condition
on `[0, 1/400]`, which is `5/14` of the chamber `[0, 7/1000]`; the next band up is
`Gap212.conditionD_at_datum_band_2`.

The argument is uniform in the cell — no enumeration of the `91` cells — and runs over the
dichotomy described above this declaration. Either the pooled mass fits in `c₁` and the trivial
partition serves, or `6 ≤ N ≤ 26`: the first affine bound caps `Y` at `1726/5000 = 0.3452` when
`N ≤ 5`, below `c₁ ≥ 868/2500 - 2ϵ = 0.3472 - 2·10⁻¹⁰`, and `27δ = 1107/2500` exceeds the flat
bound `1081/2500`. Then the deficit `D = Y - c₁` is at most `213/2500 + 2ϵ = 0.0852`, the level
`n = ⌊D/d⌋` is below `N` because `6δ = 0.0984` already exceeds `D`, and
`Gap212.Packing.exists_small_coords` supplies the `n + 1` small coordinates the two branches need.
Blocks three and four carry at most one coordinate between them: in the low branch block three
holds the one coordinate the dichotomy produces and block four is empty, and in the high branch
both are empty. -/
theorem conditionD_at_datum_mid_band (j j' : Fin gap212Params.n) {m m' : ℕ} :
    ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      capD (chamberDBand (omegaMax gap212Params j j') (7 / 10000) (1 / 400)) := by
  classical
  refine conditionD_band_of (by norm_num) (by norm_num) j j' fun γ w y hγ hγ' hw0 hw hy' hDle ↦ ?_
  have hc₂ : (0 : ℝ) ≤ 1 / 2 - γ - 2 * w - 1 / 10 ^ 10 := by linarith
  have hc₃ : (0 : ℝ) ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10 := by linarith
  have hc₄ : (0 : ℝ) ≤ 8 * w := by linarith
  -- the four mass bounds, the floor on the coordinates, and the deficit
  have hYcap := total_le_datum hy'
  have hYaff := total_le_affine_datum hy'
  have hYaff₂ := total_le_affine_datum₂ hy'
  have hYaff₃ := total_le_affine_datum₃ hy'
  have hYlow := card_delta_le_total hy'
  have hδy : ∀ i, (41 / 2500 : ℝ) ≤ y i := fun i ↦ (hy'.1 i).1
  have hy0 : ∀ i, (0 : ℝ) ≤ y i := fun i ↦ le_trans (by norm_num) (hδy i)
  have hD0 : (0 : ℝ) ≤ (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10) := by linarith
  have hDbar : (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10)
      ≤ (∑ i, y i) - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) := by linarith
  -- the cell has between six and twenty-six rough factors
  have hcast : ((m + m' : ℕ) : ℝ) = m + m' := Nat.cast_add m m'
  have hN6 : 6 ≤ m + m' := by exact_mod_cast (show (5 : ℝ) < m + m' by linarith)
  have hN26 : m + m' ≤ 26 :=
    Nat.le_of_lt_succ (by exact_mod_cast (show (m : ℝ) + m' < 27 by linarith))
  have hN6' : (6 : ℝ) ≤ m + m' := by exact_mod_cast hN6
  by_cases hex : ∃ i, y i ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10
  · -- **The low branch.** One coordinate fits in block three; the floor is `δ`.
    obtain ⟨i₀, hi₀⟩ := hex
    obtain ⟨n, hnle, hnlt⟩ :=
      Packing.exists_nat_mul_le_lt (d := (41 / 2500 : ℝ)) (by norm_num) hD0
    have hnN : (n : ℝ) < (m : ℝ) + (m' : ℝ) := by linarith
    have hnN' : n < m + m' := by exact_mod_cast hnN
    have hnsub : (0 : ℝ) < ((m : ℝ) + (m' : ℝ)) - (n : ℝ) := by linarith
    obtain ⟨v, hvmul, hdv, -, hSsum⟩ := exists_level_coords (by norm_num) hδy hnN'
    push_cast at hvmul
    have hwin : v ≤ 1 / 2 - (∑ i, y i) - 41 / 2500 - 10 * w - 2 / 10 ^ 10 := by
      refine le_of_mul_le_mul_right ?_ hnsub
      rw [hvmul]
      exact datumD_band_low_window hcast.symm hN6 hN26 hYlow hYcap hYaff hYaff₂ hYaff₃ hw0 hw
        (by linarith)
    exact Packing.admitsPartition₄_of_singleton_block
      (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (v := v) (i₀ := i₀)
      (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hc₂ hc₄ hi₀
      (by linarith [sum_le_erase_add (univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (hy0 i₀)])
      (by linarith [hδy i₀])
  · -- **The high branch.** Every coordinate exceeds `c₃`, which becomes the floor.
    push Not at hex
    have hfy : ∀ i, (4 * w + 41 / 2500 - 1 / 10 ^ 10 : ℝ) ≤ y i := fun i ↦ (hex i).le
    have hYf := mul_le_sum_of_card_le (S := univ) (k := m + m') hc₃ hfy (by simp)
    rw [hcast] at hYf
    obtain ⟨n, hnle, hnlt⟩ :=
      Packing.exists_nat_mul_le_lt (d := (4 * w + 41 / 2500 - 1 / 10 ^ 10 : ℝ)) (by linarith) hD0
    have hnN : (n : ℝ) < (m : ℝ) + (m' : ℝ) := by nlinarith
    have hnN' : n < m + m' := by exact_mod_cast hnN
    have hnsub : (0 : ℝ) < ((m : ℝ) + (m' : ℝ)) - (n : ℝ) := by linarith
    obtain ⟨v, hvmul, hdv, -, hSsum⟩ := exists_level_coords hc₃ hfy hnN'
    push_cast at hvmul
    have hwin : v ≤ 1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10 := by
      refine le_of_mul_le_mul_right ?_ hnsub
      rw [hvmul]
      exact datumD_band_high_window hcast.symm hN6 hN26 hYf hYcap hYaff hYaff₂ hYaff₃ hw0 hw
        (by linarith)
    refine admitsPartition₄_of_partition₂ ?_ hc₃ hc₄
    exact Packing.admitsPartition₂_of_small_block (v := v)
      (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v))
      (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hD0 (by linarith) (by linarith)

/-! ## The band `1/400 < ω₀ ≤ 1/250`

Above `1/400` the dichotomy of `Gap212.conditionD_at_datum_mid_band` stops closing, and what
replaces it is *a second parked coordinate*. Write `Y` for the pooled mass, `N = m + m'`,
`c̄₁ = 2/5 - 2δ - 8ω₀ - 2ϵ` for the least first capacity, `D = Y - c₁` for the deficit and

    W = c₂ - D = 1/2 - Y - 2δ - 10ω₀ - 2ϵ

for the `γ`-free reserve. With a floor `d` valid for every coordinate and `n = ⌊D/d⌋`,
`Gap212.Packing.exists_small_coords` supplies `n + 1` coordinates at most `v = (Y - n d)/(N - n)`,
and `n d ≤ D ≤ Y - c̄₁` eliminates `n` from every requirement below.

The mid band's two branches are *both* limited by how much mass the small blocks absorb. Its low
branch parks one coordinate in block three and widens the subset-sum window from `W` to `W + δ`;
its high branch parks none and raises the floor to `c₃`. Neither touches block four, and the wall
at `ω₀ ≈ 0.0027` is exactly the point where `W + δ` runs out. Block four has capacity `c₄ = 8ω₀`,
which is `0.02` at `ω₀ = 1/400` and already exceeds `δ = 0.0164`, so from that level on it can hold
a coordinate of its own — and a second parked coordinate widens the window to `W + 2δ`, which is
what carries the argument to `ω₀ = 1/250 = 0.004`.

Whether block four *has* a coordinate to hold is settled by the pooled mass, not by a further cell
enumeration: if every coordinate other than the one already parked exceeded `c₄`, then
`Y > (N - 1)·8ω₀ + δ`, which is itself a strong constraint. So the band splits into three branches,
each with one `n`-free numerical inequality:

* **Some coordinate is at most `c₃`, and some other is at most `c₄`.** Park them in blocks three
  and four. Floor `δ`, window `W + 2δ`, requirement `v ≤ W + 2δ`, i.e.
  `Gap212.datumD_band2_low_core`: `(Y - Nδ)(W + 2δ) ≤ c̄₁(W + δ)`.
* **Some coordinate is at most `c₃`, and every other exceeds `c₄`.** Park the first alone, as in
  the mid band: floor `δ`, window `W + δ`, requirement `(Y - Nδ)(W + δ) ≤ c̄₁ W`
  (`Gap212.datumD_band2_mid_core`) — but now with `(N - 1)·8ω₀ + δ ≤ Y` in hand, which is what
  makes it hold on a band where the mid-band version does not. It is also what supplies `0 ≤ W`
  (`Gap212.band2_mid_reserve`), false without it at the top of the band.
* **Every coordinate exceeds `c₃`.** Blocks three and four are both empty — on this band
  `c₄ = 8ω₀ ≤ c₃ = 4ω₀ + δ - ϵ`, since `4ω₀ ≤ 1/250·4 < δ - ϵ` — so `c₃` becomes the floor, the
  count drops, and `N c₃ ≤ Y` is forced: `Gap212.datumD_band2_high_core`, which reads
  `(Y - N c₃) W ≤ c̄₁(W - c₃)`.

All three are verified rung by rung for `5 ≤ N ≤ 26` against seven mass bounds — the flat
`Gap212.total_le_datum` and `Gap212.total_le_affine_datum`, `₂`, `₃`, `₄`, `₅`, `₆`, whose minimum
is the exact cell maximum of `B_{1,m} + B_{1,m'}` at `N = 2, 4, 6, 8, 9, 10` and at every `N` from
`14` to `26`, and is within `3/5000` of it at `N = 11, 12, 13`. The rung range is `5 ≤ N ≤ 26`:
`N ≤ 4` caps the pooled mass at `1652/5000 = 0.3304` by `Gap212.total_le_affine_datum₄`, below
`c₁ ≥ 1676/5000 - 2ϵ = 0.3352 - 2·10⁻¹⁰`, and `27δ = 1107/2500` exceeds the flat bound `1081/2500`.

**`1/250` is where this triple stops.** The binding slacks are `8.728·10⁻⁴` for the low branch at
`N = 20`, `7.815·10⁻⁵` for the middle branch at `N = 20`, and `6.839·10⁻⁵` for the high branch at
`N = 14`; the first rung to fail is `N = 12`, at `ω₀ ≈ 0.00404`, where the high branch's
`(Y - N c₃)W ≤ c̄₁(W - c₃)` turns over. That one rung on one window is all that stands in the way:
`Gap212.conditionD_at_datum_band_3` closes it by replacing the affine mass bound at `N = 12` by
the exact cell maximum — the high branch's floor `c₃` caps each *side* at six rough factors — and
carries the same triple to `ω₀ = 43/10000`, where the low branch turns over instead.

Past that, two parked coordinates are not enough, and `Gap212.conditionD_at_datum_band_4` parks a
third: above `ω₀ = δ/4 = 41/10000` the fourth block holds two coordinates at the floor, so the
dichotomy is run on `c₄` rather than on `c₃`. That carries the argument to `ω₀ = 13/2500`. -/

set_option maxHeartbeats 1000000 in
-- The rung-by-rung verification is twenty-two `nlinarith` calls, one per value of `N`.
/-- **The low branch's numerical inequality.** With floor `δ` and two coordinates parked — one in
block three, one in block four — `(Y - Nδ)(W + 2δ) ≤ c̄₁(W + δ)`, where
`W = 1/2 - Y - 2δ - 10ω₀ - 2ϵ` is the reserve and `c̄₁ = 2/5 - 2δ - 8ω₀ - 2ϵ` the least first
capacity.

This is exactly `v ≤ W + 2δ` with the level `n = ⌊D/δ⌋` eliminated, and it is `γ`-free. Verified
rung by rung for `5 ≤ N ≤ 26`; the tightest rung is `N = 20`, where the slack is
`21819998790000001/25000000000000000000 ≈ 8.73·10⁻⁴`. -/
theorem datumD_band2_low_core {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 5 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 1 / 400 < w) (hw : w ≤ 1 / 250) :
    (Y - N * (41 / 2500))
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 2 * (41 / 2500))
      ≤ (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 41 / 2500) := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 h4 h5 h6 <;>
    nlinarith [hYlo, hYcap, h1, h2, h3, h4, h5, h6, hw0, hw]

/-- **The low branch's window bound.** The bound `v = (Y - nδ)/(N - n)` on the `(n+1)`-st smallest
coordinate is at most `W + 2δ = 1/2 - Y - 10ω₀ - 2ϵ`, for every level `n` with `n δ ≤ D`.

Same elimination as in `Gap212.datumD_band_low_window`, one `δ` wider: `v ≤ W + 2δ` is
`Y - Nδ ≤ (N - n)(W + δ)`, and `n δ ≤ Y - c̄₁` turns that into
`Gap212.datumD_band2_low_core`. The multiplier `W + δ` is nonnegative on the band because
`Y ≤ 1081/2500` and `ω₀ ≤ 1/250` give `W + δ ≥ 56/5000 - 2ϵ`. -/
theorem datumD_band2_low_window {N Y w n : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 5 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 1 / 400 < w) (hw : w ≤ 1 / 250)
    (hn : n * (41 / 2500) ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)) :
    Y - n * (41 / 2500) ≤ (1 / 2 - Y - 10 * w - 2 / 10 ^ 10) * (N - n) := by
  have hW : (0 : ℝ) ≤ 1 / 2 - Y - 41 / 2500 - 10 * w - 2 / 10 ^ 10 := by linarith
  have hcore := datumD_band2_low_core hNk hk1 hk2 hYlo hYcap h1 h2 h3 h4 h5 h6 hw0 hw
  nlinarith [mul_le_mul_of_nonneg_right hn hW, hcore]

set_option maxHeartbeats 1000000 in
-- Twenty-two `nlinarith` calls, one per value of `N`.
/-- **The middle branch's reserve is nonnegative**: `0 ≤ W`, whenever every coordinate but the
parked one exceeds `c₄` — which is what puts `(N - 1)·8ω₀ + δ ≤ Y` in the hypotheses.

Without that hypothesis this is false at the top of the band: at `Y = 1081/2500` and `ω₀ = 1/250`,
`W = -26/5000 - 2ϵ`. With it, the two constraints `(N-1)·8ω₀ + δ ≤ Y` and `Y ≤ 1081/2500` can only
hold together when `ω₀` is small enough for `W ≥ 0`. -/
theorem band2_mid_reserve {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 5 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 1 / 400 < w) (hw : w ≤ 1 / 250)
    (hfar : (N - 1) * (8 * w) + 41 / 2500 ≤ Y) :
    0 ≤ 1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10 := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 h4 h5 h6 hfar <;>
    nlinarith [hYlo, hYcap, h1, h2, h3, h4, h5, h6, hw0, hw, hfar]

set_option maxHeartbeats 1000000 in
-- Twenty-two `nlinarith` calls, one per value of `N`.
/-- **The middle branch's numerical inequality.** With floor `δ`, one coordinate parked in block
three and block four empty, `(Y - Nδ)(W + δ) ≤ c̄₁ W` — the mid band's low-branch inequality, now
carrying the extra hypothesis `(N - 1)·8ω₀ + δ ≤ Y` that this branch's dichotomy supplies.

That hypothesis is what makes the inequality true above `ω₀ ≈ 0.0027`, where the mid band's version
fails: it says every coordinate but the parked one is larger than `c₄`, and on a band where `c₄`
has grown past `δ` that caps `N` sharply against the pooled mass. Verified rung by rung for
`5 ≤ N ≤ 26`; the tightest rung is `N = 20`, with slack
`705271551752000361/9025000000000000000000 ≈ 7.81·10⁻⁵`. -/
theorem datumD_band2_mid_core {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 5 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 1 / 400 < w) (hw : w ≤ 1 / 250)
    (hfar : (N - 1) * (8 * w) + 41 / 2500 ≤ Y) :
    (Y - N * (41 / 2500))
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 41 / 2500)
      ≤ (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
        * (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 h4 h5 h6 hfar <;>
    nlinarith [hYlo, hYcap, h1, h2, h3, h4, h5, h6, hw0, hw, hfar]

/-- **The middle branch's window bound**: `v = (Y - nδ)/(N - n) ≤ W + δ`, for every `n` with
`n δ ≤ D`, given that every coordinate but the parked one exceeds `c₄`. The multiplication step
needs `0 ≤ W`, which is `Gap212.band2_mid_reserve`. -/
theorem datumD_band2_mid_window {N Y w n : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 5 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 1 / 400 < w) (hw : w ≤ 1 / 250)
    (hfar : (N - 1) * (8 * w) + 41 / 2500 ≤ Y)
    (hn : n * (41 / 2500) ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)) :
    Y - n * (41 / 2500)
      ≤ (1 / 2 - Y - 41 / 2500 - 10 * w - 2 / 10 ^ 10) * (N - n) := by
  have hW := band2_mid_reserve hNk hk1 hk2 hYlo hYcap h1 h2 h3 h4 h5 h6 hw0 hw hfar
  have hcore := datumD_band2_mid_core hNk hk1 hk2 hYlo hYcap h1 h2 h3 h4 h5 h6 hw0 hw hfar
  nlinarith [mul_le_mul_of_nonneg_right hn hW, hcore]

set_option maxHeartbeats 1000000 in
-- Twenty-two `nlinarith` calls, one per value of `N`.
/-- **The high branch's floor is below its reserve**: `c₃ = 4ω₀ + δ - ϵ ≤ W`, whenever every
coordinate exceeds `c₃` — which is what puts `N c₃ ≤ Y` in the hypotheses.

This is `Gap212.datumD_band_high_floor` on the wider band, with the four extra mass bounds. Its
least slack is `3999991/20000000000 ≈ 2.00·10⁻⁴`, at `N = 14`. -/
theorem band2_high_floor {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 5 ≤ k) (hk2 : k ≤ 26)
    (hYf : N * (4 * w + 41 / 2500 - 1 / 10 ^ 10) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 1 / 400 < w) (hw : w ≤ 1 / 250) :
    0 ≤ (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
      - (4 * w + 41 / 2500 - 1 / 10 ^ 10) := by
  subst hNk
  interval_cases k <;> push_cast at hYf h1 h2 h3 h4 h5 h6 <;>
    nlinarith [hYf, hYcap, h1, h2, h3, h4, h5, h6, hw0, hw]

set_option maxHeartbeats 1000000 in
-- Twenty-two `nlinarith` calls, one per value of `N`.
/-- **The high branch's numerical inequality.** With floor `c₃ = 4ω₀ + δ - ϵ` and both small blocks
empty, `(Y - N c₃) W ≤ c̄₁ (W - c₃)`.

This is `Gap212.datumD_band_high_core` on the wider band `1/400 < ω₀ ≤ 1/250`, and it is the four
new mass bounds that carry it there: with only `Gap212.total_le_affine_datum`, `₂` and `₃` it fails
at `N = 12, 13, 14, 15`, where those bounds overshoot the exact cell maximum by up to `15/5000`.
Verified rung by rung for `5 ≤ N ≤ 26`; the tightest rung is `N = 14`, with slack
`23935946116000063/350000000000000000000 ≈ 6.84·10⁻⁵`, and `N ≥ 16` is already vacuous because
there `N c₃ > 16 · 0.0264 = 0.4224` exceeds the pooled-mass bound (`2084/5000` at `N = 16`). -/
theorem datumD_band2_high_core {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 5 ≤ k) (hk2 : k ≤ 26)
    (hYf : N * (4 * w + 41 / 2500 - 1 / 10 ^ 10) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 1 / 400 < w) (hw : w ≤ 1 / 250) :
    (Y - N * (4 * w + 41 / 2500 - 1 / 10 ^ 10))
        * (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
      ≤ (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
          - (4 * w + 41 / 2500 - 1 / 10 ^ 10)) := by
  subst hNk
  interval_cases k <;> push_cast at hYf h1 h2 h3 h4 h5 h6 <;>
    nlinarith [hYf, hYcap, h1, h2, h3, h4, h5, h6, hw0, hw]

/-- **The high branch's window bound.** With floor `c₃`, the bound `v = (Y - n c₃)/(N - n)` on the
`(n+1)`-st smallest coordinate is at most the reserve `W` itself, for every `n` with `n c₃ ≤ D`.

Same elimination as in `Gap212.datumD_band_high_window`: `v ≤ W` is
`Y - N c₃ ≤ (N - n)(W - c₃)`, and `n c₃ ≤ Y - c̄₁` gives `(N - n) c₃ ≥ c̄₁ - (Y - N c₃)`, which
needs `0 ≤ W - c₃` — `Gap212.band2_high_floor` — before it can be multiplied through. -/
theorem datumD_band2_high_window {N Y w n : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 5 ≤ k) (hk2 : k ≤ 26)
    (hYf : N * (4 * w + 41 / 2500 - 1 / 10 ^ 10) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 1 / 400 < w) (hw : w ≤ 1 / 250)
    (hn : n * (4 * w + 41 / 2500 - 1 / 10 ^ 10)
      ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)) :
    Y - n * (4 * w + 41 / 2500 - 1 / 10 ^ 10)
      ≤ (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) * (N - n) := by
  have hG := band2_high_floor hNk hk1 hk2 hYf hYcap h1 h2 h3 h4 h5 h6 hw0 hw
  have hcore := datumD_band2_high_core hNk hk1 hk2 hYf hYcap h1 h2 h3 h4 h5 h6 hw0 hw
  exact le_window_of_core (by linarith) hG hn hcore

set_option maxHeartbeats 1000000 in
-- Three branches, each running the small-coordinate count, the floor bound and the subset-sum
-- engine, in a single declaration.
/-- **Condition D at `p_⋆` for every cell, every `γ`, and every level `1/400 < ω₀ ≤ 1/250`.**

The capacities are `Gap212.capD`'s and the chamber is `Gap212.chamberDBand` at the datum's level
`ω(1,1) = 7/1000` with the level banded to `(1/400, 1/250]`. Spliced onto
`Gap212.conditionD_at_datum_mid_band` and `conditionD_at_datum_low_level` through
`Gap212.conditionD_of_band_split` and `conditionD_of_band` this gives the condition on
`[0, 1/250]`, which is `4/7` of the chamber `[0, 7/1000]`; the next band up is
`Gap212.conditionD_at_datum_band_3`.

The argument is uniform in the cell — no enumeration of the `91` cells — and runs over the three
branches described above this declaration. Either the pooled mass fits in `c₁` and the trivial
partition serves, or `5 ≤ N ≤ 26`: `Gap212.total_le_affine_datum₄` caps `Y` at `1652/5000 = 0.3304`
when `N ≤ 4`, below `c₁ ≥ 1676/5000 - 2ϵ = 0.3352 - 2·10⁻¹⁰`, and `27δ = 1107/2500` exceeds the
flat bound `1081/2500`. Then the deficit `D = Y - c₁` is at most `243/2500 + 2ϵ = 0.0972`, the
level `n = ⌊D/d⌋` is below `N` because `Gap212.total_le_affine_datum₄` also gives `Y - c̄₁ < Nδ`,
and `Gap212.Packing.exists_small_coords` supplies the `n + 1` small coordinates the branches need.

What is new here against `Gap212.conditionD_at_datum_mid_band` is the second parked coordinate. The
level `1/400` is past `δ/8 = 41/20000 = 0.00205`, so `c₄ = 8ω₀ > δ`: block four can hold a
coordinate of its own, and `Gap212.Packing.admitsPartition₄_of_two_singletons` widens the
subset-sum window from `W + δ` to `W + 2δ`. When no second coordinate is small enough for it,
every coordinate but the parked one exceeds `c₄` and `(N - 1)·8ω₀ + δ ≤ Y` closes the branch
instead. -/
theorem conditionD_at_datum_band_2 (j j' : Fin gap212Params.n) {m m' : ℕ} :
    ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      capD (chamberDBand (omegaMax gap212Params j j') (1 / 400) (1 / 250)) := by
  classical
  refine conditionD_band_of (by norm_num) (by norm_num) j j' fun γ w y hγ hγ' hw0 hw hy' hDle ↦ ?_
  have hc₂ : (0 : ℝ) ≤ 1 / 2 - γ - 2 * w - 1 / 10 ^ 10 := by linarith
  have hc₃ : (0 : ℝ) ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10 := by linarith
  have hc₄ : (0 : ℝ) ≤ 8 * w := by linarith
  -- the seven mass bounds, the floor on the coordinates, and the deficit
  have hYcap := total_le_datum hy'
  have hYaff := total_le_affine_datum hy'
  have hYaff₂ := total_le_affine_datum₂ hy'
  have hYaff₃ := total_le_affine_datum₃ hy'
  have hYaff₄ := total_le_affine_datum₄ hy'
  have hYaff₅ := total_le_affine_datum₅ hy'
  have hYaff₆ := total_le_affine_datum₆ hy'
  have hYlow := card_delta_le_total hy'
  have hδy : ∀ i, (41 / 2500 : ℝ) ≤ y i := fun i ↦ (hy'.1 i).1
  have hy0 : ∀ i, (0 : ℝ) ≤ y i := fun i ↦ le_trans (by norm_num) (hδy i)
  have hD0 : (0 : ℝ) ≤ (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10) := by linarith
  have hDbar : (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10)
      ≤ (∑ i, y i) - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) := by linarith
  have hcast : ((m + m' : ℕ) : ℝ) = m + m' := Nat.cast_add m m'
  -- the cell has between five and twenty-six rough factors
  have hN5 : 5 ≤ m + m' := by exact_mod_cast (show (4 : ℝ) < m + m' by linarith)
  have hN26 : m + m' ≤ 26 :=
    Nat.le_of_lt_succ (by exact_mod_cast (show (m : ℝ) + m' < 27 by linarith))
  have hN5' : (5 : ℝ) ≤ m + m' := by exact_mod_cast hN5
  by_cases hex : ∃ i, y i ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10
  · -- **Blocks three and four are in play.** The floor is `δ`.
    obtain ⟨i₀, hi₀⟩ := hex
    obtain ⟨n, hnle, hnlt⟩ :=
      Packing.exists_nat_mul_le_lt (d := (41 / 2500 : ℝ)) (by norm_num) hD0
    have hnN : (n : ℝ) < (m : ℝ) + (m' : ℝ) := by linarith
    have hnN' : n < m + m' := by exact_mod_cast hnN
    have hnsub : (0 : ℝ) < ((m : ℝ) + (m' : ℝ)) - (n : ℝ) := by linarith
    obtain ⟨v, hvmul, hdv, -, hSsum⟩ := exists_level_coords (by norm_num) hδy hnN'
    push_cast at hvmul
    by_cases hex4 : ∃ j₀, j₀ ≠ i₀ ∧ y j₀ ≤ 8 * w
    · -- **The low branch.** Block three takes `i₀`, block four takes `j₀`; window `W + 2δ`.
      obtain ⟨j₀, hji, hj₀⟩ := hex4
      have hwin : v ≤ 1 / 2 - (∑ i, y i) - 10 * w - 2 / 10 ^ 10 := by
        refine le_of_mul_le_mul_right ?_ hnsub
        rw [hvmul]
        exact datumD_band2_low_window hcast.symm hN5 hN26 hYlow hYcap hYaff hYaff₂ hYaff₃
          hYaff₄ hYaff₅ hYaff₆ hw0 hw (by linarith)
      exact Packing.admitsPartition₄_of_two_singletons
        (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (v := v) (i₀ := i₀) (j₀ := j₀)
        (Ne.symm hji) (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hc₂ hi₀ hj₀
        (by linarith [sum_le_erase_add (univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (hy0 i₀),
          sum_le_erase_add ((univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)).erase i₀) (hy0 j₀)])
        (by linarith [hδy i₀, hδy j₀])
    · -- **The middle branch.** Every coordinate but `i₀` exceeds `c₄`, which caps `N`.
      push Not at hex4
      have hfar : ((m : ℝ) + (m' : ℝ) - 1) * (8 * w) + 41 / 2500
          ≤ ∑ i, y i := by
        have h := floor_off_le_sum (T := {i₀}) (f := 8 * w) fun i hi ↦
          (hex4 i (notMem_singleton.1 hi)).le
        rw [card_singleton, Nat.cast_one, sum_singleton, hcast] at h
        linarith [hδy i₀]
      have hwin : v ≤ 1 / 2 - (∑ i, y i) - 41 / 2500 - 10 * w - 2 / 10 ^ 10 := by
        refine le_of_mul_le_mul_right ?_ hnsub
        rw [hvmul]
        exact datumD_band2_mid_window hcast.symm hN5 hN26 hYlow hYcap hYaff hYaff₂ hYaff₃
          hYaff₄ hYaff₅ hYaff₆ hw0 hw hfar (by linarith)
      exact Packing.admitsPartition₄_of_singleton_block
        (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (v := v) (i₀ := i₀)
        (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hc₂ hc₄ hi₀
        (by linarith [sum_le_erase_add (univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (hy0 i₀)])
        (by linarith [hδy i₀])
  · -- **The high branch.** Every coordinate exceeds `c₃`, which becomes the floor.
    push Not at hex
    have hfy : ∀ i, (4 * w + 41 / 2500 - 1 / 10 ^ 10 : ℝ) ≤ y i := fun i ↦ (hex i).le
    have hYf := mul_le_sum_of_card_le (S := univ) (k := m + m') hc₃ hfy (by simp)
    rw [hcast] at hYf
    obtain ⟨n, hnle, hnlt⟩ :=
      Packing.exists_nat_mul_le_lt (d := (4 * w + 41 / 2500 - 1 / 10 ^ 10 : ℝ)) (by linarith) hD0
    have hnN : (n : ℝ) < (m : ℝ) + (m' : ℝ) := by nlinarith
    have hnN' : n < m + m' := by exact_mod_cast hnN
    have hnsub : (0 : ℝ) < ((m : ℝ) + (m' : ℝ)) - (n : ℝ) := by linarith
    obtain ⟨v, hvmul, hdv, -, hSsum⟩ := exists_level_coords hc₃ hfy hnN'
    push_cast at hvmul
    have hwin : v ≤ 1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10 := by
      refine le_of_mul_le_mul_right ?_ hnsub
      rw [hvmul]
      exact datumD_band2_high_window hcast.symm hN5 hN26 hYf hYcap hYaff hYaff₂ hYaff₃
        hYaff₄ hYaff₅ hYaff₆ hw0 hw (by linarith)
    refine admitsPartition₄_of_partition₂ ?_ hc₃ hc₄
    exact Packing.admitsPartition₂_of_small_block (v := v)
      (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v))
      (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hD0 (by linarith) (by linarith)

/-! ## The band `1/250 < ω₀ ≤ 43/10000`

Above `1/250` the triple of `Gap212.conditionD_at_datum_band_2` fails in *one* place, and only
there: the high branch's `(Y - N c₃) W ≤ c̄₁ (W - c₃)` turns over at `N = 12` for
`ω₀ ∈ (0.004033, 0.004113)`, and from `ω₀ ≈ 0.004113` on it is vacuous again, because
`12 c₃ = 12(4ω₀ + δ - ϵ)` outgrows the affine mass bound `1970/5000` of
`Gap212.total_le_affine_datum₅`. So the whole of what stands between `1/250` and the next real wall
is that one rung on that one window — and what closes it is that the affine bound is not the truth.

**The mass bound the high branch can afford.** In the high branch every coordinate exceeds
`c₃`, so — this is `Gap212.side_floor_le_cap` — each side's count obeys `m c₃ ≤ B_{1,m}`. On this
band `c₃ > 0.0324`, so `7 c₃ > 0.2268` exceeds the whole row (`Gap212.side_le_six`) and both sides
are capped at six factors. That gives `N ≤ 12`, and it gives the pooled mass as
`B_{1,m} + B_{1,m'}` with `m, m' ≤ 6` — the *exact* cell maximum, `1966/5000 = 0.3932` at the only
cell of size twelve that survives, `(6, 6)`. The affine bound allows `1970/5000`; those `4/5000`
are the difference between a rung that fails and a rung that does not. And the same two facts make
the cell `(6, 6)` vacuous above `ω₀ = 491/120000 + ϵ/4 ≈ 0.0040917`, where `6 c₃` passes
`B_{1,6} = 983/5000`, so no case split on the level is needed: the rung-by-rung verification runs
over `m, m' ∈ [0, 6]` and the arithmetic disposes of the impossible pairs.

The low and middle branches are `Gap212.conditionD_at_datum_band_2`'s, restated on the wider band
and verified again rung by rung for `5 ≤ N ≤ 26` against the same seven mass bounds. Their branch
conditions are unchanged:

* **Some coordinate is at most `c₃`, and some other is at most `c₄`.** Park them in blocks three
  and four; floor `δ`, window `W + 2δ`, requirement `(Y - Nδ)(W + 2δ) ≤ c̄₁(W + δ)`
  (`Gap212.datumD_band3_low_core`).
* **Some coordinate is at most `c₃`, every other exceeds `c₄`.** Park the first alone; floor `δ`,
  window `W + δ`, requirement `(Y - Nδ)(W + δ) ≤ c̄₁ W` (`Gap212.datumD_band3_mid_core`), with
  `(N - 1)·8ω₀ + δ ≤ Y` in hand, which also supplies `0 ≤ W` (`Gap212.band3_mid_reserve`).
* **Every coordinate exceeds `c₃`.** Blocks three and four are both empty, `c₃` becomes the floor,
  and the per-side facts above replace `N c₃ ≤ Y ≤ Ymax(N)`: `Gap212.datumD_band3_high_core`, which
  reads `(Y - N c₃) W ≤ c̄₁(W - c₃)` at `N = m + m'` with `m, m' ≤ 6` and `Y ≤ B_{1,m} + B_{1,m'}`.

**`43/10000` is where this stops, and the wall is now the low branch.** The binding slacks are
`1.607·10⁻⁴` for the low branch at `N = 20` — at the top of the band and at the flat pooled mass
`1081/2500`, the only place the low branch is ever tight — `1.060·10⁻⁴` for the high branch at the
cell `(6, 6)` (at `ω₀ ≈ 0.0040917`, the level where that cell dies), `3.169·10⁻⁴` for the high
branch's floor `c₃ ≤ W` there, and `8.757·10⁻⁴` for the middle branch at `N = 12`. The low branch
at `N = 20` fails from `ω₀ = 0.0043685631705…` on, the root of `80ω₀² - 3.0376ω₀ + 0.0117432` (up
to `ϵ`); `43/10000` is the round numeral below it.

What that wall asks for is a *third* parked coordinate. At `ω₀ = 43/10000` and the flat mass the
reserve is already negative, `W = -41/5000 - 2ϵ`, so the two parked coordinates leave a window of
only `W + 2δ = 123/5000 = 0.0246` against a bound `v ≈ 0.0239` on the relevant coordinate; past
`0.0043686` that margin is gone. Above `ω₀ = δ/4 = 0.0041` each small block can hold *two*
coordinates at the floor
(`2δ ≤ c₃` and `2δ ≤ c₄` there), so up to four may be parked — but which coordinates fit in a
block depends on their sizes and not only on the level, so the single dichotomy "is some coordinate
at most `c₃`" no longer selects them. `Gap212.conditionD_at_datum_band_4` selects them by running
the dichotomy on `c₄` instead. -/

set_option maxHeartbeats 1000000 in
-- The rung-by-rung verification is twenty-two `nlinarith` calls, one per value of `N`.
/-- **The low branch's numerical inequality.** With floor `δ` and two coordinates parked — one in
block three, one in block four — `(Y - Nδ)(W + 2δ) ≤ c̄₁(W + δ)`, where
`W = 1/2 - Y - 2δ - 10ω₀ - 2ϵ` is the reserve and `c̄₁ = 2/5 - 2δ - 8ω₀ - 2ϵ` the least first
capacity.

This is `Gap212.datumD_band2_low_core` on the wider band `1/250 < ω₀ ≤ 43/10000`, and it is now the
binding inequality of the whole argument: verified rung by rung for `5 ≤ N ≤ 26`, its least slack
is `4017998817000001/25000000000000000000 ≈ 1.607·10⁻⁴`, at `N = 20`, `ω₀ = 43/10000` and the flat
pooled mass `Y = 1081/2500`. -/
theorem datumD_band3_low_core {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 5 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 1 / 250 < w) (hw : w ≤ 43 / 10000) :
    (Y - N * (41 / 2500))
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 2 * (41 / 2500))
      ≤ (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 41 / 2500) := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 h4 h5 h6 <;>
    nlinarith [hYlo, hYcap, h1, h2, h3, h4, h5, h6, hw0, hw]

/-- **The low branch's window bound.** The bound `v = (Y - nδ)/(N - n)` on the `(n+1)`-st smallest
coordinate is at most `W + 2δ = 1/2 - Y - 10ω₀ - 2ϵ`, for every level `n` with `n δ ≤ D`.

Same elimination as in `Gap212.datumD_band2_low_window`: `v ≤ W + 2δ` is
`Y - Nδ ≤ (N - n)(W + δ)`, and `n δ ≤ Y - c̄₁` turns that into
`Gap212.datumD_band3_low_core`. The multiplier `W + δ` is nonnegative on the band because
`Y ≤ 1081/2500` and `ω₀ ≤ 43/10000` give `W + δ ≥ 41/5000 - 2ϵ`. -/
theorem datumD_band3_low_window {N Y w n : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 5 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 1 / 250 < w) (hw : w ≤ 43 / 10000)
    (hn : n * (41 / 2500) ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)) :
    Y - n * (41 / 2500) ≤ (1 / 2 - Y - 10 * w - 2 / 10 ^ 10) * (N - n) := by
  have hW : (0 : ℝ) ≤ 1 / 2 - Y - 41 / 2500 - 10 * w - 2 / 10 ^ 10 := by linarith
  have hcore := datumD_band3_low_core hNk hk1 hk2 hYlo hYcap h1 h2 h3 h4 h5 h6 hw0 hw
  nlinarith [mul_le_mul_of_nonneg_right hn hW, hcore]

set_option maxHeartbeats 1000000 in
-- Twenty-two `nlinarith` calls, one per value of `N`.
/-- **The middle branch's reserve is nonnegative**: `0 ≤ W`, whenever every coordinate but the
parked one exceeds `c₄` — which is what puts `(N - 1)·8ω₀ + δ ≤ Y` in the hypotheses.

`Gap212.band2_mid_reserve` on the wider band. Without the hypothesis it is false at the top of the
band: at `Y = 1081/2500` and `ω₀ = 43/10000`, `W = -41/5000 - 2ϵ`. -/
theorem band3_mid_reserve {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 5 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 1 / 250 < w) (hw : w ≤ 43 / 10000)
    (hfar : (N - 1) * (8 * w) + 41 / 2500 ≤ Y) :
    0 ≤ 1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10 := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 h4 h5 h6 hfar <;>
    nlinarith [hYlo, hYcap, h1, h2, h3, h4, h5, h6, hw0, hw, hfar]

set_option maxHeartbeats 1000000 in
-- Twenty-two `nlinarith` calls, one per value of `N`.
/-- **The middle branch's numerical inequality.** With floor `δ`, one coordinate parked in block
three and block four empty, `(Y - Nδ)(W + δ) ≤ c̄₁ W`, carrying the extra hypothesis
`(N - 1)·8ω₀ + δ ≤ Y` that this branch's dichotomy supplies.

`Gap212.datumD_band2_mid_core` on the wider band. The hypothesis caps `N` at `12` there — at
`ω₀ = 43/10000` it caps it at `11` — and the least slack is `≈ 8.757·10⁻⁴`, at `N = 12` and
`ω₀ ≈ 0.004291`. This branch is nowhere near binding; the low branch is. -/
theorem datumD_band3_mid_core {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 5 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 1 / 250 < w) (hw : w ≤ 43 / 10000)
    (hfar : (N - 1) * (8 * w) + 41 / 2500 ≤ Y) :
    (Y - N * (41 / 2500))
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 41 / 2500)
      ≤ (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
        * (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 h4 h5 h6 hfar <;>
    nlinarith [hYlo, hYcap, h1, h2, h3, h4, h5, h6, hw0, hw, hfar]

/-- **The middle branch's window bound**: `v = (Y - nδ)/(N - n) ≤ W + δ`, for every `n` with
`n δ ≤ D`, given that every coordinate but the parked one exceeds `c₄`. The multiplication step
needs `0 ≤ W`, which is `Gap212.band3_mid_reserve`. -/
theorem datumD_band3_mid_window {N Y w n : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 5 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 1 / 250 < w) (hw : w ≤ 43 / 10000)
    (hfar : (N - 1) * (8 * w) + 41 / 2500 ≤ Y)
    (hn : n * (41 / 2500) ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)) :
    Y - n * (41 / 2500)
      ≤ (1 / 2 - Y - 41 / 2500 - 10 * w - 2 / 10 ^ 10) * (N - n) := by
  have hW := band3_mid_reserve hNk hk1 hk2 hYlo hYcap h1 h2 h3 h4 h5 h6 hw0 hw hfar
  have hcore := datumD_band3_mid_core hNk hk1 hk2 hYlo hYcap h1 h2 h3 h4 h5 h6 hw0 hw hfar
  nlinarith [mul_le_mul_of_nonneg_right hn hW, hcore]

set_option maxHeartbeats 1000000 in
-- Forty-nine `nlinarith` calls, one per pair of side counts.
/-- **The high branch's floor is below its reserve**: `c₃ = 4ω₀ + δ - ϵ ≤ W`, whenever every
coordinate exceeds `c₃`.

This is `Gap212.band2_high_floor` with the per-side mass bound in place of the affine ones: the
hypotheses are `m, m' ≤ 6` (`Gap212.side_le_six`), `N c₃ ≤ Y` and `Y ≤ B_{1,m} + B_{1,m'}`. Its
least slack is `≈ 3.169·10⁻⁴`, at the cell `(6, 6)` and `ω₀ ≈ 0.0040917`. With the affine bound
`Y ≤ 1970/5000` in place of `Y ≤ 1966/5000` it is false there. -/
theorem band3_high_floor {Y w : ℝ} {m m' : ℕ} (hm : m ≤ 6) (hm' : m' ≤ 6)
    (hYf : ((m : ℝ) + (m' : ℝ)) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) ≤ Y)
    (hYside : Y ≤ gap212Cap m + gap212Cap m')
    (hY1 : 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10 ≤ Y)
    (hw0 : 1 / 250 < w) (hw : w ≤ 43 / 10000) :
    0 ≤ (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
      - (4 * w + 41 / 2500 - 1 / 10 ^ 10) := by
  interval_cases m <;> interval_cases m' <;>
    norm_num [gap212Cap] at hYside hYf <;> nlinarith [hYf, hYside, hY1, hw0, hw]

set_option maxHeartbeats 1000000 in
-- Forty-nine `nlinarith` calls, one per pair of side counts.
/-- **The high branch's numerical inequality.** With floor `c₃ = 4ω₀ + δ - ϵ` and both small blocks
empty, `(Y - N c₃) W ≤ c̄₁ (W - c₃)`, at `N = m + m'`.

This is where the third band differs from the second. `Gap212.datumD_band2_high_core` states the
same inequality against the affine mass bounds and the rung `N`; here the hypotheses are per-side —
`m, m' ≤ 6` from `Gap212.side_le_six`, `Y ≤ B_{1,m} + B_{1,m'}` from `Gap212.Packing.total_le` —
which is the exact cell maximum rather than an affine majorant of it. The verification runs over
the forty-nine pairs `m, m' ∈ [0, 6]`; the pairs whose mass range is empty, including `(6, 6)` once
`6 c₃` passes `B_{1,6} = 983/5000` at `ω₀ ≈ 0.0040917`, are disposed of by the arithmetic. The
nontriviality hypothesis `c̄₁ ≤ Y` is what kills the cells too small to overflow the first block.

The least slack is `≈ 1.060·10⁻⁴`, at `(6, 6)` and `ω₀ ≈ 0.0040917`. -/
theorem datumD_band3_high_core {Y w : ℝ} {m m' : ℕ} (hm : m ≤ 6) (hm' : m' ≤ 6)
    (hYf : ((m : ℝ) + (m' : ℝ)) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) ≤ Y)
    (hYside : Y ≤ gap212Cap m + gap212Cap m')
    (hY1 : 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10 ≤ Y)
    (hw0 : 1 / 250 < w) (hw : w ≤ 43 / 10000) :
    (Y - ((m : ℝ) + (m' : ℝ)) * (4 * w + 41 / 2500 - 1 / 10 ^ 10))
        * (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
      ≤ (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
          - (4 * w + 41 / 2500 - 1 / 10 ^ 10)) := by
  interval_cases m <;> interval_cases m' <;>
    norm_num [gap212Cap] at hYside hYf ⊢ <;> nlinarith [hYf, hYside, hY1, hw0, hw]

/-- **The high branch's window bound.** With floor `c₃`, the bound `v = (Y - n c₃)/(N - n)` on the
`(n+1)`-st smallest coordinate is at most the reserve `W` itself, for every `n` with `n c₃ ≤ D`.

Same elimination as in `Gap212.datumD_band2_high_window`, over the per-side hypotheses:
`v ≤ W` is `Y - N c₃ ≤ (N - n)(W - c₃)`, and `n c₃ ≤ Y - c̄₁` gives
`(N - n) c₃ ≥ c̄₁ - (Y - N c₃)`, which needs `0 ≤ W - c₃` — `Gap212.band3_high_floor` — before it
can be multiplied through. -/
theorem datumD_band3_high_window {Y w n : ℝ} {m m' : ℕ} (hm : m ≤ 6) (hm' : m' ≤ 6)
    (hYf : ((m : ℝ) + (m' : ℝ)) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) ≤ Y)
    (hYside : Y ≤ gap212Cap m + gap212Cap m')
    (hY1 : 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10 ≤ Y)
    (hw0 : 1 / 250 < w) (hw : w ≤ 43 / 10000)
    (hn : n * (4 * w + 41 / 2500 - 1 / 10 ^ 10)
      ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)) :
    Y - n * (4 * w + 41 / 2500 - 1 / 10 ^ 10)
      ≤ (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
        * (((m : ℝ) + (m' : ℝ)) - n) := by
  have hG := band3_high_floor hm hm' hYf hYside hY1 hw0 hw
  have hcore := datumD_band3_high_core hm hm' hYf hYside hY1 hw0 hw
  exact le_window_of_core (by linarith) hG hn hcore

set_option maxHeartbeats 1000000 in
-- Three branches, each running the small-coordinate count, the floor bound and the subset-sum
-- engine, in a single declaration.
/-- **Condition D at `p_⋆` for every cell, every `γ`, and every level `1/250 < ω₀ ≤ 43/10000`.**

The capacities are `Gap212.capD`'s and the chamber is `Gap212.chamberDBand` at the datum's level
`ω(1,1) = 7/1000` with the level banded to `(1/250, 43/10000]`. Spliced onto
`Gap212.conditionD_at_datum_band_2`, `conditionD_at_datum_mid_band` and
`conditionD_at_datum_low_level` through `Gap212.conditionD_of_band_split` and `conditionD_of_band`
this gives the condition on `[0, 43/10000]`, which is `43/70` of the chamber `[0, 7/1000]`; the
next band up is `Gap212.conditionD_at_datum_band_4`.

The three branches are `Gap212.conditionD_at_datum_band_2`'s, and the low and middle ones are
verified the same way — uniformly in the cell, rung by rung for `5 ≤ N ≤ 26`. Either the pooled
mass fits in `c₁` and the trivial partition serves, or `5 ≤ N ≤ 26`:
`Gap212.total_le_affine_datum₄` caps `Y` at `1652/5000 = 0.3304` when `N ≤ 4`, below
`c₁ ≥ 1664/5000 - 2ϵ = 0.3328 - 2·10⁻¹⁰`, and `27δ = 1107/2500` exceeds the flat bound `1081/2500`.

**What is new is the high branch.** There every coordinate exceeds `c₃`, so
`Gap212.side_floor_le_cap` turns that floor into a floor on each side's mass and
`Gap212.side_le_six` caps each side at six rough factors; the pooled mass is then
`B_{1,m} + B_{1,m'}` with `m, m' ≤ 6`, the exact cell maximum, where the affine bounds of
`Gap212.total_le_affine_datum₅` overshoot by `4/5000` at the cell `(6, 6)`. Those `4/5000` are
exactly what `Gap212.conditionD_at_datum_band_2` lacked at `N = 12`. -/
theorem conditionD_at_datum_band_3 (j j' : Fin gap212Params.n) {m m' : ℕ} :
    ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      capD (chamberDBand (omegaMax gap212Params j j') (1 / 250) (43 / 10000)) := by
  classical
  refine conditionD_band_of (by norm_num) (by norm_num) j j' fun γ w y hγ hγ' hw0 hw hy' hDle ↦ ?_
  have hc₂ : (0 : ℝ) ≤ 1 / 2 - γ - 2 * w - 1 / 10 ^ 10 := by linarith
  have hc₃ : (0 : ℝ) ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10 := by linarith
  have hc₄ : (0 : ℝ) ≤ 8 * w := by linarith
  -- the seven mass bounds, the floor on the coordinates, and the deficit
  have hYcap := total_le_datum hy'
  have hYaff := total_le_affine_datum hy'
  have hYaff₂ := total_le_affine_datum₂ hy'
  have hYaff₃ := total_le_affine_datum₃ hy'
  have hYaff₄ := total_le_affine_datum₄ hy'
  have hYaff₅ := total_le_affine_datum₅ hy'
  have hYaff₆ := total_le_affine_datum₆ hy'
  have hYlow := card_delta_le_total hy'
  have hδy : ∀ i, (41 / 2500 : ℝ) ≤ y i := fun i ↦ (hy'.1 i).1
  have hy0 : ∀ i, (0 : ℝ) ≤ y i := fun i ↦ le_trans (by norm_num) (hδy i)
  have hD0 : (0 : ℝ) ≤ (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10) := by linarith
  have hDbar : (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10)
      ≤ (∑ i, y i) - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) := by linarith
  have hcast : ((m + m' : ℕ) : ℝ) = m + m' := Nat.cast_add m m'
  -- the cell has between five and twenty-six rough factors
  have hN5 : 5 ≤ m + m' := by exact_mod_cast (show (4 : ℝ) < m + m' by linarith)
  have hN26 : m + m' ≤ 26 :=
    Nat.le_of_lt_succ (by exact_mod_cast (show (m : ℝ) + m' < 27 by linarith))
  have hN5' : (5 : ℝ) ≤ m + m' := by exact_mod_cast hN5
  by_cases hex : ∃ i, y i ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10
  · -- **Blocks three and four are in play.** The floor is `δ`.
    obtain ⟨i₀, hi₀⟩ := hex
    obtain ⟨n, hnle, hnlt⟩ :=
      Packing.exists_nat_mul_le_lt (d := (41 / 2500 : ℝ)) (by norm_num) hD0
    have hnN : (n : ℝ) < (m : ℝ) + (m' : ℝ) := by linarith
    have hnN' : n < m + m' := by exact_mod_cast hnN
    have hnsub : (0 : ℝ) < ((m : ℝ) + (m' : ℝ)) - (n : ℝ) := by linarith
    obtain ⟨v, hvmul, hdv, -, hSsum⟩ := exists_level_coords (by norm_num) hδy hnN'
    push_cast at hvmul
    by_cases hex4 : ∃ j₀, j₀ ≠ i₀ ∧ y j₀ ≤ 8 * w
    · -- **The low branch.** Block three takes `i₀`, block four takes `j₀`; window `W + 2δ`.
      obtain ⟨j₀, hji, hj₀⟩ := hex4
      have hwin : v ≤ 1 / 2 - (∑ i, y i) - 10 * w - 2 / 10 ^ 10 := by
        refine le_of_mul_le_mul_right ?_ hnsub
        rw [hvmul]
        exact datumD_band3_low_window hcast.symm hN5 hN26 hYlow hYcap hYaff hYaff₂ hYaff₃
          hYaff₄ hYaff₅ hYaff₆ hw0 hw (by linarith)
      exact Packing.admitsPartition₄_of_two_singletons
        (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (v := v) (i₀ := i₀) (j₀ := j₀)
        (Ne.symm hji) (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hc₂ hi₀ hj₀
        (by linarith [sum_le_erase_add (univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (hy0 i₀),
          sum_le_erase_add ((univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)).erase i₀) (hy0 j₀)])
        (by linarith [hδy i₀, hδy j₀])
    · -- **The middle branch.** Every coordinate but `i₀` exceeds `c₄`, which caps `N`.
      push Not at hex4
      have hfar : ((m : ℝ) + (m' : ℝ) - 1) * (8 * w) + 41 / 2500
          ≤ ∑ i, y i := by
        have h := floor_off_le_sum (T := {i₀}) (f := 8 * w) fun i hi ↦
          (hex4 i (notMem_singleton.1 hi)).le
        rw [card_singleton, Nat.cast_one, sum_singleton, hcast] at h
        linarith [hδy i₀]
      have hwin : v ≤ 1 / 2 - (∑ i, y i) - 41 / 2500 - 10 * w - 2 / 10 ^ 10 := by
        refine le_of_mul_le_mul_right ?_ hnsub
        rw [hvmul]
        exact datumD_band3_mid_window hcast.symm hN5 hN26 hYlow hYcap hYaff hYaff₂ hYaff₃
          hYaff₄ hYaff₅ hYaff₆ hw0 hw hfar (by linarith)
      exact Packing.admitsPartition₄_of_singleton_block
        (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (v := v) (i₀ := i₀)
        (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hc₂ hc₄ hi₀
        (by linarith [sum_le_erase_add (univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (hy0 i₀)])
        (by linarith [hδy i₀])
  · -- **The high branch.** Every coordinate exceeds `c₃`, which becomes the floor.
    push Not at hex
    have hfy : ∀ i, (4 * w + 41 / 2500 - 1 / 10 ^ 10 : ℝ) ≤ y i := fun i ↦ (hex i).le
    have hYf := mul_le_sum_of_card_le (S := univ) (k := m + m') hc₃ hfy (by simp)
    rw [hcast] at hYf
    obtain ⟨hside, hside'⟩ := side_floor_le_cap hy' hfy
    have hm6 : m ≤ 6 := side_le_six hw0 hside
    have hm6' : m' ≤ 6 := side_le_six hw0 hside'
    have hYside : ∑ i, y i ≤ gap212Cap m + gap212Cap m' := total_le hy'
    have hY1 : 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10 ≤ ∑ i, y i := by linarith
    obtain ⟨n, hnle, hnlt⟩ :=
      Packing.exists_nat_mul_le_lt (d := (4 * w + 41 / 2500 - 1 / 10 ^ 10 : ℝ)) (by linarith) hD0
    have hnN : (n : ℝ) < (m : ℝ) + (m' : ℝ) := by nlinarith
    have hnN' : n < m + m' := by exact_mod_cast hnN
    have hnsub : (0 : ℝ) < ((m : ℝ) + (m' : ℝ)) - (n : ℝ) := by linarith
    obtain ⟨v, hvmul, hdv, -, hSsum⟩ := exists_level_coords hc₃ hfy hnN'
    push_cast at hvmul
    have hwin : v ≤ 1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10 := by
      refine le_of_mul_le_mul_right ?_ hnsub
      rw [hvmul]
      exact datumD_band3_high_window hm6 hm6' hYf hYside hY1 hw0 hw (by linarith)
    refine admitsPartition₄_of_partition₂ ?_ hc₃ hc₄
    exact Packing.admitsPartition₂_of_small_block (v := v)
      (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v))
      (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hD0 (by linarith) (by linarith)


/-! ## The band `43/10000 < ω₀ ≤ 13/2500`

`Gap212.conditionD_at_datum_band_3` stops because its low branch parks only *two* coordinates: at
`ω₀ = 43/10000` and the flat pooled mass `1081/2500` the reserve is `W = -41/5000 - 2ϵ`, the window
`W + 2δ` is `123/5000 = 0.0246`, and the bound on the relevant coordinate is `≈ 0.0239`. Past
`ω₀ = 0.0043685631…` that margin is gone. A third parked coordinate is what the band above needs,
and two things make one available.

**Block four is now the larger small block, and it holds two coordinates.** `c₄ = 8ω₀` passes
`c₃ = 4ω₀ + δ - ϵ` at `ω₀ = (δ - ϵ)/4`, and it passes `2δ` at `ω₀ = δ/4 = 41/10000`.
Both thresholds are below this band's floor `43/10000`. So on this band the dichotomy is run on
`c₄` rather than on `c₃` — a coordinate that fits anywhere fits in block four — and a *pair* of
coordinates may fit in block four together, which frees block three for a third.

Write `Y` for the pooled mass, `N = m + m'`, `c̄₁ = 2/5 - 2δ - 8ω₀ - 2ϵ` for the least first
capacity, and `W = c₂ - (Y - c₁) = 1/2 - Y - 2δ - 10ω₀ - 2ϵ` for the `γ`-free reserve. With floor
`d` and level `n = ⌊(Y - c₁)/d⌋`, `Gap212.Packing.exists_small_coords` supplies `n + 1` coordinates
at most `v = (Y - n d)/(N - n)`, and `Gap212.Packing.le_window_of_core` eliminates `n` from every
requirement. Each branch parks a set of coordinates of total mass `P` and asks `v ≤ W + P`, which
after the elimination is `(Y - Nδ)(W + P) ≤ c̄₁(W + P - δ)`:

* **Some coordinate `i₀` fits in block four, some other `j₀` fits in block three, and
  `y i₀ + y j₀ > c₄`.** Park them separately. Then `P > c₄ = 8ω₀`, which at the top of the band is
  `0.0416` against the `2δ = 0.0328` the third band had: `Gap212.datumD_band4_pair_core`. This is
  the branch that carries the band, and the one that fails first above it.
* **`y i₀ + y j₀ ≤ c₄`, and a third coordinate `k` fits in block three.** Both of the first two go
  into block four and `k` into block three, so `P ≥ 3δ`: `Gap212.datumD_band4_triple_core`. This is
  the third parked coordinate, and this branch is never tight.
* **`y i₀ + y j₀ ≤ c₄`, and every other coordinate exceeds `c₃`.** The pair still goes into block
  four, `P ≥ 2δ`, and the branch condition gives `(N - 2)c₃ + 2δ ≤ Y`:
  `Gap212.datumD_band4_pairfloor_core`.
* **`i₀` fits in block four and every other coordinate exceeds `c₃`.** Only `i₀` is parked,
  `P ≥ δ`, with `(N - 1)c₃ + δ ≤ Y`: `Gap212.datumD_band4_single_core`, whose multiplication step
  needs `0 ≤ W` (`Gap212.datumD_band4_single_reserve`), false without that hypothesis at the top of
  the band.
* **Every coordinate exceeds `c₄`.** Then it exceeds `c₃` too, both small blocks are empty, and
  `c₄` becomes the floor. Here the per-side reading of `Gap212.conditionD_at_datum_band_3` applies
  to the *fourth* block's capacity: `m·8ω₀ ≤ B_{1,m}` caps each side at five factors
  (`Gap212.side_le_five`), so `N ≤ 10` and `Y ≤ B_{1,m} + B_{1,m'} ≤ 1906/5000 = 0.3812`.
  `Gap212.datumD_band4_high_core`, verified over the twenty-five pairs of side counts.

The four rung-based branches are verified for `4 ≤ N ≤ 26`: `Gap212.total_le_affine_datum₄` caps
`Y` at `1603/5000 = 0.3206` when `N ≤ 3`, below `c₁ ≥ 1628/5000 - 2ϵ = 0.3256 - 2·10⁻¹⁰`, and
`27δ = 1107/2500` exceeds the flat bound `1081/2500`. All five run through one engine,
`Gap212.Packing.admitsPartition₄_of_blocks`, which takes the two small blocks' contents as
`Finset`s rather than as named coordinates.

The one-parked branch is the exception: it is read one side at a time, like the high branch, and for
the same reason. Stated against the affine mass bounds it turns over at `N = 11` and
`ω₀ = 0.0050846590…`, where those bounds allow `Y = 1939/5000`. But a cell of size eleven whose
sides can each hold at most six coordinates above `c₃` must be `(5, 6)` or `(6, 5)`, whose mass
maximum is `1936/5000`; and `Gap212.side_floor_le_cap_except` — the branch condition read per side,
with the parked coordinate excused — says `(m - 1)c₃ + δ ≤ B_{1,m}`, which fails at `m = 6` above
`ω₀ = 491/100000 + ϵ/4` and removes even those cells. So that branch is verified over the forty-nine
pairs `m, m' ∈ [0, 6]` rather than rung by rung.

**`13/2500` is where this stops, and the wall is the high branch at a four-coordinate cell.** The
binding slacks are `5.744·10⁻⁵` for the split-pair branch at `N = 20` and `ω₀ = 13/2500`,
`7.586·10⁻⁵` for the high branch at the cell `(m, m') = (5, 5)`, `1.235·10⁻⁴` for the one-parked
branch at the cell `(5, 5)`, `1.587·10⁻⁴` for the high branch at `(1, 3)`, and `2.311·10⁻⁴` for the
high branch's floor `c₄ ≤ W` at `(5, 5)`. The first to fail above the band is the high branch at
`(1, 3)`, at `ω₀ = 0.0052849789…`.

That cell has four coordinates and `Y - c̄₁ < c₄`, so the level is `n = 0` and the true bound on the
smallest coordinate is `Y/4`; the continuous elimination of `n` in
`Gap212.Packing.le_window_of_core` allows `n` up to `(Y - c̄₁)/c₄ ≈ 0.13` and loses exactly there.
Carrying the integrality of `n` into that branch buys `ω₀ = 271/50000 - ϵ/5 = 0.00542 - 2·10⁻¹¹`,
which is what `Gap212.conditionD_at_datum_band_5` does — it also has to be carried into the
split-pair and one-parked branches, whose continuous readings turn over at `0.0053138` and
`0.0052916`, so the integer reading of the high branch alone is not enough. Past it a *fourth*
parked coordinate is needed. Block four can hold three at the floor once `3δ ≤ 8ω₀`, i.e. from
`ω₀ = 123/20000`, and block three tops out at two on the whole chamber because `3δ = 0.0492` exceeds
`c₃ ≤ 111/2500 = 0.0444`. So the coordinates are there to park, and what selects four of them is a
dichotomy that counts items per bin rather than only their mass: `Gap212.conditionD_at_datum_band_6`
runs it on pairs. -/

set_option maxHeartbeats 1000000 in
-- Twenty-three `nlinarith` calls, one per value of `N`.
/-- **The split-pair branch's numerical inequality.** With floor `δ` and the two parked
coordinates in different blocks, `(Y - Nδ)(W + 8ω₀) ≤ c̄₁(W + 8ω₀ - δ)`.

The branch condition is `c₄ < y i₀ + y j₀`, so the parked mass exceeds the fourth block's whole
capacity `c₄ = 8ω₀` rather than merely `2δ`. That is the gain over
`Gap212.datumD_band3_low_core`, and it is what the band rests on: verified rung by rung for
`4 ≤ N ≤ 26`, its least slack is `1435998854000001/25000000000000000000 ≈ 5.744·10⁻⁵`, at `N = 20`,
`ω₀ = 13/2500` and the flat pooled mass
`Y = 1081/2500`. -/
theorem datumD_band4_pair_core {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 4 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 43 / 10000 < w) (hw : w ≤ 13 / 2500) :
    (Y - N * (41 / 2500))
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 8 * w)
      ≤ (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 8 * w - 41 / 2500) := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 h4 h5 h6 <;>
    nlinarith [hYlo, hYcap, h1, h2, h3, h4, h5, h6, hw0, hw]

set_option maxHeartbeats 1000000 in
-- Twenty-three `nlinarith` calls, one per value of `N`.
/-- **The three-parked branch's numerical inequality.** With floor `δ` and three coordinates
parked — two in block four, one in block three — `(Y - Nδ)(W + 3δ) ≤ c̄₁(W + 2δ)`.

This is the third parked coordinate, available because `2δ ≤ 8ω₀` on this band. It is never the
binding branch: at `N = 20`, `ω₀ = 13/2500` and `Y = 1081/2500` the window `W + 3δ = 0.032` is far
above the bound `v ≈ 0.0239` on the relevant coordinate. -/
theorem datumD_band4_triple_core {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 4 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 43 / 10000 < w) (hw : w ≤ 13 / 2500) :
    (Y - N * (41 / 2500))
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 3 * (41 / 2500))
      ≤ (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 2 * (41 / 2500)) := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 h4 h5 h6 <;>
    nlinarith [hYlo, hYcap, h1, h2, h3, h4, h5, h6, hw0, hw]

set_option maxHeartbeats 1000000 in
-- Twenty-three `nlinarith` calls, one per value of `N`.
/-- **The pair-and-floor branch's multiplier is nonnegative**: `0 ≤ W + δ`, whenever every
coordinate outside the parked pair exceeds `c₃` — which is what puts `(N - 2)c₃ + 2δ ≤ Y` in the
hypotheses.

Without that hypothesis this is false at the top of the band: at `Y = 1081/2500` and
`ω₀ = 13/2500`, `W + δ = -1/1250 - 2ϵ`. With it, the pooled mass is capped hard enough at every
rung for the elimination of the level `n` in `Gap212.Packing.le_window_of_core` to be multiplied
through. -/
theorem datumD_band4_pairfloor_reserve {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 4 ≤ k)
    (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 43 / 10000 < w) (hw : w ≤ 13 / 2500)
    (hfar : (N - 2) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 2 * (41 / 2500) ≤ Y) :
    0 ≤ 1 / 2 - Y - 41 / 2500 - 10 * w - 2 / 10 ^ 10 := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 h4 h5 h6 hfar <;>
    nlinarith [hYlo, hYcap, h1, h2, h3, h4, h5, h6, hw0, hw, hfar]

set_option maxHeartbeats 1000000 in
-- Twenty-three `nlinarith` calls, one per value of `N`.
/-- **The pair-and-floor branch's numerical inequality.** The two parked coordinates share block
four, block three is empty, and every coordinate outside the pair exceeds `c₃`:
`(Y - Nδ)(W + 2δ) ≤ c̄₁(W + δ)`, carrying `(N - 2)c₃ + 2δ ≤ Y`.

Without that hypothesis this is `Gap212.datumD_band3_low_core`, which fails on this band; with it
the pooled mass is capped hard enough at every rung that the two-coordinate window suffices. -/
theorem datumD_band4_pairfloor_core {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 4 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 43 / 10000 < w) (hw : w ≤ 13 / 2500)
    (hfar : (N - 2) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 2 * (41 / 2500) ≤ Y) :
    (Y - N * (41 / 2500))
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 2 * (41 / 2500))
      ≤ (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 41 / 2500) := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 h4 h5 h6 hfar <;>
    nlinarith [hYlo, hYcap, h1, h2, h3, h4, h5, h6, hw0, hw, hfar]

set_option maxHeartbeats 1000000 in
-- Forty-nine `nlinarith` calls, one per pair of side counts.
/-- **The single-parked branch's reserve is nonnegative**: `0 ≤ W`, whenever every coordinate but
the parked one exceeds `c₃` — which is what puts `(N - 1)c₃ + δ ≤ Y` in the hypotheses, and with it
the per-side readings `(m - 1)c₃ + δ ≤ B_{1,m}` of `Gap212.side_floor_le_cap_except`.

`Gap212.band3_mid_reserve` with `c₃` in place of `c₄` as the floor on the unparked coordinates,
since on this band `c₃` is the *smaller* of the two small capacities and so the weaker branch
condition, and with the per-side mass bound in place of the affine ones. Without the hypothesis it
is false at the top of the band: at `Y = 1081/2500` and `ω₀ = 13/2500`, `W = -43/2500 - 2ϵ`. -/
theorem datumD_band4_single_reserve {Y w : ℝ} {m m' : ℕ} (hm : m ≤ 6) (hm' : m' ≤ 6)
    (hs : ((m : ℝ) - 1) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 41 / 2500 ≤ gap212Cap m)
    (hs' : ((m' : ℝ) - 1) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 41 / 2500 ≤ gap212Cap m')
    (hfar : (((m : ℝ) + (m' : ℝ)) - 1) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 41 / 2500 ≤ Y)
    (hYside : Y ≤ gap212Cap m + gap212Cap m')
    (hY1 : 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10 ≤ Y)
    (hw : w ≤ 13 / 2500) :
    0 ≤ 1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10 := by
  interval_cases m <;> interval_cases m' <;>
    norm_num [gap212Cap] at hYside hfar hs hs' <;> nlinarith [hfar, hYside, hY1, hs, hs', hw]

set_option maxHeartbeats 1000000 in
-- Forty-nine `nlinarith` calls, one per pair of side counts.
/-- **The single-parked branch's numerical inequality.** Only `i₀` is parked, in block four:
`(Y - Nδ)(W + δ) ≤ c̄₁ W` at `N = m + m'`, carrying `(N - 1)c₃ + δ ≤ Y` and the per-side readings
`(m - 1)c₃ + δ ≤ B_{1,m}` of `Gap212.side_floor_le_cap_except`.

Those per-side readings are what carries the band past `ω₀ = 1/200`. Stated against the affine mass
bounds and the rung `N` alone, the branch turns over at `N = 11` and `ω₀ = 0.0050846590…`, where
the affine bounds allow `Y = 1939/5000` — but the only cells of size eleven whose sides can each
hold at most six coordinates above `c₃` are `(5, 6)` and `(6, 5)`, whose mass maximum is
`1936/5000`, and above `ω₀ = 491/100000 + ϵ/4` the inequality `(m - 1)c₃ + δ ≤ B_{1,6}` fails, so
even those are gone. Verified over the
forty-nine pairs `m, m' ∈ [0, 6]`; the least slack is
`3087999288000001/25000000000000000000 ≈ 1.235·10⁻⁴`, at the cell `(5, 5)`. -/
theorem datumD_band4_single_core {Y w : ℝ} {m m' : ℕ} (hm : m ≤ 6) (hm' : m' ≤ 6)
    (hs : ((m : ℝ) - 1) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 41 / 2500 ≤ gap212Cap m)
    (hs' : ((m' : ℝ) - 1) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 41 / 2500 ≤ gap212Cap m')
    (hYlo : ((m : ℝ) + (m' : ℝ)) * (41 / 2500) ≤ Y)
    (hfar : (((m : ℝ) + (m' : ℝ)) - 1) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 41 / 2500 ≤ Y)
    (hYside : Y ≤ gap212Cap m + gap212Cap m')
    (hY1 : 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10 ≤ Y)
    (hw0 : 43 / 10000 < w) (hw : w ≤ 13 / 2500) :
    (Y - ((m : ℝ) + (m' : ℝ)) * (41 / 2500))
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 41 / 2500)
      ≤ (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
        * (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) := by
  interval_cases m <;> interval_cases m' <;>
    norm_num [gap212Cap] at hYside hfar hYlo hs hs' ⊢ <;>
    nlinarith [hfar, hYside, hY1, hYlo, hs, hs', hw0, hw]

set_option maxHeartbeats 1000000 in
-- Twenty-five `nlinarith` calls, one per pair of side counts.
/-- **The high branch's floor is below its reserve**: `c₄ = 8ω₀ ≤ W`, whenever every coordinate
exceeds `c₄`.

`Gap212.band3_high_floor` for the fourth block's capacity, against the per-side mass bound that
`Gap212.side_le_five` unlocks. The per-side *counts* are hypotheses too and not merely `m, m' ≤ 5`:
without `m·8ω₀ ≤ B_{1,m}` the cell `(4, 5)` survives and this fails there at `ω₀ ≈ 0.00519` by
`2.2·10⁻⁴`, while with it that cell is impossible — five coordinates above `c₄ = 0.04152` would
need `0.2076 ≤ B_{1,5} = 0.1906`. Its least slack is `≈ 2.311·10⁻⁴`, at the cell `(m, m') = (5, 5)`
and `ω₀ ≈ 0.004765`. -/
theorem band4_high_floor {Y w : ℝ} {m m' : ℕ} (hm : m ≤ 5) (hm' : m' ≤ 5)
    (hs : (m : ℝ) * (8 * w) ≤ gap212Cap m) (hs' : (m' : ℝ) * (8 * w) ≤ gap212Cap m')
    (hYf : ((m : ℝ) + (m' : ℝ)) * (8 * w) ≤ Y)
    (hYside : Y ≤ gap212Cap m + gap212Cap m')
    (hY1 : 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10 ≤ Y)
    (hw : w ≤ 13 / 2500) :
    0 ≤ (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) - 8 * w := by
  interval_cases m <;> interval_cases m' <;>
    norm_num [gap212Cap] at hYside hYf hs hs' <;> nlinarith [hYf, hYside, hY1, hs, hs', hw]

set_option maxHeartbeats 1000000 in
-- Twenty-five `nlinarith` calls, one per pair of side counts.
/-- **The high branch's numerical inequality.** With floor `c₄ = 8ω₀` and both small blocks empty,
`(Y - N c₄) W ≤ c̄₁ (W - c₄)`, at `N = m + m'`.

`Gap212.datumD_band3_high_core` with the fourth block's capacity as the floor — on this band the
larger of the two, so the stronger reading. `Gap212.side_le_five` caps both side counts at five,
and the pooled mass is then `B_{1,m} + B_{1,m'}`, the exact cell maximum, at worst
`1906/5000 = 0.3812` at the cell `(5, 5)`. The verification runs over the twenty-five pairs
`m, m' ∈ [0, 5]` under the per-side counts `m·8ω₀ ≤ B_{1,m}`, which is what makes the pairs with a
side of five factors above `c₄` vacuous at the top of the band; the least slack is
`≈ 7.586·10⁻⁵`, at `(5, 5)` and `ω₀ ≈ 0.004765`. -/
theorem datumD_band4_high_core {Y w : ℝ} {m m' : ℕ} (hm : m ≤ 5) (hm' : m' ≤ 5)
    (hs : (m : ℝ) * (8 * w) ≤ gap212Cap m) (hs' : (m' : ℝ) * (8 * w) ≤ gap212Cap m')
    (hYf : ((m : ℝ) + (m' : ℝ)) * (8 * w) ≤ Y)
    (hYside : Y ≤ gap212Cap m + gap212Cap m')
    (hY1 : 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10 ≤ Y)
    (hw0 : 43 / 10000 < w) (hw : w ≤ 13 / 2500) :
    (Y - ((m : ℝ) + (m' : ℝ)) * (8 * w))
        * (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
      ≤ (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) - 8 * w) := by
  interval_cases m <;> interval_cases m' <;>
    norm_num [gap212Cap] at hYside hYf hs hs' ⊢ <;>
    nlinarith [hYf, hYside, hY1, hs, hs', hw0, hw]

set_option maxHeartbeats 1000000 in
-- Five branches, each parking a different set of coordinates in the two small blocks and then
-- running the subset-sum engine, in a single declaration.
/-- **Condition D at `p_⋆` for every cell, every `γ`, and every level `43/10000 < ω₀ ≤ 13/2500`.**

The capacities are `Gap212.capD`'s and the chamber is `Gap212.chamberDBand` at the datum's level
`ω(1,1) = 7/1000` with the level banded to `(43/10000, 13/2500]`. Spliced onto
`Gap212.conditionD_at_datum_band_3`, `conditionD_at_datum_band_2`, `conditionD_at_datum_mid_band`
and `conditionD_at_datum_low_level` through `Gap212.conditionD_of_band_split` and
`conditionD_of_band` this gives the condition on `[0, 13/2500]`, which is `26/35` of the chamber
`[0, 7/1000]`.

The five branches are described above this declaration. What is new against
`Gap212.conditionD_at_datum_band_3` is that the dichotomy is run on `c₄ = 8ω₀` rather than on `c₃`,
because above `ω₀ = 41/10000` the fourth block is the larger of the two small ones and can hold two
coordinates at the floor — so a *third* coordinate may be parked, and when only two are, the pair
that shares block four has mass exceeding `c₄` rather than `2δ`. -/
theorem conditionD_at_datum_band_4 (j j' : Fin gap212Params.n) {m m' : ℕ} :
    ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      capD (chamberDBand (omegaMax gap212Params j j') (43 / 10000) (13 / 2500)) := by
  classical
  refine conditionD_band_of (by norm_num) (by norm_num) j j' fun γ w y hγ hγ' hw0 hw hy' hDle ↦ ?_
  have hc₂ : (0 : ℝ) ≤ 1 / 2 - γ - 2 * w - 1 / 10 ^ 10 := by linarith
  have hc₃ : (0 : ℝ) ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10 := by linarith
  have hc₄ : (0 : ℝ) ≤ 8 * w := by linarith
  -- the seven mass bounds, the floor on the coordinates, and the deficit
  have hYcap := total_le_datum hy'
  have hYaff := total_le_affine_datum hy'
  have hYaff₂ := total_le_affine_datum₂ hy'
  have hYaff₃ := total_le_affine_datum₃ hy'
  have hYaff₄ := total_le_affine_datum₄ hy'
  have hYaff₅ := total_le_affine_datum₅ hy'
  have hYaff₆ := total_le_affine_datum₆ hy'
  have hYlow := card_delta_le_total hy'
  have hδy : ∀ i, (41 / 2500 : ℝ) ≤ y i := fun i ↦ (hy'.1 i).1
  have hy0 : ∀ i, (0 : ℝ) ≤ y i := fun i ↦ le_trans (by norm_num) (hδy i)
  have hD0 : (0 : ℝ) ≤ (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10) := by linarith
  have hDbar : (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10)
      ≤ (∑ i, y i) - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) := by linarith
  have hcast : ((m + m' : ℕ) : ℝ) = m + m' := Nat.cast_add m m'
  -- the cell has between four and twenty-six rough factors
  have hN4 : 4 ≤ m + m' := by exact_mod_cast (show (3 : ℝ) < m + m' by linarith)
  have hN26 : m + m' ≤ 26 :=
    Nat.le_of_lt_succ (by exact_mod_cast (show (m : ℝ) + m' < 27 by linarith))
  have hN4' : (4 : ℝ) ≤ m + m' := by exact_mod_cast hN4
  by_cases hex : ∃ i, y i ≤ 8 * w
  · -- **Block four is in play.** Its capacity is the larger of the two small ones on this band.
    obtain ⟨i₀, hi₀⟩ := hex
    obtain ⟨n, hnle, hnlt⟩ :=
      Packing.exists_nat_mul_le_lt (d := (41 / 2500 : ℝ)) (by norm_num) hD0
    have hnN : (n : ℝ) < (m : ℝ) + (m' : ℝ) := by linarith
    have hnN' : n < m + m' := by exact_mod_cast hnN
    have hnsub : (0 : ℝ) < ((m : ℝ) + (m' : ℝ)) - (n : ℝ) := by linarith
    obtain ⟨v, hvmul, hdv, -, hSsum⟩ := exists_level_coords (by norm_num) hδy hnN'
    push_cast at hvmul
    have hStot : (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10)
        ≤ ∑ i ∈ univ.filter (fun i : Fin (m + m') ↦ y i ≤ v), y i := by linarith
    by_cases hex3 : ∃ j₀, j₀ ≠ i₀ ∧ y j₀ ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10
    · obtain ⟨j₀, hji, hj₀⟩ := hex3
      by_cases hAB : 8 * w < y i₀ + y j₀
      · -- **The split branch.** `i₀` in block four, `j₀` in block three; window `W + 8ω₀`.
        have hwin : v ≤ (1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 8 * w := by
          refine le_of_mul_le_mul_right ?_ hnsub
          rw [hvmul]
          have hc := datumD_band4_pair_core hcast.symm hN4 hN26 hYlow hYcap hYaff hYaff₂
            hYaff₃ hYaff₄ hYaff₅ hYaff₆ hw0 hw
          exact Packing.le_window_of_core (cb := 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
            (by norm_num) (by linarith) (by linarith) (by linarith)
        refine Packing.admitsPartition₄_of_blocks (T₃ := {j₀}) (T₄ := {i₀})
          (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (v := v)
          (Finset.disjoint_singleton.2 hji) (by simpa using hj₀) (by simpa using hi₀)
          (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hc₂ ?_ ?_
        · refine le_trans ?_ (Packing.sum_sdiff_ge hy0)
          rw [Finset.sum_union (Finset.disjoint_singleton.2 hji), Finset.sum_singleton,
            Finset.sum_singleton]
          linarith
        · rw [Finset.sum_singleton, Finset.sum_singleton]
          linarith
      · -- **The pair branch.** `i₀` and `j₀` both fit in block four; block three is free.
        push Not at hAB
        by_cases hex3b : ∃ k, k ≠ i₀ ∧ k ≠ j₀ ∧ y k ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10
        · -- a third coordinate goes into block three; window `W + 3δ`
          obtain ⟨k, hki, hkj, hk⟩ := hex3b
          have hwin : v ≤ (1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
              + 3 * (41 / 2500) := by
            refine le_of_mul_le_mul_right ?_ hnsub
            rw [hvmul]
            have hc := datumD_band4_triple_core hcast.symm hN4 hN26 hYlow hYcap hYaff hYaff₂
              hYaff₃ hYaff₄ hYaff₅ hYaff₆ hw0 hw
            exact Packing.le_window_of_core (cb := 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
              (by norm_num) (by linarith) (by linarith) (by linarith)
          have hTd : Disjoint ({k} : Finset (Fin (m + m'))) ({i₀, j₀} : Finset (Fin (m + m'))) := by
            simp [hki, hkj]
          have hpair : ∑ i ∈ ({i₀, j₀} : Finset (Fin (m + m'))), y i = y i₀ + y j₀ :=
            Finset.sum_pair (Ne.symm hji)
          refine Packing.admitsPartition₄_of_blocks (T₃ := {k}) (T₄ := {i₀, j₀})
            (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (v := v)
            hTd (by simpa using hk) (by rw [hpair]; linarith)
            (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hc₂ ?_ ?_
          · refine le_trans ?_ (Packing.sum_sdiff_ge hy0)
            rw [Finset.sum_union hTd, Finset.sum_singleton, hpair]
            linarith [hδy i₀, hδy j₀, hδy k]
          · rw [Finset.sum_singleton, hpair]
            linarith [hδy i₀, hδy j₀, hδy k]
        · -- every other coordinate exceeds `c₃`, which caps `N`; window `W + 2δ`
          push Not at hex3b
          have hpair : ∑ i ∈ ({i₀, j₀} : Finset (Fin (m + m'))), y i = y i₀ + y j₀ :=
            Finset.sum_pair (Ne.symm hji)
          have hfar : ((m : ℝ) + (m' : ℝ) - 2) * (4 * w + 41 / 2500 - 1 / 10 ^ 10)
              + 2 * (41 / 2500) ≤ ∑ i, y i := by
            have h := floor_off_le_sum (T := {i₀, j₀}) (f := 4 * w + 41 / 2500 - 1 / 10 ^ 10)
              fun i hi ↦ by
                simp only [mem_insert, mem_singleton, not_or] at hi
                exact (hex3b i hi.1 hi.2).le
            rw [card_pair (Ne.symm hji), Nat.cast_ofNat, hpair, hcast] at h
            linarith [hδy i₀, hδy j₀]
          have hwin : v ≤ (1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
              + 2 * (41 / 2500) := by
            refine le_of_mul_le_mul_right ?_ hnsub
            rw [hvmul]
            have hres := datumD_band4_pairfloor_reserve hcast.symm hN4 hN26 hYlow hYcap hYaff
              hYaff₂ hYaff₃ hYaff₄ hYaff₅ hYaff₆ hw0 hw hfar
            have hc := datumD_band4_pairfloor_core hcast.symm hN4 hN26 hYlow hYcap hYaff
              hYaff₂ hYaff₃ hYaff₄ hYaff₅ hYaff₆ hw0 hw hfar
            exact Packing.le_window_of_core (cb := 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
              (by norm_num) (by linarith) (by linarith) (by linarith)
          refine Packing.admitsPartition₄_of_blocks (T₃ := ∅) (T₄ := {i₀, j₀})
            (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (v := v)
            (Finset.disjoint_empty_left _) (by simpa using hc₃) (by rw [hpair]; linarith)
            (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hc₂ ?_ ?_
          · refine le_trans ?_ (Packing.sum_sdiff_ge hy0)
            rw [Finset.empty_union, hpair]
            linarith [hδy i₀, hδy j₀]
          · rw [Finset.sum_empty, hpair]
            linarith [hδy i₀, hδy j₀]
    · -- **The single branch.** Every coordinate but `i₀` exceeds `c₃`; window `W + δ`.
      push Not at hex3
      have hfar : ((m : ℝ) + (m' : ℝ) - 1) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 41 / 2500
          ≤ ∑ i, y i := by
        have h := floor_off_le_sum (T := {i₀}) (f := 4 * w + 41 / 2500 - 1 / 10 ^ 10) fun i hi ↦
          (hex3 i (notMem_singleton.1 hi)).le
        rw [card_singleton, Nat.cast_one, sum_singleton, hcast] at h
        linarith [hδy i₀]
      -- the branch condition, read one side at a time
      obtain ⟨hs, hs'⟩ := side_floor_le_cap_except hy' hδy (by linarith)
        (fun i hi ↦ (hex3 i hi).le)
      have hm6 : m ≤ 6 := side_le_six_except hw0 hs
      have hm6' : m' ≤ 6 := side_le_six_except hw0 hs'
      have hYside : ∑ i, y i ≤ gap212Cap m + gap212Cap m' := total_le hy'
      have hY1 : 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10 ≤ ∑ i, y i := by linarith
      have hres := datumD_band4_single_reserve hm6 hm6' hs hs' hfar hYside hY1 hw
      have hwin : v ≤ (1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
          + 41 / 2500 := by
        refine le_of_mul_le_mul_right ?_ hnsub
        rw [hvmul]
        have hc := datumD_band4_single_core hm6 hm6' hs hs' hYlow hfar hYside hY1 hw0 hw
        exact Packing.le_window_of_core (cb := 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
          (by norm_num) (by linarith) (by linarith) (by linarith)
      refine Packing.admitsPartition₄_of_blocks (T₃ := ∅) (T₄ := {i₀})
        (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (v := v)
        (Finset.disjoint_empty_left _) (by simpa using hc₃) (by simpa using hi₀)
        (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hc₂ ?_ ?_
      · refine le_trans ?_ (Packing.sum_sdiff_ge hy0)
        rw [Finset.empty_union, Finset.sum_singleton]
        linarith [hδy i₀]
      · rw [Finset.sum_empty, Finset.sum_singleton]
        linarith [hδy i₀]
  · -- **The high branch.** Every coordinate exceeds `c₄ = 8ω₀`, the larger small block.
    push Not at hex
    have hfy : ∀ i, (8 * w : ℝ) ≤ y i := fun i ↦ (hex i).le
    have hYf := mul_le_sum_of_card_le (S := univ) (k := m + m') hc₄ hfy (by simp)
    rw [hcast] at hYf
    obtain ⟨hside, hside'⟩ := side_floor_le_cap hy' hfy
    have hm5 : m ≤ 5 := side_le_five hw0 hside
    have hm5' : m' ≤ 5 := side_le_five hw0 hside'
    have hYside : ∑ i, y i ≤ gap212Cap m + gap212Cap m' := total_le hy'
    have hY1 : 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10 ≤ ∑ i, y i := by linarith
    have hfl := band4_high_floor hm5 hm5' hside hside' hYf hYside hY1 hw
    obtain ⟨n, hnle, hnlt⟩ :=
      Packing.exists_nat_mul_le_lt (d := (8 * w : ℝ)) (by linarith) hD0
    have hnN : (n : ℝ) < (m : ℝ) + (m' : ℝ) := by nlinarith
    have hnN' : n < m + m' := by exact_mod_cast hnN
    have hnsub : (0 : ℝ) < ((m : ℝ) + (m' : ℝ)) - (n : ℝ) := by linarith
    obtain ⟨v, hvmul, hdv, -, hSsum⟩ := exists_level_coords hc₄ hfy hnN'
    push_cast at hvmul
    have hwin : v ≤ 1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10 := by
      refine le_of_mul_le_mul_right ?_ hnsub
      rw [hvmul]
      exact Packing.le_window_of_core (d := (8 * w : ℝ))
        (cb := 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) (by linarith)
        (by linarith) (by linarith)
        (datumD_band4_high_core hm5 hm5' hside hside' hYf hYside hY1 hw0 hw)
    refine admitsPartition₄_of_partition₂ ?_ hc₃ hc₄
    exact Packing.admitsPartition₂_of_small_block (v := v)
      (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v))
      (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hD0 (by linarith) (by linarith)

/-! ## The band `13/2500 < ω₀ ≤ 541/100000`

`Gap212.conditionD_at_datum_band_4` stops at `ω₀ = 0.0052849789…`, and it does not stop because a
branch runs out of capacity. It stops because the *level* is eliminated continuously.

Every branch of that theorem computes a level `n = ⌊(Y - c₁)/d⌋` from the deficit and the floor
`d`, takes the `n + 1` coordinates that `Gap212.Packing.exists_small_coords` puts below
`v = (Y - n d)/(N - n)`, and asks `v ≤ W + P` for the reserve `W` and the parked mass `P`. That
requirement is increasing in `n`, so `Gap212.Packing.le_window_of_core` — which knows only
`n d ≤ Y - c̄₁` — has to make it good for every *real* `n` up to `(Y - c̄₁)/d`. But `n` is a
natural number, and at the three branches that bind the fractional part is the whole loss:

* the high branch at the cell `(m, m') = (1, 3)`, where the rung has four coordinates,
  `Y - c̄₁ < c₄` forces `n = 0`, and the continuous bound allows `n` up to `(Y - c̄₁)/c₄ ≈ 0.13`;
* the split-pair branch at `N = 20`, where `(Y - c̄₁)/δ = 6.61` and the level is at most `6`;
* the one-parked branch at the cell `(5, 5)`, where `(Y - c̄₁)/δ = 4.22` and the level is at
  most `4`.

So this band is `Gap212.conditionD_at_datum_band_4`'s five branches with those three window steps
restated at an *integer* level and verified level by level:
`Gap212.datumD_band5_pair_window`, `datumD_band5_single_window`, `datumD_band5_high_window`. The
two branches that never bind keep the continuous elimination, restated only for the new level
range: `Gap212.datumD_band5_triple_core`, `datumD_band5_pairfloor_core` and
`datumD_band5_pairfloor_reserve`.

Reading the level as an integer is worth `13/2500 = 0.0052` to
`271/50000 - ϵ/5 = 0.00542 - 2·10⁻¹¹`, and no further: at `ω₀ = 271/50000` the cell `(1, 3)` has
`Y ≤ B_{1,1} + B_{1,3} = 1652/5000`, the level is already pinned to its only value `0`, and the
bound `Y/4` on the smallest coordinate meets the reserve `W` with equality. `541/100000` is the
round numeral below that.
-/

set_option maxHeartbeats 4000000 in
-- One `linarith` per pair `(N, n)`: the rung and the integer level.
/-- **The split-pair branch's window, with the level read as an integer.** With floor `δ` and the
two parked coordinates in different blocks, `Y - nδ ≤ (W + 8ω₀)(N - n)` at every integer level
`n ≤ 6` below the rung `N`.

This replaces the continuous elimination of `Gap212.Packing.le_window_of_core` used by
`Gap212.datumD_band4_pair_core`, and that is the whole difference between the fourth band and the
fifth. The requirement is increasing in `n`, so the continuous form has to allow `n` up to
`(Y - c̄₁)/δ`, which is `6.61` at `N = 20`, `Y = 1081/2500` and the top of this band, while the
level is an integer and so at most `6`. Nothing else changes: `n δ ≤ Y - c̄₁` still caps the level,
and it is what makes the pairs with `n` too large vacuous rung by rung. Verified over the `155`
feasible pairs `4 ≤ N ≤ 26`, `n ≤ min(6, N-1)`; the least slack is at `N = 20`, `n = 6` and the
flat pooled mass, where `Y - 6δ = 334/1000` falls short of `14(W + 8ω₀)` by `1.72·10⁻³`. -/
theorem datumD_band5_pair_window {N nn Y w : ℝ} {k n : ℕ} (hNk : N = k) (hnn : nn = n)
    (hk1 : 4 ≤ k) (hk2 : k ≤ 26) (hnK : n ≤ 6) (hnlt : n < k)
    (hn : nn * (41 / 2500) ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10))
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 13 / 2500 < w) (hw : w ≤ 541 / 100000) :
    Y - nn * (41 / 2500)
      ≤ ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 8 * w) * (N - nn) := by
  subst hNk
  subst hnn
  interval_cases k <;> interval_cases n <;> push_cast at hn hYlo h1 h2 h3 h4 h5 h6 ⊢ <;> linarith

set_option maxHeartbeats 1000000 in
-- Twenty-three `nlinarith` calls, one per value of `N`.
/-- **The three-parked branch's numerical inequality, on the fifth band.**
`Gap212.datumD_band4_triple_core` at the level range `13/2500 < ω₀ ≤ 541/100000`: with floor `δ`
and three coordinates parked — two in block four, one in block three —
`(Y - Nδ)(W + 3δ) ≤ c̄₁(W + 2δ)`.

Still never the binding branch: the least slack over `4 ≤ N ≤ 26` is `1.25·10⁻³`, at `N = 20` and
the flat pooled mass, where the continuous elimination of the level is good enough and no integer
reading is needed. -/
theorem datumD_band5_triple_core {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 4 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 13 / 2500 < w) (hw : w ≤ 541 / 100000) :
    (Y - N * (41 / 2500))
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 3 * (41 / 2500))
      ≤ (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 2 * (41 / 2500)) := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 h4 h5 h6 <;>
    nlinarith [hYlo, hYcap, h1, h2, h3, h4, h5, h6, hw0, hw]

set_option maxHeartbeats 1000000 in
-- Twenty-three `nlinarith` calls, one per value of `N`.
/-- **The pair-and-floor branch's multiplier is nonnegative, on the fifth band**: `0 ≤ W + δ`
whenever every coordinate outside the parked pair exceeds `c₃`.

`Gap212.datumD_band4_pairfloor_reserve` at the level range `13/2500 < ω₀ ≤ 541/100000`. The least
slack is `4.17·10⁻²`. -/
theorem datumD_band5_pairfloor_reserve {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 4 ≤ k)
    (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 13 / 2500 < w) (hw : w ≤ 541 / 100000)
    (hfar : (N - 2) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 2 * (41 / 2500) ≤ Y) :
    0 ≤ 1 / 2 - Y - 41 / 2500 - 10 * w - 2 / 10 ^ 10 := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 h4 h5 h6 hfar <;>
    nlinarith [hYlo, hYcap, h1, h2, h3, h4, h5, h6, hw0, hw, hfar]

set_option maxHeartbeats 1000000 in
-- Twenty-three `nlinarith` calls, one per value of `N`.
/-- **The pair-and-floor branch's numerical inequality, on the fifth band.**
`Gap212.datumD_band4_pairfloor_core` at the level range `13/2500 < ω₀ ≤ 541/100000`: the two parked
coordinates share block four, block three is empty, every coordinate outside the pair exceeds `c₃`,
and `(Y - Nδ)(W + 2δ) ≤ c̄₁(W + δ)`.

The least slack over `4 ≤ N ≤ 26` is `1.46·10⁻³`, at `N = 11`. -/
theorem datumD_band5_pairfloor_core {N Y w : ℝ} {k : ℕ} (hNk : N = k) (hk1 : 4 ≤ k) (hk2 : k ≤ 26)
    (hYlo : N * (41 / 2500) ≤ Y) (hYcap : Y ≤ 1081 / 2500)
    (h1 : Y ≤ (1546 + 36 * N) / 5000) (h2 : Y ≤ (1748 + 21 * N) / 5000)
    (h3 : Y ≤ (1802 + 18 * N) / 5000) (h4 : Y ≤ (1456 + 49 * N) / 5000)
    (h5 : Y ≤ (1598 + 31 * N) / 5000) (h6 : Y ≤ (1668 + 26 * N) / 5000)
    (hw0 : 13 / 2500 < w) (hw : w ≤ 541 / 100000)
    (hfar : (N - 2) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 2 * (41 / 2500) ≤ Y) :
    (Y - N * (41 / 2500))
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 2 * (41 / 2500))
      ≤ (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
        * ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 41 / 2500) := by
  subst hNk
  interval_cases k <;> push_cast at hYlo h1 h2 h3 h4 h5 h6 hfar <;>
    nlinarith [hYlo, hYcap, h1, h2, h3, h4, h5, h6, hw0, hw, hfar]

set_option maxHeartbeats 4000000 in
-- One `linarith` per triple `(m, m', n)`: the two side counts and the integer level.
/-- **The single-parked branch's window, with the level read as an integer.** Only `i₀` is parked,
in block four, every other coordinate exceeds `c₃`, and `Y - nδ ≤ (W + δ)(N - n)` at `N = m + m'`
and every integer level `n ≤ 4`.

`Gap212.datumD_band4_single_core` with the level read as an integer rather than eliminated
continuously — which is what carries the branch past `ω₀ = 13/2500`, where the continuous form
turns over at the cell `(5, 5)`. The per-side readings `(m - 1)c₃ + δ ≤ B_{1,m}` of
`Gap212.side_floor_le_cap_except` are still what caps both side counts at six and pins the pooled
mass to the exact cell maximum. The least slack is `6.10·10⁻³`, at the cell `(5, 5)` and
`n = 3`. -/
theorem datumD_band5_single_window {nn Y w : ℝ} {m m' n : ℕ} (hnn : nn = n) (hm : m ≤ 6)
    (hm' : m' ≤ 6) (hnK : n ≤ 4) (hnlt : n < m + m')
    (hs : ((m : ℝ) - 1) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 41 / 2500 ≤ gap212Cap m)
    (hs' : ((m' : ℝ) - 1) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 41 / 2500 ≤ gap212Cap m')
    (hn : nn * (41 / 2500) ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10))
    (hYlo : ((m : ℝ) + (m' : ℝ)) * (41 / 2500) ≤ Y)
    (hfar : (((m : ℝ) + (m' : ℝ)) - 1) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 41 / 2500 ≤ Y)
    (hYside : Y ≤ gap212Cap m + gap212Cap m')
    (hw0 : 13 / 2500 < w) (hw : w ≤ 541 / 100000) :
    Y - nn * (41 / 2500)
      ≤ ((1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 41 / 2500)
        * (((m : ℝ) + (m' : ℝ)) - nn) := by
  subst hnn
  interval_cases m <;> interval_cases m' <;> interval_cases n <;>
    norm_num [gap212Cap] at hYside hfar hYlo hs hs' hn ⊢ <;> linarith

set_option maxHeartbeats 1000000 in
-- One `linarith` per triple `(m, m', n)`: the two side counts and the integer level.
/-- **The high branch's window, with the level read as an integer.** Both small blocks are empty,
`c₄ = 8ω₀` is the floor, and `Y - n c₄ ≤ W (N - n)` at `N = m + m'` and every integer level
`n ≤ 1`.

This is the rung the fourth band ends on. `Gap212.datumD_band4_high_core` eliminates the level
continuously, which at the cell `(1, 3)` allows `n` up to `(Y - c̄₁)/c₄ ≈ 0.13` where the only
integer available is `0`, and that is exactly where it loses: with the integer reading the cell
closes up to `ω₀ = 271/50000 - ϵ/5`, against `0.0052849789…` without it. Above `ω₀ = 271/50000`
even the integer reading fails at `(1, 3)`, where `Y ≤ B_{1,1} + B_{1,3} = 1652/5000` and the bound
`Y/4` on the smallest coordinate meets the reserve `W` with equality, which is why the band stops
at `541/100000`. The least slack over the twenty-five pairs of side counts and the two levels is
`4.00·10⁻⁴`, at `(1, 3)` and `n = 0`. -/
theorem datumD_band5_high_window {nn Y w : ℝ} {m m' n : ℕ} (hnn : nn = n) (hm : m ≤ 5)
    (hm' : m' ≤ 5) (hnK : n ≤ 1) (hnlt : n < m + m')
    (hs : (m : ℝ) * (8 * w) ≤ gap212Cap m) (hs' : (m' : ℝ) * (8 * w) ≤ gap212Cap m')
    (hYf : ((m : ℝ) + (m' : ℝ)) * (8 * w) ≤ Y)
    (hYside : Y ≤ gap212Cap m + gap212Cap m')
    (hn : nn * (8 * w) ≤ Y - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10))
    (hw0 : 13 / 2500 < w) (hw : w ≤ 541 / 100000) :
    Y - nn * (8 * w)
      ≤ (1 / 2 - Y - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) * (((m : ℝ) + (m' : ℝ)) - nn) := by
  subst hnn
  interval_cases m <;> interval_cases m' <;> interval_cases n <;>
    norm_num [gap212Cap] at hYside hYf hs hs' hn ⊢ <;> linarith

/-- **The cap row's sixth rung bounds it below the seventh.** `B_{1,m} ≤ 983/5000` for `m ≤ 6`,
which is what pins the pooled mass of a cell whose two sides are capped at six factors. -/
theorem gap212Cap_le_six {m : ℕ} (hm : m ≤ 6) : gap212Cap m ≤ 983 / 5000 := by
  interval_cases m <;> norm_num [gap212Cap]

/-- **The cap row's fifth rung bounds it below the sixth.** `B_{1,m} ≤ 953/5000` for `m ≤ 5`, which
is what pins the pooled mass of the high branch's cell. -/
theorem gap212Cap_le_five {m : ℕ} (hm : m ≤ 5) : gap212Cap m ≤ 953 / 5000 := by
  interval_cases m <;> norm_num [gap212Cap]

set_option maxHeartbeats 1000000 in
-- The five branches of `Gap212.conditionD_at_datum_band_4`, with the three that bind reading the
-- level `n` as an integer instead of eliminating it continuously.
/-- **Condition D at `p_⋆` for every cell, every `γ`, and every level
`13/2500 < ω₀ ≤ 541/100000`.**

The same five branches as `Gap212.conditionD_at_datum_band_4` — the dichotomy is still run on
`c₄ = 8ω₀`, a pair sharing block four still frees block three for a third coordinate, and the
one-parked and high branches still read their floors one side at a time. What is new is the
*level*.

Each branch supplies `n + 1` coordinates at most `v = (Y - n δ)/(N - n)` and asks `v ≤ W + P`,
where `n = ⌊(Y - c₁)/δ⌋` is the level, `P` the parked mass and `W = 1/2 - Y - 2δ - 10ω₀ - 2ϵ` the
reserve. The requirement is increasing in `n`, and `Gap212.Packing.le_window_of_core` eliminates
`n` from it using only `n δ ≤ Y - c̄₁` — so it has to allow every *real* `n` up to `(Y - c̄₁)/δ`.
But `n` is a natural number, and at the three branches that bind the fractional part is exactly
what is lost:

* the high branch at the cell `(m, m') = (1, 3)`, where the rung has four coordinates,
  `Y - c̄₁ < c₄` forces `n = 0` and the true bound on the smallest coordinate is `Y/4`, while the
  continuous elimination allows `n` up to `(Y - c̄₁)/c₄ ≈ 0.13`. That is where
  `Gap212.conditionD_at_datum_band_4` ends, at `ω₀ = 0.0052849789…`;
* the split-pair branch at `N = 20`, where `(Y - c̄₁)/δ = 6.61` and the level is at most `6`;
* the one-parked branch at the cell `(5, 5)`, where `(Y - c̄₁)/δ = 4.22` and the level is at most
  `4`.

So `Gap212.datumD_band5_pair_window`, `datumD_band5_single_window` and `datumD_band5_high_window`
state the window requirement at an integer level and are verified level by level; the two branches
that never bind — `Gap212.datumD_band5_triple_core` and `datumD_band5_pairfloor_core`, with
`datumD_band5_pairfloor_reserve` — keep the continuous elimination.

**`541/100000` is where the integer reading stops, and the wall is again the cell `(1, 3)`.** There
`Y ≤ B_{1,1} + B_{1,3} = 1652/5000`, the level is `0`, and `Y/4 ≤ W` reads
`1652/5000 ≤ 4(1/2 - 1652/5000 - 2δ - 10ω₀ - 2ϵ)`, i.e. `ω₀ ≤ 271/50000 - ϵ/5 = 0.00542 - 2·10⁻¹¹`.
`541/100000` is the round numeral below that. The binding slacks on the band are `4.00·10⁻⁴` (high
branch, `(1, 3)`, level `0`), `1.72·10⁻³` (split pair, `N = 20`, level `6`), `1.25·10⁻³` (three
parked, `N = 20`), `1.46·10⁻³` (pair and floor, `N = 11`) and `6.10·10⁻³` (one parked, `(5, 5)`,
level `3`).

Above `271/50000` no reading of the level helps, because there is none left to read: the level is
already pinned to its only value. `Gap212.conditionD_at_datum_band_6` continues with a fourth
parked coordinate, selected by a dichotomy on pairs. -/
theorem conditionD_at_datum_band_5 (j j' : Fin gap212Params.n) {m m' : ℕ} :
    ConditionD (Xi (gap212Params.B j m) (gap212Params.B j' m') m m' gap212Params.δ)
      capD (chamberDBand (omegaMax gap212Params j j') (13 / 2500) (541 / 100000)) := by
  classical
  refine conditionD_band_of (by norm_num) (by norm_num) j j' fun γ w y hγ hγ' hw0 hw hy' hDle ↦ ?_
  have hc₂ : (0 : ℝ) ≤ 1 / 2 - γ - 2 * w - 1 / 10 ^ 10 := by linarith
  have hc₃ : (0 : ℝ) ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10 := by linarith
  have hc₄ : (0 : ℝ) ≤ 8 * w := by linarith
  have hYcap := total_le_datum hy'
  have hYaff := total_le_affine_datum hy'
  have hYaff₂ := total_le_affine_datum₂ hy'
  have hYaff₃ := total_le_affine_datum₃ hy'
  have hYaff₄ := total_le_affine_datum₄ hy'
  have hYaff₅ := total_le_affine_datum₅ hy'
  have hYaff₆ := total_le_affine_datum₆ hy'
  have hYlow := card_delta_le_total hy'
  have hδy : ∀ i, (41 / 2500 : ℝ) ≤ y i := fun i ↦ (hy'.1 i).1
  have hy0 : ∀ i, (0 : ℝ) ≤ y i := fun i ↦ le_trans (by norm_num) (hδy i)
  have hD0 : (0 : ℝ) ≤ (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10) := by linarith
  have hDbar : (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10)
      ≤ (∑ i, y i) - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) := by linarith
  have hcast : ((m + m' : ℕ) : ℝ) = m + m' := Nat.cast_add m m'
  have hN4 : 4 ≤ m + m' := by exact_mod_cast (show (3 : ℝ) < m + m' by linarith)
  have hN26 : m + m' ≤ 26 :=
    Nat.le_of_lt_succ (by exact_mod_cast (show (m : ℝ) + m' < 27 by linarith))
  have hN4' : (4 : ℝ) ≤ m + m' := by exact_mod_cast hN4
  by_cases hex : ∃ i, y i ≤ 8 * w
  · -- **Block four is in play.** Its capacity is the larger of the two small ones on this band.
    obtain ⟨i₀, hi₀⟩ := hex
    obtain ⟨n, hnle, hnlt⟩ :=
      Packing.exists_nat_mul_le_lt (d := (41 / 2500 : ℝ)) (by norm_num) hD0
    have hnN : (n : ℝ) < (m : ℝ) + (m' : ℝ) := by linarith
    have hnN' : n < m + m' := by exact_mod_cast hnN
    have hnK : n ≤ 6 := by
      by_contra hcon
      have h7 : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 7 ≤ n)
      linarith
    have hnδ : (n : ℝ) * (41 / 2500)
        ≤ (∑ i, y i) - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) := by linarith
    have hnsub : (0 : ℝ) < ((m : ℝ) + (m' : ℝ)) - (n : ℝ) := by linarith
    obtain ⟨v, hvmul, hdv, -, hSsum⟩ := exists_level_coords (by norm_num) hδy hnN'
    push_cast at hvmul
    have hStot : (∑ i, y i) - (γ - 2 * (41 / 2500 : ℝ) - 8 * w - 1 / 10 ^ 10)
        ≤ ∑ i ∈ univ.filter (fun i : Fin (m + m') ↦ y i ≤ v), y i := by linarith
    by_cases hex3 : ∃ j₀, j₀ ≠ i₀ ∧ y j₀ ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10
    · obtain ⟨j₀, hji, hj₀⟩ := hex3
      by_cases hAB : 8 * w < y i₀ + y j₀
      · -- **The split branch.** `i₀` in block four, `j₀` in block three; window `W + 8ω₀`.
        have hwin : v ≤ (1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10) + 8 * w := by
          refine le_of_mul_le_mul_right ?_ hnsub
          rw [hvmul]
          exact datumD_band5_pair_window hcast.symm rfl hN4 hN26 hnK hnN' hnδ hYlow hYcap
            hYaff hYaff₂ hYaff₃ hYaff₄ hYaff₅ hYaff₆ hw0 hw
        refine Packing.admitsPartition₄_of_blocks (T₃ := {j₀}) (T₄ := {i₀})
          (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (v := v)
          (Finset.disjoint_singleton.2 hji) (by simpa using hj₀) (by simpa using hi₀)
          (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hc₂ ?_ ?_
        · refine le_trans ?_ (Packing.sum_sdiff_ge hy0)
          rw [Finset.sum_union (Finset.disjoint_singleton.2 hji), Finset.sum_singleton,
            Finset.sum_singleton]
          linarith
        · rw [Finset.sum_singleton, Finset.sum_singleton]
          linarith
      · -- **The pair branch.** `i₀` and `j₀` both fit in block four; block three is free.
        push Not at hAB
        by_cases hex3b : ∃ k, k ≠ i₀ ∧ k ≠ j₀ ∧ y k ≤ 4 * w + 41 / 2500 - 1 / 10 ^ 10
        · -- a third coordinate goes into block three; window `W + 3δ`
          obtain ⟨k, hki, hkj, hk⟩ := hex3b
          have hwin : v ≤ (1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
              + 3 * (41 / 2500) := by
            refine le_of_mul_le_mul_right ?_ hnsub
            rw [hvmul]
            have hc := datumD_band5_triple_core hcast.symm hN4 hN26 hYlow hYcap hYaff hYaff₂
              hYaff₃ hYaff₄ hYaff₅ hYaff₆ hw0 hw
            exact Packing.le_window_of_core (cb := 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
              (by norm_num) (by linarith) (by linarith) (by linarith)
          have hTd : Disjoint ({k} : Finset (Fin (m + m'))) ({i₀, j₀} : Finset (Fin (m + m'))) := by
            simp [hki, hkj]
          have hpair : ∑ i ∈ ({i₀, j₀} : Finset (Fin (m + m'))), y i = y i₀ + y j₀ :=
            Finset.sum_pair (Ne.symm hji)
          refine Packing.admitsPartition₄_of_blocks (T₃ := {k}) (T₄ := {i₀, j₀})
            (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (v := v)
            hTd (by simpa using hk) (by rw [hpair]; linarith)
            (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hc₂ ?_ ?_
          · refine le_trans ?_ (Packing.sum_sdiff_ge hy0)
            rw [Finset.sum_union hTd, Finset.sum_singleton, hpair]
            linarith [hδy i₀, hδy j₀, hδy k]
          · rw [Finset.sum_singleton, hpair]
            linarith [hδy i₀, hδy j₀, hδy k]
        · -- every other coordinate exceeds `c₃`, which caps `N`; window `W + 2δ`
          push Not at hex3b
          have hpair : ∑ i ∈ ({i₀, j₀} : Finset (Fin (m + m'))), y i = y i₀ + y j₀ :=
            Finset.sum_pair (Ne.symm hji)
          have hfar : ((m : ℝ) + (m' : ℝ) - 2) * (4 * w + 41 / 2500 - 1 / 10 ^ 10)
              + 2 * (41 / 2500) ≤ ∑ i, y i := by
            have h := floor_off_le_sum (T := {i₀, j₀}) (f := 4 * w + 41 / 2500 - 1 / 10 ^ 10)
              fun i hi ↦ by
                simp only [mem_insert, mem_singleton, not_or] at hi
                exact (hex3b i hi.1 hi.2).le
            rw [card_pair (Ne.symm hji), Nat.cast_ofNat, hpair, hcast] at h
            linarith [hδy i₀, hδy j₀]
          have hwin : v ≤ (1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
              + 2 * (41 / 2500) := by
            refine le_of_mul_le_mul_right ?_ hnsub
            rw [hvmul]
            have hres := datumD_band5_pairfloor_reserve hcast.symm hN4 hN26 hYlow hYcap hYaff
              hYaff₂ hYaff₃ hYaff₄ hYaff₅ hYaff₆ hw0 hw hfar
            have hc := datumD_band5_pairfloor_core hcast.symm hN4 hN26 hYlow hYcap hYaff
              hYaff₂ hYaff₃ hYaff₄ hYaff₅ hYaff₆ hw0 hw hfar
            exact Packing.le_window_of_core (cb := 2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10)
              (by norm_num) (by linarith) (by linarith) (by linarith)
          refine Packing.admitsPartition₄_of_blocks (T₃ := ∅) (T₄ := {i₀, j₀})
            (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (v := v)
            (Finset.disjoint_empty_left _) (by simpa using hc₃) (by rw [hpair]; linarith)
            (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hc₂ ?_ ?_
          · refine le_trans ?_ (Packing.sum_sdiff_ge hy0)
            rw [Finset.empty_union, hpair]
            linarith [hδy i₀, hδy j₀]
          · rw [Finset.sum_empty, hpair]
            linarith [hδy i₀, hδy j₀]
    · -- **The single branch.** Every coordinate but `i₀` exceeds `c₃`; window `W + δ`.
      push Not at hex3
      have hfar : ((m : ℝ) + (m' : ℝ) - 1) * (4 * w + 41 / 2500 - 1 / 10 ^ 10) + 41 / 2500
          ≤ ∑ i, y i := by
        have h := floor_off_le_sum (T := {i₀}) (f := 4 * w + 41 / 2500 - 1 / 10 ^ 10) fun i hi ↦
          (hex3 i (notMem_singleton.1 hi)).le
        rw [card_singleton, Nat.cast_one, sum_singleton, hcast] at h
        linarith [hδy i₀]
      obtain ⟨hsd, hsd'⟩ := side_floor_le_cap_except hy' hδy (by linarith)
        (fun i hi ↦ (hex3 i hi).le)
      have hm6 : m ≤ 6 := side_le_six_except (by linarith) hsd
      have hm6' : m' ≤ 6 := side_le_six_except (by linarith) hsd'
      have hYside : ∑ i, y i ≤ gap212Cap m + gap212Cap m' := total_le hy'
      have hnK4 : n ≤ 4 := by
        by_contra hcon
        have h5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 5 ≤ n)
        linarith [gap212Cap_le_six hm6, gap212Cap_le_six hm6']
      have hwin : v ≤ (1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10)
          + 41 / 2500 := by
        refine le_of_mul_le_mul_right ?_ hnsub
        rw [hvmul]
        exact datumD_band5_single_window rfl hm6 hm6' hnK4 hnN' hsd hsd' hnδ hYlow hfar hYside
          hw0 hw
      refine Packing.admitsPartition₄_of_blocks (T₃ := ∅) (T₄ := {i₀})
        (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v)) (v := v)
        (Finset.disjoint_empty_left _) (by simpa using hc₃) (by simpa using hi₀)
        (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hc₂ ?_ ?_
      · refine le_trans ?_ (Packing.sum_sdiff_ge hy0)
        rw [Finset.empty_union, Finset.sum_singleton]
        linarith [hδy i₀]
      · rw [Finset.sum_empty, Finset.sum_singleton]
        linarith [hδy i₀]
  · -- **The high branch.** Every coordinate exceeds `c₄ = 8ω₀`, the larger small block.
    push Not at hex
    have hfy : ∀ i, (8 * w : ℝ) ≤ y i := fun i ↦ (hex i).le
    have hYf := mul_le_sum_of_card_le (S := univ) (k := m + m') hc₄ hfy (by simp)
    rw [hcast] at hYf
    obtain ⟨hside, hside'⟩ := side_floor_le_cap hy' hfy
    have hm5 : m ≤ 5 := side_le_five (by linarith) hside
    have hm5' : m' ≤ 5 := side_le_five (by linarith) hside'
    have hYside : ∑ i, y i ≤ gap212Cap m + gap212Cap m' := total_le hy'
    obtain ⟨n, hnle, hnlt⟩ :=
      Packing.exists_nat_mul_le_lt (d := (8 * w : ℝ)) (by linarith) hD0
    have hnK : n ≤ 1 := by
      by_contra hcon
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
      have h2' : (2 : ℝ) * (8 * w) ≤ (n : ℝ) * (8 * w) :=
        mul_le_mul_of_nonneg_right h2 (by linarith)
      linarith [gap212Cap_le_five hm5, gap212Cap_le_five hm5']
    have hn1 : (n : ℝ) ≤ 1 := by exact_mod_cast hnK
    have hnN : (n : ℝ) < (m : ℝ) + (m' : ℝ) := by linarith
    have hnN' : n < m + m' := by exact_mod_cast hnN
    have hnδ : (n : ℝ) * (8 * w)
        ≤ (∑ i, y i) - (2 / 5 - 2 * (41 / 2500) - 8 * w - 2 / 10 ^ 10) := by linarith
    have hnsub : (0 : ℝ) < ((m : ℝ) + (m' : ℝ)) - (n : ℝ) := by linarith
    obtain ⟨v, hvmul, hdv, -, hSsum⟩ := exists_level_coords hc₄ hfy hnN'
    push_cast at hvmul
    have hwin : v ≤ 1 / 2 - (∑ i, y i) - 2 * (41 / 2500) - 10 * w - 2 / 10 ^ 10 := by
      refine le_of_mul_le_mul_right ?_ hnsub
      rw [hvmul]
      exact datumD_band5_high_window rfl hm5 hm5' hnK hnN' hside hside' hYf hYside hnδ hw0 hw
    refine admitsPartition₄_of_partition₂ ?_ hc₃ hc₄
    exact Packing.admitsPartition₂_of_small_block (v := v)
      (S := univ.filter (fun i : Fin (m + m') ↦ y i ≤ v))
      (fun i hi ↦ (Finset.mem_filter.mp hi).2) (by linarith) hD0 (by linarith) (by linarith)

end Gap212
