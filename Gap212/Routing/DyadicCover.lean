/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Defs
public meta import Gap212.Attr

/-!
# Every modulus sits at the bottom of its own dyadic block

The Type IIc route is run per dyadic block, because its three windows depend on the block's level.
For that to cover anything, every modulus in range has to lie in *some* block at a level the route
admits — and the cheapest way to see that is to let the modulus pick its own block, taking the
level for which it sits exactly at the lower endpoint.

That level is `ω₀ = (log_x q - 1/2)/2`, and the whole content is that `x^{1/2 + 2ω₀} = q`: the
exponent was chosen to make the identity hold, so membership is immediate and the level's range
follows from the two size bounds by one application of `Real.rpow_le_rpow_left_iff`.

What the route needs is `ω₀ ∈ [-ε₁, ω]`; what comes out is `[-ε₁/2, ω]`, which is stronger, because
the level is *half* the excess of the logarithmic size over `1/2`. The count of blocks needed —
`O(log x)` — is not stated here: nothing downstream uses it, since the Type IIc bound is applied
with `A` increased by one and absorbs any polylogarithmic multiplicity.

## Main results

* `Gap212.Routing.exists_level_mem_dyadicBlock`: every modulus above the retreated half-level lies
  in a block whose level is admissible.
-/

@[expose] public section

namespace Gap212.Routing

open Real Gap212.Defs

/-- **Every modulus in range sits at the bottom of a block at an admissible level.** For
`x^{1/2 - ε₁} < q ≤ x^{1/2 + 2ω}` the level `ω₀ = (log_x q - 1/2)/2` lies in `[-ε₁/2, ω]` and `q`
is in the dyadic block at that level.

The identity `x^{1/2 + 2ω₀} = q` is what makes this work, so `q` sits exactly at the block's lower
endpoint and the upper constraint `q < 2 x^{1/2 + 2ω₀}` is `q < 2q`. -/
@[gap212 "lem_dyadic_block_cover"]
theorem exists_level_mem_dyadicBlock {x ε₁ ω : ℝ} {q : ℕ} (hx : 1 < x) (hq : 0 < q)
    (hlow : x ^ (1 / 2 - ε₁) < (q : ℝ)) (hhigh : (q : ℝ) ≤ x ^ (1 / 2 + 2 * ω)) :
    ∃ ω₀ ∈ Set.Icc (-ε₁ / 2) ω, q ∈ dyadicBlock x ω₀ := by
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hxne : x ≠ 1 := ne_of_gt hx
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- The level is chosen so that `x ^ (1/2 + 2ω₀) = q` on the nose.
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hid : x ^ (Real.log q / Real.log x) = (q : ℝ) := by
    have hcancel : Real.log x * (Real.log q / Real.log x) = Real.log q := by
      field_simp
    rw [Real.rpow_def_of_pos hx0, hcancel]
    exact Real.exp_log hqpos
  have halg : (1 : ℝ) / 2 + 2 * ((Real.log q / Real.log x - 1 / 2) / 2)
      = Real.log q / Real.log x := by ring
  rw [← hid] at hlow hhigh
  have hlow' : 1 / 2 - ε₁ < Real.log q / Real.log x := (Real.rpow_lt_rpow_left_iff hx).mp hlow
  have hhigh' : Real.log q / Real.log x ≤ 1 / 2 + 2 * ω := (Real.rpow_le_rpow_left_iff hx).mp hhigh
  refine ⟨(Real.log q / Real.log x - 1 / 2) / 2, ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · rw [halg, hid]
  · rw [halg, hid]; linarith

end Gap212.Routing
