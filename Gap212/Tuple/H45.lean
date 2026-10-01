/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Tuple.H50
public meta import Gap212.Attr

/-!
# An admissible 45-tuple of diameter 212

The main theorems are stated at the bound `212`, and the bound a sieve argument delivers is the
diameter of the admissible tuple it runs on. The certificate is taken at
`Certificate gap212Params 44 0 0`, so `k = 45`, and what is needed is therefore an admissible
`45`-tuple of diameter exactly `212`. The entries below meet both requirements exactly.

Each of the three facts is a finite check, so `decide` settles it; admissibility in particular
needs no closure lemma about subsets or translations. Only primes `p ≤ 45` can matter: a prime
`p > 45` has more residue classes than the tuple has elements, so some class is omitted for free.
-/

@[expose] public section

namespace Gap212

open Finset

/-- A normalized admissible `45`-tuple of diameter `212`: the tuple of the main theorems. -/
@[gap212 "def_h45"]
def H45 : Finset ℕ :=
  {0, 2, 12, 14, 24, 26, 30, 36, 44, 50, 54, 56, 60, 66, 72, 74, 80, 84, 92, 96,
   102, 110, 114, 116, 122, 126, 134, 140, 144, 150, 156, 162, 164, 170, 176, 180,
   182, 186, 192, 194, 200, 204, 206, 210, 212}

/-- `H45` has `45` elements. -/
theorem card_H45 : #H45 = 45 := by
  set_option maxRecDepth 4000 in decide

/-- The diameter of `H45` is `212`. -/
@[gap212 "lem_h45_diameter"]
theorem diameter_H45 : H45.diameter = 212 := by
  set_option maxRecDepth 4000 in decide

/-- `H45` is admissible. -/
@[gap212 "lem_tuple"]
theorem admissible_H45 : H45.Admissible := by
  set_option maxRecDepth 8000 in decide

end Gap212
