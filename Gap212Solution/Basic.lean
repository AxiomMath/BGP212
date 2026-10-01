/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Gap212.Challenge.ObligationPairing

/-! # Satisfying the formal challenge -/

@[expose] public section

namespace Gap212.Challenge

/-- **`thm_main` — the main theorem.** Given the five equidistribution estimates, the two external
citations and the numerical certificate, beyond every bound there are two primes `p < q` with
`q ≤ p + 212`. -/
theorem thm_main
    (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath) (h₃ : TypeIBakerIrving)
    (h₄ : TypeIStadlmann) (h₅ : TypeIIIPolymath) (hharman : Gap212HarmanReduction)
    (hbv : BilinearBombieriVinogradov) (hcert : Gap212Certificate) :
    ∀ n₀ : ℕ, ∃ p q : ℕ, n₀ ≤ p ∧ p < q ∧ p.Prime ∧ q.Prime ∧ q ≤ p + 212 :=
  primeGapLE_212_of_challenge_hypotheses h₁ h₂ h₃ h₄ h₅ hharman hbv hcert

/-- **`thm_nth` — the `nth`-prime form.** The same hypotheses give `p_{n+1} - p_n ≤ 212` for
arbitrarily large `n`. -/
theorem thm_nth
    (h₁ : TypeIIPolymath) (h₂ : TypeIbPolymath) (h₃ : TypeIBakerIrving)
    (h₄ : TypeIStadlmann) (h₅ : TypeIIIPolymath) (hharman : Gap212HarmanReduction)
    (hbv : BilinearBombieriVinogradov) (hcert : Gap212Certificate) :
    ∀ n₀ : ℕ, ∃ n ≥ n₀, (n + 1).nth Nat.Prime ≤ n.nth Nat.Prime + 212 :=
  nthPrimeGapLE_212_of_challenge_hypotheses h₁ h₂ h₃ h₄ h₅ hharman hbv hcert

end Gap212.Challenge
