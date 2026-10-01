[![](logo.svg)](https://axiommath.ai/)

# Bounded gaps between primes (H₁ ≤ 212)

This is a Lean formalization of the bound `H₁ ≤ 212` on gaps between consecutive primes, conditional
on the numerical certificate `Gap212.Gap212Certificate` and on cited analytic estimates.

## Main Results

* Beyond every bound there are two primes `p < q` with `q ≤ p + 212`, assuming the five
  equidistribution estimates, the Harman reduction, bilinear Bombieri–Vinogradov and the
  numerical certificate `Gap212.Gap212Certificate`.
* Under the same hypotheses, `p_{n+1} ≤ p_n + 212` for arbitrarily large `n`.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4) and on Axiom Math's
repository [PrimeGapsLib](https://github.com/AxiomMath/PrimeGapsLib).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results claimed above
is located at [Gap212Challenge/Basic.lean](Gap212Challenge/Basic.lean). This file only depends on
the dependencies above. It contains formal statements of [§Main Results](#main-results) with
`sorry` as proof.

This repository can be verified against the formal challenge with the Lean comparator on a Linux
machine. First, follow the instructions in https://github.com/leanprover/comparator to install
`comparator`. Then, run the following command:

```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.
