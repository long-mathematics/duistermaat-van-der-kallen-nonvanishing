# A Resolution-Free Proof of the Duistermaat--van der Kallen Nonvanishing Theorem

## Abstract

We present a resolution-free semialgebraic proof of the following theorem of Duistermaat and van der Kallen: if the Newton polytope of a nonzero complex Laurent polynomial contains the origin, then infinitely many of its positive powers have nonzero constant term. The principal estimate is a uniform middle-dimensional sublevel bound for the restriction of a holomorphic volume form to a semialgebraic family. Polynomial differentiation and a finite-multiplicity projection estimate prove this bound; a dyadic decomposition then gives absolute integrability of the logarithmic volume form on every middle-dimensional semialgebraic chain on which the Laurent polynomial is bounded. The local residue construction of Duistermaat and van der Kallen identifies the constant-term generating function with a fiber period. Our estimate gives a primitive with a power-law endpoint bound, contradicting the simple pole forced by vanishing of all positive constant terms. Infinite nonvanishing follows by applying this minimal nonvanishing statement to powers of the polynomial. The standard semialgebraic and stratified-topological inputs are stated explicitly.

## Preprint and source

- [Preprint PDF](duistermaat_van_der_kallen_nonvanishing.pdf)
- [LaTeX source](duistermaat_van_der_kallen_nonvanishing.tex)

This repository is the canonical development location for the research draft and its Lean formalization. The manuscript is currently a research draft for adversarial mathematical audit and is not yet formally verified.

## Main results targeted for formalization

The primary target is the full arbitrary-rank, resolution-free Duistermaat--van der Kallen nonvanishing theorem:

> If the Newton polytope of a nonzero complex Laurent polynomial contains the origin, then infinitely many positive powers have nonzero constant term.

The manuscript derives from the minimal nonvanishing theorem:

- infinite nonvanishing;
- the Newton-polytope classification of universal constant-term vanishing;
- the Laurent-polynomial Mathieu property;
- the compact-torus Mathieu property for finite Fourier sums.

The formalization is intended to be independent of the compact-Lie-group development in [`long-mathematics/mathieu-property-compact-connected-lie-groups`](https://github.com/long-mathematics/mathieu-property-compact-connected-lie-groups). Once complete and audited, the resulting DvK theorem can be adapted there through a thin interface to close the deferred torus direction.

## Lean formalization

Formalization has not yet started. No Lean theorem is currently claimed proved in this repository.

The development should target the manuscript's resolution-free proof, not a resolution-of-singularities substitute. Standard inputs used by the manuscript must not be inserted as project axioms: use existing mathlib results where available, prove the needed statements, or record the exact missing infrastructure and formalization boundary.

See [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the coverage ledger.

## Author

Christopher D. Long

Email: galizur@gmail.com
