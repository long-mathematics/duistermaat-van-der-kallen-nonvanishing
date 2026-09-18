# A Resolution-Free Proof of the Duistermaat--van der Kallen Nonvanishing Theorem

## Abstract

We present a resolution-free semialgebraic proof of the following theorem of Duistermaat and van der Kallen: if the Newton polytope of a nonzero complex Laurent polynomial contains the origin, then infinitely many of its positive powers have nonzero constant term. The principal estimate is a uniform middle-dimensional sublevel bound for the restriction of a holomorphic volume form to a semialgebraic family. Polynomial differentiation and a finite-multiplicity projection estimate prove this bound; a dyadic decomposition then gives absolute integrability of the logarithmic volume form on every middle-dimensional semialgebraic chain on which the Laurent polynomial is bounded. The local residue construction of Duistermaat and van der Kallen identifies the constant-term generating function with a fiber period. Our estimate gives a primitive with a power-law endpoint bound, contradicting the simple pole forced by vanishing of all positive constant terms. Infinite nonvanishing follows by applying this minimal nonvanishing statement to powers of the polynomial. The standard semialgebraic inputs are stated explicitly. Global cycle transport is obtained by an explicit generalized-critical-value ODE rather than Whitney--Thom theory; the latter is retained as an alternative in an appendix.

## Preprint and source

- [Preprint PDF](duistermaat_van_der_kallen_nonvanishing.pdf)
- [LaTeX source](duistermaat_van_der_kallen_nonvanishing.tex)

This repository is the canonical development location for the research draft and its Lean formalization. The manuscript is currently a research draft for adversarial mathematical audit and is not yet formally verified.

## Proof architecture

The main global transport argument identifies $(\mathbb C^\times)^d$ with the closed smooth affine variety
`{(z,w) : z_j w_j = 1}` in $\mathbb C^{2d}$, so the induced Euclidean radius is proper and detects both $|x_j|\to\infty$ and $|x_j|\to0$. Ordinary and asymptotic generalized critical values give a finite exceptional set. Away from that set, the minimal-norm right inverse of the differential defines a horizontal ODE with at most linear growth; Gronwall gives complete path lifting and hence transport of the residue cycle and holomorphic continuation of its period.

Hardt triviality is retained for semialgebraic control, in particular for the final real sweep near zero. The earlier projective-graph / complex Whitney-stratification / Thom-isotopy argument is preserved in an appendix as an independent alternate transport proof; it is not a dependency of the main proof.

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

A fresh formalization should target the manuscript's generalized-critical-value / ODE transport route. In particular, the proper affine-torus metric must count $x_j\to0$ as escape. The Whitney--Thom appendix is an alternate proof and is not a required formalization dependency unless explicitly brought into scope.

Standard semialgebraic inputs used by the manuscript must not be inserted as project axioms: use existing mathlib results where available, prove the needed statements, or record the exact missing infrastructure and formalization boundary.

See [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the coverage ledger.

## Author

Christopher D. Long

Email: galizur@gmail.com
