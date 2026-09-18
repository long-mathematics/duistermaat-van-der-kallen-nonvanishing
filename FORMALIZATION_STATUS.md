# Formalization status

## Current status

Lean formalization has not yet started.

The checked-in manuscript is a research draft for adversarial mathematical audit. No manuscript theorem is currently claimed formally verified in this repository.

## Primary target

Formalize the full arbitrary-rank resolution-free Duistermaat--van der Kallen nonvanishing theorem.

The intended proof architecture is the manuscript's resolution-free route. In particular, a resolution-of-singularities replacement is outside the current target unless explicitly approved.

## Manuscript results to cover

| Result | Status | Notes |
|---|---|---|
| Theorem 1.1: Duistermaat--van der Kallen infinite nonvanishing | NOT STARTED | Main headline theorem; derived from minimal nonvanishing by applying it to powers. |
| Theorem 1.2: minimal nonvanishing | NOT STARTED | Principal analytic theorem. |
| Lemma 2.1: minimal-face reduction | NOT STARTED | Newton-polytope reduction. |
| Lemma 2.2: powers of Newton polytopes | NOT STARTED | Algebraic/convex-geometric input. |
| Lemma 2.3: unimodular vertex chart | NOT STARTED | Lattice/monomial-coordinate reduction. |
| Semialgebraic integration/projection package | NOT STARTED | Includes the standard inputs and uniform finite-multiplicity integration. |
| Middle-dimensional polynomial sublevel estimate | NOT STARTED | Principal new estimate. |
| Logarithmic-volume integrability | NOT STARTED | Dyadic global consequence of the sublevel estimate. |
| Finite exceptional values / fiber transport | NOT STARTED | Uses the stated Whitney/Thom inputs in the manuscript. |
| Holomorphic transported period | NOT STARTED | Fiber-period continuation. |
| Quantitative endpoint primitive | NOT STARTED | Endpoint estimate excluding the forced simple pole. |
| Residue cycles near a vertex | NOT STARTED | Local DvK residue construction. |
| Newton-polytope classification | NOT STARTED | Corollary of minimal nonvanishing plus separation. |
| Laurent-polynomial Mathieu property | NOT STARTED | Corollary of the classification. |
| Compact-torus Mathieu property | NOT STARTED | Fourier/Laurent translation of the preceding corollary. |

This is an initial ledger, not a claim that the listed rows are the final optimal Lean decomposition. Refine it as the formalization exposes the actual dependency graph, while preserving correspondence with every manuscript proof-bearing obligation.

## Validation

No Lean package or CI workflow has been initialized yet.
