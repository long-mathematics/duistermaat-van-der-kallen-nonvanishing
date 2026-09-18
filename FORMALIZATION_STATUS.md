# Formalization status

## Current status

Lean formalization has not yet started.

The checked-in manuscript is a research draft for adversarial mathematical audit. No manuscript theorem is currently claimed formally verified in this repository.

Before the Lean project is initialized, the manuscript's global transport architecture was revised so that the main proof uses generalized critical values and a complete horizontal ODE on the closed affine torus. The earlier Whitney--Thom proof is retained as an appendix alternative and is not on the main dependency path.

## Primary target

Formalize the full arbitrary-rank resolution-free Duistermaat--van der Kallen nonvanishing theorem.

The intended proof architecture is the manuscript's main generalized-critical-value / ODE route. In particular, a resolution-of-singularities replacement is outside the current target unless explicitly approved.

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
| Proper affine-torus embedding and Rabier function | NOT STARTED | Main transport geometry; the induced proper radius detects both infinity and coordinate collapse. |
| Finiteness of ordinary/asymptotic generalized critical values | NOT STARTED | Uses semialgebraic Łojasiewicz control at infinity, radial path-length bounds, and Hardt control of the radius map. |
| Complete ODE transport | NOT STARTED | Minimal-norm right inverse plus the uniform Malgrange bound and Gronwall continuation. |
| Holomorphic transported period | NOT STARTED | ODE local trivialization plus compact-cycle triangle sweep and Morera. |
| Hardt endpoint representatives and sweep | NOT STARTED | Semialgebraic sweep on a final interval `(0,b]`; remains in the main proof. |
| Quantitative endpoint primitive | NOT STARTED | Endpoint estimate excluding the forced simple pole. |
| Residue cycles near a vertex | NOT STARTED | Local DvK residue construction. |
| Newton-polytope classification | NOT STARTED | Corollary of minimal nonvanishing plus separation. |
| Laurent-polynomial Mathieu property | NOT STARTED | Corollary of the classification. |
| Compact-torus Mathieu property | NOT STARTED | Fourier/Laurent translation of the preceding corollary. |
| Whitney--Thom appendix alternative | NOT STARTED | Alternate transport proof only; not required for the main theorem/formalization unless explicitly included in scope. |

This is an initial ledger, not a claim that the listed rows are the final optimal Lean decomposition. Refine it as the formalization exposes the actual dependency graph, while preserving correspondence with every manuscript proof-bearing obligation.

## Validation

No Lean package or CI workflow has been initialized yet.
