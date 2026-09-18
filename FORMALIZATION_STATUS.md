# Formalization status

## Current status

Lean formalization has not yet started.

The checked-in manuscript is a research draft for adversarial mathematical audit. No manuscript theorem is currently claimed formally verified in this repository.

Before Lean initialization, the global transport architecture was finalized so that the main proof uses the **direct scalar common-radius / normalized-gradient route**. The earlier Whitney--Thom proof is retained as an appendix alternative and is not on the main dependency path.

## Primary target

Formalize the full arbitrary-rank resolution-free Duistermaat--van der Kallen nonvanishing theorem.

The intended proof architecture is the manuscript's main direct scalar route. In particular, a resolution-of-singularities replacement is outside the current target unless explicitly approved.

## Manuscript results to cover

| Result | Status | Notes |
|---|---|---|
| Theorem 1.1: Duistermaat--van der Kallen infinite nonvanishing | NOT STARTED | Main headline theorem; derived from minimal nonvanishing by applying it to powers. |
| Theorem 1.2: minimal nonvanishing | NOT STARTED | Principal analytic theorem. |
| Lemma 2.1: minimal-face reduction | NOT STARTED | Newton-polytope reduction. |
| Lemma 2.2: powers of Newton polytopes | NOT STARTED | Algebraic/convex-geometric input. |
| Lemma 2.3: unimodular vertex chart | NOT STARTED | Lattice/monomial-coordinate reduction. |
| Semialgebraic integration/projection package | NOT STARTED | Includes decomposition, Hardt, compact triangulation, integration/Stokes, and uniform finite-multiplicity integration. |
| Uniform compact-family connecting paths | NOT STARTED | Derived in the manuscript from Hardt, compact triangulation, and the uniform one-dimensional volume bound. |
| Middle-dimensional polynomial sublevel estimate | NOT STARTED | Principal new estimate. |
| Logarithmic-volume integrability | NOT STARTED | Dyadic global consequence of the sublevel estimate. |
| Proper affine-torus embedding and restricted differential norm | NOT STARTED | Uses `z ↦ (z,z⁻¹)`; the proper radius detects both infinity and coordinate collapse. |
| Finiteness of ordinary critical values | NOT STARTED | Finite semialgebraic decomposition of the critical locus; the scalar map is constant on each connected smooth piece. |
| Direct finiteness of asymptotic critical values | NOT STARTED | Common-radius component-count argument on the fixed family `A_{R,ε}`; no generalized Bertini--Sard or asymptotic power-rate theorem is a main dependency. |
| Uniform differential lower bound | NOT STARTED | Compact-base contradiction using `K₀ ∪ K∞`. |
| Explicit scalar normalized-gradient lift | NOT STARTED | Coordinate formula for the minimal-norm lift in the induced Hermitian metric. |
| Complete ODE transport | NOT STARTED | Linear-growth/Gronwall radius bound plus a positive lower bound on the differential on the controlled compact region. |
| Smooth local trivialization | NOT STARTED | Parameter-dependent segment flows on a disk of good values. |
| Holomorphic transported period | NOT STARTED | Smooth local trivialization plus compact-cycle triangle sweep and Morera. |
| Hardt endpoint representatives and sweep | NOT STARTED | Separate semialgebraic sweep on a final interval `(0,b]`; distinct from smooth ODE class transport. |
| Quantitative endpoint primitive | NOT STARTED | Endpoint estimate excluding the forced simple pole. |
| Residue cycles near a vertex | NOT STARTED | Local DvK residue construction. |
| Newton-polytope classification | NOT STARTED | Corollary of minimal nonvanishing plus separation. |
| Laurent-polynomial Mathieu property | NOT STARTED | Corollary of the classification. |
| Compact-torus Mathieu property | NOT STARTED | Fourier/Laurent translation of the preceding corollary. |
| Whitney--Thom appendix alternative | NOT STARTED | Alternate transport proof only; not required for the main theorem/formalization unless explicitly included in scope. |

This is an initial ledger, not a claim that the listed rows are the final optimal Lean decomposition. Refine it as the formalization exposes the actual dependency graph, while preserving correspondence with every manuscript proof-bearing obligation.

## Validation

No Lean package or CI workflow has been initialized yet.
