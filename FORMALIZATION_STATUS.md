# Formalization status

## Scope and current boundary

**INCOMPLETE.** The full arbitrary-rank minimal nonvanishing theorem, infinite
nonvanishing, Newton classification, Laurent Mathieu property, and compact-torus
Mathieu property are not proved. This is an audited foundation checkpoint of the
mandatory direct scalar route, not a completed paper formalization.

The mathematical source remains the unmodified manuscript at
`e4da66e13a47ae533222075487feae1eee6a22c8`. Lean uses `leanprover/lean4:v4.34.0`
and mathlib `5ed2965256430c3649e86755f9576b54eca72435`, matching the neighboring
compact-Lie-group development. There is no dependency on that development.

The first unresolved geometric inputs are recorded as **unproved propositions**
`RadiusTailObligation` and `SpherePathObligation` in
`DuistermaatVanDerKallen/SemialgebraicObligations.lean`. They are not axioms,
instances, or proved coverage. See [the precise boundary report](FORMALIZATION_BLOCKERS.md).

Status conventions:

- **PROVED component**: the specified constituent statement has a checked proof.
- **PARTIAL**: some components are proved; the manuscript result is not covered.
- **CONDITIONAL**: a checked implication with explicitly unproved mathematical premises.
- **OPEN**: no completed proof of this obligation.
- **OPTIONAL / EXCLUDED**: not required by the main-route target.

All Lean names below are in `DuistermaatVanDerKallen` unless qualified further.

## Main manuscript result ledger

| Manuscript obligation | Lean correspondence | Status | Proof / unresolved dependencies |
|---|---|---|---|
| `thm:main`: arbitrary-rank infinite nonvanishing | `InfiniteNonvanishing` in `Targets`; `infinite_of_minimal_and_newton_powers` | CONDITIONAL | Same power argument; requires `MinimalNonvanishing` and `OriginInNewtonPowers`. Neither is proved. |
| `thm:minimal`: arbitrary-rank minimal nonvanishing | `MinimalNonvanishing`; `minimal_nonvanishing_rank_zero` | PARTIAL | Only rank zero is unconditional. All positive ranks and the analytic contradiction remain open. |
| `lem:face`: minimal-face reduction | `support_pow_lower_bound` in `Laurent` is related support infrastructure only | OPEN | Exposed face, coefficient identity including cancellation, rational subspace lattice basis, rank reduction and relative interior. |
| `lem:powers`: Newton polytope of powers | `OriginInNewtonPowers` is an unproved weaker target proposition | OPEN | Neither full homogeneity nor even this origin-preservation consequence is proved. |
| `lem:chart`: unimodular vertex chart | `constantTerm_pow_reindex` | PARTIAL | Arbitrary lattice automorphisms preserve all power constant terms. Existence of the cone basis, negative vertex coordinates, and polynomial factorization remain open. |
| `std:sa`: semialgebraic standard input | `PolynomialTail`; `SemialgebraicObligations` | PARTIAL | Detailed component inventory below. No Hardt/projection input is assumed as a project axiom. |
| `std:stokes`: integration and Stokes | None | OPEN | Chain integration, subdivision, reparametrization, finite measure, Stokes, and homology pairing. |
| `def:density`: absolute restricted complex-form density | None | OPEN | Definition, independence of stratification, density identities, finite-chain multiplicities. |
| `lem:projection`: uniform finite-multiplicity integration | None | OPEN | Uniform component count; smooth rank decomposition; dimension bounds; change of variables / area formula. |
| `rem:uniform-parameters`: retain all family parameters | Scope of the two specialized obligations | OPEN | No uniform geometric theorem has been proved. Constants in `finite_of_common_radius` are explicitly uniform hypotheses. |
| `cor:bounded-volume`: uniform bounded-family volume | None | OPEN | Projection estimates and real-coordinate wedge bounds. |
| `lem:connecting-paths`: uniform compact-family connecting paths | `SpherePathObligation` | OPEN | Even the restricted sphere-family version, with no semialgebraic requirement on the path, is unproved. Hardt + compact triangulation + uniform arc volume remain dependencies. |
| `rem:connecting-paths-background`: Teissier/KOS comparison | None | BACKGROUND ONLY | Not used as a replacement input. |
| `thm:sublevel`: uniform middle-dimensional sublevel bound | None | OPEN | Full restricted complex density, derivative lemma, uniform coefficient induction. |
| `lem:derivative`: one-derivative estimate | None | OPEN | Parameter-retaining projection estimate and complex-to-real wedge inequality. |
| Unlabeled sublevel remark: zero density on components in `P=0` | None | OPEN | Consequence of sublevel theorem; not a Euclidean-volume assertion. |
| `thm:log-integrability`: logarithmic integrability and power bound | None | OPEN | Newton cube support bound, normalized dyadic family, sublevel theorem, countable additivity including boundaries. |
| Proper affine-torus geometry, `eq:closed-embedding`–`eq:proper-radius` | `AffineTorus`; `TorusDifferential` | PROVED component | Closed image, chart homeomorphism, smoothness on the open torus, actual chart derivative, tangent image and linearized constraint characterization, proper L2 radius and compact sublevels. A separate abstract manifold instance is not needed for these statements. |
| Restricted differential and `eq:embedding-metric`, `eq:lambda-formula` | `torusTangentMap_norm_sq`, `restricted_fderiv_norm_sq`, `polynomial_restricted_norm` | PROVED component | Exact induced metric and restricted operator norm, via tangent Riesz representative. Polynomial coordinate partials are analytically identified as `P_zᵢ − wᵢ² P_wᵢ`. `LaurentEvaluation` constructs representatives for every `MultiLaurent` and proves agreement with its finite coefficient-sum evaluation. |
| Explicit lift, `eq:gradient-lift`–`eq:gradient-identities` | `NormalizedGradient`; `polynomialVectorField_derivative`; `polynomialVectorField_embedded_norm` | PROVED component | Actual tangent lift, right inverse, unsquared norm, minimality, surjectivity, real/complex norm agreement. Both identities hold for the original Laurent evaluation through `LaurentGeometry`; no ambient differential norm is substituted. |
| `lem:scalar-finiteness`: finiteness of `K₀` | `ordinaryCriticalValues` definition | OPEN | Semialgebraic critical-locus decomposition and constancy on smooth connected pieces. |
| `lem:scalar-finiteness`: finiteness of `K∞` | `CommonRadius`; `RadiusTailObligation`; `SpherePathObligation` | CONDITIONAL | Full abstract common-radius finiteness is proved from uniform image diameters and radius tails. Derivation of those inputs for Laurent polynomials remains open. |
| Compactness of `eq:small-gradient-sphere` | `smallGradientSphere_isCompact`, `ambientDifferentialNorm_continuous` | PROVED component | Exact family on ambient L2 spheres, all real parameters. This proves neither path length nor component bounds. |
| `eq:small-gradient-diameter` | Explicit hypothesis of `finite_of_common_radius` | OPEN | Rectifiable chain rule and integration of restricted derivative along the controlled paths. |
| `eq:common-radius-set`: existence of a common large radius | `PolynomialSignFormula.contains_tail_of_unbounded`; `common_radius_contradiction` | PARTIAL | Boolean-polynomial univariate tails and finite intersection of tails proved. Existential radius-set projection remains open. |
| `prop:generalized-critical`: finite union of ordinary/asymptotic values | None | OPEN | Requires both parts of scalar finiteness. |
| `lem:uniform-gradient`: uniform differential lower bound | `uniform_gradient_lower_bound`, `affineTorus_uniform_gradient`, `laurent_uniform_gradient` | PROVED | Manuscript proper-radius argument, specialized to every algebraic Laurent polynomial with the actual restricted differential norm. The compact base excludes the explicitly defined ordinary/asymptotic critical-value sets. This lemma requires no finiteness assertion about those sets. |
| ODE standard inputs before `lem:complete-segment` | `PolynomialGradient`; `ODEContinuation`; `LaurentPicard` | PARTIAL | Joint field smoothness, local existence, uniqueness, uniform existence time on compact subsets, extension past finite endpoints, and existence from a priori compact control are proved for autonomous fields. A regular Picard branch is analytic on an open parameter neighborhood of zero time scale, jointly in velocity and initial point, and its integral equation produces actual scaled ODE trajectories. Identification with chosen transport, smooth dependence along complete segments, and the time-dependent ODE package remain open. |
| `lem:complete-segment`: complete segment transport | `laurent_complete_segment`, `laurent_segment_unique`, `laurent_segment_reverse_inverse` in `LaurentTransport` | PARTIAL | Complete existence on an open interval containing `[0,1]`, exact base motion, uniqueness, and reversal identity are proved for every Laurent polynomial and every initial torus point under precisely segment exclusion from the ordinary/asymptotic critical values. Compact control is proved, not assumed. `fiberTransportHomeomorph` gives the fiber homeomorphism; `fiberCurves_continuous` gives joint continuity in initial point and time for fixed velocity; `fiberSweep_isCompact` gives compact sweeps. Smoothness of the fiber maps and dependence on varying velocity remain open. |
| `prop:bifurcation`: piecewise C¹ transport, local smooth triviality, local system | `FiberTransport`; `FiberContinuity` | PARTIAL | Fixed straight segments have actual fiber homeomorphisms. Arbitrary piecewise C¹ paths, smooth dependence including base-velocity parameters, local smooth trivializations, and the fiber homology local system remain open. |
| `rem:asymptotic-example`: `c+x+(y−1)²/(xy)` | None | OPEN | Example retained in the unchanged manuscript; derivative, limits, Newton interior and regular-value computation not formalized. |
| `rem:transport-background`: smooth transport distinct from semialgebraic sweep | Module architecture and boundary documentation | DESIGN CONSTRAINT | No assertion that the normalized-gradient flow is semialgebraic. No background alternative is imported. |
| Relative form preceding `lem:holomorphy` | None | OPEN | Well-defined quotient form, independence, holomorphicity and fiberwise closedness. |
| `lem:holomorphy`: holomorphic transported periods | None | OPEN | Compact-cycle triangle sweep, Stokes, homology pairing, continuity, Morera, analytic continuation. |
| Endpoint Hardt application `eq:hardt` and `eq:sweep-boundary` | None | OPEN | Separate normalized Hardt trivialization, semialgebraic cycle representatives, local-system agreement, oriented finite sweep and compact truncations. |
| `prop:primitive`: quantitative endpoint primitive | None | OPEN | Log-integrability, finite multiplicities, limiting absolute integrals, local compact Stokes and difference-quotient error. |
| `cor:no-pole`: exclude forced simple pole | None | OPEN | Dyadic primitive estimate and the nonzero `A log 2` integral. |
| `lem:residue`: residue-cycle identity | None | OPEN | Zero-free polydisc, Rouché, simple roots, compact covering cycles, orientation, residue sign/normalization, locally smooth class. |
| `cor:classification`: Newton classification | `positive_powers_vanish_of_origin_not_mem`, `classification_of_minimal` | PARTIAL / CONDITIONAL | Exclusion implies all positive powers vanish, unconditionally. Converse requires minimal nonvanishing. |
| `cor:mathieu`: Laurent Mathieu property | `eventual_constantTerm_zero_of_newton`, `mathieu_of_minimal` | CONDITIONAL | Full separated-support conclusion proved for all ranks and all multipliers. Vanishing-moments premise reaches it only assuming minimal nonvanishing. |
| `cor:torus`: finite Fourier sums on compact tori | None | OPEN | Haar/constant-term correspondence and Laurent Mathieu. No dependence on the neighboring repository is imported. |
| Unlabeled compact-torus remark: finite Fourier sums = continuous K-finite functions | None | OPEN | Averaged inner product, simultaneous diagonalization and character lattice identification. |
| `std:whitney`: complex algebraic Whitney stratification/first isotopy | None | OPTIONAL / EXCLUDED | Appendix only; not a main-route dependency. |
| `prop:bifurcation-whitney`: alternate finite exceptional set | None | OPTIONAL / EXCLUDED | No projective graph, Whitney or Thom proof introduced. |
| Two unlabeled appendix remarks: complex algebraic strata; local compact-cycle alternative | None | OPTIONAL / EXCLUDED | No formal coverage claimed. |

## Standard-input and internal proof inventory

| Obligation | Status / exact boundary |
|---|---|
| Arbitrary-real-coefficient semialgebraic descriptions | OPEN: no general representation/decomposition package developed. |
| Coordinate projection / Tarski–Seidenberg | OPEN: even the exact specialized `RadiusTailObligation` is unproved. |
| Univariate Boolean polynomial tail property | PROVED component: `polynomial_nonneg_eventuallyConstant`, `PolynomialSignFormula.eventuallyConstant`, `PolynomialSignFormula.contains_tail_of_unbounded`; uses polynomial leading-term asymptotics. |
| Finite union of points/intervals on the whole real line | OPEN: tail property does not prove this stronger global decomposition. |
| Nash stratification compatible with a finite collection | OPEN. |
| Uniform connected-component counts | OPEN, including the specific sphere family. |
| Hardt triviality | OPEN. Required separately for path families and endpoint sweep. |
| Compact semialgebraic triangulation, finite one-skeleton paths | OPEN. |
| Semialgebraic cycle representatives of compact homology classes | OPEN. |
| Stratification-independent integration and subdivision | OPEN. |
| Bounded semialgebraic Hausdorff volume | OPEN; does not follow from topological compactness. |
| Stokes on compact semialgebraic chains | OPEN. Mathlib's box divergence theorem is not this statement. |
| Agreement with singular-homology integration pairing | OPEN; availability of singular homology alone does not provide the pairing. |
| Restricted density scalar law, triangle inequality, cancellation example | OPEN. |
| Projection estimate positive-dimensional exceptional fibers and null preimages | OPEN. |
| Sublevel coefficient lower bound and normalized derivative induction | OPEN. |
| Dyadic Newton support growth and lattice geometric series | OPEN. |
| Ordinary critical-locus constancy and finite image | OPEN. |
| Finite metric separation, uniform pigeonhole step and common tail intersection | PROVED components in `CommonRadius`. |
| Proper-radius contradiction for uniform gradient bound | PROVED abstract component, including bounded subsequence versus escape. |
| Scalar weighted lift and actual tangent norm | PROVED components in `ScalarLift`, `TorusDifferential`, `NormalizedGradient`; differentiability and true polynomial partials established separately in `PolynomialCalculus`. |
| Polynomial vector field joint real smoothness and local ODE existence | PROVED components in `PolynomialGradient`; no global continuation is inferred. |
| `MultiLaurent` evaluation as an ambient polynomial restriction | PROVED: `laurentRepresentative_eval`, `laurentEval_eq_polynomial_restriction`; `laurentEvalHom` also proves product/power compatibility on the open torus. |
| Restricted-versus-ambient and inverse-metric regression checks | PROVED: `torusPartial_constraint_eval` and `restrictedDifferential_unit_rank_one`. |
| Radius Gronwall estimate on an existing trajectory | PROVED component: `trajectory_radius_bound`, specialized to actual Laurent integral curves by `laurent_integral_curve_radius_bound`. |
| Compact sublevel ∩ compact-base inverse image, positive differential lower bound | PROVED component: `compact_regular_controlled_region`; `laurentControlledRegion_isCompact` and `laurentControlledRegion_regular` transfer this to the actual coordinate ODE domain. |
| Exact straight-segment base equation | PROVED component: `laurent_integral_curve_base` on every connected open time interval carrying an integral curve. |
| Reverse-path inverse and smooth local segment trivialization | PARTIAL: `fiberTransportEquiv` and `fiberTransportHomeomorph` construct actual inverse fiber maps. Smoothness and local trivializations remain open. |
| Uniform Lipschitz dependence in initial points at bounded proper radius | PROVED: `fiberCurves_lipschitz_initial`, via a common compact regular region and Gronwall. Velocity is fixed. |
| Joint continuity in initial point and time | PROVED: `fiberCurves_continuous`, on the initial fiber times `[0,1]`. |
| Compact sweep of a compact initial subset | PROVED: `fiberSweep_isCompact`, `fiberSweep_subset_regular`; the whole image is compact and contained in the regular torus domain. No smooth or semialgebraic parametrization is claimed. |
| Smooth superposition of the actual vector field on compact curve spaces | PROVED: `curveVectorField_apply`, `laurentCurveVectorField_contDiffAt`; Banach-algebra inversion at nowhere-zero curves, polynomial evaluation, and real-linear conjugation preserve the exact induced-metric formula. This is field smoothness on curve space, not solution smoothness. |
| Bounded primitive on the fixed unit interval | PROVED: `curvePrimitiveCLM`, `curvePrimitiveCLM_norm_le`, `curvePrimitive_hasDerivAt`; norm at most one and the fundamental theorem of calculus, using a continuous clamped extension. |
| Implicit Picard branch at zero time scale | PROVED: `picardResidual_partial_zero` gives the identity partial derivative; `exists_smooth_picard_branch` applies the smooth implicit-function theorem without assuming invertibility of a later-time linearization. |
| Local Laurent Picard branch with velocity and initial-point parameters | PROVED component: `laurent_exists_analytic_picard_neighborhood` gives an open neighborhood of zero time scale with an analytic map into the Banach space of regular curves satisfying the actual integral equation; it includes nearby nonzero time scales. `laurent_picard_equation_solves_ode` constructs scaled ODE trajectories agreeing with these curves on `[0,1]`, including endpoint derivatives. Identification with `fiberCurve` and complete-segment smooth dependence remain open. |
| Identity transport for a stationary segment | PROVED regression: `fiberTransport_zero`. |
| Uniform local time on a compact subset of the regular domain | PROVED: `uniform_ode_time_on_compact`, retaining the range bound from the local Picard construction. |
| Compact-domain continuation | PROVED: `ode_extend_right_of_compact` and `ode_exists_past_of_compact_control`; autonomous Banach-space statements with explicit domain and compact-control hypotheses. |
| Complete Laurent segment existence | PROVED component: `laurent_complete_segment` derives its own compact control and constructs an open solution interval containing `[0,1]`. |
| Stationary base-segment regression | PROVED: `laurent_zero_velocity_curve`; the zero-velocity field has a constant solution. |
| Homology local system and analytic continuation without monodromy invariance | OPEN. |
| Endpoint representative/ODE class comparison | OPEN. |
| Endpoint error term by continuity from above on compact truncations | OPEN. |
| Residue geometric-series convergence and character coefficient extraction | OPEN. |
| Analytic continuation of the rational period to the small positive interval | OPEN. |
| Exponent support estimates, strict separation and eventual multiplier vanishing | PROVED components in `Laurent`; adapted proof provenance below. |

## Proof substitutions and provenance

1. `Laurent.lean` adapts the support/separation proofs from
   `long-mathematics/mathieu-property-compact-connected-lie-groups`,
   `MathieuProperty/LaurentSupport.lean`, inspected at repository HEAD
   `12cc27d6958e10b5ad4b14007588bac6a74fff79`. Namespace and imports were adjusted.
   It uses only mathlib and proves the same separating-functional argument as the
   manuscript; it does not import the neighboring project's missing DvK premise.
2. The univariate tail proof uses leading-coefficient asymptotics for polynomial
   inequalities and induction on Boolean formulas. It is a proved special case
   of the manuscript standard input; it does not replace projection or Hardt.
3. `uniform_gradient_lower_bound` abstracts the manuscript subsequence proof to
   a space with compact radius sublevels. `affineTorus_uniform_gradient` supplies
   the paper's geometry. `TorusDifferential` and `PolynomialCalculus` now provide
   the coordinate/differential identification for polynomial restrictions.
4. `trajectory_radius_bound` specializes mathlib Gronwall to the exact linear
   growth estimate, including zero velocity. This is a fully proved substitution
   for the manuscript integrating-factor calculation on an existing trajectory.
5. The scalar norm formula is proved by constructing the tangent Riesz vector
   and using its operator norm. This proves the same weighted Cauchy–Schwarz
   identity and minimality as the manuscript. The tangent model is the image of
   the derivative of the global torus chart, also characterized by the
   linearized defining equations; it is not the full ambient space.
6. Polynomial representatives are handled by polynomial induction and the
   analytic chain rule. Local ODE existence specializes mathlib to the actual
   smooth field. Neither step assumes a semialgebraic flow or global existence.
7. `LaurentEvaluation` replaces each signed coordinate power with a power of
   its corresponding ambient coordinate. Equality with the original finite
   Laurent sum is proved term by term. The representative is not claimed to
   preserve products off the torus; evaluation on the open torus is an algebra
   homomorphism. `LaurentGeometry` then specializes the previously proved
   analytic results without additional smoothness assumptions.
8. `ODEContinuation` proves the required autonomous compact-domain continuation
   using mathlib Picard–Lindelöf (local construction adapted from
   `Analysis/ODE/ExistUnique.lean` and `PicardLindelof.lean`; see
   `THIRD_PARTY_NOTICES.md`): retain the closed-ball range bound, obtain a
   uniform local time by a finite compact subcover, glue solutions by uniqueness,
   and use the supremum of reachable times. `LaurentTransport` proves the
   needed compact control for every partial Laurent curve from its base equation
   and the proper-radius Gronwall bound. This implements the manuscript
   continuation argument without assuming a maximal flow or completeness.
   Smooth parameter dependence is not inferred from these existence results.
9. `FiberTransport` chooses complete trajectories and uses uniqueness and
   reversal to construct inverse maps on fibers. `FiberContinuity` places each
   family with bounded initial proper radius in one compact regular region,
   obtains a Lipschitz constant there, and applies Gronwall to prove continuous
   dependence and compactness of sweeps. This proves the topological components
   of transport; smooth dependence, especially in velocity, is still open.
10. `CurveField` lifts the same explicit rational normalized-gradient formula to
    Banach algebras of continuous curves. `CurveIntegral` supplies a bounded
    primitive on `[0,1]`. `PicardImplicit` implements smooth local dependence
    through the equation `u - constant(z) - δ K(V_a(u)) = 0`: at `δ = 0` the
    partial derivative in `u` is the identity. `LaurentPicard` specializes this
    to the actual Laurent field, keeps the nearby curves in the regular domain,
    and recovers ODE trajectories from the integral equation. This is an
    implementation of the manuscript's ODE standard input, not a change of
    transport route. In this mathlib version `⊤ : WithTop ℕ∞` is the analytic
    order, so the implicit branch is analytic on one open neighborhood of
    parameters, including nonzero small time scales. Identification with chosen
    complete transports and propagation along full segments remain unproved.
11. No mathematical manuscript corrections or changes were made. No alternate
   Bertini–Sard, Puiseux, resolution, or Whitney–Thom route was introduced.

## Validation and restart

The root module imports every mathematical module. `scripts/audit_sources.py`
checks forbidden proof mechanisms and umbrella reachability.
`scripts/AxiomAudit.lean` inspects all declarations by **defining module**, including
private/generated ones, permitting only `propext`, `Classical.choice`, and
`Quot.sound`. `scripts/CheckTargets.lean` displays exact open target propositions;
its successful execution proves no instance of those propositions.

`scripts/audit_coverage.py` checks that all labeled result environments are
represented in this ledger. This is a bookkeeping check; semantic statement
alignment is documented above and is not inferred from a passing script.

The checkpoint has 24 mathematical module files plus the root umbrella and
2 Lean verification helpers. See `scripts/validation.txt` for exact theorem
counts, the full build job count, and environment-level axiom/declaration counts. CI runs the same checks in a clean GitHub checkout.

The general-torus DvK dependency in the compact-Lie-group project is **not closed**.
Resume at the two explicit geometric obligations and the boundary report.
