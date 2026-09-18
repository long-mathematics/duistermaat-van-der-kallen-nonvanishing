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
instances, or proved coverage. `RadiusProjection` now reduces the radius-tail
input to the explicitly unproved `SemialgebraicProjectionObligation`, using a
proved polynomial incidence description. `SphereC1ChainObligation` separately
states the finite-C¹-piece path input used in the checked diameter estimate;
it is not inferred from the weaker rectifiable-path obligation. See [the precise boundary report](FORMALIZATION_BLOCKERS.md).

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
| `thm:main`: arbitrary-rank infinite nonvanishing | `InfiniteNonvanishing` in `Targets`; `infinite_of_minimal` in `NewtonPowers` | CONDITIONAL | The manuscript power argument now requires only `MinimalNonvanishing`, which remains unproved. The Newton-power premise is discharged by `origin_in_newton_powers`. The older two-premise implication remains available. |
| `thm:minimal`: arbitrary-rank minimal nonvanishing | `MinimalNonvanishing`; `minimal_nonvanishing_rank_zero` | PARTIAL | Rank zero is unconditional. `minimal_iff_interior_minimal` and `minimal_iff_vertex_minimal` identify the full target with its positive-rank full-interior and vertex-chart forms. The analytic theorem in either form remains open. |
| `lem:face`: minimal-face reduction | `face_reduction` in `FaceReduction` | PROVED | Every origin-containing Newton polytope reduces to a polynomial in `r ≤ d` variables with all power constant terms preserved, including `n = 0`. The reduced polynomial is either a nonzero constant in rank zero or has the origin in its full interior in positive rank. Successive supporting cuts replace the one-step minimal-face choice; an integer basis of the saturated lattice supplies coordinates. |
| `lem:powers`: Newton polytope of powers | `newtonPolytope_pow`; `origin_in_newton_powers` in `NewtonPowers` | PROVED | Full equality `Newt(f^n) = n • Newt(f)` in arbitrary finite rank for every `n ≥ 1`. Support containment proves one inclusion; uniquely exposed support vertices survive with coefficient `a_v^n`, and finite convex-hull recovery proves the other. The result also handles the zero polynomial. |
| `lem:chart`: unimodular vertex chart | `unimodular_vertex_chart`; `unimodular_vertex_chart_evaluation` | PROVED | In every positive rank, an integral linear automorphism gives `f = y^(-m) u`, every `m_i > 0`, and an ordinary polynomial with nonzero value at zero. Exact algebraic factorization, pointwise evaluation on the open torus, Newton interior, and all power constant terms are preserved. Integer separating weights and shears replace the primitive-vector choice and basis-extension step. |
| `std:sa`: semialgebraic standard input | `PolynomialTail`; `SemialgebraicSets`; `ComplexSemialgebraic`; `SemialgebraicObligations` | PARTIAL | Detailed component inventory below. No Hardt/projection input is assumed as a project axiom. |
| `std:stokes`: integration and Stokes | None | OPEN | Chain integration, subdivision, reparametrization, finite measure, Stokes, and homology pairing. |
| `def:density`: absolute restricted complex-form density | None | OPEN | Definition, independence of stratification, density identities, finite-chain multiplicities. |
| `lem:projection`: uniform finite-multiplicity integration | None | OPEN | Uniform component count; smooth rank decomposition; dimension bounds; change of variables / area formula. |
| `rem:uniform-parameters`: retain all family parameters | Scope of the two specialized obligations | OPEN | No uniform geometric theorem has been proved. Constants in `finite_of_common_radius` are explicitly uniform hypotheses. |
| `cor:bounded-volume`: uniform bounded-family volume | None | OPEN | Projection estimates and real-coordinate wedge bounds. |
| `lem:connecting-paths`: uniform compact-family connecting paths | `SpherePathObligation`; `SphereC1ChainObligation` | OPEN | Both the earlier rectifiable-path version and the finite-C¹-piece version needed by the checked integration estimate are unproved. No equivalence between these formulations is claimed. Hardt + compact triangulation + uniform arc volume, including the needed regular parametrizations, remain dependencies. |
| `rem:connecting-paths-background`: Teissier/KOS comparison | None | BACKGROUND ONLY | Not used as a replacement input. |
| `thm:sublevel`: uniform middle-dimensional sublevel bound | None | OPEN | Full restricted complex density, derivative lemma, uniform coefficient induction. |
| `lem:derivative`: one-derivative estimate | None | OPEN | Parameter-retaining projection estimate and complex-to-real wedge inequality. |
| Unlabeled sublevel remark: zero density on components in `P=0` | None | OPEN | Consequence of sublevel theorem; not a Euclidean-volume assertion. |
| `thm:log-integrability`: logarithmic integrability and power bound | None | OPEN | Newton cube support bound, normalized dyadic family, sublevel theorem, countable additivity including boundaries. |
| Proper affine-torus geometry, `eq:closed-embedding`–`eq:proper-radius` | `AffineTorus`; `TorusDifferential` | PROVED component | Closed image, chart homeomorphism, smoothness on the open torus, actual chart derivative, tangent image and linearized constraint characterization, proper L2 radius and compact sublevels. A separate abstract manifold instance is not needed for these statements. |
| Restricted differential and `eq:embedding-metric`, `eq:lambda-formula` | `torusTangentMap_norm_sq`, `restricted_fderiv_norm_sq`, `polynomial_restricted_norm` | PROVED component | Exact induced metric and restricted operator norm, via tangent Riesz representative. Polynomial coordinate partials are analytically identified as `P_zᵢ − wᵢ² P_wᵢ`. `LaurentEvaluation` constructs representatives for every `MultiLaurent` and proves agreement with its finite coefficient-sum evaluation. |
| Explicit lift, `eq:gradient-lift`–`eq:gradient-identities` | `NormalizedGradient`; `polynomialVectorField_derivative`; `polynomialVectorField_embedded_norm` | PROVED component | Actual tangent lift, right inverse, unsquared norm, minimality, surjectivity, real/complex norm agreement. Both identities hold for the original Laurent evaluation through `LaurentGeometry`; no ambient differential norm is substituted. |
| `lem:scalar-finiteness`: finiteness of `K₀` | `ordinaryCriticalValues_subset_dummy_asymptotic`; `laurent_finite_ordinary_of_projection_and_paths` in `CriticalFiniteness` | CONDITIONAL | The unconditional dummy-coordinate inclusion reduces ordinary finiteness in rank d to asymptotic finiteness in rank d+1. It requires the same unproved projection and uniform finite-C¹-chain inputs, with no separate critical-locus decomposition premise. This is a documented proof substitution. |
| `lem:scalar-finiteness`: finiteness of `K∞` | `finite_asymptoticCriticalValues_of_radius_and_paths`; `laurent_finite_asymptotic_of_projection_and_paths` in `ScalarFinitenessReduction` | CONDITIONAL | Finiteness of the actual Laurent asymptotic critical-value set follows from `SemialgebraicProjectionObligation` and `SphereC1ChainObligation`, both explicitly unproved. Asymptotic-sequence approximation, common-radius choice, normalization, path integration, and finite-label contradiction are checked. The weaker earlier `SpherePathObligation` alone is not used to infer the needed C¹ pieces. |
| Compact semialgebraic family `eq:small-gradient-sphere` | `smallGradientSphere_isCompact`; `ambientDifferentialNorm_continuous`; `isSemialgebraic_smallGradientTotalFamily` | PROVED component | Compactness holds for all real parameters. Semialgebraicity holds for the single total family with radius and threshold as free coordinates on their manuscript range. It uses the full ambient L2 norm and actual restricted differential expression. This proves neither path length nor component bounds. |
| `eq:small-gradient-diameter` | `smallGradient_curve_derivative_norm_le`; `smallGradient_curve_image_integral_bound`; `C1ArcChain.smallGradient_image_dist_le` | PARTIAL | Tangency, the actual restricted derivative bound, and the integrated estimate are proved for C¹ arcs and finite chains, giving image distance at most ε times the summed speed integrals. Uniform existence of such chains remains open. No general rectifiable-chain rule or equality with metric variation has been proved. |
| `eq:common-radius-set`: existence of a common large radius | `IsSemialgebraic.contains_tail_of_unbounded`; `isSemialgebraic_radiusIncidence`; `radiusApproximationSet_iff_projection`; `radiusTail_of_semialgebraic_projection`; `common_radius_contradiction` | PARTIAL / CONDITIONAL | The exact incidence set is semialgebraic and its coordinate projection equals the actual radius set. The full radius-tail input follows from the explicitly unproved real coordinate-projection obligation. Boolean-polynomial univariate tails and finite intersection of tails are proved; existential elimination remains open. |
| `prop:generalized-critical`: finite union of ordinary/asymptotic values | `laurent_finite_critical_union_of_projection_and_paths`; `laurentGoodValues_finite_compl_of_projection_and_paths` | CONDITIONAL | The actual union and complement of the actual good-value locus are finite under the same explicitly unproved projection and uniform finite-C¹-chain inputs. No unconditional finiteness is claimed. |
| `lem:uniform-gradient`: uniform differential lower bound | `uniform_gradient_lower_bound`, `affineTorus_uniform_gradient`, `laurent_uniform_gradient` | PROVED | Manuscript proper-radius argument, specialized to every algebraic Laurent polynomial with the actual restricted differential norm. The compact base excludes the explicitly defined ordinary/asymptotic critical-value sets. This lemma requires no finiteness assertion about those sets. |
| ODE standard inputs before `lem:complete-segment` | `ODEContinuation`; `AnalyticTransport`; `DrivenPicard`; `DrivenLocalODE`; `DrivenContinuation`; `DrivenAnalytic`; `DrivenContinuity` | PROVED components | Autonomous transport has complete analytic dependence. For the actual time-dependent scalar family, a Picard branch permits an arbitrary continuous velocity curve as a Banach parameter; anchored integration and time rescaling give two-sided local solutions and uniform existence time on compact time/position sets. Spatial Lipschitz control, uniqueness, gluing, and continuation from compact regular-domain control are proved. Local analytic endpoint maps are identified by uniqueness, and analytic initial-point dependence propagates along every existing complete driven trajectory. The velocity need only be continuous on the closed time interval. Joint driven initial-point/time continuity is also proved using the continuous local endpoint maps and uniqueness. These results cover the scalar field used here; no general smooth-dependence theorem for arbitrary nonautonomous vector fields is claimed. |
| `lem:complete-segment`: complete segment transport | `complete_segment_transport`, `fiberTransportDiffeomorph`; existence on a larger interval in `laurent_complete_segment` | PROVED | Under precisely segment exclusion from ordinary/asymptotic critical values: complete normalized-gradient trajectories, exact base motion, and the actual time-one map as an analytic real-manifold diffeomorphism. Every compact initial subset has compact sweep inside the regular torus, covering the compact-cycle support assertion without assuming a cycle integration package. The regular-fiber manifold instances are constructed from the actual differential, not postulated. |
| `prop:bifurcation`: piecewise C¹ transport, local smooth triviality, local system | `FiberDiffeomorph`; `LocalTrivialization`; `DrivenTransport`; `C1FiberTransport`; `PiecewiseTransport`; `C1Sweeps`; `LocalTransportHomotopy`; `TransportHomology`; `HomologyTransitions`; `HomologySheaf`; `HomologyLift`; `ChainHomologyHomotopy` | PARTIAL | Regular fibers, straight-segment diffeomorphisms, and local smooth triviality are proved. `laurent_complete_C1_path` now proves complete horizontal lifts with exact base motion for any C¹ path on `[0,1]`, requiring only continuous velocity there and one-sided base derivatives at the endpoints. Compact control is derived, not assumed. `LaurentC1Path.transportDiffeomorph` supplies the actual complete endpoint map and reversed-path inverse as an analytic real-manifold diffeomorphism. `LaurentC1Path.ofInterval` rescales compact time pieces, and `LaurentC1Chain.transportDiffeomorph` composes finite endpoint-matching chains. A chain is an explicit presentation by C¹ pieces; no global derivative at its corners is asserted. Joint continuous sweeps of compact initial sets are compact in the regular domain, also for finite chains. Actual integral singular-homology isomorphisms and their composition are proved in every degree, with constancy in any local product coordinate when the pieces stay in one convex good neighborhood. The homology coordinates have constant transitions on convex overlaps and glue to an actual sheaf of integral modules over the entire good-value locus. Its module stalks are linearly identified with actual fiber homology, germ maps on every convex patch are linear isomorphisms, and its underlying étalé space is a covering. The actual ODE homology class is a continuous lift in the module-stalk covering along every C¹ path; its endpoints are the original class and the actual ODE image. Finite C¹ chains agree with covering monodromy along their concatenated base paths, and arbitrary continuous fixed-endpoint homotopies in the good locus preserve their homology maps. This closes the global transport/local-system compatibility component. Critical-value finiteness, and hence the finite-exceptional-set dependency of the full proposition, is now conditional on the unproved projection and uniform finite-C¹-chain inputs. |
| `rem:asymptotic-example`: `c+x+(y−1)²/(xy)` | None | OPEN | Example retained in the unchanged manuscript; derivative, limits, Newton interior and regular-value computation not formalized. |
| `rem:transport-background`: smooth transport distinct from semialgebraic sweep | Module architecture and boundary documentation | DESIGN CONSTRAINT | No assertion that the normalized-gradient flow is semialgebraic. No background alternative is imported. |
| Relative form preceding `lem:holomorphy` | None | OPEN | Well-defined quotient form, independence, holomorphicity and fiberwise closedness. |
| `lem:holomorphy`: holomorphic transported periods | None | OPEN | Compact-cycle triangle sweep, Stokes, homology pairing, continuity, Morera, analytic continuation. |
| Endpoint Hardt application `eq:hardt` and `eq:sweep-boundary` | None | OPEN | Separate normalized Hardt trivialization, semialgebraic cycle representatives, local-system agreement, oriented finite sweep and compact truncations. |
| `prop:primitive`: quantitative endpoint primitive | None | OPEN | Log-integrability, finite multiplicities, limiting absolute integrals, local compact Stokes and difference-quotient error. |
| `cor:no-pole`: exclude forced simple pole | None | OPEN | Dyadic primitive estimate and the nonzero `A log 2` integral. |
| `lem:residue`: residue-cycle identity | `ResiduePolydisc`; `ResidueRootLocus`; `ResidueCovering`; `ResidueCoveringDegree`; `ResidueSemialgebraic`; `ResidueRootBranches`; `CoefficientSeries`; `TorusCauchySeries` | PARTIAL | The zero-free polydisc, strict derivative estimates, boundary exclusion for large fiber values, compact root locus in the actual Laurent fiber, and the surjective covering projection with exactly `m₁` points in every fiber are proved. The root locus is nonempty. Every root has a locally unique complex-smooth branch in the fiber value and remaining coordinates. The scalar generating series converges and equals the normalized Haar Cauchy integral. The coordinate image and total parameter family are semialgebraic, proved by explicit real polynomial descriptions. Oriented cycles, integration comparison, residue sign/normalization, and the locally smooth homology class remain open. |
| `cor:classification`: Newton classification | `positive_powers_vanish_of_origin_not_mem`, `classification_of_minimal` | PARTIAL / CONDITIONAL | Exclusion implies all positive powers vanish, unconditionally. Converse requires minimal nonvanishing. |
| `cor:mathieu`: Laurent Mathieu property | `eventual_constantTerm_zero_of_newton`, `mathieu_of_minimal` | CONDITIONAL | Full separated-support conclusion proved for all ranks and all multipliers. Vanishing-moments premise reaches it only assuming minimal nonvanishing. |
| `cor:torus`: finite Fourier sums on compact tori | `torus_mathieu_of_minimal` in `TorusMathieu` | CONDITIONAL | The normalized product-Haar/constant-term correspondence is proved on `(ℝ/ℤ)^d`, with actual Haar and probability-measure instances. Finite Fourier sums are exactly finite integer-character sums. The complete Mathieu implication now requires only the still-unproved `MinimalNonvanishing`. No dependence on the neighboring repository is imported. |
| Unlabeled compact-torus remark: finite Fourier sums = continuous K-finite functions | None | OPEN | Averaged inner product, simultaneous diagonalization and character lattice identification. |
| `std:whitney`: complex algebraic Whitney stratification/first isotopy | None | OPTIONAL / EXCLUDED | Appendix only; not a main-route dependency. |
| `prop:bifurcation-whitney`: alternate finite exceptional set | None | OPTIONAL / EXCLUDED | No projective graph, Whitney or Thom proof introduced. |
| Two unlabeled appendix remarks: complex algebraic strata; local compact-cycle alternative | None | OPTIONAL / EXCLUDED | No formal coverage claimed. |

## Standard-input and internal proof inventory

| Obligation | Status / exact boundary |
|---|---|
| Arbitrary-real-coefficient semialgebraic descriptions | PROVED component: `IsSemialgebraic` defines finite Boolean combinations of polynomial inequalities. Finite Boolean closure and real/complex polynomial preimages are proved. `polynomial_real_parts` supplies explicit real polynomials for complex evaluations; `complexCoordinatesHomeomorph` identifies coordinate spaces. Projection and decomposition remain OPEN. |
| Coordinate projection / Tarski–Seidenberg | OPEN: `SemialgebraicProjectionObligation` explicitly states this input. `radiusTail_of_semialgebraic_projection` derives the exact specialized `RadiusTailObligation` from it using proved incidence semialgebraicity, exact projection identification, and the univariate tail theorem. Neither obligation is proved. |
| Univariate Boolean polynomial tail property | PROVED component: `polynomial_nonneg_eventuallyConstant`, `PolynomialSignFormula.eventuallyConstant`, `PolynomialSignFormula.contains_tail_of_unbounded`; `IsSemialgebraic.eventuallyConstant_polynomial_curve`; `IsSemialgebraic.contains_tail_of_unbounded`. Uses polynomial leading-term asymptotics; the set-based definition is now linked directly to them. |
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
| Ordinary critical-locus constancy and finite image | PROVED components: exact zero-partial characterization, semialgebraicity, and constancy along C¹ arcs and finite chains in `CriticalLocus`. Finite image is CONDITIONAL via the dummy-coordinate reduction, using the same two geometric inputs as asymptotic finiteness. No finite decomposition theorem is assumed. |
| Finite metric separation, uniform pigeonhole step and common tail intersection | PROVED components in `CommonRadius`. |
| Proper-radius contradiction for uniform gradient bound | PROVED abstract component, including bounded subsequence versus escape. |
| Scalar weighted lift and actual tangent norm | PROVED components in `ScalarLift`, `TorusDifferential`, `NormalizedGradient`; differentiability and true polynomial partials established separately in `PolynomialCalculus`. |
| Polynomial vector field joint real smoothness and local ODE existence | PROVED components in `PolynomialGradient`; no global continuation is inferred. |
| `MultiLaurent` evaluation as an ambient polynomial restriction | PROVED: `laurentRepresentative_eval`, `laurentEval_eq_polynomial_restriction`; `laurentEvalHom` also proves product/power compatibility on the open torus. |
| Restricted-versus-ambient and inverse-metric regression checks | PROVED: `torusPartial_constraint_eval` and `restrictedDifferential_unit_rank_one`. |
| Radius Gronwall estimate on an existing trajectory | PROVED component: `trajectory_radius_bound`, specialized to actual Laurent integral curves by `laurent_integral_curve_radius_bound`. |
| Compact sublevel ∩ compact-base inverse image, positive differential lower bound | PROVED component: `compact_regular_controlled_region`; `laurentControlledRegion_isCompact` and `laurentControlledRegion_regular` transfer this to the actual coordinate ODE domain. |
| Exact straight-segment base equation | PROVED component: `laurent_integral_curve_base` on every connected open time interval carrying an integral curve. |
| Reverse-path inverse and smooth local segment trivialization | PROVED: `fiberTransportDiffeomorph` gives the fiber map, `convexTransportDiffeomorph` gives the product diffeomorphism over each convex open good base, and `laurent_local_trivialization_at` supplies such neighborhoods at all good values. Both directions use the same normalized-gradient segment curves. |
| Uniform Lipschitz dependence in initial points at bounded proper radius | PROVED: `fiberCurves_lipschitz_initial`, via a common compact regular region and Gronwall. Velocity is fixed. |
| Joint continuity in initial point and time | PROVED: `fiberCurves_continuous`, on the initial fiber times `[0,1]`. |
| Compact sweep of a compact initial subset | PROVED: `fiberSweep_isCompact`, `fiberSweep_subset_regular`; the whole image is compact and contained in the regular torus domain. No smooth or semialgebraic parametrization is claimed. |
| Smooth superposition of the actual vector field on compact curve spaces | PROVED: `curveVectorField_apply`, `laurentCurveVectorField_contDiffAt`; Banach-algebra inversion at nowhere-zero curves, polynomial evaluation, and real-linear conjugation preserve the exact induced-metric formula. This is field smoothness on curve space, not solution smoothness. |
| Bounded primitive on the fixed unit interval | PROVED: `curvePrimitiveCLM`, `curvePrimitiveCLM_norm_le`, `curvePrimitive_hasDerivAt`; norm at most one and the fundamental theorem of calculus, using a continuous clamped extension. |
| Implicit Picard branch at zero time scale | PROVED: `picardResidual_partial_zero` gives the identity partial derivative; `exists_smooth_picard_branch` applies the smooth implicit-function theorem without assuming invertibility of a later-time linearization. |
| Local Laurent Picard branch with velocity and initial-point parameters | PROVED component: `laurent_exists_analytic_picard_neighborhood` gives an open neighborhood of zero time scale with an analytic map into the Banach space of regular curves satisfying the actual integral equation; it includes nearby nonzero time scales. `laurent_picard_equation_solves_ode` constructs scaled ODE trajectories agreeing with these curves on `[0,1]`, including endpoint derivatives. Identification and propagation are proved in `AnalyticTransport` and `SegmentAnalytic`; `LocalTrivialization` constructs the smooth product maps from this parameter dependence. |
| Propagation of analytic dependence along a complete regular trajectory | PROVED: `laurent_local_analytic_endpoint`, `laurent_family_analytic`, `laurent_family_joint_analytic`. Uniqueness identifies local analytic endpoint maps; connected-interval induction propagates dependence, and rescaling adds joint time dependence. No parameter regularity of the chosen solutions is assumed in advance. |
| Complete chosen transport with varying velocity | PROVED: `laurentSegmentCurve_joint_analytic`, `laurentSegmentCurve_eq_fiberCurve`, `laurentSegmentCurve_has_analytic_extension`. The parameter set is precisely `admissibleSegmentParameters`; results hold within that set and give analytic ambient germs at every admissible triple. Openness of the admissible set is not asserted. |
| Analyticity of forward and inverse fiber transport | PROVED: `fiberTransport_has_analytic_extension`, `fiberTransportBack_has_analytic_extension`. At every point the existing fiber maps agree locally on the source fiber with a real analytic ambient map. No manifold instance or diffeomorphism object is assumed by these statements. |
| Regular fibers as analytic real manifolds | PROVED: `laurent_regular_product_chart_fixed`, `laurentRealDifferential_ker_finrank`, `regularFiberIsManifold`. The actual real differential is surjective via the normalized lift; complemented-kernel implicit charts are sliced and their transitions proved analytic. The fixed model has real dimension `2d - 2`, retains the subtype topology, and handles empty fibers. `regularLaurentValue_of_not_critical` derives the explicit regularity property from exclusion of ordinary critical values. A complex-manifold atlas is not claimed. |
| Manifold smoothness of complete fiber transport | PROVED: `regularFiber_val_contMDiff`, `fiberTransport_contMDiff`, `fiberTransportBack_contMDiff`, `fiberTransportDiffeomorph`; analytic ambient extensions yield analytic maps between the constructed fiber manifolds. The diffeomorphism definition derives both regular-fiber instances from `GoodSegment`; it uses the original fiber equivalence. |
| Openness of the actual good-value locus | PROVED: `exists_local_gradient_bound`, `gradient_bound_excludes_critical`, `criticalValues_union_isClosed`, specialized by `laurentCriticalValues_isClosed` and `laurentGoodValues`. A local version of the proper-radius compactness contradiction supplies a weighted-gradient bound on an entire base neighborhood. This proves closedness of the union, not finiteness of either set. |
| Smooth product transport and compact base/cycle sweeps | PROVED: `convexTransport_contMDiff`, `convexTransportBack_contMDiff`, `convexTransportDiffeomorph_base`, `convexTransport_center`, `convexTransport_compact_sweep`. The model uses the previously constructed fiber manifold and the usual open-subset manifold of the coordinate torus. Compact parameter subsets have compact images contained in the regular domain. Empty fibers are covered by the same equivalence. No semialgebraicity, integration, or local-system package is inferred. |
| Identity transport for a stationary segment | PROVED regression: `fiberTransport_zero`. |
| Uniform local time on a compact subset of the regular domain | PROVED: `uniform_ode_time_on_compact`, retaining the range bound from the local Picard construction. |
| Compact-domain continuation | PROVED: `ode_extend_right_of_compact` and `ode_exists_past_of_compact_control`; autonomous Banach-space statements with explicit domain and compact-control hypotheses. |
| Complete Laurent segment existence | PROVED component: `laurent_complete_segment` derives its own compact control and constructs an open solution interval containing `[0,1]`. |
| Stationary base-segment regression | PROVED: `laurent_zero_velocity_curve`; the zero-velocity field has a constant solution. |
| Picard branch for a continuous driving velocity curve | PROVED: `drivenCurveVectorField_apply`, `drivenCurveVectorField_contDiffAt`, `laurent_exists_driven_picard_neighborhood`. The velocity is a Banach-space parameter in `C([0,1], ℂ)`, with no derivative in time required. `torusCurveIntegralFrom` permits arbitrary time anchors. The integral equation yields actual scaled ODE curves via `laurent_driven_picard_equation_solves_ode`. |
| Two-sided local driven ODE and uniform compact-family time | PROVED: `laurent_driven_local_family`, `laurent_driven_local_existence`, `laurent_driven_uniform_time`. The family is continuous in start time, scale, and initial point, and analytic in the initial point with the other parameters fixed. A midpoint anchor gives full endpoint derivatives on a two-sided local interval. A finite subcover gives one time for compact time/position sets. No autonomous time augmentation or time differentiability of the velocity is assumed. |
| Driven uniqueness, gluing, and continuation | PROVED: `laurent_driven_lipschitz_on_compact`, `laurent_driven_unique_on_open_interval`, `laurent_driven_unique_on_closed_interval`, `laurent_driven_glue_right`, `laurent_driven_extend_right_of_compact`, `laurent_driven_exists_past_of_compact_control`. Time-dependent Gronwall supplies uniqueness and the supremum-of-reachable-times proof supplies continuation. |
| Proper control and complete lifting of a C¹ base path | PROVED component: `laurent_driven_curve_base`, `laurent_driven_curve_radius_bound`, `laurent_complete_driven_path`, `laurent_complete_C1_path`. The compact base is the path image; its positive weighted-gradient bound and a velocity bound give a common proper-radius bound and separation from the critical locus. A clamped continuous velocity extension removes any global-extension hypothesis from the closed-interval theorem. This establishes existence and exact base motion; the subsequent modules below provide endpoint analyticity and finite composition. |
| Analytic dependence for complete driven solutions | PROVED: `laurent_driven_local_analytic_endpoint`, `laurent_driven_family_analytic`, `laurent_driven_family_analytic_on`. Fixed-time endpoint maps are analytic in the initial position. The driving velocity is fixed and only continuous in time; no joint analytic time dependence or prior continuity of a chosen solution family is assumed. |
| Complete C¹-path fiber diffeomorphism | PROVED component: `LaurentC1Path.curve_spec`, `reverse_curve`, `transportEquiv`, `ambientCurve_analytic`, `transportDiffeomorph`. The chosen actual normalized-gradient trajectories have exact base motion. Uniqueness gives the inverse through time reversal; analytic ambient germs yield actual manifold maps. Endpoint regularity follows from the path exclusion hypothesis. |
| Finite composition of C¹ pieces | PROVED component: `LaurentC1Path.ofInterval` rescales an arbitrary compact interval, including the velocity factor. `LaurentC1Chain.transportDiffeomorph` composes a finite nonempty sequence of endpoint-matching unit pieces; its inverse traverses reversed pieces in reverse order. This is a concrete piecewise-path presentation. `ChainHomologyHomotopy.basePath` gives its concatenated continuous base path and the homology-level homotopy theorem; no derivative at corners is asserted. |
| Joint continuity of complete driven transport | PROVED: `laurent_driven_family_joint_continuous_on`, `LaurentC1Path.ambientCurve_joint_continuous`, `LaurentC1Path.curves_continuous`. Uses continuity of the local Picard endpoint in start time, duration, and initial position, together with fixed-time initial analyticity and uniqueness. The velocity is continuous only on `[0,1]`; separate continuity is not used as a substitute for joint continuity. |
| Compact C¹ and finite-chain sweeps | PROVED: `LaurentC1Path.sweep_isCompact`, `sweep_subset_regular`, `sweep_base`; `LaurentC1Chain.sweep_isCompact`, `sweep_subset_regular`. The finite-chain sweep is the union of each successive piece sweep, starting from the preceding endpoint image. No global derivative at corners or semialgebraicity is asserted. |
| Local homotopy comparison with product coordinates | PROVED: `LaurentC1Path.localCoordinateHomotopy`, `localTransportHomotopy`, `transportHomotopyOfConvex`. Project the complete jointly continuous trajectory to a reference fiber using the actual smooth local trivialization. At the terminal reference value the coordinate is the identity. Paths inside the same convex good neighborhood with matching endpoints induce homotopic fiber maps. |
| Actual integral singular-homology transport | PROVED components: `laurentFiberHomology` uses mathlib singular homology with coefficients in the ℤ-module ℤ; `LaurentC1Path.homologyIso` and `LaurentC1Chain.homologyIso` act in every degree. The reverse path induces the inverse, and `LaurentC1Chain.homologyMap_append` proves composition. These are maps on the actual singular homology of the fibers, not abstract unspecified groups. |
| Agreement with local product coordinates on homology | PROVED components: `LaurentC1Path.homologyMap_eq_local`, `homologyMap_eq_of_convex`, and `LaurentC1Path.homologyMap_comp_coordinate` / `LaurentC1Chain.homologyMap_comp_coordinate`. Mathlib homotopy invariance identifies the induced homology maps. The hypotheses explicitly require the whole path/chain in one convex good neighborhood. |
| Homology coordinate changes | PROVED: `localFiberCoordinateHomeomorph`, `localFiberHomologyIso`, `LaurentC1Path.homologyMap_eq_coordinate_iso`, `localHomologyTransition_eq_on_overlap`. A straight C¹ segment inside the convex intersection compares both coordinates through the same actual ODE homology map. |
| Global homology sheaf and local constancy | PROVED component: `ConstantTransitionAtlas.sheaf` supplies verified gluing of dependent sections, `stalkEquiv` identifies actual stalks, and `isCoveringMap_etale` proves the étalé covering. `ConstantTransitionModuleAtlas.sheaf`, `stalkLinearEquiv`, and `germLinearEquiv` retain the integral module operations and actual module colimits. `laurentHomologyModuleSheaf`, `laurentHomologyStalkLinearEquiv`, `laurentHomologyGermLinearEquiv`, and `laurentHomologySheaf_isCoveringMap` instantiate all these constructions on the full good-value locus using proved transition identities and a covering family of convex patches. |
| Local sheaf/ODE transport comparison | PROVED: `laurentHomologySection_transport`: sections are transported by the actual ODE homology map along a C¹ path contained in a single convex patch. The subsequent `HomologyLift` and `ChainHomologyHomotopy` modules provide the global comparison. |
| Homology maps at intermediate times | PROVED: `LaurentC1Path.timeMap`, `timeHomologyMap`, `timeCoordinateHomotopy`, `timeHomologyMap_coordinate_eq`, and `exists_time_patch`. Jointly continuous complete trajectories induce actual homology maps at each time; interpolation between nearby times stays in a single patch and produces the needed coordinate homotopy. |
| Global ODE/covering transport comparison | PROVED: `laurentHomologyModuleSheaf_isCoveringMap`, `LaurentC1Path.homologyLift_continuous`, `homologyLift_zero`, `homologyLift_one`, `homologyLift_eq_liftPath`, and `monodromy_homologyMap`. `LaurentC1Chain.monodromy_homologyMap` extends agreement to all finite C¹ chains through covering monodromy composition and actual ODE-map composition. No semialgebraicity of the ODE curves is asserted. |
| General fixed-endpoint homotopy invariance | PROVED: `LaurentC1Path.homologyMap_eq_of_homotopicRel`, `homologyMap_eq_of_homotopic`, and `LaurentC1Chain.homologyMap_eq_of_homotopic`. The homotopy is arbitrary continuous in the full good locus, may cross charts, and need not be differentiable. `LaurentC1Chain.homologyMap_eq_id_of_nullhomotopic` requires a null-homotopy explicitly; arbitrary loops may act nontrivially. |
| Analytic continuation of periods | OPEN: the topological local system and its ODE transport are constructed, but differential forms, integration pairing, and holomorphic period continuation remain unproved. |
| Endpoint representative/ODE class comparison | OPEN. |
| Endpoint error term by continuity from above on compact truncations | OPEN. |
| Residue geometric-series convergence and character coefficient extraction | PROVED scalar components: `summable_constantTerm_series`, `integral_torusCharacter`, `integral_torusLaurent_eq_constantTerm`, and `generatingFunction_eq_torusCauchy`. The measure is normalized product Haar on arbitrary nonzero-radius product circles, parametrized by `(ℝ/ℤ)^d`. The oriented logarithmic-form interpretation remains open. |
| Analytic continuation of the rational period to the small positive interval | OPEN. |
| Exponent support estimates, strict separation and eventual multiplier vanishing | PROVED components in `Laurent`; adapted proof provenance below. |
| Newton-power coefficient and vertex arguments | PROVED: `coeff_pow_unique_min` proves the exact coefficient at `n • v`, `finite_extremePoint_exposed` supplies a strict supporting functional for every extreme point of a finite hull, and `extremePoint_pow_mem` proves vertex survival. `newtonPolytope_mul_subset` and `newtonPolytope_pow_subset` supply the support-based inclusions. |
| Finite vertex hull and Newton-power homogeneity | PROVED: `newtonPolytope_pow` recovers the finite vertex hull using mathlib's Krein–Milman theorem plus compactness, then proves the full set equality. `origin_in_newton_powers` inhabits the exact previously isolated target proposition. |
| Supporting-face restriction | PROVED: `facePart_mul`, `facePart_pow`, and `constantTerm_facePart_pow` compare full convolution coefficients under nonnegative supporting weights. `newtonPolytope_facePart` gives the exact intersection with the supporting hyperplane. |
| Termination of supporting cuts | PROVED: `exists_proper_supporting_cut` works in the actual real-span topology. `facePart_support_card_lt` and support-cardinality induction give `exists_span_interior_restriction`, with surviving coefficients and every power constant term preserved. |
| Integral coordinates and full interior | PROVED: `integralLattice`, `latticeEmbedding`, and `latticeRealMap` use an integer basis of the lattice in the real span. `latticeRealMap_injective` uses faithful scalar extension of integer vectors, `lattice_rank_le` proves `r ≤ d`, and `exists_interior_lattice_coordinates` transfers relative interior through a real linear homeomorphism. |
| Boundary-to-interior minimal theorem reduction | CONDITIONAL: `minimal_of_interior_minimal` and `minimal_iff_interior_minimal` remove boundary and rank-zero cases. `InteriorMinimalNonvanishing` is an unproved proposition for all positive ranks, not a theorem or an axiom. |
| Integral support coordinates | PROVED: `exists_integer_weight_injOn` uses a non-root of finitely many nonzero integer polynomials to separate support with weights `(1,N,...,N^(d-1))`. `exists_first_coordinate_minimum` and `exists_all_coordinate_minimum` construct actual integer linear automorphisms by transvections. |
| Real extension of exponent changes | PROVED: `realExponentMap`, `realExponentEquiv`, `newtonPolytope_reindex`, and `origin_interior_reindex` transfer lattice automorphisms to real linear homeomorphisms. `coordinate_minimum_neg` uses full Newton interior to make each support minimum negative. |
| Ordinary-polynomial factorization and evaluation | PROVED: `polynomialLaurentHom` is the injective ordinary-polynomial inclusion. `factor_at_coordinate_minimum` gives the exact coefficient-preserving factorization; `laurentEval_polynomialLaurentHom` and `laurentEval_polynomial_factor` identify the pointwise formula. |
| Vertex-chart analytic target | CONDITIONAL: `minimal_of_vertex_minimal` and `minimal_iff_vertex_minimal` reduce the full target to `VertexMinimalNonvanishing`, an unproved proposition retaining full Newton interior as well as positive monomial exponents and nonzero polynomial constant coefficient. |
| Local polynomial derivative disc | PROVED: `exists_polynomial_derivative_polydisc` gives a zero-free closed polydisc and strict bounds for all logarithmic partials. `residueFiberPolynomial_logderiv`, `residueFiberPolynomial_regular_root`, and `residueFiberPolynomial_deriv_ne_zero` give exact root identities and nonzero actual one-variable derivatives. `exists_residue_regular_polydisc` is uniform in the fiber parameter. |
| Constant-term generating function | PROVED: `coeff_pow_norm_le` controls every power coefficient by the finite coefficient mass. `summable_constantTerm_series` proves convergence outside that bound. `generatingFunction_eq_inv_of_vanishing` proves exactly `R(s)=1/s` under the explicit universal-vanishing premise. |
| Haar Cauchy transform | PROVED: `weightedCoefficientMass` bounds Laurent evaluation on every product circle. `hasSum_constantTerm_torusCauchy` uses dominated convergence and exact power coefficient extraction; `generatingFunction_eq_torusCauchy` identifies the scalar integral. This is not an integration pairing with a residue cycle. |
| Finite Fourier sum representation | PROVED: `isFiniteFourierSum_iff_coefficients` identifies the Laurent representation with a finite sum of standard integer characters. Continuity, product/power coefficient extraction, and the conditional torus Mathieu theorem are checked. Equivalence with all continuous torus-finite functions remains an open separate remark. |
| Compact residue root locus | PROVED: `exists_residue_boundary_bound`, `isCompact_residue_root_locus`, and `exists_residue_interior_regular_roots` give the compactness and boundary estimates. `unimodular_vertex_chart_nat` bridges the natural exponents, and `residueFiberPolynomial_zero_iff` identifies the equation with the Laurent fiber. `residueRootPoint` is continuous and injective with compact range. |
| Residue covering projection | PROVED: `exists_residue_covering_degree` supplies the actual surjective covering with exactly `m 0` points in each fiber. `ResidueDiscData.residueRootSpace_nonempty` proves the root locus nonempty. `CompactRootCovering` constructs the projection charts explicitly from the implicit function theorem. The earlier degree-free covering result is strengthened by the checked deformation argument. |
| Local root variation | PROVED: `exists_residue_covering_with_branches` gives a locally unique complex-smooth root branch at every point of the chosen covering, with the fiber value and other coordinates as parameters. This is local root variation, not yet a cycle or a homology-class variation theorem. |
| Uniform root deformation | PROVED: `ResidueDiscData` packages a proved small-disc choice, a uniform evaluation bound, and the strict derivative estimate. `residueDeformationEquation_logderiv`, `deformation_boundary_ne_zero`, and `deformation_regular_root` control `u(t y₁,y′)` uniformly for `‖t‖≤1`. `isCoveringMap_deformationProjection` constructs the compact deformation covering. |
| Exact root count | PROVED: `complex_monomial_root_card_in_disc` counts the distinct monomial roots using algebraic closedness and separability. `covering_fiber_card_eq_along_path` transports cardinality along the parameter segment. `ResidueDiscData.residueRootProjection_card` identifies its endpoint with the actual residue projection and proves degree `m 0`. This is the documented replacement for the manuscript's Rouché step. |

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
   of transport. The later analytic-dependence modules supply the parameter
   regularity, `FiberDiffeomorph` supplies the manifold refinement, and
   `LocalTrivialization` constructs the product maps.
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
    parameters, including nonzero small time scales.
11. `AnalyticTransport` identifies each local analytic endpoint map with every
    regular solution through the same initial point by ODE uniqueness. A
    connected-interval induction propagates analytic dependence from time zero
    to any time of an existing complete segment; rescaling gives joint time
    dependence, including the endpoints. `SegmentAnalytic` applies this to the
    actual chosen transport with varying velocity and initial point. The
    resulting analyticity within the admissible parameter set supplies local
    ambient analytic extensions, including for the original forward and inverse
    fiber maps. This implements the manuscript's smooth-dependence input for
    this explicit autonomous family; it neither changes the field nor assumes
    a separate global smooth flow. Parameter-set openness is not inferred from
    these statements. Fiber manifolds and local trivializations are constructed
    separately below.
12. `RegularFiberCharts` uses the existing complex derivative and scalar lift
    to prove surjectivity of the actual real differential, then applies the
    complemented-kernel implicit-function theorem. Restricting the resulting
    product chart keeps its source in the regular torus and its inverse
    analytic. Rank-nullity gives real kernel dimension `2d - 2`.
    `FiberAtlas` slices these charts at the fiber value and proves analytic
    chart changes, producing genuine `ChartedSpace` and `IsManifold` instances
    with the existing subtype topology. The `RegularLaurentValue` hypothesis
    is an explicit property, proved from exclusion of ordinary critical values
    and from every good segment; it is not a project axiom.
    `FiberDiffeomorph` transfers the prior ambient-extension results to these
    manifolds and packages the actual transport equivalence as a diffeomorphism.
    `complete_segment_transport` assembles the segment lemma, including compact
    sweeps for arbitrary compact initial subsets. These are real analytic
    manifold constructions; no complex atlas is claimed. The later driven modules
    extend the transport from segments to C¹ paths.
13. `LocalTrivialization` follows the manuscript's straight-segment construction:
    forward transport uses velocity `s - b`, and the inverse uses `b - f(y)`.
    Uniqueness and reversal give the two inverse identities; ambient parameter
    dependence gives manifold smoothness of both maps. The result is a bundled
    smooth (`∞`, not analytic `⊤`) product diffeomorphism with the original
    Laurent evaluation as its base coordinate. The center map is the identity,
    and compact parameter families have compact sweeps in the regular domain.
14. `CriticalNeighborhood` proves openness of the good-value locus directly by
    the same proper-radius compactness argument used for the uniform gradient
    lemma: failure of a neighborhood lower bound produces either an ordinary
    critical limit or an escaping sequence witnessing an asymptotic value.
    Conversely such a bound excludes both kinds of critical value on that open
    neighborhood. This supplies the open discs for local triviality without
    waiting for the separately required finiteness theorem. It does not replace
    the common-radius finiteness proof or assert semialgebraicity. This extra
    topological lemma is documented as a dependency refinement, with no change
    to the manuscript's transport map or local-triviality conclusion.
15. `DrivenPicard` extends the same scalar lift to a continuous velocity curve
    as a Banach-space parameter. Its analytic implicit-function argument still
    uses the identity partial derivative at zero time scale. Subtracting the
    primitive at a chosen anchor permits a midpoint initial value.
    `DrivenLocalODE` rescales these anchored curves to actual time and uses
    finite compact subcovers for uniform local time. This avoids imposing
    differentiability or Lipschitz regularity in time on a merely continuous
    velocity, as an autonomous time-augmentation shortcut would require.
16. `DrivenContinuation` adapts the existing project uniqueness/gluing/supremum
    arguments to the time-dependent scalar field. Spatial Lipschitz constants
    are obtained on compact velocity/position products; local existence time
    is uniform over compact time/position products. The inherited Apache-2.0
    notices are retained. `DrivenTransport` then follows the manuscript:
    prescribed base motion, velocity supremum, proper-radius Gronwall, and the
    positive differential bound on a compact regular-domain subset. The final
    C¹ lifting theorem allows one-sided base derivatives and velocity continuity
    only on the closed unit interval, using a continuous clamped extension in
    the proof. Endpoint smoothness and finite composition are supplied separately
    by the next modules.
17. `DrivenAnalytic` repeats the local-identification/connected-interval argument
    for fixed continuous driving velocities, rescaling oriented subintervals
    and using the driven uniqueness theorem. It proves analyticity in initial
    points only; continuity of the velocity does not imply analytic dependence
    in time. `C1FiberTransport` reverses the actual chosen complete trajectories
    and extracts ambient analytic germs to construct the regular-fiber
    diffeomorphisms. The path structure carries precisely continuous velocity,
    one-sided base derivatives, endpoint values and critical-value exclusion.
18. `PiecewiseTransport` represents finite piecewise paths as endpoint-matching
    C¹ chains. Each piece can be normalized from any compact time interval by
    `LaurentC1Path.ofInterval`; the velocity acquires the interval-length factor.
    Endpoint maps compose in order, and inverses in reverse order. This proves
    the finite-composition component without asserting a derivative at the
    corners. Global homotopy/monodromy compatibility is supplied by
    `ChainHomologyHomotopy` below.
19. `DrivenAnalytic.laurent_driven_local_analytic_endpoint` now retains the
    continuous dependence on all local parameters already provided by Picard.
    `DrivenContinuity` combines this with fixed-time initial analyticity and
    uniqueness to identify the complete family on a product neighborhood of
    each initial-point/time pair. `C1Sweeps` pulls back to the fiber and closed
    time interval, then takes compact images. Finite chains use finite unions
    of the individual piece sweeps, with transported compact initial sets.
20. `LocalTransportHomotopy` projects a C¹ trajectory into a fixed reference
    fiber through the existing local product inverse. This gives an actual
    continuous homotopy between the initial product identification and the
    terminal identification after ODE transport. It avoids any smoothness
    assumption on an interpolating family of base paths. `TransportHomology`
    applies mathlib's singular-homology functor and its homotopy invariance,
    with integral coefficients in every degree. Functoriality supplies the
    finite-chain identities. The next modules supply global gluing; a
    semialgebraic integration/homology pairing remains open.
21. `HomologyTransitions` compares the coordinate maps along a straight C¹
    path in each convex overlap. The coordinate-change map is therefore
    constant across that whole overlap. `ConstantTransitionSheaf` constructs
    dependent sections that are locally constant in these coordinates, uses
    mathlib's local-predicate sheaf construction to prove gluing, and identifies
    actual stalks by evaluation. Connected chart domains give bijective germ
    maps, hence a covering étalé space through mathlib's covering criterion.
    `ConstantTransitionModuleSheaf` proves closure under module operations,
    reflects the sheaf condition through the forgetful functor, and constructs
    linear stalk evaluation using the module colimit. `HomologySheaf`
    specializes both constructions to actual Laurent-fiber singular homology.
    Its covering and linear germ isomorphisms express local constancy without
    postulating any gluing or local-system axiom. The linear sheaf is shown
    to have exactly the underlying set sheaf already constructed. Agreement
    with actual ODE transport is proved for paths in each convex patch.
22. `TimeHomology` constructs the homology map of every time slice of the
    complete trajectory. Near any time, the prescribed base lies in one convex
    good chart. Interpolating the time variable inside that neighborhood gives
    a homotopy of maps to the fixed reference fiber. `HomologyLift` uses this
    to identify the time-dependent homology class locally with the germ of
    one fixed chart section. Its continuity follows from the actual étalé
    topology; its two endpoints are checked against the identity and the ODE
    endpoint map. Covering-space uniqueness then identifies this class curve
    with mathlib's path lift, and mathlib's homotopy lifting theorem proves
    invariance under general continuous fixed-endpoint homotopies. This is a
    checked implementation of local-system transport, avoiding a separate
    combinatorial subdivision construction. `ChainHomologyHomotopy` composes
    the comparison through the monodromy API for the actual finite chain.
    No regularity of the interpolating path homotopy beyond continuity and
    no triviality of arbitrary loop monodromy are assumed.
23. `NewtonPowers` implements the manuscript's exposed-vertex coefficient
    argument. Convolution at `n • v` reduces to the unique minimizing exponent,
    using the existing support lower bound to exclude every other summand.
    Strict separation of a vertex from the convex hull of the remaining finite
    support supplies its exposing functional, with minima replacing maxima by
    sign convention. For the finite-polytope fact that the hull equals the hull
    of its vertices, the implementation specializes mathlib's Krein–Milman
    theorem and removes the closure using compactness of the finite vertex hull.
    This is a documented proof substitution for that convex-geometric step;
    the Laurent coefficient argument and the full manuscript equality are
    unchanged. All positive exponents and all finite ranks are covered, and the
    proof also handles zero polynomials. `infinite_of_minimal` discharges the
    formerly separate Newton-power premise while leaving minimal nonvanishing
    explicit and unproved.
24. `FaceRestriction`, `RelativeFaceReduction`, `LatticeCoordinates`, and
    `FaceReduction` prove the complete statement of `lem:face`. The implementation
    uses successive proper supporting cuts in place of selecting the smallest
    face in one step. Hahn–Banach in the real span gives a functional that is
    genuinely positive somewhere whenever zero is not interior; each cut strictly
    reduces finite support cardinality. Full convolution identities preserve
    coefficients and every power constant term, including the zeroth power.
    The exact convex-hull intersection uses extreme points and finite-hull
    compactness as in the preceding Krein–Milman specialization. This is a
    proof substitution, not a manuscript correction or a new hypothesis.
    After termination, the lattice is exactly the integral vectors in the
    real span. The PID submodule basis theorem gives its integer basis;
    faithful scalar extension proves real independence, and the support gives
    real spanning. The induced linear homeomorphism transfers interior and
    proves the rank bound. The zero-rank polynomial is explicitly a nonzero
    singleton at exponent zero. Downstream, `minimal_iff_interior_minimal`
    proves that the outstanding principal theorem is equivalent to its
    positive-rank full-interior form. No positive-rank nonvanishing follows
    without that remaining analytic premise.
25. `IntegerSupportShear` replaces the manuscript's rational-density and
    primitive-vector basis-extension construction in `lem:chart`. Encode an
    exponent vector as an integer polynomial. Distinct support vectors give
    distinct polynomials; avoid the finitely many roots of their differences
    to obtain an integer weight `(1,N,...,N^(d-1))` injective on support. Its
    first coefficient is one, so an explicit transvection extends it to an
    integer coordinate automorphism. A second integer transvection makes its
    unique minimizing support point the strict minimum in all coordinates.
    `RealExponentChange` extends integral maps to real linear maps and proves
    that coordinate automorphisms preserve Newton interior. Interior excludes
    a nonnegative coordinate minimum. `PolynomialFactorization` shifts the
    minimum exponent to zero, proves nonnegative support, and pulls back along
    the injective ordinary-polynomial exponent map. Its constant coefficient
    is exactly the original minimum coefficient, including its complex value.
    `VertexChart` assembles the full manuscript statement, and
    `VertexChartEvaluation` proves the pointwise formula with `u(0) ≠ 0`.
    This is a proof substitution for the coordinate choice, not a change of
    mathematical statement. Downstream, `minimal_iff_vertex_minimal` reduces
    the full minimal theorem to its chart form while retaining the necessary
    full-interior hypothesis. No residue, period, or positive-rank
    nonvanishing conclusion is inferred without the remaining analytic work.
26. `ResiduePolydisc` proves the first local estimates in `lem:residue`
    directly from continuity at the nonzero constant coefficient, with a single
    closed polydisc controlling every coordinate. The formal logarithmic
    derivative of `s y^m-u` is computed at a root; the strict estimate makes
    both the coordinate and that partial nonzero. An induction on ordinary
    polynomials identifies these partials with actual derivatives while the
    other coordinates are fixed. This does not establish root multiplicities,
    root count, covering degree, or a cycle integration theorem.
    `CoefficientSeries` gives a direct convolution bound for all power
    coefficients, proves convergence, and computes `R(s)=1/s` under universal
    positive-power vanishing. `TorusCoefficients` models phases by `(ℝ/ℤ)^d`
    and supplies actual normalized product-Haar instances. Mathlib's Fourier
    orthogonality and finite-product Fubini give integer-character integration
    and exact Laurent coefficient extraction. For arbitrary nonzero radii,
    a finite weighted coefficient sum bounds the integrands.
    `TorusCauchySeries` uses dominated convergence with a summable geometric
    majorant to exchange summation and Haar integration; this substitutes for
    the manuscript's uniform-geometric-series exchange. The resulting scalar
    Cauchy formula is proved, but its oriented logarithmic-form interpretation
    and conversion to a residue period remain open. `TorusMathieu` uses the
    Haar bridge to prove the full finite-Fourier implication conditionally
    on `MinimalNonvanishing`; the premise has not been discharged.
27. `ResidueRootLocus` completes the boundary and compactness estimates for
    the local root equation, converts the checked vertex chart to positive
    natural exponents, and proves exact agreement with the Laurent fiber.
    `CompactRootCovering` slices the ordinary product-domain implicit-function
    chart, keeping the base subset arbitrary, to construct an open partial
    homeomorphism whose map is the actual base projection. A continuous map
    from this compact root locus is closed; mathlib's compact local-homeomorphism
    criterion therefore gives a covering. `PolynomialRootCharts` discharges
    the differential hypotheses by polynomial induction and the already proved
    partial-derivative formula. `ResidueCovering` applies this to the manuscript's
    product circles, including the rank-one empty base product, and proves the
    fibers finite and the coordinate image compact and injectively parametrized.
    `ResidueRootBranches` includes the fiber value among the implicit parameters
    and proves local complex-smooth branches with local uniqueness. This follows
    the manuscript's compactness/implicit-function argument. This covering
    construction permits empty fibers; the degree, nonemptiness, and
    surjectivity require the separate argument in the next item. No orientation,
    cycle, or homology-class statement follows from this covering construction.
    Semialgebraicity is supplied separately in item 29.
28. `ResidueCoveringDegree` replaces the manuscript's Rouché invocation by
    a fully proved special-case deformation count. On the same small polydisc,
    replace `u(y₁,y′)` by `u(t y₁,y′)` for `|t|≤1`. The logarithmic derivative
    identity and strict estimate hold at the scaled point, so every root stays
    regular. A single uniform bound excludes boundary roots for every base
    point and parameter. For fixed `y′`, compactness and the implicit function
    theorem give a covering over the closed unit parameter disc. Mathlib's
    covering monodromy gives an actual equivalence of the endpoint fibers
    along `t∈[0,1]`. At zero the equation is `A z^(m 0)=u(0,y′)`;
    nonzero coefficients, complex algebraic closedness, and separability give
    exactly `m 0` distinct roots, all strictly inside the chosen disc. Explicit
    fiber equivalences identify the endpoint at one with the original residue
    projection. Thus `exists_residue_covering_degree` proves the same sheet
    count as the manuscript, in every positive rank, and discharges surjectivity
    and nonemptiness. `residueRoot_local_branch` supplies local smooth branches
    for this same radius. No general Rouché theorem is assumed or claimed.
    Oriented cycles, residues, and the period identity remain
    separate open obligations. This auxiliary root deformation does not change
    the main common-radius / normalized-gradient transport dependency chain.
29. `SemialgebraicSets` defines the standard finite Boolean combinations of
    real polynomial weak inequalities and proves finite Boolean closure and
    polynomial preimages. `PolynomialRealParts` proves real/imaginary polynomial
    representations by polynomial induction. `ComplexSemialgebraic` identifies
    the real coordinates by an explicit homeomorphism and proves polynomial
    zero sets, disc/circle constraints, and complex polynomial preimages
    semialgebraic. `ResidueSemialgebraic` proves exact equality of the covering
    coordinate image with the polynomial root locus and hence its
    semialgebraicity. The total family, including the fiber value as a complex
    coordinate, has an explicit polynomial description as well.
    `exists_compact_semialgebraic_residue_covering` assembles compactness,
    semialgebraicity, surjectivity, and the exact sheet count with no additional
    regularity hypothesis. No projection, Hardt, orientation, cycle, or
    integration theorem is assumed by this construction.
30. `SemialgebraicRational` clears a finite sum of fractions using the product
    of their strictly positive polynomial denominators. `AffineSemialgebraic`
    proves semialgebraicity of the actual closed affine torus, its induced L2
    spheres, and restricted-differential sublevel sets. `PolynomialSignFamilies`
    retains arbitrary real polynomial parameters in weighted gradient bounds,
    norm equalities, and strict target-distance inequalities.
    `CommonRadiusSemialgebraic` applies these to the exact two-parameter family
    `smallGradientTotalFamily`, with radius and threshold as free coordinates.
    `RadiusProjection` proves the exact radius incidence set semialgebraic and
    identifies its coordinate projection with `radiusApproximationSet`.
    `SemialgebraicTail` proves sign stabilization along polynomial curves, and
    hence tails for unbounded one-dimensional semialgebraic sets. These give
    `radiusTail_of_semialgebraic_projection`, a conditional proof from the
    explicitly unproved real coordinate-projection proposition. The metric,
    restricted differential, parameter range, and existential point witnesses
    agree with the original geometric obligation. This follows the manuscript
    squaring/positive-denominator/projection argument; it assumes neither
    elimination nor a uniform component/path bound.
31. `SpherePathEstimate` differentiates the equations `zᵢwᵢ=1` along a
    real curve within the affine torus, proving its velocity belongs to the
    already identified tangent subspace. Restricting the actual polynomial
    differential gives the bound `|(F(Rγ))′| ≤ ε ‖γ′‖`. The interval fundamental
    theorem of calculus and norm/integral inequalities yield the integrated
    bound. `SpherePathChain` sums this over finite endpoint-matching C¹ pieces;
    no derivative at a corner is required. Its length is the sum of the speed
    integrals. The explicitly unproved `SphereC1ChainObligation` asks for
    uniform component labels and such chains with a uniform length bound.
    This is separate from the previous, weaker rectifiable-path obligation;
    equivalence, regular reparametrization, and equality with metric variation
    are not assumed. `ScalarFinitenessReduction` proves radius-set unboundedness
    from actual asymptotic sequences, normalization on the proper sphere, and
    the complete common-radius pigeonhole contradiction. The resulting
    `laurent_finite_asymptotic_of_projection_and_paths` applies to the original
    Laurent evaluation and restricted differential but retains projection and
    finite-C¹-path inputs as unproved hypotheses. This is conditional coverage
    of the same manuscript statement, not an unconditional finiteness theorem.
32. `CriticalLocus` proves that vanishing of the restricted norm is equivalent
    to vanishing of every torus partial, proves the locus semialgebraic, and
    proves constancy along finite C¹ chains. `DummyCoordinate` adjoins a new
    coordinate and its inverse, renames the old polynomial variables, and
    proves exact evaluation and partial-derivative identities. At a critical
    point, the extended polynomial remains critical for every nonzero value
    of the added coordinate. Choosing that value as n+1 gives a sequence
    escaping in the full induced radius, with constant polynomial value and
    identically zero radius times restricted norm.
    `ordinaryCriticalValues_subset_dummy_asymptotic` is the unconditional
    inclusion `K₀(p) ⊆ K∞(p extended)` in rank d+1. This replaces the manuscript
    ordinary-critical-locus stratification argument with a fully proved
    product-torus reduction to its required common-radius argument. There is
    no circularity: the checked asymptotic argument uses only projection and
    uniform sphere paths, not ordinary critical-value finiteness. Consequently
    `CriticalFiniteness` proves ordinary finiteness, finiteness of the actual
    union, and finiteness of the complement of `laurentGoodValues`, all under
    those same two explicitly unproved inputs. No additional critical-cover
    proposition or decomposition premise is introduced. This changes the Lean
    proof dependency only; the manuscript statement and source are unchanged.
33. No mathematical manuscript corrections or changes were made. No alternate
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

The checkpoint has 90 mathematical module files plus the root umbrella and
2 Lean verification helpers. See `scripts/validation.txt` for exact theorem
counts, the full build job count, and environment-level axiom/declaration counts. CI runs the same checks in a clean GitHub checkout.

The general-torus DvK dependency in the compact-Lie-group project is **not closed**.
Resume at the two explicit geometric obligations and the boundary report.
