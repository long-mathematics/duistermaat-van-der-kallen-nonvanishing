# Direct scalar route: precise formalization boundary

The theorem is **not formalized**. This report identifies the first unproved
geometric obligations after checking nontrivial special cases. It is a library
boundary, not a counterexample to the manuscript or a claim that the mathematics
is impossible in Lean. The manuscript has not been edited.

## Reproducible library investigation

Pinned mathlib: `5ed2965256430c3649e86755f9576b54eca72435` (Lean 4.34.0).
A source-tree search for `semialgebraic`, `semi-algebraic`, `Hardt trivial`,
`Tarski.Seidenberg` and `o-minimal` found no applicable implementation.
Searching triangulation found categorical triangulated structures and polygon
combinatorics, not compact semialgebraic triangulation. This finding is about
this pinned source tree, not every possible external Lean repository.

Additional checks:

- `ModelTheory/Algebra/Ring/Definability.lean` supplies ring definability, but
  does not eliminate real existential quantifiers.
- `FieldTheory/IsRealClosed/Basic.lean` supplies real-closed-field algebraic
  facts, square/odd-root existence, and ordered positivity facts. It supplies
  neither the required projection theorem nor Hardt triviality.
- `ModelTheory/Arithmetic/Presburger/Basic.lean` concerns integer additive
  arithmetic. Its quantifier-elimination references do not solve these real
  polynomial inequalities.
- `Analysis/Polynomial/Basic.lean` supplies polynomial leading-term asymptotics.
  These were successfully used for the univariate tail special case below.
- `Analysis/ODE/ExistUnique.lean`, `PicardLindelof.lean`, and `Gronwall.lean`
  provide meaningful local existence/uniqueness/continuous-flow tools. Gronwall
  and local existence for the actual smooth polynomial vector field are used
  in the checked project. `ODEContinuation` now proves the needed autonomous
  compact-domain continuation, and `LaurentTransport` proves complete segment
  existence and reversal. `FiberContinuity` proves uniform Lipschitz dependence
  in initial points at bounded proper radius, joint continuity in initial point
  and time, fiber homeomorphisms, and compact sweeps. Analytic parameter
  dependence and smooth local trivializations are now proved as detailed below.
  Complete C¹-path lifting, analytic endpoint diffeomorphisms, and finite
  composition of endpoint-matching C¹ pieces are also proved, along with joint
  continuity, compact sweeps, and convex-local compatibility on singular homology.
- Differential forms and singular homology exist, in separate mathlib modules.
  The general semialgebraic-chain integration/Stokes/homology pairing needed
  here was not found. `Analysis/BoxIntegral/DivergenceTheorem.lean` is a box
  theorem and cannot be relabeled as that package.

## Smallest isolated radius-tail obligation

The exact Lean proposition is `DuistermaatVanDerKallen.RadiusTailObligation` in
`DuistermaatVanDerKallen/SemialgebraicObligations.lean`.

Fix arbitrary finite rank `d`, complex polynomials `P,G₁,…,G_d` on the closed
ambient model, a target `c`, and positive thresholds ε,δ. For

    X = {(z,w) : zᵢwᵢ = 1},
    λ_G(x)² = Σᵢ |Gᵢ(x)|² / (1 + |wᵢ|⁴),

set

    E = {R > 1 : ∃ x ∈ X,
                    ‖x‖₂ = R,
                    R λ_G(x) ≤ ε,
                    |P(x) − c| < δ}.

Prove that if E is unbounded above, then it contains a tail. Polynomials on X
represent the Laurent polynomial and its coordinate partials. Permitting arbitrary
G gives a slightly stronger, still correct, specialized projection problem.
The norm includes both z and w; denominators are strictly positive.

What has been tried and checked:

1. A polynomial inequality in **one free real variable** has constant truth
   value sufficiently far to the right: proved from leading-term asymptotics.
2. Every finite Boolean combination of such inequalities has this property:
   proved by induction on `PolynomialSignFormula`.
3. Unboundedness then forces the true tail: proved as
   `PolynomialSignFormula.contains_tail_of_unbounded`.
4. Finite intersections of these tails support the common-radius pigeonhole
   proof: the complete abstract argument is kernel checked.
5. Polynomial evaluation, the displayed λ_G expression, and every fixed
   small-gradient sphere are continuous/compact as required: proved.
6. The actual induced tangent metric and restricted analytic differential norm
   are identified with this expression for true polynomial torus partials
   `P_zᵢ − wᵢ² P_wᵢ`: proved. `LaurentEvaluation` now constructs an ambient
   representative of every `MultiLaurent`, with equality of evaluations and
   product/power compatibility on the torus.
7. `isSemialgebraic_radiusIncidence` now proves the full incidence set
   semialgebraic by squaring nonnegative norm constraints and clearing the
   strictly positive polynomial denominators.
8. `radiusApproximationSet_iff_projection` proves exact agreement of its
   real coordinate projection with the original radius set.
9. `IsSemialgebraic.contains_tail_of_unbounded` connects the general finite
   Boolean sign definition to the checked univariate asymptotic theorem.
   `radiusTail_of_semialgebraic_projection` consequently derives the exact
   `RadiusTailObligation` from the explicitly unproved
   `SemialgebraicProjectionObligation` in `RadiusProjection`. No further
   encoding or metric-identification premise remains in this implication.

The exact remaining implication is an **existential projection**. E has one
free radius variable but also `4d` real existential coordinates. Calling it a
univariate polynomial set does not remove those quantifiers. Squaring the
nonnegative norm inequalities and clearing positive denominators leaves an
arbitrary-rank polynomial existential system, not a finite list of univariate
polynomial inequalities. Leading-term sign stabilization therefore does not
apply directly. Proving a relevant elimination procedure, or this particular
projection-to-tail theorem, is the next precise obligation.

## Independent uniform-path obligation

The exact Lean proposition is `DuistermaatVanDerKallen.SpherePathObligation`.
For the single family

    A(R,ε) = {u : ‖u‖₂ = 1, Ru ∈ X, R λ_G(Ru) ≤ ε},

find N ≥ 1 and L ≥ 1 **before** quantifying R > 1 and ε > 0, so that each
fiber's connected components can be labeled injectively by `Fin N`, and every
pair in a component has a continuous rectifiable path in that component with
metric variation at most L. `eVariationOn` on `[0,1]` is used for its length.
The restricted statement does not even demand semialgebraic parametrization;
thus proving it is necessary but would not by itself cover the manuscript's
stronger general compact-family lemma.

Compactness and the correct metric have been proved for this family.
`isSemialgebraic_smallGradientTotalFamily` now proves semialgebraicity of the
single family with both radius and threshold as free coordinates, and
`isComplexSemialgebraic_smallGradientSphere` checks its exact fibers. The
remaining path theorem cannot be deduced merely from that compactness:
compact sets in general can have infinitely many components and nonrectifiable
connected pieces. Nor can a separate finite bound for each fixed R,ε supply
uniform N,L. The manuscript's Hardt/model-triangulation/arc-volume proof needs
those missing structural results, even for these sphere fibers.

A valid next development can specialize those structural arguments to this
polynomial family, but must establish uniformity with respect to both parameters
and must not assume bounded derivatives for the Hardt homeomorphisms.

## Checked diameter estimate and remaining regular path input

`SpherePathEstimate` now proves tangency for derivatives of curves in the
closed affine torus and the restricted derivative bound on small-gradient
spheres. The interval fundamental theorem of calculus proves the endpoint
image distance is at most ε times the integral of the speed.
`C1ArcChain.smallGradient_image_dist_le` adds these estimates over finite C¹
pieces with matching endpoints. No differentiability at junctions is needed.

`SphereC1ChainObligation` asks for uniform component labels and such finite
chains, with the sum of the speed integrals bounded independently of R and ε.
It remains unproved. It is recorded separately from `SpherePathObligation`:
the earlier metric-variation bound alone has not been upgraded to the required
C¹ parametrizations, nor has equality of these notions of length been proved.
Hardt/triangulation/volume development must supply appropriate regular paths,
or the diameter estimate must be extended to arbitrary rectifiable paths.

`ScalarFinitenessReduction` assembles the actual common-radius proof. Its
`laurent_finite_asymptotic_of_projection_and_paths` has only the explicitly
unproved `SemialgebraicProjectionObligation` and `SphereC1ChainObligation` as
geometric premises. Asymptotic sequences give the exact unbounded radius
sets; projection gives their tails; finite intersections select one radius;
the checked chain estimate and pigeonhole principle give the contradiction.
This does not prove either geometric premise or unconditional finiteness.

## Ordinary critical values use the same geometric inputs

`ordinaryCriticalValues_subset_dummy_asymptotic` proves an unconditional
inclusion from the ordinary critical values of a rank-d polynomial into the
asymptotic critical values of its extension by one unused torus coordinate.
The point sequence has new coordinate n+1 and inverse 1/(n+1), so it stays in
the rank-(d+1) closed torus and escapes in the full induced radius. Exact
partial-derivative identities show that the restricted norm remains zero.

This fully checked substitution removes the need for a separate finite
critical-locus decomposition premise in the ordinary finiteness proof. Both
parts of scalar finiteness, their union, and finiteness of the complement of
the actual good-value locus now depend on the same unproved projection and
uniform finite-C¹-chain inputs. The proof does not establish those inputs or
unconditional finiteness. General stratification needed elsewhere in the
manuscript remains open. The canonical manuscript has not been changed.

## Why this is a substantive boundary

The missing inputs form a new real-algebraic-geometric foundation, not a missing
rewrite lemma. The available real-closed-field algebra and one-variable
asymptotics do not supply arbitrary-rank existential projection, compact
triangulation, uniform component counts, or the uniform arc-volume estimate.
Developing and auditing those results is a substantial prerequisite project.
The independent semialgebraic chain-integration and period/residue dependencies
also remain open, as itemized in the coverage ledger.

No project axiom has been introduced for any of these facts. The geometric and projection obligation
constants have type `Prop`; they are definitions of goals, not terms proving the
goals. Conditional results cannot be used to obtain minimal nonvanishing without
real proofs of their hypotheses. The appendix has not been substituted.

## Restart point and downstream consequences

Use the root `DuistermaatVanDerKallen` module and the pinned Lake configuration.
Run:

```sh
lake build
python3 scripts/audit_sources.py
python3 scripts/audit_coverage.py
lake env lean scripts/AxiomAudit.lean
lake env lean scripts/CheckTargets.lean
```

After supplying radius tails and uniform paths, prove the image-diameter
estimate using the now-proved restricted differential formula, and instantiate
`finite_of_common_radius` for the actual asymptotic-critical-value set.
`affineTorus_uniform_gradient`, `compact_regular_controlled_region`, and
`trajectory_radius_bound` already provide checked downstream control lemmas.
`LaurentGeometry` specializes actual field smoothness and local existence to
`MultiLaurent`, proves exact base motion and the proper-radius Gronwall estimate,
and proves that the controlled coordinate-space set is compact and lies in the
regular domain. `ODEContinuation` and `LaurentTransport` now complete
autonomous continuation and segment existence, uniqueness, and reversal.
`FiberTransport` and `FiberContinuity` now construct fiber homeomorphisms and
prove joint continuity in initial point/time and compactness of compact initial
sweeps. `CurveField`, `CurveIntegral`, `PicardImplicit`, and `LaurentPicard`
now supply the next local analytic input: a Banach-space Picard branch analytic
on an open parameter neighborhood of zero time scale, jointly in velocity and
initial point, with regular curves solving the actual integral equation and
producing scaled ODE trajectories. This includes nearby nonzero time scales;
`⊤ : WithTop ℕ∞` is mathlib's analytic differentiability order.
The zero-time partial derivative is proved to be the identity; no invertibility
hypothesis has been introduced. `AnalyticTransport` now identifies the local
analytic endpoint maps by uniqueness and propagates analytic dependence along
complete trajectories using connected-interval induction. `SegmentAnalytic`
proves joint analytic dependence of the chosen transport within the admissible
velocity/initial-point/time set and obtains analytic ambient germs for forward
and inverse fiber maps. No regularity of the chosen solution family was
assumed before propagation.

`RegularFiberCharts`, `FiberAtlas`, and `FiberDiffeomorph` now construct the
regular fibers as analytic real manifolds and package the actual complete
segment transport as an analytic diffeomorphism. The real kernel has dimension
`2d - 2`; regularity follows from exclusion of ordinary critical values.
`complete_segment_transport` assembles existence, base motion, the manifold map,
and compact sweeps of arbitrary compact initial subsets.

`LocalTrivialization` now constructs the product diffeomorphism over every
convex open good base, with the actual Laurent evaluation as base coordinate,
identity at the reference fiber, and compact sweeps of compact parameter sets.
`CriticalNeighborhood` proves the union of ordinary/asymptotic critical values
closed by a local proper-radius gradient-bound argument. Thus
`laurent_local_trivialization_at` applies at every value outside that union;
it does not assume openness or finiteness. This is a local-triviality result,
not a proof of either critical-value finiteness theorem.

`DrivenPicard` now permits a continuous velocity curve as a Banach parameter.
An arbitrary primitive anchor and a midpoint initial value give two-sided local
solutions. `DrivenLocalODE` supplies actual time rescaling and uniform local time
on compact time/position sets. `DrivenContinuation` proves spatial Lipschitz
control, uniqueness, gluing, and continuation from compact regular-domain control.
`DrivenTransport` derives that control from the path image, velocity bound, and
proper-radius Gronwall estimate. `laurent_complete_C1_path` gives complete lifts
with exact base motion under one-sided base derivatives and velocity continuity
on the closed unit interval; no global extension premise is required.

`DrivenAnalytic` now identifies local driven Picard endpoints by uniqueness
and propagates analytic initial-point dependence along complete trajectories.
`C1FiberTransport` constructs actual endpoint diffeomorphisms, with their inverse
from reversed paths, and rescales arbitrary compact time pieces. Analyticity is
in initial points, not time. `PiecewiseTransport` composes finite chains of
endpoint-matching C¹ pieces. It does not construct a globally parametrized
concatenated curve or assert differentiability at the corners.

`DrivenContinuity` now proves joint initial-point/time continuity using the
continuous local endpoint map and uniqueness. `C1Sweeps` proves that compact
initial sets have compact sweeps contained in the regular ODE domain, both for
a C¹ piece and for a finite chain. No global concatenated-curve derivative at a
corner, semialgebraicity, or integration pairing is asserted.

`LocalTransportHomotopy` projects the jointly continuous curve through the
product trivialization into a chosen reference fiber. It gives an actual
homotopy between the initial coordinate map and the terminal coordinate map
after transport. `TransportHomology` uses mathlib's integral singular homology
and homotopy invariance to prove that the transported class is constant in
these coordinates. Complete C¹ paths and finite chains induce homology
isomorphisms in every degree, and composition agrees with concatenation of
pieces. These local statements require all pieces to stay inside one convex
good neighborhood.

`HomologyTransitions` now proves constant coordinate changes across convex
chart overlaps using straight C¹ paths. `HomologySheaf` glues the resulting
coordinates into a sheaf of integral modules on the entire good-value locus.
The construction proves sheaf gluing, identifies actual module stalks with
actual fiber homology, gives linear germ isomorphisms on each convex chart,
and proves that the underlying étalé projection is a covering map. Its sections
agree with the actual ODE homology maps for paths inside a single chart.

`TimeHomology` and `HomologyLift` now prove the global ODE/covering
comparison. Near each time, the actual homology class has constant coordinates
in a convex chart, by a homotopy obtained from nearby time slices of the
jointly continuous trajectory. It therefore gives a continuous curve of germs
in the module-valued étalé space. Its endpoints are identified with the initial
class and the actual ODE homology image. Covering uniqueness and homotopy
lifting give fixed-endpoint path-homotopy invariance with no differentiability
assumption on the homotopy. `ChainHomologyHomotopy` extends the comparison and
invariance to finite C¹ chains through concatenation and monodromy composition.
Only null-homotopic loops are proved to act trivially. Arbitrary loop monodromy
is retained.

The transport and local-system components over the actual good locus are now
proved. Critical-value finiteness remains unresolved and is required to identify
the manuscript's finite exceptional set. The other principal analytic gaps are
listed below; none follows merely from the constructed topological local system.

Period transport, the separate endpoint Hardt sweep, sublevel/logarithmic
estimates, and residues remain open. Openness of the whole velocity/initial-point
admissible-parameter set has not been asserted and was not needed for the local
product maps.

`NewtonPowers` now proves the full arbitrary-rank Newton-polytope power
identity, including the exact exposed-vertex coefficient argument and finite
vertex-hull recovery. Thus `origin_in_newton_powers` discharges the isolated
origin-preservation obligation. `infinite_of_minimal` requires only the minimal
nonvanishing theorem; the classification and Laurent Mathieu implications are
also ready to consume that theorem, which remains the principal unproved target.
The neighboring
compact-Lie-group project's general-torus DvK dependency must remain deferred.


`face_reduction` in `FaceReduction`
now proves the complete minimal-face reduction. Finite supporting cuts preserve
all power constant terms and terminate with zero interior in the real span;
an integer lattice basis then gives full interior in at most the original number
of variables. The rank-zero alternative is a nonzero constant. The proof
substitution and scalar-extension details are recorded in the coverage ledger.
`minimal_iff_interior_minimal` isolates the still-unproved positive-rank
full-interior analytic theorem. The unimodular vertex chart (`lem:chart`) is now also proved by
`unimodular_vertex_chart` and `unimodular_vertex_chart_evaluation`: explicit
integer weights and transvections give a lattice automorphism, real extension
preserves Newton interior, and shifting the minimum exponent gives an ordinary
polynomial with nonzero constant coefficient. The pointwise torus formula and
all power constant-term identities are checked. `minimal_iff_vertex_minimal`
identifies the full target with the still-open analytic vertex-chart case,
retaining full Newton interior. The listed semialgebraic, integration, period,
and residue-cycle obligations remain open. `ResiduePolydisc` now proves the
zero-free closed polydisc, all strict logarithmic-partial estimates, and nonzero
actual coordinate derivatives at roots, uniformly in the fiber parameter.
`CoefficientSeries` proves convergence of the generating series and its forced
value `1/s` under universal vanishing. `TorusCoefficients` proves normalized
product-Haar coefficient extraction, including products and powers, and
`TorusCauchySeries` identifies the scalar Cauchy transform by dominated
convergence. The comparison with oriented logarithmic-form integration is not
proved. The compact root locus, its continuous injective parametrization in
the actual Laurent fiber, its covering projection with finite fibers, and locally unique complex-smooth
root branches are now checked in `ResidueRootLocus`, `CompactRootCovering`,
`PolynomialRootCharts`, `ResidueCovering`, and `ResidueRootBranches`.
The exact root-counting obligation is now closed by `ResidueCoveringDegree`:
for a proved choice of radius and all sufficiently large fiber values, every
fiber of `residueRootProjection` has `Nat.card` equal to `m 0`. The projection
is surjective and the compact root locus is nonempty. The implementation
replaces the manuscript's Rouché step by the regular deformation
`u(t y₁,y′)`, an endpoint fiber equivalence, and the exact monomial root count.
`ResidueSemialgebraic` now proves semialgebraicity of the actual covering
coordinate image and of the total family with the fiber value as a parameter.
`SemialgebraicSets` uses the standard finite Boolean polynomial-sign definition;
realification and polynomial substitution are proved directly, without
projection or Hardt input. The next residue obligations are
orientation and cycle construction, comparison of logarithmic-form integration
with scalar circle integration, and the residue-period identity including
its sign and normalization. Local smooth root branches are proved; the
associated cycle and homology-class variation still require their integration
and cycle infrastructure.
`TorusMathieu` supplies
the complete finite-Fourier torus implication with minimal nonvanishing still
explicit as its unproved premise.

The core infinity regression is now checked in `AsymptoticExampleNewton`:
`infinityExample_regression` uses the main Laurent representation and proves
Newton interiority together with an ordinary regular value that belongs to
its asymptotic critical set. It has no open premises. This guards against
removing the asymptotic set from the transport argument. The exact metric
formula, hull vertex enumeration, and complete critical-point/value list in
the manuscript remark have not been separately checked.

The real one-dimensional standard-input cases are now proved in
`SemialgebraicLine` and `SemialgebraicLineFamilies`. Polynomial-curve pullbacks
have finite boundary and a finite convex/interval decomposition. For a fixed
semialgebraic description and a degree bound, one bound controls all component
counts and all finite intersection cardinalities, uniformly over arbitrary
curve coefficients. In particular, real line fibers have uniform component
and finite-fiber bounds over their entire parameter space. Zero specializations
and degree drops are included. This does not eliminate the existential torus
coordinates in the radius set and does not supply the higher-dimensional
sphere-family path or Hardt inputs.

`FiniteMultiplicity` now reduces the arbitrary-dimensional uniform count of
finite fibers to coordinate projection and the checked uniform line-fiber
bound. The graph theorem retains both the parameter and target value; the
projection premise remains open. `SemialgebraicMeasurable` gives unconditional
real/complex measurability. `MultiplicityIntegral` proves a Euclidean Jacobian
estimate on given countably many disjoint measurable injective pieces, allowing
a null exceptional target set. Its uniform family theorem combines this with
the conditional fiber bound. The missing integration steps are now more
specific: construct the pieces on strata, prove that infinite-fiber targets
form a negligible set in the required setting, and compare the chart Jacobian
integrals with the manuscript's restricted complex-form densities. These facts
are not inferred from the compiled Euclidean estimate.


`RegularJacobian` and `SemialgebraicJacobian` now close the piece-construction
and negligible-exceptional-target steps for locally C¹ maps between
**equal-dimensional Euclidean spaces**. Nonsingular points have injective open
neighborhoods; second countability and disjointification give measurable
injective pieces. The actual critical image is null by mathlib's Jacobian
critical-image theorem, so regular whole fibers are countable. The interval
cover shows countable real semialgebraic sets are finite; coordinate projection
extends this to finite-dimensional fibers. Thus the flat C¹ family estimate
needs only the open projection premise in addition to its actual graph and
smoothness hypotheses. No countable partition or exceptional-target estimate
is assumed in this new theorem. The theorem permits noncompact parameter sets
and images of infinite measure.

The remaining integration gap is passage from charts on the manuscript's
semialgebraic strata in arbitrary ambient dimension to this Euclidean theorem,
including lower-dimensional strata and the exact restricted complex-form
density. The equal-dimensional critical-image measure theorem here concerns
real integration only. It neither proves asymptotic critical-value finiteness
nor changes the required common-radius route.


The one-dimensional integration input now has an unconditional parametrized
version. `ScalarVariation` bounds absolute derivative integrals uniformly using
the semialgebraic graph's real line fibers. `CurveVariation` applies this to
every coordinate, deriving a uniform speed integral and velocity integrability
for bounded families, with no projection or uniform Lipschitz hypothesis.
`CurveRectifiability` identifies a bound on the actual metric variation via
FTC and partition sums. Curves need only be C¹ on the open interval and
continuous at endpoints; unbounded endpoint velocities are allowed.

This reduces the path-side gap to constructing suitable jointly semialgebraic
model curve families from Hardt/triangulation, bounding their finite regular
piece counts, and matching them with the actual sphere-component endpoints.
It does not prove a decomposition theorem for arbitrary continuous
semialgebraic arcs, does not identify Hausdorff measure with arc length, and
does not discharge either sphere-path obligation.


The finite-model path construction is now proved. `FiniteCoverPaths` gives a
uniform bound on the number of polygonal segments within each component of a
fixed finite closed convex cover. `SimplicialPaths` applies this to every finite
geometric simplicial complex, proves compactness and component finiteness,
bounds the component count by the number of faces, and constructs actual
`C1ArcChain` paths with uniform piece-count and length bounds. The ambient real
normed space need not be finite-dimensional. The face-intersection proof is
documented as a substitution for the manuscript's one-skeleton route.

The remaining model-to-fiber gap is unchanged in substance: construct the
finite model by semialgebraic triangulation, obtain the jointly semialgebraic
Hardt maps, and establish the needed finite regular parametrizations of image
arcs so the checked curve-variation bound applies. A bounded length in the
model does not by itself bound the lengths of its images, and no such inference
is made. Both actual sphere-path obligations remain open.
