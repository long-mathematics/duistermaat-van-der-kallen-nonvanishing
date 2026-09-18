# A Resolution-Free Proof of the Duistermaat--van der Kallen Nonvanishing Theorem

## Abstract

We present a resolution-free semialgebraic proof of the following theorem of Duistermaat and van der Kallen: if the Newton polytope of a nonzero complex Laurent polynomial contains the origin, then infinitely many of its positive powers have nonzero constant term. The principal estimate is a uniform middle-dimensional sublevel bound for the restriction of a holomorphic volume form to a semialgebraic family. Polynomial differentiation and a finite-multiplicity projection estimate prove this bound; a dyadic decomposition then gives absolute integrability of the logarithmic volume form on every middle-dimensional semialgebraic chain on which the Laurent polynomial is bounded. Global cycle transport uses the closed embedding $z\mapsto(z,z^{-1})$, a direct scalar asymptotic-critical-value finiteness argument, and an explicit normalized-gradient ODE. The local residue construction of Duistermaat and van der Kallen identifies the constant-term generating function with a fiber period. A semialgebraic endpoint sweep gives a primitive with a power-law bound, contradicting the simple pole forced by universal positive-power vanishing. The independent Whitney--Thom transport proof is retained in an appendix.

## Preprint and source

- [Preprint PDF](duistermaat_van_der_kallen_nonvanishing.pdf)
- [LaTeX source](duistermaat_van_der_kallen_nonvanishing.tex)

This repository is the canonical development location for the research draft and its Lean formalization. The manuscript is a research draft for adversarial mathematical audit and is not yet formally verified.

## Proof architecture

The main global transport argument identifies $(\mathbb C^\times)^d$ with the closed smooth affine variety
`{(z,w) : z_j w_j = 1}` in $\mathbb C^{2d}$. The induced Euclidean radius is proper, so both $|z_j|\to\infty$ and $|z_j|\to0$ count as escape.

A compact-family **uniform connecting-path lemma** is proved from Hardt triviality, compact semialgebraic triangulation, and the manuscript's existing uniform one-dimensional volume bound. Applied to the small-gradient sets on a common large sphere, it gives a direct pigeonhole proof that the scalar asymptotic critical-value set is finite. This avoids importing a separate generalized Bertini--Sard theorem or an asymptotic power-rate theorem.

Away from the finite ordinary/asymptotic bad-value set, the scalar holomorphic target gives an explicit minimal-norm lift

$$
V_a(z)_i=
\frac{a\,\overline{\partial_i f(z)}}
{(1+|z_i|^{-4})\lambda(\Phi(z))^2}.
$$

The uniform lower bound on $(1+r)\lambda$ gives at-most-linear growth. Gronwall bounds the proper radius, while the same lower bound keeps the trajectory uniformly inside the regular ODE domain. This yields complete path transport, smooth local trivializations, and holomorphic continuation of the fiber period.

Hardt triviality is used separately again near zero to choose semialgebraic representatives and construct the endpoint sweep. The smooth ODE flow transports the homology class; it is not asserted to be semialgebraic.

The earlier projective-graph / complex Whitney-stratification / Thom-isotopy argument is preserved in an appendix as an independent alternate route to the finite-exceptional-set and topological transport conclusion. It is not a dependency of the main proof.

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

**Incomplete foundation checkpoint.** The arbitrary-rank DvK theorem and its
Mathieu corollaries are not yet formally proved. The manuscript remains unchanged.

The project uses Lean 4.34.0 and pinned mathlib. Its root module is
`DuistermaatVanDerKallen`; the 113 modules in `DuistermaatVanDerKallen/` cover:

- Laurent support/separation, the zero-rank case, coordinate invariance, and
  the full arbitrary-rank Newton-polytope power identity, and the complete
  minimal-face reduction with lattice coordinates and all power constant terms
  preserved. The full unimodular vertex chart gives an ordinary polynomial
  factor with nonzero constant coefficient and its exact torus evaluation.
  Minimal nonvanishing reduces to the positive-rank full-interior chart case,
  which remains unproved. Infinite nonvanishing
  now follows conditionally from the minimal theorem alone; classification and
  the Laurent Mathieu property also remain conditional on that theorem;
- the common-radius pigeonhole argument under explicit geometric hypotheses;
- the tail property and global finite interval decomposition for univariate
  Boolean polynomial inequalities; uniform component counts and finite-fiber
  cardinal bounds for real one-dimensional semialgebraic fibers, with all
  parameters retained and no boundedness assumption;
- measurable real/complex semialgebraic sets; uniform finite-fiber counts in
  arbitrary dimension conditional on projection; and a uniform Euclidean C¹
  family Jacobian estimate using actual derivatives. Projection remains an
  explicit open premise; measurable injective pieces and almost-everywhere
  finite fibers are now derived. Manifold-stratum and form-density integration
  remain open;
- smoothness of each continuous semialgebraic scalar or Euclidean curve
  outside a finite set of interior parameter values, derived from nonzero
  polynomial relations and simple-root implicit functions. Uniform exceptional
  counts across families and endpoint C¹ reparametrizations remain open;
- uniform variation and rectifiable-length bounds for supplied bounded
  semialgebraic curve families, C¹ in the interval interior. These use real
  line-fiber counts without projection or uniform Lipschitz assumptions;
  construction of connecting curves in the actual fibers remains open;
- compactness, finite component counts, and uniform polygonal C¹ connecting
  chains for a fixed finite simplicial model. Semialgebraic triangulation and
  transport of these model paths through Hardt maps remain open;
- the proper L2 affine-torus radius, compact sublevels, weighted scalar lift
  identities, an abstract uniform-gradient bound, and Gronwall/regular-domain control;
- compactness of the actual small-gradient sphere family and precise unproved
  semialgebraic obligations;
- the smooth torus chart, its tangent subspace and induced metric, the actual
  restricted differential norm, and the minimal scalar lift;
- analytic polynomial partials, joint smoothness of the normalized-gradient
  vector field, and local ODE existence inside its regular domain;
- an algebra-homomorphic Laurent evaluation and explicit ambient polynomial
  representatives, connecting the analytic results to `MultiLaurent`;
- the uniform gradient theorem for Laurent polynomials, the exact base equation
  and Gronwall estimate on existing curves, and compactness of the controlled
  region inside the actual coordinate ODE domain;
- compact-domain continuation and complete existence along every segment
  avoiding the ordinary/asymptotic critical values, including uniqueness and
  the reverse-trajectory identity;
- fiber transport homeomorphisms, uniform Lipschitz dependence on initial
  points for bounded proper radius, joint continuity in initial point and time,
  and compact sweeps of compact initial sets;
- smoothness of the actual field on Banach spaces of continuous curves, a
  bounded primitive operator, and a regular analytic Picard branch on an open
  parameter neighborhood of zero time scale, jointly in velocity and initial
  point, with its integral equation yielding actual scaled ODE trajectories;
- analytic dependence of the chosen complete segment transport on admissible
  velocity, initial-point and time parameters, with analytic ambient extensions
  of the forward and inverse fiber maps near every point;
- analytic real-manifold structures on regular fibers of dimension `2d - 2`,
  and the assembled complete-segment lemma with the actual transport
  diffeomorphism, exact base motion, and compact sweeps;
- smooth local product trivializations over the actual good-value locus, with
  base-coordinate preservation and compact sweeps of compact parameter sets.
  Openness of that locus is proved by proper-radius compactness; finiteness of
  the critical-value sets remains open;
- complete horizontal lifts of C¹ base paths, with exact base motion, using
  continuous driving velocities, two-sided local existence, uniqueness, and
  proper-radius compact control before continuation;
- real analytic endpoint diffeomorphisms along C¹ paths, inverted by time
  reversal, and their finite composition for endpoint-matching C¹ pieces.
  Analytic dependence is in the initial point; the driving velocity remains
  merely continuous in time;
- joint continuity and compact sweeps for C¹ paths and finite chains, together
  with actual integral singular-homology isomorphisms in every degree, finite
  composition, and agreement with local product coordinates inside a convex
  good neighborhood;
- constant coordinate transitions on convex overlaps, a global sheaf of
  integral homology modules on the good-value locus, linear identification of
  its actual stalks with fiber homology, linear germ isomorphisms on every
  convex patch, and a covering étalé space for its underlying set sheaf.
  ODE homology classes give continuous lifts in the module-stalk covering
  along arbitrary C¹ paths. Actual homology transport along finite C¹ chains
  agrees with covering monodromy and is invariant under arbitrary continuous
  fixed-endpoint homotopies in the good locus;
- a zero-free closed polydisc and strict logarithmic-derivative estimates for
  the local residue equation, including nonzero actual coordinate derivatives
  at roots; convergence of the constant-term generating series; exact
  normalized product-Haar coefficient extraction and its scalar Cauchy formula;
- the finite-Fourier compact-torus Mathieu implication, conditional on the
  still-unproved minimal nonvanishing theorem. The residue-cycle identity
  and oriented-form comparison remain open;
- compact residue root loci and their actual projections as coverings with
  finite fibers, together with locally unique complex-smooth root branches as
  the fiber value and remaining coordinates vary;
- the exact positive sheet count of the residue covering, including
  surjectivity and nonemptiness, by a regular deformation to a monomial
  equation;
- semialgebraicity of the actual compact residue covering image and its total
  family in the complex fiber parameter, via explicit real polynomial
  equalities and inequalities. The oriented residue cycle and its integration
  identity remain open;
- semialgebraicity of the exact small-gradient family with both radius and
  threshold as free coordinates, and of the proper-radius incidence set.
  Its exact projection is the manuscript radius set. The tail conclusion is
  proved conditionally on the still-unproved real projection theorem;
- tangent-velocity, restricted-derivative, and integrated path estimates on the
  small-gradient spheres, summed over finite C¹ pieces. The common-radius
  proof now yields finiteness of the actual Laurent asymptotic critical-value
  set conditionally on projection and a uniform finite-C¹-chain input. Both
  inputs remain unproved;
- ordinary critical values embed into the asymptotic critical values of a
  polynomial with one unused torus coordinate. Thus both critical-value sets
  and their union are finite under the same two geometric inputs; no separate
  critical-locus decomposition premise is needed;
- the manuscript's example `c+x+(y-1)²/(xy)`: for every c, the same Laurent
  polynomial has Newton interiority, c is an asymptotic critical value in the
  proper induced metric, and c is an ordinary regular value. The proof also
  verifies invariance of the restricted differential under a change of ambient
  polynomial representative.

Semialgebraic projection and uniform path bounds, critical-value finiteness,
chain integration, periods, residues, and minimal nonvanishing remain open. No general-rank nonvanishing theorem is
being claimed from the conditional implications. The general-torus dependency in the
compact-Lie-group project remains deferred.

```sh
python3 scripts/fetch_mathlib_cache.py
lake build
python3 scripts/audit_sources.py
python3 scripts/audit_coverage.py
lake env lean scripts/AxiomAudit.lean
lake env lean scripts/CheckTargets.lean
```

The audit checks all project declarations by defining module, including generated
and private declarations. Only mathlib's standard `propext`, `Classical.choice`,
and `Quot.sound` may occur as transitive axioms. CI repeats the checks from a clean
checkout. Target-proposition definitions and conditional proofs do not establish
their missing premises.

See [the exhaustive coverage ledger](FORMALIZATION_STATUS.md),
[the precise formalization boundary](FORMALIZATION_BLOCKERS.md), and
[local validation results](scripts/validation.txt).
The Whitney–Thom appendix is optional and excluded from this checkpoint; it has
not been substituted for the required direct scalar proof.

## Author

Christopher D. Long

Email: galizur@gmail.com
