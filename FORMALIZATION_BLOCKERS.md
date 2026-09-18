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
  in the checked project. Smooth parameter dependence and the required
  global continuation have not yet been assembled, so this report does not
  claim all ODE infrastructure is absent.
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
   `P_zᵢ − wᵢ² P_wᵢ`: proved. The algebraic `MultiLaurent` representation bridge
   remains open; arbitrary ambient polynomial restrictions are covered.

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

Compactness and the correct metric have been proved for this family. The
remaining path theorem cannot be deduced merely from that compactness:
compact sets in general can have infinitely many components and nonrectifiable
connected pieces. Nor can a separate finite bound for each fixed R,ε supply
uniform N,L. The manuscript's Hardt/model-triangulation/arc-volume proof needs
those missing structural results, even for these sphere fibers.

A valid next development can specialize those structural arguments to this
polynomial family, but must establish uniformity with respect to both parameters
and must not assume bounded derivatives for the Hardt homeomorphisms.

## Why this is a substantive boundary

The missing inputs form a new real-algebraic-geometric foundation, not a missing
rewrite lemma. The available real-closed-field algebra and one-variable
asymptotics do not supply arbitrary-rank existential projection, compact
triangulation, uniform component counts, or the uniform arc-volume estimate.
Developing and auditing those results is a substantial prerequisite project.
The independent semialgebraic chain-integration and period/residue dependencies
also remain open, as itemized in the coverage ledger.

No project axiom has been introduced for any of these facts. The two obligation
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
`PolynomialGradient` now proves actual field smoothness and local ODE existence.
Continue with global ODE continuation and smooth flow dependence, period transport,
the separate endpoint Hardt sweep, sublevel/logarithmic estimates, and residues.

Minimal nonvanishing is still the principal unproved target. The conditional
classification and Laurent Mathieu implications are ready to consume it; infinite
nonvanishing additionally needs Newton-power origin preservation. The neighboring
compact-Lie-group project's general-torus DvK dependency must remain deferred.
