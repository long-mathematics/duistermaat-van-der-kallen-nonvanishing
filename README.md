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
`DuistermaatVanDerKallen`; the eighteen modules in `DuistermaatVanDerKallen/` cover:

- Laurent support/separation, the zero-rank case, coordinate invariance, and
  explicitly conditional downstream implications;
- the common-radius pigeonhole argument under explicit geometric hypotheses;
- the tail property for univariate Boolean polynomial inequalities;
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
  the reverse-trajectory identity.

Semialgebraic projection and uniform path bounds, smooth flow dependence,
transport diffeomorphisms, chain integration, periods, residues, and minimal
nonvanishing remain open. No general-rank nonvanishing theorem is being claimed
from the conditional implications. The general-torus dependency in the
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
