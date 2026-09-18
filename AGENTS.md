# Repository instructions

The canonical mathematical source is `duistermaat_van_der_kallen_nonvanishing.tex`. Compile it with:

```sh
latexmk -pdf duistermaat_van_der_kallen_nonvanishing.tex
```

Check for undefined references and citations if the manuscript changes. The compiled PDF may be tracked; LaTeX auxiliaries may not.

## Mathematical integrity

The manuscript is a research draft for adversarial mathematical audit. Treat it as the mathematical source of truth unless the user explicitly approves a correction.

- Do not silently change theorem, proposition, lemma, corollary, definition, standard-input statement, hypothesis, conclusion, notation, or parameter range.
- Do not silently repair a suspected mathematical error. Flag it, explain it, and preserve a restart point.
- Distinguish manuscript mathematics, Lean formalization, proof substitutions, and editorial/repository changes.
- When replacing a manuscript proof by a Lean-friendlier proof, prove the same statement and document the substitution.
- Inspect downstream results whenever a mathematical statement or proof dependency changes.

## Lean formalization target

The primary target is the full arbitrary-rank resolution-free Duistermaat--van der Kallen nonvanishing theorem, with the manuscript's minimal nonvanishing theorem as the principal analytic theorem and the following downstream results as formalization targets:

1. infinite nonvanishing;
2. Newton-polytope classification of universal constant-term vanishing;
3. Laurent-polynomial Mathieu property;
4. compact-torus Mathieu property for finite Fourier sums.

Do not replace the resolution-free proof by Hironaka/resolution-of-singularities machinery unless explicitly instructed.

The manuscript states semialgebraic, stratified-topological, integration, Whitney-stratification, and Thom-isotopy inputs explicitly. Do not turn missing infrastructure into project axioms. Search mathlib first; if a required foundation is absent, isolate the smallest exact missing theorem, record a type-correct target when possible, and distinguish a library blocker from a mathematical gap.

## Formalization discipline

All project Lean proof work must be free of `sorry`, `admit`, project-added axioms, unsafe proof escapes, `native_decide`, `implemented_by`, and `extern` proof substitutes. Use mathlib and kernel-checked proofs.

Maintain an exhaustive coverage ledger in `FORMALIZATION_STATUS.md`. A partial or conditional statement is never PROVED coverage of a stronger manuscript statement. Record proof substitutions and unresolved dependencies explicitly.

Before a formalization milestone is merged:

- run a full `lake build`;
- audit project-owned Lean sources for proof placeholders and added axioms;
- audit the transitive axioms of project theorem declarations;
- ensure the README's coverage claims agree with the ledger.

## Repository organization

Keep the descriptive manuscript filenames at repository root, following the `long-mathematics` convention. Lean root modules and their module directories should also live at repository root once the formalization is initialized. Put verification, audit, target-checking, and other auxiliary tooling under `scripts/`. Put GitHub Actions workflows under `.github/workflows/`.

Use feature branches, stable checkpoint commits, pull requests, passing CI, and squash merges for substantive work. Keep `main` releasable and buildable.
