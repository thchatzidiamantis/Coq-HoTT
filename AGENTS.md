# AGENTS.md

Repository-wide guidance for coding agents. A more specific `AGENTS.md` in a
subdirectory takes precedence for files below it.

## Project

HoTT is a Rocq (formerly Coq) library for homotopy type theory. Library sources
live in `theories/`, additional developments in `contrib/`, tests in `test/`,
and developer tooling in `etc/`.

- Preserve the required `-noinit` and `-indices-matter` flags by using the
  project build rather than invoking Rocq with ad-hoc arguments.
- Treat the matrices in `.github/workflows/ci.yml` as the source of truth for
  supported Rocq versions; avoid unnecessary version-specific features.

## Proof Development

- Read `STYLE.md` before changing `.v` files and match the surrounding style.
  In particular, do not hard-wrap prose in Rocq comments.
- Prove results at their natural level of generality: consider arbitrary
  truncation levels, modalities, or reflective subuniverses when appropriate.
- Prefer reusable lemmas over long proofs, and keep intermediate goals readable
  enough for a human to follow. Useful project tactics include `napply`,
  `rapply`, `snapply`, and `srapply`, plus the `lhs`, `lhs_V`, `rhs`, and
  `rhs_V` tacticals (and primed variants) described in `STYLE.md`.
- Preserve intended universe polymorphism while avoiding unnecessary universe
  parameters and constraints. Inspect universe-sensitive definitions with
  `About` or `Print` and `Set Printing Universes.`; add regression checks under
  `test/` when appropriate.

## Working Rules

- Keep changes focused and avoid unrelated formatting or refactoring.
- Do not introduce `Admitted`, `admit`, or new axioms to finish a proof. Follow
  the axiom conventions in `STYLE.md` when axioms are genuinely in scope.
- Do not edit generated files or build products such as `_CoqProject`,
  `Makefile.coq`, `*.vo`, or `_build/`.
- Wire new library files into the existing exports and build structure, usually
  `theories/HoTT.v` and the relevant `dune` stanza.
- Keep commits atomic and self-contained, with tests and implementation grouped
  so that each commit is independently valid.
- Do not stage, commit, or rewrite repository history unless explicitly asked.

## Build and Test

Prefer Dune. Use `dune build` for fast feedback while iterating:

```sh
dune build
```

Before each commit, run the complete validation target; it subsumes the build:

```sh
dune test
```

Use `make -j2` only when a task specifically concerns the Make build or needs
to reproduce that CI path. Finish with `git diff --check` and report what was
and was not validated.

## Rocq MCP

When a Rocq MCP server is available, use it for quick proof inspection and
iteration. Treat it as optional fast feedback and validate final edits with the
normal Dune build and tests.
