# Classical proof of PA-provability

This development proves

```text
PA ⊢ Nonhalt(K230) ↔ Con(ZFC).
```

`K230` is the exact 230-state, two-symbol machine in
[`../machine/k230.tm`](../machine/k230.tm), started in state 0 on the all-zero
tape. It has 230 working states and a separate halt state numbered 230. The
machine's SHA-256 digest is

```text
e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8
```

The endpoint is
[`PA_proves_literal230_ZFC_consistency`](coq/PAModel/PALiteralZFCConsistency.v)
in the logical module `PAModel.PALiteralZFCConsistency`. Its type is the
classical first-order derivability predicate `FullND.tprv` with theory
`PA.PAeq` and conclusion `literal230_ZFC_comparison_sentence`. That closed
arithmetic sentence expresses nonhalting of the literal machine iff there is
no numerical ZFC proof of a contradiction.

## What is classical here

The final theorem's `Print Assumptions` report contains exactly

```text
Classical_Prop.classic
ClassicalUniqueChoice.dependent_unique_choice
RelationalChoice.relational_choice
```

These belong to the Rocq metatheory. The object theory remains PA with equality;
it does not acquire these additional axioms. The proof establishes validity in
every PA model, then uses classical first-order completeness to prove the
existence of a PA derivation. It does not produce an explicit PA sequent
calculus derivation or an MM0 certificate.

The [axiom-free verification](../README.md#axiom-free-verification) is a separate
development with a separate endpoint and assumption audit. Its root build
continues to require both final declarations to be closed under the global
context. Classical proof sources and objects do not enter that build.

## Build and independently check

Run these commands from the repository root. Install Python 3.9 or later, Git,
and the pinned toolchain: Rocq 9.1.0, rocq-stdlib 9.0.0, and OCaml 4.14.2.
In an OCaml 4.14.2 opam switch:

```sh
opam install coq.9.1.0 rocq-stdlib.9.0.0
python fetch_dependency.py
opam exec -- python classical/build.py --coqchk --jobs 2 --require-opam-stdlib
```

Use `python3` if required by your installation. The standard-library version is
independent of the compiler version. Installing rocq-stdlib 9.1.0 changes the
library API and does not reproduce this build.

`--jobs` limits the number of compiler processes running at once. The examples
use two to limit memory use; the Linux workflow uses four. Adjust this value to
the available memory and CPU capacity.

For native Rocq Platform installations without opam metadata, omit
`--require-opam-stdlib`. The builder still checks the compiler version and
compiles the standard-library API probe. If needed, supply `--coqc /path/to/coqc`
and `--coqchk-command /path/to/coqchk`. On Windows, keep the checkout and Rocq
installation on the same drive.

The pinned reference is
[`jeff87654/busy-beaver` at `c132d7eae8158cd3a9850ea3eb7251158c3dd821`](https://github.com/jeff87654/busy-beaver/tree/c132d7eae8158cd3a9850ea3eb7251158c3dd821).
To use an existing checkout at that commit:

```sh
python classical/build.py --reference /path/to/busy-beaver --coqchk --jobs 2
```

For a toolchain check without a proof build, or an input check without compiling:

```sh
python classical/build.py --check-toolchain --require-opam-stdlib
python classical/build.py --check-only --reference /path/to/busy-beaver
```

[`manifest.json`](manifest.json) pins all 2,442 source modules and their
compilation dependencies. Of these, 2,409 are under `classical/coq`, 19 reuse
existing public sources from the axiom-free development, and 14 are fetched
unchanged from the pinned reference. [`provenance.json`](provenance.json)
records each source's origin and its relationship to the verified development.
The builder checks every input hash and all 460 transitions,
copies source files into `.build/classical`, and compiles them there. It does
not reuse precompiled objects from the reference checkout or the axiom-free
build. It checks the endpoint's assumption report against the three names
above. With `--coqchk`, it recursively checks the endpoint and all its
dependencies using the independent kernel checker, without `-admit` or
`-norec`.

Build results and logs are saved under `.build/classical`. The separate
[Linux workflow](../.github/workflows/classical.yml) installs the exact pinned
packages, runs the build infrastructure tests, rebuilds the proof, and runs
`coqchk`. It uploads the reports and logs even when a step fails. The
[axiom-free workflow](../.github/workflows/verify.yml) retains its own build and
assumption check.

## Proof outline

The argument works in an arbitrary model of `PA.PAeq`, without assuming that its
natural numbers are standard.

1. Arithmetize formulas, proofs, K's axiom recognition, and numerical proof
   search inside the PA model. Prove the K consistency comparison with the
   numerical source ZFC theory in both directions.
2. Prove that the actual program implements this numerical search, including
   its axiom-checking action and its internally finite register histories.
3. Connect that program to the literal transition table and its arithmetical
   run predicate. These steps give
   `literal230_nonhalting_ZFC_consistency` in every PA model.
4. Prove that the closed comparison sentence has the intended meaning in each
   model. Classical completeness, with the equality interpretation, gives
   `PA_proves_literal230_ZFC_consistency`.

Internally finite proof and run lengths can be nonstandard elements of the PA
model. The argument does not replace them with externally finite histories or
assume the model's arithmetic is sound.

The compact theory K and the released machine are described in the
[root README](../README.md#the-theory-k). Source attribution and the scope of
upstream licenses are recorded in [THIRD_PARTY.md](../THIRD_PARTY.md).
