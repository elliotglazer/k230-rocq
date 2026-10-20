# K230: a 230-state Turing machine for the consistency of ZFC

This repository contains a binary Turing machine and two separate Rocq developments.
The axiom-free verification proves

```text
the machine halts from the blank tape  <->  ZFC proves a contradiction.
```

The classical development proves that PA proves the corresponding arithmetical
equivalence, `Nonhalt(K230) ↔ Con(ZFC)`. It uses excluded middle and choice in
Rocq, followed by first-order completeness. It establishes the existence of a PA
derivation; it does not export a PA or MM0 proof certificate.

| Development | Final result | Rocq assumptions | Build |
| --- | --- | --- | --- |
| Axiom-free verification | Machine halting iff ZFC has a contradiction proof | None in either final theorem | `python build.py --coqchk` |
| [Classical PA-provability](classical/README.md) | `PA ⊢ Nonhalt(K230) ↔ Con(ZFC)` | Excluded middle, dependent unique choice, relational choice | `python classical/build.py --coqchk --jobs 2` |

Both developments use Rocq 9.1.0 and rocq-stdlib 9.0.0, with separate build outputs
and CI workflows. The axiom-free theorem passed a clean development build
and a second clean build using this repository's portable script. Each build
compiled all 216 proof sources and reported both final declarations closed
under the global context, with no axioms. See [provenance.json](provenance.json).

The machine has 230 working states, numbered 0 through 229, and a separate halt
state numbered 230. It starts in state 0 on an all-zero tape. The exact table is
[machine/k230.tm](machine/k230.tm), with SHA-256

```text
e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8
```

## Axiom-free verification

The final declarations are in [Correct230.v](coq/tm/Correct230.v):

```coq
Theorem tm230_halts_iff_ZFC_inconsistent :
  K230.TM230.TM230.halts K230.TM230.tm K230.TM230.TM230.c0 <->
  StandardZFC ⊢TC ⊥.

Corollary tm230_nonhalting_iff_ZFC_consistent :
  (~ K230.TM230.TM230.halts K230.TM230.tm K230.TM230.TM230.c0) <->
  ~ (StandardZFC ⊢TC ⊥).
```

`StandardZFC` is the reference first-order ZF theory with Foundation and Choice.
The right side refers to a finite derivation in its classical first-order proof
system. See [KQuotZFC.v](coq/settheory/KQuotZFC.v) for its definition.

These are external Rocq theorems. They do not assert that ZFC is consistent.
The separate [classical development](classical/README.md) establishes the
internal PA-provability result. The local proof sources for the axiom-free
verification introduce no Rocq axioms or admitted proofs. The final
[assumption audit](coq/tm/AuditCorrect.v) checks that both declarations are closed
under the global context. Object-level classical logic and the axioms of ZFC are
represented as syntax, not imported as assumptions of Rocq.

One upstream utility, BusyCoq's `LibTactics.v`, declares `inj_pair2`, imports
`Stdlib.Logic.ProofIrrelevance.proof_irrelevance` and
`Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq`, and defines a `skip` tactic using
`admit`. Neither final theorem depends on these axioms or uses that tactic.
`coqchk -o` lists axioms present in the loaded environment; `Print Assumptions`
reports the actual dependencies of each theorem. Both final dependency reports
are closed under the global context.

## Classical PA-provability

The endpoint
[`PA_proves_literal230_ZFC_consistency`](classical/coq/PAModel/PALiteralZFCConsistency.v)
proves derivability of a closed arithmetic sentence from `PA.PAeq`. The sentence
states that this exact machine does not halt iff ZFC is consistent. The proof
first establishes the equivalence in arbitrary PA models, including models with
nonstandard numbers and internally finite proof or run histories. Classical
first-order completeness then yields a PA derivation.

The final theorem's Rocq assumption report lists exactly
`Classical_Prop.classic`,
`ClassicalUniqueChoice.dependent_unique_choice`, and
`RelationalChoice.relational_choice`. These are assumptions of the Rocq
metatheory, not additional axioms of the object theory PA. This development has
its own source manifest, build directory, and Linux kernel check. See its
[build instructions and proof outline](classical/README.md).

## The theory K

K replaces explicit rank machinery with one set-theoretic axiom schema. Its
ordinary first-order presentation uses membership and equality. For any formula
`φ(y,p,q)`, where `q` is a finite tuple of parameters, write

```text
p ⊆ u     := ∀z (z ∈ p → z ∈ u).
Wφ(p,C)   := (∃y φ(y,p,q)) → ∃y (y ∈ C ∧ φ(y,p,q)).
Hφ(C)     := ∀u (u ∈ C →
               ((∃p φ(u,p,q)) ∧ ∀p (p ⊆ u → Wφ(p,C)))).
```

The theory contains the universal closures of

```text
∀a ∀x ∃C ((φ(x,a,q) → x ∈ C) ∧ Hφ(C)),
```

together with the equality axioms. Thus `C` contains the specified output `x`
when `φ(x,a,q)` holds; every member of `C` is an output of `φ`; and `C` supplies
witnesses whenever an input is a subset of one of its members. The condition
`Hφ(C)` is required even when `φ(x,a,q)` is false.

This presentation is named `KPrimeOrd` in the proof. The machine's falsity
encoding uses `KPrimeOrdIR`, which also includes irreflexivity,
`∀x ¬(x ∈ x)`. Both theories are proved equiconsistent with `StandardZFC`.
Tagged constructions and an extensional quotient recover the required set
theory; the reverse interpretation uses constructible-hierarchy reflection.
See the [proof overview](docs/proof-overview.md) and the formal definitions in
[KPrimeCore.v](coq/settheory/KPrimeCore.v) and
[KPrimeTheory.v](coq/settheory/KPrimeTheory.v).

## Reproduce the axiom-free check

Install Python 3.9 or later and Git. The pinned proof toolchain is **Rocq 9.1.0,
rocq-stdlib 9.0.0, and OCaml 4.14.2**. For an opam installation, use an OCaml
4.14.2 switch and install both exact package versions:

```sh
opam install coq.9.1.0 rocq-stdlib.9.0.0
```

The compiler and standard library have independent versions. Installing
`rocq-stdlib 9.1.0` does not reproduce this build. In an activated opam
environment, run:

```sh
python fetch_dependency.py
python build.py --coqchk --require-opam-stdlib
```

Use `python3` if that is the Python command on your system. If `coqc` is not on
your path, use `python build.py --coqc /path/to/coqc` or set `COQC`. On Windows,
place this checkout on the same drive as the Rocq installation. For a native
Rocq Platform installation without opam metadata, omit `--require-opam-stdlib`.
The build still checks the exact compiler version and compiles a standard-library
API probe before starting the proof. That probe detects the incompatible
`FinFun.Injective` change; it is not a claim to recover a package version from
an installation without version metadata.

The dependency is pinned to
[`jeff87654/busy-beaver` at `c132d7eae8158cd3a9850ea3eb7251158c3dd821`](https://github.com/jeff87654/busy-beaver/tree/c132d7eae8158cd3a9850ea3eb7251158c3dd821).
Only the 115 upstream proof files listed in [manifest.json](manifest.json) enter
the build. To use an existing checkout at that commit, run:

```sh
python build.py --reference /path/to/busy-beaver
```

The script checks every source hash and all 460 transitions, copies the required
sources into `.build`, and recompiles all 216 proof files. It never reads
precompiled objects from the dependency checkout. Success requires both final
assumption reports to say `Closed under the global context`, with no reported
axioms. The result and compiler output are saved in `.build/verification-result.json`
and `.build/verification.log`. With `--coqchk`, the script additionally checks
`K230.Correct230` and all its dependencies using the independent kernel checker,
without `-admit` or `-norec`. Its output is saved in `.build/coqchk.log`, including
the environment's axiom summary. Use `--coqchk-command /path/to/coqchk` if needed.

To check the toolchain before fetching or compiling proof dependencies:

```sh
python build.py --check-toolchain
```

For a fast check of the pinned inputs without compiling:

```sh
python build.py --check-only --reference /path/to/busy-beaver
```

The [axiom-free Linux workflow](.github/workflows/verify.yml) installs the pinned opam
packages, verifies the installed standard-library version, rebuilds every proof
source, and runs `coqchk`. It preserves the build reports and logs as a workflow
artifact. The recorded local builds used the Windows Rocq Platform distribution;
an independent external audit also reports a successful Linux rebuild and kernel
recheck. A macOS run has not been recorded.

To build and independently kernel-check the classical result with the same
toolchain and fetched dependency, install its additional Equations dependency
and run:

```sh
opam repository add rocq-released https://rocq-prover.org/opam/released
opam install rocq-equations.1.3.1+9.1
python classical/build.py --coqchk --jobs 2 --require-opam-dependencies
```

Its outputs are under `.build/classical`. The root build does not import these
objects or the classical proof sources. The
[classical Linux workflow](.github/workflows/classical.yml) runs this check
separately. Native Rocq Platform users can omit `--require-opam-dependencies`;
the builder still checks the compiler, standard-library API, and Equations
availability before compiling the proof.

## Proof structure

The [proof overview](docs/proof-overview.md) describes the compact set theory and
the chain from the literal transition table to ordinary ZFC. The principal files
are:

- [Table230.v](coq/tm/Table230.v), [TM230.v](coq/tm/TM230.v), and
  [Sim230Main.v](coq/tm/Sim230Main.v) for the exact machine and its simulation.
- [Main230.v](coq/prog/Main230.v) for the program-to-enumerator connection.
- [Seed230.v](coq/logic/Seed230.v) for the actual nonzero initial search state.
- [Bridge230.v](coq/logic/Bridge230.v) for the numerical proof calculus.
- [KQuotZFC.v](coq/settheory/KQuotZFC.v) and
  [KUpperConsistency.v](coq/settheory/KUpperConsistency.v) for both consistency
  reductions.

## Relation to earlier constructions

The machine and proof-search architecture build on the work of
[Mira](https://github.com/mira-emmy/busy-beaver/tree/zf253-exact-equivalence) and
[Vladimir Reshetnikov's ProveIt project](https://github.com/VladimirReshetnikov/ProveIt).

The main mathematical improvement here is the compact theory K and its more
efficient axiom encoding. Its interpretation retains the consistency strength
of ZFC while reducing the theory that the machine's proof checker must recognize.
Changes to source scheduling, compiler sharing, and the transition table also
contributed to the state count. The proof checks the released table and
source-program certificate directly.

The compiler work also builds on
[Andrew James Wade's Turing Machine Explorer](https://codeberg.org/ajwade/turing_machine_explorer).
The compiler is not needed to verify the frozen table, but its provenance and
MIT No Attribution notice are preserved here.

[Jeff's busy-beaver project](https://github.com/jeff87654/busy-beaver) supplies the
Rocq reference development on which this verification builds. The local proof
adds the K interpretation, both consistency reductions, the numerical decoding
bridge, and the checked connection to this exact machine. The attribution below
identifies reused and adapted proof components.

## Attribution and licensing

The development uses and adapts parts of the pinned reference proof by
`jeff87654`, which verifies Mira-Cult's 254-state construction. It also uses the
reference's vendored BusyCoq and Coq Library of Undecidability sources. See
[THIRD_PARTY.md](THIRD_PARTY.md) for the file-level attribution and the license
scope. Existing MIT, MIT X11, MIT No Attribution, and MPL 2.0 notices are preserved
in [LICENSES](LICENSES).
No repository-wide license is asserted for the custom upstream or adapted files
whose licensing is not specified at the pinned source.
