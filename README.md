# K230: a 230-state Turing machine for the consistency of ZFC

This repository contains a binary Turing machine and a Rocq proof of the equivalence

```text
the machine halts from the blank tape  <->  ZFC proves a contradiction.
```

**Verified with Rocq 9.1.** The complete theorem passed a clean development build
and a second clean build using this repository's portable script. Each build
compiled all 216 proof sources and reported both final declarations closed
under the global context, with no axioms. See [provenance.json](provenance.json).

The machine has 230 working states, numbered 0 through 229, and a separate halt
state numbered 230. It starts in state 0 on an all-zero tape. The exact table is
[machine/k230.tm](machine/k230.tm), with SHA-256

```text
e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8
```

## What the theorem says

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

These are external Rocq theorems. They do not assert that ZFC is consistent, and
they are not an internal formalization of `PA ⊢ Nonhalt(K230) ↔ Con(ZFC)`.
The local proof sources introduce no Rocq axioms or admitted proofs. The final
[assumption audit](coq/tm/AuditCorrect.v) checks that both declarations are closed
under the global context. Object-level classical logic and the axioms of ZFC are
represented as syntax, not imported as assumptions of Rocq.

One upstream utility, BusyCoq's `LibTactics.v`, declares an `inj_pair2` axiom and
defines a `skip` tactic using `admit`. Those declarations are not used by the
final proofs. The endpoint audit checks the actual dependencies of both final
theorems, rather than asserting that every loaded upstream file is free of
unrelated axiom declarations.

## Reproduce the check

Install Python 3.9 or later, Git, and Rocq 9.1 with its standard library. Then run:

```sh
python fetch_dependency.py
python build.py
```

Use `python3` if that is the Python command on your system. If `coqc` is not on
your path, use `python build.py --coqc /path/to/coqc` or set `COQC`. On Windows,
place this checkout on the same drive as the Rocq installation.

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
and `.build/verification.log`.

For a fast check of the pinned inputs without compiling:

```sh
python build.py --check-only --reference /path/to/busy-beaver
```

The proof development has been checked with the Windows distribution of Rocq
9.1. The release scripts use portable Python and Git commands; a Linux or macOS
run has not yet been recorded.

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

The 230-state version changes one unconditional logical-axiom row of the
231-state source from `rho6(a,b)` to `rho6(a,c)`. This changes the compiled machine
while enumerating the same axiom family. The proof checks the resulting table
and source-program certificate directly.

## Relation to earlier constructions

The machine and proof-search architecture build on the work of
[Mira](https://github.com/mira-emmy/busy-beaver/tree/zf253-exact-equivalence) and
[Vladimir Reshetnikov's ProveIt project](https://github.com/VladimirReshetnikov/ProveIt).

The main mathematical improvement here is the compact theory K and its more
efficient axiom encoding. Its interpretation retains the consistency strength
of ZFC while reducing the theory that the machine's proof checker must recognize.
Later changes to source scheduling, compiler sharing, and the transition table
also contributed to the state count. The one-state reduction from 231 to 230 is
the logical-row parameter change described above.

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
