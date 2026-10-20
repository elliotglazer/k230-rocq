# Attribution and license scope

The reference source is
[`jeff87654/busy-beaver`](https://github.com/jeff87654/busy-beaver/tree/c132d7eae8158cd3a9850ea3eb7251158c3dd821)
at commit `c132d7eae8158cd3a9850ea3eb7251158c3dd821`. Its `ZF` development verifies
Mira-Cult's 254-state construction and supplies the logical and set-theoretic
reference libraries used here.

Unchanged upstream proof sources are retrieved separately. The axiom-free
build's `manifest.json` and the classical build's `classical/manifest.json`
list their required upstream paths and SHA-256 digests. Each build compiles
copies without modifying the reference checkout. The classical development
also reuses local sources from the axiom-free verification; these remain
subject to the attribution and license scope stated here.

## Preserved notices

- The reference's BusyCoq sources carry the MIT license, copyright 2023
  Maja Kądziołka. The notice is preserved in
  [LICENSES/BusyCoq-MIT.txt](LICENSES/BusyCoq-MIT.txt).
- Its LibTactics source carries the MIT X11 notice, copyright 2018
  Arthur Charguéraud, including the additional name-use paragraph. The complete
  notice is preserved in
  [LICENSES/LibTactics-MIT-X11.txt](LICENSES/LibTactics-MIT-X11.txt).
- Its Coq Library of Undecidability sources carry the Mozilla Public License
  2.0. The complete text is preserved in
  [LICENSES/Undecidability-MPL-2.0.txt](LICENSES/Undecidability-MPL-2.0.txt).
- Andrew James Wade's compiler sources carry MIT No Attribution, copyright
  2025 Andrew James Wade. The reference generator preserves that notice in
  `ZF/generator/LICENSE.wade`; its complete text is retained in
  [LICENSES/Wade-MIT-0.txt](LICENSES/Wade-MIT-0.txt).
- Rocq and its standard library are separately installed dependencies with
  the notices supplied by their distributions.
- The classical build also requires the separately installed
  [Equations plugin](https://github.com/rocq-prover/equations/tree/v1.3.1-9.1),
  whose distribution supplies its LGPL notice. No Equations source files are
  vendored here.

No root license or explicit license notice was found in the pinned reference's
custom `ZF/m254`, `ZF/stdzf/coq`, `ZF/stdzf_r3/zfc`, or `ZF/stdzf_r3/regcon`
sources. The notices above do not assign a license to those custom files or to
the portions adapted from them. This repository does not assert a blanket MIT
or other repository-wide license. Attribution and source availability do not
by themselves resolve that license scope.

## Adapted files

- `coq/tm/TM230.v`, `Zip.v`, and `Boot230.v` adapt the reference's `TM254.v`,
  `Zip.v`, and `Boot.v`. The bootstrap uses the K230 table, step count, and
  register values. `RM.v` and `RMEquiv.v` reuse its generic register-machine
  semantics.
- `coq/tm/Prog230.v` uses the reference program representation and
  well-formedness checker. The generated tree and witnesses are K230's.
  `Table230.v` contains the frozen K230 table.
- The program layer ports `m254/prog/Bisim.v`, `ProgLib254.v`, and
  `L2Root254.v`, adds the local loop-rotation proof, and checks the K230
  source-program certificate. The reference certificate generator is not
  part of the trusted proof.
- The numerical calculus and enumeration files adapt `Codes254.v`,
  `Thm254.v`, `Enum254.v`, `L1_Sound254.v`, `L1_Comp254.v`, `CD254.v`,
  `Comp_Prop254.v`, the generic part of `Comp_Bundle254.v`, and `Sound254.v`.
  The K schema, its decoding, and the nonzero-seed theorem are local additions.
- `KOrderedPair.v` imports `S_raw.op_inj`. Its construction and the `KQuot`
  files adapt the reference ordered-pair and bisimulation arguments to the
  tagged domain and the local bounded-relation theorem. Imported `OP0` and
  `App0` retain the reference raw-code convention.
- `KQuotFormula.v` adapts `S_quot.qt_inv`. `KQuotDeduction.v` adapts
  `S_qt.qt_prv` and `RegCon.Rel.rel_prv`, with a moving marker parameter and
  domain-restricted quantifiers. `KUpper*.v` use the reference constructible
  hierarchy, reflection, Foundation, and Choice libraries.
- `compat/Lists/Streams.v` re-exports a standard-library module relocated in
  Rocq 9.

Every local proof is rechecked. This list records provenance; it is not an
additional logical assumption.

The upstream BusyCoq utility `LibTactics.v` contains an `inj_pair2` axiom, imports
`Stdlib.Logic.ProofIrrelevance.proof_irrelevance` and
`Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq`, and contains a `skip` tactic defined
using `admit`. The final axiom-free K230 proofs use none of these axioms or that tactic.
Their `Print Assumptions` checks concern the dependencies of the two endpoint
theorems. They do not claim that every declaration in every loaded upstream
utility is axiom-free. The pinned utility is retained unchanged.

The separate `classical/` development uses Rocq's excluded middle, dependent
unique choice, and relational choice. Its final PA-provability theorem is
audited against those three assumptions. Its completeness argument reuses the
Coq Library of Undecidability's classical first-order logic development, under
the MPL 2.0 notice preserved above. See
[classical/README.md](classical/README.md) for the theorem's scope and the
separate build.

## Compiler provenance

The compiler work builds on Andrew James Wade's
[Turing Machine Explorer](https://codeberg.org/ajwade/turing_machine_explorer).
The pinned reference's `ZF/generator/README.md` attributes `TMBuilder.py`,
`tm.py`, `tmdb.py`, `zf2.py`, and reused subroutines to Wade. Later source and
compiler optimizations produced the frozen K230 table. This verification
repository does not bundle the optimizer or require it to run; it checks the
resulting table and certificate in Rocq.
