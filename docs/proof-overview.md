# Proof overview

The machine searches for a contradiction in a compact first-order set theory.
Its consistency is equivalent to the consistency of ordinary ZFC. The proof
uses an interpretation; it does not identify the raw objects of the compact
theory with extensional sets.

## The compact theory

Use one binary relation `∈`, logical equality, and the abbreviation
`p ⊆ u := ∀z (z ∈ p → z ∈ u)`. For every formula `φ(x,p,q)` with any finite tuple
of additional parameters `q`, define

```text
Wφ(p,C) := (∃y φ(y,p,q)) → ∃y (y ∈ C ∧ φ(y,p,q)).

Hφ(C) := ∀u (u ∈ C →
             ((∃p φ(u,p,q)) ∧ ∀p (p ⊆ u → Wφ(p,C)))).
```

The ordinary theory `KPrimeOrd` contains the universal closures of

```text
∀a ∀x ∃C ((φ(x,a,q) → x ∈ C) ∧ Hφ(C)),
```

together with the equality axioms. The closure condition `Hφ(C)` is required
even when `φ(x,a,q)` is false. See
[KPrimeCore.v](../coq/settheory/KPrimeCore.v) and
[KPrimeTheory.v](../coq/settheory/KPrimeTheory.v) for the actual de Bruijn syntax.
The emitted source rearranges conjunctions and moves a support witness across
a conjunct in which it does not occur. The proof establishes the correspondence.

The numerical calculus uses a designated membership atom for falsity. Its
calibration therefore uses `KPrimeOrdIR`, which adds irreflexivity. Both
`KPrimeOrd` and `KPrimeOrdIR` are proved equiconsistent with `StandardZFC` in
[KUpperConsistency.v](../coq/settheory/KUpperConsistency.v).

## Why it has ZFC strength

The lower reduction first obtains elementary raw set constructions and a
tagged domain. Tagged bounded comprehension and collection permit relation
codes in that domain. A bisimulation quotient supplies extensionality and
supports the set-theoretic operations. In particular, the power-set proof bounds
canonical representatives and then uses the quotient relation to include all
equivalent representatives. It does not assume a power set of all raw codes.

The quotient interprets extensional ZF without Foundation. The pinned reference
proof supplies the relative-consistency steps for Foundation and Choice.
[KQuotZFTransfer.v](../coq/settheory/KQuotZFTransfer.v) and
[KQuotZFC.v](../coq/settheory/KQuotZFC.v) connect the local construction to those
reference theorems.

For the upper reduction, the constructible-hierarchy reflection library supplies
sets closed under the required subset and witness operations. Separation selects
the supported outputs. [KUpperCore.v](../coq/settheory/KUpperCore.v),
[KUpperReflect.v](../coq/settheory/KUpperReflect.v), and
[KUpperFinish.v](../coq/settheory/KUpperFinish.v) prove each required schema
instance inside the reference interpretation.

## From the table to the theorem

The proof checks the 230-state literal table, its 408419-step bootstrap, and the
simulation of the source program. A Rocq checker verifies the finite program
bisimulation certificate. The program enumerates the numerical calculus and
halts exactly on a derivation of the designated falsity code.

The source-to-logic bridge handles the actual variable labels, freshness gate,
coincident labels, and low numerical codes. The seed theorem addresses the
machine's actual initial register values rather than assuming an empty proof
cache. The final theorem composes these results with both set-theory reductions.

The scripts that proposed the transition table or the certificate are not
needed to check the theorem. The repository includes the exact proposed data
and the Rocq proofs that validate them. This release does not contain the
separate project investigating proofs internal to PA.
