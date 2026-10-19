(** The abstract K230 proof search halts exactly when standard ZFC is inconsistent.
    The remaining program layer must connect this enumerator to the frozen TM. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230S Require Import KQuotZFC KUpperConsistency.
From K230L Require Import Thm230 Enum230 Bridge230.

Theorem thm230_iff_standardZFC : thm230 1 <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite thm230_iff_KPrimeOrdIR.
  exact KPrimeOrdIR_standardZFC_equiconsistent.
Qed.

Theorem enum230_iff_standardZFC : enum230_halts <-> StandardZFC ⊢TC ⊥.
Proof.
  rewrite enum230_iff_KPrimeOrdIR.
  exact KPrimeOrdIR_standardZFC_equiconsistent.
Qed.
