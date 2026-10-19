(** The abstract numerical proof search exactly detects inconsistency of K' + IR. *)
From Coq Require Import List.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From K230S Require Import KP0 KPrimeTheory KDecodeTheory KDecodeComplete.
From K230L Require Import Codes230 Thm230 Enum230 L1_230 Sound230 Complete230.
Import ListNotations.

Lemma decodedIR_to_KPrimeOrdIR phi : DecodedK230IR ⊢TC phi -> KPrimeOrdIR ⊢TC phi.
Proof.
  apply (theory_derivation_map DecodedK230IR KPrimeOrdIR phi).
  intros a [Ha| ->].
  - assert (Hp : DecodedK230Ord ⊢TC a).
    { exists [a]. split; [intros b [<-|[]]; exact Ha|apply Ctx; now left]. }
    apply (Weak_T (DecodedK230Ord_derivation_to_KPrimeOrd a Hp)).
    intros b Hb. now left.
  - exists [irreflexivity]. split; [intros b [<-|[]]; now right|apply Ctx; now left].
Qed.

Theorem thm230_iff_KPrimeOrdIR : thm230 1 <-> KPrimeOrdIR ⊢TC ⊥.
Proof.
  split.
  - intros H. apply decodedIR_to_KPrimeOrdIR, thm_to_DecodedK230IR, H.
  - apply KPrimeOrdIR_to_thm.
Qed.

Theorem enum230_iff_KPrimeOrdIR : enum230_halts <-> KPrimeOrdIR ⊢TC ⊥.
Proof. rewrite L1_230. exact thm230_iff_KPrimeOrdIR. Qed.
