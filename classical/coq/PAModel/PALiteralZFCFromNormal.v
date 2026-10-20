(** Final PA sentence for the literal public230 machine. The one remaining
    premise is deliberately visible: uniform correctness of the normal loop.
    The machine, its halting formula and the ZFC consistency formula are fixed. *)
From FOL Require Import FullSyntax Arithmetics.
From PAModel Require Import Model CodeExpressions TM230RunArithmetic TM230CounterEquivalence
 Program230HaltingSentence Program230SearchRealization Program230SearchComparison
 Program230SearchWithoutHalt SourceZFCProvability NumericalSearchZFCConsistency
 PALiteralCounterEquivalence PAValidityDerivability SentenceBounds.
Unset Implicit Arguments.
#[local] Existing Instance Undecidability.FOL.Arithmetics.Signature.PA_funcs_signature |0.
#[local] Existing Instance Undecidability.FOL.Arithmetics.Signature.PA_preds_signature |0.
#[local] Existing Instance Undecidability.FOL.Syntax.Core.falsity_on |0.
#[local] Existing Instance Undecidability.FOL.Syntax.Core.class |0.

Definition literal230_ZFC_comparison_sentence:form:=
 (literal230_nonhalting_formula → source_zfc_consistency_formula) ∧
 (source_zfc_consistency_formula → literal230_nonhalting_formula).

Theorem literal230_nonhalting_ZFC_from_normal M:
 p230_normal_search_macro M ->
 (~machine230_arithmetical_halts M <-> source_zfc_consistent M).
Proof.
 intro Hnormal.
 pose proof (p230_counter_search_equivalence_from_normal M Hnormal) as Hsearch.
 pose proof (machine230_counter_halting_iff M) as Hmachine.
 pose proof (numerical_search_nonhalting_ZFC_consistency M) as Hzfc.
 unfold numerical_search_nonhalting,numerical_search_halts in Hzfc.
 unfold p230_numerical_search_halts in Hsearch.
 split.
 -intro Hno;apply (proj1 Hzfc);intro Hhalt.
  apply Hno;apply (proj2 Hmachine);apply (proj2 Hsearch);exact Hhalt.
 -intros Hconsistent Hhalt.
  apply (proj2 Hzfc Hconsistent);apply (proj1 Hsearch);apply (proj1 Hmachine);exact Hhalt.
Qed.

Theorem literal230_ZFC_comparison_correct M rho:
 holds M rho literal230_ZFC_comparison_sentence <->
 (~machine230_arithmetical_halts M <-> source_zfc_consistent M).
Proof.
 change (((holds M rho literal230_nonhalting_formula ->
     holds M rho source_zfc_consistency_formula) /\
    (holds M rho source_zfc_consistency_formula ->
     holds M rho literal230_nonhalting_formula)) <->
    (~machine230_arithmetical_halts M <-> source_zfc_consistent M)).
 rewrite !literal230_nonhalting_formula_correct,!source_zfc_consistency_formula_correct.
 reflexivity.
Qed.

Lemma literal230_source_ZFC_formula_closed:closed source_zfc_consistency_formula.
Proof. apply formula_boundb_sound;vm_compute;reflexivity. Qed.

Theorem literal230_ZFC_comparison_closed:closed literal230_ZFC_comparison_sentence.
Proof.
 unfold closed,literal230_ZFC_comparison_sentence;constructor;constructor.
 -exact literal230_nonhalting_formula_closed.
 -exact literal230_source_ZFC_formula_closed.
 -exact literal230_source_ZFC_formula_closed.
 -exact literal230_nonhalting_formula_closed.
Qed.

Theorem literal230_ZFC_comparison_valid_from_normal:
 (forall M,p230_normal_search_macro M) ->
 forall M rho,holds M rho literal230_ZFC_comparison_sentence.
Proof.
 intros Hnormal M rho;apply literal230_ZFC_comparison_correct.
 exact (literal230_nonhalting_ZFC_from_normal M (Hnormal M)).
Qed.

Theorem PA_proves_literal230_ZFC_from_normal:
 (forall M,p230_normal_search_macro M) ->
 @Undecidability.FOL.Deduction.FullND.tprv
   Undecidability.FOL.Arithmetics.Signature.PA_funcs_signature
   Undecidability.FOL.Arithmetics.Signature.PA_preds_signature
   Undecidability.FOL.Syntax.Core.falsity_on
   Undecidability.FOL.Syntax.Core.class
   Undecidability.FOL.Arithmetics.PA.PAeq
   literal230_ZFC_comparison_sentence.
Proof.
 intro Hnormal;apply (full_PAeq_validity_derivability literal230_ZFC_comparison_sentence).
 -exact literal230_ZFC_comparison_closed.
 -exact (literal230_ZFC_comparison_valid_from_normal Hnormal).
Qed.

Print Assumptions literal230_nonhalting_ZFC_from_normal.
Print Assumptions literal230_ZFC_comparison_closed.
Print Assumptions PA_proves_literal230_ZFC_from_normal.
