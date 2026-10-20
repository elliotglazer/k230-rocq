(** PA proof existence for the exact literal-machine/counterprogram comparison.
    The remaining counterprogram/numerical-search compiler comparison is not
    assumed or asserted here. *)
From FOL Require Import FullSyntax Arithmetics.
From PAModel Require Import Model CodeExpressions NumericalProofs TM230RunArithmetic TM230CounterEquivalence
 Program230HaltingSentence Program230HistoryBounds PAValidityDerivability.
Unset Implicit Arguments.
#[local] Existing Instance Undecidability.FOL.Arithmetics.Signature.PA_funcs_signature |0.
#[local] Existing Instance Undecidability.FOL.Arithmetics.Signature.PA_preds_signature |0.
#[local] Existing Instance Undecidability.FOL.Syntax.Core.falsity_on |0.
#[local] Existing Instance Undecidability.FOL.Syntax.Core.class |0.

Definition literal230_nonhalting_formula:form:=¬machine230_halt_sentence.
Definition literal230_counter_comparison_sentence:form:=
 (literal230_nonhalting_formula→p230_counter_nonhalting_formula) ∧
 (p230_counter_nonhalting_formula→literal230_nonhalting_formula).
Lemma literal230_nonhalting_formula_correct M rho:
 holds M rho literal230_nonhalting_formula<->~machine230_arithmetical_halts M.
Proof.
 unfold literal230_nonhalting_formula.
 change((holds M rho machine230_halt_sentence->False)<->~machine230_arithmetical_halts M).
 now rewrite machine230_halt_sentence_correct.
Qed.
Lemma literal230_counter_comparison_correct M rho:
 holds M rho literal230_counter_comparison_sentence<->
 (~machine230_arithmetical_halts M<->p230_counter_nonhalting M).
Proof.
 change (((holds M rho literal230_nonhalting_formula ->
   holds M rho p230_counter_nonhalting_formula) /\
   (holds M rho p230_counter_nonhalting_formula ->
   holds M rho literal230_nonhalting_formula)) <->
   (~machine230_arithmetical_halts M <-> p230_counter_nonhalting M)).
 rewrite !literal230_nonhalting_formula_correct,!p230_counter_nonhalting_formula_correct.
 reflexivity.
Qed.
Theorem literal230_counter_comparison_valid M rho:
 holds M rho literal230_counter_comparison_sentence.
Proof.
 apply literal230_counter_comparison_correct;unfold p230_counter_nonhalting.
 split;intros H HH;apply H.
 -apply(proj2(machine230_counter_halting_iff M));exact HH.
 -apply(proj1(machine230_counter_halting_iff M));exact HH.
Qed.
Lemma literal230_nonhalting_formula_closed:closed literal230_nonhalting_formula.
Proof.
 unfold closed,literal230_nonhalting_formula;constructor.
 -exact machine230_halt_sentence_closed.
 -constructor.
Qed.
Theorem literal230_counter_comparison_closed:closed literal230_counter_comparison_sentence.
Proof.
 unfold closed,literal230_counter_comparison_sentence;constructor;constructor.
 -exact literal230_nonhalting_formula_closed.
 -exact p230_counter_nonhalting_formula_closed.
 -exact p230_counter_nonhalting_formula_closed.
 -exact literal230_nonhalting_formula_closed.
Qed.
Theorem PA_proves_literal230_counter_comparison:
 @Undecidability.FOL.Deduction.FullND.tprv
   Undecidability.FOL.Arithmetics.Signature.PA_funcs_signature
   Undecidability.FOL.Arithmetics.Signature.PA_preds_signature
   Undecidability.FOL.Syntax.Core.falsity_on
   Undecidability.FOL.Syntax.Core.class
   Undecidability.FOL.Arithmetics.PA.PAeq
   literal230_counter_comparison_sentence.
Proof.
 apply(full_PAeq_validity_derivability literal230_counter_comparison_sentence).
 -exact literal230_counter_comparison_closed.
 -exact literal230_counter_comparison_valid.
Qed.
Print Assumptions literal230_counter_comparison_valid.
Print Assumptions literal230_counter_comparison_closed.
Print Assumptions PA_proves_literal230_counter_comparison.
