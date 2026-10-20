(** PA-provability endpoint for the fixed public 230-state machine.
    All program-to-search contracts are discharged by actual histories.
    The last step uses classical first-order completeness to establish
    existence of a PA derivation; it does not emit an explicit certificate. *)
From FOL Require Import FullSyntax Arithmetics.
From PAModel Require Import Model TM230RunArithmetic SourceZFCProvability
 Program230HaltingSentence Program230SearchRealization Program230SearchComparison
 Program230SearchWithoutHalt Program230NormalSearch Program230AXAction
 PALiteralZFCFromNormal.
Unset Implicit Arguments.
#[local] Existing Instance Undecidability.FOL.Arithmetics.Signature.PA_funcs_signature |0.
#[local] Existing Instance Undecidability.FOL.Arithmetics.Signature.PA_preds_signature |0.
#[local] Existing Instance Undecidability.FOL.Syntax.Core.falsity_on |0.
#[local] Existing Instance Undecidability.FOL.Syntax.Core.class |0.

Theorem p230_actual_normal_search M : p230_normal_search_macro M.
Proof.
 apply p230_normal_search_from_ax.
 exact (p230_actual_ax_action M).
Qed.

Theorem p230_actual_counter_search_equivalence M :
 (p230_counter_halting M <-> p230_numerical_search_halts M).
Proof.
 exact (p230_counter_search_equivalence_from_normal M (p230_actual_normal_search M)).
Qed.

Theorem literal230_nonhalting_ZFC_consistency M :
 (~machine230_arithmetical_halts M <-> source_zfc_consistent M).
Proof.
 exact (literal230_nonhalting_ZFC_from_normal M (p230_actual_normal_search M)).
Qed.

Theorem literal230_ZFC_comparison_valid :
 forall M rho, holds M rho literal230_ZFC_comparison_sentence.
Proof.
 apply literal230_ZFC_comparison_valid_from_normal.
 exact p230_actual_normal_search.
Qed.

Theorem PA_proves_literal230_ZFC_consistency :
 @Undecidability.FOL.Deduction.FullND.tprv
   Undecidability.FOL.Arithmetics.Signature.PA_funcs_signature
   Undecidability.FOL.Arithmetics.Signature.PA_preds_signature
   Undecidability.FOL.Syntax.Core.falsity_on
   Undecidability.FOL.Syntax.Core.class
   Undecidability.FOL.Arithmetics.PA.PAeq
   literal230_ZFC_comparison_sentence.
Proof.
 apply PA_proves_literal230_ZFC_from_normal.
 exact p230_actual_normal_search.
Qed.

Print Assumptions p230_actual_normal_search.
Print Assumptions p230_actual_counter_search_equivalence.
Print Assumptions literal230_nonhalting_ZFC_consistency.
Print Assumptions PA_proves_literal230_ZFC_consistency.
