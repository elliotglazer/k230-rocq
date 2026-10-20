(** The exact numerical proof-search nonhalting sentence and its PA proof.
    This is the seeded numerical enumerator. No literal TM simulation is used. *)
From FOL Require Import FullSyntax Arithmetics.
From PAModel Require Import Model CodeExpressions NumericalProofs RunSyntax
 UniformSearch UniformSearchCompleteness SentenceBounds SourceZFCProvability
 ActualKZFCConsistency PAValidityDerivability.
Unset Implicit Arguments.
#[local] Existing Instance Undecidability.FOL.Arithmetics.Signature.PA_funcs_signature |0.
#[local] Existing Instance Undecidability.FOL.Arithmetics.Signature.PA_preds_signature |0.
#[local] Existing Instance Undecidability.FOL.Syntax.Core.falsity_on |0.
#[local] Existing Instance Undecidability.FOL.Syntax.Core.class |0.

Definition numerical_search_halts M :=
 exists b c N,numerical_run M b c N /\ halt_at M b c N.
Definition numerical_search_nonhalting M := ~numerical_search_halts M.

Theorem numerical_search_nonhalting_ZFC_consistency M :
 numerical_search_nonhalting M <-> source_zfc_consistent M.
Proof.
 split.
 - intro Hno. apply(proj1(numerical_K_ZFC_consistency M)).
   intro Hproof. apply Hno. exact(uniform_numerical_search_complete M Hproof).
 - intros Hzfc Hrun. apply(proj2(numerical_K_ZFC_consistency M)Hzfc).
   exact(proj2(uniform_numerical_search_iff M)Hrun).
Qed.

Definition numerical_search_halting_formula : form :=
 ∃∃∃(run_formula $2 $1 $0 ∧ halt_at_formula $2 $1 $0).
Definition numerical_search_nonhalting_formula : form :=
 ¬numerical_search_halting_formula.
Definition numerical_search_ZFC_comparison_sentence : form :=
 (numerical_search_nonhalting_formula → source_zfc_consistency_formula) ∧
 (source_zfc_consistency_formula → numerical_search_nonhalting_formula).

Local Opaque holds run_formula halt_at_formula source_zfc_consistency_formula.
Theorem numerical_search_halting_formula_correct M rho :
 holds M rho numerical_search_halting_formula <-> numerical_search_halts M.
Proof.
 unfold numerical_search_halting_formula,numerical_search_halts.
 repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
 setoid_rewrite run_formula_correct. setoid_rewrite halt_at_formula_correct.
 reflexivity.
Qed.
Theorem numerical_search_nonhalting_formula_correct M rho :
 holds M rho numerical_search_nonhalting_formula <-> numerical_search_nonhalting M.
Proof.
 unfold numerical_search_nonhalting_formula,numerical_search_nonhalting.
 change ((holds M rho numerical_search_halting_formula ->False)<->
   (numerical_search_halts M ->False)).
 now rewrite numerical_search_halting_formula_correct.
Qed.
Local Opaque numerical_search_nonhalting_formula.
Theorem numerical_search_ZFC_comparison_sentence_correct M rho :
 holds M rho numerical_search_ZFC_comparison_sentence <->
 (numerical_search_nonhalting M <->source_zfc_consistent M).
Proof.
 unfold numerical_search_ZFC_comparison_sentence. rewrite holds_and.
 repeat setoid_rewrite holds_imp.
 rewrite !numerical_search_nonhalting_formula_correct,
   !source_zfc_consistency_formula_correct. reflexivity.
Qed.
Theorem numerical_search_ZFC_comparison_sentence_valid M rho :
 holds M rho numerical_search_ZFC_comparison_sentence.
Proof.
 apply numerical_search_ZFC_comparison_sentence_correct.
 apply numerical_search_nonhalting_ZFC_consistency.
Qed.

Local Transparent run_formula halt_at_formula source_zfc_consistency_formula numerical_search_nonhalting_formula.
Theorem numerical_search_ZFC_comparison_sentence_closed :
 closed numerical_search_ZFC_comparison_sentence.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Theorem PA_proves_numerical_search_ZFC_consistency :
 @Undecidability.FOL.Deduction.FullND.tprv
   Undecidability.FOL.Arithmetics.Signature.PA_funcs_signature
   Undecidability.FOL.Arithmetics.Signature.PA_preds_signature
   Undecidability.FOL.Syntax.Core.falsity_on
   Undecidability.FOL.Syntax.Core.class
   Undecidability.FOL.Arithmetics.PA.PAeq
   numerical_search_ZFC_comparison_sentence.
Proof.
 apply(full_PAeq_validity_derivability numerical_search_ZFC_comparison_sentence).
 - exact numerical_search_ZFC_comparison_sentence_closed.
 - exact numerical_search_ZFC_comparison_sentence_valid.
Qed.
Print Assumptions numerical_search_nonhalting_ZFC_consistency.
Print Assumptions numerical_search_ZFC_comparison_sentence_closed.
Print Assumptions PA_proves_numerical_search_ZFC_consistency.
