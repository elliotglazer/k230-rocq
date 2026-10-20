(** Actual Op5 profile extraction from the included finite ZFR context. *)
From Stdlib Require Import Lia.
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceLocalDefinabilityContext SourceSelectionOperationGraph SourceSelectionSCBinder SourceIffGraphs
 SourceProofWeakening SourceDerivedRules.
Unset Implicit Arguments.
Theorem source_full_local_selection_operation M fb fc fn gb gc gn rep old carrier selected tested
 operation inY inA sc pair profile k:
 source_local_fixed_context M fb fc fn ->context_included M fb fc fn gb gc gn ->context_bounded M gb gc gn k ->
 code_relation M(local_operation5_names rep old carrier selected)source_local_operation5_expression operation ->
 sf_relation M SFMember tested selected inY ->sf_relation M SFMember tested carrier inA ->
 code_relation M(local_SC_names rep old tested)source_local_SC_expression sc ->sf_relation M SFAnd inA sc pair ->
 source_iff_graph M inY pair profile ->source_full_prv M gb gc gn operation ->source_full_prv M gb gc gn profile.
Proof.
 intros HF HI BC HOp HY HA HSC HPair HProfile POp.
 destruct(sf_relation_total M SFImpl operation profile)as(law&HLaw).
 pose proof(source_local_selection_operation_graph M rep old carrier selected tested operation inY inA sc pair profile law
  HOp HY HA HSC HPair HProfile HLaw)as HCode.
 pose proof(source_full_local_fixed_instance M fb fc fn 3(local_selection_law_names rep old carrier selected tested)law
  HF ltac:(lia)HCode)as PLaw.
 pose proof(source_full_prv_weaken_bounded M fb fc fn gb gc gn law k PLaw HI BC)as PLaw'.
 exact(source_full_modus_ponens M gb gc gn operation profile law HLaw PLaw' POp).
Qed.
Print Assumptions source_full_local_selection_operation.
