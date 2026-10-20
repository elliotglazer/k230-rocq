(** A selected-set profile implies the literal Sub0 predicate. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceBoundedCalibration SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterNamedBinder SourceParameterGraphs
 SourceNamedQuantifierRules SourceNamedVacuity SourceIffGraphs SourceConjunctionRules SourceDerivedRules
 SourceUpperProofHelpers SourceContextProofHelpers NumericalEnvironments SourceNamedSelfSpecialization
 SourceEnvironmentCarrierClosure SourceSubsetClosedPoint OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldZFC Require Z_base.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition source_local_subset:sf_form:=source_point_raw_subset $0 $1.
Definition source_local_subset_expression:=source_parameter_expression(source_finite_parameter_names 2)source_local_subset.
Definition local_subset_names {A}(selected carrier:A)i:=match i with 0=>selected|_=>carrier end.
Lemma source_local_subset_literal:source_local_subset=isolated_formula
 (OldZFC.Z_base.Sub0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)).
Proof. reflexivity. Qed.
Lemma source_local_subset_body_bound:bounded 3($0 ∈' $1 →$0 ∈' $2).
Proof. apply bounded_bin;apply(proj2(sb_atom_bounded 3 _ _));cbn;lia. Qed.
Theorem source_local_subset_named_binder M selected carrier tested memberSelected memberCarrier point subset:
 tested<>selected ->tested<>carrier ->sf_relation M SFMember tested selected memberSelected ->
 sf_relation M SFMember tested carrier memberCarrier ->sf_relation M SFImpl memberSelected memberCarrier point ->
 code_relation M(local_subset_names selected carrier)source_local_subset_expression subset ->
 source_named_quantifier M true tested point subset.
Proof.
 intros TS TA HMS HMA HP HS.
 apply(source_finite_parameter_named_binder M 2($0 ∈' $1 →$0 ∈' $2)
  (local_subset_names selected carrier)tested point subset true).
 - exact source_local_subset_body_bound.
 - intros[|[|i]]HI;try lia;cbn[local_subset_names];assumption.
 - cbn[source_parameter_expression].
   eapply environment_carrier_code_join;[| |exact HP].
   + eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HMS].
   + eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HMA].
 - exact HS.
Qed.
Theorem source_full_selected_subset_point M gb gc gn tested selected carrier memberSelected memberCarrier matrix pair profile point subset k:
 context_bounded M gb gc gn k ->source_bounded M memberSelected k ->source_bounded M memberCarrier k ->
 source_bounded M matrix k ->source_named_context_vacuous M gb gc gn tested ->
 tested<>selected ->tested<>carrier ->sf_relation M SFMember tested selected memberSelected ->
 sf_relation M SFMember tested carrier memberCarrier ->sf_relation M SFAnd memberCarrier matrix pair ->
 source_iff_graph M memberSelected pair profile ->sf_relation M SFImpl memberSelected memberCarrier point ->
 code_relation M(local_subset_names selected carrier)source_local_subset_expression subset ->
 source_full_prv M gb gc gn profile ->source_full_prv M gb gc gn subset.
Proof.
 intros BC BMS BMA BM VCtx TS TA HMS HMA HPair HProfile HPoint HSubset PProfile.
 destruct(source_iff_parts M memberSelected pair profile HProfile)as(lr&rl&HL&HR&HP).
 pose proof(source_full_conjunction_left M gb gc gn lr rl profile HP PProfile)as PLR.
 destruct(environment_cons_total M gb gc gn memberSelected)as(ub&uc&un&HCons).
 pose proof(proj2(context_bounded_cons M gb gc gn memberSelected ub uc un k HCons)(conj BMS BC))as BU.
 pose proof(source_full_cons_head M gb gc gn memberSelected ub uc un k HCons BMS BU)as PMS.
 pose proof(source_full_cons_weaken M gb gc gn memberSelected ub uc un k lr HCons BU PLR)as PLR'.
 pose proof(source_full_modus_ponens M ub uc un memberSelected pair lr HL PLR' PMS)as PPair.
 pose proof(source_full_conjunction_left M ub uc un memberCarrier matrix pair HPair PPair)as PMA.
 pose proof(source_full_implication_intro M gb gc gn memberSelected memberCarrier point ub uc un HCons HPoint PMA)as PPoint.
 exact(source_full_named_quantifier_all_intro M gb gc gn tested point subset VCtx
  (source_local_subset_named_binder M selected carrier tested memberSelected memberCarrier point subset TS TA HMS HMA HPoint HSubset)PPoint).
Qed.
Theorem source_full_selected_subset_from_profile M gb gc gn tested selected carrier memberSelected memberCarrier matrix pair profile allProfile point subset k:
 context_bounded M gb gc gn k ->source_bounded M memberSelected k ->source_bounded M memberCarrier k ->
 source_bounded M matrix k ->source_named_context_vacuous M gb gc gn tested ->
 tested<>selected ->tested<>carrier ->sf_relation M SFMember tested selected memberSelected ->
 sf_relation M SFMember tested carrier memberCarrier ->sf_relation M SFAnd memberCarrier matrix pair ->
 source_iff_graph M memberSelected pair profile ->source_named_quantifier M true tested profile allProfile ->
 sf_relation M SFImpl memberSelected memberCarrier point ->
 code_relation M(local_subset_names selected carrier)source_local_subset_expression subset ->
 source_full_prv M gb gc gn allProfile ->source_full_prv M gb gc gn subset.
Proof.
 intros BC BMS BMA BM VCtx TS TA HMS HMA HPair HProfile HAll HPoint HSubset PAll.
 assert(BPair:source_bounded M pair k).
 { exact(proj2(source_bounded_accept_binary M SFAnd memberCarrier matrix pair k(or_introl eq_refl)HPair)(conj BMA BM)). }
 pose proof(source_iff_bounded M memberSelected pair profile k BMS BPair HProfile)as BProfile.
 destruct HAll as(rb&rc&body&HMap&HRen&HQ).
 pose proof(source_full_named_self_all_elim M gb gc gn profile tested rb rc body allProfile k BProfile HMap HRen HQ PAll)as PProfile.
 exact(source_full_selected_subset_point M gb gc gn tested selected carrier memberSelected memberCarrier matrix pair profile point subset k
  BC BMS BMA BM VCtx TS TA HMS HMA HPair HProfile HPoint HSubset PProfile).
Qed.
Print Assumptions source_local_subset_named_binder.
Print Assumptions source_full_selected_subset_point.
Print Assumptions source_full_selected_subset_from_profile.
