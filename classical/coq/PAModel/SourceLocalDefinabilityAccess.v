(** The actual Def0 closure membership rule at arbitrary PA-model names. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceFiniteParameters SourceFiniteNameParameters SourceFiniteParameterNamedBinder SourceParameterGraphs
 SourceSubsetClosedPoint SourceLocalSelectedSubset SourceLocalParameterReindex SourceFiniteParameterComposition
 SourceNamedQuantifierRules SourceNamedSelfSpecialization SourceDerivedRules SourceEnvironmentCarrierClosure
 SourceBoundedCalibration OldNamedSyntaxBridge OldFullNDSourceBridge.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition local_access_subset_sigma i:sf_term:=match i with 0=>$0|_=>$2 end.
Definition source_local_access_body:sf_form:=($0 ∈' $1)→source_local_subset[local_access_subset_sigma]→($0 ∈' $3).
Definition source_local_access:sf_form:=∀source_local_access_body.
Definition source_local_access_expression:=source_parameter_expression(source_finite_parameter_names 3)source_local_access.
Definition local_access_names {A}(closure carrier definables:A)i:=match i with 0=>closure|1=>carrier|_=>definables end.
Lemma source_local_access_body_bound:bounded 4 source_local_access_body.
Proof.
 unfold source_local_access_body. apply bounded_bin.
 - apply(proj2(sb_atom_bounded 4 _ _));cbn;lia.
 - apply bounded_bin.
   + unfold source_local_subset,source_point_raw_subset,local_access_subset_sigma.
     cbn. apply bounded_quant,bounded_bin;apply(proj2(sb_atom_bounded 5 _ _));cbn;lia.
   + apply(proj2(sb_atom_bounded 4 _ _));cbn;lia.
Qed.
Lemma source_local_access_bound:bounded 3 source_local_access.
Proof. constructor. exact source_local_access_body_bound. Qed.
Theorem source_local_access_named_binder M selected closure carrier definables inClosure subset inDef tail point all:
 selected<>closure ->selected<>carrier ->selected<>definables ->
 sf_relation M SFMember selected closure inClosure ->
 code_relation M(local_subset_names selected carrier)source_local_subset_expression subset ->
 sf_relation M SFMember selected definables inDef ->sf_relation M SFImpl subset inDef tail ->
 sf_relation M SFImpl inClosure tail point ->
 code_relation M(local_access_names closure carrier definables)source_local_access_expression all ->
 source_named_quantifier M true selected point all.
Proof.
 intros SC SA SD HC HS HD HT HP HA.
 apply(source_finite_parameter_named_binder M 3 source_local_access_body
  (local_access_names closure carrier definables)selected point all true).
 - exact source_local_access_body_bound.
 - intros[|[|[|i]]]HI;try lia;cbn[local_access_names];assumption.
 - unfold source_local_access_body. cbn[source_parameter_expression].
   eapply environment_carrier_code_join;[| |exact HP].
   + eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HC].
   + eapply environment_carrier_code_join;[| |exact HT].
     * apply(source_local_parameter_reindex M 2 source_local_subset(source_finite_parameter_names 4)
        local_access_subset_sigma(finite_binder_environment selected(local_access_names closure carrier definables))
        (local_subset_names selected carrier)subset).
       -- constructor. exact source_local_subset_body_bound.
       -- intros[|[|i]]HI;try lia;reflexivity.
       -- exact HS.
     * eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HD].
 - exact HA.
Qed.
Theorem source_full_local_def_access M gb gc gn selected closure carrier definables inClosure subset inDef tail point all k:
 selected<>closure ->selected<>carrier ->selected<>definables ->source_bounded M point k ->
 sf_relation M SFMember selected closure inClosure ->
 code_relation M(local_subset_names selected carrier)source_local_subset_expression subset ->
 sf_relation M SFMember selected definables inDef ->sf_relation M SFImpl subset inDef tail ->
 sf_relation M SFImpl inClosure tail point ->
 code_relation M(local_access_names closure carrier definables)source_local_access_expression all ->
 source_full_prv M gb gc gn all ->source_full_prv M gb gc gn inClosure ->
 source_full_prv M gb gc gn subset ->source_full_prv M gb gc gn inDef.
Proof.
 intros SC SA SD BP HC HS HD HT HP HA PAll PC PS.
 destruct(source_local_access_named_binder M selected closure carrier definables inClosure subset inDef tail point all
  SC SA SD HC HS HD HT HP HA)as(rb&rc&body&HMap&HRen&HQ).
 pose proof(source_full_named_self_all_elim M gb gc gn point selected rb rc body all k BP HMap HRen HQ PAll)as PPoint.
 exact(source_full_modus_ponens M gb gc gn subset inDef tail HT
  (source_full_modus_ponens M gb gc gn inClosure tail point HP PPoint PC)PS).
Qed.
Print Assumptions source_local_access_named_binder.
Print Assumptions source_full_local_def_access.
