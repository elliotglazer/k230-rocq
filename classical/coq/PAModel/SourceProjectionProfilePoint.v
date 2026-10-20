(** The literal Op4 membership point as an actual ZFR source theorem at
    arbitrary PA-model-valued An/child/carrier/result/test names. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SetSchemaConstructors SourceIffGraphs
 SourceProjectionFiniteSyntax SourceProjectionFiniteBinders SourceProjectionOperationFixed
 SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourceFiniteParameterComposition
 SourceEnvironmentCarrierClosure SourceZFRProvability.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition projection_profile_sigma i:sf_term:=match i with 0=>$1|1=>$2|_=>$4 end.
Lemma projection_profile_literal:source_projection_operation_law=
 (projection_operation4 →$4∈'$0 →($4∈'$3 ↔projection_PJ3[projection_profile_sigma])).
Proof. reflexivity. Qed.
Definition projection_five_values {A}(an child carrier result tested:A)i:=match i with
 |0=>an|1=>child|2=>carrier|3=>result|_=>tested end.
Theorem source_zfr_projection_profile_point M an child carrier result tested op inAn inResult profile equiv inner law:
 code_relation M(projection_five_values an child carrier result tested)
  (source_parameter_expression(source_finite_parameter_names 4)projection_operation4)op ->
 sf_relation M SFMember tested an inAn ->sf_relation M SFMember tested result inResult ->
 code_relation M(projection_three_values child carrier tested)
  (source_parameter_expression(source_finite_parameter_names 3)projection_PJ3)profile ->
 source_iff_graph M inResult profile equiv ->sf_relation M SFImpl inAn equiv inner ->
 sf_relation M SFImpl op inner law ->source_zfr_provable M law.
Proof.
 intros HOp HAn HResult HProfile HE HI HL.
 apply(source_zfr_projection_operation M(projection_five_values an child carrier result tested)law).
 unfold source_projection_operation_expression. rewrite projection_profile_literal.
 cbn[source_parameter_expression]. rewrite source_parameter_substitution.
 assert(GOp:code_relation M(projection_five_values an child carrier result tested)
  (source_parameter_expression(source_finite_parameter_names 5)projection_operation4)op).
 { apply(proj2(source_parameter_graph_ext M 4 projection_operation4 projection_operation_bound
    (source_finite_parameter_names 5)(source_finite_parameter_names 4)
    (projection_five_values an child carrier result tested)(projection_five_values an child carrier result tested)
    ltac:(intros[|[|[|[|i]]]]v HN;try lia;reflexivity)op)). exact HOp. }
 assert(GProfile:code_relation M(projection_five_values an child carrier result tested)
  (source_parameter_expression(fun i=>source_finite_parameter_names 5(sf_index(projection_profile_sigma i)))projection_PJ3)profile).
 { apply(proj2(source_parameter_graph_ext M 3 projection_PJ3 projection_PJ_bound
    (fun i=>source_finite_parameter_names 5(sf_index(projection_profile_sigma i)))(source_finite_parameter_names 3)
    (projection_five_values an child carrier result tested)(projection_three_values child carrier tested)
    ltac:(intros[|[|[|i]]]v HN;try lia;reflexivity)profile)). exact HProfile. }
 destruct(source_iff_parts M inResult profile equiv HE)as(lr&rl&HLR&HRL&HAnd).
 eapply environment_carrier_code_join;[exact GOp| |exact HL].
 eapply environment_carrier_code_join;[| |exact HI].
 - eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HAn].
 - eapply environment_carrier_code_join;[| |exact HAnd].
   + eapply environment_carrier_code_join;[|exact GProfile|exact HLR].
     eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HResult].
   + eapply environment_carrier_code_join;[exact GProfile| |exact HRL].
     eapply environment_carrier_code_join;[reflexivity|reflexivity|exact HResult].
Qed.
Print Assumptions projection_profile_literal.
Print Assumptions source_zfr_projection_profile_point.
