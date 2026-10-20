(** Literal canonical trace expansion at the fresh input variable. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors
  SchemaConstructorBounds SourceBounded SourceNativeKMatrixMaps SourceUpperTraceProfile
  SourceTraceMatrixAlignment SourceTraceProfileShell SourcePropositionalTemplates
  SourcePropositionalRebase SourceSeparationSubset SourceWFSeparationConstructor.
Unset Implicit Arguments.

Theorem source_upper_profile_expansion M phi k profile :
  source_bounded M phi k ->source_upper_trace_profile M phi profile ->
  exists theta atom matrix body left right point,
    source_native_k_matrix M NativeKA phi matrix /\
    sf_relation M SFMember (zeroM M)(code_numeral M 3) atom /\
    sf_relation M SFAnd atom matrix body /\sf_relation M SFEx body (zeroM M) theta /\
    sf_relation M SFMember (zeroM M)(code_numeral M 1) left /\
    sf_relation M SFMember (zeroM M)(code_numeral M 2) right /\
    code_relation M (schema_env3 left right theta)
      (source_prop_expression separation_point_template) point /\
    sf_relation M SFAll point (zeroM M) profile /\
    source_trace_profile_shell M theta (zeroM M)(code_numeral M 1) profile.
Proof.
  intros HP [trace [theta [HT [HS HO]]]].
  destruct (source_upper_trace_theta_matrix M phi trace theta k HP HT HS)
    as (atom&matrix&body&HM&HA&HB&HE).
  destruct (schema_expression_quantifier_split M (fun _=>theta) SFAll _ profile HO)
    as [point [HPoint HAll]].
  destruct (sf_relation_total M SFMember (zeroM M)(code_numeral M 1)) as [left HL].
  destruct (sf_relation_total M SFMember (zeroM M)(code_numeral M 2)) as [right HR].
  assert (HPCode:code_relation M (schema_env3 left right theta)
    (source_prop_expression separation_point_template) point).
  { apply (proj1 (source_prop_expression_with_graph M (fun _=>theta)
      (fun i=>match i with 0=>E_sf_mem 0 1|1=>E_sf_mem 0 2|_=>CEvar 0 end)
      (schema_env3 left right theta) separation_point_template
      ltac:(intros [|[|i]];cbn [schema_env3];
        [exact (proj2 (schema_expression_graph M (fun _=>theta) SFMember (CEconst 0)(CEconst 1)
          (zeroM M)(code_numeral M 1) left eq_refl eq_refl) HL)
        |exact (proj2 (schema_expression_graph M (fun _=>theta) SFMember (CEconst 0)(CEconst 2)
          (zeroM M)(code_numeral M 2) right eq_refl eq_refl) HR)
        |reflexivity]) point)).
    exact HPoint. }
  exists theta,atom,matrix,body,left,right,point.
  split;[exact HM|]. split;[exact HA|]. split;[exact HB|]. split;[exact HE|].
  split;[exact HL|]. split;[exact HR|]. split;[exact HPCode|]. split;[exact HAll|].
  exists left,right,point. auto.
Qed.

Print Assumptions source_upper_profile_expansion.
