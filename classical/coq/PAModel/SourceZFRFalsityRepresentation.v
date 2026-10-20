(** The falsity case of representation existence inside C is an actual
    ZFR source theorem for every internal n. No closure-law proof or
    auxiliary syntax family remains a premise. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
 SourceRepresentationRecipe SourceRepresentationFalsityClosure SourceRepresentationClosureRecipe
 SourceDefinabilityPrimitives SourceClosureNumeralsFixed SourceParameterIdentityCalibration
 SourceFiniteParameters SourceFiniteNameParameters SourceNumeralLift SchemaConstructorBounds SourceZFRProvability.
Unset Implicit Arguments.

Theorem source_zfr_falsity_representation M n result :
 source_representation_in_closure_recipe M n(zeroM M) result ->source_zfr_provable M result.
Proof.
 intros(rep&succ&closure&body&ex&middle&HR&HS&HC&HB&HE&HM&HO).
 set(rawbody:=code_numeral M(sf_encode representation_raw_closure_body)).
 set(rawex:=code_numeral M(sf_encode representation_raw_closure_exists)).
 assert(HRaw:sf_relation M SFAnd(code_numeral M(sf_encode source_def_empty))(representation_member_code M) rawbody).
 { exact(sf_make_numeral M SFAnd(sf_encode source_def_empty)(sf_make SFMember 0 3)). }
 assert(HRawEx:sf_relation M SFEx rawbody(zeroM M) rawex).
 { exact(sf_make_numeral M SFEx(sf_encode representation_raw_closure_body) 0). }
 destruct(sf_relation_total M SFImpl closure rawex)as(rawmiddle&HMRaw).
 destruct(sf_relation_total M SFImpl succ rawmiddle)as(law&HOuter).
 assert(HLaw:code_relation M(representation_identity_environment M) source_closure_empty_expression law).
 { rewrite representation_closure_empty_shell.
   pose proof(source_parameter_identity_calibration M representation_raw_closure_exists
    (source_finite_parameter_names 3)(representation_identity_environment M)(representation_identity_names_graph M))as HEx.
   pose proof(proj2(schema_expression_graph M(representation_identity_environment M) SFImpl _ _
    closure rawex rawmiddle HC HEx) HMRaw)as HMiddle.
   exact(proj2(schema_expression_graph M(representation_identity_environment M) SFImpl _ _
    succ rawmiddle law HS HMiddle) HOuter). }
 exact(source_zfr_representation_falsity_closure M n rep(representation_identity_environment M)
   succ closure rawbody rawex rawmiddle law body ex middle result HR HLaw
   (representation_successor_condition_bounded M succ HS)(representation_closure_condition_bounded M closure HC)
   HRaw HRawEx HMRaw HOuter HB HE HM HO).
Qed.

Theorem source_zfr_falsity_representation_total M n :exists result,
 source_representation_in_closure_recipe M n(zeroM M) result /\source_zfr_provable M result.
Proof.
 destruct(source_representation_in_closure_recipe_total M n(zeroM M))as(result&HR).
 exists result. exact(conj HR(source_zfr_falsity_representation M n result HR)).
Qed.
Print Assumptions source_zfr_falsity_representation.
Print Assumptions source_zfr_falsity_representation_total.
