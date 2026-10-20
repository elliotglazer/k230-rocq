(** Generate the genuine RR Replacement range, retaining only the exact ordinary recursion background. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift FixedSourceBounds
 SetSchemaConstructors SchemaConstructorBounds SchemaRenamingDescriptors SourceFiniteTelescope SourceFunctionalityShells
 SourceRecursionRangeRelation SourceRecursionRangeSchema SourceRecursionRangeCutoff SourceRecursionRangeBackground SourceRecursionRangeFunctionality
 SourceReplacementContainerSpecialization SourceZFRReplacementConditionalContainer SourceZFRProvability.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_zfr_rec_rr_range_total M phi A:
 source_bounded M phi(code_numeral M 2) ->source_rec_rr_background M phi(code_numeral M 0)(code_numeral M 2)A ->
 exists matrix p2 range law,
 source_rec_rr M phi(code_numeral M 0)(code_numeral M 1)(code_numeral M 2)(code_numeral M 3)(code_numeral M 4)matrix /\
 source_rec_rr M phi(code_numeral M 0)(code_numeral M 1)(code_numeral M 3)(code_numeral M 4)(code_numeral M 5)p2 /\
 code_relation M(source_replacement_container_environment M(code_numeral M 2)p2)(E_replacement_container(CEvar 0)(CEvar 1))range /\
 source_finite_telescope M A range law /\source_zfr_provable M law.
Proof.
 intros BP HA.
 destruct(source_rec_rr_total M phi(code_numeral M 0)(code_numeral M 1)(code_numeral M 2)(code_numeral M 3)(code_numeral M 4))as(matrix&HMatrix).
 destruct(source_rec_rr_total M phi(code_numeral M 0)(code_numeral M 1)(code_numeral M 3)(code_numeral M 4)(code_numeral M 5))as(p2&HP2).
 assert(BMatrix:source_bounded M matrix(code_numeral M 5)).
 { apply(source_rec_rr_bounded M phi(code_numeral M 0)(code_numeral M 1)(code_numeral M 2)(code_numeral M 3)(code_numeral M 4)matrix(code_numeral M 5)BP);try(apply(proj2(fixed_source_numeral_lt_iff M _ _));lia);exact HMatrix. }
 assert(BP2:source_bounded M p2(code_numeral M 6)).
 { apply(source_rec_rr_bounded M phi(code_numeral M 0)(code_numeral M 1)(code_numeral M 3)(code_numeral M 4)(code_numeral M 5)p2(code_numeral M 6)BP);try(apply(proj2(fixed_source_numeral_lt_iff M _ _));lia);exact HP2. }
 pose proof(source_rec_rr_cutoff_two M phi(code_numeral M 0)(code_numeral M 1)(code_numeral M 2)matrix p2 BP HMatrix HP2)as HC2.
 destruct(schema_renaming_total M RepA matrix)as(ra&HRA).
 destruct(schema_renaming_total M RepB matrix)as(rb&HRB).
 destruct(schema_renaming_total M RepC matrix)as(rc&HRC).
 pose proof(source_rec_rr_schema M phi matrix RepA ra BP HMatrix HRA)as HRArr.
 pose proof(source_rec_rr_schema M phi matrix RepB rb BP HMatrix HRB)as HRBrr.
 destruct(code_relation_total M(E_sf_functionality(CEvar 0)(CEvar 1))(schema_env3 ra rb(zeroM M)))as(functionality&HF).
 destruct(source_finite_telescope_total M A functionality)as(funlaw&HFunlaw).
 assert(PFunlaw:source_zfr_provable M funlaw).
 { apply(source_zfr_rec_rr_functionality_named M phi(code_numeral M 0)(code_numeral M 1)(code_numeral M 2)A ra rb functionality funlaw(code_numeral M 3)BP);
   try(apply(proj2(fixed_source_numeral_lt_iff M _ _));lia);assumption. }
 set(env:=source_replacement_container_environment M(code_numeral M 2)p2).
 destruct(code_relation_total M(E_replacement_container(CEvar 0)(CEvar 1))env)as(range&HRange).
 assert(BRange:source_bounded M range(code_numeral M 3)).
 { assert(HE:schema_expression_bound M env(E_replacement_container(CEvar 0)(CEvar 1))(code_numeral M 3)).
   { unfold E_replacement_container,E_sf_ex,E_sf_all. apply schema_expression_unary;[now right|].
     apply schema_expression_unary;[now left|]. apply schema_expression_iff.
     - apply schema_expression_atom;[now left|schema_small_index|schema_small_index].
     - apply schema_expression_unary;[now right|]. apply schema_expression_binary;[now left| |].
       + intros f HGraph. apply(proj1(schema_expression_graph M env SFMember(CEconst 0)(CEvar 1)(zeroM M)(code_numeral M 5)f eq_refl eq_refl))in HGraph.
         apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 5)f(code_numeral M 6)(or_introl eq_refl)HGraph)).
         split;schema_small_index.
       + apply schema_expression_variable. exact BP2. }
   exact(HE range HRange). }
 destruct(source_finite_telescope_total M A range)as(law&HLaw).
 exists matrix,p2,range,law. repeat split;try assumption.
 apply(source_zfr_replacement_conditional_container M matrix(code_numeral M 3)ra rb rc functionality p2(code_numeral M 2)A funlaw range law(code_numeral M 3));try assumption.
 exact(source_rec_rr_background_bounded M phi(code_numeral M 0)(code_numeral M 2)A(code_numeral M 3)BP(proj2(fixed_source_numeral_lt_iff M 0 3)ltac:(lia))(proj2(fixed_source_numeral_lt_iff M 2 3)ltac:(lia))HA).
Qed.
Print Assumptions source_zfr_rec_rr_range_total.
