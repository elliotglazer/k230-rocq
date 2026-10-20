(** The actual Replacement container graph is exactly the literal RR range chart. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds SourcePropositionalRebase
 SourceWFSeparationConstructor SourcePropositionalTemplates SourceRecursionRangeRelation SourceRecursionRangeFibre SourceRecursionRangeChart
 SourceReplacementContainerSpecialization.
Unset Implicit Arguments.
Theorem source_rec_rr_range_shell M phi p2 out:
 source_rec_rr M phi(code_numeral M 0)(code_numeral M 1)(code_numeral M 3)(code_numeral M 4)(code_numeral M 5)p2 ->
 code_relation M(source_replacement_container_environment M(code_numeral M 2)p2)(E_replacement_container(CEvar 0)(CEvar 1))out ->
 exists body,source_rec_range_chart M phi(code_numeral M 1)(code_numeral M 2)(code_numeral M 3)(zeroM M)body /\sf_relation M SFEx body(zeroM M)out.
Proof.
 intros HRR HO. set(env:=source_replacement_container_environment M(code_numeral M 2)p2).
 unfold E_replacement_container,E_sf_ex,E_sf_all in HO.
 destruct(schema_expression_quantifier_split M env SFEx _ out HO)as(body&HBody&HEx).
 destruct(schema_expression_quantifier_split M env SFAll _ body HBody)as(point&HPoint&HAll).
 destruct(code_relation_total M(E_sf_mem 0 1)env)as(left&HLeft).
 destruct(code_relation_total M(E_sf_ex(E_sf SFAnd(E_sf SFMember(CEconst 0)(CEvar 1))(CEvar 0)))env)as(fibre&HFibre).
 apply(proj1(source_replacement_container_iff_graph M env _ _ left fibre point HLeft HFibre))in HPoint.
 pose proof(proj1(schema_expression_graph M env SFMember(CEconst 0)(CEconst 1)(zeroM M)(code_numeral M 1)left eq_refl eq_refl)HLeft)as HM.
 destruct(schema_expression_quantifier_split M env SFEx _ fibre HFibre)as(fibrebody&HFibreBody&HFibreEx).
 destruct(schema_expression_split M env SFAnd _ _ fibrebody HFibreBody)as(member&rr&HMember&HR&HAnd).
 change(rr=p2)in HR. subst rr.
 pose proof(proj1(schema_expression_graph M env SFMember(CEconst 0)(CEvar 1)(zeroM M)(code_numeral M 5)member eq_refl eq_refl)HMember)as HMN.
 exists body. split;[exists point;split;[|exact HAll]|exact HEx].
 exists left,fibre. split;[exact HM|]. split.
 - exists member,p2,fibrebody. auto.
 - exact HPoint.
Qed.
Print Assumptions source_rec_rr_range_shell.
