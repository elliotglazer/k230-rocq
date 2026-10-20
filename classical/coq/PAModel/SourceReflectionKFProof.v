(** Actual guarded-AllI closure of the K-successor proof. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceFiniteTelescope SourceFiniteTelescopeQuantifier
 SourceLFixed SourceHierarchySyntax SourcePieceConjunctionBounds
 SourceRecursionClosureSyntax SourceRecursionClosureTransport SourceRecursionExAAdjoin
 SourceReflectionStep SourceReflectionOrdinalChart SourceReflectionOrdinalChartTransport SourceReflectionKF SourceReflectionKFWitness
 SourceReflectionKFInputs SourceReflectionKFNext SourceReflectionKFPoint SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem source_reflection_KF_shell M domain level sb sc count K out:
 source_reflection_KF M domain level sb sc count K out ->exists guard next point,
 sf_relation M SFMember(zeroM M)(succM M K)guard /\source_reflection_KF_next M domain level sb sc count(succM M K)(zeroM M)next /\
 sf_relation M SFImpl guard next point /\sf_relation M SFAll point(zeroM M)out.
Proof.
 intros(g&l&p&q&all&m&t&i&body&ex&tail&HG&HL&HP&HQ&HA&HM&HT&HI&HB&HE&HU&HO).
 exists g,ex,tail. split;[exact HG|]. split;[|auto].
 exists body. split;[|exact HE]. exists m,t,l,p,q,all,i. auto 15.
Qed.
Theorem source_zfr_reflection_KF M level sb sc count phi a Y K chart closure out law k:
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->source_bounded M phi(code_numeral M 2) ->
 source_reflection_step M(source_L_domain_code M)level sb sc count(zeroM M)(code_numeral M 1)phi ->
 coding_lt M a k ->coding_lt M Y k ->coding_lt M K k ->source_reflection_ordinal_chart M Y K chart ->
 source_rec_closure M phi a Y closure ->source_reflection_KF M(source_L_domain_code M)level sb sc count K out ->
 source_finite_telescope M[chart;closure]out law ->source_zfr_provable M law.
Proof.
 intros HLevel HV BP HMatrix BA BY BK HC HClosure HT HLaw. set(s:=succM M).
 pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
  (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel)as HL.
 pose proof(source_reflection_ordinal_chart_bounded M Y K chart k BY BK HC)as BC.
 pose proof(source_rec_closure_bounded M phi a Y closure k BP BA BY HClosure)as BClosure.
 assert(Bounds:forall f,In f[chart;closure]->source_bounded M f k)by(intros f[<-|[<-|[]]];assumption).
 pose proof(source_reflection_KF_bounded M(source_L_domain_code M)level sb sc count K out k(numerical_L_domain_bounded M)HL HV BK HT)as BT.
 destruct(source_reflection_KF_shell M(source_L_domain_code M)level sb sc count K out HT)as(guard&next&point&HG&HN&HP&HAll).
 pose proof(proj1(source_bounded_accept_unary M SFAll point out k(or_introl eq_refl)HAll)BT)as BPoint.
 destruct(source_reflection_ordinal_chart_total M(s Y)(s K))as(chartS&HCS).
 destruct(source_rec_closure_total M phi(s a)(s Y))as(closureS&HClosureS).
 assert(HS:Forall2(SourceQuantifierRules.source_formula_shift M)[chart;closure][chartS;closureS]).
 { constructor;[exact(source_reflection_ordinal_chart_shift M Y K chart chartS HC HCS)|]. constructor;[exact(source_rec_closure_shift M phi a Y closure closureS BP HClosure HClosureS)|constructor]. }
 destruct(source_finite_telescope_total M[chartS;closureS]point)as(pointLaw&HPointLaw).
 assert(HTel:source_finite_telescope M([chartS;closureS]++[guard])next pointLaw).
 { apply(source_finite_telescope_prefix M[chartS;closureS][guard]point next pointLaw HPointLaw). exists next. split;[reflexivity|exact HP]. }
 assert(HInputs:source_reflection_KF_inputs M phi(s a)(s Y)(s K)(zeroM M)([chartS;closureS]++[guard])).
 { exists chartS,closureS,guard. split;[reflexivity|]. auto. }
 assert(PPoint:source_zfr_provable M pointLaw).
 { apply(source_zfr_reflection_KF_point M level sb sc count phi(s a)(s Y)(s K)(zeroM M)([chartS;closureS]++[guard])next pointLaw(s k)HLevel HV BP HMatrix);
   try(rec_exa_name_bound);assumption. }
 exact(source_zfr_finite_telescope_all M[chart;closure][chartS;closureS]point out pointLaw law k Bounds BPoint HS HAll HPointLaw HLaw PPoint).
Qed.
Print Assumptions source_reflection_KF_shell.
Print Assumptions source_zfr_reflection_KF.
