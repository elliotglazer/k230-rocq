(** Actual membership-preserving successor of the numeral-in-closure proof.
 Both existential eliminations are compiled into genuine source derivations. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceBoundMonotone NumericalRenaming NumericalInstantiation SourceQuantifierRules SourceImplicationAllShift
 SourceDefinabilityStep SourceDefinabilityPrimitives SourceDefinabilitySuccessor SourceDefinabilityLogicalStep
 SourceInstantiationConstructors SourceNumFClosureRecipe SourceNumFClosureSyntax SourceNumFClosureBounds
 SourceNumFClosureFiniteShells SourceNumFClosurePoint SourceNumFClosurePrograms
 SourcePropositionalTemplates SourceWitnessProofComposition SourceZFRProvability SourceDescriptorProvability
 SourceRepresentationClosureRecipe.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_def_successor01 representation_closure_condition numf_closure_succ_shift_form numf_closure_condition_shift_form.
Ltac nc_graph :=lazymatch goal with
 | |-code_relation ?M ?rho (source_prop_expression(SPTSlot ?idx)) ?out =>reflexivity
 | |-code_relation ?M ?rho (source_prop_expression(SPTImpl ?A ?B)) ?out =>
   match goal with H:sf_relation M SFImpl ?a ?b out|-_ =>
    apply(source_prop_template_join M rho SFImpl A B a b out);[nc_graph|nc_graph|exact H]end
 | |-code_relation ?M ?rho (source_prop_expression(SPTAnd ?A ?B)) ?out =>
   match goal with H:sf_relation M SFAnd ?a ?b out|-_ =>
    apply(source_prop_template_join M rho SFAnd A B a b out);[nc_graph|nc_graph|exact H]end
 end.
Theorem source_zfr_numf_closure_step M p q old result :source_bounded M p(code_numeral M 1) ->
 source_def_step M false p q ->source_numf_closure_statement M p old ->source_numf_closure_statement M q result ->
 source_zfr_provable M old ->source_zfr_provable M result.
Proof.
 intros BP HStep HOld HResult POld.
 destruct(source_numf_closure_statement_parts M p old HOld)as(bp&ep&mp&HPairP&HMP&HOldOut).
 destruct(source_numf_closure_statement_parts M q result HResult)as(bq3&eq3&mq&HPairQ&HMQ&HResultOut).
 pose proof(source_def_numeral_step_bound M p q BP HStep)as BQ.
 destruct(source_def_step_graph M false p q HStep)as(unused&pair&EU&HNextPair&HNext). subst unused.
 destruct(numerical_renaming_total M p(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(ps&HPS).
 pose proof(source_shift_bound M p ps(code_numeral M 1)BP HPS)as BPS.
 destruct(source_numf_member_shell_total M q 4)as(bq4&eq4&HQ4).
 destruct(source_numf_member_shell_total M q 5)as(bq5&eq5&HQ5).
 pose proof(source_numf_member_shell_bounded M p 3 bp ep BP HPairP)as(BBP&BEP).
 pose proof(source_numf_member_shell_bounded M q 3 bq3 eq3 BQ HPairQ)as(BBQ3&BEQ3).
 pose proof(source_numf_member_shell_bounded M q 4 bq4 eq4 BQ HQ4)as(BBQ4&BEQ4).
 pose proof(source_numf_member_shell_bounded M q 5 bq5 eq5 BQ HQ5)as(BBQ5&BEQ5).
 destruct(source_numf_closure_successor_point_shell M)as(sbody&exs&tail&middle&law&HSBody&HExS&HTail&HMiddle&HLaw&PLaw).
 pose proof(source_numf_member_exists_shift M q 2 bq3 eq3 bq4 eq4 BQ HPairQ HQ4)as HEQ34.
 pose proof(source_numf_member_exists_shift M q 3 bq4 eq4 bq5 eq5 BQ HQ4 HQ5)as HEQ45.
 destruct(sf_relation_total M SFAnd ps(code_numeral M(sf_encode source_def_succ10)))as(pairinst&HPI).
 assert(HInst:numerical_instantiation M pair(code_numeral M 1)pairinst).
 { exact(source_instantiation_binary M SFAnd p _ pair(code_numeral M 1)ps _ pairinst(or_introl eq_refl)
   HNextPair(source_unit_instantiation_shift M p ps BP HPS)(source_def_successor_swap M)HPI). }
 pose proof(source_numf_member_body_instance M q 4 bq5 bq4 BQ(proj1 HQ5)(proj1 HQ4))as HTInst.
 destruct(sf_relation_total M SFImpl pairinst q)as(first&HFirst).
 destruct(sf_relation_total M SFImpl bq4 eq5)as(second&HSecond).
 destruct(sf_relation_total M SFImpl ps eq5)as(inner&HInner).
 destruct(sf_relation_total M SFImpl sbody inner)as(point&HPoint).
 assert(BP6:source_bounded M p(code_numeral M 6))by(exact(source_numf_bound_to_six M p 1 ltac:(lia)BP)).
 assert(BPS6:source_bounded M ps(code_numeral M 6))by(exact(source_numf_bound_to_six M ps 2 ltac:(lia)BPS)).
 assert(BQ6:source_bounded M q(code_numeral M 6))by(exact(source_numf_bound_to_six M q 1 ltac:(lia)BQ)).
 assert(BS106:source_bounded M(code_numeral M(sf_encode source_def_succ10))(code_numeral M 6))
 by(exact(source_numf_bound_to_six M _ 2 ltac:(lia)(source_def_succ10_bound M))).
 assert(BM3:source_bounded M(source_numf_closure_member M 3)(code_numeral M 6)).
 { apply source_numf_closure_member_bounded;[apply coding_zero_lt_succ|]. do 3 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 assert(BM4:source_bounded M(source_numf_closure_member M 4)(code_numeral M 6)).
 { apply source_numf_closure_member_bounded;[apply coding_zero_lt_succ|]. do 4 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 assert(BEQ46:source_bounded M eq4(code_numeral M 6))by(exact(source_numf_bound_to_six M eq4 4 ltac:(lia)BEQ4)).
 assert(BEQ56:source_bounded M eq5(code_numeral M 6))by(exact(source_numf_bound_to_six M eq5 5 ltac:(lia)BEQ5)).
 assert(PPoint:source_zfr_provable M point).
 { apply(proj1(source_zfr_descriptor_provable M point)).
   exact(source_descriptor_numf_closure_point M SourceSetTheoryDescriptors.ZFRSourceDescriptor ps
    (code_numeral M(sf_encode source_def_succ10))(source_numf_closure_member M 4)pair q bq5 eq5
    pairinst sbody bq4 first second inner point(code_numeral M 1)(zeroM M)(code_numeral M 6)
    BPS6 BS106 BM4 BQ6 BEQ56 HNext HInst(proj2 HQ5)HTInst HPI HSBody(proj1 HQ4)
    HFirst HSecond HInner HPoint). }
 destruct(sf_relation_total M SFImpl p eq4)as(targetA&HTargetA).
 pose proof(source_implication_shift_graph M p eq4 targetA ps eq5 inner HTargetA HInner HPS HEQ45)as HTAShift.
 destruct(sf_relation_total M SFImpl exs targetA)as(use&HUse).
 assert(BTargetA:source_bounded M targetA(code_numeral M 6)).
 { exact(proj2(source_bounded_accept_binary M SFImpl p eq4 targetA(code_numeral M 6)(or_intror(or_intror eq_refl))HTargetA)(conj BP6 BEQ46)). }
 assert(BSBody:source_bounded M sbody(code_numeral M 6)).
 { exact(proj2(source_bounded_accept_binary M SFAnd _ _ sbody(code_numeral M 6)(or_introl eq_refl)HSBody)(conj BS106 BM4)). }
 assert(BExS:source_bounded M exs(code_numeral M 6)).
 { apply(proj2(source_bounded_accept_unary M SFEx sbody exs(code_numeral M 6)(or_intror eq_refl)HExS)).
   apply(source_bounded_monotone M sbody(code_numeral M 6)(code_numeral M 7)BSBody). do 6 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 pose proof(source_zfr_exists_implication M sbody exs targetA inner point use(code_numeral M 6)(code_numeral M 6)
   BExS BTargetA HExS HTAShift HPoint HUse PPoint)as PUse.
 destruct(sf_relation_total M SFImpl(numf_closure_condition_shift_code M)eq4)as(targetMiddle&HTargetMiddle).
 destruct(sf_relation_total M SFImpl(numf_closure_succ_shift_code M)targetMiddle)as(targetShift&HTargetShift).
 destruct(sf_relation_total M SFImpl bp targetShift)as(witness&HWitness).
 pose proof(source_implication_shift_graph M _ eq3 mq _ eq4 targetMiddle HMQ HTargetMiddle
   (source_numf_closure_condition_shift M)HEQ34)as HMiddleShift.
 pose proof(source_implication_shift_graph M _ mq result _ targetMiddle targetShift HResultOut HTargetShift
   (source_numf_closure_succ_shift M)HMiddleShift)as HResultShift.
 assert(BS1:source_bounded M(numf_closure_succ_shift_code M)(code_numeral M 6)).
 { apply(source_numf_bound_to_six M _ 3 ltac:(lia)). exact(source_shift_bound M _ _(code_numeral M 2)
   (numerical_def_successor_bound M)(source_numf_closure_succ_shift M)). }
 assert(BC1:source_bounded M(numf_closure_condition_shift_code M)(code_numeral M 6)).
 { apply(source_numf_bound_to_six M _ 4 ltac:(lia)). apply(source_shift_bound M(numf_closure_condition_code M)(numf_closure_condition_shift_code M)(code_numeral M 3));[|apply source_numf_closure_condition_shift].
   apply SourceNumeralLift.source_formula_numeral_bounded,representation_closure_finite_bound. }
 set(env:=fun idx:nat=>match idx with 0=>numf_closure_succ_shift_code M|1=>numf_closure_condition_shift_code M|
   2=>source_numf_closure_member M 3|3=>exs|4=>p|_=>eq4 end).
 pose proof(proj1 HPairP)as HBPAnd.
 assert(PWitness:source_zfr_provable M witness).
 { apply(source_zfr_prop_two M nc_step_law nc_step_use nc_step_result source_numf_closure_step_program env(code_numeral M 6)law use witness).
   - intros[|[|[|[|[|idx]]]]];cbn[env];assumption.
   - unfold nc_step_law. nc_graph.
   - unfold nc_step_use. nc_graph.
   - unfold nc_step_result,nc_step_body. nc_graph.
   - exact PLaw.
   - exact PUse. }
 pose proof(source_numf_bound_to_six M result 3 ltac:(lia)(source_numf_closure_statement_bounded M q result BQ HResult))as BResult.
 pose proof(source_numf_bound_to_six M ep 3 ltac:(lia)BEP)as BEP6.
 destruct(sf_relation_total M SFImpl ep result)as(map&HMap).
 pose proof(source_zfr_exists_implication M bp ep result targetShift witness map(code_numeral M 6)(code_numeral M 6)
   BEP6 BResult(proj2 HPairP)HResultShift HWitness HMap PWitness)as PMap.
 assert(BS0:source_bounded M(numf_closure_succ_code M)(code_numeral M 6))by(exact(source_numf_bound_to_six M _ 2 ltac:(lia)(numerical_def_successor_bound M))).
 assert(BC0:source_bounded M(numf_closure_condition_code M)(code_numeral M 6)).
 { apply(source_numf_bound_to_six M _ 3 ltac:(lia)). apply SourceNumeralLift.source_formula_numeral_bounded,representation_closure_finite_bound. }
 pose proof(source_numf_bound_to_six M eq3 3 ltac:(lia)BEQ3)as BEQ36.
 set(lastenv:=fun idx:nat=>match idx with 0=>numf_closure_succ_code M|1=>numf_closure_condition_code M|2=>ep|_=>eq3 end).
 apply(source_zfr_prop_two M _ _ _ source_numf_closure_induction_program lastenv(code_numeral M 6)old map result).
 - intros[|[|[|idx]]];cbn[lastenv];assumption.
 - nc_graph.
 - nc_graph.
 - nc_graph.
 - exact POld.
 - exact PMap.
Qed.
Print Assumptions source_zfr_numf_closure_step.
