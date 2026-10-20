(** Actual empty-environment-in-C proof. The empty parameter block is
    retained in the exact statement and is discharged by ordinary logic. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceNumeralLift
 OldNamedSyntaxBridge SchemaConstructorBounds SourceBounded SourceDefinabilityPrimitives SourceEnvironmentCarrierBase SourceFiniteCutoffShift SourceQfFunctionality
 SourceEnvInClosureRecipe SourceMembershipBlocks SourceNumFClosureSyntax SourceNumFClosureBounds SourceNumFClosureRecipe SourceNumFClosureInduction
 SourceWitnessProofComposition SourcePropositionalRebase SourcePropositionalTemplates SourceRepresentationClosureRecipe SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition EIC_base_old:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 2)).
Definition EIC_base_result:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 3)(SPTSlot 2))).
Lemma EIC_base_program:source_prop_program[EIC_base_old]EIC_base_result.
Proof.
 unfold EIC_base_old,EIC_base_result. do 3 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 1);[|apply SPTCtx;cbn;auto].
 eapply SPTIE with(a:=SPTSlot 0);apply SPTCtx;cbn;auto.
Qed.
Local Opaque source_def_successor01 representation_closure_condition.
Theorem source_zfr_env_in_closure_zero M out:
 source_env_in_closure_recipe M(zeroM M)(code_numeral M(sf_encode source_def_empty))out->source_zfr_provable M out.
Proof.
 intros(block&first&second&shifted&HB&H1&H2&H3&HO).
 assert(HE:source_cutoff_shift M 1(code_numeral M(sf_encode source_def_empty))(code_numeral M(sf_encode source_def_empty))).
 { rewrite<-environment_empty_cutoff at 2.
   exact(source_cutoff_shift_fixed_source M 1(fun _=>zeroM M)source_def_empty _ _
    (source_formula_numeral_graph M source_def_empty)
    (source_formula_numeral_graph M(C.subst_form(source_shift_sigma 1)source_def_empty))). }
 rewrite(source_cutoff_shift_functional M 1 _ first _ H1 HE)in H2.
 rewrite(source_cutoff_shift_functional M 1 _ second _ H2 HE)in H3.
 rewrite(source_cutoff_shift_functional M 1 _ shifted _ H3 HE)in HO.
 apply source_membership_block_zero in HB.
 destruct(source_numf_member_shell_total M(code_numeral M(sf_encode source_def_empty))3)as(body&ex&HBody&HEx).
 destruct(sf_relation_total M SFImpl(numf_closure_condition_code M)ex)as(middle&HMiddle).
 destruct(sf_relation_total M SFImpl(numf_closure_succ_code M)middle)as(old&HOld).
 pose proof(source_numf_closure_statement_join M _ body ex middle old(conj HBody HEx)HMiddle HOld)as HLaw.
 pose proof(source_zfr_numf_closure_zero M old HLaw)as POld.
 pose proof(proj2(source_numf_member_shell_bounded M _ 3 body ex(numerical_def_empty_bound M)(conj HBody HEx)))as BEx.
 assert(BBlock:source_bounded M block(code_numeral M 3)).
 { apply(proj2(source_bounded_accept_binary M SFImpl(zeroM M)(zeroM M)block(code_numeral M 3)
    (or_intror(or_intror eq_refl))HB)). split;apply source_bounded_accept_falsity. }
 assert(BS:source_bounded M(numf_closure_succ_code M)(code_numeral M 3)).
 { apply SourceBoundMonotone.source_bounded_monotone with(k:=code_numeral M 2);[apply numerical_def_successor_bound|].
   do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 assert(BC:source_bounded M(numf_closure_condition_code M)(code_numeral M 3)).
 { apply source_formula_numeral_bounded,representation_closure_finite_bound. }
 set(rho:=fun i=>match i with 0=>numf_closure_succ_code M|1=>numf_closure_condition_code M|2=>ex|_=>block end).
 assert(GOld:code_relation M rho(source_prop_expression EIC_base_old)old).
 { unfold EIC_base_old. eapply source_prop_template_join;[reflexivity| |exact HOld].
   eapply source_prop_template_join;[reflexivity|reflexivity|exact HMiddle]. }
 assert(GEx:code_relation M(env_in_closure_values block(code_numeral M(sf_encode source_def_empty)))
  (E_sf SFEx(E_sf SFAnd(CEvar 1)(CEconst(sf_make SFMember 0 3)))(CEconst 0))ex).
 { eapply source_numf_code_join;[|reflexivity|exact HEx].
   eapply source_numf_code_join;[reflexivity|reflexivity|exact HBody]. }
 assert(GResult:code_relation M rho(source_prop_expression EIC_base_result)out).
 { unfold E_env_in_closure in HO.
   destruct(schema_expression_split M _ SFImpl _ _ out HO)as(s&c&HS&HC&HOut).
   change(s=numf_closure_succ_code M)in HS. subst s.
   destruct(schema_expression_split M _ SFImpl _ _ c HC)as(cl&inner&HCl&HInner&HCOut).
   change(cl=numf_closure_condition_code M)in HCl. subst cl.
   destruct(schema_expression_split M _ SFImpl _ _ inner HInner)as(b&e&HB0&HE0&HInnerOut).
   change(b=block)in HB0. subst b.
   rewrite(code_relation_functional M _ _ e ex HE0 GEx)in HInnerOut.
   unfold EIC_base_result. eapply source_prop_template_join;[reflexivity| |exact HOut].
   eapply source_prop_template_join;[reflexivity| |exact HCOut].
   eapply source_prop_template_join;[reflexivity|reflexivity|exact HInnerOut]. }
 exact(source_zfr_prop_one M EIC_base_old EIC_base_result EIC_base_program rho(code_numeral M 3)old out
  ltac:(intros[|[|[|i]]];cbn[rho];assumption)GOld GResult POld).
Qed.
Print Assumptions source_zfr_env_in_closure_zero.
