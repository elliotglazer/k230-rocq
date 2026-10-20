(** Actual successor witness proof from hygienic numerical graphs.
    All mathematical certificates and both existential eliminations are
    discharged here. The final allocator must still supply the two
    canonical old/output named-binder graphs and literal freshness. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceDefinabilityPrimitives SourceDefinabilityStep
 SourceEnvInClosureRoleMaps SourceEnvInClosureConstructor SourceEnvInClosureExtensionInstance SourceEnvInClosureOrderedWitnessShell
 SourceEnvInClosureWitnessShell SourceRepresentationClosureRecipe SourceNumFClosureRecipe SourcePropositionalTemplates SourceDescriptorNamedPrograms
 SourceDescriptorProvability SourceNamedQuantifierRules SourceNamedVacuity SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Definition EIC_point_values M oldmem headmem previous extension newmem next oldex newex ex i:=match i with
 |0=>numf_closure_succ_code M|1=>numf_closure_condition_code M|2=>oldmem|3=>headmem|4=>previous|5=>extension
 |6=>newmem|7=>next|8=>newex|9=>ex|10=>oldex|_=>zeroM M end.
Local Opaque source_def_extension021 source_def_successor01 representation_closure_condition.
Theorem source_zfr_env_in_closure_successor_point M f next e z k bound previousNamed nextNamed oldmem headmem newmem extension
 oldbody targetbody oldex newex result:
 source_bounded M f k->source_def_step M true f next->
 source_env_witness_renaming M e 3 f previousNamed->source_env_witness_renaming M z 2 next nextNamed->
 sf_relation M SFMember e(CodeExpressions.code_numeral M 2)oldmem->
 sf_relation M SFMember(CodeExpressions.code_numeral M 3)(zeroM M)headmem->
 sf_relation M SFMember z(CodeExpressions.code_numeral M 2)newmem->
 code_relation M(EIC_ext_roles e z(CodeExpressions.code_numeral M 3))EIC_ext_expression extension->
 sf_relation M SFAnd previousNamed oldmem oldbody->sf_relation M SFAnd nextNamed newmem targetbody->
 source_named_quantifier M false e oldbody oldex->source_named_quantifier M false z targetbody newex->
 (forall i,source_bounded M(EIC_point_values M oldmem headmem previousNamed extension newmem nextNamed oldex newex(zeroM M)i)bound)->
 source_named_vacuous M z previousNamed->source_named_vacuous M z newex->
 source_named_vacuous M e(numf_closure_succ_code M)->source_named_vacuous M e(numf_closure_condition_code M)->
 source_named_vacuous M e headmem->source_named_vacuous M e newex->
 e<>z->CodeExpressions.code_numeral M 3<>e->
 z<>zeroM M->z<>CodeExpressions.code_numeral M 1->z<>CodeExpressions.code_numeral M 2->z<>CodeExpressions.code_numeral M 3->
 (forall i,FiniteCoding.coding_lt M i k->i<>zeroM M->addM M i(CodeExpressions.code_numeral M 3)<>e)->
 (forall ex,code_relation M(EIC_point_values M oldmem headmem previousNamed extension newmem nextNamed oldex newex ex)
  (source_prop_expression EIW_result)result)->source_zfr_provable M result.
Proof.
 intros BF HStep HP HN HOld HHead HNew HExt HOldBody HTargetBody QOld QTarget HB VPrev VNew VSucc VCl VHead VOut
  HEZ H3E HZ0 HZ1 HZ2 HZ3 HFresh HResult.
 destruct(sf_relation_total M SFAnd newmem extension)as(extbody&HExtBody).
 destruct(sf_relation_total M SFAnd previousNamed extension)as(nextbody&HNextBody).
 destruct(source_zfr_env_in_closure_extension_instance M e z oldmem headmem newmem extension extbody
  HOld HHead HNew HExt HExtBody HZ0 HZ1 HZ2 ltac:(intro E;exact(HEZ(eq_sym E)))HZ3)
 as(ex&law&QExt&GLaw&PLaw).
 pose proof(source_env_in_closure_named_constructor M f next previousNamed nextNamed extension nextbody e z k
  BF HStep HP HN HExt HNextBody HEZ H3E HFresh)as QNext.
 set(rho:=EIC_point_values M oldmem headmem previousNamed extension newmem nextNamed oldex newex ex).
 assert(BSlots:forall i,source_bounded M(rho i)bound).
 { intros[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]];cbn[rho EIC_point_values].
   1:exact(HB 0). 1:exact(HB 1). 1:exact(HB 2). 1:exact(HB 3). 1:exact(HB 4).
   1:exact(HB 5). 1:exact(HB 6). 1:exact(HB 7). 1:exact(HB 8).
   - apply(source_named_quantifier_bound M false z extbody ex bound);[|exact QExt].
     exact(proj2(source_bounded_accept_binary M SFAnd newmem extension extbody bound(or_introl eq_refl)HExtBody)(conj(HB 6)(HB 5))).
   - exact(HB 10).
   - apply source_bounded_accept_falsity. }
 assert(GOld:code_relation M rho(source_prop_expression EIW_oldbody)oldbody).
 { unfold EIW_oldbody. eapply source_prop_template_join;[reflexivity|reflexivity|exact HOldBody]. }
 assert(GExt:code_relation M rho(source_prop_expression EIW_extbody)extbody).
 { unfold EIW_extbody. eapply source_prop_template_join;[reflexivity|reflexivity|exact HExtBody]. }
 assert(GNext:code_relation M rho(source_prop_expression EIW_nextbody)nextbody).
 { unfold EIW_nextbody. eapply source_prop_template_join;[reflexivity|reflexivity|exact HNextBody]. }
 assert(GTarget:code_relation M rho(source_prop_expression EIW_ordered_targetbody)targetbody).
 { unfold EIW_ordered_targetbody. eapply source_prop_template_join;[reflexivity|reflexivity|exact HTargetBody]. }
 assert(GFixed:code_relation M rho(source_prop_expression EIW_fixed)law).
 { exact GLaw. }
 apply(proj1(source_zfr_descriptor_provable M result)).
 apply(source_descriptor_env_in_closure_ordered_shell M ZFRSourceDescriptor rho bound e z oldbody extbody nextbody targetbody result
  BSlots GOld GExt GNext GTarget QOld QExt QNext QTarget).
 - change(source_named_vacuous M z previousNamed /\source_named_vacuous M z newex). auto.
 - change(source_named_vacuous M e(numf_closure_succ_code M) /\
   (source_named_vacuous M e(numf_closure_condition_code M) /\(source_named_vacuous M e headmem /\source_named_vacuous M e newex))). auto.
 - intros out HOut. rewrite(code_relation_functional M _ rho out law HOut GFixed).
   exact(proj2(source_zfr_descriptor_provable M law)PLaw).
 - exact(HResult ex).
Qed.
Print Assumptions source_zfr_env_in_closure_successor_point.
