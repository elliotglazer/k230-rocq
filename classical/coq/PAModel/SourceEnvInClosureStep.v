(** Actual EnvF-in-C successor. Its only proof input is the genuine
    previous-count theorem. Head/tail membership transport, witness
    allocation, finite closure operations and ExE are all discharged. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceNumeralLift SourceBounded SourceBoundMonotone
 SourceDefinabilityPrimitives SourceDefinabilityBounds SourceDefinabilityStep SourceFiniteCutoffShift SourceEnvInClosureRecipe SourceEnvInClosureTailProof
 SourceEnvInClosurePointTotal SourceMembershipBlocks SourceMembershipBlockProofs SourceMembershipBlockTail SourcePropositionalTemplates
 SourcePropRenaming SourceDescriptorProvability SourceDescriptorClosure SourceDescriptorPrograms SourceSetTheoryDescriptors SourceZFRProvability
 SourceNumFClosureRecipe SourceNumFClosureSyntax SourceRepresentationClosureRecipe SchemaConstructorBounds.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition EIS_old:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 3)(SPTSlot 5))).
Definition EIS_point:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 4)(SPTImpl(SPTSlot 5)(SPTSlot 6)))).
Definition EIS_head:=SPTImpl(SPTSlot 2)(SPTSlot 4).
Definition EIS_tail:=SPTImpl(SPTSlot 2)(SPTSlot 3).
Definition EIS_result:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTSlot 6))).
Ltac eis_ctx:=apply SPTCtx;cbn;auto 20.
Lemma EIS_program:source_prop_program[EIS_old;EIS_point;EIS_head;EIS_tail]EIS_result.
Proof.
 unfold EIS_old,EIS_point,EIS_head,EIS_tail,EIS_result. do 3 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 5).
 - eapply SPTIE with(a:=SPTSlot 4).
   + eapply SPTIE with(a:=SPTSlot 1);[|eis_ctx]. eapply SPTIE with(a:=SPTSlot 0);eis_ctx.
   + eapply SPTIE with(a:=SPTSlot 2);eis_ctx.
 - eapply SPTIE with(a:=SPTSlot 3).
   + eapply SPTIE with(a:=SPTSlot 1);[|eis_ctx]. eapply SPTIE with(a:=SPTSlot 0);eis_ctx.
   + eapply SPTIE with(a:=SPTSlot 2);eis_ctx.
Qed.
Definition EIS_values M block tail head oldex newex i:=match i with
 |0=>numf_closure_succ_code M|1=>numf_closure_condition_code M|2=>block|3=>tail|4=>head|5=>oldex|6=>newex|_=>zeroM M end.
Local Opaque source_def_successor01 representation_closure_condition.
Theorem source_zfr_env_in_closure_step M count f next old out:
 source_envf M count f->source_envf M(succM M count)next->source_def_step M true f next->
 source_env_in_closure_recipe M count f old->source_env_in_closure_recipe M(succM M count)next out->
 source_zfr_provable M old->source_zfr_provable M out.
Proof.
 intros HF HNext HStep HOld(block&n1&n2&n3&HBlock&HN1&HN2&HN3&HOut)POld.
 destruct(source_zfr_env_in_closure_tail_total M count f old HF HOld POld)
 as(p1&p2&p3&p4&tail&tailout&H1&H2&H3&H4&HTail&HTailOut&PTailOut).
 destruct(source_env_in_closure_spine M tail p4 tailout HTailOut)
 as(oldbody&oldex&oldinner&oldmiddle&HOldBody&HOldEx&HOldInner&HOldMiddle&HOldOut).
 destruct(source_env_in_closure_spine M block n3 out HOut)
 as(newbody&newex&newinner&newmiddle&HNewBody&HNewEx&HNewInner&HNewMiddle&HNewOut).
 destruct(source_zfr_env_in_closure_point_total M count f next p1 p2 p3 p4 n1 n2 n3 oldbody oldex newbody newex
  HF HStep H1 H2 H3 H4 HN1 HN2 HN3 HOldBody HOldEx HNewBody HNewEx)
 as(head&point&HHead&GPoint&PPoint).
 set(K:=succM M(succM M(succM M(succM M count)))).
 assert(HNames:forall i,coding_lt M i(succM M count)->coding_lt M(addM M i(code_numeral M 3))K).
 { intros i HI. rewrite(Arithmetic.add_comm M i(code_numeral M 3)). unfold K. cbn[code_numeral].
   rewrite!Arithmetic.add_succ,Arithmetic.add_zero. do 3 apply coding_lt_succ_cancel. exact HI. }
 assert(HZero:coding_lt M(zeroM M)K)by(apply coding_zero_lt_succ).
 assert(BBlock:source_bounded M block K)by(exact(source_membership_block_bound M _ _ _ block K HNames HZero HBlock)).
 assert(BTail:source_bounded M tail K).
 { apply(source_membership_block_bound M(code_numeral M 4)(zeroM M)count tail K);try assumption.
   intros i HI. change(coding_lt M(addM M i(succM M(code_numeral M 3)))K).
   rewrite source_block_tail_index. apply HNames,coding_lt_succ_cancel. exact HI. }
 destruct(sf_relation_total M SFImpl block head)as(headlaw&HHeadLaw).
 destruct(sf_relation_total M SFImpl block tail)as(taillaw&HTailLaw).
 destruct(source_membership_block_head_tail_laws M(code_numeral M 3)(zeroM M)count block tail head headlaw taillaw K
  HNames HZero HBlock HTail HHead HHeadLaw HTailLaw)as(PHeadLaw&PTailLaw).
 pose proof(source_envf_bound M count f HF)as BF.
 pose proof(source_cutoff_shift_bounded M 1 f p1 count BF H1)as BP1.
 pose proof(source_cutoff_shift_bounded M 1 p1 p2(succM M count)BP1 H2)as BP2.
 pose proof(source_cutoff_shift_bounded M 1 p2 p3(succM M(succM M count))BP2 H3)as BP3.
 pose proof(source_cutoff_shift_bounded M 1 p3 p4(succM M(succM M(succM M count)))BP3 H4)as BP4.
 pose proof(source_envf_bound M(succM M count)next HNext)as BN.
 pose proof(source_cutoff_shift_bounded M 1 next n1(succM M count)BN HN1)as BN1.
 pose proof(source_cutoff_shift_bounded M 1 n1 n2(succM M(succM M count))BN1 HN2)as BN2.
 pose proof(source_cutoff_shift_bounded M 1 n2 n3(succM M(succM M(succM M count)))BN2 HN3)as BN3.
 assert(BMember:source_bounded M(source_numf_closure_member M 3)(succM M K)).
 { apply source_numf_closure_member_bounded;unfold K;schema_small_index. }
 assert(BOEx:source_bounded M oldex K).
 { apply(proj2(source_bounded_accept_unary M SFEx oldbody oldex K(or_intror eq_refl)HOldEx)).
   exact(proj2(source_bounded_accept_binary M SFAnd p4 _ oldbody(succM M K)(or_introl eq_refl)HOldBody)(conj BP4 BMember)). }
 assert(BNEx:source_bounded M newex K).
 { apply(proj2(source_bounded_accept_unary M SFEx newbody newex K(or_intror eq_refl)HNewEx)).
   exact(proj2(source_bounded_accept_binary M SFAnd n3 _ newbody(succM M K)(or_introl eq_refl)HNewBody)(conj BN3 BMember)). }
 assert(BHead:source_bounded M head K).
 { apply(proj2(source_bounded_accept_atom M SFMember _ _ head K(or_introl eq_refl)HHead)). split;unfold K;schema_small_index. }
 assert(BS:source_bounded M(numf_closure_succ_code M)K).
 { apply(source_bounded_monotone M _(code_numeral M 2)K(numerical_def_successor_bound M)). unfold K;schema_small_index. }
 assert(BC:source_bounded M(numf_closure_condition_code M)K).
 { apply(source_bounded_monotone M _(code_numeral M 3)K).
   - apply source_formula_numeral_bounded,representation_closure_finite_bound.
   - unfold K;schema_small_index. }
 set(values:=EIS_values M block tail head oldex newex).
 assert(BValues:forall i,source_bounded M(values i)K).
 { intros[|[|[|[|[|[|[|i]]]]]]];cbn[values EIS_values];try assumption;apply source_bounded_accept_falsity. }
 assert(GOld:code_relation M values(source_prop_expression EIS_old)tailout).
 { unfold EIS_old. eapply source_prop_template_join;[reflexivity| |exact HOldOut].
   eapply source_prop_template_join;[reflexivity| |exact HOldMiddle].
   eapply source_prop_template_join;[reflexivity|reflexivity|exact HOldInner]. }
 assert(GP:code_relation M values(source_prop_expression EIS_point)point)by(exact GPoint).
 assert(GHead:code_relation M values(source_prop_expression EIS_head)headlaw).
 { unfold EIS_head. eapply source_prop_template_join;[reflexivity|reflexivity|exact HHeadLaw]. }
 assert(GTail:code_relation M values(source_prop_expression EIS_tail)taillaw).
 { unfold EIS_tail. eapply source_prop_template_join;[reflexivity|reflexivity|exact HTailLaw]. }
 assert(GResult:code_relation M values(source_prop_expression EIS_result)out).
 { unfold EIS_result. eapply source_prop_template_join;[reflexivity| |exact HNewOut].
   eapply source_prop_template_join;[reflexivity| |exact HNewMiddle].
   eapply source_prop_template_join;[reflexivity|reflexivity|exact HNewInner]. }
 apply(proj1(source_zfr_descriptor_provable M out)).
 apply(source_descriptor_prop_program M ZFRSourceDescriptor _ _ EIS_program values K out BValues);[|exact GResult].
 intros p[<-|[<-|[<-|[<-|[]]]]]g HG.
 - rewrite(code_relation_functional M _ values g tailout HG GOld). exact(proj2(source_zfr_descriptor_provable M _)PTailOut).
 - rewrite(code_relation_functional M _ values g point HG GP). exact(proj2(source_zfr_descriptor_provable M _)PPoint).
 - rewrite(code_relation_functional M _ values g headlaw HG GHead). exact(source_descriptor_provable_from_empty M ZFRSourceDescriptor headlaw PHeadLaw).
 - rewrite(code_relation_functional M _ values g taillaw HG GTail). exact(source_descriptor_provable_from_empty M ZFRSourceDescriptor taillaw PTailLaw).
Qed.
Print Assumptions source_zfr_env_in_closure_step.
