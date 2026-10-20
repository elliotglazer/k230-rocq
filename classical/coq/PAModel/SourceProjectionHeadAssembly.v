(** Assemble carrier coverage, Op4's literal profile, and quantified
    child correctness into a parent existential-representation point. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded SourcePropositionalTemplates
 SourceDescriptorProvability SourceDescriptorPrograms SourceDescriptorNamedPrograms SourceDescriptorNamedUniversal
 SourceRepresentationDifferenceProgram SourceNamedVacuity SourceNamedQuantifierRules SourceProjectionGuardedTransfer.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition EPA_coverage_body:=SPTImpl(SPTSlot 0)(SPTSlot 13).
Definition EPA_operation:=SPTImpl(SPTSlot 15)(SPTImpl(SPTSlot 13)(SPTIff(SPTSlot 14)(SPTSlot 11))).
Definition EPA_condition:=SPTAnd(SPTSlot 15)(SPTAnd(SPTSlot 7)(SPTSlot 16)).
Definition EPA_parent_body:=SPTImpl(SPTSlot 0)(SPTIff(SPTSlot 14)(SPTSlot 12)).
Definition EPA_result:=SPTImpl(SPTSlot 15)(SPTImpl(SPTSlot 7)(SPTImpl(SPTSlot 16)(SPTSlot 17))).
Ltac epa_ctx:=apply SPTCtx;cbn;auto 16.
Lemma projection_program_weaken A a:source_prop_program A a ->
 forall B,(forall p,In p A ->In p B)->source_prop_program B a.
Proof.
 intro H. induction H;intros B HB.
 - apply SPTCtx,HB. exact H.
 - apply SPTII,IHsource_prop_program. intros p[<-|HP];[now left|right;now apply HB].
 - eapply SPTIE;[apply IHsource_prop_program1|apply IHsource_prop_program2];exact HB.
 - apply SPTExp,IHsource_prop_program,HB.
 - apply SPTCI;[apply IHsource_prop_program1|apply IHsource_prop_program2];exact HB.
 - eapply SPTCE1. apply IHsource_prop_program,HB.
 - eapply SPTCE2. apply IHsource_prop_program,HB.
 - apply SPTDI1,IHsource_prop_program,HB.
 - apply SPTDI2,IHsource_prop_program,HB.
 - eapply SPTDE.
   + apply IHsource_prop_program1,HB.
   + apply IHsource_prop_program2. intros p[<-|HP];[now left|right;now apply HB].
   + apply IHsource_prop_program3. intros p[<-|HP];[now left|right;now apply HB].
 - apply SPTPc.
Qed.
Lemma EPA_point_program:source_prop_program
 [EPG_result;SPTImpl(SPTSlot 16)EPA_coverage_body;EPA_operation](SPTImpl EPA_condition EPA_parent_body).
Proof.
 unfold EPG_result,EPA_coverage_body,EPA_operation,EPA_condition,EPA_parent_body,SPTIff.
 do 2 apply SPTII.
 assert(HOp:source_prop_program
  [SPTSlot 0;SPTAnd(SPTSlot 15)(SPTAnd(SPTSlot 7)(SPTSlot 16));
   SPTImpl(SPTSlot 7)(SPTImpl(SPTSlot 0)(SPTAnd(SPTImpl(SPTSlot 11)(SPTSlot 12))(SPTImpl(SPTSlot 12)(SPTSlot 11)))) ;
   SPTImpl(SPTSlot 16)(SPTImpl(SPTSlot 0)(SPTSlot 13));
   SPTImpl(SPTSlot 15)(SPTImpl(SPTSlot 13)(SPTAnd(SPTImpl(SPTSlot 14)(SPTSlot 11))(SPTImpl(SPTSlot 11)(SPTSlot 14))))]
  (SPTAnd(SPTImpl(SPTSlot 14)(SPTSlot 11))(SPTImpl(SPTSlot 11)(SPTSlot 14)))).
 { eapply SPTIE with(a:=SPTSlot 13).
   - eapply SPTIE with(a:=SPTSlot 15);[epa_ctx|]. apply SPTCE1 with(b:=SPTAnd(SPTSlot 7)(SPTSlot 16));epa_ctx.
   - eapply SPTIE with(a:=SPTSlot 0);[|epa_ctx]. eapply SPTIE with(a:=SPTSlot 16);[epa_ctx|].
     apply SPTCE2 with(a:=SPTSlot 7). apply SPTCE2 with(a:=SPTSlot 15);epa_ctx. }
 assert(HP:source_prop_program
  [SPTSlot 0;SPTAnd(SPTSlot 15)(SPTAnd(SPTSlot 7)(SPTSlot 16));
   SPTImpl(SPTSlot 7)(SPTImpl(SPTSlot 0)(SPTAnd(SPTImpl(SPTSlot 11)(SPTSlot 12))(SPTImpl(SPTSlot 12)(SPTSlot 11)))) ;
   SPTImpl(SPTSlot 16)(SPTImpl(SPTSlot 0)(SPTSlot 13));
   SPTImpl(SPTSlot 15)(SPTImpl(SPTSlot 13)(SPTAnd(SPTImpl(SPTSlot 14)(SPTSlot 11))(SPTImpl(SPTSlot 11)(SPTSlot 14))))]
  (SPTAnd(SPTImpl(SPTSlot 11)(SPTSlot 12))(SPTImpl(SPTSlot 12)(SPTSlot 11)))).
 { eapply SPTIE with(a:=SPTSlot 0);[|epa_ctx]. eapply SPTIE with(a:=SPTSlot 7);[epa_ctx|].
   apply SPTCE1 with(b:=SPTSlot 16). apply SPTCE2 with(a:=SPTSlot 15);epa_ctx. }
 apply SPTCI;apply SPTII.
 - eapply SPTIE with(a:=SPTSlot 11).
   + apply SPTCE1 with(b:=SPTImpl(SPTSlot 12)(SPTSlot 11)). eapply projection_program_weaken;[exact HP|]. cbn;auto 12.
   + eapply SPTIE with(a:=SPTSlot 14);[|epa_ctx]. apply SPTCE1 with(b:=SPTImpl(SPTSlot 11)(SPTSlot 14)).
     eapply projection_program_weaken;[exact HOp|]. cbn;auto 12.
 - eapply SPTIE with(a:=SPTSlot 11).
   + apply SPTCE2 with(a:=SPTImpl(SPTSlot 14)(SPTSlot 11)). eapply projection_program_weaken;[exact HOp|]. cbn;auto 12.
   + eapply SPTIE with(a:=SPTSlot 12);[|epa_ctx]. apply SPTCE2 with(a:=SPTImpl(SPTSlot 11)(SPTSlot 12)).
     eapply projection_program_weaken;[exact HP|]. cbn;auto 12.
Qed.
Lemma EPA_result_program:source_prop_program[SPTImpl EPA_condition(SPTSlot 17)]EPA_result.
Proof.
 unfold EPA_condition,EPA_result. do 3 apply SPTII.
 eapply SPTIE with(a:=SPTAnd(SPTSlot 15)(SPTAnd(SPTSlot 7)(SPTSlot 16)));[epa_ctx|].
 apply SPTCI;[epa_ctx|apply SPTCI;epa_ctx].
Qed.
Theorem source_descriptor_projection_head_assembly M T values p coveragebody parentbody result k:
 (forall i,source_bounded M(values i)k) ->
 code_relation M values(source_prop_expression EPA_coverage_body)coveragebody ->
 source_named_quantifier M true p coveragebody(values 16) ->
 code_relation M values(source_prop_expression EPA_parent_body)parentbody ->
 source_named_quantifier M true p parentbody(values 17) ->
 source_named_vacuous M p(values 15) ->source_named_vacuous M p(values 7) ->source_named_vacuous M p(values 16) ->
 source_descriptor_template M T values EPG_result ->source_descriptor_template M T values EPA_operation ->
 code_relation M values(source_prop_expression EPA_result)result ->source_descriptor_provable M T result.
Proof.
 intros HB HC HCov HP HParent VO VH VC PGuard POp HResult.
 assert(PCov:source_descriptor_template M T values(SPTImpl(SPTSlot 16)EPA_coverage_body)).
 { intros f HF. destruct(source_prop_template_binary M values SFImpl(SPTSlot 16)EPA_coverage_body f HF)as(u&v&HU&HV&HO).
   change(u=values 16)in HU. subst u. rewrite(code_relation_functional M _ values v coveragebody HV HC)in HO.
   exact(source_descriptor_named_all_specialization M T p coveragebody(values 16)f k
    (source_prop_template_bound M values EPA_coverage_body k HB coveragebody HC)HCov HO). }
 assert(PAll:source_descriptor_template M T values(SPTImpl EPA_condition(SPTSlot 17))).
 { apply(source_descriptor_template_named_all M T values p EPA_condition EPA_parent_body 17 parentbody k HB HP HParent).
   - unfold EPA_condition. cbn[source_prop_named_vacuity]. auto.
   - apply(source_descriptor_template_program M T values k _ _ HB EPA_point_program).
     intros q[<-|[<-|[<-|[]]]];assumption. }
 exact(source_descriptor_template_program M T values k _ _ HB EPA_result_program
  ltac:(intros q[<-|[]];exact PAll)result HResult).
Qed.
Print Assumptions source_descriptor_projection_head_assembly.
