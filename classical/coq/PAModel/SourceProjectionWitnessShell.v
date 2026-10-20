(** Three actual existential eliminations for one binary closure operation.
    Formula slots are arbitrary internal codes with explicit vacuity. *)
From PAModel Require Import Model CodeExpressions SourceBounded SourcePropositionalTemplates SourceDescriptorProvability SourceDescriptorPrograms SourceDescriptorNamedPrograms SourceNamedQuantifierRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition PW_left:=SPTAnd(SPTSlot 2)(SPTSlot 5).
Definition PW_right:=SPTAnd(SPTSlot 3)(SPTSlot 6).
Definition PW_output:=SPTAnd(SPTSlot 4)(SPTSlot 8).
Definition PW_target:=SPTAnd(SPTSlot 4)(SPTSlot 7).
Definition PW_point:=SPTImpl(SPTSlot 8)(SPTImpl(SPTSlot 6)(SPTImpl(SPTSlot 5)(SPTSlot 7))).
Definition PW_operation:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 9)))).
Definition PW_goal0:=SPTImpl PW_left(SPTImpl PW_right(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 12)))).
Definition PW_after0:=SPTImpl(SPTSlot 9)PW_goal0.
Definition PW_goal3:=SPTImpl PW_left(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 12))).
Definition PW_after3:=SPTImpl(SPTSlot 11)PW_goal3.
Definition PW_goal4:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 11)(SPTSlot 12))).
Definition PW_after4:=SPTImpl(SPTSlot 10)PW_goal4.
Definition PW_result:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 10)(SPTImpl(SPTSlot 11)(SPTSlot 12)))).
Ltac pw_ctx:=apply SPTCtx;cbn;auto 12.
Lemma PW_leaf_program:source_prop_program[PW_point;SPTImpl PW_target(SPTSlot 12)](SPTImpl PW_output PW_goal0).
Proof.
 unfold PW_point,PW_target,PW_output,PW_goal0,PW_left,PW_right. do 5 apply SPTII.
 eapply SPTIE with(a:=SPTAnd(SPTSlot 4)(SPTSlot 7));[pw_ctx|]. apply SPTCI.
 - apply SPTCE1 with(b:=SPTSlot 8);pw_ctx.
 - eapply SPTIE with(a:=SPTSlot 5).
   + eapply SPTIE with(a:=SPTSlot 6).
     * eapply SPTIE with(a:=SPTSlot 8);[pw_ctx|]. apply SPTCE2 with(a:=SPTSlot 4);pw_ctx.
     * apply SPTCE2 with(a:=SPTSlot 3);pw_ctx.
   + apply SPTCE2 with(a:=SPTSlot 2);pw_ctx.
Qed.
Lemma PW_operation_program:source_prop_program[PW_after0;PW_operation](SPTImpl PW_right PW_goal3).
Proof.
 unfold PW_after0,PW_operation,PW_goal0,PW_goal3,PW_left,PW_right. do 4 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 1);[|pw_ctx]. eapply SPTIE with(a:=SPTSlot 0);[|pw_ctx].
 eapply SPTIE with(a:=SPTAnd(SPTSlot 3)(SPTSlot 6));[|pw_ctx].
 eapply SPTIE with(a:=SPTAnd(SPTSlot 2)(SPTSlot 5));[|pw_ctx].
 eapply SPTIE with(a:=SPTSlot 9);[pw_ctx|].
 eapply SPTIE with(a:=SPTSlot 3).
 - eapply SPTIE with(a:=SPTSlot 2).
   + eapply SPTIE with(a:=SPTSlot 1);[|pw_ctx]. eapply SPTIE with(a:=SPTSlot 0);pw_ctx.
   + apply SPTCE1 with(b:=SPTSlot 5);pw_ctx.
 - apply SPTCE1 with(b:=SPTSlot 6);pw_ctx.
Qed.
Lemma PW_left_program:source_prop_program[PW_after3](SPTImpl PW_left PW_goal4).
Proof.
 unfold PW_after3,PW_goal3,PW_goal4. do 4 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 1);[|pw_ctx]. eapply SPTIE with(a:=SPTSlot 0);[|pw_ctx].
 eapply SPTIE with(a:=PW_left);[|pw_ctx]. eapply SPTIE with(a:=SPTSlot 11);pw_ctx.
Qed.
Lemma PW_result_program:source_prop_program[PW_after4]PW_result.
Proof.
 unfold PW_after4,PW_goal4,PW_result. do 4 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 11);[|pw_ctx]. eapply SPTIE with(a:=SPTSlot 1);[|pw_ctx].
 eapply SPTIE with(a:=SPTSlot 0);[|pw_ctx]. eapply SPTIE with(a:=SPTSlot 10);pw_ctx.
Qed.
Theorem source_descriptor_projection_witness_shell M T rho bound outputname leftname rightname output left right target result:
 (forall i,source_bounded M(rho i)bound)->
 code_relation M rho(source_prop_expression PW_output)output->code_relation M rho(source_prop_expression PW_left)left->
 code_relation M rho(source_prop_expression PW_right)right->code_relation M rho(source_prop_expression PW_target)target->
 source_named_quantifier M false outputname output(rho 9)->source_named_quantifier M false leftname left(rho 10)->
 source_named_quantifier M false rightname right(rho 11)->source_named_quantifier M false outputname target(rho 12)->
 source_prop_named_vacuity M rho outputname PW_goal0->source_prop_named_vacuity M rho rightname PW_goal3->source_prop_named_vacuity M rho leftname PW_goal4->
 source_descriptor_template M T rho PW_point->source_descriptor_template M T rho PW_operation->
 code_relation M rho(source_prop_expression PW_result)result->source_descriptor_provable M T result.
Proof.
 intros HB HO HL HR HT QO QL QR QT V0 V3 V4 PP PO HResult.
 pose proof(source_descriptor_template_named_intro M T rho outputname PW_target 12 target bound
  (source_prop_template_bound M rho PW_target bound HB target HT)HT QT)as PI.
 assert(PLeaf:source_descriptor_template M T rho(SPTImpl PW_output PW_goal0)).
 { apply(source_descriptor_template_program M T rho bound _ _ HB PW_leaf_program). intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho outputname PW_output 9 PW_goal0 output HO QO V0 PLeaf)as P0.
 assert(PRight:source_descriptor_template M T rho(SPTImpl PW_right PW_goal3)).
 { apply(source_descriptor_template_program M T rho bound _ _ HB PW_operation_program). intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho rightname PW_right 11 PW_goal3 right HR QR V3 PRight)as P3.
 assert(PLeft:source_descriptor_template M T rho(SPTImpl PW_left PW_goal4)).
 { apply(source_descriptor_template_program M T rho bound _ _ HB PW_left_program). intros p[<-|[]];exact P3. }
 pose proof(source_descriptor_template_named_exists M T rho leftname PW_left 10 PW_goal4 left HL QL V4 PLeft)as P4.
 exact(source_descriptor_template_program M T rho bound _ _ HB PW_result_program ltac:(intros p[<-|[]];exact P4)result HResult).
Qed.
Print Assumptions source_descriptor_projection_witness_shell.
