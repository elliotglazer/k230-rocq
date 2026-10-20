(** Actual five-witness existential assembly for An minus (L minus R).
    The extra An witness remains the same one in both the Op2 law and
    the implication representation premise. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourcePropositionalTemplates SourceDescriptorProvability SourceDescriptorNamedPrograms SourceNamedQuantifierRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition IRS_left:=SPTAnd(SPTSlot 2)(SPTSlot 6).
Definition IRS_right:=SPTAnd(SPTSlot 3)(SPTSlot 7).
Definition IRS_middle:=SPTAnd(SPTSlot 4)(SPTSlot 9).
Definition IRS_final:=SPTAnd(SPTSlot 5)(SPTSlot 10).
Definition IRS_target:=SPTAnd(SPTSlot 5)(SPTSlot 8).
Definition IRS_An:=SPTAnd(SPTSlot 16)(SPTSlot 17).
Definition IRS_point:=SPTImpl(SPTAnd(SPTSlot 9)(SPTSlot 10))
 (SPTImpl(SPTSlot 17)(SPTImpl(SPTSlot 6)(SPTImpl(SPTSlot 7)(SPTSlot 8)))).
Definition IRS_first:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 11)))).
Definition IRS_second:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 16)(SPTImpl(SPTSlot 4)(SPTSlot 12)))).
Definition IRS_goal0:=SPTImpl IRS_middle(SPTImpl IRS_left(SPTImpl IRS_right(SPTImpl IRS_An(SPTSlot 13)))).
Definition IRS_after0:=SPTImpl(SPTSlot 12)IRS_goal0.
Definition IRS_goal5:=SPTImpl IRS_left(SPTImpl IRS_right(SPTImpl IRS_An(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 13))))).
Definition IRS_after5:=SPTImpl(SPTSlot 11)IRS_goal5.
Definition IRS_goal4:=SPTImpl IRS_left(SPTImpl IRS_An(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 13)))).
Definition IRS_after4:=SPTImpl(SPTSlot 15)IRS_goal4.
Definition IRS_goal3:=SPTImpl(SPTSlot 15)(SPTImpl IRS_An(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 13)))).
Definition IRS_after3:=SPTImpl(SPTSlot 14)IRS_goal3.
Definition IRS_result:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 14)(SPTImpl(SPTSlot 15)(SPTImpl IRS_An(SPTSlot 13))))).
Definition IRS_goal6:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 13)).
Definition IRS_after6:=SPTImpl(SPTSlot 18)IRS_goal6.
Definition IRS_exists index:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot index)).
Ltac irs_ctx:=apply SPTCtx;cbn;auto 16.
Lemma IRS_leaf_program:source_prop_program[IRS_point;SPTImpl IRS_target(SPTSlot 13)](SPTImpl IRS_final IRS_goal0).
Proof.
 unfold IRS_point,IRS_target,IRS_final,IRS_goal0,IRS_middle,IRS_left,IRS_right,IRS_An.
 do 5 apply SPTII. eapply SPTIE with(a:=SPTAnd(SPTSlot 5)(SPTSlot 8));[irs_ctx|]. apply SPTCI.
 - apply SPTCE1 with(b:=SPTSlot 10). irs_ctx.
 - eapply SPTIE with(a:=SPTSlot 7).
   + eapply SPTIE with(a:=SPTSlot 6).
     * eapply SPTIE with(a:=SPTSlot 17).
       -- eapply SPTIE with(a:=SPTAnd(SPTSlot 9)(SPTSlot 10));[irs_ctx|]. apply SPTCI.
          ++ apply SPTCE2 with(a:=SPTSlot 4). irs_ctx.
          ++ apply SPTCE2 with(a:=SPTSlot 5). irs_ctx.
       -- apply SPTCE2 with(a:=SPTSlot 16). irs_ctx.
     * apply SPTCE2 with(a:=SPTSlot 2). irs_ctx.
   + apply SPTCE2 with(a:=SPTSlot 3). irs_ctx.
Qed.
Lemma IRS_middle_program:source_prop_program[IRS_after0;IRS_second](SPTImpl IRS_middle IRS_goal5).
Proof.
 unfold IRS_after0,IRS_second,IRS_goal0,IRS_goal5,IRS_middle,IRS_left,IRS_right,IRS_An.
 do 6 apply SPTII.
 eapply SPTIE with(a:=SPTAnd(SPTSlot 16)(SPTSlot 17));[|irs_ctx].
 eapply SPTIE with(a:=SPTAnd(SPTSlot 3)(SPTSlot 7));[|irs_ctx].
 eapply SPTIE with(a:=SPTAnd(SPTSlot 2)(SPTSlot 6));[|irs_ctx].
 eapply SPTIE with(a:=SPTAnd(SPTSlot 4)(SPTSlot 9));[|irs_ctx].
 eapply SPTIE with(a:=SPTSlot 12);[irs_ctx|].
 eapply SPTIE with(a:=SPTSlot 4).
 - eapply SPTIE with(a:=SPTSlot 16).
   + eapply SPTIE with(a:=SPTSlot 1).
     * eapply SPTIE with(a:=SPTSlot 0);irs_ctx.
     * irs_ctx.
   + apply SPTCE1 with(b:=SPTSlot 17). irs_ctx.
 - apply SPTCE1 with(b:=SPTSlot 9). irs_ctx.
Qed.
Lemma IRS_right_program:source_prop_program[IRS_after5;IRS_first](SPTImpl IRS_right IRS_goal4).
Proof.
 unfold IRS_after5,IRS_first,IRS_goal5,IRS_goal4,IRS_left,IRS_right. do 5 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 1);[|irs_ctx]. eapply SPTIE with(a:=SPTSlot 0);[|irs_ctx].
 eapply SPTIE with(a:=IRS_An);[|irs_ctx].
 eapply SPTIE with(a:=SPTAnd(SPTSlot 3)(SPTSlot 7));[|irs_ctx].
 eapply SPTIE with(a:=SPTAnd(SPTSlot 2)(SPTSlot 6));[|irs_ctx].
 eapply SPTIE with(a:=SPTSlot 11);[irs_ctx|].
 eapply SPTIE with(a:=SPTSlot 3).
 - eapply SPTIE with(a:=SPTSlot 2).
   + eapply SPTIE with(a:=SPTSlot 1).
     * eapply SPTIE with(a:=SPTSlot 0);irs_ctx.
     * irs_ctx.
   + apply SPTCE1 with(b:=SPTSlot 6). irs_ctx.
 - apply SPTCE1 with(b:=SPTSlot 7). irs_ctx.
Qed.
Lemma IRS_left_program:source_prop_program[IRS_after4](SPTImpl IRS_left IRS_goal3).
Proof.
 unfold IRS_after4,IRS_goal4,IRS_goal3. do 5 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 1);[|irs_ctx]. eapply SPTIE with(a:=SPTSlot 0);[|irs_ctx].
 eapply SPTIE with(a:=IRS_An);[|irs_ctx]. eapply SPTIE with(a:=IRS_left);[|irs_ctx].
 eapply SPTIE with(a:=SPTSlot 15);irs_ctx.
Qed.
Lemma IRS_result_program:source_prop_program[IRS_after3]IRS_result.
Proof.
 unfold IRS_after3,IRS_goal3,IRS_result. do 5 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 1);[|irs_ctx]. eapply SPTIE with(a:=SPTSlot 0);[|irs_ctx].
 eapply SPTIE with(a:=IRS_An);[|irs_ctx]. eapply SPTIE with(a:=SPTSlot 15);[|irs_ctx].
 eapply SPTIE with(a:=SPTSlot 14);irs_ctx.
Qed.
Lemma IRS_An_program:source_prop_program[IRS_result;IRS_exists 14;IRS_exists 15](SPTImpl IRS_An IRS_goal6).
Proof.
 unfold IRS_result,IRS_exists,IRS_goal6. do 3 apply SPTII.
 eapply SPTIE with(a:=IRS_An);[|irs_ctx].
 eapply SPTIE with(a:=SPTSlot 15).
 - eapply SPTIE with(a:=SPTSlot 14).
   + eapply SPTIE with(a:=SPTSlot 1);[|irs_ctx]. eapply SPTIE with(a:=SPTSlot 0);irs_ctx.
   + eapply SPTIE with(a:=SPTSlot 1);[|irs_ctx]. eapply SPTIE with(a:=SPTSlot 0);irs_ctx.
 - eapply SPTIE with(a:=SPTSlot 1);[|irs_ctx]. eapply SPTIE with(a:=SPTSlot 0);irs_ctx.
Qed.
Lemma IRS_close_program:source_prop_program[IRS_after6;IRS_exists 18]IRS_goal6.
Proof.
 unfold IRS_after6,IRS_exists,IRS_goal6. do 2 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 1);[|irs_ctx]. eapply SPTIE with(a:=SPTSlot 0);[|irs_ctx].
 eapply SPTIE with(a:=SPTSlot 18);[irs_ctx|].
 eapply SPTIE with(a:=SPTSlot 1);[|irs_ctx]. eapply SPTIE with(a:=SPTSlot 0);irs_ctx.
Qed.
Theorem source_descriptor_implication_witness_shell M T rho k x0 x5 x4 x3 x6 final middle left right an target:
 (forall i,source_bounded M(rho i)k)->
 code_relation M rho(source_prop_expression IRS_final)final->code_relation M rho(source_prop_expression IRS_middle)middle->
 code_relation M rho(source_prop_expression IRS_left)left->code_relation M rho(source_prop_expression IRS_right)right->
 code_relation M rho(source_prop_expression IRS_An)an->code_relation M rho(source_prop_expression IRS_target)target->
 source_named_quantifier M false x0 final(rho 12)->source_named_quantifier M false x5 middle(rho 11)->
 source_named_quantifier M false x4 right(rho 15)->source_named_quantifier M false x3 left(rho 14)->
 source_named_quantifier M false x6 an(rho 18)->source_named_quantifier M false x0 target(rho 13)->
 source_prop_named_vacuity M rho x0 IRS_goal0->source_prop_named_vacuity M rho x5 IRS_goal5->
 source_prop_named_vacuity M rho x4 IRS_goal4->source_prop_named_vacuity M rho x3 IRS_goal3->source_prop_named_vacuity M rho x6 IRS_goal6->
 source_descriptor_template M T rho IRS_point->source_descriptor_template M T rho IRS_first->source_descriptor_template M T rho IRS_second->
 source_descriptor_template M T rho(IRS_exists 14)->source_descriptor_template M T rho(IRS_exists 15)->source_descriptor_template M T rho(IRS_exists 18)->
 source_descriptor_template M T rho IRS_goal6.
Proof.
 intros HB HF HM HL HR HA HT QF QM QR QL QA QT V0 V5 V4 V3 V6 PP PF PS PL PR PA.
 pose proof(source_descriptor_template_named_intro M T rho x0 IRS_target 13 target k(source_prop_template_bound M rho IRS_target k HB target HT)HT QT)as PI.
 assert(PLeaf:source_descriptor_template M T rho(SPTImpl IRS_final IRS_goal0)).
 { apply(source_descriptor_template_program M T rho k _ _ HB IRS_leaf_program). intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho x0 IRS_final 12 IRS_goal0 final HF QF V0 PLeaf)as P0.
 assert(PMiddle:source_descriptor_template M T rho(SPTImpl IRS_middle IRS_goal5)).
 { apply(source_descriptor_template_program M T rho k _ _ HB IRS_middle_program). intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho x5 IRS_middle 11 IRS_goal5 middle HM QM V5 PMiddle)as P5.
 assert(PRight:source_descriptor_template M T rho(SPTImpl IRS_right IRS_goal4)).
 { apply(source_descriptor_template_program M T rho k _ _ HB IRS_right_program). intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho x4 IRS_right 15 IRS_goal4 right HR QR V4 PRight)as P4.
 assert(PLeft:source_descriptor_template M T rho(SPTImpl IRS_left IRS_goal3)).
 { apply(source_descriptor_template_program M T rho k _ _ HB IRS_left_program). intros p[<-|[]]. exact P4. }
 pose proof(source_descriptor_template_named_exists M T rho x3 IRS_left 14 IRS_goal3 left HL QL V3 PLeft)as P3.
 assert(PResult:source_descriptor_template M T rho IRS_result).
 { apply(source_descriptor_template_program M T rho k _ _ HB IRS_result_program). intros p[<-|[]]. exact P3. }
 assert(PAn:source_descriptor_template M T rho(SPTImpl IRS_An IRS_goal6)).
 { apply(source_descriptor_template_program M T rho k _ _ HB IRS_An_program). intros p[<-|[<-|[<-|[]]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho x6 IRS_An 18 IRS_goal6 an HA QA V6 PAn)as P6.
 apply(source_descriptor_template_program M T rho k _ _ HB IRS_close_program). intros p[<-|[<-|[]]];assumption.
Qed.
Print Assumptions source_descriptor_implication_witness_shell.
