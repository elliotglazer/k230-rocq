(** The four actual existential eliminations in the double-difference
    construction. This is a logical shell: its three proof inputs are
    the two literal closure-operation laws and the conjunction point law.
    All matrix holes remain arbitrary internal formulas. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourcePropositionalTemplates SourceDescriptorProvability SourceDescriptorNamedPrograms
 SourceNamedQuantifierRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition RCS_left :=SPTAnd(SPTSlot 2)(SPTSlot 6).
Definition RCS_right :=SPTAnd(SPTSlot 3)(SPTSlot 7).
Definition RCS_middle :=SPTAnd(SPTSlot 4)(SPTSlot 9).
Definition RCS_final :=SPTAnd(SPTSlot 5)(SPTSlot 10).
Definition RCS_target :=SPTAnd(SPTSlot 5)(SPTSlot 8).
Definition RCS_point_law :=SPTImpl(SPTAnd(SPTSlot 9)(SPTSlot 10))
 (SPTImpl(SPTSlot 6)(SPTImpl(SPTSlot 7)(SPTSlot 8))).
Definition RCS_first_law :=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)
 (SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 11)))).
Definition RCS_second_law :=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)
 (SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 4)(SPTSlot 12)))).
Definition RCS_goal0 :=SPTImpl RCS_middle(SPTImpl RCS_left(SPTImpl RCS_right(SPTSlot 13))).
Definition RCS_after0 :=SPTImpl(SPTSlot 12)RCS_goal0.
Definition RCS_goal5 :=SPTImpl RCS_left(SPTImpl RCS_right
 (SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 13)))).
Definition RCS_after5 :=SPTImpl(SPTSlot 11)RCS_goal5.
Definition RCS_goal4 :=SPTImpl RCS_left(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 13))).
Definition RCS_after4 :=SPTImpl(SPTSlot 15)RCS_goal4.
Definition RCS_goal3 :=SPTImpl(SPTSlot 15)(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 13))).
Definition RCS_after3 :=SPTImpl(SPTSlot 14)RCS_goal3.
Definition RCS_result :=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)
 (SPTImpl(SPTSlot 14)(SPTImpl(SPTSlot 15)(SPTSlot 13)))).
Ltac rcs_ctx :=apply SPTCtx;cbn;auto 12.

Lemma RCS_leaf_program :source_prop_program
 [RCS_point_law;SPTImpl RCS_target(SPTSlot 13)](SPTImpl RCS_final RCS_goal0).
Proof.
 unfold RCS_point_law,RCS_target,RCS_final,RCS_goal0,RCS_middle,RCS_left,RCS_right.
 do 4 apply SPTII. eapply SPTIE with(a:=SPTAnd(SPTSlot 5)(SPTSlot 8));[rcs_ctx|].
 apply SPTCI.
 - apply SPTCE1 with(b:=SPTSlot 10). rcs_ctx.
 - eapply SPTIE with(a:=SPTSlot 7).
   + eapply SPTIE with(a:=SPTSlot 6).
     * eapply SPTIE with(a:=SPTAnd(SPTSlot 9)(SPTSlot 10));[rcs_ctx|].
       apply SPTCI.
       -- apply SPTCE2 with(a:=SPTSlot 4). rcs_ctx.
       -- apply SPTCE2 with(a:=SPTSlot 5). rcs_ctx.
     * apply SPTCE2 with(a:=SPTSlot 2). rcs_ctx.
   + apply SPTCE2 with(a:=SPTSlot 3). rcs_ctx.
Qed.

Lemma RCS_middle_program :source_prop_program [RCS_after0;RCS_second_law]
 (SPTImpl RCS_middle RCS_goal5).
Proof.
 unfold RCS_after0,RCS_second_law,RCS_goal0,RCS_middle,RCS_goal5,RCS_left,RCS_right.
 do 5 apply SPTII.
 eapply SPTIE with(a:=SPTAnd(SPTSlot 3)(SPTSlot 7));[|rcs_ctx].
 eapply SPTIE with(a:=SPTAnd(SPTSlot 2)(SPTSlot 6));[|rcs_ctx].
 eapply SPTIE with(a:=SPTAnd(SPTSlot 4)(SPTSlot 9));[|rcs_ctx].
 eapply SPTIE with(a:=SPTSlot 12);[rcs_ctx|].
 eapply SPTIE with(a:=SPTSlot 4).
 - eapply SPTIE with(a:=SPTSlot 2).
   + eapply SPTIE with(a:=SPTSlot 1).
     * eapply SPTIE with(a:=SPTSlot 0);rcs_ctx.
     * rcs_ctx.
   + apply SPTCE1 with(b:=SPTSlot 6). rcs_ctx.
 - apply SPTCE1 with(b:=SPTSlot 9). rcs_ctx.
Qed.

Lemma RCS_right_program :source_prop_program [RCS_after5;RCS_first_law]
 (SPTImpl RCS_right RCS_goal4).
Proof.
 unfold RCS_after5,RCS_first_law,RCS_goal5,RCS_goal4,RCS_left,RCS_right.
 do 4 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 1);[|rcs_ctx].
 eapply SPTIE with(a:=SPTSlot 0);[|rcs_ctx].
 eapply SPTIE with(a:=SPTAnd(SPTSlot 3)(SPTSlot 7));[|rcs_ctx].
 eapply SPTIE with(a:=SPTAnd(SPTSlot 2)(SPTSlot 6));[|rcs_ctx].
 eapply SPTIE with(a:=SPTSlot 11);[rcs_ctx|].
 eapply SPTIE with(a:=SPTSlot 3).
 - eapply SPTIE with(a:=SPTSlot 2).
   + eapply SPTIE with(a:=SPTSlot 1).
     * eapply SPTIE with(a:=SPTSlot 0);rcs_ctx.
     * rcs_ctx.
   + apply SPTCE1 with(b:=SPTSlot 6). rcs_ctx.
 - apply SPTCE1 with(b:=SPTSlot 7). rcs_ctx.
Qed.

Lemma RCS_left_program :source_prop_program [RCS_after4](SPTImpl RCS_left RCS_goal3).
Proof.
 unfold RCS_after4,RCS_goal4,RCS_goal3. do 4 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 1);[|rcs_ctx].
 eapply SPTIE with(a:=SPTSlot 0);[|rcs_ctx].
 eapply SPTIE with(a:=RCS_left);[|rcs_ctx].
 eapply SPTIE with(a:=SPTSlot 15);rcs_ctx.
Qed.

Lemma RCS_result_program :source_prop_program [RCS_after3]RCS_result.
Proof.
 unfold RCS_after3,RCS_goal3,RCS_result. do 4 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 1);[|rcs_ctx].
 eapply SPTIE with(a:=SPTSlot 0);[|rcs_ctx].
 eapply SPTIE with(a:=SPTSlot 15);[|rcs_ctx].
 eapply SPTIE with(a:=SPTSlot 14);rcs_ctx.
Qed.

Theorem source_descriptor_conjunction_witness_shell M T rho k x0 x5 x3 x4
 final middle left right target :
 (forall i,source_bounded M(rho i) k) ->
 code_relation M rho(source_prop_expression RCS_final)final ->
 code_relation M rho(source_prop_expression RCS_middle)middle ->
 code_relation M rho(source_prop_expression RCS_left)left ->
 code_relation M rho(source_prop_expression RCS_right)right ->
 code_relation M rho(source_prop_expression RCS_target)target ->
 source_named_quantifier M false x0 final(rho 12) ->
 source_named_quantifier M false x5 middle(rho 11) ->
 source_named_quantifier M false x3 left(rho 14) ->
 source_named_quantifier M false x4 right(rho 15) ->
 source_named_quantifier M false x0 target(rho 13) ->
 source_prop_named_vacuity M rho x0 RCS_goal0 ->
 source_prop_named_vacuity M rho x5 RCS_goal5 ->
 source_prop_named_vacuity M rho x4 RCS_goal4 ->
 source_prop_named_vacuity M rho x3 RCS_goal3 ->
 source_descriptor_template M T rho RCS_point_law ->
 source_descriptor_template M T rho RCS_first_law ->
 source_descriptor_template M T rho RCS_second_law ->
 source_descriptor_template M T rho RCS_result.
Proof.
 intros HB HF HM HL HR HT QF QM QL QR QT V0 V5 V4 V3 PP PF PS.
 pose proof(source_descriptor_template_named_intro M T rho x0 RCS_target 13 target k
  (source_prop_template_bound M rho RCS_target k HB target HT) HT QT)as PI.
 assert(PLeaf:source_descriptor_template M T rho(SPTImpl RCS_final RCS_goal0)).
 { apply(source_descriptor_template_program M T rho k _ _ HB RCS_leaf_program).
   intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho x0 RCS_final 12 RCS_goal0 final HF QF V0 PLeaf)as P0.
 assert(PMiddle:source_descriptor_template M T rho(SPTImpl RCS_middle RCS_goal5)).
 { apply(source_descriptor_template_program M T rho k _ _ HB RCS_middle_program).
   intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho x5 RCS_middle 11 RCS_goal5 middle HM QM V5 PMiddle)as P5.
 assert(PRight:source_descriptor_template M T rho(SPTImpl RCS_right RCS_goal4)).
 { apply(source_descriptor_template_program M T rho k _ _ HB RCS_right_program).
   intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho x4 RCS_right 15 RCS_goal4 right HR QR V4 PRight)as P4.
 assert(PLeft:source_descriptor_template M T rho(SPTImpl RCS_left RCS_goal3)).
 { apply(source_descriptor_template_program M T rho k _ _ HB RCS_left_program).
   intros p[<-|[]]. exact P4. }
 pose proof(source_descriptor_template_named_exists M T rho x3 RCS_left 14 RCS_goal3 left HL QL V3 PLeft)as P3.
 apply(source_descriptor_template_program M T rho k _ _ HB RCS_result_program).
 intros p[<-|[]]. exact P3.
Qed.

Print Assumptions source_descriptor_conjunction_witness_shell.
