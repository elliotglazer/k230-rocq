(** Four actual named existential eliminations for atomic representation.
    The input templates are literal carrier/numeral/operation proofs;
    this shell does not assume representation existence. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourcePropositionalTemplates SourceDescriptorProvability SourceDescriptorNamedPrograms SourceNamedQuantifierRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition AWS_An:=SPTAnd(SPTSlot 2)(SPTSlot 6).
Definition AWS_Ni:=SPTAnd(SPTSlot 3)(SPTSlot 7).
Definition AWS_Nj:=SPTAnd(SPTSlot 4)(SPTSlot 8).
Definition AWS_Op:=SPTAnd(SPTSlot 5)(SPTSlot 9).
Definition AWS_Target:=SPTAnd(SPTSlot 5)(SPTSlot 10).
Definition AWS_point:=SPTImpl(SPTAnd(SPTSlot 9)(SPTAnd(SPTSlot 7)(SPTSlot 8)))(SPTImpl(SPTSlot 6)(SPTSlot 10)).
Definition AWS_operation:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 4)(SPTSlot 11))))).
Definition AWS_An_exists:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 12)).
Definition AWS_Ni_exists:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 13)).
Definition AWS_Nj_exists:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 14)).
Definition AWS_goal0:=SPTImpl AWS_An(SPTImpl AWS_Ni(SPTImpl AWS_Nj(SPTSlot 15))).
Definition AWS_after0:=SPTImpl(SPTSlot 11)AWS_goal0.
Definition AWS_goal5:=SPTImpl AWS_An(SPTImpl AWS_Ni(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 15)))).
Definition AWS_after5:=SPTImpl(SPTSlot 14)AWS_goal5.
Definition AWS_goal4:=SPTImpl AWS_An(SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 15))).
Definition AWS_after4:=SPTImpl(SPTSlot 13)AWS_goal4.
Definition AWS_goal3:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTSlot 15)).
Definition AWS_after3:=SPTImpl(SPTSlot 12)AWS_goal3.
Ltac aws_ctx:=apply SPTCtx;cbn;auto 14.
Lemma AWS_leaf_program:source_prop_program[AWS_point;SPTImpl AWS_Target(SPTSlot 15)](SPTImpl AWS_Op AWS_goal0).
Proof.
 unfold AWS_point,AWS_Target,AWS_Op,AWS_goal0,AWS_An,AWS_Ni,AWS_Nj.
 do 4 apply SPTII. eapply SPTIE with(a:=SPTAnd(SPTSlot 5)(SPTSlot 10));[aws_ctx|].
 apply SPTCI.
 - apply SPTCE1 with(b:=SPTSlot 9). aws_ctx.
 - eapply SPTIE with(a:=SPTSlot 6).
   + eapply SPTIE with(a:=SPTAnd(SPTSlot 9)(SPTAnd(SPTSlot 7)(SPTSlot 8)));[aws_ctx|].
     apply SPTCI.
     * apply SPTCE2 with(a:=SPTSlot 5). aws_ctx.
     * apply SPTCI;[apply SPTCE2 with(a:=SPTSlot 3)|apply SPTCE2 with(a:=SPTSlot 4)];aws_ctx.
   + apply SPTCE2 with(a:=SPTSlot 2). aws_ctx.
Qed.
Lemma AWS_operation_program:source_prop_program[AWS_after0;AWS_operation](SPTImpl AWS_Nj AWS_goal5).
Proof.
 unfold AWS_after0,AWS_operation,AWS_goal0,AWS_goal5,AWS_An,AWS_Ni,AWS_Nj.
 do 5 apply SPTII.
 eapply SPTIE with(a:=SPTAnd(SPTSlot 4)(SPTSlot 8));[|aws_ctx].
 eapply SPTIE with(a:=SPTAnd(SPTSlot 3)(SPTSlot 7));[|aws_ctx].
 eapply SPTIE with(a:=SPTAnd(SPTSlot 2)(SPTSlot 6));[|aws_ctx].
 eapply SPTIE with(a:=SPTSlot 11);[aws_ctx|].
 eapply SPTIE with(a:=SPTSlot 4).
 - eapply SPTIE with(a:=SPTSlot 3).
   + eapply SPTIE with(a:=SPTSlot 2).
     * eapply SPTIE with(a:=SPTSlot 1).
       -- eapply SPTIE with(a:=SPTSlot 0);aws_ctx.
       -- aws_ctx.
     * apply SPTCE1 with(b:=SPTSlot 6). aws_ctx.
   + apply SPTCE1 with(b:=SPTSlot 7). aws_ctx.
 - apply SPTCE1 with(b:=SPTSlot 8). aws_ctx.
Qed.
Lemma AWS_Ni_program:source_prop_program[AWS_after5;AWS_Nj_exists](SPTImpl AWS_Ni AWS_goal4).
Proof.
 unfold AWS_after5,AWS_Nj_exists,AWS_goal5,AWS_goal4. do 4 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 1);[|aws_ctx].
 eapply SPTIE with(a:=SPTSlot 0);[|aws_ctx].
 eapply SPTIE with(a:=AWS_Ni);[|aws_ctx].
 eapply SPTIE with(a:=AWS_An);[|aws_ctx].
 eapply SPTIE with(a:=SPTSlot 14);[aws_ctx|].
 eapply SPTIE with(a:=SPTSlot 1);[|aws_ctx].
 eapply SPTIE with(a:=SPTSlot 0);aws_ctx.
Qed.
Lemma AWS_An_program:source_prop_program[AWS_after4;AWS_Ni_exists](SPTImpl AWS_An AWS_goal3).
Proof.
 unfold AWS_after4,AWS_Ni_exists,AWS_goal4,AWS_goal3. do 3 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 1);[|aws_ctx].
 eapply SPTIE with(a:=SPTSlot 0);[|aws_ctx].
 eapply SPTIE with(a:=AWS_An);[|aws_ctx].
 eapply SPTIE with(a:=SPTSlot 13);[aws_ctx|].
 eapply SPTIE with(a:=SPTSlot 1);[|aws_ctx].
 eapply SPTIE with(a:=SPTSlot 0);aws_ctx.
Qed.
Lemma AWS_result_program:source_prop_program[AWS_after3;AWS_An_exists]AWS_goal3.
Proof.
 unfold AWS_after3,AWS_An_exists,AWS_goal3. do 2 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 1);[|aws_ctx].
 eapply SPTIE with(a:=SPTSlot 0);[|aws_ctx].
 eapply SPTIE with(a:=SPTSlot 12);[aws_ctx|].
 eapply SPTIE with(a:=SPTSlot 1);[|aws_ctx].
 eapply SPTIE with(a:=SPTSlot 0);aws_ctx.
Qed.
Theorem source_descriptor_atomic_witness_shell M T rho k x0 x5 x4 x3 an ni nj op target:
 (forall i,source_bounded M(rho i)k)->
 code_relation M rho(source_prop_expression AWS_An)an->
 code_relation M rho(source_prop_expression AWS_Ni)ni->
 code_relation M rho(source_prop_expression AWS_Nj)nj->
 code_relation M rho(source_prop_expression AWS_Op)op->
 code_relation M rho(source_prop_expression AWS_Target)target->
 source_named_quantifier M false x0 op(rho 11)->
 source_named_quantifier M false x3 an(rho 12)->
 source_named_quantifier M false x4 ni(rho 13)->
 source_named_quantifier M false x5 nj(rho 14)->
 source_named_quantifier M false x0 target(rho 15)->
 source_prop_named_vacuity M rho x0 AWS_goal0->
 source_prop_named_vacuity M rho x5 AWS_goal5->
 source_prop_named_vacuity M rho x4 AWS_goal4->
 source_prop_named_vacuity M rho x3 AWS_goal3->
 source_descriptor_template M T rho AWS_point->
 source_descriptor_template M T rho AWS_operation->
 source_descriptor_template M T rho AWS_An_exists->
 source_descriptor_template M T rho AWS_Ni_exists->
 source_descriptor_template M T rho AWS_Nj_exists->
 source_descriptor_template M T rho AWS_goal3.
Proof.
 intros HB HA HI HJ HO HT QO QA QI QJ QT V0 V5 V4 V3 PP PO PA PI PJ.
 pose proof(source_descriptor_template_named_intro M T rho x0 AWS_Target 15 target k
  (source_prop_template_bound M rho AWS_Target k HB target HT)HT QT)as PT.
 assert(PL:source_descriptor_template M T rho(SPTImpl AWS_Op AWS_goal0)).
 { apply(source_descriptor_template_program M T rho k _ _ HB AWS_leaf_program).
   intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho x0 AWS_Op 11 AWS_goal0 op HO QO V0 PL)as P0.
 assert(PJ0:source_descriptor_template M T rho(SPTImpl AWS_Nj AWS_goal5)).
 { apply(source_descriptor_template_program M T rho k _ _ HB AWS_operation_program).
   intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho x5 AWS_Nj 14 AWS_goal5 nj HJ QJ V5 PJ0)as P5.
 assert(PI0:source_descriptor_template M T rho(SPTImpl AWS_Ni AWS_goal4)).
 { apply(source_descriptor_template_program M T rho k _ _ HB AWS_Ni_program).
   intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho x4 AWS_Ni 13 AWS_goal4 ni HI QI V4 PI0)as P4.
 assert(PA0:source_descriptor_template M T rho(SPTImpl AWS_An AWS_goal3)).
 { apply(source_descriptor_template_program M T rho k _ _ HB AWS_An_program).
   intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho x3 AWS_An 12 AWS_goal3 an HA QA V3 PA0)as P3.
 apply(source_descriptor_template_program M T rho k _ _ HB AWS_result_program).
 intros p[<-|[<-|[]]];assumption.
Qed.
Print Assumptions source_descriptor_atomic_witness_shell.
