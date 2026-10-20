(** Two actual named existential eliminations for extending an EnvF
    witness inside C. Formula holes remain arbitrary internal codes. *)
From PAModel Require Import Model CodeExpressions SourceBounded SourcePropositionalTemplates
 SourceDescriptorProvability SourceDescriptorPrograms SourceDescriptorNamedPrograms SourceNamedQuantifierRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition EIW_oldbody:=SPTAnd(SPTSlot 4)(SPTSlot 2).
Definition EIW_extbody:=SPTAnd(SPTSlot 6)(SPTSlot 5).
Definition EIW_nextbody:=SPTAnd(SPTSlot 4)(SPTSlot 5).
Definition EIW_targetbody:=SPTAnd(SPTSlot 6)(SPTSlot 7).
Definition EIW_extgoal:=SPTImpl(SPTSlot 4)(SPTSlot 8).
Definition EIW_extmap:=SPTImpl(SPTSlot 9)EIW_extgoal.
Definition EIW_fixed:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl(SPTSlot 3)(SPTSlot 9)))).
Definition EIW_oldgoal:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 3)(SPTSlot 8))).
Definition EIW_oldmap:=SPTImpl(SPTSlot 10)EIW_oldgoal.
Definition EIW_result:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 3)(SPTImpl(SPTSlot 10)(SPTSlot 8)))).
Ltac eiw_ctx:=apply SPTCtx;cbn;auto 14.
Lemma EIW_leaf_program:source_prop_program
 [SPTImpl EIW_nextbody(SPTSlot 7);SPTImpl EIW_targetbody(SPTSlot 8)](SPTImpl EIW_extbody EIW_extgoal).
Proof.
 unfold EIW_nextbody,EIW_targetbody,EIW_extbody,EIW_extgoal. do 2 apply SPTII.
 eapply SPTIE with(a:=SPTAnd(SPTSlot 6)(SPTSlot 7));[eiw_ctx|]. apply SPTCI.
 - apply SPTCE1 with(b:=SPTSlot 5);eiw_ctx.
 - eapply SPTIE with(a:=SPTAnd(SPTSlot 4)(SPTSlot 5));[eiw_ctx|]. apply SPTCI;[eiw_ctx|].
   apply SPTCE2 with(a:=SPTSlot 6);eiw_ctx.
Qed.
Lemma EIW_old_program:source_prop_program[EIW_extmap;EIW_fixed](SPTImpl EIW_oldbody EIW_oldgoal).
Proof.
 unfold EIW_extmap,EIW_extgoal,EIW_fixed,EIW_oldbody,EIW_oldgoal. do 4 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 4);[|apply SPTCE1 with(b:=SPTSlot 2);eiw_ctx].
 eapply SPTIE with(a:=SPTSlot 9);[eiw_ctx|].
 eapply SPTIE with(a:=SPTSlot 3);[|eiw_ctx].
 eapply SPTIE with(a:=SPTSlot 2);[|apply SPTCE2 with(a:=SPTSlot 4);eiw_ctx].
 eapply SPTIE with(a:=SPTSlot 1);[|eiw_ctx]. eapply SPTIE with(a:=SPTSlot 0);eiw_ctx.
Qed.
Lemma EIW_result_program:source_prop_program[EIW_oldmap]EIW_result.
Proof.
 unfold EIW_oldmap,EIW_oldgoal,EIW_result. do 4 apply SPTII.
 eapply SPTIE with(a:=SPTSlot 3);[|eiw_ctx]. eapply SPTIE with(a:=SPTSlot 1);[|eiw_ctx].
 eapply SPTIE with(a:=SPTSlot 0);[|eiw_ctx]. eapply SPTIE with(a:=SPTSlot 10);eiw_ctx.
Qed.
Theorem source_descriptor_env_in_closure_witness_shell M T rho bound oldname newname oldbody extbody nextbody targetbody result:
 (forall i,source_bounded M(rho i)bound)->
 code_relation M rho(source_prop_expression EIW_oldbody)oldbody->
 code_relation M rho(source_prop_expression EIW_extbody)extbody->
 code_relation M rho(source_prop_expression EIW_nextbody)nextbody->
 code_relation M rho(source_prop_expression EIW_targetbody)targetbody->
 source_named_quantifier M false oldname oldbody(rho 10)->
 source_named_quantifier M false newname extbody(rho 9)->
 source_named_quantifier M false oldname nextbody(rho 7)->
 source_named_quantifier M false newname targetbody(rho 8)->
 source_prop_named_vacuity M rho newname EIW_extgoal->
 source_prop_named_vacuity M rho oldname EIW_oldgoal->
 source_descriptor_template M T rho EIW_fixed->
 code_relation M rho(source_prop_expression EIW_result)result->source_descriptor_provable M T result.
Proof.
 intros HB HO HE HN HT QO QE QN QT VE VO PF HResult.
 pose proof(source_descriptor_template_named_intro M T rho oldname EIW_nextbody 7 nextbody bound
  (source_prop_template_bound M rho EIW_nextbody bound HB nextbody HN)HN QN)as PN.
 pose proof(source_descriptor_template_named_intro M T rho newname EIW_targetbody 8 targetbody bound
  (source_prop_template_bound M rho EIW_targetbody bound HB targetbody HT)HT QT)as PT.
 assert(PLeaf:source_descriptor_template M T rho(SPTImpl EIW_extbody EIW_extgoal)).
 { apply(source_descriptor_template_program M T rho bound _ _ HB EIW_leaf_program). intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho newname EIW_extbody 9 EIW_extgoal extbody HE QE VE PLeaf)as PE.
 assert(POld:source_descriptor_template M T rho(SPTImpl EIW_oldbody EIW_oldgoal)).
 { apply(source_descriptor_template_program M T rho bound _ _ HB EIW_old_program). intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho oldname EIW_oldbody 10 EIW_oldgoal oldbody HO QO VO POld)as PO.
 exact(source_descriptor_template_program M T rho bound _ _ HB EIW_result_program
  ltac:(intros p[<-|[]];exact PO)result HResult).
Qed.
Print Assumptions source_descriptor_env_in_closure_witness_shell.
