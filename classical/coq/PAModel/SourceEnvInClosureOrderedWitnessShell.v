(** The canonical EnvF witness uses EnvF before member-in-C. This
    variant reuses the checked two-ExE shell with that literal order. *)
From PAModel Require Import Model CodeExpressions SourceBounded SourcePropositionalTemplates
 SourceDescriptorProvability SourceDescriptorPrograms SourceDescriptorNamedPrograms SourceNamedQuantifierRules SourceEnvInClosureWitnessShell.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition EIW_ordered_targetbody:=SPTAnd(SPTSlot 7)(SPTSlot 6).
Lemma EIW_ordered_leaf_program:source_prop_program
 [SPTImpl EIW_nextbody(SPTSlot 7);SPTImpl EIW_ordered_targetbody(SPTSlot 8)](SPTImpl EIW_extbody EIW_extgoal).
Proof.
 unfold EIW_nextbody,EIW_ordered_targetbody,EIW_extbody,EIW_extgoal. do 2 apply SPTII.
 eapply SPTIE with(a:=SPTAnd(SPTSlot 7)(SPTSlot 6));[eiw_ctx|]. apply SPTCI.
 - eapply SPTIE with(a:=SPTAnd(SPTSlot 4)(SPTSlot 5));[eiw_ctx|]. apply SPTCI;[eiw_ctx|].
   apply SPTCE2 with(a:=SPTSlot 6);eiw_ctx.
 - apply SPTCE1 with(b:=SPTSlot 5);eiw_ctx.
Qed.
Theorem source_descriptor_env_in_closure_ordered_shell M T rho bound oldname newname oldbody extbody nextbody targetbody result:
 (forall i,source_bounded M(rho i)bound)->
 code_relation M rho(source_prop_expression EIW_oldbody)oldbody->
 code_relation M rho(source_prop_expression EIW_extbody)extbody->
 code_relation M rho(source_prop_expression EIW_nextbody)nextbody->
 code_relation M rho(source_prop_expression EIW_ordered_targetbody)targetbody->
 source_named_quantifier M false oldname oldbody(rho 10)->
 source_named_quantifier M false newname extbody(rho 9)->
 source_named_quantifier M false oldname nextbody(rho 7)->
 source_named_quantifier M false newname targetbody(rho 8)->
 source_prop_named_vacuity M rho newname EIW_extgoal->source_prop_named_vacuity M rho oldname EIW_oldgoal->
 source_descriptor_template M T rho EIW_fixed->
 code_relation M rho(source_prop_expression EIW_result)result->source_descriptor_provable M T result.
Proof.
 intros HB HO HE HN HT QO QE QN QT VE VO PF HResult.
 pose proof(source_descriptor_template_named_intro M T rho oldname EIW_nextbody 7 nextbody bound
  (source_prop_template_bound M rho EIW_nextbody bound HB nextbody HN)HN QN)as PN.
 pose proof(source_descriptor_template_named_intro M T rho newname EIW_ordered_targetbody 8 targetbody bound
  (source_prop_template_bound M rho EIW_ordered_targetbody bound HB targetbody HT)HT QT)as PT.
 assert(PLeaf:source_descriptor_template M T rho(SPTImpl EIW_extbody EIW_extgoal)).
 { apply(source_descriptor_template_program M T rho bound _ _ HB EIW_ordered_leaf_program). intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho newname EIW_extbody 9 EIW_extgoal extbody HE QE VE PLeaf)as PE.
 assert(POld:source_descriptor_template M T rho(SPTImpl EIW_oldbody EIW_oldgoal)).
 { apply(source_descriptor_template_program M T rho bound _ _ HB EIW_old_program). intros p[<-|[<-|[]]];assumption. }
 pose proof(source_descriptor_template_named_exists M T rho oldname EIW_oldbody 10 EIW_oldgoal oldbody HO QO VO POld)as PO.
 exact(source_descriptor_template_program M T rho bound _ _ HB EIW_result_program
  ltac:(intros p[<-|[]];exact PO)result HResult).
Qed.
Print Assumptions source_descriptor_env_in_closure_ordered_shell.
