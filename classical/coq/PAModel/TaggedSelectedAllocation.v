(** The singleton query name is allocated here, after the target formula
    has been fixed. No ghost singleton witness or external bound remains. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT ProofClosure
  CodeExpressions NumericalProofs ProofTemplates NamedLeibnizSteps FreshNames
  TemplateBinderFresh TemplateNamedSubstitution TaggedUniversalSelected
  TaggedSelectedDischarge NumericalFreshSingleton.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.
Unset Implicit Arguments.

Fixpoint finite_name_bound M (names:list (carrier M)) : carrier M :=
  match names with
  | nil=>succM M (zeroM M)
  | x::xs=>succM M (addM M x (finite_name_bound M xs))
  end.
Lemma finite_name_bound_above M names x :
  In x names -> coding_lt M x (finite_name_bound M names).
Proof.
  induction names as [|a names IH];cbn;intro H;[contradiction|].
  destruct H as [<-|H].
  - exists (finite_name_bound M names). reflexivity.
  - eapply coding_lt_trans with (y:=addM M a (finite_name_bound M names));[|apply coding_lt_succ].
    rewrite (Arithmetic.add_comm M a). apply lt_left_sum,IH,H.
Qed.

Definition selected_fixed_roles_distinct M rho :=
  forall i j,i<9 -> j<9 -> i<>2 -> j<>2 -> i<>j ->
    selected_query_role M rho i<>selected_query_role M rho j.
Definition selected_fixed_roles_nonzero M rho :=
  forall i,i<9 -> i<>2 -> selected_query_role M rho i<>zeroM M.

Theorem numerical_tagged_selected_allocated M rho :
  selected_fixed_roles_distinct M rho -> selected_fixed_roles_nonzero M rho ->
  formula_fresh M (rho 8) (rho 10) ->
  expression_named_substitution M rho rho (rho 0) (rho 1) (CEvar 8) (CEvar 9) ->
  expression_binder_absent M rho (rho 1) (CEvar 8) ->
  ns_proof M rho E_selected_result.
Proof.
  intros HD HN HF HSub HAbs.
  destruct (code_relation_total M E_selected_result rho) as [result HResult].
  set (names:=[zeroM M;rho 0;rho 1;rho 3;rho 4;rho 5;rho 6;rho 7;rho 10;rho 8;result]).
  set (base:=finite_name_bound M names).
  set (p:=succM M (succM M base)).
  set (env:=fun i=>if Nat.eq_dec i 2 then p else if Nat.eq_dec i 11 then base else rho i).
  assert (E:forall i,i<9 -> selected_query_role M env i =
    if Nat.eq_dec i 2 then p else selected_query_role M rho i).
  { intros i Hi. do 9 (destruct i as [|i];[reflexivity|]);lia. }
  assert (HB:forall x,In x names -> coding_lt M x base).
  { intros x Hx. apply finite_name_bound_above,Hx. }
  assert (HP:coding_lt M base p).
  { eapply coding_lt_trans;apply coding_lt_succ. }
  assert (B:forall i,i<9 -> i<>2 -> coding_lt M (selected_query_role M rho i) base).
  { intros i Hi Hi2. apply HB. unfold names.
    do 9 (destruct i as [|i];[cbn in *;tauto|]);lia. }
  assert (D:selected_query_roles_distinct M env).
  { intros i j Hi Hj Hij. rewrite (E i Hi),(E j Hj).
    destruct (Nat.eq_dec i 2) as [->|Hi2],(Nat.eq_dec j 2) as [->|Hj2].
    - contradiction.
    - apply not_eq_sym,fresh_singleton_lt_neq. eapply coding_lt_trans;[apply B;assumption|exact HP].
    - apply fresh_singleton_lt_neq. eapply coding_lt_trans;[apply B;assumption|exact HP].
    - apply HD;assumption. }
  assert (N:selected_query_roles_nonzero M env).
  { intros i Hi. rewrite (E i Hi). destruct (Nat.eq_dec i 2) as [->|Hi2].
    - apply not_eq_sym,fresh_singleton_lt_neq. apply coding_zero_lt_succ.
    - apply HN;assumption. }
  assert (HResult':code_relation M env E_selected_result result).
  { change (code_relation M rho E_selected_result result). exact HResult. }
  assert (HSub':expression_named_substitution M env env (env 0) (env 1) (CEvar 8) (CEvar 9)).
  { change (expression_named_substitution M rho rho (rho 0) (rho 1) (CEvar 8) (CEvar 9)). exact HSub. }
  assert (HAbs':expression_binder_absent M env (env 1) (CEvar 8)).
  { change (expression_binder_absent M rho (rho 1) (CEvar 8)). exact HAbs. }
  assert (Q:ns_proof M env E_selected_result).
  { apply (numerical_tagged_selected_discharge M env result base D N).
    - exact HF.
    - exact HSub'.
    - exact HAbs'.
    - exact HResult'.
    - reflexivity.
    - reflexivity.
    - apply HB. unfold names;cbn;tauto.
    - apply HB. unfold names;cbn;tauto.
    - apply HB. unfold names;cbn;tauto.
    - apply HB. unfold names;cbn;tauto.
    - apply HB. unfold names;cbn;tauto. }
  change (ns_proof M rho E_selected_result) in Q. exact Q.
Qed.

Print Assumptions numerical_tagged_selected_allocated.
