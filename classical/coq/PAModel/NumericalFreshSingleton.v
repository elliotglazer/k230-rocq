(** A fresh singleton with a caller-specified numerical container name
    and the pre-existing inner binder of a tagged matrix. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  ProofTemplates NamedLeibnizSteps TemplateBinderFresh NumericalSingleton
  NumericalChosenSingleton SingletonRebind.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Lemma fresh_singleton_lt_neq M x y : coding_lt M x y -> x<>y.
Proof.
  exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) x y).
Qed.

Lemma ns_proof_reinstance M rho e s1 s2 values :
  (forall i,code_relation M rho (s1 i) (values i)) ->
  (forall i,code_relation M rho (s2 i) (values i)) ->
  ns_proof M rho (code_subst s1 e) -> ns_proof M rho (code_subst s2 e).
Proof.
  intros H1 H2 HP f HF. apply HP.
  apply (proj2 (code_subst_graph M rho s1 values H1 e f)).
  exact (proj1 (code_subst_graph M rho s2 values H2 e f) HF).
Qed.

Theorem numerical_fresh_singleton M rho X P Z Fresh x p z base :
  code_relation M rho X x -> code_relation M rho P p ->
  code_relation M rho Z z -> code_relation M rho Fresh base ->
  x<>z -> p=succM M (succM M base) ->
  coding_lt M (zeroM M) base -> coding_lt M x base -> coding_lt M z base ->
  ns_proof M rho (E_wex P (E_raw_singleton X P Z)).
Proof.
  intros HX HP HZ HB Hxz Ep H0 Hx Hz.
  set (A:=CEadd (CEadd Fresh (CEconst 1)) (CEconst 1)).
  set (W:=CEadd A (CEconst 1)).
  assert (HA:code_relation M rho A p).
  { rewrite Ep. apply template_fresh_increment_graph,template_fresh_increment_graph,HB. }
  assert (HW:code_relation M rho W (succM M p)).
  { apply template_fresh_increment_graph,HA. }
  assert (Hxp:coding_lt M x p).
  { rewrite Ep. eapply coding_lt_trans;[exact Hx|].
    eapply coding_lt_trans;apply coding_lt_succ. }
  assert (Hzp:coding_lt M z p).
  { rewrite Ep. eapply coding_lt_trans;[exact Hz|].
    eapply coding_lt_trans;apply coding_lt_succ. }
  assert (HPW:p<>succM M p) by (apply fresh_singleton_lt_neq,coding_lt_succ).
  assert (HXW:x<>succM M p).
  { apply fresh_singleton_lt_neq. eapply coding_lt_trans;[exact Hxp|apply coding_lt_succ]. }
  assert (HWZ:succM M p<>z).
  { apply not_eq_sym,fresh_singleton_lt_neq.
    eapply coding_lt_trans;[exact Hzp|apply coding_lt_succ]. }
  assert (HInt:ns_proof M rho (E_wex A (E_raw_singleton X A Z))).
  { eapply ns_proof_mp.
    - exact (numerical_chosen_singleton M rho X Fresh x base HX HB H0 Hx).
    - exact (numerical_singleton_exists_rebind M rho X A W Z x p (succM M p) z
        HX HA HW HZ HWZ HPW HXW
        (not_eq_sym (fresh_singleton_lt_neq M z p Hzp))
        Hxz). }
  set (body:=E_wex (CEvar 0) (E_raw_singleton (CEvar 1) (CEvar 0) (CEvar 2))).
  set (s1:=fun i=>match i with 0=>A|1=>X|2=>Z|_=>CEconst 0 end).
  set (s2:=fun i=>match i with 0=>P|1=>X|2=>Z|_=>CEconst 0 end).
  set (values:=fun i=>match i with 0=>p|1=>x|2=>z|_=>zeroM M end).
  change (ns_proof M rho (code_subst s2 body)).
  apply (ns_proof_reinstance M rho body s1 s2 values).
  - intros [|[|[|i]]];assumption||reflexivity.
  - intros [|[|[|i]]];assumption||reflexivity.
  - exact HInt.
Qed.

Print Assumptions numerical_fresh_singleton.
