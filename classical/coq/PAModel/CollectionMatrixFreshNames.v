(** Retain every fixed name mentioned in the binary Collection matrix,
    including the input-container name A, then assemble allocated roles. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  TemplateFormulaFresh ExpressionFreshElimination FreshMembershipNames FreshNames FreshPropagation
  CollectionSupportCleanup CollectionMatrixInstance CollectionSupportedKernel
  NumericalSingleton NumericalFreshSingleton NumericalTaggedComprehension.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma collection_matrix_fresh_container M rho name T A B R I U V Theta Z :
  expression_fresh M rho name (E_collection_choices T A B R I U V Theta Z) ->
  expression_name_avoids M rho name A.
Proof.
  unfold E_collection_choices. intro H.
  apply expression_fresh_disjunction_parts in H. destruct H as [_ H].
  apply expression_fresh_disjunction_parts in H. destruct H as [_ H].
  unfold E_collection_selected in H.
  apply collection_fresh_exists_parts in H. destruct H as [_ H].
  apply expression_fresh_conjunction_parts in H. destruct H as [_ H].
  apply expression_fresh_conjunction_parts in H. destruct H as [H _].
  apply expression_fresh_conjunction_parts in H. destruct H as [_ H].
  exact (proj2 (expression_fresh_membership_names M rho name U A H)).
Qed.

Theorem collection_matrix_fresh_all_names M rho name T A B R I U V Theta Z :
  expression_fresh M rho name (E_collection_choices T A B R I U V Theta Z) ->
  name<>zeroM M /\
  (forall N,In N [T;A;B;R;I;U;V;Z] -> expression_name_avoids M rho name N) /\
  expression_fresh M rho name Theta.
Proof.
  intro H.
  pose proof (collection_matrix_fresh_container M rho name T A B R I U V Theta Z H) as HA.
  pose proof (collection_matrix_fresh_nonzero M rho name T A B R I U V Theta Z H) as H0.
  destruct (collection_matrix_fresh_parts M rho name T A B R I U V Theta Z H)
    as [HI [HR [HV [HB [HT [HU [HZ HTheta]]]]]]].
  split;[exact H0|]. split;[|exact HTheta].
  intros N [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];assumption.
Qed.

Theorem collection_matrix_fresh_numeric_names M i v t a b r u theta z m name :
  code_relation M (collection_matrix_parameters M i v t a b r u theta z)
    E_collection_parameter_matrix m ->
  formula_fresh M m name ->
  name<>zeroM M /\ (forall value,In value [t;a;b;r;i;u;v;z] -> value<>name).
Proof.
  intros HM HF.
  set (rho:=collection_matrix_parameters M i v t a b r u theta z).
  assert (HE:expression_fresh M rho name E_collection_parameter_matrix).
  { intros f Hf. rewrite (code_relation_functional M _ rho f m Hf HM). exact HF. }
  destruct (collection_matrix_fresh_all_names M rho name
    (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8) HE)
    as [H0 [HNames _]].
  split;[exact H0|].
  assert (Ht:t<>name) by exact (HNames (CEvar 2) ltac:(cbn;tauto) t eq_refl).
  assert (Ha:a<>name) by exact (HNames (CEvar 3) ltac:(cbn;tauto) a eq_refl).
  assert (Hb:b<>name) by exact (HNames (CEvar 4) ltac:(cbn;tauto) b eq_refl).
  assert (Hr:r<>name) by exact (HNames (CEvar 5) ltac:(cbn;tauto) r eq_refl).
  assert (Hi:i<>name) by exact (HNames (CEvar 0) ltac:(cbn;tauto) i eq_refl).
  assert (Hu:u<>name) by exact (HNames (CEvar 6) ltac:(cbn;tauto) u eq_refl).
  assert (Hv:v<>name) by exact (HNames (CEvar 1) ltac:(cbn;tauto) v eq_refl).
  assert (Hz:z<>name) by exact (HNames (CEvar 8) ltac:(cbn;tauto) z eq_refl).
  intros value [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];assumption.
Qed.

Lemma collection_nodup_insert {D:Type} (prefix suffix:list D) value :
  NoDup (prefix++suffix) -> ~In value (prefix++suffix) ->
  NoDup (prefix++value::suffix).
Proof.
  induction prefix as [|a prefix IH];cbn;intros HN HV.
  - now constructor.
  - inversion HN as [|a' rest Hnot Hrest];subst. constructor.
    + rewrite in_app_iff. rewrite in_app_iff in Hnot.
      intro H. destruct H as [H|[H|H]].
      * apply Hnot;now left.
      * apply HV;now left.
      * apply Hnot;now right.
    + apply IH;[assumption|]. intro H. apply HV;now right.
Qed.

Theorem collection_allocated_roles_nodup M i v t a b r u theta z m x q target k query tag :
  NoDup [t;a;b;r;i;x;u;v;z;q;target] ->
  code_relation M (collection_matrix_parameters M i v t a b r u theta z)
    E_collection_parameter_matrix m ->
  formula_fresh M m k -> formula_fresh M m query ->
  k<>query -> k<>x -> k<>q -> query<>x -> query<>q ->
  (forall value,In value [t;a;b;r;k;query;x;u;v;z;q] -> coding_lt M value tag) ->
  NoDup [t;a;b;r;k;query;x;tag;u;v;z;q].
Proof.
  intros HN HM HK HQ HKQ HKX HKq HQX HQq HT.
  destruct (collection_matrix_fresh_numeric_names M i v t a b r u theta z m k HM HK) as [_ HKN].
  destruct (collection_matrix_fresh_numeric_names M i v t a b r u theta z m query HM HQ) as [_ HQN].
  assert (HBase:NoDup [t;a;b;r;x;u;v;z;q]).
  { pose proof (NoDup_remove_1 [t;a;b;r] [x;u;v;z;q;target] i HN) as H1.
    exact (NoDup_remove_1 [t;a;b;r;x;u;v;z;q] [] target H1). }
  assert (HNotK:~In k [t;a;b;r;x;u;v;z;q]).
  { intro H. destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]];
      subst;try contradiction;exact (HKN k ltac:(cbn;tauto) eq_refl). }
  assert (HWithK:NoDup [t;a;b;r;k;x;u;v;z;q]).
  { exact (collection_nodup_insert [t;a;b;r] [x;u;v;z;q] k HBase HNotK). }
  assert (HNotQ:~In query [t;a;b;r;k;x;u;v;z;q]).
  { intro H. destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]];
      subst;try contradiction;exact (HQN query ltac:(cbn;tauto) eq_refl). }
  assert (HWithQ:NoDup [t;a;b;r;k;query;x;u;v;z;q]).
  { exact (collection_nodup_insert [t;a;b;r;k] [x;u;v;z;q] query HWithK HNotQ). }
  apply (collection_nodup_insert [t;a;b;r;k;query;x] [u;v;z;q] tag HWithQ).
  intro H. exact (fresh_singleton_lt_neq M tag tag (HT tag H) eq_refl).
Qed.

Print Assumptions collection_matrix_fresh_all_names.
Print Assumptions collection_matrix_fresh_numeric_names.
Print Assumptions collection_allocated_roles_nodup.
