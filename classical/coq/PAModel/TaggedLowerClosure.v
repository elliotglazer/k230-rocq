(** Universal lower profile. A fresh output test name is chosen above
    the fixed context, so contextual generalization is justified by an actual
    vacuity proof; stopping alpha then returns to the kernel's binder. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  ProofTemplates NamedLeibnizSteps NamedAlpha FreshNames NamedBinderFresh NamedSubstitutionRules
  TemplateBinderFresh TemplateNamedSubstitution NumericalVacuitySteps NumericalVacuity
  NumericalRawPair NumericalTaggedComprehension NumericalTaggedKernel TaggedLowerPoint
  TaggedUniversalSelected TaggedSelectedAllocation NumericalFreshSingleton
  RawMarkerExclusions RawMarkerQuantifiers StoppingAlpha QuotientAtomTemplates
  NumericalKP0 TemplatePropositional ProofMacros QuantifierMacros.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.
Unset Implicit Arguments.

Definition E_tagged_lower_context :=
  E_wa (E_marker_empty (CEvar 4) (CEvar 7))
    (E_wa (E_wn (E_weq (CEvar 3) (CEvar 4)))
      (E_wa (E_raw_pair (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 7))
        (E_tagged_request_clause (CEvar 0) (CEvar 10) (CEvar 3) (CEvar 4)
          (CEvar 5) (CEvar 6) (CEvar 8) (CEvar 7)))).
Definition E_tagged_lower_body y theta :=
  E_wim (E_tagged_profile y (CEvar 3) (CEvar 4) theta) (E_wel y (CEvar 6)).
Definition E_tagged_lower_closed :=
  E_wim E_tagged_lower_context (E_wal (CEvar 0) (E_tagged_lower_body (CEvar 0) (CEvar 8))).

Lemma lower_context_program A B C D F :
  proof_macro nil (E_wim A (E_wim B (E_wim C (E_wim D F))) :: nil)
    (E_wim (E_wa A (E_wa B (E_wa C D))) F).
Proof.
  apply macro_discharge,macro_deduction.
  eapply md_mp with (a:=D).
  - apply tagged_md_right with (a:=C),tagged_md_right with (a:=B),
      tagged_md_right with (a:=A),md_hyp;now left.
  - eapply md_mp with (a:=C).
    + apply tagged_md_left with (b:=D),tagged_md_right with (a:=B),
        tagged_md_right with (a:=A),md_hyp;now left.
    + eapply md_mp with (a:=B).
      * apply tagged_md_left with (b:=E_wa C D),tagged_md_right with (a:=A),md_hyp;now left.
      * eapply md_mp with (a:=A).
        -- apply tagged_md_left with (b:=E_wa B (E_wa C D)),md_hyp;now left.
        -- apply md_global,PM_input;now left.
Qed.

Theorem numerical_tagged_lower_closed M rho :
  selected_fixed_roles_distinct M rho -> selected_fixed_roles_nonzero M rho ->
  formula_fresh M (rho 8) (rho 10) ->
  named_binder_absent M (rho 8) (rho 5) -> named_binder_absent M (rho 8) (rho 4) ->
  ns_proof M rho E_tagged_lower_closed.
Proof.
  intros HD HN HF HR HT.
  destruct (code_relation_total M E_tagged_lower_context rho) as [c HC].
  destruct (code_relation_total M (E_tagged_lower_body (CEvar 0) (CEvar 8)) rho) as [b HB].
  set (names:=[zeroM M;rho 0;rho 3;rho 4;rho 5;rho 6;rho 7;rho 10;rho 8;c;b]).
  set (x:=finite_name_bound M names).
  assert (Bound:forall v,In v names -> coding_lt M v x).
  { intros v Hv. apply finite_name_bound_above,Hv. }
  assert (HXtheta:formula_fresh M (rho 8) x).
  { apply formula_above_is_fresh,Bound. unfold names;cbn;tauto. }
  destruct (named_substitution_binder_absent_total M (rho 8) (rho 0) x
    (named_formula_fresh_binder_absent M (rho 8) x HXtheta)) as [mx Hmx].
  set (env:=fun i=>if Nat.eq_dec i 1 then x else if Nat.eq_dec i 9 then mx else rho i).
  assert (Role:forall i,i<9 -> selected_query_role M env i =
    if Nat.eq_dec i 1 then x else selected_query_role M rho i).
  { intros i Hi. do 9 (destruct i as [|i];[reflexivity|]);lia. }
  assert (RB:forall i,i<9 -> i<>1 -> i<>2 -> coding_lt M (selected_query_role M rho i) x).
  { intros i Hi Hi1 Hi2. apply Bound. unfold names.
    do 9 (destruct i as [|i];[cbn in *;tauto|]);lia. }
  assert (D:selected_fixed_roles_distinct M env).
  { intros i j Hi Hj Hi2 Hj2 Hij. rewrite (Role i Hi),(Role j Hj).
    destruct (Nat.eq_dec i 1) as [->|Hi1],(Nat.eq_dec j 1) as [->|Hj1].
    - contradiction.
    - apply not_eq_sym,fresh_singleton_lt_neq,RB;assumption.
    - apply fresh_singleton_lt_neq,RB;assumption.
    - apply HD;assumption. }
  assert (N:selected_fixed_roles_nonzero M env).
  { intros i Hi Hi2. rewrite (Role i Hi). destruct (Nat.eq_dec i 1) as [->|Hi1].
    - apply not_eq_sym,fresh_singleton_lt_neq,Bound. unfold names;cbn;tauto.
    - apply HN;assumption. }
  assert (HS:expression_named_substitution M env env (env 0) (env 1) (CEvar 8) (CEvar 9)).
  { intros f g F G. change (f=rho 8) in F. change (g=mx) in G. subst f g. exact Hmx. }
  assert (HA:expression_binder_absent M env (env 1) (CEvar 8)).
  { intros f F. change (f=rho 8) in F. subst f.
    exact (named_formula_fresh_binder_absent M (rho 8) x HXtheta). }
  pose proof (numerical_tagged_lower_point M env D N HF HR HT HS HA) as HPoint.
  assert (HOpen:ns_proof M env (E_wim E_tagged_lower_context
    (E_tagged_lower_body (CEvar 1) (CEvar 9)))).
  { apply (ns_proof_macro M env (E_lower_point :: nil)).
    - intros e [<-|[]]. exact HPoint.
    - apply lower_context_program. }
  assert (HContext:code_relation M env E_tagged_lower_context c).
  { change (code_relation M rho E_tagged_lower_context c). exact HC. }
  assert (HVac:ns_proof M env (E_vac (CEvar 1) E_tagged_lower_context)).
  { intros f F. apply (numerical_vacuity M x c f).
    - apply formula_above_is_fresh,Bound. unfold names;cbn;tauto.
    - exact (proj1 (expression_vacuity_graph M env (CEvar 1) E_tagged_lower_context
        x c f eq_refl HContext) F). }
  pose proof (marker_generalize_one M env (CEvar 1) E_tagged_lower_context
    (E_tagged_lower_body (CEvar 1) (CEvar 9)) HVac HOpen) as HAllX.
  assert (HBenv:code_relation M env (E_tagged_lower_body (CEvar 0) (CEvar 8)) b).
  { change (code_relation M rho (E_tagged_lower_body (CEvar 0) (CEvar 8)) b). exact HB. }
  assert (RY:expression_named_replace M env env (rho 0) x (CEvar 0) (CEvar 1)).
  { intros a z A Z. change (a=rho 0) in A. change (z=x) in Z. subst a z. now left. }
  assert (Fixed:forall i,i=3 \/ i=4 \/ i=6 ->
    expression_named_replace M env env (rho 0) x (CEvar i) (CEvar i)).
  { intros i Hi a z A Z. destruct Hi as [Ei|[Ei|Ei]];subst i;
      cbn [code_relation] in A,Z;subst a z;right;split;try reflexivity.
    - exact (HD 3 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (HD 4 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (HD 6 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (Sub:expression_named_substitution M env env (rho 0) x
    (E_tagged_lower_body (CEvar 0) (CEvar 8)) (E_tagged_lower_body (CEvar 1) (CEvar 9))).
  { unfold E_tagged_lower_body,E_tagged_profile. apply expression_ns_implication.
    - apply expression_ns_disjunction;[exact (HN 0 ltac:(lia) ltac:(lia))| |].
      + apply (expression_ns_atom M env env (rho 0) x true);[exact RY|apply Fixed;tauto].
      + apply expression_ns_disjunction;[exact (HN 0 ltac:(lia) ltac:(lia))| |].
        * apply (expression_ns_atom M env env (rho 0) x true);[exact RY|apply Fixed;tauto].
        * apply expression_ns_conjunction;[exact (HN 0 ltac:(lia) ltac:(lia))| |exact HS].
          apply (expression_ns_atom M env env (rho 0) x false);[exact RY|apply Fixed;tauto].
    - apply (expression_ns_atom M env env (rho 0) x false);[exact RY|apply Fixed;tauto]. }
  destruct (code_relation_total M (E_tagged_lower_body (CEvar 1) (CEvar 9)) env) as [bx HBX].
  assert (Hxy:rho 0<>x).
  { apply fresh_singleton_lt_neq,Bound. unfold names;cbn;tauto. }
  pose proof (proj2 (proj1 (ns_stopping_alpha M env (CEvar 0) (CEvar 1)
    (E_tagged_lower_body (CEvar 0) (CEvar 8)) (E_tagged_lower_body (CEvar 1) (CEvar 9))
    (rho 0) x b bx eq_refl eq_refl HBenv HBX Hxy
    (formula_above_is_fresh M b x (Bound b ltac:(unfold names;cbn;tauto)))
    (Sub b bx HBenv HBX)))) as HAlpha.
  pose proof (ns_proof_syl M env E_tagged_lower_context
    (E_wal (CEvar 1) (E_tagged_lower_body (CEvar 1) (CEvar 9)))
    (E_wal (CEvar 0) (E_tagged_lower_body (CEvar 0) (CEvar 8))) HAllX HAlpha) as HFinal.
  change (ns_proof M rho E_tagged_lower_closed) in HFinal. exact HFinal.
Qed.

Print Assumptions numerical_tagged_lower_closed.
