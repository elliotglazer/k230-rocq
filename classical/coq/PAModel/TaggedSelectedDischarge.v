(** Existentially discharge the actual fresh singleton used by a selected
    query. Allocation occurs above the already-fixed target formula code. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  ProofTemplates NamedLeibnizSteps FreshNames NamedBinderFresh TemplateBinderFresh
  TemplateNamedSubstitution NumericalSingleton NumericalRawPair NumericalTaggedComprehension
  NumericalTaggedKernel TaggedUniversalSelected NumericalFreshSingleton RawMarkerExclusions
  NumericalKP0 NumericalKP0Requests NumericalVacuitySteps NumericalVacuity
  TemplatePropositional ProofMacros QuantifierMacros.
From Stdlib Require Import Lists.List Lia.
Unset Implicit Arguments.

Definition E_selected_result :=
  E_wim (E_marker_empty (CEvar 4) (CEvar 7))
    (E_wim (E_wn (E_weq (CEvar 3) (CEvar 4)))
      (E_wim (E_raw_pair (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 7))
        (E_wim (E_wel (CEvar 3) (CEvar 6))
          (E_wim (E_tagged_request_clause (CEvar 0) (CEvar 10) (CEvar 3) (CEvar 4)
            (CEvar 5) (CEvar 6) (CEvar 8) (CEvar 7))
            (E_wim (E_wa (E_wel (CEvar 1) (CEvar 3)) (CEvar 9))
              (E_wel (CEvar 1) (CEvar 6))))))).

Lemma selected_argument_reorder Emp Neq Pair Member Req Sing Cond Result :
  proof_macro nil
    (E_wim Emp (E_wim Neq (E_wim Pair (E_wim Member
      (E_wim Req (E_wim Sing (E_wim Cond Result)))))) :: nil)
    (E_wim Sing (E_wim Emp (E_wim Neq (E_wim Pair
      (E_wim Member (E_wim Req (E_wim Cond Result))))))).
Proof.
  apply macro_discharge. do 7 apply macro_deduction.
  eapply md_mp with (a:=Cond);[apply md_hyp;now left|].
  eapply md_mp with (a:=Sing);[apply md_hyp;now right;right;right;right;right;right;left|].
  eapply md_mp with (a:=Req);[apply md_hyp;now right;left|].
  eapply md_mp with (a:=Member);[apply md_hyp;now right;right;left|].
  eapply md_mp with (a:=Pair);[apply md_hyp;now right;right;right;left|].
  eapply md_mp with (a:=Neq);[apply md_hyp;now right;right;right;right;left|].
  eapply md_mp with (a:=Emp);[apply md_hyp;now right;right;right;right;right;left|].
  apply md_global,PM_input;now left.
Qed.

Theorem numerical_tagged_selected_discharge M rho result base :
  selected_query_roles_distinct M rho -> selected_query_roles_nonzero M rho ->
  formula_fresh M (rho 8) (rho 10) ->
  expression_named_substitution M rho rho (rho 0) (rho 1) (CEvar 8) (CEvar 9) ->
  expression_binder_absent M rho (rho 1) (CEvar 8) ->
  code_relation M rho E_selected_result result ->
  rho 11=base -> rho 2=succM M (succM M base) ->
  coding_lt M (zeroM M) base -> coding_lt M (rho 1) base ->
  coding_lt M (rho 7) base -> coding_lt M (rho 8) base -> coding_lt M result base ->
  ns_proof M rho E_selected_result.
Proof.
  intros HD HN HF HSub HAbs HT HBase HP H0 HX HZ HTheta HResult.
  assert (Hbp:coding_lt M base (rho 2)).
  { rewrite HP. eapply coding_lt_trans;apply coding_lt_succ. }
  assert (HFresh:named_binder_absent M (rho 8) (rho 2)).
  { apply named_formula_fresh_binder_absent,formula_above_is_fresh.
    eapply coding_lt_trans;eassumption. }
  pose proof (numerical_tagged_universal_selected M rho HD HN HF HFresh HSub HAbs) as HLocal.
  set (Sing:=E_raw_singleton (CEvar 1) (CEvar 2) (CEvar 7)).
  assert (HPoint:ns_proof M rho (E_wim Sing E_selected_result)).
  { apply (ns_proof_macro M rho
      (E_wim (E_marker_empty (CEvar 4) (CEvar 7))
        (E_wim (E_wn (E_weq (CEvar 3) (CEvar 4)))
          (E_wim (E_raw_pair (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 7))
            (E_wim (E_wel (CEvar 3) (CEvar 6))
              (E_wim (E_tagged_request_clause (CEvar 0) (CEvar 10) (CEvar 3) (CEvar 4)
                (CEvar 5) (CEvar 6) (CEvar 8) (CEvar 7))
                (E_wim Sing (E_wim (E_wa (E_wel (CEvar 1) (CEvar 3)) (CEvar 9))
                  (E_wel (CEvar 1) (CEvar 6)))))))) :: nil)).
    - intros e [<-|[]]. exact HLocal.
    - apply selected_argument_reorder. }
  assert (HS:ns_proof M rho (E_wex (CEvar 2) Sing)).
  { apply (numerical_fresh_singleton M rho (CEvar 1) (CEvar 2) (CEvar 7)
      (CEvar 11) (rho 1) (rho 2) (rho 7) base).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - change (base=rho 11). symmetry. exact HBase.
    - exact (HD 1 7 ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact HP.
    - exact H0.
    - exact HX.
    - exact HZ. }
  assert (HV:ns_proof M rho (E_vac (CEvar 2) E_selected_result)).
  { intros v HV. apply (numerical_vacuity M (rho 2) result v).
    - apply formula_above_is_fresh. eapply coding_lt_trans;eassumption.
    - exact (proj1 (expression_vacuity_graph M rho (CEvar 2) E_selected_result
        (rho 2) result v eq_refl HT) HV). }
  apply (ns_proof_macro M rho
    (E_wim Sing E_selected_result :: E_vac (CEvar 2) E_selected_result ::
      E_wex (CEvar 2) Sing :: nil)).
  - intros e [<-|[<-|[<-|[]]]];assumption.
  - eapply PM_mp;[apply PM_input;now right;right;left|].
    apply kp0_exists_eliminate;apply PM_input;cbn;tauto.
Qed.

Print Assumptions numerical_tagged_selected_discharge.
