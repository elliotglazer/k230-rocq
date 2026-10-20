(** Eliminate the actual envelope and pair witnesses after a raw Collection
    construction. The only construction premise is its proof under those
    two hypotheses; both existence proofs below come from K. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates NamedLeibnizSteps TemplatePropositional TemplateFormulaFresh
  ProofMacros QuantifierMacros NumericalKP0 NumericalKP0Eligibility NumericalVacuitySteps
  NumericalFreshEnvelope NumericalFreshPair NumericalRawEnvelope NumericalRawPair
  RawMarkerExclusions.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem numerical_collection_close_auxiliaries M rho T A B R Z Q FB FR Goal
    t a b r z q baseB baseR :
  code_relation M rho T t -> code_relation M rho A a -> code_relation M rho B b ->
  code_relation M rho R r -> code_relation M rho Z z -> code_relation M rho Q q ->
  code_relation M rho FB baseB -> code_relation M rho FR baseR ->
  t<>q -> a<>q -> q<>zeroM M -> b<>z -> t<>z -> z<>zeroM M ->
  b=succM M (succM M baseB) -> r=succM M (succM M baseR) ->
  coding_lt M (zeroM M) baseB -> coding_lt M t baseB ->
  coding_lt M a baseB -> coding_lt M q baseB ->
  coding_lt M (zeroM M) baseR -> coding_lt M b baseR ->
  coding_lt M t baseR -> coding_lt M z baseR ->
  expression_fresh M rho b
    (E_wim (E_marker_empty T Z) (E_wim (E_wel T A) Goal)) ->
  expression_fresh M rho r (E_wim (E_raw_envelope T A B Q)
    (E_wim (E_marker_empty T Z) (E_wim (E_wel T A) Goal))) ->
  ns_proof M rho (E_wim (E_marker_empty T Z) (E_wim (E_wel T A)
    (E_wim (E_raw_envelope T A B Q) (E_wim (E_raw_pair B T R Z) Goal)))) ->
  ns_proof M rho (E_wim (E_marker_empty T Z) (E_wim (E_wel T A) Goal)).
Proof.
  intros HT HA HB HR HZ HQ HFB HFR HTQ HAQ HQ0 HBZ HTZ HZ0 EB ER
    H0B HTB HAB HQB H0R HBR HTR HZR FreshB FreshR Construction.
  set (Final:=E_wim (E_marker_empty T Z) (E_wim (E_wel T A) Goal)).
  set (Env:=E_raw_envelope T A B Q).
  set (Pair:=E_raw_pair B T R Z).
  assert (ExistsB:ns_proof M rho (E_wex B Env)).
  { exact (numerical_fresh_envelope M rho T A B Q FB t a b q baseB
      HT HA HB HQ HFB HTQ HAQ HQ0 EB H0B HTB HAB HQB). }
  assert (ExistsR:ns_proof M rho (E_wex R Pair)).
  { exact (numerical_fresh_pair M rho B T R Z FR b t r z baseR
      HB HT HR HZ HFR HBZ HTZ HZ0 ER H0R HBR HTR HZR). }
  assert (Step:ns_proof M rho (E_wim Pair (E_wim Env Final))).
  { apply (ns_proof_macro M rho
      (E_wim (E_marker_empty T Z) (E_wim (E_wel T A)
        (E_wim Env (E_wim Pair Goal))) :: nil)).
    - intros e [<-|[]]. exact Construction.
    - apply macro_discharge. unfold Final. do 4 apply macro_deduction.
      eapply md_mp with (a:=Pair);[apply md_hyp;cbn;tauto|].
      eapply md_mp with (a:=Env);[apply md_hyp;cbn;tauto|].
      eapply md_mp with (a:=E_wel T A);[apply md_hyp;cbn;tauto|].
      eapply md_mp with (a:=E_marker_empty T Z);[apply md_hyp;cbn;tauto|].
      apply md_global,PM_input;now left. }
  assert (VacR:ns_proof M rho (E_vac R (E_wim Env Final))).
  { exact (kp0_expression_fresh_vacuity M rho R (E_wim Env Final) r HR FreshR). }
  assert (NoR:ns_proof M rho (E_wim Env Final)).
  { apply (ns_proof_macro M rho
      (E_vac R (E_wim Env Final) :: E_wim Pair (E_wim Env Final) :: E_wex R Pair :: nil)).
    - intros e [<-|[<-|[<-|[]]]];assumption.
    - eapply PM_mp;[apply PM_input;now right;right;left|].
      apply kp0_exists_eliminate;apply PM_input;cbn;tauto. }
  assert (VacB:ns_proof M rho (E_vac B Final)).
  { exact (kp0_expression_fresh_vacuity M rho B Final b HB FreshB). }
  apply (ns_proof_macro M rho (E_vac B Final :: E_wim Env Final :: E_wex B Env :: nil)).
  - intros e [<-|[<-|[<-|[]]]];assumption.
  - eapply PM_mp;[apply PM_input;now right;right;left|].
    apply kp0_exists_eliminate;apply PM_input;cbn;tauto.
Qed.

Print Assumptions numerical_collection_close_auxiliaries.
