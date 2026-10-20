(** Raw domain Separation with a prescribed result binder. The envelope,
    tagged container, pair seed and singleton requests are all constructed. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  ProofTemplates NamedLeibnizSteps NamedBinderFresh FreshNames NumericalVacuitySteps NumericalVacuity
  NumericalFreshEnvelope NumericalFreshSingleton TaggedSelectedAllocation
  NumericalRawEnvelope RawMarkerExclusions QuotedSameContainer
  RawSeparationFromEnvelope RawSeparationNormalizedEnvelope
  NumericalKP0 TemplatePropositional ProofMacros QuantifierMacros.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.

Definition raw_domain_roles M w a t z idx : carrier M :=
  match idx with 0=>w|1=>a|2=>t|_=>z end.
Definition raw_domain_environment M w a t z theta c idx : carrier M :=
  match idx with 0=>w|1=>a|3=>t|5=>z|6=>theta|7=>c|_=>zeroM M end.
Definition E_raw_domain_statement :=
  E_wim (E_marker_empty (CEvar 3) (CEvar 5))
    (E_wim (E_wel (CEvar 3) (CEvar 1)) E_normalized_envelope_result).

Theorem numerical_raw_domain_separation M w a t z theta c :
  (forall i j,i<4 -> j<4 -> i<>j -> raw_domain_roles M w a t z i<>raw_domain_roles M w a t z j) ->
  (forall i,i<4 -> raw_domain_roles M w a t z i<>zeroM M) ->
  named_binder_absent M theta t ->
  c<>zeroM M -> t<>c -> a<>c -> w<>c -> formula_fresh M theta c ->
  ns_proof M (raw_domain_environment M w a t z theta c) E_raw_domain_statement.
Proof.
  intros D N HT NC TC AC WC FC.
  pose proof (D 0 1 ltac:(lia) ltac:(lia) ltac:(lia)) as DWA.
  pose proof (D 0 2 ltac:(lia) ltac:(lia) ltac:(lia)) as DWT.
  pose proof (D 0 3 ltac:(lia) ltac:(lia) ltac:(lia)) as DWZ.
  pose proof (D 1 2 ltac:(lia) ltac:(lia) ltac:(lia)) as DAT.
  pose proof (D 1 3 ltac:(lia) ltac:(lia) ltac:(lia)) as DAZ.
  pose proof (D 2 3 ltac:(lia) ltac:(lia) ltac:(lia)) as DTZ.
  pose proof (N 0 ltac:(lia)) as NW. pose proof (N 1 ltac:(lia)) as NA.
  pose proof (N 2 ltac:(lia)) as NT. pose proof (N 3 ltac:(lia)) as NZ.
  set (initial:=raw_domain_environment M w a t z theta c).
  destruct (code_relation_total M E_raw_domain_statement initial) as [g HG].
  set (names:=[zeroM M;w;a;t;z;theta;c;g]).
  set (base:=finite_name_bound M names). set (b:=succM M (succM M base)).
  assert (Bound:forall v,In v names -> coding_lt M v base).
  { intros v Hv. apply finite_name_bound_above,Hv. }
  assert (HB:coding_lt M base b) by (eapply coding_lt_trans;apply coding_lt_succ).
  assert (LT:forall v,In v names -> coding_lt M v b).
  { intros v Hv. exact (coding_lt_trans M v base b (Bound v Hv) HB). }
  assert (BW:w<>b) by (apply fresh_singleton_lt_neq,LT;unfold names;cbn;tauto).
  assert (BA:a<>b) by (apply fresh_singleton_lt_neq,LT;unfold names;cbn;tauto).
  assert (BT:t<>b) by (apply fresh_singleton_lt_neq,LT;unfold names;cbn;tauto).
  assert (BZ:z<>b) by (apply fresh_singleton_lt_neq,LT;unfold names;cbn;tauto).
  assert (NB:b<>zeroM M) by (apply not_eq_sym,fresh_singleton_lt_neq,LT;unfold names;cbn;tauto).
  assert (DE:forall i j,i<5 -> j<5 -> i<>j ->
    envelope_separation_environment M w a b t z theta z i <>
    envelope_separation_environment M w a b t z theta z j).
  { intros i j Hi Hj Hij. destruct i as [|[|[|[|[|i]]]]];destruct j as [|[|[|[|[|j]]]]];
      cbn [envelope_separation_environment raw_domain_roles] in *;try lia;congruence. }
  assert (NE:forall i,i<4 -> envelope_separation_environment M w a b t z theta z i<>zeroM M).
  { intros i Hi. destruct i as [|[|[|[|i]]]];
      cbn [envelope_separation_environment raw_domain_roles] in *;try lia;congruence. }
  pose proof (numerical_raw_separation_normalized_envelope M w a b t z theta c DE NE NZ HT NC TC AC WC FC) as HP.
  set (rho:=fun idx=>match idx with 2=>b|8=>base|_=>raw_domain_environment M w a t z theta c idx end).
  change (ns_proof M rho (E_wim E_envelope_separation_parameter E_normalized_envelope_result)) in HP.
  set (Emp:=E_marker_empty (CEvar 3) (CEvar 5)).
  set (DA:=E_wel (CEvar 3) (CEvar 1)).
  set (Env:=E_raw_envelope (CEvar 3) (CEvar 1) (CEvar 2) (CEvar 0)).
  set (Out:=E_normalized_envelope_result).
  assert (HPoint:ns_proof M rho (E_wim Env E_raw_domain_statement)).
  { apply (ns_proof_macro M rho (E_wim E_envelope_separation_parameter Out :: nil)).
    - intros e [<-|[]]. exact HP.
    - apply macro_discharge. do 3 apply macro_deduction.
      eapply md_mp with (a:=E_envelope_separation_parameter).
      + unfold E_envelope_separation_parameter. apply kp0_md_conjunction.
        * apply md_hyp;now right;left.
        * apply kp0_md_conjunction;apply md_hyp;cbn;tauto.
      + apply md_global,PM_input;now left. }
  assert (HG':code_relation M rho E_raw_domain_statement g).
  { change (code_relation M initial E_raw_domain_statement g). exact HG. }
  assert (HV:ns_proof M rho (E_vac (CEvar 2) E_raw_domain_statement)).
  { intros v Hv. apply (numerical_vacuity M b g v).
    - apply formula_above_is_fresh,LT. unfold names;cbn;tauto.
    - exact (proj1 (expression_vacuity_graph M rho (CEvar 2) E_raw_domain_statement b g v eq_refl HG') Hv). }
  assert (HE:ns_proof M rho (E_wex (CEvar 2) Env)).
  { apply (numerical_fresh_envelope M rho (CEvar 3) (CEvar 1) (CEvar 2) (CEvar 0) (CEvar 8)
      t a b w base eq_refl eq_refl eq_refl eq_refl eq_refl
      (not_eq_sym DWT) (not_eq_sym DWA) NW eq_refl).
    - apply Bound;unfold names;cbn;tauto.
    - apply Bound;unfold names;cbn;tauto.
    - apply Bound;unfold names;cbn;tauto.
    - apply Bound;unfold names;cbn;tauto. }
  assert (P:ns_proof M rho E_raw_domain_statement).
  { apply (ns_proof_macro M rho (E_wim Env E_raw_domain_statement ::
      E_vac (CEvar 2) E_raw_domain_statement :: E_wex (CEvar 2) Env :: nil)).
    - intros e [<-|[<-|[<-|[]]]];assumption.
    - eapply PM_mp;[apply PM_input;now right;right;left|].
      apply kp0_exists_eliminate;apply PM_input;cbn;tauto. }
  change (ns_proof M (raw_domain_environment M w a t z theta c) E_raw_domain_statement) in P. exact P.
Qed.

Print Assumptions numerical_raw_domain_separation.
