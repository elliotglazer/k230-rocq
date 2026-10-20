(** Raw Separation after fixing one domain envelope. The selected
    predicate and generated tagged container are actual numerical codes. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps FreshNames NamedBinderFresh TemplateBinderFresh TemplateFormulaFresh
  NumericalVacuitySteps NumericalKP0Eligibility NumericalKP0 NumericalBootstrap
  NumericalRawEnvelope NumericalEnvelopeFacts EnvelopeSpecializations
  NumericalRawTagged NumericalRawTaggedFresh NumericalFreshEnvelope
  NumericalTaggedComprehension RawMarkerExclusions RawMarkerQuantifiers
  RawSeparationPoint RawSeparationAll RawSeparationContainer
  QuotedSameContainer LiteralMemberSeparationPoint SeparationPredicate
  NumericalFreshSingleton TemplatePropositional ProofMacros QuantifierMacros.
From Stdlib Require Import Lists.List Lia.
Unset Implicit Arguments.

Definition envelope_separation_environment M w a b t z theta k idx : carrier M :=
  match idx with 0=>w|1=>a|2=>b|3=>t|4=>k|5=>z|6=>theta|_=>zeroM M end.
Definition E_envelope_separation_parameter :=
  E_wa (E_marker_empty (CEvar 3) (CEvar 5))
    (E_wa (E_wel (CEvar 3) (CEvar 1))
      (E_raw_envelope (CEvar 3) (CEvar 1) (CEvar 2) (CEvar 0))).
Definition E_envelope_separation_body :=
  E_raw_selection_container (CEvar 3) (CEvar 1) (CEvar 4) (CEvar 0) (CEvar 6).

Theorem numerical_raw_separation_from_envelope M w a b t z theta :
  (forall i j,i<5 -> j<5 -> i<>j ->
    envelope_separation_environment M w a b t z theta z i <>
    envelope_separation_environment M w a b t z theta z j) ->
  (forall i,i<4 -> envelope_separation_environment M w a b t z theta z i<>zeroM M) ->
  z<>zeroM M -> named_binder_absent M theta t ->
  exists k f,k<>zeroM M /\ k<>w /\ k<>a /\ k<>b /\ k<>t /\ k<>z /\
    formula_fresh M theta k /\
    code_relation M (envelope_separation_environment M w a b t z theta k)
      (E_wim E_envelope_separation_parameter (E_wex (CEvar 4) E_envelope_separation_body)) f /\
    numerically_provable M f.
Proof.
  intros D N NZ Htheta.
  (* Role 4 in the assumption environment is z, matching the fixed empty binder. *)
  pose proof (D 0 1 ltac:(lia) ltac:(lia) ltac:(lia)) as DWA.
  pose proof (D 0 2 ltac:(lia) ltac:(lia) ltac:(lia)) as DWB.
  pose proof (D 0 3 ltac:(lia) ltac:(lia) ltac:(lia)) as DWT.
  pose proof (D 0 4 ltac:(lia) ltac:(lia) ltac:(lia)) as DWZ.
  pose proof (D 1 2 ltac:(lia) ltac:(lia) ltac:(lia)) as DAB.
  pose proof (D 1 3 ltac:(lia) ltac:(lia) ltac:(lia)) as DAT.
  pose proof (D 1 4 ltac:(lia) ltac:(lia) ltac:(lia)) as DAZ.
  pose proof (D 2 3 ltac:(lia) ltac:(lia) ltac:(lia)) as DBT.
  pose proof (D 2 4 ltac:(lia) ltac:(lia) ltac:(lia)) as DBZ.
  pose proof (D 3 4 ltac:(lia) ltac:(lia) ltac:(lia)) as DTZ.
  pose proof (N 0 ltac:(lia)) as NW. pose proof (N 1 ltac:(lia)) as NA.
  pose proof (N 2 ltac:(lia)) as NB. pose proof (N 3 ltac:(lia)) as NT.
  set (initial:=envelope_separation_environment M w a b t z theta (zeroM M)).
  set (Cut:=E_separation_predicate (CEvar 0) (CEvar 1) (CEvar 6)).
  destruct (code_relation_total M Cut initial) as [cut HCut].
  assert (CutAbs:named_binder_absent M cut t).
  { apply (separation_predicate_binder_absent M initial t (CEvar 0) (CEvar 1) (CEvar 6)).
    - intros f Hf. change (f=theta) in Hf. now subst f.
    - exact HCut. }
  assert (TD:forall i j,i<4 -> j<4 -> i<>j -> raw_tagged_roles M w b t z i<>raw_tagged_roles M w b t z j).
  { intros i j Hi Hj Hij. destruct i as [|[|[|[|i]]]];destruct j as [|[|[|[|j]]]];
      cbn [raw_tagged_roles envelope_separation_environment] in *;try lia;congruence. }
  assert (TN:forall i,i<4 -> raw_tagged_roles M w b t z i<>zeroM M).
  { intros i Hi. destruct i as [|[|[|[|i]]]];cbn [raw_tagged_roles envelope_separation_environment] in *;try lia;congruence. }
  destruct (numerical_raw_tagged_comprehension_fresh M w b t cut z TD TN CutAbs)
    as (k & f & NK & KW & KB & KT & KZ & FreshCut & HF & PF).
  set (rho:=envelope_separation_environment M w a b t z theta k).
  assert (HCut':code_relation M rho Cut cut).
  { change (code_relation M initial Cut cut). exact HCut. }
  assert (FExpr:expression_fresh M rho k Cut).
  { intros f0 Hf0. assert (f0=cut) by (eapply code_relation_functional;eassumption). now subst f0. }
  destruct (separation_predicate_fresh_parts M rho k (CEvar 0) (CEvar 1) (CEvar 6) FExpr)
    as (FW & FA & FTheta).
  specialize (FA a eq_refl).
  specialize (FTheta theta eq_refl).
  set (Tag:=E_wal (CEvar 0) (E_raw_separation_tagged_point
    (CEvar 3) (CEvar 1) (CEvar 2) (CEvar 4) (CEvar 0) (CEvar 6))).
  set (Emp:=E_marker_empty (CEvar 3) (CEvar 5)).
  set (Neq:=E_wn (E_weq (CEvar 2) (CEvar 3))).
  set (DA:=E_wel (CEvar 3) (CEvar 1)).
  set (Env:=E_raw_envelope (CEvar 3) (CEvar 1) (CEvar 2) (CEvar 0)).
  set (Raw:=E_raw_selection_container (CEvar 3) (CEvar 1) (CEvar 4) (CEvar 0) (CEvar 6)).
  assert (HRawTag:ns_proof M (raw_tagged_parameters M w b t cut z k) E_raw_tagged_statement).
  { intros g Hg. assert (g=f) by (eapply code_relation_functional;eassumption). now subst g. }
  set (s:=fun i=>match i with 0=>CEvar 0|3=>CEvar 2|4=>CEvar 3|6=>CEvar 4|7=>CEvar 5|8=>Cut|_=>CEconst 0 end).
  assert (HGraphs:forall i,code_relation M rho (s i) (raw_tagged_parameters M w b t cut z k i)).
  { intros i. destruct i as [|[|[|[|[|[|[|[|[|i]]]]]]]]];try reflexivity. exact HCut'. }
  assert (HTag:ns_proof M rho (E_wim Emp (E_wim Neq (E_wex (CEvar 4) Tag)))).
  { change (ns_proof M rho (code_subst s E_raw_tagged_statement)).
    intros g Hg. apply HRawTag.
    apply (proj1 (code_subst_graph M rho s (raw_tagged_parameters M w b t cut z k) HGraphs E_raw_tagged_statement g) Hg).
  }
  assert (HBody:ns_proof M rho (E_wim E_envelope_separation_parameter (E_wim Tag Raw))).
  { apply (ns_proof_macro M rho
      (E_wim Emp (E_wim DA (E_wim Env (E_wim Tag Raw))) :: nil)).
    - intros e [<-|[]]. exact (numerical_raw_separation_container M rho
        (CEvar 3) (CEvar 1) (CEvar 2) (CEvar 4) (CEvar 0) (CEvar 5) (CEvar 6)
        t a b k w z eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl NW NZ
        (not_eq_sym DWT) (not_eq_sym DWA) (not_eq_sym DWB) KW DTZ DAZ (not_eq_sym DWZ)).
    - apply macro_discharge. do 2 apply macro_deduction.
      eapply md_mp with (a:=Tag);[apply md_hyp;now left|].
      eapply md_mp with (a:=Env).
      + apply tagged_md_right with (a:=DA),tagged_md_right with (a:=Emp),md_hyp;now right;left.
      + eapply md_mp with (a:=DA).
        * apply tagged_md_left with (b:=Env),tagged_md_right with (a:=Emp),md_hyp;now right;left.
        * eapply md_mp with (a:=Emp).
          -- apply tagged_md_left with (b:=E_wa DA Env),md_hyp;now right;left.
          -- apply md_global,PM_input;now left. }
  assert (HParamV:ns_proof M rho (E_vac (CEvar 4) E_envelope_separation_parameter)).
  { apply (kp0_expression_fresh_vacuity M rho (CEvar 4) E_envelope_separation_parameter k eq_refl).
    unfold E_envelope_separation_parameter. apply expression_fresh_conjunction;[exact NK| |].
    - exact (marker_empty_fresh M rho (CEvar 3) (CEvar 5) t z k eq_refl eq_refl NK (not_eq_sym KT) (not_eq_sym KZ)).
    - apply expression_fresh_conjunction;[exact NK| |].
      + apply expression_fresh_atom;[now left| |].
        * exact (marker_name_avoids M rho (CEvar 3) t k eq_refl (not_eq_sym KT)).
        * exact (marker_name_avoids M rho (CEvar 1) a k eq_refl FA).
      + apply expression_fresh_universal.
        * exact (marker_name_avoids M rho (CEvar 0) w k eq_refl (not_eq_sym KW)).
        * exact (envelope_point_fresh M rho (CEvar 3) (CEvar 1) (CEvar 2) (CEvar 0)
            t a b w k eq_refl eq_refl eq_refl eq_refl NK (not_eq_sym KT) FA (not_eq_sym KB) (not_eq_sym KW)). }
  assert (HNeq:ns_proof M rho (E_wim E_envelope_separation_parameter Neq)).
  { apply (ns_proof_macro M rho ((E_wim Emp (E_wim DA (E_wim Env (E_envelope_facts (CEvar 3) (CEvar 1) (CEvar 2) (CEvar 0)))))::nil)).
    - intros e [<-|[]]. exact (numerical_raw_envelope_facts M rho (CEvar 3) (CEvar 1) (CEvar 2) (CEvar 0) (CEvar 5)
        t a b w z eq_refl eq_refl eq_refl eq_refl eq_refl NW (not_eq_sym DWT) (not_eq_sym DWA) (not_eq_sym DWB) NZ DTZ DAZ).
    - apply macro_discharge,macro_deduction.
      apply tagged_md_right with (a:=E_wn (E_wel (CEvar 3) (CEvar 2))),
        tagged_md_right with (a:=E_wa (E_wel (CEvar 1) (CEvar 2)) (E_envelope_domain_all (CEvar 3) (CEvar 2) (CEvar 0))).
      eapply md_mp with (a:=Env).
      + apply tagged_md_right with (a:=DA),tagged_md_right with (a:=Emp),md_hyp;now left.
      + eapply md_mp with (a:=DA).
        * apply tagged_md_left with (b:=Env),tagged_md_right with (a:=Emp),md_hyp;now left.
        * eapply md_mp with (a:=Emp).
          -- apply tagged_md_left with (b:=E_wa DA Env),md_hyp;now left.
          -- apply md_global,PM_input;now left. }
  set (liftingInputs:=E_vac (CEvar 4) E_envelope_separation_parameter ::
       E_wim E_envelope_separation_parameter (E_wim Tag Raw) ::
       E_wim Emp (E_wim Neq (E_wex (CEvar 4) Tag)) ::
       E_wim E_envelope_separation_parameter Neq :: nil).
  assert (P:ns_proof M rho (E_wim E_envelope_separation_parameter (E_wex (CEvar 4) Raw))).
  { apply (ns_proof_macro M rho liftingInputs).
    - intros e [<-|[<-|[<-|[<-|[]]]]];assumption.
    - assert (HL:proof_macro nil liftingInputs (E_wim E_envelope_separation_parameter
        (E_wim (E_wex (CEvar 4) Tag) (E_wex (CEvar 4) Raw)))).
      { apply kp0_parameter_exists;apply PM_input;cbn;tauto. }
      apply macro_discharge,macro_deduction.
      eapply md_mp with (a:=E_wex (CEvar 4) Tag).
      + eapply md_mp with (a:=Neq).
        * eapply md_mp;[apply md_hyp;now left|]. apply md_global,PM_input;now right;right;right;left.
        * eapply md_mp with (a:=Emp).
          -- apply tagged_md_left with (b:=E_wa DA Env),md_hyp;now left.
          -- apply md_global,PM_input;now right;right;left.
      + eapply md_mp;[apply md_hyp;now left|apply md_global,HL]. }
  destruct (code_relation_total M (E_wim E_envelope_separation_parameter (E_wex (CEvar 4) Raw)) rho) as [result HResult].
  exists k,result. repeat split;try assumption. exact (not_eq_sym FA). exact (P result HResult).
Qed.

Print Assumptions numerical_raw_separation_from_envelope.
