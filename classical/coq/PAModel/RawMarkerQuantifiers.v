(** Quantified marker exclusions with explicit name freshness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  ProofTemplates TemplatePropositional ProofMacros QuantifierMacros
  NumericalVacuitySteps NamedLeibnizSteps TemplateFormulaFresh FreshNames
  NumericalKP0Eligibility NumericalSingleton NumericalRawPair QuotientAtomTemplates
  RawMarkerExclusions.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Lemma marker_name_avoids M rho X x y :
  code_relation M rho X x -> x<>y -> expression_name_avoids M rho y X.
Proof. intros HX Hxy v Hv. now rewrite (code_relation_functional M X rho v x Hv HX). Qed.

Lemma marker_generalize_one M rho Y A B :
  ns_proof M rho (E_vac Y A) -> ns_proof M rho (E_wim A B) ->
  ns_proof M rho (E_wim A (E_wal Y B)).
Proof.
  intros HV HP. apply (ns_proof_macro M rho (E_vac Y A :: E_wim A B :: nil)).
  - intros e [<-|[<-|[]]];assumption.
  - eapply macro_syl;[apply PM_input;now left|].
    apply macro_all_monotone,PM_input;now right;left.
Qed.

Lemma marker_generalize_two M rho Y A B C :
  ns_proof M rho (E_vac Y A) -> ns_proof M rho (E_vac Y B) ->
  ns_proof M rho (E_wim A (E_wim B C)) ->
  ns_proof M rho (E_wim A (E_wim B (E_wal Y C))).
Proof.
  intros VA VB HP.
  assert (HS:ns_proof M rho (E_wim A (E_wim (E_wal Y B) (E_wal Y C)))).
  { apply (ns_proof_macro M rho (E_wim A (E_wim B C) :: E_vac Y A :: nil)).
    - intros e [<-|[<-|[]]];assumption.
    - apply ns_macro_all. }
  apply (ns_proof_macro M rho (E_vac Y B :: E_wim A (E_wim (E_wal Y B) (E_wal Y C)) :: nil)).
  - intros e [<-|[<-|[]]];assumption.
  - apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=E_wal Y B).
    + eapply md_mp with (a:=B);[apply md_hyp;now left|]. apply md_global,PM_input;now left.
    + eapply md_mp with (a:=A);[apply md_hyp;now right;left|].
      apply md_global,PM_input;now right;left.
Qed.

Lemma marker_empty_fresh M rho T Z tv zv x :
  code_relation M rho T tv -> code_relation M rho Z zv ->
  x<>zeroM M -> tv<>x -> zv<>x -> expression_fresh M rho x (E_marker_empty T Z).
Proof.
  intros HT HZ H0 HTX HZX. unfold E_marker_empty.
  apply expression_fresh_universal.
  - exact (marker_name_avoids M rho Z zv x HZ HZX).
  - apply expression_fresh_negation;[exact H0|].
    apply expression_fresh_atom;[now left| |];eapply marker_name_avoids;eassumption.
Qed.

Lemma marker_pair_fresh M rho B T R Z bv tv rv zv x :
  code_relation M rho B bv -> code_relation M rho T tv ->
  code_relation M rho R rv -> code_relation M rho Z zv ->
  x<>zeroM M -> bv<>x -> tv<>x -> rv<>x -> zv<>x ->
  expression_fresh M rho x (E_raw_pair B T R Z).
Proof.
  intros HB HT HR HZ H0 HBX HTX HRX HZX. unfold E_raw_pair.
  apply expression_fresh_conjunction;[exact H0| |].
  - apply expression_fresh_conjunction;[exact H0| |];
      apply expression_fresh_atom;[now left| | |now left| |];eapply marker_name_avoids;eassumption.
  - apply expression_fresh_universal;[eapply marker_name_avoids;eassumption|].
    apply expression_fresh_implication.
    + apply expression_fresh_atom;[now left| |];eapply marker_name_avoids;eassumption.
    + apply expression_fresh_disjunction;[exact H0| |];
        apply expression_fresh_atom;[now right| | |now right| |];eapply marker_name_avoids;eassumption.
Qed.

Theorem numerical_empty_no_singletons M rho T X Z tv xv zv :
  code_relation M rho T tv -> code_relation M rho X xv -> code_relation M rho Z zv ->
  zv<>zeroM M -> xv<>zeroM M -> zv<>xv -> tv<>zv -> tv<>xv ->
  ns_proof M rho (E_wim (E_marker_empty T Z) (E_wal X (E_wn (E_raw_singleton X T Z)))).
Proof.
  intros HT HX HZ HZ0 HX0 HZX HTZ HTX. apply marker_generalize_one.
  - apply (kp0_expression_fresh_vacuity M rho X (E_marker_empty T Z) xv HX).
    exact (marker_empty_fresh M rho T Z tv zv xv HT HZ HX0 HTX HZX).
  - exact (numerical_empty_not_singleton M rho T X Z tv xv zv HT HX HZ HZ0 HZX HTZ).
Qed.

Theorem numerical_pair_no_singletons M rho B T R X Z bv tv rv xv zv :
  code_relation M rho B bv -> code_relation M rho T tv -> code_relation M rho R rv ->
  code_relation M rho X xv -> code_relation M rho Z zv ->
  xv<>zeroM M -> zv<>bv -> zv<>tv -> rv<>zv -> xv<>zv ->
  bv<>xv -> tv<>xv -> rv<>xv ->
  ns_proof M rho (E_wim (E_wn (E_weq B T))
    (E_wim (E_raw_pair B T R Z) (E_wal X (E_wn (E_raw_singleton X R Z))))).
Proof.
  intros HB HT HR HX HZ HX0 HZB HZT HRZ HXZ HBX HTX HRX. apply marker_generalize_two.
  - apply (kp0_expression_fresh_vacuity M rho X (E_wn (E_weq B T)) xv HX).
    apply expression_fresh_negation;[exact HX0|].
    apply expression_fresh_atom;[now right| |];eapply marker_name_avoids;eassumption.
  - apply (kp0_expression_fresh_vacuity M rho X (E_raw_pair B T R Z) xv HX).
    apply (marker_pair_fresh M rho B T R Z bv tv rv zv xv HB HT HR HZ HX0 HBX HTX HRX).
    congruence.
  - exact (numerical_pair_not_singleton M rho B T R X Z bv tv rv xv zv HB HT HR HX HZ HZB HZT HRZ HXZ).
Qed.

Theorem numerical_pair_not_empty_reverse M rho B T R Z bv tv zv :
  code_relation M rho B bv -> code_relation M rho T tv -> code_relation M rho Z zv ->
  zv<>zeroM M -> zv<>bv -> tv<>zv ->
  ns_proof M rho (E_wim (E_marker_empty T Z)
    (E_wim (E_raw_pair B T R Z) (E_wn (E_weq T R)))).
Proof.
  intros HB HT HZ H0 HZB HTZ.
  apply (ns_proof_macro M rho
    (E_wim (E_marker_empty T Z) (E_wim (E_raw_pair B T R Z) (E_wn (E_weq R T))) ::
     E_wim (E_weq T R) (E_weq R T) :: nil)).
  - intros e [<-|[<-|[]]].
    + exact (numerical_pair_not_empty M rho B T R Z bv tv zv HB HT HZ H0 HZB HTZ).
    + apply ns_proof_symmetry.
  - apply macro_discharge. do 3 apply macro_deduction.
    eapply md_mp with (a:=E_weq R T).
    + eapply md_mp with (a:=E_weq T R);[apply md_hyp;now left|]. apply md_global,PM_input;now right;left.
    + eapply md_mp with (a:=E_raw_pair B T R Z);[apply md_hyp;now right;left|].
      eapply md_mp with (a:=E_marker_empty T Z);[apply md_hyp;now right;right;left|].
      apply md_global,PM_input;now left.
Qed.

Print Assumptions numerical_empty_no_singletons.
Print Assumptions numerical_pair_no_singletons.
Print Assumptions numerical_pair_not_empty_reverse.
