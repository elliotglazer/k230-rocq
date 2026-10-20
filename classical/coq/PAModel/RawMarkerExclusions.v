(** Fixed marker exclusions for the raw tagged construction. All hypotheses
    are formulas of the numerical K calculus; model-valued names are kept
    arbitrary, with the binder exclusions stated explicitly. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs ProofTemplates TemplatePropositional ProofMacros QuantifierMacros
  EqualityMacros NumericalEquality NumericalVacuitySteps NamedLeibnizSteps QuotientAtomTemplates
  NamedBinderFresh TemplateBinderFresh NamedSubstitution TemplateNamedSubstitution StoppingInstantiation
  NumericalSingleton NumericalRawPair NumericalTaggedComprehension NumericalBootstrap.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_marker_empty t z := E_wal z (E_wn (E_wel z t)).

Lemma marker_empty_specialization M rho T Z X tv zv xv :
  code_relation M rho T tv -> code_relation M rho Z zv -> code_relation M rho X xv ->
  zv<>zeroM M -> zv<>xv -> tv<>zv ->
  ns_proof M rho (E_wim (E_marker_empty T Z) (E_wn (E_wel X T))).
Proof.
  intros HT HZ HX H0 HZX HTZ.
  set (A:=E_wn (E_wel Z T)). set (B:=E_wn (E_wel X T)).
  destruct (code_relation_total M A rho) as [a HA].
  destruct (code_relation_total M B rho) as [b HB].
  assert (HRZ:expression_named_replace M rho rho zv xv Z X).
  { intros u v HU HV. rewrite (code_relation_functional M Z rho u zv HU HZ),
      (code_relation_functional M X rho v xv HV HX). now left. }
  assert (HRT:expression_named_replace M rho rho zv xv T T).
  { intros u v HU HV. rewrite (code_relation_functional M T rho u tv HU HT),
      (code_relation_functional M T rho v tv HV HT). now right. }
  assert (HS:expression_named_substitution M rho rho zv xv A B).
  { unfold A,B. apply expression_ns_negation;[exact H0|].
    apply (expression_ns_atom M rho rho zv xv false);assumption. }
  assert (HAbs:named_binder_absent M a xv).
  { apply (expression_binder_absent_implication M rho xv (E_wel Z T) (CEconst 1)).
    - apply expression_binder_absent_atom;now left.
    - apply expression_binder_absent_one.
    - exact HA. }
  exact (proj1 (ns_stopping_instantiation M rho Z X A B zv xv a b
    HZ HX HA HB HZX HAbs (HS a b HA HB))).
Qed.

Lemma marker_membership_transport M rho X P R :
  ns_proof M rho (E_wim (E_weq P R) (E_wim (E_wel X P) (E_wel X R))).
Proof.
  eapply ns_proof_mp;[apply ns_proof_reflexivity|].
  exact (ns_proof_atom_transport M rho false X X P R).
Qed.

Lemma marker_equality_transitivity M rho X Y Z :
  ns_proof M rho (E_wim (E_weq X Y) (E_wim (E_weq Y Z) (E_weq X Z))).
Proof.
  apply (ns_proof_macro M rho (E_weq X X :: nil)).
  - intros e [<-|[]]. apply ns_proof_reflexivity.
  - apply macro_eq_trans,PM_input;now left.
Qed.

Theorem numerical_empty_not_singleton M rho T X Z tv xv zv :
  code_relation M rho T tv -> code_relation M rho X xv -> code_relation M rho Z zv ->
  zv<>zeroM M -> zv<>xv -> tv<>zv ->
  ns_proof M rho (E_wim (E_marker_empty T Z) (E_wn (E_raw_singleton X T Z))).
Proof.
  intros HT HX HZ H0 HZX HTZ.
  apply (ns_proof_macro M rho
    (E_wim (E_marker_empty T Z) (E_wn (E_wel X T)) :: nil)).
  - intros e [<-|[]]. exact (marker_empty_specialization M rho T Z X tv zv xv HT HZ HX H0 HZX HTZ).
  - apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=E_wel X T).
    + apply tagged_md_left with (b:=E_wal Z (E_wim (E_wel Z T) (E_weq Z X))).
      apply md_hyp;now left.
    + eapply md_mp with (a:=E_marker_empty T Z).
      * apply md_hyp;now right;left.
      * apply md_global,PM_input;now left.
Qed.

Theorem numerical_pair_not_empty M rho B T R Z bv tv zv :
  code_relation M rho B bv -> code_relation M rho T tv -> code_relation M rho Z zv ->
  zv<>zeroM M -> zv<>bv -> tv<>zv ->
  ns_proof M rho (E_wim (E_marker_empty T Z)
    (E_wim (E_raw_pair B T R Z) (E_wn (E_weq R T)))).
Proof.
  intros HB HT HZ H0 HZB HTZ.
  apply (ns_proof_macro M rho
    (E_wim (E_marker_empty T Z) (E_wn (E_wel B T)) ::
     E_wim (E_weq R T) (E_wim (E_wel B R) (E_wel B T)) :: nil)).
  - intros e [<-|[<-|[]]].
    + exact (marker_empty_specialization M rho T Z B tv zv bv HT HZ HB H0 HZB HTZ).
    + apply marker_membership_transport.
  - apply macro_discharge. do 3 apply macro_deduction.
    eapply md_mp with (a:=E_wel B T).
    + eapply md_mp with (a:=E_wel B R).
      * apply tagged_md_left with (b:=E_wel T R).
        apply tagged_md_left with
          (b:=E_wal Z (E_wim (E_wel Z R) (E_or (E_weq Z B) (E_weq Z T)))).
        apply md_hyp;now right;left.
      * eapply md_mp with (a:=E_weq R T).
        -- apply md_hyp;now left.
        -- apply md_global,PM_input;now right;left.
    + eapply md_mp with (a:=E_marker_empty T Z).
      * apply md_hyp;now right;right;left.
      * apply md_global,PM_input;now left.
Qed.

Theorem numerical_pair_not_singleton M rho B T R X Z bv tv rv xv zv :
  code_relation M rho B bv -> code_relation M rho T tv -> code_relation M rho R rv ->
  code_relation M rho X xv -> code_relation M rho Z zv ->
  zv<>bv -> zv<>tv -> rv<>zv -> xv<>zv ->
  ns_proof M rho (E_wim (E_wn (E_weq B T))
    (E_wim (E_raw_pair B T R Z) (E_wn (E_raw_singleton X R Z)))).
Proof.
  intros HB HT HR HX HZ HZB HZT HRZ HXZ.
  set (inputs:=
    E_wim (E_wel B R) (E_wim (E_raw_singleton X R Z) (E_weq X B)) ::
    E_wim (E_wel T R) (E_wim (E_raw_singleton X R Z) (E_weq X T)) ::
    E_wim (E_weq X B) (E_weq B X) ::
    E_wim (E_weq B X) (E_wim (E_weq X T) (E_weq B T)) :: nil).
  set (delta:= E_raw_singleton X R Z :: E_raw_pair B T R Z :: E_wn (E_weq B T) :: nil).
  apply (ns_proof_macro M rho inputs).
  - intros e [<-|[<-|[<-|[<-|[]]]]].
    + exact (numerical_singleton_uniqueness M rho B X R Z bv xv rv zv HB HX HR HZ HZB HRZ HXZ).
    + exact (numerical_singleton_uniqueness M rho T X R Z tv xv rv zv HT HX HR HZ HZT HRZ HXZ).
    + apply ns_proof_symmetry.
    + apply marker_equality_transitivity.
  - apply macro_discharge. do 3 apply macro_deduction.
    assert (HP:macro_derivation nil inputs delta (E_wa (E_wel B R) (E_wel T R))).
    { apply tagged_md_left with
        (b:=E_wal Z (E_wim (E_wel Z R) (E_or (E_weq Z B) (E_weq Z T)))).
      apply md_hyp;now right;left. }
    assert (HXB:macro_derivation nil inputs delta (E_weq X B)).
    { eapply md_mp with (a:=E_raw_singleton X R Z);[apply md_hyp;now left|].
      eapply md_mp with (a:=E_wel B R);[now apply tagged_md_left with (b:=E_wel T R)|].
      apply md_global,PM_input;now left. }
    assert (HXT:macro_derivation nil inputs delta (E_weq X T)).
    { eapply md_mp with (a:=E_raw_singleton X R Z);[apply md_hyp;now left|].
      eapply md_mp with (a:=E_wel T R);[now apply tagged_md_right with (a:=E_wel B R)|].
      apply md_global,PM_input;now right;left. }
    eapply md_mp with (a:=E_weq B T).
    + eapply md_mp with (a:=E_weq X T);[exact HXT|].
      eapply md_mp with (a:=E_weq B X).
      * eapply md_mp with (a:=E_weq X B);[exact HXB|].
        apply md_global,PM_input;now right;right;left.
      * apply md_global,PM_input;now right;right;right;left.
    + apply md_hyp;now right;right;left.
Qed.

Print Assumptions numerical_empty_not_singleton.
Print Assumptions numerical_pair_not_empty.
Print Assumptions numerical_pair_not_singleton.
