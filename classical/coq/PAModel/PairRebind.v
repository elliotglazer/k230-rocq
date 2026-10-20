(** The profile binder of a raw pair may be renamed while preserving the
    same pair container. The two members need not be distinct. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  ProofMacros QuantifierMacros NumericalVacuitySteps NamedLeibnizSteps
  NamedBinderFresh TemplateBinderFresh TemplateNamedSubstitution StoppingInstantiation
  TemplateFormulaFresh NumericalKP0 NumericalKP0Eligibility NumericalRawPair
  NumericalTaggedComprehension RawMarkerQuantifiers QuotientAtomTemplates.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Lemma pair_profile_specialization M rho A B R Z W av bv rv zv wv :
  code_relation M rho A av -> code_relation M rho B bv -> code_relation M rho R rv ->
  code_relation M rho Z zv -> code_relation M rho W wv ->
  zv<>zeroM M -> zv<>wv -> av<>zv -> bv<>zv -> rv<>zv ->
  ns_proof M rho
    (E_wim (E_wal Z (E_wim (E_wel Z R) (E_or (E_weq Z A) (E_weq Z B))))
      (E_wim (E_wel W R) (E_or (E_weq W A) (E_weq W B)))).
Proof.
  intros HA HB HR HZ HW H0 HZW HAZ HBZ HRZ.
  set (F:=E_wim (E_wel Z R) (E_or (E_weq Z A) (E_weq Z B))).
  set (G:=E_wim (E_wel W R) (E_or (E_weq W A) (E_weq W B))).
  assert (RZ:expression_named_replace M rho rho zv wv Z W).
  { intros u v HU HV. rewrite (code_relation_functional M Z rho u zv HU HZ),
      (code_relation_functional M W rho v wv HV HW). now left. }
  assert (RA:expression_named_replace M rho rho zv wv A A).
  { intros u v HU HV. rewrite (code_relation_functional M A rho u av HU HA),
      (code_relation_functional M A rho v av HV HA). now right. }
  assert (RB:expression_named_replace M rho rho zv wv B B).
  { intros u v HU HV. rewrite (code_relation_functional M B rho u bv HU HB),
      (code_relation_functional M B rho v bv HV HB). now right. }
  assert (RR:expression_named_replace M rho rho zv wv R R).
  { intros u v HU HV. rewrite (code_relation_functional M R rho u rv HU HR),
      (code_relation_functional M R rho v rv HV HR). now right. }
  assert (HS:expression_named_substitution M rho rho zv wv F G).
  { unfold F,G. apply expression_ns_implication.
    - apply (expression_ns_atom M rho rho zv wv false);assumption.
    - apply expression_ns_disjunction;[exact H0| |];
        apply (expression_ns_atom M rho rho zv wv true);assumption. }
  assert (HF:expression_binder_absent M rho wv F).
  { unfold F. apply expression_binder_absent_implication.
    - apply expression_binder_absent_atom;now left.
    - apply expression_binder_absent_disjunction;apply expression_binder_absent_atom;now right. }
  destruct (code_relation_total M F rho) as [f Hf].
  destruct (code_relation_total M G rho) as [g Hg].
  exact (proj1 (ns_stopping_instantiation M rho Z W F G zv wv f g
    HZ HW Hf Hg HZW (HF f Hf) (HS f g Hf Hg))).
Qed.

Theorem numerical_pair_rebind M rho A B R Z W av bv rv zv wv :
  code_relation M rho A av -> code_relation M rho B bv -> code_relation M rho R rv ->
  code_relation M rho Z zv -> code_relation M rho W wv ->
  zv<>zeroM M -> wv<>zeroM M -> zv<>wv ->
  av<>zv -> bv<>zv -> rv<>zv -> av<>wv -> bv<>wv -> rv<>wv ->
  ns_proof M rho (E_wim (E_raw_pair A B R Z) (E_raw_pair A B R W)).
Proof.
  intros HA HB HR HZ HW HZ0 HW0 HZW HAZ HBZ HRZ HAW HBW HRW.
  set (AZ:=E_wal Z (E_wim (E_wel Z R) (E_or (E_weq Z A) (E_weq Z B)))).
  set (AW:=E_wal W (E_wim (E_wel W R) (E_or (E_weq W A) (E_weq W B)))).
  assert (HP:ns_proof M rho (E_wim AZ AW)).
  { apply marker_generalize_one.
    - apply (kp0_expression_fresh_vacuity M rho W AZ wv HW).
      unfold AZ. apply expression_fresh_universal.
      + exact (marker_name_avoids M rho Z zv wv HZ HZW).
      + apply expression_fresh_implication.
        * apply expression_fresh_atom;[now left| |];eapply marker_name_avoids;eassumption.
        * apply expression_fresh_disjunction;[exact HW0| |];
            apply expression_fresh_atom;[now right| | |now right| |];
            eapply marker_name_avoids;eassumption.
    - exact (pair_profile_specialization M rho A B R Z W av bv rv zv wv
        HA HB HR HZ HW HZ0 HZW HAZ HBZ HRZ). }
  apply (ns_proof_macro M rho (E_wim AZ AW :: nil)).
  - intros e [<-|[]]. exact HP.
  - change (proof_macro nil (E_wim AZ AW :: nil)
      (E_wim (E_wa (E_wa (E_wel A R) (E_wel B R)) AZ)
        (E_wa (E_wa (E_wel A R) (E_wel B R)) AW))).
    apply macro_discharge,macro_deduction,kp0_md_conjunction.
    + apply tagged_md_left with (b:=AZ),md_hyp;now left.
    + eapply md_mp with (a:=AZ).
      * apply tagged_md_right with (a:=E_wa (E_wel A R) (E_wel B R)),md_hyp;now left.
      * apply md_global,PM_input;now left.
Qed.

Theorem numerical_pair_exists_rebind M rho A B R Z W av bv rv zv wv :
  code_relation M rho A av -> code_relation M rho B bv -> code_relation M rho R rv ->
  code_relation M rho Z zv -> code_relation M rho W wv ->
  zv<>zeroM M -> wv<>zeroM M -> zv<>wv ->
  av<>zv -> bv<>zv -> rv<>zv -> av<>wv -> bv<>wv -> rv<>wv ->
  ns_proof M rho
    (E_wim (E_wex R (E_raw_pair A B R Z)) (E_wex R (E_raw_pair A B R W))).
Proof.
  intros HA HB HR HZ HW HZ0 HW0 HZW HAZ HBZ HRZ HAW HBW HRW.
  apply (ns_proof_macro M rho (E_wim (E_raw_pair A B R Z) (E_raw_pair A B R W) :: nil)).
  - intros e [<-|[]]. exact (numerical_pair_rebind M rho A B R Z W av bv rv zv wv
      HA HB HR HZ HW HZ0 HW0 HZW HAZ HBZ HRZ HAW HBW HRW).
  - apply macro_exists_monotone,PM_input;now left.
Qed.

Print Assumptions pair_profile_specialization.
Print Assumptions numerical_pair_rebind.
Print Assumptions numerical_pair_exists_rebind.
