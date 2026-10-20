(** The support direction of the arbitrary-predicate tagged construction.
    Theta is an arbitrary internal formula code. The singleton predicate is
    kept as an explicit formula slot, so this step needs no singleton axiom. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs ProofTemplates TemplatePropositional ProofMacros QuantifierMacros
  NumericalVacuitySteps NamedLeibnizSteps NamedExistential TemplateFormulaFresh
  QuotientAtomTemplates ContextualPropositional NumericalBootstrap
  NumericalKP0 NumericalKP0Requests NumericalKP0Eligibility
  StoppingSpecialization NumericalEquality NamedAlpha BoundVariableVacuityRules
  TemplateNamedSubstitution TemplateBinderFresh NamedBinderFresh StoppingInstantiation.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_tagged_choices y p carrier marker root theta singleton :=
  E_or (E_wa (E_weq p root) (E_weq y carrier))
    (E_or (E_wa (E_weq p marker) (E_weq y marker))
      (E_wa singleton (E_wa (E_wel y carrier) theta))).

Definition E_tagged_profile y carrier marker theta :=
  E_or (E_weq y carrier) (E_or (E_weq y marker) (E_wa (E_wel y carrier) theta)).

Lemma tagged_or_cases G inputs a b c :
  proof_macro G inputs (E_wim a c) -> proof_macro G inputs (E_wim b c) ->
  proof_macro G inputs (E_wim (E_or a b) c).
Proof.
  intros HA HB. eapply PM_mp;[exact HB|]. eapply PM_mp;[exact HA|].
  apply PM_template,template_or_elimination.
Qed.

Lemma tagged_choices_projection G inputs y p carrier marker root theta singleton :
  proof_macro G inputs
    (E_wim (E_tagged_choices y p carrier marker root theta singleton)
      (E_tagged_profile y carrier marker theta)).
Proof.
  unfold E_tagged_choices,E_tagged_profile. apply tagged_or_cases.
  - eapply macro_syl;[apply PM_template,bootstrap_projection_right|].
    apply PM_template,template_or_left.
  - apply tagged_or_cases.
    + eapply macro_syl;[apply PM_template,bootstrap_projection_right|].
      eapply macro_syl;[apply PM_template,template_or_left|].
      apply PM_template,template_or_right.
    + eapply macro_syl;[apply PM_template,bootstrap_projection_right|].
      eapply macro_syl;apply PM_template,template_or_right.
Qed.

Definition E_tagged_support y p carrier marker root container theta singleton :=
  E_wal y (E_wim (E_wel y container)
    (E_wex p (E_tagged_choices y p carrier marker root theta singleton))).

Definition E_tagged_containment y carrier marker container theta :=
  E_wal y (E_wim (E_wel y container) (E_tagged_profile y carrier marker theta)).

Lemma tagged_support_projection_program y p carrier marker root container theta singleton :
  proof_macro nil (E_vac p (E_tagged_profile y carrier marker theta) :: nil)
    (E_wim (E_tagged_support y p carrier marker root container theta singleton)
      (E_tagged_containment y carrier marker container theta)).
Proof.
  unfold E_tagged_support,E_tagged_containment.
  apply macro_all_monotone,kp0_implication_map,kp0_exists_eliminate.
  - apply PM_input;now left.
  - apply tagged_choices_projection.
Qed.

Lemma tagged_profile_fresh M rho name y carrier marker theta :
  name<>zeroM M -> expression_name_avoids M rho name y ->
  expression_name_avoids M rho name carrier -> expression_name_avoids M rho name marker ->
  expression_fresh M rho name theta ->
  expression_fresh M rho name (E_tagged_profile y carrier marker theta).
Proof.
  intros HN HY HC HT HTheta. unfold E_tagged_profile.
  apply expression_fresh_disjunction;[exact HN| |].
  - apply expression_fresh_atom;[now right|exact HY|exact HC].
  - apply expression_fresh_disjunction;[exact HN| |].
    + apply expression_fresh_atom;[now right|exact HY|exact HT].
    + apply expression_fresh_conjunction;[exact HN| |exact HTheta].
      apply expression_fresh_atom;[now left|exact HY|exact HC].
Qed.

Theorem numerical_tagged_support_projection M rho y p carrier marker root container theta singleton pv :
  code_relation M rho p pv -> pv<>zeroM M ->
  expression_name_avoids M rho pv y -> expression_name_avoids M rho pv carrier ->
  expression_name_avoids M rho pv marker -> expression_fresh M rho pv theta ->
  ns_proof M rho
    (E_wim (E_tagged_support y p carrier marker root container theta singleton)
      (E_tagged_containment y carrier marker container theta)).
Proof.
  intros HP HN HY HC HT HTheta.
  apply (ns_proof_macro M rho (E_vac p (E_tagged_profile y carrier marker theta) :: nil)).
  - intros e [<-|[]]. apply (kp0_expression_fresh_vacuity M rho p
      (E_tagged_profile y carrier marker theta) pv HP).
    apply tagged_profile_fresh;assumption.
  - apply tagged_support_projection_program.
Qed.

Lemma tagged_md_left G inputs delta a b :
  macro_derivation G inputs delta (E_wa a b) -> macro_derivation G inputs delta a.
Proof.
  intro H. eapply md_mp;[exact H|]. apply md_global,PM_template,bootstrap_projection_left.
Qed.
Lemma tagged_md_right G inputs delta a b :
  macro_derivation G inputs delta (E_wa a b) -> macro_derivation G inputs delta b.
Proof.
  intro H. eapply md_mp;[exact H|]. apply md_global,PM_template,bootstrap_projection_right.
Qed.
Lemma tagged_md_cases G inputs delta a b c :
  macro_derivation G inputs delta (E_or a b) ->
  macro_derivation G inputs delta (E_wim a c) ->
  macro_derivation G inputs delta (E_wim b c) ->
  macro_derivation G inputs delta c.
Proof.
  intros HAB HA HB. eapply md_mp;[exact HAB|]. eapply md_mp;[exact HB|].
  eapply md_mp;[exact HA|]. apply md_global,PM_template,template_or_elimination.
Qed.

Definition E_tagged_witness_hyp y x p marker root singleton :=
  E_wa (E_wn (E_weq p root))
    (E_wa (E_wn (E_weq p marker)) (E_wal y (E_wim singleton (E_weq y x)))).

Definition tagged_witness_inputs (y x p marker root container singleton : code_expr) :=
  E_wim (E_wal y (E_wim singleton (E_weq y x))) (E_wim singleton (E_weq y x)) ::
  E_wim (E_weq y x) (E_wim (E_wel y container) (E_wel x container)) :: nil.

Lemma tagged_witness_point_program y x p carrier marker root container theta singleton :
  proof_macro nil (tagged_witness_inputs y x p marker root container singleton)
    (E_wim (E_tagged_witness_hyp y x p marker root singleton)
      (E_wim (E_wa (E_wel y container)
        (E_tagged_choices y p carrier marker root theta singleton)) (E_wel x container))).
Proof.
  set (inputs:=tagged_witness_inputs y x p marker root container singleton).
  set (H:=E_tagged_witness_hyp y x p marker root singleton).
  set (F:=E_wa (E_wel y container) (E_tagged_choices y p carrier marker root theta singleton)).
  apply macro_discharge. do 2 apply macro_deduction.
  apply (tagged_md_cases _ _ _
    (E_wa (E_weq p root) (E_weq y carrier))
    (E_or (E_wa (E_weq p marker) (E_weq y marker))
      (E_wa singleton (E_wa (E_wel y carrier) theta)))).
  - apply tagged_md_right with (a:=E_wel y container),md_hyp;now left.
  - apply macro_deduction. eapply md_mp with (a:=CEconst 1).
    + eapply md_mp with (a:=E_weq p root).
      * apply tagged_md_left with (b:=E_weq y carrier),md_hyp;now left.
      * unfold H,E_tagged_witness_hyp.
        apply tagged_md_left with (b:=E_wa (E_wn (E_weq p marker))
          (E_wal y (E_wim singleton (E_weq y x)))),md_hyp;cbn;tauto.
    + apply md_global,PM_template,template_F.
  - apply macro_deduction. apply (tagged_md_cases _ _ _
      (E_wa (E_weq p marker) (E_weq y marker))
      (E_wa singleton (E_wa (E_wel y carrier) theta))).
    + apply md_hyp;now left.
    + apply macro_deduction. eapply md_mp with (a:=CEconst 1).
      * eapply md_mp with (a:=E_weq p marker).
        -- apply tagged_md_left with (b:=E_weq y marker),md_hyp;now left.
        -- unfold H,E_tagged_witness_hyp.
           apply tagged_md_left with (b:=E_wal y (E_wim singleton (E_weq y x))).
           apply tagged_md_right with (a:=E_wn (E_weq p root)),md_hyp;cbn;tauto.
      * apply md_global,PM_template,template_F.
    + apply macro_deduction. eapply md_mp with (a:=E_wel y container).
      * apply tagged_md_left with (b:=E_tagged_choices y p carrier marker root theta singleton),md_hyp;cbn;tauto.
      * eapply md_mp with (a:=E_weq y x).
        -- eapply md_mp with (a:=singleton).
           ++ apply tagged_md_left with (b:=E_wa (E_wel y carrier) theta),md_hyp;now left.
           ++ eapply md_mp with (a:=E_wal y (E_wim singleton (E_weq y x))).
              ** unfold H,E_tagged_witness_hyp.
                 apply tagged_md_right with (a:=E_wn (E_weq p marker)).
                 apply tagged_md_right with (a:=E_wn (E_weq p root)),md_hyp;cbn;tauto.
              ** apply md_global,PM_input;unfold inputs,tagged_witness_inputs;now left.
        -- apply md_global,PM_input;unfold inputs,tagged_witness_inputs;now right;left.
Qed.

Lemma tagged_macro_inputs G A B e :
  (forall f,In f A -> In f B) -> proof_macro G A e -> proof_macro G B e.
Proof.
  intros HI HD. induction HD.
  - now apply PM_template.
  - apply PM_input,HI;assumption.
  - exact (PM_mp _ _ IHHD1 IHHD2).
  - exact (PM_gen _ _ IHHD).
Qed.

Lemma tagged_witness_cleanup_program y x p carrier marker root container theta singleton :
  proof_macro nil
    (E_vac y (E_tagged_witness_hyp y x p marker root singleton) ::
     E_vac y (E_wel x container) ::
     tagged_witness_inputs y x p marker root container singleton)
    (E_wim (E_tagged_witness_hyp y x p marker root singleton)
      (E_wim (E_wex y (E_wa (E_wel y container)
        (E_tagged_choices y p carrier marker root theta singleton))) (E_wel x container))).
Proof.
  set (inputs:=E_vac y (E_tagged_witness_hyp y x p marker root singleton) ::
     E_vac y (E_wel x container) :: tagged_witness_inputs y x p marker root container singleton).
  assert (HP : proof_macro nil inputs
    (E_wim (E_tagged_witness_hyp y x p marker root singleton)
      (E_wim (E_wa (E_wel y container)
        (E_tagged_choices y p carrier marker root theta singleton)) (E_wel x container)))).
  { eapply (tagged_macro_inputs nil
      (tagged_witness_inputs y x p marker root container singleton) inputs).
    - intros e HE. unfold inputs. now right;right.
    - apply tagged_witness_point_program. }
  eapply macro_syl.
  - apply kp0_parameter_exists;[apply PM_input;unfold inputs;now left|exact HP].
  - apply kp0_implication_map,request_existential_collapse,PM_input.
    unfold inputs;now right;left.
Qed.

Theorem numerical_tagged_membership_transport M rho y x container :
  ns_proof M rho (E_wim (E_weq y x) (E_wim (E_wel y container) (E_wel x container))).
Proof.
  apply (ns_proof_macro M rho
    (E_weq container container ::
     E_wim (E_weq y x) (E_wim (E_weq container container)
       (E_wim (E_wel y container) (E_wel x container))) :: nil)).
  - intros e [<-|[<-|[]]].
    + apply ns_proof_reflexivity.
    + exact (ns_proof_atom_transport M rho false y x container container).
  - apply macro_discharge,macro_deduction.
    eapply md_mp with (a:=E_weq container container).
    + apply md_global,PM_input;now left.
    + eapply md_mp with (a:=E_weq y x);[apply md_hyp;now left|].
      apply md_global,PM_input;now right;left.
Qed.

Theorem numerical_tagged_witness_cleanup M rho y x p carrier marker root container theta singleton :
  ns_proof M rho (E_vac y (E_tagged_witness_hyp y x p marker root singleton)) ->
  ns_proof M rho (E_vac y (E_wel x container)) ->
  ns_proof M rho
    (E_wim (E_tagged_witness_hyp y x p marker root singleton)
      (E_wim (E_wex y (E_wa (E_wel y container)
        (E_tagged_choices y p carrier marker root theta singleton))) (E_wel x container))).
Proof.
  intros HH HM. apply (ns_proof_macro M rho
    (E_vac y (E_tagged_witness_hyp y x p marker root singleton) ::
     E_vac y (E_wel x container) :: tagged_witness_inputs y x p marker root container singleton)).
  - intros e [<-|[<-|[<-|[<-|[]]]]].
    + exact HH.
    + exact HM.
    + apply ns_stopping_self_specialization.
    + apply numerical_tagged_membership_transport.
  - apply tagged_witness_cleanup_program.
Qed.

Theorem numerical_tagged_witness_cleanup_fresh M rho y x p carrier marker root container theta singleton yv :
  code_relation M rho y yv -> yv<>zeroM M ->
  expression_name_avoids M rho yv p -> expression_name_avoids M rho yv root ->
  expression_name_avoids M rho yv marker -> expression_name_avoids M rho yv x ->
  expression_name_avoids M rho yv container ->
  ns_proof M rho
    (E_wim (E_tagged_witness_hyp y x p marker root singleton)
      (E_wim (E_wex y (E_wa (E_wel y container)
        (E_tagged_choices y p carrier marker root theta singleton))) (E_wel x container))).
Proof.
  intros HY HN HP HR HT HX HC. apply numerical_tagged_witness_cleanup.
  - apply (ns_proof_macro M rho
      (E_vac y (E_wn (E_weq p root)) :: E_vac y (E_wn (E_weq p marker)) ::
       E_vac y (E_wal y (E_wim singleton (E_weq y x))) :: nil)).
    + intros e [<-|[<-|[<-|[]]]].
      * apply (kp0_expression_fresh_vacuity M rho y (E_wn (E_weq p root)) yv HY).
        apply expression_fresh_negation;[exact HN|].
        apply expression_fresh_atom;[now right|exact HP|exact HR].
      * apply (kp0_expression_fresh_vacuity M rho y (E_wn (E_weq p marker)) yv HY).
        apply expression_fresh_negation;[exact HN|].
        apply expression_fresh_atom;[now right|exact HP|exact HT].
      * apply ns_bound_universal_vacuity.
    + unfold E_tagged_witness_hyp. apply kp0_vacuous_conjunction.
      * apply PM_input;now left.
      * apply kp0_vacuous_conjunction;apply PM_input;cbn;tauto.
  - apply (kp0_expression_fresh_vacuity M rho y (E_wel x container) yv HY).
    apply expression_fresh_atom;[now left|exact HX|exact HC].
Qed.

Theorem tagged_choices_output_substitution M rho yv xv y x p carrier marker root
    theta theta_x singleton singleton_x :
  yv<>zeroM M ->
  expression_named_replace M rho rho yv xv y x ->
  expression_named_replace M rho rho yv xv p p ->
  expression_named_replace M rho rho yv xv carrier carrier ->
  expression_named_replace M rho rho yv xv marker marker ->
  expression_named_replace M rho rho yv xv root root ->
  expression_named_substitution M rho rho yv xv theta theta_x ->
  expression_named_substitution M rho rho yv xv singleton singleton_x ->
  expression_named_substitution M rho rho yv xv
    (E_tagged_choices y p carrier marker root theta singleton)
    (E_tagged_choices x p carrier marker root theta_x singleton_x).
Proof.
  intros HN HY HP HB HT HR HTheta HS.
  unfold E_tagged_choices. apply expression_ns_disjunction;[exact HN| |].
  - apply expression_ns_conjunction;[exact HN| |];
      apply (expression_ns_atom M rho rho yv xv true);assumption.
  - apply expression_ns_disjunction;[exact HN| |].
    + apply expression_ns_conjunction;[exact HN| |];
        apply (expression_ns_atom M rho rho yv xv true);assumption.
    + apply expression_ns_conjunction;[exact HN|exact HS|].
      apply expression_ns_conjunction;[exact HN| |exact HTheta].
      apply (expression_ns_atom M rho rho yv xv false);assumption.
Qed.

Lemma tagged_choices_binder_absent M rho name y p carrier marker root theta singleton :
  expression_binder_absent M rho name theta -> expression_binder_absent M rho name singleton ->
  expression_binder_absent M rho name (E_tagged_choices y p carrier marker root theta singleton).
Proof.
  intros HTheta HS. unfold E_tagged_choices.
  apply expression_binder_absent_disjunction.
  - apply expression_binder_absent_conjunction;apply expression_binder_absent_atom;now right.
  - apply expression_binder_absent_disjunction.
    + apply expression_binder_absent_conjunction;apply expression_binder_absent_atom;now right.
    + apply expression_binder_absent_conjunction;[exact HS|].
      apply expression_binder_absent_conjunction;[|exact HTheta].
      apply expression_binder_absent_atom;now left.
Qed.

Theorem numerical_tagged_output_intro M rho yv xv y x p carrier marker root
    theta theta_x singleton singleton_x :
  code_relation M rho y yv -> code_relation M rho x xv -> yv<>xv -> yv<>zeroM M ->
  expression_named_replace M rho rho yv xv y x ->
  expression_named_replace M rho rho yv xv p p ->
  expression_named_replace M rho rho yv xv carrier carrier ->
  expression_named_replace M rho rho yv xv marker marker ->
  expression_named_replace M rho rho yv xv root root ->
  expression_named_substitution M rho rho yv xv theta theta_x ->
  expression_named_substitution M rho rho yv xv singleton singleton_x ->
  expression_binder_absent M rho xv theta -> expression_binder_absent M rho xv singleton ->
  ns_proof M rho
    (E_wim (E_tagged_choices x p carrier marker root theta_x singleton_x)
      (E_wex y (E_tagged_choices y p carrier marker root theta singleton))).
Proof.
  intros HY HX Hneq HN HReplace HP HB HT HR HTheta HS HBTheta HBS.
  destruct (code_relation_total M (E_tagged_choices y p carrier marker root theta singleton) rho)
    as [f HF].
  destruct (code_relation_total M (E_tagged_choices x p carrier marker root theta_x singleton_x) rho)
    as [v HV].
  assert (HAbs : named_binder_absent M f xv).
  { exact (tagged_choices_binder_absent M rho xv y p carrier marker root theta singleton
      HBTheta HBS f HF). }
  assert (HSub : NamedSubstitution.named_substitution M f yv xv v).
  { exact (tagged_choices_output_substitution M rho yv xv y x p carrier marker root
      theta theta_x singleton singleton_x HN HReplace HP HB HT HR HTheta HS f v HF HV). }
  exact (proj2 (ns_stopping_instantiation M rho y x
    (E_tagged_choices y p carrier marker root theta singleton)
    (E_tagged_choices x p carrier marker root theta_x singleton_x)
    yv xv f v HY HX HF HV Hneq HAbs HSub)).
Qed.

Definition E_tagged_local_request y p carrier marker root container theta singleton :=
  E_wim (E_kp_eligible root y container p)
    (E_wim (E_wex y (E_tagged_choices y p carrier marker root theta singleton))
      (E_wex y (E_wa (E_wel y container)
        (E_tagged_choices y p carrier marker root theta singleton)))).

Lemma tagged_request_use_program y x p carrier marker root container theta theta_x singleton singleton_x :
  proof_macro nil
    (E_wim (E_tagged_choices x p carrier marker root theta_x singleton_x)
       (E_wex y (E_tagged_choices y p carrier marker root theta singleton)) ::
     E_wim (E_tagged_witness_hyp y x p marker root singleton)
       (E_wim (E_wex y (E_wa (E_wel y container)
         (E_tagged_choices y p carrier marker root theta singleton))) (E_wel x container)) :: nil)
    (E_wim (E_tagged_witness_hyp y x p marker root singleton)
      (E_wim (E_tagged_local_request y p carrier marker root container theta singleton)
        (E_wim (E_kp_eligible root y container p)
          (E_wim (E_tagged_choices x p carrier marker root theta_x singleton_x) (E_wel x container))))).
Proof.
  apply macro_discharge. do 4 apply macro_deduction.
  eapply md_mp with (a:=E_wex y (E_wa (E_wel y container)
    (E_tagged_choices y p carrier marker root theta singleton))).
  - eapply md_mp with (a:=E_wex y (E_tagged_choices y p carrier marker root theta singleton)).
    + eapply md_mp;[apply md_hyp;now left|]. apply md_global,PM_input;now left.
    + eapply md_mp with (a:=E_kp_eligible root y container p);[apply md_hyp;cbn;tauto|].
      apply md_hyp;cbn;tauto.
  - eapply md_mp with (a:=E_tagged_witness_hyp y x p marker root singleton);
      [apply md_hyp;cbn;tauto|]. apply md_global,PM_input;now right;left.
Qed.

Theorem numerical_tagged_request_use M rho y x p carrier marker root container theta theta_x singleton singleton_x :
  ns_proof M rho (E_wim (E_tagged_choices x p carrier marker root theta_x singleton_x)
    (E_wex y (E_tagged_choices y p carrier marker root theta singleton))) ->
  ns_proof M rho (E_vac y (E_tagged_witness_hyp y x p marker root singleton)) ->
  ns_proof M rho (E_vac y (E_wel x container)) ->
  ns_proof M rho
    (E_wim (E_tagged_witness_hyp y x p marker root singleton)
      (E_wim (E_tagged_local_request y p carrier marker root container theta singleton)
        (E_wim (E_kp_eligible root y container p)
          (E_wim (E_tagged_choices x p carrier marker root theta_x singleton_x) (E_wel x container))))).
Proof.
  intros HIntro HVH HVM. eapply ns_proof_macro;[|apply tagged_request_use_program].
  intros e [<-|[<-|[]]].
  - exact HIntro.
  - exact (numerical_tagged_witness_cleanup M rho y x p carrier marker root container theta singleton HVH HVM).
Qed.

Print Assumptions tagged_choices_projection.
Print Assumptions numerical_tagged_support_projection.
Print Assumptions numerical_tagged_witness_cleanup.
Print Assumptions numerical_tagged_witness_cleanup_fresh.
Print Assumptions tagged_choices_output_substitution.
Print Assumptions numerical_tagged_output_intro.
Print Assumptions numerical_tagged_request_use.
