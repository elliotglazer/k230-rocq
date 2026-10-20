(** Capture-checked specialization of the relation-free exceptional request
    summary. The arbitrary Collection matrix is absent from this formula. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedSubstitution TemplateNamedSubstitution TemplateBinderFresh TemplateFormulaFresh
  NumericalKP0 NumericalKP0Eligibility NumericalSingleton NamedLeibnizSteps
  StoppingInstantiation QuotientAtomTemplates CollectionRequestProjection.
Unset Implicit Arguments.

Definition E_collection_reduced_at T B R C P U V Z :=
  E_wim (E_kp_eligible R V C P) (E_collection_reduced_request T B R C P U V Z).

Lemma collection_reduced_at_absent M rho T B R C P U V Z j :
  expression_name_avoids M rho j C -> expression_name_avoids M rho j U ->
  expression_name_avoids M rho j V -> expression_name_avoids M rho j Z ->
  expression_binder_absent M rho j (E_collection_reduced_at T B R C P U V Z).
Proof.
  intros HC HU HV HZ. unfold E_collection_reduced_at,E_kp_eligible,
    E_collection_reduced_request,E_collection_first_two,E_collection_summary,E_ksubset,E_raw_singleton.
  apply expression_binder_absent_implication.
  - apply expression_binder_absent_disjunction;[apply expression_binder_absent_atom;now right|].
    apply expression_binder_absent_existential;[exact HV|].
    apply expression_binder_absent_conjunction;[apply expression_binder_absent_atom;now left|].
    apply expression_binder_absent_universal;[exact HC|].
    apply expression_binder_absent_implication;apply expression_binder_absent_atom;now left.
  - apply expression_binder_absent_implication.
    + apply expression_binder_absent_existential;[exact HV|].
      apply expression_binder_absent_disjunction;apply expression_binder_absent_conjunction;
        apply expression_binder_absent_atom;now right.
    + apply expression_binder_absent_existential;[exact HV|].
      apply expression_binder_absent_conjunction;[apply expression_binder_absent_atom;now left|].
      apply expression_binder_absent_disjunction.
      * apply expression_binder_absent_conjunction;apply expression_binder_absent_atom;now right.
      * apply expression_binder_absent_disjunction.
        -- apply expression_binder_absent_conjunction;apply expression_binder_absent_atom;now right.
        -- apply expression_binder_absent_existential;[exact HU|].
           apply expression_binder_absent_conjunction;[apply expression_binder_absent_atom;now left|].
           apply expression_binder_absent_universal;[exact HZ|].
           apply expression_binder_absent_implication;apply expression_binder_absent_atom;auto.
Qed.

Theorem collection_reduced_at_substitution M rho T B R C P J U V Z p j c u v z :
  code_relation M rho P p -> code_relation M rho J j ->
  code_relation M rho C c -> code_relation M rho U u ->
  code_relation M rho V v -> code_relation M rho Z z ->
  p<>zeroM M -> c<>p -> c<>j -> u<>p -> u<>j -> v<>p -> v<>j -> z<>p -> z<>j ->
  expression_name_avoids M rho p T -> expression_name_avoids M rho p B ->
  expression_name_avoids M rho p R ->
  expression_named_substitution M rho rho p j
    (E_collection_reduced_at T B R C P U V Z) (E_collection_reduced_at T B R C J U V Z).
Proof.
  intros HP HJ HC HU HV HZ H0 HCP HCJ HUP HUJ HVP HVJ HZP HZJ HT HB HR.
  assert (RP:expression_named_replace M rho rho p j P J).
  { intros x y HX HY. rewrite (code_relation_functional M P rho x p HX HP),
      (code_relation_functional M J rho y j HY HJ). now left. }
  assert (fixed:forall X,expression_name_avoids M rho p X -> expression_named_replace M rho rho p j X X).
  { intros X HX x y Hx Hy. right. split;[exact (HX x Hx)|].
    symmetry. exact (code_relation_functional M X rho x y Hx Hy). }
  assert (RT:expression_named_replace M rho rho p j T T) by now apply fixed.
  assert (RB:expression_named_replace M rho rho p j B B) by now apply fixed.
  assert (RR:expression_named_replace M rho rho p j R R) by now apply fixed.
  assert (RC:expression_named_replace M rho rho p j C C).
  { apply fixed. intros x HX. now rewrite (code_relation_functional M C rho x c HX HC). }
  assert (RU:expression_named_replace M rho rho p j U U).
  { apply fixed. intros x HX. now rewrite (code_relation_functional M U rho x u HX HU). }
  assert (RV:expression_named_replace M rho rho p j V V).
  { apply fixed. intros x HX. now rewrite (code_relation_functional M V rho x v HX HV). }
  assert (RZ:expression_named_replace M rho rho p j Z Z).
  { apply fixed. intros x HX. now rewrite (code_relation_functional M Z rho x z HX HZ). }
  assert (F:expression_named_substitution M rho rho p j
    (E_collection_first_two T B R P V) (E_collection_first_two T B R J V)).
  { unfold E_collection_first_two. apply expression_ns_disjunction;[exact H0| |];
      apply expression_ns_conjunction;try exact H0;apply (expression_ns_atom M rho rho p j true);assumption. }
  assert (S:expression_named_substitution M rho rho p j
    (E_collection_summary T B R P U V Z) (E_collection_summary T B R J U V Z)).
  { unfold E_collection_summary. apply expression_ns_disjunction;[exact H0| |].
    - apply expression_ns_conjunction;try exact H0;apply (expression_ns_atom M rho rho p j true);assumption.
    - apply expression_ns_disjunction;[exact H0| |].
      + apply expression_ns_conjunction;try exact H0;apply (expression_ns_atom M rho rho p j true);assumption.
      + apply (expression_ns_existential M rho rho p j U U _ _ u H0 HU HU HUP HUJ).
        unfold E_raw_singleton. apply expression_ns_conjunction;[exact H0| |].
        * apply (expression_ns_atom M rho rho p j false);assumption.
        * apply (expression_ns_universal M rho rho p j Z Z _ _ z HZ HZ HZP HZJ).
          apply expression_ns_implication.
          -- apply (expression_ns_atom M rho rho p j false);assumption.
          -- apply (expression_ns_atom M rho rho p j true);assumption. }
  unfold E_collection_reduced_at. apply expression_ns_implication.
  - unfold E_kp_eligible. apply expression_ns_disjunction;[exact H0| |].
    + apply (expression_ns_atom M rho rho p j true);assumption.
    + apply (expression_ns_existential M rho rho p j V V _ _ v H0 HV HV HVP HVJ).
      apply expression_ns_conjunction;[exact H0| |].
      * apply (expression_ns_atom M rho rho p j false);assumption.
      * unfold E_ksubset. apply (expression_ns_universal M rho rho p j C C _ _ c HC HC HCP HCJ).
        apply expression_ns_implication;apply (expression_ns_atom M rho rho p j false);assumption.
  - unfold E_collection_reduced_request. apply expression_ns_implication.
    + exact (expression_ns_existential M rho rho p j V V _ _ v H0 HV HV HVP HVJ F).
    + apply (expression_ns_existential M rho rho p j V V _ _ v H0 HV HV HVP HVJ).
      apply expression_ns_conjunction;[exact H0| |exact S].
      apply (expression_ns_atom M rho rho p j false);assumption.
Qed.

Theorem numerical_collection_reduced_specialization M rho T B R C P J U V Z p j c u v z :
  code_relation M rho P p -> code_relation M rho J j ->
  code_relation M rho C c -> code_relation M rho U u ->
  code_relation M rho V v -> code_relation M rho Z z ->
  p<>zeroM M -> p<>j -> c<>p -> c<>j -> u<>p -> u<>j -> v<>p -> v<>j -> z<>p -> z<>j ->
  expression_name_avoids M rho p T -> expression_name_avoids M rho p B ->
  expression_name_avoids M rho p R ->
  ns_proof M rho (E_wim (E_collection_reduced_requests T B R C P U V Z)
    (E_collection_reduced_at T B R C J U V Z)).
Proof.
  intros HP HJ HC HU HV HZ H0 HPJ HCP HCJ HUP HUJ HVP HVJ HZP HZJ HT HB HR.
  destruct (code_relation_total M (E_collection_reduced_at T B R C P U V Z) rho) as [f HF].
  destruct (code_relation_total M (E_collection_reduced_at T B R C J U V Z) rho) as [g HG].
  assert (HA:expression_binder_absent M rho j (E_collection_reduced_at T B R C P U V Z)).
  { apply (collection_reduced_at_absent M rho T B R C P U V Z j);try (intros x HX);
      [now rewrite (code_relation_functional M C rho x c HX HC)|
       now rewrite (code_relation_functional M U rho x u HX HU)|
       now rewrite (code_relation_functional M V rho x v HX HV)|
       now rewrite (code_relation_functional M Z rho x z HX HZ)]. }
  pose proof (collection_reduced_at_substitution M rho T B R C P J U V Z p j c u v z
      HP HJ HC HU HV HZ H0 HCP HCJ HUP HUJ HVP HVJ HZP HZJ HT HB HR f g HF HG) as HS.
  exact (proj1 (ns_stopping_instantiation M rho P J
    (E_collection_reduced_at T B R C P U V Z) (E_collection_reduced_at T B R C J U V Z)
    p j f g HP HJ HF HG HPJ (HA f HF) HS)).
Qed.

Print Assumptions collection_reduced_at_absent.
Print Assumptions collection_reduced_at_substitution.
Print Assumptions numerical_collection_reduced_specialization.
