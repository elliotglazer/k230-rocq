(** The actual binary Collection matrix has a numerical KP0 instance.
    The input selecting a singleton differs from the bound element tested
    by that singleton.  The arbitrary internal relation is left intact. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs ProofTemplates NumericalSingleton NumericalTaggedMatrix
  NumericalFixedSeed KP0SeedSpecialization TemplateBinderFresh TemplateFormulaFresh FreshNames
  NamedBinderFresh NamedSubstitution NamedSubstitutionFunctionality
  TemplateNamedSubstitution FreshSubstitutionIdentity ExpressionFreshElimination
  CollectionSupportCleanup.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Lemma collection_matrix_mentions_root M rho T A B R I U V Theta Z r :
  code_relation M rho R r -> expression_mentions M rho r
    (E_collection_choices T A B R I U V Theta Z).
Proof.
  intro HR. unfold E_collection_choices.
  apply expression_mentions_disjunction_left,expression_mentions_conjunction_left.
  destruct (code_relation_total M I rho) as [i HI].
  exact (expression_mentions_equality_right M rho I R i r HI HR).
Qed.

Lemma collection_matrix_binder_absent M rho name T A B R I U V Theta Z u z :
  code_relation M rho U u -> code_relation M rho Z z ->
  u<>name -> z<>name -> expression_binder_absent M rho name Theta ->
  expression_binder_absent M rho name (E_collection_choices T A B R I U V Theta Z).
Proof.
  intros HU HZ HUN HZN HTheta. unfold E_collection_choices,E_collection_selected.
  apply expression_binder_absent_disjunction.
  - apply expression_binder_absent_conjunction;apply expression_binder_absent_atom;now right.
  - apply expression_binder_absent_disjunction.
    + apply expression_binder_absent_conjunction;apply expression_binder_absent_atom;now right.
    + apply expression_binder_absent_existential.
      * intros v Hv. now rewrite (code_relation_functional M U rho v u Hv HU).
      * apply expression_binder_absent_conjunction.
        -- unfold E_raw_singleton. apply expression_binder_absent_conjunction.
           ++ apply expression_binder_absent_atom;now left.
           ++ apply expression_binder_absent_universal.
              ** intros v Hv. now rewrite (code_relation_functional M Z rho v z Hv HZ).
              ** apply expression_binder_absent_implication;apply expression_binder_absent_atom;auto.
        -- apply expression_binder_absent_conjunction.
           ++ apply expression_binder_absent_conjunction;apply expression_binder_absent_atom;now left.
           ++ apply expression_binder_absent_conjunction;[apply expression_binder_absent_atom;now left|exact HTheta].
Qed.

Definition collection_matrix_parameters M i v t a b r u theta z :=
  i .: v .: t .: a .: b .: r .: u .: theta .: z .: fun _=>zeroM M.
Definition E_collection_parameter_matrix :=
  E_collection_choices (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)
    (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8).

Theorem numerical_collection_matrix_instance M i v t a b r u theta z m :
  i<>zeroM M -> v<>i -> i<>r -> v<>r -> u<>i -> u<>r -> z<>i -> z<>r ->
  named_binder_absent M theta i -> named_binder_absent M theta r ->
  code_relation M (collection_matrix_parameters M i v t a b r u theta z)
    E_collection_parameter_matrix m ->
  exists k p mp f,
    k<>i /\ k<>v /\ k<>r /\ i<>p /\ v<>p /\ k<>p /\ p<>r /\
    p<>zeroM M /\ formula_fresh M m k /\ formula_fresh M m p /\
    named_substitution M m i p mp /\
    code_relation M (kp0_seed_parameters M i v k p m mp r)
      (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2)
        (CEvar 3) (CEvar 4) (CEvar 5)) f /\ numerically_provable M f.
Proof.
  intros H0 HVI HIR HVR HUI HUR HZI HZR HTI HTR HM.
  set (rho:=collection_matrix_parameters M i v t a b r u theta z).
  apply (numerical_uniform_kp0_fixed_seed M i v m r H0 HVI HIR HVR).
  - exact (collection_matrix_binder_absent M rho i (CEvar 2) (CEvar 3) (CEvar 4)
      (CEvar 5) (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8) u z
      eq_refl eq_refl HUI HZI ltac:(intros f Hf;change (f=theta) in Hf;now subst f) m HM).
  - exact (collection_matrix_binder_absent M rho r (CEvar 2) (CEvar 3) (CEvar 4)
      (CEvar 5) (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8) u z
      eq_refl eq_refl HUR HZR ltac:(intros f Hf;change (f=theta) in Hf;now subst f) m HM).
  - exact (collection_matrix_mentions_root M rho (CEvar 2) (CEvar 3) (CEvar 4)
      (CEvar 5) (CEvar 0) (CEvar 6) (CEvar 1) (CEvar 7) (CEvar 8) r eq_refl m HM).
Qed.

Lemma collection_fresh_exists_parts M rho name U F :
  expression_fresh M rho name (E_wex U F) ->
  expression_name_avoids M rho name U /\ expression_fresh M rho name F.
Proof.
  unfold E_wex. intro H. apply expression_fresh_negation_body in H.
  apply expression_fresh_universal_parts in H. destruct H as [HU HF].
  split;[exact HU|now apply expression_fresh_negation_body in HF].
Qed.

Lemma collection_matrix_fresh_parts M rho name T A B R I U V Theta Z :
  expression_fresh M rho name (E_collection_choices T A B R I U V Theta Z) ->
  expression_name_avoids M rho name I /\ expression_name_avoids M rho name R /\
  expression_name_avoids M rho name V /\ expression_name_avoids M rho name B /\
  expression_name_avoids M rho name T /\ expression_name_avoids M rho name U /\
  expression_name_avoids M rho name Z /\ expression_fresh M rho name Theta.
Proof.
  unfold E_collection_choices. intro H.
  apply expression_fresh_disjunction_parts in H. destruct H as [HFirst HRest].
  apply expression_fresh_conjunction_parts in HFirst. destruct HFirst as [HIR HVB].
  apply expression_fresh_equality_names in HIR. destruct HIR as [HI HR].
  apply expression_fresh_equality_names in HVB. destruct HVB as [HV HB].
  apply expression_fresh_disjunction_parts in HRest. destruct HRest as [HSecond HSelected].
  apply expression_fresh_conjunction_parts in HSecond. destruct HSecond as [HIT _].
  apply expression_fresh_equality_names in HIT. destruct HIT as [_ HT].
  unfold E_collection_selected in HSelected.
  apply collection_fresh_exists_parts in HSelected. destruct HSelected as [HU HBody].
  apply expression_fresh_conjunction_parts in HBody. destruct HBody as [HSingleton HBody].
  apply expression_fresh_conjunction_parts in HBody. destruct HBody as [_ HBody].
  apply expression_fresh_conjunction_parts in HBody. destruct HBody as [_ HTheta].
  unfold E_raw_singleton in HSingleton.
  apply expression_fresh_conjunction_parts in HSingleton. destruct HSingleton as [_ HAll].
  apply expression_fresh_universal_parts in HAll. destruct HAll as [HZ _].
  repeat split;assumption.
Qed.

Theorem collection_matrix_input_substitution M rho T A B R I P U V Theta Z i p u z :
  code_relation M rho I i -> code_relation M rho P p ->
  code_relation M rho U u -> code_relation M rho Z z ->
  i<>zeroM M -> u<>i -> u<>p -> z<>i -> z<>p ->
  expression_name_avoids M rho i T -> expression_name_avoids M rho i A ->
  expression_name_avoids M rho i B -> expression_name_avoids M rho i R ->
  expression_name_avoids M rho i V ->
  expression_fresh M rho i Theta -> expression_binder_absent M rho p Theta ->
  expression_named_substitution M rho rho i p
    (E_collection_choices T A B R I U V Theta Z)
    (E_collection_choices T A B R P U V Theta Z).
Proof.
  intros HI HP HU HZ H0 HUI HUP HZI HZP HT HA HB HR HV HTheta HBind.
  assert (RI:expression_named_replace M rho rho i p I P).
  { intros x y HX HY. rewrite (code_relation_functional M I rho x i HX HI),
      (code_relation_functional M P rho y p HY HP). now left. }
  assert (fixed:forall X,expression_name_avoids M rho i X ->
    expression_named_replace M rho rho i p X X).
  { intros X HX x y Hx Hy. right. split;[exact (HX x Hx)|].
    symmetry. exact (code_relation_functional M X rho x y Hx Hy). }
  assert (RT:expression_named_replace M rho rho i p T T) by exact (fixed T HT).
  assert (RA:expression_named_replace M rho rho i p A A) by exact (fixed A HA).
  assert (RB:expression_named_replace M rho rho i p B B) by exact (fixed B HB).
  assert (RR:expression_named_replace M rho rho i p R R) by exact (fixed R HR).
  assert (RV:expression_named_replace M rho rho i p V V) by exact (fixed V HV).
  assert (RU:expression_named_replace M rho rho i p U U).
  { apply fixed. intros x HX. now rewrite (code_relation_functional M U rho x u HX HU). }
  assert (RZ:expression_named_replace M rho rho i p Z Z).
  { apply fixed. intros x HX. now rewrite (code_relation_functional M Z rho x z HX HZ). }
  assert (STheta:expression_named_substitution M rho rho i p Theta Theta).
  { intros f g HF HG. assert (E:g=f) by exact (code_relation_functional M Theta rho g f HG HF).
    subst g. exact (named_substitution_source_fresh M f i p (HTheta f HF) (HBind f HF)). }
  unfold E_collection_choices. apply expression_ns_disjunction;[exact H0| |].
  - apply expression_ns_conjunction;[exact H0| |];apply (expression_ns_atom M rho rho i p true);assumption.
  - apply expression_ns_disjunction;[exact H0| |].
    + apply expression_ns_conjunction;[exact H0| |];apply (expression_ns_atom M rho rho i p true);assumption.
    + unfold E_collection_selected.
      apply (expression_ns_existential M rho rho i p U U _ _ u H0 HU HU HUI HUP).
      apply expression_ns_conjunction;[exact H0| |].
      * unfold E_raw_singleton. apply expression_ns_conjunction;[exact H0| |].
        -- apply (expression_ns_atom M rho rho i p false);assumption.
        -- apply (expression_ns_universal M rho rho i p Z Z _ _ z HZ HZ HZI HZP).
           apply expression_ns_implication.
           ++ apply (expression_ns_atom M rho rho i p false);assumption.
           ++ apply (expression_ns_atom M rho rho i p true);assumption.
      * apply expression_ns_conjunction;[exact H0| |].
        -- apply expression_ns_conjunction;[exact H0| |];apply (expression_ns_atom M rho rho i p false);assumption.
        -- apply expression_ns_conjunction;[exact H0| |exact STheta].
           apply (expression_ns_atom M rho rho i p false);assumption.
Qed.

Print Assumptions numerical_collection_matrix_instance.
Print Assumptions collection_matrix_fresh_parts.
Print Assumptions collection_matrix_input_substitution.
