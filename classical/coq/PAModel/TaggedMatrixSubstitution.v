(** Exact input substitution in the arbitrary internal tagged matrix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent
  NumericalProofs NumericalEquality NamedLeibnizSteps ProofTemplates
  NamedSubstitution NamedSubstitutionFunctionality NamedBinderFresh
  TemplateFormulaFresh TemplateBinderFresh TemplateNamedSubstitution
  NumericalSingleton NumericalTaggedComprehension NumericalTaggedMatrix
  FreshSubstitutionIdentity ExpressionFreshElimination QuotientAtomTemplates.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Lemma tagged_matrix_fresh_parts M rho name y input carrier marker root theta z :
  expression_fresh M rho name (E_tagged_matrix y input carrier marker root theta z) ->
  expression_name_avoids M rho name input /\ expression_name_avoids M rho name root /\
  expression_name_avoids M rho name y /\ expression_name_avoids M rho name carrier /\
  expression_name_avoids M rho name marker /\ expression_name_avoids M rho name z /\
  expression_fresh M rho name theta.
Proof.
  intro HM. unfold E_tagged_matrix,E_tagged_choices in HM.
  apply expression_fresh_disjunction_parts in HM. destruct HM as [HFirst HRest].
  apply expression_fresh_conjunction_parts in HFirst. destruct HFirst as [HI HY].
  apply expression_fresh_equality_names in HI. destruct HI as [Hinput Hroot].
  apply expression_fresh_equality_names in HY. destruct HY as [Hy Hcarrier].
  apply expression_fresh_disjunction_parts in HRest. destruct HRest as [HSecond HLast].
  apply expression_fresh_conjunction_parts in HSecond. destruct HSecond as [HT _].
  apply expression_fresh_equality_names in HT. destruct HT as [_ Hmarker].
  apply expression_fresh_conjunction_parts in HLast. destruct HLast as [HS HSelected].
  apply expression_fresh_conjunction_parts in HSelected. destruct HSelected as [_ Htheta].
  unfold E_raw_singleton in HS. apply expression_fresh_conjunction_parts in HS.
  destruct HS as [_ HAll]. apply expression_fresh_universal_parts in HAll.
  destruct HAll as [Hz _]. repeat split;assumption.
Qed.

Theorem tagged_matrix_input_substitution M rho y input query carrier marker root theta z
    inputv queryv zv :
  code_relation M rho input inputv -> code_relation M rho query queryv ->
  code_relation M rho z zv -> inputv<>zeroM M -> zv<>inputv -> zv<>queryv ->
  expression_name_avoids M rho inputv y ->
  expression_name_avoids M rho inputv carrier ->
  expression_name_avoids M rho inputv marker ->
  expression_name_avoids M rho inputv root ->
  expression_fresh M rho inputv theta -> expression_binder_absent M rho queryv theta ->
  expression_named_substitution M rho rho inputv queryv
    (E_tagged_matrix y input carrier marker root theta z)
    (E_tagged_matrix y query carrier marker root theta z).
Proof.
  intros HI HP HZ H0 HZI HZP HY HB HT HR HTheta HBind.
  assert (RI:expression_named_replace M rho rho inputv queryv input query).
  { intros u v HU HV. rewrite (code_relation_functional M input rho u inputv HU HI),
      (code_relation_functional M query rho v queryv HV HP). now left. }
  assert (fixed:forall X,expression_name_avoids M rho inputv X ->
    expression_named_replace M rho rho inputv queryv X X).
  { intros X HX u v HU HV. right. split;[exact (HX u HU)|].
    symmetry. exact (code_relation_functional M X rho u v HU HV). }
  assert (RY:expression_named_replace M rho rho inputv queryv y y) by exact (fixed y HY).
  assert (RB:expression_named_replace M rho rho inputv queryv carrier carrier) by exact (fixed carrier HB).
  assert (RT:expression_named_replace M rho rho inputv queryv marker marker) by exact (fixed marker HT).
  assert (RR:expression_named_replace M rho rho inputv queryv root root) by exact (fixed root HR).
  assert (RZ:expression_named_replace M rho rho inputv queryv z z).
  { apply fixed. intros v HV. now rewrite (code_relation_functional M z rho v zv HV HZ). }
  assert (STheta:expression_named_substitution M rho rho inputv queryv theta theta).
  { intros f g HF HG. assert (E:g=f) by exact (code_relation_functional M theta rho g f HG HF).
    subst g. exact (named_substitution_source_fresh M f inputv queryv (HTheta f HF) (HBind f HF)). }
  assert (SS:expression_named_substitution M rho rho inputv queryv
    (E_raw_singleton y input z) (E_raw_singleton y query z)).
  { unfold E_raw_singleton. apply expression_ns_conjunction;[exact H0| |].
    - apply (expression_ns_atom M rho rho inputv queryv false);assumption.
    - apply (expression_ns_universal M rho rho inputv queryv z z _ _ zv HZ HZ HZI HZP).
      apply expression_ns_implication.
      + apply (expression_ns_atom M rho rho inputv queryv false);assumption.
      + apply (expression_ns_atom M rho rho inputv queryv true);assumption. }
  unfold E_tagged_matrix,E_tagged_choices.
  apply expression_ns_disjunction;[exact H0| |].
  - apply expression_ns_conjunction;[exact H0| |];
      apply (expression_ns_atom M rho rho inputv queryv true);assumption.
  - apply expression_ns_disjunction;[exact H0| |].
    + apply expression_ns_conjunction;[exact H0| |];
        apply (expression_ns_atom M rho rho inputv queryv true);assumption.
    + apply expression_ns_conjunction;[exact H0|exact SS|].
      apply expression_ns_conjunction;[exact H0| |exact STheta].
      apply (expression_ns_atom M rho rho inputv queryv false);assumption.
Qed.

Print Assumptions tagged_matrix_fresh_parts.
Print Assumptions tagged_matrix_input_substitution.
