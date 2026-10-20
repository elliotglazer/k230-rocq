(** Renaming the raw Collection witness fibers without treating bound
    names as fresh in the context that contains the original profile. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent FreshNames
  NumericalEquivalence NumericalVacuitySteps NamedLeibnizSteps NamedSubstitution
  NamedSubstitutionRules TemplateNamedSubstitution NamedBinderFresh NamedBinderConstructors NamedExistential
  TemplateExistsAlpha QuotationPayloads QuotationNamedSubstitution QuotationBinderFresh SetFormulaCodes.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem numerical_named_exists_alpha_equivalence_checked M f x y g exf exg :
  x<>zeroM M -> y<>zeroM M -> x<>y -> named_binder_absent M f x ->
  formula_fresh M f y -> named_substitution M f x y g ->
  named_exists_graph M x f exf -> named_exists_graph M y g exg ->
  numerical_equivalent M exf exg.
Proof.
  intros HX HY HXY HA HF HS HEF HEG. split;intros result HR.
  - destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
      (exg .: exf .: fun _=>zeroM M)) as [back HB].
    exact (proj1 (numerical_named_exists_alpha M f x y g exf exg result back HX HY HXY HA HF HS HEF HEG HR HB)).
  - destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
      (exf .: exg .: fun _=>zeroM M)) as [forward HFor].
    exact (proj2 (numerical_named_exists_alpha M f x y g exf exg forward result HX HY HXY HA HF HS HEF HEG HFor HR)).
Qed.

Theorem raw_support_fiber_substitution M t a old new theta theta' dom dom' mem mem' child child' body body' :
  old<>zeroM M -> t<>old -> a<>old -> named_substitution M theta old new theta' ->
  membership_graph M t old dom -> membership_graph M t new dom' ->
  membership_graph M old a mem -> membership_graph M new a mem' ->
  quotation_binary M SFAnd dom mem child -> quotation_binary M SFAnd dom' mem' child' ->
  quotation_binary M SFAnd child theta body -> quotation_binary M SFAnd child' theta' body' ->
  named_substitution M body old new body'.
Proof.
  intros H0 HT HA HTheta HD HD' HM HM' HC HC' HB HB'.
  assert (SD : named_substitution M dom old new dom').
  { apply (ns_combine_atom M false t old dom t new dom' old new HD HD').
    - right;split;[exact HT|reflexivity].
    - left;auto. }
  assert (SM : named_substitution M mem old new mem').
  { apply (ns_combine_atom M false old a mem new a mem' old new HM HM').
    - left;auto.
    - right;split;[exact HA|reflexivity]. }
  exact (quotation_binary_named_substitution M SFAnd child theta child' theta' body body' old new H0
    (quotation_binary_named_substitution M SFAnd dom mem dom' mem' child child' old new H0 SD SM HC HC')
    HTheta HB HB').
Qed.

Theorem raw_coverage_fiber_substitution M t c old new theta theta' dom dom' mem mem' child child' body body' :
  old<>zeroM M -> t<>old -> c<>old -> named_substitution M theta old new theta' ->
  membership_graph M t old dom -> membership_graph M t new dom' ->
  membership_graph M old c mem -> membership_graph M new c mem' ->
  quotation_binary M SFAnd mem theta child -> quotation_binary M SFAnd mem' theta' child' ->
  quotation_binary M SFAnd dom child body -> quotation_binary M SFAnd dom' child' body' ->
  named_substitution M body old new body'.
Proof.
  intros H0 HT HC HTheta HD HD' HM HM' HG HG' HB HB'.
  assert (SD : named_substitution M dom old new dom').
  { apply (ns_combine_atom M false t old dom t new dom' old new HD HD').
    - right;split;[exact HT|reflexivity].
    - left;auto. }
  assert (SM : named_substitution M mem old new mem').
  { apply (ns_combine_atom M false old c mem new c mem' old new HM HM').
    - left;auto.
    - right;split;[exact HC|reflexivity]. }
  exact (quotation_binary_named_substitution M SFAnd dom child dom' child' body body' old new H0 SD
    (quotation_binary_named_substitution M SFAnd mem theta mem' theta' child child' old new H0 SM HTheta HG HG')
    HB HB').
Qed.

Theorem raw_support_fiber_alpha M t a old new theta theta' dom dom' mem mem' child child' body body' ex ex' :
  old<>zeroM M -> new<>zeroM M -> old<>new -> t<>old -> a<>old ->
  named_binder_absent M theta old -> formula_fresh M body new ->
  named_substitution M theta old new theta' ->
  membership_graph M t old dom -> membership_graph M t new dom' ->
  membership_graph M old a mem -> membership_graph M new a mem' ->
  quotation_binary M SFAnd dom mem child -> quotation_binary M SFAnd dom' mem' child' ->
  quotation_binary M SFAnd child theta body -> quotation_binary M SFAnd child' theta' body' ->
  named_exists_graph M old body ex -> named_exists_graph M new body' ex' ->
  numerical_equivalent M ex ex'.
Proof.
  intros H0 HN HOn HT HA HAbsent HFresh HTheta HD HD' HM HM' HC HC' HB HB' HE HE'.
  apply (numerical_named_exists_alpha_equivalence_checked M body old new body' ex ex' H0 HN HOn).
  - apply (quotation_binary_binder_absent M SFAnd child theta body old HB);[|exact HAbsent].
    apply (quotation_binary_binder_absent M SFAnd dom mem child old HC).
    + exact (named_binder_absent_membership M t old dom old HD).
    + exact (named_binder_absent_membership M old a mem old HM).
  - exact HFresh.
  - exact (raw_support_fiber_substitution M t a old new theta theta' dom dom' mem mem' child child' body body'
      H0 HT HA HTheta HD HD' HM HM' HC HC' HB HB').
  - exact HE.
  - exact HE'.
Qed.

Theorem raw_coverage_fiber_alpha M t c old new theta theta' dom dom' mem mem' child child' body body' ex ex' :
  old<>zeroM M -> new<>zeroM M -> old<>new -> t<>old -> c<>old ->
  named_binder_absent M theta old -> formula_fresh M body new ->
  named_substitution M theta old new theta' ->
  membership_graph M t old dom -> membership_graph M t new dom' ->
  membership_graph M old c mem -> membership_graph M new c mem' ->
  quotation_binary M SFAnd mem theta child -> quotation_binary M SFAnd mem' theta' child' ->
  quotation_binary M SFAnd dom child body -> quotation_binary M SFAnd dom' child' body' ->
  named_exists_graph M old body ex -> named_exists_graph M new body' ex' ->
  numerical_equivalent M ex ex'.
Proof.
  intros H0 HN HOn HT HC HAbsent HFresh HTheta HD HD' HM HM' HG HG' HB HB' HE HE'.
  apply (numerical_named_exists_alpha_equivalence_checked M body old new body' ex ex' H0 HN HOn).
  - apply (quotation_binary_binder_absent M SFAnd dom child body old HB).
    + exact (named_binder_absent_membership M t old dom old HD).
    + apply (quotation_binary_binder_absent M SFAnd mem theta child old HG);[|exact HAbsent].
      exact (named_binder_absent_membership M old c mem old HM).
  - exact HFresh.
  - exact (raw_coverage_fiber_substitution M t c old new theta theta' dom dom' mem mem' child child' body body'
      H0 HT HC HTheta HD HD' HM HM' HG HG' HB HB').
  - exact HE.
  - exact HE'.
Qed.

Print Assumptions numerical_named_exists_alpha_equivalence_checked.
Print Assumptions raw_support_fiber_substitution.
Print Assumptions raw_coverage_fiber_substitution.
Print Assumptions raw_support_fiber_alpha.
Print Assumptions raw_coverage_fiber_alpha.

Theorem raw_guarded_fiber_substitution M t old new theta theta' dom dom' body body' :
  old<>zeroM M -> t<>old -> named_substitution M theta old new theta' ->
  membership_graph M t old dom -> membership_graph M t new dom' ->
  quotation_binary M SFAnd dom theta body -> quotation_binary M SFAnd dom' theta' body' ->
  named_substitution M body old new body'.
Proof.
  intros H0 HT HS HD HD' HB HB'.
  apply (quotation_binary_named_substitution M SFAnd dom theta dom' theta' body body' old new H0);try assumption.
  apply (ns_combine_atom M false t old dom t new dom' old new HD HD').
  - right;split;[exact HT|reflexivity].
  - left;auto.
Qed.

Theorem raw_guarded_fiber_alpha M t old new theta theta' dom dom' body body' ex ex' :
  old<>zeroM M -> new<>zeroM M -> old<>new -> t<>old ->
  named_binder_absent M theta old -> formula_fresh M body new ->
  named_substitution M theta old new theta' ->
  membership_graph M t old dom -> membership_graph M t new dom' ->
  quotation_binary M SFAnd dom theta body -> quotation_binary M SFAnd dom' theta' body' ->
  named_exists_graph M old body ex -> named_exists_graph M new body' ex' ->
  numerical_equivalent M ex ex'.
Proof.
  intros H0 HN HOn HT HA HF HS HD HD' HB HB' HE HE'.
  apply (numerical_named_exists_alpha_equivalence_checked M body old new body' ex ex' H0 HN HOn).
  - exact (quotation_binary_binder_absent M SFAnd dom theta body old HB
      (named_binder_absent_membership M t old dom old HD) HA).
  - exact HF.
  - exact (raw_guarded_fiber_substitution M t old new theta theta' dom dom' body body' H0 HT HS HD HD' HB HB').
  - exact HE.
  - exact HE'.
Qed.

Print Assumptions raw_guarded_fiber_substitution.
Print Assumptions raw_guarded_fiber_alpha.
