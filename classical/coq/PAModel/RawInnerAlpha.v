(** The inner witness of each raw Collection clause can be changed by
    checked numerical alpha conversion, without changing its outer binder. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent NumericalProofs
  NumericalEquivalence NamedSubstitution NamedBinderFresh FreshNames TemplateBinderFresh TemplateFormulaFresh
  TemplateNamedSubstitution RawCollectionProfile RawClauseAlpha ExpressionAlpha.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem raw_support_inner_alpha M t a c old new v theta theta' all all' :
  old<>zeroM M -> new<>zeroM M -> old<>new -> t<>old -> a<>old ->
  t<>new -> a<>new -> named_binder_absent M theta old -> formula_fresh M theta new ->
  named_substitution M theta old new theta' ->
  code_relation M (raw_clause_parameters M t a c old v theta)
    (E_wal (CEvar 4) E_raw_support_clause) all ->
  code_relation M (raw_clause_parameters M t a c new v theta')
    (E_wal (CEvar 4) E_raw_support_clause) all' -> numerical_equivalent M all all'.
Proof.
  intros H0 H1 Hxy HT HA HTN HAN HB HF HS G G'.
  set (rho:=t .: a .: c .: old .: v .: theta .: new .: theta' .: fun _=>zeroM M).
  apply (proj1 (numerical_equivalent_expression M rho
    (E_wal (CEvar 4) (E_raw_collection_support (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)))
    (E_wal (CEvar 4) (E_raw_collection_support (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 6) (CEvar 4) (CEvar 7)))
    all all' G G')).
  apply expression_equivalent_all. unfold E_raw_collection_support.
  apply expression_equivalent_implication;[apply expression_equivalent_refl|].
  apply (expression_exists_alpha_capture_free M rho (CEvar 3) (CEvar 6) _ _ old new eq_refl eq_refl H0 H1 Hxy).
  - apply expression_binder_absent_conjunction.
    + apply expression_binder_absent_conjunction;apply expression_binder_absent_atom;now left.
    + intros f H;change (f=theta) in H;now subst f.
  - apply expression_fresh_conjunction;[exact H1| |].
    + apply expression_fresh_conjunction;[exact H1| |];apply expression_fresh_atom;[now left| |now intros ? ->|now left|now intros ? ->|now intros ? ->].
      intros ? ->;exact HTN.
    + intros f H;change (f=theta) in H;now subst f.
  - assert (R0:expression_named_replace M rho rho old new (CEvar 0) (CEvar 0)).
    { intros f g -> ->;right;split;[exact HT|reflexivity]. }
    assert (R1:expression_named_replace M rho rho old new (CEvar 1) (CEvar 1)).
    { intros f g -> ->;right;split;[exact HA|reflexivity]. }
    assert (RX:expression_named_replace M rho rho old new (CEvar 3) (CEvar 6)).
    { intros f g -> ->;left;auto. }
    apply expression_ns_conjunction;[exact H0| |].
    + apply expression_ns_conjunction;[exact H0| |];apply (expression_ns_atom M rho rho old new false);assumption.
    + intros f g H H';change(f=theta) in H;change(g=theta') in H';now subst f g.
Qed.

Print Assumptions raw_support_inner_alpha.


Theorem raw_coverage_inner_alpha M t a c u old new theta theta' all all' :
  old<>zeroM M -> new<>zeroM M -> old<>new -> t<>old -> c<>old ->
  t<>new -> c<>new -> named_binder_absent M theta old -> formula_fresh M theta new ->
  named_substitution M theta old new theta' ->
  code_relation M (raw_clause_parameters M t a c u old theta)
    (E_wal (CEvar 3) E_raw_coverage_clause) all ->
  code_relation M (raw_clause_parameters M t a c u new theta')
    (E_wal (CEvar 3) E_raw_coverage_clause) all' -> numerical_equivalent M all all'.
Proof.
  intros H0 H1 Hxy HT HC HTN HCN HB HF HS G G'.
  set (rho:=t .: a .: c .: u .: old .: theta .: new .: theta' .: fun _=>zeroM M).
  assert (R0:expression_named_replace M rho rho old new (CEvar 0) (CEvar 0)).
  { intros f g -> ->;right;split;[exact HT|reflexivity]. }
  assert (R2:expression_named_replace M rho rho old new (CEvar 2) (CEvar 2)).
  { intros f g -> ->;right;split;[exact HC|reflexivity]. }
  assert (RX:expression_named_replace M rho rho old new (CEvar 4) (CEvar 6)).
  { intros f g -> ->;left;auto. }
  assert (RS:expression_named_substitution M rho rho old new (CEvar 5) (CEvar 7)).
  { intros f g H H';change(f=theta) in H;change(g=theta') in H';now subst f g. }
  assert (HB':expression_binder_absent M rho old (CEvar 5)).
  { intros f H;change (f=theta) in H;now subst f. }
  assert (HF':expression_fresh M rho new (CEvar 5)).
  { intros f H;change (f=theta) in H;now subst f. }
  assert (HD:expression_fresh M rho new (E_wel (CEvar 0) (CEvar 4))).
  { apply expression_fresh_atom;[now left|now intros ? ->|now intros ? ->]. }
  assert (HM:expression_fresh M rho new (E_wel (CEvar 4) (CEvar 2))).
  { apply expression_fresh_atom;[now left|now intros ? ->|now intros ? ->]. }
  assert (EA:expression_equivalent M rho
    (E_wex (CEvar 4) (E_wa (E_wel (CEvar 0) (CEvar 4)) (CEvar 5)))
    (E_wex (CEvar 6) (E_wa (E_wel (CEvar 0) (CEvar 6)) (CEvar 7)))).
  { apply (expression_exists_alpha_capture_free M rho (CEvar 4) (CEvar 6) _ _ old new eq_refl eq_refl H0 H1 Hxy).
    - apply expression_binder_absent_conjunction;[apply expression_binder_absent_atom;now left|exact HB'].
    - now apply expression_fresh_conjunction.
    - apply expression_ns_conjunction;[exact H0| |exact RS].
      exact (expression_ns_atom M rho rho old new false _ _ _ _ R0 RX). }
  assert (EB:expression_equivalent M rho
    (E_wex (CEvar 4) (E_wa (E_wel (CEvar 0) (CEvar 4)) (E_wa (E_wel (CEvar 4) (CEvar 2)) (CEvar 5))))
    (E_wex (CEvar 6) (E_wa (E_wel (CEvar 0) (CEvar 6)) (E_wa (E_wel (CEvar 6) (CEvar 2)) (CEvar 7))))).
  { apply (expression_exists_alpha_capture_free M rho (CEvar 4) (CEvar 6) _ _ old new eq_refl eq_refl H0 H1 Hxy).
    - apply expression_binder_absent_conjunction;[apply expression_binder_absent_atom;now left|].
      apply expression_binder_absent_conjunction;[apply expression_binder_absent_atom;now left|exact HB'].
    - apply expression_fresh_conjunction;[exact H1|exact HD|]. now apply expression_fresh_conjunction.
    - apply expression_ns_conjunction;[exact H0| |].
      + exact (expression_ns_atom M rho rho old new false _ _ _ _ R0 RX).
      + apply expression_ns_conjunction;[exact H0| |exact RS].
        exact (expression_ns_atom M rho rho old new false _ _ _ _ RX R2). }
  apply (proj1 (numerical_equivalent_expression M rho
    (E_wal (CEvar 3) (E_raw_collection_coverage (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)))
    (E_wal (CEvar 3) (E_raw_collection_coverage (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 6) (CEvar 7)))
    all all' G G')).
  apply expression_equivalent_all. unfold E_raw_collection_coverage.
  apply expression_equivalent_implication;[apply expression_equivalent_refl|].
  now apply expression_equivalent_implication.
Qed.

Print Assumptions raw_coverage_inner_alpha.

