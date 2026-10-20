(** Capture-free alpha conversion lifted directly to finite code expressions.
    The body may be a nonstandard source quotation in an opaque expression leaf. *)
From PAModel Require Import Model FiniteCoding CodeDescent CodeExpressions NumericalProofs
  NumericalEquivalence NumericalVacuitySteps NamedBinderFresh FreshNames
  TemplateBinderFresh TemplateFormulaFresh TemplateNamedSubstitution NamedExistential
  NamedAlpha RawCollectionRenaming RawClauseAlpha.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem expression_exists_alpha_capture_free M rho X Y A B x y :
  code_relation M rho X x -> code_relation M rho Y y ->
  x<>zeroM M -> y<>zeroM M -> x<>y ->
  expression_binder_absent M rho x A -> expression_fresh M rho y A ->
  expression_named_substitution M rho rho x y A B ->
  expression_equivalent M rho (E_wex X A) (E_wex Y B).
Proof.
  intros HX HY H0 H1 Hxy HA HF HS.
  destruct (code_relation_total M (E_wex X A) rho) as [exA GA].
  destruct (code_relation_total M (E_wex Y B) rho) as [exB GB].
  apply (proj2 (numerical_equivalent_expression M rho _ _ exA exB GA GB)).
  destruct (code_relation_total M A rho) as [a Ga].
  destruct (code_relation_total M B rho) as [b Gb].
  exact (numerical_named_exists_alpha_equivalence_checked M a x y b exA exB
    H0 H1 Hxy (HA a Ga) (HF a Ga) (HS a b Ga Gb)
    (proj1 (named_exists_expression M rho X A x a exA HX Ga) GA)
    (proj1 (named_exists_expression M rho Y B y b exB HY Gb) GB)).
Qed.

Theorem expression_all_alpha_capture_free M rho X Y A B x y :
  code_relation M rho X x -> code_relation M rho Y y -> x<>y ->
  expression_binder_absent M rho x A -> expression_fresh M rho y A ->
  expression_named_substitution M rho rho x y A B ->
  expression_equivalent M rho (E_wal X A) (E_wal Y B).
Proof.
  intros HX HY Hxy HA HF HS.
  destruct (code_relation_total M (E_wal X A) rho) as [allA GA].
  destruct (code_relation_total M (E_wal Y B) rho) as [allB GB].
  apply (proj2 (numerical_equivalent_expression M rho _ _ allA allB GA GB)).
  destruct (code_relation_total M A rho) as [a Ga].
  destruct (code_relation_total M B rho) as [b Gb].
  exact (numerical_named_all_alpha_equivalence_checked M a x y b allA allB
    Hxy (HA a Ga) (HF a Ga) (HS a b Ga Gb)
    (proj1 (expression_universal_iff M rho X A x a allA HX Ga) GA)
    (proj1 (expression_universal_iff M rho Y B y b allB HY Gb) GB)).
Qed.

Print Assumptions expression_exists_alpha_capture_free.
Print Assumptions expression_all_alpha_capture_free.


