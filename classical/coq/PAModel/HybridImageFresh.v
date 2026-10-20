(** Strong syntactic freshness of hybrid image predicates. *)
From PAModel Require Import Model FiniteCoding FreshNames QuotationFormulaFresh
  TemplateFormulaFresh ContextualGuardedQuantifiers HybridImageGraphs BinaryMatrixFresh BinaryMatrixRenaming.
Unset Implicit Arguments.

Theorem hybrid_image_formula_fresh M phi eb ec en t a y x atomBase matrixBase image name :
  hybrid_image_graph M phi eb ec en t a y x atomBase matrixBase image ->
  name<>zeroM M -> x<>name -> t<>name -> a<>name -> y<>name ->
  coding_lt M name atomBase -> coding_lt M name matrixBase ->
  environment_avoids_name M eb ec en name -> formula_fresh M image name.
Proof.
  intros [q [theta [dom [rest [body [GQ [GT [GD [GR [GB GI]]]]]]]]]]
    H0 HX HT HA HY HAname HMname HE.
  apply (quotation_quantifier_fresh M false x t rest image name);try assumption.
  - exact (proj2 (quotation_guarded_exists_graph M x t rest dom body image GD GB) GI).
  - apply (quotation_binary_fresh M SetFormulaCodes.SFAnd q theta rest name GR H0).
    + exact (quotation_atom_fresh M false x a t atomBase q name GQ HAname H0 HX HA HT).
    + exact (binary_matrix_formula_fresh M phi eb ec en x y matrixBase t theta name
        GT HMname H0 ltac:(congruence) HX HY HE).
Qed.

Print Assumptions hybrid_image_formula_fresh.

