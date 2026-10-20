(** Extract the free role names from a fresh raw membership atom. *)
From PAModel Require Import Model CodeExpressions CodeDescent NumericalProofs
  FreshNames FreshPropagation TemplateFormulaFresh TemplateBinderFresh.
Unset Implicit Arguments.

Lemma expression_fresh_membership_names M rho name A B :
  expression_fresh M rho name (E_wel A B) ->
  expression_name_avoids M rho name A /\ expression_name_avoids M rho name B.
Proof.
  intro HF. split.
  - intros a HA. destruct (code_relation_total M B rho) as [b HB].
    destruct (code_relation_total M (E_wel A B) rho) as [f Hf].
    exact (proj1 (formula_fresh_membership M a b f name
      (expression_tagged_graph M rho 1 A B a b f HA HB Hf) (HF f Hf))).
  - intros b HB. destruct (code_relation_total M A rho) as [a HA].
    destruct (code_relation_total M (E_wel A B) rho) as [f Hf].
    exact (proj2 (formula_fresh_membership M a b f name
      (expression_tagged_graph M rho 1 A B a b f HA HB Hf) (HF f Hf))).
Qed.

Print Assumptions expression_fresh_membership_names.
