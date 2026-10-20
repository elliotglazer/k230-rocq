(** Exact outer witness in the literal quotient membership template.
    The deqv argument order is the selected element followed by its
    representative; its own private binders start one name higher. *)
From PAModel Require Import Model Arithmetic CodeExpressions ProofTemplates
  QuotientAtomTemplates QuotationPayloads QuotientSeparationWitness.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition E_member_witness t x y w :=
  E_wex w (E_selection_witness (E_wel t w) (E_wel w y)
    (code_subst (quotation_atom_parameters x w t (CEadd w (CEconst 1)) (CEconst 0))
      quotient_equal_template)).

Theorem quotient_member_template_expansion :
  quotient_member_template = E_member_witness (CEvar 2) (CEvar 0) (CEvar 1) (CEvar 3).
Proof. reflexivity. Qed.

Theorem member_witness_atom_graph M env T X Y W t x y w result :
  code_relation M env T t -> code_relation M env X x ->
  code_relation M env Y y -> code_relation M env W w ->
  (code_relation M env (E_member_witness T X Y W) result <->
   quotation_atom M false x y t w result).
Proof.
  intros HT HX HY HW. unfold quotation_atom,quotation_atom_expression.
  change (code_relation M env
    (code_subst (quotation_atom_parameters X Y T W (CEconst 0)) quotient_member_template) result <->
    code_relation M (quotation_atom_parameters x y t w (zeroM M)) quotient_member_template result).
  apply code_subst_graph. intros [|[|[|[|i]]]];[exact HX|exact HY|exact HT|exact HW|reflexivity].
Qed.

Theorem member_witness_equality_graph M env T X W t x w result :
  code_relation M env T t -> code_relation M env X x -> code_relation M env W w ->
  (code_relation M env
    (code_subst (quotation_atom_parameters X W T (CEadd W (CEconst 1)) (CEconst 0))
      quotient_equal_template) result <->
   quotation_atom M true x w t (succM M w) result).
Proof.
  intros HT HX HW. unfold quotation_atom,quotation_atom_expression.
  apply code_subst_graph. intros [|[|[|[|i]]]];[exact HX|exact HW|exact HT| |reflexivity].
  exists w,(code_numeral M 1). split;[exact HW|]. split;[reflexivity|].
  cbn [code_numeral]. apply succ_as_add.
Qed.

Print Assumptions quotient_member_template_expansion.
Print Assumptions member_witness_atom_graph.
Print Assumptions member_witness_equality_graph.
