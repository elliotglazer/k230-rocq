(** Finite output templates for the full-source quotient translation.
    Falsity will translate to code 1. Atoms are the audited tagged-quotient
    templates, and quantifiers receive the explicit domain guard. This file
    describes the output constructors, not the recursive source translation. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs SetFormulaCodes QuotientAtomTemplates SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition quotation_atom_expression (equality : bool) : code_expr :=
  if equality then quotient_equal_template else quotient_member_template.
Definition quotation_atom_parameters {A} (x y t k z : A) : nat -> A :=
  x .: y .: t .: k .: fun _ => z.
Definition quotation_atom M equality x y t k v :=
  code_relation M (quotation_atom_parameters x y t k (zeroM M))
    (quotation_atom_expression equality) v.
Definition quotation_atom_formula equality (x y t k v : term) : form :=
  code_formula (quotation_atom_expression equality)
    (quotation_atom_parameters x y t k zero) v.

Lemma quotation_atom_formula_correct M rho equality x y t k v :
  holds M rho (quotation_atom_formula equality x y t k v) <->
  quotation_atom M equality (evalM M rho x) (evalM M rho y)
    (evalM M rho t) (evalM M rho k) (evalM M rho v).
Proof.
  unfold quotation_atom_formula,quotation_atom. rewrite code_formula_correct.
  apply code_relation_ext. intros [|[|[|[|i]]]]; reflexivity.
Qed.
Lemma quotation_atom_total M equality x y t k :
  exists v, quotation_atom M equality x y t k v.
Proof. apply code_relation_total. Qed.
Lemma quotation_atom_functional M equality x y t k v w :
  quotation_atom M equality x y t k v -> quotation_atom M equality x y t k w -> v=w.
Proof. apply code_relation_functional. Qed.

Definition quotation_binary_expression (h : sf_head) : code_expr :=
  match h with
  | SFAnd => E_wa (CEvar 0) (CEvar 1)
  | SFOr => E_or (CEvar 0) (CEvar 1)
  | _ => E_wim (CEvar 0) (CEvar 1)
  end.
Definition quotation_binary M h x y v :=
  code_relation M (x .: y .: fun _ => zeroM M) (quotation_binary_expression h) v.
Definition quotation_binary_formula h (x y v : term) : form :=
  code_formula (quotation_binary_expression h) (x .: y .: fun _ => zero) v.

Lemma quotation_binary_formula_correct M rho h x y v :
  holds M rho (quotation_binary_formula h x y v) <->
  quotation_binary M h (evalM M rho x) (evalM M rho y) (evalM M rho v).
Proof.
  unfold quotation_binary_formula,quotation_binary. rewrite code_formula_correct.
  apply code_relation_ext. intros [|[|i]]; reflexivity.
Qed.
Lemma quotation_binary_total M h x y : exists v, quotation_binary M h x y v.
Proof. apply code_relation_total. Qed.
Lemma quotation_binary_functional M h x y v w :
  quotation_binary M h x y v -> quotation_binary M h x y w -> v=w.
Proof. apply code_relation_functional. Qed.

Definition quotation_quantifier_expression (universal : bool) : code_expr :=
  if universal then
    E_wal (CEvar 0) (E_wim (E_wel (CEvar 1) (CEvar 0)) (CEvar 2))
  else E_wex (CEvar 0) (E_wa (E_wel (CEvar 1) (CEvar 0)) (CEvar 2)).
Definition quotation_quantifier M universal k t x v :=
  code_relation M (k .: t .: x .: fun _ => zeroM M)
    (quotation_quantifier_expression universal) v.
Definition quotation_quantifier_formula universal (k t x v : term) : form :=
  code_formula (quotation_quantifier_expression universal)
    (k .: t .: x .: fun _ => zero) v.

Lemma quotation_quantifier_formula_correct M rho universal k t x v :
  holds M rho (quotation_quantifier_formula universal k t x v) <->
  quotation_quantifier M universal (evalM M rho k) (evalM M rho t)
    (evalM M rho x) (evalM M rho v).
Proof.
  unfold quotation_quantifier_formula,quotation_quantifier. rewrite code_formula_correct.
  apply code_relation_ext. intros [|[|[|i]]]; reflexivity.
Qed.
Lemma quotation_quantifier_total M universal k t x :
  exists v, quotation_quantifier M universal k t x v.
Proof. apply code_relation_total. Qed.
Lemma quotation_quantifier_functional M universal k t x v w :
  quotation_quantifier M universal k t x v -> quotation_quantifier M universal k t x w -> v=w.
Proof. apply code_relation_functional. Qed.

Lemma quotation_atom_formula_bound equality :
  bounded 5 (quotation_atom_formula equality $0 $1 $2 $3 $4).
Proof. destruct equality; apply formula_boundb_sound; vm_compute; reflexivity. Qed.
Lemma quotation_binary_formula_bound h :
  bounded 3 (quotation_binary_formula h $0 $1 $2).
Proof. destruct h; apply formula_boundb_sound; vm_compute; reflexivity. Qed.
Lemma quotation_quantifier_formula_bound universal :
  bounded 4 (quotation_quantifier_formula universal $0 $1 $2 $3).
Proof. destruct universal; apply formula_boundb_sound; vm_compute; reflexivity. Qed.

Print Assumptions quotation_atom_formula_correct.
Print Assumptions quotation_atom_total.
Print Assumptions quotation_atom_functional.
Print Assumptions quotation_quantifier_formula_correct.
Print Assumptions quotation_quantifier_total.
Print Assumptions quotation_quantifier_functional.
