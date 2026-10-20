(** Output constructors for de Bruijn renaming.  The t and k arguments
    are inert here; they match the seven-field recursive record interface. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition renaming_source_atom (b : bool) := if b then SFEqual else SFMember.
Definition renaming_source_quantifier (b : bool) := if b then SFAll else SFEx.
Definition renaming_atom M equality x y (t k : carrier M) v :=
  sf_relation M (renaming_source_atom equality) x y v.
Definition renaming_atom_formula equality (x y t k v : term) :=
  sf_formula (renaming_source_atom equality) x y v.
Lemma renaming_atom_formula_correct M rho equality x y t k v :
  holds M rho (renaming_atom_formula equality x y t k v) <->
  renaming_atom M equality (evalM M rho x) (evalM M rho y) (evalM M rho t) (evalM M rho k) (evalM M rho v).
Proof. apply sf_formula_correct. Qed.
Lemma renaming_atom_total M equality x y t k : exists v, renaming_atom M equality x y t k v.
Proof. apply sf_relation_total. Qed.
Lemma renaming_atom_functional M equality x y t k v w :
  renaming_atom M equality x y t k v -> renaming_atom M equality x y t k w -> v=w.
Proof. apply sf_relation_functional. Qed.
Definition renaming_binary := sf_relation.
Definition renaming_binary_formula := sf_formula.
Definition renaming_binary_formula_correct := sf_formula_correct.
Definition renaming_binary_total := sf_relation_total.
Definition renaming_binary_functional := sf_relation_functional.
Definition renaming_quantifier M universal (k t : carrier M) x v :=
  sf_relation M (renaming_source_quantifier universal) x (zeroM M) v.
Definition renaming_quantifier_formula universal (k t x v : term) :=
  sf_formula (renaming_source_quantifier universal) x zero v.
Lemma renaming_quantifier_formula_correct M rho universal k t x v :
  holds M rho (renaming_quantifier_formula universal k t x v) <->
  renaming_quantifier M universal (evalM M rho k) (evalM M rho t) (evalM M rho x) (evalM M rho v).
Proof. apply sf_formula_correct. Qed.
Lemma renaming_quantifier_total M universal k t x : exists v, renaming_quantifier M universal k t x v.
Proof. apply sf_relation_total. Qed.
Lemma renaming_quantifier_functional M universal k t x v w :
  renaming_quantifier M universal k t x v -> renaming_quantifier M universal k t x w -> v=w.
Proof. apply sf_relation_functional. Qed.
