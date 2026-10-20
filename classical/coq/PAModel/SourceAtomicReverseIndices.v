(** Reverse-index witnesses are internal PA elements, not externally
    enumerated finite indices. The source assignment position i corresponds
    to the numeral k determined by length n=succ(k+i). *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature|0.
#[local] Existing Instance PA_preds_signature|0.
Definition source_reverse_index M n i k:=n=succM M(addM M k i).
Definition source_reverse_index_formula(n i k:term):form:=n==σ(k⊕i).
Theorem source_reverse_index_formula_correct M rho n i k:
 holds M rho(source_reverse_index_formula n i k)<->
 source_reverse_index M(evalM M rho n)(evalM M rho i)(evalM M rho k).
Proof. reflexivity. Qed.
Theorem source_reverse_index_exists M n i:coding_lt M i n->exists k,source_reverse_index M n i k.
Proof. intros(k&HK). exists k. unfold source_reverse_index. rewrite(coding_add_comm M k i). exact HK. Qed.
Theorem source_reverse_index_unique M n i k l:
 source_reverse_index M n i k->source_reverse_index M n i l->k=l.
Proof.
 intros HK HL. unfold source_reverse_index in HK,HL. apply(Arithmetic.add_cancel M k l i),succ_injective.
 exact(eq_trans(eq_sym HK)HL).
Qed.
Theorem source_reverse_index_lt M n i k:source_reverse_index M n i k->coding_lt M i n.
Proof. intro H. exists k. unfold source_reverse_index in H. rewrite(coding_add_comm M i k). exact H. Qed.
Print Assumptions source_reverse_index_formula_correct.
Print Assumptions source_reverse_index_exists.
Print Assumptions source_reverse_index_unique.
