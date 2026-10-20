(** The finite substitution square for the one-parameter induction macro.
    Normalize only the variable maps, independently of any proof context. *)
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
#[local] Existing Instance falsity_on | 0.

Theorem full_PA_parameter_specialization_square (guard phi : form) :
 (((guard[up ↑] → phi[$1 .: $0 .: (S >> S >> var)])[up (up ↑)][up (up ↑)][up ($0..)])[$1..])
   = (guard[↑] → phi).
Proof.
 cbn [subst_form]. f_equal.
 - rewrite !subst_comp. apply subst_ext. intros [|n]; reflexivity.
 - rewrite !subst_comp. apply subst_id. intros [|[|n]]; reflexivity.
Qed.

Print Assumptions full_PA_parameter_specialization_square.
