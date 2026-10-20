(** Actual PAeq proof existence for every closed formula valid in PA models. *)
From FOL Require Import FullSyntax Arithmetics.
From PAModel Require Import Model FullPAClosureEquivalence PAClosedValidityDerivability.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.
#[local] Existing Instance falsity_on |0.
#[local] Existing Instance class |0.
Theorem full_PAeq_validity_derivability(phi:form):
 closed phi->(forall(M:Model)rho,holds M rho phi)->FullND.tprv PAeq phi.
Proof.
 intros Hclosed Hvalid. apply full_PA_closed_proof_to_open.
 now apply full_PA_closed_validity_derivability.
Qed.
Print Assumptions full_PAeq_validity_derivability.
