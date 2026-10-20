(** The exact closed PA schema translated to the classical universal fragment. *)
From PAModel Require Import FullPAClosure FullFragmentSyntax FullFragmentSemantics FullFragmentProofReturn.
From FOL Require Import FullSyntax Arithmetics Theories.
From Undecidability.FOL.Deduction Require FragmentND.
Set Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.
#[local] Existing Instance falsity_on |0.
#[local] Existing Instance class |0.
Definition fragment_PA_closed_axiom(theta:@form PA_funcs_signature PA_preds_signature FragmentSyntax.frag_operators falsity_on):Prop :=
 full_fragment_theory full_PA_closed_axiom theta.
Theorem fragment_PA_closed_theory:
 @closed_T PA_funcs_signature PA_preds_signature FragmentSyntax.frag_operators falsity_on fragment_PA_closed_axiom.
Proof. intros theta H. eapply full_fragment_closed_theory;[apply full_PA_closed_theory|exact H]. Qed.
Theorem fragment_PA_closed_models {D:Type}(I:@FragSem.interp PA_funcs_signature PA_preds_signature D):
 (forall theta rho,fragment_PA_closed_axiom theta->FragSem.sat I rho theta)<->
 (forall ax rho,PAeq ax->FullSem.sat(fragment_full_interp I)rho ax).
Proof.
 unfold fragment_PA_closed_axiom.
 rewrite fragment_full_theory_semantics. apply full_PA_closed_semantics.
Qed.
Theorem fragment_PA_proof_to_closed(phi:@form PA_funcs_signature PA_preds_signature FullSyntax.full_operators falsity_on):
 @FragmentND.tprv PA_funcs_signature PA_preds_signature falsity_on class fragment_PA_closed_axiom(full_to_fragment phi)->
 @FullND.tprv PA_funcs_signature PA_preds_signature falsity_on class full_PA_closed_axiom phi.
Proof. apply fragment_translated_proof_return. Qed.
Print Assumptions fragment_PA_closed_theory.
Print Assumptions fragment_PA_closed_models.
Print Assumptions fragment_PA_proof_to_closed.
