(** Exact syntactic conservativity of the universally closed PAeq theory. *)
From FOL Require Import FullSyntax Arithmetics Theories.
From Stdlib Require Import Lists.List.
From PAModel Require Import FullPAClosure FullPAAxiomGeneralization FullPATheoryGeneralization.
Import ListNotations FullSyntax.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
#[local] Existing Instance falsity_on | 0.
#[local] Existing Instance class | 0.
Theorem full_PA_closed_proof_to_open phi:
 FullND.tprv full_PA_closed_axiom phi ->FullND.tprv PAeq phi.
Proof.
 intros(A&HA&P). apply(full_theory_cut PAeq A phi P).
 intros ax Hax. destruct(HA ax Hax)as(n&original&HOriginal&HBound&->).
 apply full_PA_generalize_prefix,full_PA_axiom_proof,HOriginal.
Qed.
Theorem full_PA_closed_proof_iff phi:
 FullND.tprv full_PA_closed_axiom phi <->FullND.tprv PAeq phi.
Proof. split;[apply full_PA_closed_proof_to_open|apply full_PA_proof_to_closed]. Qed.
Print Assumptions full_PA_closed_proof_to_open.
Print Assumptions full_PA_closed_proof_iff.
