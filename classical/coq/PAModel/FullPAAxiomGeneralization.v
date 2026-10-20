(** Genuine PAeq parameter generalization through a stronger induction axiom. *)
From FOL Require Import FullSyntax Arithmetics Theories.
From Stdlib Require Import Lists.List.
From PAModel Require Import FullPAClosure FullPAFiniteAxioms FullPAParameterInduction FullPATheoryGeneralization.
Import ListNotations FullSyntax.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
#[local] Existing Instance falsity_on | 0.
#[local] Existing Instance class | 0.
Lemma full_PA_axiom_proof ax:PAeq ax ->FullND.tprv PAeq ax.
Proof.
 intro H. exists(ax::nil). split.
 - intros f [<-|HF];[exact H|inversion HF].
 - apply Ctx. now left.
Qed.
Theorem full_PA_axiom_generalize ax:PAeq ax ->FullND.tprv PAeq(∀ax).
Proof.
 intro H. destruct H as[ax HF| | |phi].
 - exists(ax::nil). split.
   + intros f [<-|H];[now constructor|inversion H].
   + apply full_closed_formula_generalize. now apply full_PA_FAeq_closed.
 - exists(ax_zero_succ::nil). split.
   + intros f [<-|H];[apply PAeq_discr|inversion H].
   + apply full_closed_formula_generalize,full_PA_zero_succ_closed.
 - exists(ax_succ_inj::nil). split.
   + intros f [<-|H];[apply PAeq_inj|inversion H].
   + apply full_closed_formula_generalize,full_PA_succ_inj_closed.
 - exists(ax_induction(full_PA_strengthened phi)::nil). split.
   + intros f [<-|H];[apply PAeq_induction|inversion H].
   + apply full_PA_induction_parameter_closure.
Qed.
Theorem full_PA_generalize phi:
 FullND.tprv PAeq phi ->FullND.tprv PAeq(∀phi).
Proof. apply(full_theory_generalize_from_axioms PAeq phi full_PA_axiom_generalize). Qed.
Theorem full_PA_generalize_prefix n phi:
 FullND.tprv PAeq phi ->FullND.tprv PAeq(forall_times n phi).
Proof.
 revert phi. induction n as[|n IH];intros phi P;[exact P|].
 rewrite full_forall_times_successor. apply IH,full_PA_generalize,P.
Qed.
Print Assumptions full_PA_axiom_generalize.
Print Assumptions full_PA_generalize.
Print Assumptions full_PA_generalize_prefix.
