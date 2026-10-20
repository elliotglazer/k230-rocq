(** Universal closure of the actual PAeq schema, with open parameters retained explicitly. *)
From FOL Require Import FullSyntax Arithmetics Theories.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations FullSyntax.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
#[local] Existing Instance falsity_on | 0.
#[local] Existing Instance class | 0.
Definition full_PA_closed_axiom(closedax:form):Prop :=
 exists n ax,PAeq ax /\bounded n ax /\closedax=forall_times n ax.
Lemma full_forall_times_successor n(ax:form):forall_times(S n)ax=forall_times n(∀ax).
Proof. unfold forall_times. cbn[iter]. apply iter_switch. Qed.
Lemma full_universal_closure_closed n(ax:form):bounded n ax ->closed(forall_times n ax).
Proof.
 revert ax. induction n as[|n IH];intros ax HB.
 - exact HB.
 - rewrite full_forall_times_successor. apply IH. now constructor.
Qed.
Theorem full_PA_closed_theory:closed_T full_PA_closed_axiom.
Proof. intros theta(n&ax&HA&HB&->). now apply full_universal_closure_closed. Qed.
Lemma full_universal_closure_valid {D:Type}(I:interp D)n(ax:form):
 (forall rho,sat I rho(forall_times n ax)) <->(forall rho,sat I rho ax).
Proof.
 revert ax. induction n as[|n IH];intro ax;[reflexivity|].
 rewrite full_forall_times_successor,IH.
 split.
 - intros H rho. specialize(H(fun j : nat => rho (S j))(rho 0)).
   apply(@sat_ext PA_funcs_signature PA_preds_signature D I falsity_on (rho 0 .:(fun j : nat => rho (S j)))rho ax)in H;[exact H|].
   intros[|i];reflexivity.
 - intros H rho x. apply H.
Qed.
Theorem full_PA_closed_semantics {D:Type}(I:interp D):
 (forall theta rho,full_PA_closed_axiom theta ->sat I rho theta) <->
 (forall ax rho,PAeq ax ->sat I rho ax).
Proof.
 split.
 - intros H ax rho HA. destruct(find_bounded ax)as[n HB].
   assert(HC:forall xi,sat I xi(forall_times n ax)).
   { intro xi. apply H. exists n,ax. auto. }
   exact(proj1(full_universal_closure_valid I n ax)HC rho).
 - intros H theta rho(n&ax&HA&HB&->).
   exact(proj2(full_universal_closure_valid I n ax)(fun xi => H ax xi HA)rho).
Qed.
Definition full_PA_close_formula(ax:form):form :=forall_times(proj1_sig(find_bounded ax))ax.
Lemma full_PA_close_formula_axiom ax:PAeq ax ->full_PA_closed_axiom(full_PA_close_formula ax).
Proof.
 intro HA. unfold full_PA_close_formula. exists(proj1_sig(find_bounded ax)),ax.
 split;[exact HA|]. split;[apply proj2_sig|reflexivity].
Qed.
Theorem full_PA_proof_to_closed phi:
 FullND.tprv PAeq phi ->FullND.tprv full_PA_closed_axiom phi.
Proof.
 intros(A&HA&P). exists(map full_PA_close_formula A). split.
 - intros theta H. apply in_map_iff in H as(ax&<-&Hax). now apply full_PA_close_formula_axiom,HA.
 - apply(FullNDFacts.prv_cut P). intros ax Hax.
   pose proof(FullND.Ctx (A:=map full_PA_close_formula A)(phi:=full_PA_close_formula ax)
    (in_map full_PA_close_formula A ax Hax))as PC.
   pose proof(FullNDFacts.subst_forall_prv PC(proj2_sig(find_bounded ax))var)as PA.
   now rewrite subst_id in PA.
Qed.
Print Assumptions full_PA_closed_theory.
Print Assumptions full_PA_closed_semantics.
Print Assumptions full_PA_proof_to_closed.
