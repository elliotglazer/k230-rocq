(** Classical completeness for the exact native-equality PA Model record.
    This is assembled from the concrete term countermodel, same-carrier
    full/fragment bridge, and canonical equality quotient. *)
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Logic.Classical_Prop.
From PAModel Require Import Model PAEqualityQuotient PAFullFragmentTheory
 FullPAClosure FullFragmentSyntax FullFragmentSemantics
 PACountermodel PATermEnumeration.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.
#[local] Existing Instance falsity_on |0.
#[local] Existing Instance class |0.
Theorem full_PA_closed_validity_derivability (phi:form):
 closed phi->(forall(M:Model)rho,holds M rho phi)->FullND.tprv full_PA_closed_axiom phi.
Proof.
 intros Hclosed Hvalid. apply NNPP. intro Hnot.
 assert(Hfragment:~@CountermodelND.tprv PA_funcs_signature PA_preds_signature
  falsity_on class fragment_PA_closed_axiom(full_to_fragment phi)).
 {intro Hproof. apply Hnot,fragment_PA_proof_to_closed,Hproof. }
 destruct(@pa_closed_fragment_term_countermodel_not
  fragment_PA_closed_axiom(full_to_fragment phi)fragment_PA_closed_theory
  (full_to_fragment_closed Hclosed)Hfragment)as(I&HT&Hfalse).
 pose proof(proj1(fragment_PA_closed_models I)HT)as HPA.
 destruct(countable_PAeq_native_model (@term PA_funcs_signature)(fragment_full_interp I)
  pa_term_enumerate pa_term_enumerate_surjective HPA)as(M&project&represent&Hrel&Hsection&Hsat).
 apply Hfalse. apply(proj2(full_to_fragment_semantics I phi var)).
 apply(proj2(Hsat phi var(fun n=>project(var n))(fun n=>eq_refl))).
 apply Hvalid.
Qed.
Print Assumptions full_PA_closed_validity_derivability.
