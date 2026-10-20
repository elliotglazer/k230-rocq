(** One genuine parameter-generalization step for the PA induction schema.
    The stronger induction predicate quantifies the parameter together with
    its own base/step hypotheses. All other parameters remain free. *)
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
From PAModel Require Import FullPAParameterSquare.
Import ListNotations FullSyntax.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
#[local] Existing Instance falsity_on | 0.
#[local] Existing Instance class | 0.
Definition full_PA_induction_step(phi:form):form :=∀(phi→phi[σ $0 .: S >> var]).
Definition full_PA_induction_guard(phi:form):form :=phi[zero..]∧full_PA_induction_step phi.
Definition full_PA_parameter_swap :nat->term :=$1 .: $0 .: (S >> S >> var).
Definition full_PA_strengthened(phi:form):form :=
 ∀((full_PA_induction_guard phi)[up ↑]→phi[full_PA_parameter_swap]).
Lemma full_PA_strengthened_base phi:
 @FullND.prv PA_funcs_signature PA_preds_signature falsity_on class (@nil form)((full_PA_strengthened phi)[zero..]).
Proof.
 unfold full_PA_strengthened,full_PA_parameter_swap,full_PA_induction_guard,full_PA_induction_step.
 cbn. asimpl. apply AllI,II. eapply CE1. apply Ctx. now left.
Qed.
Lemma full_PA_strengthened_step phi:
 @FullND.prv PA_funcs_signature PA_preds_signature falsity_on class (@nil form)(full_PA_induction_step(full_PA_strengthened phi)).
Proof.
 unfold full_PA_induction_step at 1. apply AllI,II.
 unfold full_PA_strengthened. cbn. apply AllI,II. cbn.
 match goal with |- @FullND.prv _ _ _ _ (?guard::?previous::?A) _ =>
   assert(HGuard:FullND.prv(guard::previous::A)guard)by(apply Ctx;now left);
   assert(HPrevious:FullND.prv(guard::previous::A)previous)by(apply Ctx;right;now left);
   pose proof(CE2 HGuard)as HStep;
   pose proof(AllE(var 1)HStep)as HUse;
   pose proof(AllE(var 0)HPrevious)as HBefore
 end.
 unfold full_PA_strengthened,full_PA_parameter_swap,full_PA_induction_guard,full_PA_induction_step in *.
 cbn in *. asimpl in HUse. asimpl in HBefore. asimpl.
 eapply IE;[exact HUse|]. eapply IE;[exact HBefore|]. apply Ctx. now left.
Qed.
Lemma full_PA_strengthened_conclusion phi:
 @FullND.prv PA_funcs_signature PA_preds_signature falsity_on class
  (ax_induction(full_PA_strengthened phi)::nil)(∀full_PA_strengthened phi).
Proof.
 eapply IE.
 - eapply IE.
   + apply Ctx. now left.
   + apply(FullNDFacts.Weak(full_PA_strengthened_base phi)). intros f H;inversion H.
 - apply(FullNDFacts.Weak(full_PA_strengthened_step phi)). intros f H;inversion H.
Qed.
Lemma full_PA_parameter_conclusion(A:list form)(phi:form):
 FullND.prv A(∀full_PA_strengthened phi) ->FullND.prv A(∀ax_induction phi).
Proof.
 intro P. apply AllI. unfold ax_induction at 1. apply II,II,AllI. cbn.
 pose proof(FullNDFacts.subst_Weak ↑(FullNDFacts.subst_Weak ↑ P))as HAll.
 pose proof(AllE(var 0)HAll)as HX.
 pose proof(AllE(var 1)HX)as HPoint.
 change(FullND.prv(map(subst_form ↑)(map(subst_form ↑)A))
  ((((full_PA_induction_guard phi)[up ↑]→phi[$1 .: $0 .: (S >> S >> var)])
    [up(up ↑)][up(up ↑)][up($0..)])[$1..]))in HPoint.
 rewrite(full_PA_parameter_specialization_square(full_PA_induction_guard phi)phi)in HPoint.
 eapply IE.
 - apply(FullNDFacts.Weak HPoint). intros f H. right;right;exact H.
 - apply CI.
   + apply Ctx. right;now left.
   + apply Ctx. now left.
Qed.
Theorem full_PA_induction_parameter_closure phi:
 @FullND.prv PA_funcs_signature PA_preds_signature falsity_on class
  (ax_induction(full_PA_strengthened phi)::nil)(∀ax_induction phi).
Proof. apply full_PA_parameter_conclusion,full_PA_strengthened_conclusion. Qed.
Print Assumptions full_PA_strengthened_base.
Print Assumptions full_PA_strengthened_step.
Print Assumptions full_PA_induction_parameter_closure.
