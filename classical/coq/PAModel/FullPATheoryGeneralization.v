(** Finite FullND theory cut and genuine generalization from proved
    universally quantified axiom instances. No arbitrary theory AllI is assumed. *)
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import ListNotations FullSyntax.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
#[local] Existing Instance falsity_on | 0.
#[local] Existing Instance class | 0.
Lemma full_theory_modus_ponens(T:form->Prop)(phi psi:form):
 FullND.tprv T(phi→psi) ->FullND.tprv T phi ->FullND.tprv T psi.
Proof.
 intros(A&HA&PA)(B&HB&PB). exists(A++B). split.
 - intros ax H. apply in_app_or in H as[H|H];[exact(HA ax H)|exact(HB ax H)].
 - eapply IE.
   + apply(FullNDFacts.Weak PA). intros ax H. apply in_or_app. now left.
   + apply(FullNDFacts.Weak PB). intros ax H. apply in_or_app. now right.
Qed.
Lemma full_theory_cut(T:form->Prop)(A:list form)(phi:form):
 FullND.prv A phi ->(forall ax,In ax A ->FullND.tprv T ax) ->FullND.tprv T phi.
Proof.
 revert phi. induction A as[|ax A IH];intros phi P H.
 - exists nil. split;[intros f HF;inversion HF|exact P].
 - apply(full_theory_modus_ponens T ax phi).
   + apply IH;[now apply II|]. intros f HF. apply H. now right.
   + apply H. now left.
Qed.
Lemma full_prefix_generalize_context(A:list form)(phi:form):
 FullND.prv A phi ->FullND.prv(map(fun ax=>∀ax)A)(∀phi).
Proof.
 intro P. apply AllI. apply(FullNDFacts.prv_cut P). intros ax Hax.
 assert(HMember:In((∀ax)[↑])(map(subst_form ↑)(map(fun f=>∀f)A))).
 { apply in_map. now apply in_map. }
 pose proof(AllE(var 0)(Ctx HMember))as H. asimpl in H. exact H.
Qed.
Theorem full_theory_generalize_from_axioms(T:form->Prop)(phi:form):
 (forall ax,T ax ->FullND.tprv T(∀ax)) ->FullND.tprv T phi ->FullND.tprv T(∀phi).
Proof.
 intros HGen(A&HA&P). apply(full_theory_cut T(map(fun ax=>∀ax)A)(∀phi)).
 - now apply full_prefix_generalize_context.
 - intros ax Hax. apply in_map_iff in Hax as(f&<-&HF). apply HGen,HA,HF.
Qed.
Print Assumptions full_theory_generalize_from_axioms.
