(** Classical full syntax encoded in the implication/universal fragment. *)
From Undecidability.FOL.Syntax Require Import Core Bounded.
From Stdlib Require Import Lists.List.
Import ListNotations.
Set Implicit Arguments.
Section Translation.
Context {F:funcs_signature} {P:preds_signature}.
Local Notation full := (@form F P FullSyntax.full_operators falsity_on).
Local Notation frag := (@form F P FragmentSyntax.frag_operators falsity_on).
Definition frag_impl (a b:frag):frag := @bin F P FragmentSyntax.frag_operators falsity_on FragmentSyntax.Impl a b.
Definition frag_neg (a:frag):frag :=frag_impl a falsity.
Fixpoint full_to_fragment {ff} (phi:@form F P FullSyntax.full_operators ff):frag :=
 match phi with
 |falsity=>falsity
 |atom p v=>atom p v
 |bin FullSyntax.Impl a b=>frag_impl(full_to_fragment a)(full_to_fragment b)
 |bin FullSyntax.Conj a b=>frag_neg(frag_impl(full_to_fragment a)(frag_neg(full_to_fragment b)))
 |bin FullSyntax.Disj a b=>frag_impl(frag_neg(full_to_fragment a))(full_to_fragment b)
 |quant FullSyntax.All a=>@quant F P FragmentSyntax.frag_operators falsity_on FragmentSyntax.All(full_to_fragment a)
 |quant FullSyntax.Ex a=>frag_neg(@quant F P FragmentSyntax.frag_operators falsity_on FragmentSyntax.All(frag_neg(full_to_fragment a)))
 end.
Fixpoint fragment_to_full {ff} (phi:@form F P FragmentSyntax.frag_operators ff):full :=
 match phi with
 |falsity=>falsity
 |atom p v=>atom p v
 |bin FragmentSyntax.Impl a b=>@bin F P FullSyntax.full_operators falsity_on FullSyntax.Impl(fragment_to_full a)(fragment_to_full b)
 |quant FragmentSyntax.All a=>@quant F P FullSyntax.full_operators falsity_on FullSyntax.All(fragment_to_full a)
 end.
Theorem full_to_fragment_substitution {ff} (phi:@form F P FullSyntax.full_operators ff) sigma:
 full_to_fragment(subst_form sigma phi)=subst_form sigma(full_to_fragment phi).
Proof.
 induction phi in sigma|-*;cbn;try reflexivity.
 -destruct b0;cbn[frag_impl frag_neg];now rewrite IHphi1,IHphi2.
 -destruct q;cbn[frag_impl frag_neg];now rewrite IHphi.
Qed.
Theorem fragment_to_full_substitution {ff} (phi:@form F P FragmentSyntax.frag_operators ff) sigma:
 fragment_to_full(subst_form sigma phi)=subst_form sigma(fragment_to_full phi).
Proof.
 induction phi in sigma|-*;cbn;try reflexivity.
 -destruct b0;cbn;now rewrite IHphi1,IHphi2.
 -destruct q;cbn;now rewrite IHphi.
Qed.
Theorem fragment_full_roundtrip (phi:frag):
 full_to_fragment(fragment_to_full phi)=phi.
Proof.
 induction phi using form_ind_falsity;cbn;try reflexivity.
 -destruct b0;cbn[full_to_fragment frag_impl]. now rewrite IHphi1,IHphi2.
 -destruct q;cbn;now rewrite IHphi.
Qed.
Theorem full_to_fragment_bounded n (phi:full):
 bounded n phi ->bounded n(full_to_fragment phi).
Proof.
 intro H;induction H;cbn;try constructor;try assumption.
 -destruct binop;cbn[frag_impl frag_neg];repeat constructor;assumption.
 -destruct quantop;cbn[frag_impl frag_neg];repeat constructor;assumption.
Qed.
Theorem fragment_to_full_bounded n (phi:frag):
 bounded n phi ->bounded n(fragment_to_full phi).
Proof.
 intro H;induction H;cbn;try constructor;try assumption.
 -destruct binop;cbn;now constructor.
 -destruct quantop;cbn;now constructor.
Qed.
Theorem full_to_fragment_closed (phi:full):closed phi ->closed(full_to_fragment phi).
Proof. apply full_to_fragment_bounded. Qed.
Theorem fragment_to_full_closed (phi:frag):closed phi ->closed(fragment_to_full phi).
Proof. apply fragment_to_full_bounded. Qed.
Definition full_fragment_theory(T:full->Prop)(theta:frag):Prop :=
 exists ax,T ax /\theta=full_to_fragment ax.
Theorem full_fragment_closed_theory(T:full->Prop):
 (forall ax,T ax->closed ax)->forall theta,full_fragment_theory T theta->closed theta.
Proof. intros HT theta(ax&HA&->). now apply full_to_fragment_closed,HT. Qed.
End Translation.
Print Assumptions full_to_fragment_substitution.
Print Assumptions fragment_to_full_substitution.
Print Assumptions fragment_full_roundtrip.
Print Assumptions full_to_fragment_closed.
Print Assumptions fragment_to_full_closed.
Print Assumptions full_fragment_closed_theory.
