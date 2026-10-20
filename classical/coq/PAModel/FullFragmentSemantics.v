(** Same-carrier semantic bridge; atoms, including equality, are copied literally. *)
From PAModel Require Import FullFragmentSyntax.
From Undecidability.FOL.Semantics.Tarski Require Import FullCore FragmentCore.
From Undecidability.FOL.Syntax Require Import Bounded.
From Stdlib Require Import Logic.Classical_Prop Vectors.Vector.
Module FullSem := Undecidability.FOL.Semantics.Tarski.FullCore.
Module FragSem := Undecidability.FOL.Semantics.Tarski.FragmentCore.
Set Implicit Arguments.
Section SemanticTranslation.
Context {F:funcs_signature}{P:preds_signature}{D:Type}.
Definition fragment_full_interp(I:FragSem.interp D):FullSem.interp D :=
 {|FullSem.i_func:=@FragSem.i_func F P D I;FullSem.i_atom:=@FragSem.i_atom F P D I|}.
Theorem fragment_full_eval(I:FragSem.interp D)rho t:
 @FullSem.eval F P D(fragment_full_interp I)rho t=@FragSem.eval F P D I rho t.
Proof.
 reflexivity.
Qed.
Theorem full_to_fragment_semantics(I:FragSem.interp D)(phi:@form F P FullSyntax.full_operators falsity_on)rho:
 FragSem.sat I rho(full_to_fragment phi)<->FullSem.sat(fragment_full_interp I)rho phi.
Proof.
 revert rho. induction phi using form_ind_falsity;intro rho;cbn.
 -tauto.
 -replace(Vector.map(@FullSem.eval F P D(fragment_full_interp I)rho)t)
   with(Vector.map(@FragSem.eval F P D I rho)t);[reflexivity|].
  apply Vector.map_ext. intro x. symmetry. apply fragment_full_eval.
 -destruct b0;cbn[full_to_fragment frag_impl frag_neg FragSem.sat FullSem.sat];rewrite IHphi1,IHphi2;tauto.
 -destruct q;cbn[full_to_fragment frag_impl frag_neg FragSem.sat FullSem.sat].
  +split;intros H d;[apply(proj1(IHphi(d.:rho)))|apply(proj2(IHphi(d.:rho)))];apply H.
  +split.
   *intro H. apply NNPP. intro Hn. apply H. intros d Hd. apply Hn.
    exists d. now apply(proj1(IHphi(d.:rho))).
   *intros[d Hd]H. apply(H d). now apply(proj2(IHphi(d.:rho))).
Qed.
Theorem fragment_to_full_semantics(I:FragSem.interp D)(phi:@form F P FragmentSyntax.frag_operators falsity_on)rho:
 FullSem.sat(fragment_full_interp I)rho(fragment_to_full phi)<->FragSem.sat I rho phi.
Proof.
 pose proof(full_to_fragment_semantics I(fragment_to_full phi)rho)as H.
 rewrite fragment_full_roundtrip in H. symmetry. exact H.
Qed.
Theorem fragment_full_theory_semantics(I:FragSem.interp D)(T:@form F P FullSyntax.full_operators falsity_on->Prop):
 (forall theta rho,full_fragment_theory T theta->FragSem.sat I rho theta)<->
 (forall ax rho,T ax->FullSem.sat(fragment_full_interp I)rho ax).
Proof.
 split.
 -intros H ax rho HA. apply(proj1(full_to_fragment_semantics I ax rho)),H.
  exists ax. auto.
 -intros H theta rho(ax&HA&->). apply(proj2(full_to_fragment_semantics I ax rho)),H,HA.
Qed.
End SemanticTranslation.
Print Assumptions fragment_full_eval.
Print Assumptions full_to_fragment_semantics.
Print Assumptions fragment_full_theory_semantics.
