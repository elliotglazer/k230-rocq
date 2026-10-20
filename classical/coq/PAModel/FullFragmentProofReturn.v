(** Direct finite proof return, without a completeness theorem. *)
From PAModel Require Import FullFragmentSyntax FragmentFullProofEmbedding FullFragmentRoundtrip.
From Undecidability.FOL.Syntax Require Import Core.
From Undecidability.FOL.Deduction Require Import FullNDFacts.
From Undecidability.FOL.Deduction Require FragmentND.
From Stdlib Require Import Lists.List.
Import ListNotations FullSyntax.
Set Implicit Arguments.
Section ReturnProof.
Context {F:funcs_signature}{P:preds_signature}.
Local Notation full:=(@form F P FullSyntax.full_operators falsity_on).
Local Notation frag:=(@form F P FragmentSyntax.frag_operators falsity_on).
Local Notation Prv:=(@FullND.prv F P falsity_on class).
Local Notation TPrv:=(@FullND.tprv F P falsity_on class).
Lemma full_theory_collect_context(T:full->Prop)(A:list full):
 (forall ax,In ax A->TPrv T ax)->
 exists B,(forall ax,In ax B->T ax)/\(forall ax,In ax A->Prv B ax).
Proof.
 induction A as[|a A IH];intro HA.
 -exists[]. split;intros ax H;inversion H.
 -destruct(HA a(or_introl eq_refl))as(B&HB&PB).
  destruct(IH(fun ax H=>HA ax(or_intror H)))as(C&HC&PC).
  exists(B++C). split.
  +intros ax H. apply in_app_iff in H. destruct H;auto.
  +intros ax[<-|H].
   *eapply FullNDFacts.Weak;[exact PB|]. intros v Hv. apply in_or_app. now left.
   *eapply FullNDFacts.Weak;[exact(PC ax H)|]. intros v Hv. apply in_or_app. now right.
Qed.
Lemma full_theory_finite_cut(T:full->Prop)(A:list full)(phi:full):
 Prv A phi->(forall ax,In ax A->TPrv T ax)->TPrv T phi.
Proof.
 intros H HA. destruct(full_theory_collect_context HA)as(B&HB&PB).
 exists B. split;[exact HB|]. now apply(FullNDFacts.prv_cut H).
Qed.
Theorem fragment_translated_proof_return(T:full->Prop)(phi:full):
 @FragmentND.tprv F P falsity_on class(full_fragment_theory T)(full_to_fragment phi)->
 TPrv T phi.
Proof.
 intros(A&HA&PA).
 pose proof(fragment_full_proof PA)as PP.
 assert(HT:TPrv T(full_roundtrip phi)).
 {apply(full_theory_finite_cut PP). intros theta Htheta.
  apply in_map_iff in Htheta as(psi&<-&HP).
  destruct(HA psi HP)as(ax&Hax&->).
  exists[ax]. split.
  -intros z[<-|H];[exact Hax|inversion H].
  -apply(proj1(full_roundtrip_proof ax ([ax]))). apply FullND.Ctx. now left. }
 destruct HT as(B&HB&PB). exists B. split;[exact HB|].
 now apply(proj2(full_roundtrip_proof phi B)).
Qed.
End ReturnProof.
Print Assumptions full_theory_collect_context.
Print Assumptions fragment_translated_proof_return.
