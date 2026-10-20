(** Actual classical natural-deduction equivalence of full formulas and their encodings. *)
From PAModel Require Import FullFragmentSyntax.
From Undecidability.FOL.Syntax Require Import Core Subst.
From Undecidability.FOL.Deduction Require Import FullNDFacts.
From Stdlib Require Import Lists.List.
Import ListNotations FullSyntax.
Set Implicit Arguments.
Section Roundtrip.
Context {F:funcs_signature}{P:preds_signature}.
Local Notation full :=(@form F P FullSyntax.full_operators falsity_on).
Local Notation Prv :=(@FullND.prv F P falsity_on class).
Local Ltac ctx :=apply FullND.Ctx;cbn;firstorder.
Local Ltac weaken H :=eapply FullNDFacts.Weak;[exact H|firstorder].
Lemma encoded_conjunction_rule(G:list full)(a b:full):
 Prv G(¬(a→¬b)) <->(Prv G a /\Prv G b).
Proof.
 split.
 -intro H. split.
  +apply FullNDFacts.DN,FullND.II. eapply FullND.IE;[weaken H|].
   apply FullND.II,FullND.II. eapply FullND.IE;[ctx|ctx].
  +apply FullNDFacts.DN,FullND.II. eapply FullND.IE;[weaken H|].
   apply FullND.II. ctx.
 -intros[Ha Hb]. apply FullND.II. eapply FullND.IE.
  +eapply FullND.IE;[ctx|weaken Ha].
  +weaken Hb.
Qed.
Lemma encoded_disjunction_rule(G:list full)(a b:full):
 Prv G((¬a)→b)<->Prv G(a∨b).
Proof.
 split.
 -intro H. apply(FullNDFacts.XMc(A:=G)(phi:=a)).
  +apply FullND.DI1. ctx.
  +apply FullND.DI2. eapply FullND.IE;[weaken H|ctx].
 -intro H. eapply FullND.DE;[exact H| |].
  +apply FullND.II,FullND.Exp. eapply FullND.IE;[ctx|ctx].
  +apply FullND.II. ctx.
Qed.
Lemma encoded_exists_rule(G:list full)(a:full):
 Prv G(¬∀¬a)<->Prv G(∃a).
Proof.
 split.
 -intro H. apply FullNDFacts.DN,FullND.II. eapply FullND.IE;[weaken H|].
  apply FullNDFacts.AllI_named. intro t. cbn. apply FullND.II.
  eapply FullND.IE;[ctx|]. apply(FullND.ExI t). ctx.
 -intro H. apply FullND.II.
  eapply FullNDFacts.ExE_named;[weaken H|]. intro t.
  eapply FullND.IE with(phi:=a[t..]).
  +change(Prv(a[t..]::(∀¬a)::G)((¬a)[t..])).
   apply(FullND.AllE t). ctx.
  +ctx.
Qed.
Lemma full_implication_equiv(a a' b b':full):
 (forall G,Prv G a<->Prv G a')->(forall G,Prv G b<->Prv G b')->
 forall G,Prv G(a→b)<->Prv G(a'→b').
Proof.
 intros HA HB G. split;intro H;apply FullND.II.
 -apply(proj1(HB _)). eapply FullND.IE;[weaken H|]. apply(proj2(HA _)). ctx.
 -apply(proj2(HB _)). eapply FullND.IE;[weaken H|]. apply(proj1(HA _)). ctx.
Qed.
Lemma full_conjunction_equiv(a a' b b':full):
 (forall G,Prv G a<->Prv G a')->(forall G,Prv G b<->Prv G b')->
 forall G,Prv G(a∧b)<->Prv G(a'∧b').
Proof.
 intros HA HB G. split;intro H;apply FullND.CI.
 -apply(proj1(HA _)). now apply(FullND.CE1 H).
 -apply(proj1(HB _)). now apply(FullND.CE2 H).
 -apply(proj2(HA _)). now apply(FullND.CE1 H).
 -apply(proj2(HB _)). now apply(FullND.CE2 H).
Qed.
Lemma full_disjunction_equiv(a a' b b':full):
 (forall G,Prv G a<->Prv G a')->(forall G,Prv G b<->Prv G b')->
 forall G,Prv G(a∨b)<->Prv G(a'∨b').
Proof.
 intros HA HB G. split.
 -intro H;eapply FullND.DE;[exact H| |].
  +apply FullND.DI1, (proj1(HA _)). ctx.
  +apply FullND.DI2, (proj1(HB _)). ctx.
 -intro H;eapply FullND.DE;[exact H| |].
  +apply FullND.DI1, (proj2(HA _)). ctx.
  +apply FullND.DI2, (proj2(HB _)). ctx.
Qed.
Lemma full_all_equiv(a b:full):
 (forall sigma G,Prv G(a[sigma])<->Prv G(b[sigma]))->
 forall sigma G,Prv G((∀a)[sigma])<->Prv G((∀b)[sigma]).
Proof.
 intros HE sigma G. cbn. split;intro H;apply FullNDFacts.AllI_named;intro t;
 rewrite subst_comp.
 -apply(proj1(HE _ _)). rewrite <-subst_comp. now apply(FullND.AllE t).
 -apply(proj2(HE _ _)). rewrite <-subst_comp. now apply(FullND.AllE t).
Qed.
Lemma full_exists_equiv(a b:full):
 (forall sigma G,Prv G(a[sigma])<->Prv G(b[sigma]))->
 forall sigma G,Prv G((∃a)[sigma])<->Prv G((∃b)[sigma]).
Proof.
 intros HE sigma G. cbn. split.
 -intro H;eapply FullNDFacts.ExE_named;[exact H|];intro t.
  apply(FullND.ExI t);rewrite !subst_comp.
  apply(proj1(HE _ _)). ctx.
 -intro H;eapply FullNDFacts.ExE_named;[exact H|];intro t.
  apply(FullND.ExI t);rewrite !subst_comp.
  apply(proj2(HE _ _)). ctx.
Qed.
Definition full_roundtrip(phi:full):full:=fragment_to_full(full_to_fragment phi).
Theorem full_roundtrip_substitution(phi:full)sigma:
 full_roundtrip(phi[sigma])=(full_roundtrip phi)[sigma].
Proof. unfold full_roundtrip. rewrite full_to_fragment_substitution,fragment_to_full_substitution. reflexivity. Qed.
Theorem full_roundtrip_proof_equivalence(phi:full):
 forall sigma G,Prv G(phi[sigma])<->Prv G((full_roundtrip phi)[sigma]).
Proof.
 induction phi using form_ind_falsity;intros sigma G.
 -reflexivity.
 -reflexivity.
 -destruct b0;cbn[full_roundtrip full_to_fragment fragment_to_full frag_impl frag_neg subst_form].
  +rewrite encoded_conjunction_rule. split.
   *intro H. split;[apply(proj1(IHphi1 sigma G));now apply(FullND.CE1 H)|apply(proj1(IHphi2 sigma G));now apply(FullND.CE2 H)].
   *intros[Ha Hb]. apply FullND.CI;[now apply(proj2(IHphi1 sigma G))|now apply(proj2(IHphi2 sigma G))].
  +rewrite encoded_disjunction_rule. apply full_disjunction_equiv;[apply IHphi1|apply IHphi2].
  +apply full_implication_equiv;[apply IHphi1|apply IHphi2].
 -destruct q.
  +apply full_all_equiv. exact IHphi.
  +cbn[full_roundtrip full_to_fragment fragment_to_full frag_impl frag_neg subst_form].
   rewrite encoded_exists_rule. apply(full_exists_equiv IHphi sigma G).
Qed.
Theorem full_roundtrip_proof(phi:full)G:
 Prv G phi<->Prv G(full_roundtrip phi).
Proof.
 pose proof(full_roundtrip_proof_equivalence phi var G)as H. now rewrite !subst_var in H.
Qed.
End Roundtrip.
Print Assumptions encoded_exists_rule.
Print Assumptions full_roundtrip_proof.
