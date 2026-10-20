(** A finite source proof of membership irreflexivity from Pairing and
    Foundation. The local context tactics follow the elementary FullND
    pattern used by the original set-theoretic verification. *)
From PAModel Require Import SetFormulaCodes ZFCFiniteAxiomTemplates.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts Syntax.Facts.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma ns_weak_cons (G:list sf_form) (a f:sf_form) : G ⊢C f -> (a::G) ⊢C f.
Proof. intro H. apply (Weak H). intros x HX. now right. Qed.
Ltac ns_simp := cbn; asimpl; cbn.
Ltac ns_simp_in H := cbn in H; asimpl in H; cbn in H.
Ltac ns_push H :=
  match goal with |- (?a::?G) ⊢C _ =>
    repeat match goal with
    | K:G ⊢C _ |- _ => apply (ns_weak_cons G a) in K
    | K:In ?f G |- _ => let K' := fresh in assert (K':In f (a::G)) by (right;exact K);clear K;rename K' into K
    end;
    assert (H:(a::G) ⊢C a) by (apply Ctx;now left);
    let G' := fresh "Gamma" in set (G':=a::G) in *;
    repeat match goal with K:?C ⊢C ?phi |- _ =>
      tryif constr_eq C G' then fail else change (G' ⊢C phi) in K end;
    repeat match goal with K:In ?phi ?C |- _ =>
      tryif constr_eq C G' then fail else change (In phi G') in K end;
    clearbody G';try clear G
  end.
Ltac ns_intro H := apply II;ns_simp;ns_push H;try ns_simp_in H.
Ltac ns_all x := apply AllI_named;intro x;ns_simp.
Ltac ns_exists_elim H x HX := apply (ExE_named H);intro x;ns_simp;ns_push HX;ns_simp_in HX;try clear H.
Ltac ns_inst H t := apply (AllE t) in H;ns_simp_in H.
Ltac ns_mp H H' := let K:=fresh in pose proof (IE H H') as K;clear H;rename K into H.
Tactic Notation "ns_assert" ident(H) constr(f) :=
  match goal with |- ?G ⊢C _ => assert (H:G ⊢C f) end.

Lemma finite_set_refl G t : In ax_refl' G -> G ⊢C t ≡' t.
Proof. intro HR. assert (H:G ⊢C ax_refl') by (apply Ctx;exact HR). ns_inst H t. exact H. Qed.
Lemma finite_set_sym G t u : In ax_sym' G -> G ⊢C t ≡' u -> G ⊢C u ≡' t.
Proof.
  intros HS Htu. assert (H:G ⊢C ax_sym') by (apply Ctx;exact HS).
  ns_inst H t. ns_inst H u. exact (IE H Htu).
Qed.
Lemma finite_set_mem_cong G t u t' u' : In ax_eq_elem' G ->
  G ⊢C t ≡' t' -> G ⊢C u ≡' u' -> G ⊢C t ∈' u -> G ⊢C t' ∈' u'.
Proof.
  intros HE HT HU HM. assert (H:G ⊢C ax_eq_elem') by (apply Ctx;exact HE).
  ns_inst H t. ns_inst H u. ns_inst H t'. ns_inst H u'.
  ns_mp H HT. ns_mp H HU. exact (IE H HM).
Qed.

Theorem finite_source_no_self G :
  In source_foundation G -> In ax_pair' G -> In ax_refl' G -> In ax_sym' G -> In ax_eq_elem' G ->
  G ⊢C ∀ ¬ ($0 ∈' $0).
Proof.
  intros HFound HPair HRefl HSym HElem.
  ns_all x. ns_intro Hxx.
  ns_assert HP ax_pair'. { apply Ctx;exact HPair. }
  ns_inst HP x. ns_inst HP x.
  ns_exists_elim HP s HS.
  ns_assert Hxs (x ∈' s).
  { pose proof HS as H. ns_inst H x.
    apply (IE (CE2 H)). apply DI1. apply finite_set_refl;exact HRefl. }
  ns_assert HF source_foundation. { apply Ctx;exact HFound. }
  ns_inst HF s.
  ns_assert Hnonempty (∃ $0 ∈' s`[↑]).
  { apply (ExI x). ns_simp. exact Hxs. }
  ns_mp HF Hnonempty.
  ns_exists_elim HF y HY.
  pose proof (CE1 HY) as Hys. pose proof (CE2 HY) as Hmin.
  pose proof HS as HEq. ns_inst HEq y. pose proof (IE (CE1 HEq) Hys) as HEq'.
  apply (DE HEq');ns_push Hyx.
  all: ns_assert Hxy (x ≡' y);[apply finite_set_sym;[exact HSym|exact Hyx]|].
  all: ns_assert HxyMem (x ∈' y).
  all: try (eapply finite_set_mem_cong;[exact HElem|apply finite_set_refl;exact HRefl|exact Hxy|exact Hxx]).
  all: ns_inst Hmin x.
  all: ns_mp Hmin HxyMem.
  all: exact (IE Hmin Hxs).
Qed.

Definition finite_no_self_axioms : list sf_form :=
  [source_foundation;ax_pair';ax_refl';ax_sym';ax_eq_elem'].
Theorem finite_no_self_closed : finite_no_self_axioms ⊢C ∀ ¬ ($0 ∈' $0).
Proof. apply finite_source_no_self;unfold finite_no_self_axioms;cbn;tauto. Qed.

Print Assumptions finite_no_self_closed.
