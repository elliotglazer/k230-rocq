(** A transitive raw container from two KP0 instances. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From K230S Require Import KP0 KP0Use KPRaw.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition raw_transitive (c : term) : form :=
  ∀ ($0 ∈' c`[↑] → raw_subset $0 c`[↑]).

Lemma raw_transitive_subst c sg :
  (raw_transitive c)[sg] = raw_transitive c`[sg].
Proof. psubst raw_transitive. Qed.
#[global] Hint Rewrite raw_transitive_subst : fsub.
#[global] Arguments raw_transitive : simpl never.

Definition transitive_matrix : form := raw_singleton $0 $1.

Lemma transitive_matrix_bounded : fb 2 transitive_matrix.
Proof. unfold transitive_matrix, raw_singleton. cbn. lia. Qed.

Lemma kp0_transitive G (HE : incl EqAx G) a :
  In (forall_times 1 (kp0 singleton_matrix)) G ->
  In (kp0 transitive_matrix) G ->
  G ⊢C ∃ (a`[↑] ∈' $0 ∧ raw_transitive $0).
Proof.
  intros Hsingleton Htransitive.
  fobtain (kp0_singleton _ HE a Hsingleton) as s Hs.
  pose proof (kp0_use _ 0 transitive_matrix var s Htransitive transitive_matrix_bounded) as T.
  fex T C HC. fdestr HC Hrequest Hsupport.
  unfold transitive_matrix in Hrequest, Hsupport. simp_in Hrequest. simp_in Hsupport.
  fassert HaC : (a ∈' C).
  { pose proof Hrequest as H. finst H s.
    fassert Helig : (s ≡' s ∨ ∃ ($0 ∈' C`[↑] ∧ raw_subset s`[↑] $0)).
    { fleft. feqE. }
    unfold raw_subset in Helig. fmp H Helig.
    fassert Hwit : (∃ raw_singleton $0 s`[↑]). { fexists a. exact Hs. }
    fmp H Hwit. fex H y Hy. fdestr Hy HyC Hys.
    unfold raw_singleton in Hs, Hys.
    pose proof (CE1 Hs) as Has. pose proof (CE2 Hys) as Hprofile.
    finst Hprofile a. fmp Hprofile Has. fmemE. }
  fexists C. fsplit; [exact HaC|]. unfold raw_transitive.
  fall u. fintro HuC. unfold raw_subset. fall v. fintro Hvu.
  fobtain (kp0_singleton _ HE v Hsingleton) as p Hp.
  pose proof Hrequest as H. finst H p.
  fassert Helig : (p ≡' s ∨ ∃ ($0 ∈' C`[↑] ∧ raw_subset p`[↑] $0)).
  { fright. fexists u. fsplit; [exact HuC|].
    unfold raw_subset. fall z. fintro Hzp.
    pose proof Hp as Hp'. unfold raw_singleton in Hp'.
    pose proof (CE2 Hp') as Hprofile. finst Hprofile z. fmp Hprofile Hzp. fmemE. }
  unfold raw_subset in Helig. fmp H Helig.
  fassert Hwit : (∃ raw_singleton $0 p`[↑]). { fexists v. exact Hp. }
  fmp H Hwit. fex H y Hy. fdestr Hy HyC Hyp.
  unfold raw_singleton in Hp, Hyp.
  pose proof (CE1 Hp) as Hvp. pose proof (CE2 Hyp) as Hprofile.
  finst Hprofile v. fmp Hprofile Hvp. fmemE.
Qed.

Definition raw_transitive_axiom : form := ∀ ∃ ($1 ∈' $0 ∧ raw_transitive $0).

Theorem K0_proves_transitive : K0 ⊢TC raw_transitive_axiom.
Proof.
  exists (EqAx ++ [forall_times 1 (kp0 singleton_matrix); kp0 transitive_matrix]). split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[<-|[]]]].
    + apply K0_eq. exact Hb.
    + apply K0_instance, kp0_closed. exact singleton_matrix_bounded.
    + apply (K0_instance transitive_matrix 0), kp0_closed. exact transitive_matrix_bounded.
  - unfold raw_transitive_axiom. fall a. apply kp0_transitive.
    + intros b Hb. cbn in *. tauto.
    + cbn. tauto.
    + cbn. tauto.
Qed.
