(** Augmented raw Separation: the chosen subset together with its carrier marker. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From K230S Require Import KP0 KP0Use KPRaw.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** theta has the selected element at index 0. Matrix parameters are a, s,
    then theta's parameters. *)
Definition separation_matrix (theta : form) : form :=
  ($1 ≡' $3 ∧ $0 ≡' $2) ∨
  (raw_singleton $0 $1 ∧ ($0 ∈' $2 ∧ theta[$0 .: (fun k => $(4 + k))])).

Lemma separation_matrix_bounded n theta : fb (S n) theta ->
  fb (S (S (S (S n)))) (separation_matrix theta).
Proof.
  intros H. unfold separation_matrix, raw_singleton. cbn.
  repeat split; try lia. eapply fb_subst; [exact H|].
  intros [|k] Hk; cbn; lia.
Qed.

Lemma kp0_augmented_separation G (HE : incl EqAx G) n theta (sg : nat -> term) a :
  fb (S n) theta ->
  In (forall_times 1 (kp0 singleton_matrix)) G ->
  In (forall_times (S (S n)) (kp0 (separation_matrix theta))) G ->
  G ⊢C ∃ ∀ ($0 ∈' $1 ↔
     ($0 ≡' a`[↑]`[↑] ∨ ($0 ∈' a`[↑]`[↑] ∧ theta[$0 .: (fun k => (sg k)`[↑]`[↑])]))).
Proof.
  intros Hfb Hsingleton Hseparation.
  fobtain (kp0_singleton _ HE a Hsingleton) as s Hs.
  pose proof (kp0_use _ (S (S n)) (separation_matrix theta) (a .: s .: sg) s
    Hseparation (separation_matrix_bounded n theta Hfb)) as T.
  fex T C HC. fdestr HC Hrequest Hsupport.
  unfold separation_matrix in Hrequest, Hsupport. simp_in Hrequest. simp_in Hsupport.
  fassert HaC : (a ∈' C).
  { pose proof Hrequest as H. finst H s.
    fassert Helig : (s ≡' s ∨ ∃ ($0 ∈' C`[↑] ∧ raw_subset s`[↑] $0)).
    { fleft. feqE. }
    unfold raw_subset in Helig. fmp H Helig.
    match type of H with _ ⊢C ?A → _ => fassert Hwit : A end.
    { fexists a. fleft. fsplit; feqE. }
    fmp H Hwit. fex H y Hy. fdestr Hy HyC Hycases.
    fcases Hycases Hleft Hright.
    - pose proof (CE2 Hleft) as Hya. fmemE.
    - pose proof (CE1 Hright) as Hys. unfold raw_singleton in Hs, Hys.
      pose proof (CE1 Hs) as Has. pose proof (CE2 Hys) as Hprofile.
      finst Hprofile a. fmp Hprofile Has. fmemE. }
  fexists C. fall x. fsplit.
  - fintro HxC. pose proof Hsupport as H. finst H x. fmp H HxC.
    fex H p Hp. fcases Hp Hleft Hright.
    + fleft. exact (CE2 Hleft).
    + fright. pose proof (CE2 Hright) as Hpair.
      fsplit; [exact (CE1 Hpair)|]. pose proof (CE2 Hpair) as Htheta. kconv Htheta.
  - fintro Hcases. fcases Hcases Heq Hselected.
    + fmemE.
    + fdestr Hselected Hxa Htheta.
      fobtain (kp0_singleton _ HE x Hsingleton) as p Hp.
      pose proof Hrequest as H. finst H p.
      fassert Helig : (p ≡' s ∨ ∃ ($0 ∈' C`[↑] ∧ raw_subset p`[↑] $0)).
      { fright. fexists a. fsplit; [exact HaC|].
        unfold raw_subset. fall z. fintro Hzp.
        pose proof Hp as Hp'. unfold raw_singleton in Hp'.
        pose proof (CE2 Hp') as Hprofile. finst Hprofile z. fmp Hprofile Hzp. fmemE. }
      unfold raw_subset in Helig. fmp H Helig.
      match type of H with _ ⊢C ?A → _ => fassert Hwit : A end.
      { fexists x. fright. fsplit; [exact Hp|]. fsplit; [exact Hxa|]. kconv Htheta. }
      fmp H Hwit. fex H y Hy. fdestr Hy HyC Hycases.
      fcases Hycases Hleft Hright.
      * fdestr Hleft Hps Hya.
        pose proof Hp as Hp'. unfold raw_singleton in Hp', Hs.
        pose proof (CE1 Hp') as Hxp.
        fassert Hxs : (x ∈' s). { fmemE. }
        pose proof (CE2 Hs) as Hprofile. finst Hprofile x. fmp Hprofile Hxs. fmemE.
      * pose proof (CE1 Hright) as Hyp. unfold raw_singleton in Hp, Hyp.
        pose proof (CE1 Hp) as Hxp. pose proof (CE2 Hyp) as Hprofile.
        finst Hprofile x. fmp Hprofile Hxp. fmemE.
Qed.

Definition augmented_separation (theta : form) : form :=
  ∀ ∃ ∀ ($0 ∈' $1 ↔ ($0 ≡' $2 ∨
     ($0 ∈' $2 ∧ theta[$0 .: (fun k => $(3 + k))]))).

Theorem K0_proves_augmented_separation n theta : fb (S n) theta ->
  K0 ⊢TC forall_times n (augmented_separation theta).
Proof.
  intros Hfb.
  exists (EqAx ++ [forall_times 1 (kp0 singleton_matrix);
                  forall_times (S (S n)) (kp0 (separation_matrix theta))]). split.
  - intros b Hb. apply in_app_or in Hb as [Hb|[<-|[<-|[]]]].
    + apply K0_eq. exact Hb.
    + apply K0_instance, kp0_closed. exact singleton_matrix_bounded.
    + apply K0_instance, kp0_closed, separation_matrix_bounded, Hfb.
  - apply ft_intro. intros sg. cbn. fall a.
    match goal with |- ?G ⊢C _ =>
      pose proof (kp0_augmented_separation G ltac:(intros b Hb; cbn in *; tauto)
        n theta sg a Hfb ltac:(cbn; tauto) ltac:(cbn; tauto)) as T
    end.
    kconv T.
Qed.
