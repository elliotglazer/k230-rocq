(** Direct preservation of classical natural-deduction proofs by qtrans.
    Adapted from the pinned reference's qt_prv and rel_prv arguments. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldUndecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations ListAutomationFacts ListAutomationHints ListAutomationInstances.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From OldK230S Require Import KP0Use KQuotFormula KPrimeTheory.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Ltac qspec_refl := repeat match goal with H : ?x = ?x -> _ |- _ => specialize (H eq_refl) end.

Theorem qtrans_prv A (phi : form) :
  A ⊢C phi -> forall G m (sg : nat -> term),
  (forall k, G ⊢C m ∈' sg k) ->
  (forall a, In a A -> G ⊢C qtrans m a[sg]) -> G ⊢C qtrans m phi[sg].
Proof.
  intros H. remember class as p eqn:Hp. revert Hp. revert p A phi H.
  apply (prv_ind_full (P := fun p A phi => p = class -> forall G m sg,
    (forall k, @prv _ _ falsity_on p G (m ∈' sg k)) ->
    (forall a, In a A -> @prv _ _ falsity_on p G (qtrans m a[sg])) ->
    @prv _ _ falsity_on p G (qtrans m phi[sg]))); cbn.
  - intros p A phi psi _ IH Hp G m sg HD HA. subst p. qspec_refl.
    apply II. apply IH.
    + intros k. apply weak_cons, HD.
    + intros a [<-|Ha]; [apply Ctx; now left|apply weak_cons, HA, Ha].
  - intros p A phi psi _ IH1 _ IH2 Hp G m sg HD HA. subst p. qspec_refl.
    eapply IE; [apply IH1|apply IH2]; trivial.
  - intros p A phi _ IH Hp G m sg HD HA. subst p. qspec_refl.
    apply AllI_named. intros z. simp. apply II.
    apply (IH _ m (z .: sg)).
    + intros [|k]; cbn; [apply Ctx; now left|apply weak_cons, HD].
    + intros a Ha. apply in_map_iff in Ha as [b [<- Hb]].
      autorewrite with fsub. apply weak_cons, HA, Hb.
  - intros p A u phi _ IH Hp G m sg HD HA. subst p. qspec_refl.
    specialize (IH G m sg HD HA). cbn in IH. finst IH u`[sg].
    assert (Hu : G ⊢C m ∈' u`[sg]).
    { destruct u as [k|[]]. apply HD. }
    pose proof (IE IH Hu) as T. kconv T.
  - intros p A u phi _ IH Hp G m sg HD HA. subst p. qspec_refl.
    apply (ExI u`[sg]). simp. apply CI.
    + destruct u as [k|[]]. apply HD.
    + pose proof (IH G m sg HD HA) as T. kconv T.
  - intros p A phi psi _ IH1 _ IH2 Hp G m sg HD HA. subst p. qspec_refl.
    specialize (IH1 G m sg HD HA). cbn in IH1.
    apply (ExE_named IH1). intros z. simp.
    replace (qtrans m psi[sg]) with (qtrans m psi[↑][z .: sg]) by
      (f_equal; form_subst_eq).
    apply (IH2 _ m (z .: sg)).
    + intros [|k]; cbn.
      * eapply CE1. apply Ctx. now left.
      * apply weak_cons, HD.
    + intros a [<-|Ha].
      * eapply CE2. apply Ctx. now left.
      * apply in_map_iff in Ha as [b [<- Hb]].
        autorewrite with fsub. apply weak_cons, HA, Hb.
  - intros p A phi _ IH Hp G m sg HD HA. subst p. qspec_refl.
    apply Exp. exact (IH G m sg HD HA).
  - intros p A phi Hphi Hp G m sg HD HA. subst p. now apply HA.
  - intros p A phi psi _ IH1 _ IH2 Hp G m sg HD HA. subst p. qspec_refl.
    apply CI; [apply IH1|apply IH2]; trivial.
  - intros p A phi psi _ IH Hp G m sg HD HA. subst p. qspec_refl.
    eapply CE1. now apply IH.
  - intros p A phi psi _ IH Hp G m sg HD HA. subst p. qspec_refl.
    eapply CE2. now apply IH.
  - intros p A phi psi _ IH Hp G m sg HD HA. subst p. qspec_refl.
    apply DI1. now apply IH.
  - intros p A phi psi _ IH Hp G m sg HD HA. subst p. qspec_refl.
    apply DI2. now apply IH.
  - intros p A phi psi theta _ IH1 _ IH2 _ IH3 Hp G m sg HD HA. subst p. qspec_refl.
    eapply DE; [now apply IH1|apply IH2|apply IH3].
    1,3: intros k; apply weak_cons, HD.
    all: intros a [<-|Ha]; [apply Ctx; now left|apply weak_cons, HA, Ha].
  - intros A phi psi Hp G m sg HD HA. apply Pc.
Qed.

(** A constant domain-valued assignment needs only one membership proof,
    so gathering the target context never invokes an infinite choice. *)
Theorem qtrans_theory_map (T U : form -> Prop) m e phi :
  U ⊢TC m ∈' e ->
  (forall a, T a -> U ⊢TC qtrans m a[(fun _ => e)]) ->
  T ⊢TC phi -> U ⊢TC qtrans m phi[(fun _ => e)].
Proof.
  intros [E [HE DE]] HT [A [HA DA]].
  set (f := fun a : form => qtrans m a[(fun _ => e)]).
  destruct (collect_theory_proofs U (map f A)) as [B [HB DB]].
  { intros b Hb. apply in_map_iff in Hb as [a [<- Ha]]. apply HT, HA, Ha. }
  exists (E ++ B). split.
  - intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [apply HE|apply HB]; assumption.
  - apply (qtrans_prv A phi DA (E ++ B) m (fun _ => e)).
    + intros k. eapply Weak; [exact DE|]. intros a Ha. apply in_or_app. now left.
    + intros a Ha. eapply Weak.
      * apply (DB (f a)). apply in_map, Ha.
      * intros b Hb. apply in_or_app. now right.
Qed.

Corollary qtrans_inconsistency_map (T U : form -> Prop) m e :
  U ⊢TC m ∈' e ->
  (forall a, T a -> U ⊢TC qtrans m a[(fun _ => e)]) ->
  T ⊢TC ⊥ -> U ⊢TC ⊥.
Proof. intros HD HT H. exact (qtrans_theory_map T U m e ⊥ HD HT H). Qed.
