(** Translation of full first-order formulas into the tagged quotient. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From ZFC Require Import Z_base.
From K230S Require Import KP0 KP0Use KBase KMarkers KTagged KRelation KQuot KQuotSym KQuotTrans KQuotMem.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Fixpoint qtrans {ff} (t : term) (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : form :=
  match phi with
  | falsity => falsity
  | atom P v =>
      match P return Vector.t term (ar_preds P) -> form with
      | elem => fun v => dmem t (Vector.hd v) (Vector.hd (Vector.tl v))
      | equal => fun v => deqv t (Vector.hd v) (Vector.hd (Vector.tl v))
      end v
  | bin op a b => bin op (qtrans t a) (qtrans t b)
  | quant All a => ∀ (t`[↑] ∈' $0 → qtrans t`[↑] a)
  | quant Ex a => ∃ (t`[↑] ∈' $0 ∧ qtrans t`[↑] a)
  end.

Lemma qtrans_subst (phi : form) : forall t sg,
  (qtrans t phi)[sg] = qtrans t`[sg] phi[sg].
Proof.
  induction phi as [|P v|op a IHa b IHb|q a IHa] using form_ind_falsity; intros t sg; cbn.
  - reflexivity.
  - destruct P; cbn; rewrite (vec2 v); cbn; autorewrite with fsub; reflexivity.
  - now rewrite IHa, IHb.
  - destruct q; cbn; rewrite IHa; autorewrite with fsub; reflexivity.
Qed.

#[global] Hint Rewrite qtrans_subst : fsub.

Lemma idx_shift t : idx t`[↑] = S (idx t).
Proof. destruct t as [n|[]]. reflexivity. Qed.

Lemma fb_deqv n t x y : idx t < n -> idx x < n -> idx y < n -> fb n (deqv t x y).
Proof.
  destruct t as [i|[]], x as [j|[]], y as [k|[]]. intros Ht Hx Hy.
  unfold deqv, dbisim, dchild, App0, OP0, Sing0, Pair0. cbn in *. lia.
Qed.

Lemma fb_dmem n t x y : idx t < n -> idx x < n -> idx y < n -> fb n (dmem t x y).
Proof.
  destruct t as [i|[]], x as [j|[]], y as [k|[]]. intros Ht Hx Hy.
  unfold dmem, deqv, dbisim, dchild, App0, OP0, Sing0, Pair0. cbn in *. lia.
Qed.

Lemma qtrans_bounded (phi : form) : forall n t, fb n phi -> idx t < n -> fb n (qtrans t phi).
Proof.
  induction phi as [|P v|op a IHa b IHb|q a IHa] using form_ind_falsity; intros n t H Ht; cbn in *.
  - exact I.
  - destruct P; cbn in H |- *; rewrite (vec2 v) in H |- *; cbn in *.
    + apply fb_dmem; tauto.
    + apply fb_deqv; tauto.
  - destruct H as [Ha Hb]. split; [apply IHa|apply IHb]; assumption.
  - destruct q; cbn; split.
    1,3: cbn; rewrite idx_shift; lia.
    all: apply IHa; [exact H|rewrite idx_shift; lia].
Qed.

Definition KLogic : list form := KBase ++
  [forall_times 5 (kp0 (tagged_matrix (relation_selector domain_diagonal)));
   forall_times 5 (kp0 (tagged_matrix (relation_selector domain_reverse)));
   forall_times 6 (kp0 (tagged_matrix (relation_selector domain_composition)))].

Lemma KLogic_ok a : In a KLogic -> K0 a.
Proof.
  unfold KLogic. intros H. apply in_app_or in H as [H|[<-|[<-|[<-|[]]]]].
  - apply KBase_ok, H.
  - apply K0_instance, kp0_closed, tagged_matrix_bounded, relation_selector_bounded, domain_diagonal_bounded.
  - apply K0_instance, kp0_closed, tagged_matrix_bounded, relation_selector_bounded, domain_reverse_bounded.
  - apply K0_instance, kp0_closed, tagged_matrix_bounded, relation_selector_bounded, domain_composition_bounded.
Qed.

Lemma KLogic_base G : incl KLogic G -> incl KBase G.
Proof. intros H a Ha. apply H. unfold KLogic. apply in_or_app. now left. Qed.
Lemma KLogic_diag G : incl KLogic G ->
  In (forall_times 5 (kp0 (tagged_matrix (relation_selector domain_diagonal)))) G.
Proof. intros H. apply H. unfold KLogic. apply in_or_app; right; cbn; tauto. Qed.
Lemma KLogic_reverse G : incl KLogic G ->
  In (forall_times 5 (kp0 (tagged_matrix (relation_selector domain_reverse)))) G.
Proof. intros H. apply H. unfold KLogic. apply in_or_app; right; cbn; tauto. Qed.
Lemma KLogic_compose G : incl KLogic G ->
  In (forall_times 6 (kp0 (tagged_matrix (relation_selector domain_composition)))) G.
Proof. intros H. apply H. unfold KLogic. apply in_or_app; right; cbn; tauto. Qed.

Lemma KLogic_refl G (HL : incl KLogic G) t x :
  G ⊢C raw_empty t -> G ⊢C t ∈' x -> G ⊢C deqv t x x.
Proof. apply deqv_refl; [now apply KLogic_base|now apply KLogic_diag]. Qed.
Lemma KLogic_sym G (HL : incl KLogic G) t x y :
  G ⊢C raw_empty t -> G ⊢C deqv t x y -> G ⊢C deqv t y x.
Proof. apply deqv_sym; [now apply KLogic_base|now apply KLogic_reverse]. Qed.
Lemma KLogic_trans G (HL : incl KLogic G) t x y z :
  G ⊢C raw_empty t -> G ⊢C deqv t x y -> G ⊢C deqv t y z -> G ⊢C deqv t x z.
Proof. apply deqv_trans; [now apply KLogic_base|now apply KLogic_compose]. Qed.

Lemma qtrans_inv (phi : form) : forall G t (sg tau : nat -> term),
  incl KLogic G -> G ⊢C raw_empty t ->
  (forall n, G ⊢C deqv t (sg n) (tau n)) ->
  G ⊢C qtrans t phi[sg] -> G ⊢C qtrans t phi[tau].
Proof.
  induction phi as [|P v|op a IHa b IHb|q a IHa] using form_ind_falsity;
    intros G t sg tau HL Hempty Hst H.
  - exact H.
  - destruct P; cbn in v |- *; rewrite (vec2 v) in H |- *; cbn in *;
      destruct (Vector.hd v) as [n|[]]; destruct (Vector.hd (Vector.tl v)) as [m|[]]; cbn in *.
    + eapply dmem_right; [now apply KLogic_base|now apply KLogic_compose|exact Hempty|apply Hst|].
      eapply dmem_left; [now apply KLogic_base|now apply KLogic_reverse|now apply KLogic_compose|exact Hempty|apply Hst|exact H].
    + eapply KLogic_trans; [exact HL|exact Hempty| |apply Hst].
      eapply KLogic_trans; [exact HL|exact Hempty| |exact H].
      eapply KLogic_sym; [exact HL|exact Hempty|apply Hst].
  - assert (Hts : forall n, G ⊢C deqv t (tau n) (sg n)).
    { intros n. exact (KLogic_sym _ HL t _ _ Hempty (Hst n)). }
    destruct op; cbn in H |- *.
    + apply CI; [eapply IHa|eapply IHb]; eauto; [eapply CE1|eapply CE2]; exact H.
    + apply (DE H).
      * apply DI1. eapply IHa; [now apply incl_cons_r|apply weak_cons, Hempty| |apply Ctx; now left].
        intros n. apply weak_cons, Hst.
      * apply DI2. eapply IHb; [now apply incl_cons_r|apply weak_cons, Hempty| |apply Ctx; now left].
        intros n. apply weak_cons, Hst.
    + apply II. eapply IHb; [now apply incl_cons_r|apply weak_cons, Hempty| |].
      * intros n. apply weak_cons, Hst.
      * eapply IE; [apply weak_cons, H|].
        eapply IHa; [now apply incl_cons_r|apply weak_cons, Hempty| |apply Ctx; now left].
        intros n. apply weak_cons, Hts.
  - destruct q; cbn in H |- *.
    + apply AllI_named. intros z. simp. apply II.
      apply (AllE z) in H. simp_in H.
      eapply (IHa _ t (z .: sg) (z .: tau)); [now apply incl_cons_r|apply weak_cons, Hempty| |].
      * intros [|n]; cbn.
        -- eapply KLogic_refl; [now apply incl_cons_r|apply weak_cons, Hempty|apply Ctx; now left].
        -- apply weak_cons, Hst.
      * eapply IE; [apply weak_cons, H|apply Ctx; now left].
    + apply (ExE_named H). intros z. simp. apply (ExI z). simp. apply CI.
      * eapply CE1. apply Ctx. now left.
      * eapply (IHa _ t (z .: sg) (z .: tau)); [now apply incl_cons_r|apply weak_cons, Hempty| |].
        -- intros [|n]; cbn.
           ++ eapply KLogic_refl; [now apply incl_cons_r|apply weak_cons, Hempty|].
              eapply CE1. apply Ctx. now left.
           ++ apply weak_cons, Hst.
        -- eapply CE2. apply Ctx. now left.
Qed.

Lemma deqv_mixed G (HL : incl KLogic G) t x x' y y' :
  G ⊢C raw_empty t -> (x = x' \/ G ⊢C deqv t x x') ->
  (y = y' \/ G ⊢C deqv t y y') -> G ⊢C deqv t x y -> G ⊢C deqv t x' y'.
Proof.
  intros Hempty [<-|Hx] [<-|Hy] H.
  - exact H.
  - exact (KLogic_trans _ HL t x y y' Hempty H Hy).
  - pose proof (KLogic_sym _ HL t x x' Hempty Hx) as Hx'x.
    exact (KLogic_trans _ HL t x' x y Hempty Hx'x H).
  - pose proof (KLogic_sym _ HL t x x' Hempty Hx) as Hx'x.
    pose proof (KLogic_trans _ HL t x' x y Hempty Hx'x H) as Hx'y.
    exact (KLogic_trans _ HL t x' y y' Hempty Hx'y Hy).
Qed.

Lemma dmem_mixed G (HL : incl KLogic G) t x x' y y' :
  G ⊢C raw_empty t -> (x = x' \/ G ⊢C deqv t x x') ->
  (y = y' \/ G ⊢C deqv t y y') -> G ⊢C dmem t x y -> G ⊢C dmem t x' y'.
Proof.
  intros Hempty [<-|Hx] [<-|Hy] H.
  - exact H.
  - exact (dmem_right _ (KLogic_base _ HL) t x y y' (KLogic_compose _ HL) Hempty Hy H).
  - exact (dmem_left _ (KLogic_base _ HL) t x x' y (KLogic_reverse _ HL) (KLogic_compose _ HL) Hempty Hx H).
  - pose proof (dmem_left _ (KLogic_base _ HL) t x x' y (KLogic_reverse _ HL) (KLogic_compose _ HL) Hempty Hx H) as Hx'y.
    exact (dmem_right _ (KLogic_base _ HL) t x' y y' (KLogic_compose _ HL) Hempty Hy Hx'y).
Qed.

(** Fixed parameters need not be in D_t: literal equality suffices at those
    positions. The alternative is a supplied object-level bisimulation. *)
Lemma qtrans_mixed_inv (phi : form) : forall G t (sg tau : nat -> term),
  incl KLogic G -> G ⊢C raw_empty t ->
  (forall n, sg n = tau n \/ G ⊢C deqv t (sg n) (tau n)) ->
  G ⊢C qtrans t phi[sg] -> G ⊢C qtrans t phi[tau].
Proof.
  induction phi as [|P v|op a IHa b IHb|q a IHa] using form_ind_falsity;
    intros G t sg tau HL Hempty Hst H.
  - exact H.
  - destruct P; cbn in v |- *; rewrite (vec2 v) in H |- *; cbn in *;
      destruct (Vector.hd v) as [n|[]]; destruct (Vector.hd (Vector.tl v)) as [m|[]]; cbn in *.
    + exact (dmem_mixed _ HL t _ _ _ _ Hempty (Hst n) (Hst m) H).
    + exact (deqv_mixed _ HL t _ _ _ _ Hempty (Hst n) (Hst m) H).
  - assert (Hts : forall n, tau n = sg n \/ G ⊢C deqv t (tau n) (sg n)).
    { intros n. destruct (Hst n) as [E|D].
      - left. symmetry. exact E.
      - right. exact (KLogic_sym _ HL t _ _ Hempty D). }
    destruct op; cbn in H |- *.
    + apply CI; [eapply IHa|eapply IHb]; eauto; [eapply CE1|eapply CE2]; exact H.
    + apply (DE H).
      * apply DI1. eapply IHa; [now apply incl_cons_r|apply weak_cons, Hempty| |apply Ctx; now left].
        intros n. destruct (Hst n) as [E|D]; [now left|right; now apply weak_cons].
      * apply DI2. eapply IHb; [now apply incl_cons_r|apply weak_cons, Hempty| |apply Ctx; now left].
        intros n. destruct (Hst n) as [E|D]; [now left|right; now apply weak_cons].
    + apply II. eapply (IHb _ t sg tau); [now apply incl_cons_r|apply weak_cons, Hempty| |].
      * intros n. destruct (Hst n) as [E|D]; [now left|right; apply weak_cons; exact D].
      * eapply IE; [apply weak_cons, H|].
        eapply (IHa _ t tau sg); [now apply incl_cons_r|apply weak_cons, Hempty| |apply Ctx; now left].
        intros n. destruct (Hts n) as [E|D]; [now left|right; apply weak_cons; exact D].
  - destruct q; cbn in H |- *.
    + apply AllI_named. intros z. simp. apply II.
      apply (AllE z) in H. simp_in H.
      eapply (IHa _ t (z .: sg) (z .: tau)); [now apply incl_cons_r|apply weak_cons, Hempty| |].
      * intros [|n]; cbn; [left; reflexivity|].
        destruct (Hst n) as [E|D]; [now left|right; now apply weak_cons].
      * eapply IE; [apply weak_cons, H|apply Ctx; now left].
    + apply (ExE_named H). intros z. simp. apply (ExI z). simp. apply CI.
      * eapply CE1. apply Ctx. now left.
      * eapply (IHa _ t (z .: sg) (z .: tau)); [now apply incl_cons_r|apply weak_cons, Hempty| |].
        -- intros [|n]; cbn; [left; reflexivity|].
           destruct (Hst n) as [E|D]; [now left|right; now apply weak_cons].
        -- eapply CE2. apply Ctx. now left.
Qed.

Lemma qtrans_unary_inv G (HL : incl KLogic G) t phi (sg : nat -> term) x y :
  G ⊢C raw_empty t -> G ⊢C deqv t x y ->
  G ⊢C qtrans t phi[x .: sg] -> G ⊢C qtrans t phi[y .: sg].
Proof.
  intros Hempty Hxy H. eapply (qtrans_mixed_inv phi _ t (x .: sg) (y .: sg)); eauto.
  intros [|n]; cbn; [now right|left; reflexivity].
Qed.
