(** * Transfer of the relative consistency of regularity to the library's minimal signature

    minZF: only ∈ and ≡ (library FOL/Sets/minZF.v), axioms minZFeq.  We take universally closed
    axioms: ZFcl_all = { forall_times n psi | minZFeq psi } (any n) and the subset ZFcl_closed of
    those that are closed formulas.  Main result:

      (ZFcl_all + ax_reg') ⊢TC ⊥  ->  ZFcl_closed ⊢TC ⊥

    which implies the statement for every theory between ZFcl_closed and ZFcl_all.
    Route: embed into the function-symbol signature (library prv_embed / embed_ZF'), apply
    regularity_relcon (Main.v), and come back with the library's rm_const_prv / minZF_sep /
    minZF_rep. *)

From OldUndecidability.FOL Require Import Syntax.Facts Deduction.FullNDFacts.
From OldUndecidability.FOL.Sets Require Import ZF minZF.
From OldUndecidability.FOL.Reductions Require Import PCPb_to_ZF PCPb_to_minZF PCPb_to_ZFD.
From OldUndecidability.FOL.Sets.Models Require Import ZF_conservativity.
From OldUndecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations ListAutomationHints.
Require Import Lia.
From OldRegCon Require Import Rel WF Main.

Open Scope syn.

#[local] Hint Constructors prv : core.

(* ** Generic facts about universal closures *)

Section Closures.

  Context {Σ_funcs : funcs_signature} {Σ_preds : preds_signature} {p : peirce}.

  Lemma gen_closed (G : list (form falsity_on)) n chi :
    (forall b sigma, b el G -> b[sigma] = b) -> G ⊢ chi -> G ⊢ forall_times n chi.
  Proof.
    intros HG H. induction n; trivial.
    change (forall_times (S n) chi) with (∀ forall_times n chi). apply AllI.
    erewrite map_ext_in, map_id; trivial. intros b Hb. now apply HG.
  Qed.

  Lemma up_shift_var0 (phi : form falsity_on) : phi[up ↑][$0..] = phi.
  Proof. rewrite subst_comp. apply subst_id. now intros []. Qed.

  Lemma all_shift (G : list (form falsity_on)) phi : G ⊢ ∀ phi -> map (subst_form ↑) G ⊢ phi.
  Proof.
    intros H. apply (subst_Weak ↑) in H. cbn in H. apply (AllE $0) in H.
    now rewrite up_shift_var0 in H.
  Qed.

  Lemma forall_times_mp (G : list (form falsity_on)) n X Y :
    G ⊢ forall_times n (X → Y) -> G ⊢ forall_times n X -> G ⊢ forall_times n Y.
  Proof.
    induction n in G |- *; intros H1 H2.
    - eapply IE; eassumption.
    - change (forall_times (S n) Y) with (∀ forall_times n Y). apply AllI.
      apply IHn; now apply all_shift.
  Qed.

  Lemma forall_times_inst (G : list (form falsity_on)) n chi :
    G ⊢ forall_times n chi -> bounded n chi -> G ⊢ chi.
  Proof.
    intros H Hb. rewrite <- (subst_var chi). now apply (subst_forall_prv H Hb).
  Qed.

  Lemma ft_bounded n k (theta : form falsity_on) : bounded (k + n) theta -> bounded k (forall_times n theta).
  Proof.
    induction n in k |- *; intros H.
    - now rewrite PeanoNat.Nat.add_0_r in H.
    - change (forall_times (S n) theta) with (∀ forall_times n theta). constructor.
      apply IHn. now rewrite PeanoNat.Nat.add_succ_r in H.
  Qed.

  Lemma ft_closed n (theta : form falsity_on) : bounded n theta -> bounded 0 (forall_times n theta).
  Proof. intros H. now apply ft_bounded. Qed.

End Closures.

(* ** The theories in the minimal signature *)

Notation form' := (@form sig_empty ZF_pred_sig _ falsity_on).

Definition ax_reg' : form' :=
  ∀ (∃ $0 ∈' $1) → ∃ ($0 ∈' $1 ∧ ∀ ($0 ∈' $1 → ¬ ($0 ∈' $2))).

Definition ZFcl_all (phi : form') : Prop := exists n psi, minZFeq psi /\ phi = forall_times n psi.
Definition ZFcl_closed (phi : form') : Prop := ZFcl_all phi /\ bounded 0 phi.
(* The smallest theory we need on the conclusion side: the finite axioms and the closed closures
   of the schema instances. *)
Definition ZFcl_min (phi : form') : Prop :=
  phi el minZFeq' \/ (exists n psi, phi = forall_times n (ax_sep' psi) /\ bounded 0 phi)
                  \/ (exists n psi, phi = forall_times n (ax_rep' psi) /\ bounded 0 phi).
Definition ZFclReg (phi : form') : Prop := ZFcl_all phi \/ phi = ax_reg'.

#[local] Instance sig_empty_dec : eq_dec sig_empty.
Proof. intros []. Defined.

#[local] Instance ZF_preds_dec'' : eq_dec ZF_pred_sig.
Proof. intros x y. unfold dec. decide equality. Defined.

#[local] Instance ZF_funcs_dec'' : eq_dec ZF_func_sig.
Proof. intros x y. unfold dec. decide equality. Defined.

Lemma minZFeq'_closed b sigma : b el minZFeq' -> b[sigma] = b.
Proof.
  intros Hb. apply bounded_0_subst. unfold minZFeq', minZF' in Hb.
  repeat (destruct Hb as [<-|Hb]; [apply bounded_comp_eq; compute; repeat split; lia |]). destruct Hb.
Qed.

Lemma ZFeq'_closed b sigma : b el ZFeq' -> b[sigma] = b.
Proof. intros Hb. apply B0_closed. unfold B0. apply in_app_iff. now left. Qed.

(* ** Syntactic commutation lemmas *)

Lemma embed_forall_times n (psi : form') : embed (forall_times n psi) = forall_times n (embed psi).
Proof.
  induction n; [reflexivity |]. change (forall_times (S n) psi) with (∀ forall_times n psi).
  change (forall_times (S n) (embed psi)) with (∀ forall_times n (embed psi)). cbn. now rewrite IHn.
Qed.

Lemma rm_const_forall_times n (phi : form) : rm_const_fm (forall_times n phi) = forall_times n (rm_const_fm phi).
Proof.
  induction n; [reflexivity |]. change (forall_times (S n) phi) with (∀ forall_times n phi).
  change (forall_times (S n) (rm_const_fm phi)) with (∀ forall_times n (rm_const_fm phi)). cbn. now rewrite IHn.
Qed.

Lemma embed_sep (phi : form') : embed (ax_sep' phi) = ax_sep (embed phi).
Proof.
  cbn. unfold ax_sep. rewrite embed_subst. erewrite subst_ext; try reflexivity. now intros [|n].
Qed.

Lemma embed_rep (phi : form') : embed (ax_rep' phi) = ax_rep (embed phi).
Proof.
  cbn. unfold ax_rep, fun_rel. rewrite !embed_subst.
  setoid_rewrite subst_ext at 1. setoid_rewrite subst_ext at 2.
  setoid_rewrite subst_ext at 3. setoid_rewrite subst_ext at 4. reflexivity.
  all: now intros [|[|n]].
Qed.

Lemma embed_reg : embed ax_reg' = ax_reg.
Proof. reflexivity. Qed.

(* ** Step 1: from the minimal signature to the rich one *)

Lemma closed_list_app {ff : falsity_flag} {Σf : funcs_signature} (A B : list (@form Σf ZF_pred_sig _ ff)) :
  (forall b sigma, b el A -> b[sigma] = b) -> (forall b sigma, b el B -> b[sigma] = b) ->
  forall b sigma, b el A ++ B -> b[sigma] = b.
Proof. intros HA HB b sigma [H|H]%in_app_iff; auto. Qed.

Lemma embed_axiom_ZF a : ZFcl_all a ->
  exists L, (forall b, b el L -> ZFc b) /\ L ⊢C embed a.
Proof.
  intros (n & psi & H & ->). rewrite embed_forall_times. destruct H as [psi H | psi | psi].
  - exists ZFeq'. split; [intros b Hb; now apply ZFc_base |].
    apply gen_closed; [apply ZFeq'_closed | now apply embed_ZF'].
  - rewrite embed_sep. destruct (find_bounded (ax_sep (embed psi))) as [k Hk].
    exists [forall_times k (ax_sep (embed psi))]. split.
    + intros b [<-|[]]. now apply ZFc_sep.
    + apply gen_closed.
      * intros b sigma [<-|[]]. now apply bounded_0_subst, ft_closed.
      * apply (forall_times_inst (n := k)); [apply Ctx; now left | exact Hk].
  - rewrite embed_rep. destruct (find_bounded (ax_rep (embed psi))) as [k Hk].
    exists [forall_times k (ax_rep (embed psi))]. split.
    + intros b [<-|[]]. now apply ZFc_rep.
    + apply gen_closed.
      * intros b sigma [<-|[]]. now apply bounded_0_subst, ft_closed.
      * apply (forall_times_inst (n := k)); [apply Ctx; now left | exact Hk].
Qed.

Lemma embed_axiom a : ZFclReg a ->
  exists L, (forall b, b el L -> ZFcReg b) /\ L ⊢C embed a.
Proof.
  intros [(n & psi & H & ->) | ->].
  - rewrite embed_forall_times. destruct H as [psi H | psi | psi].
    + exists ZFeq'. split; [intros b Hb; now apply ZFcReg_ZF, ZFc_base |].
      apply gen_closed; [apply ZFeq'_closed | now apply embed_ZF'].
    + rewrite embed_sep. destruct (find_bounded (ax_sep (embed psi))) as [k Hk].
      exists [forall_times k (ax_sep (embed psi))]. split.
      * intros b [<-|[]]. now apply ZFcReg_ZF, ZFc_sep.
      * apply gen_closed.
        -- intros b sigma [<-|[]]. now apply bounded_0_subst, ft_closed.
        -- apply (forall_times_inst (n := k)); [apply Ctx; now left | exact Hk].
    + rewrite embed_rep. destruct (find_bounded (ax_rep (embed psi))) as [k Hk].
      exists [forall_times k (ax_rep (embed psi))]. split.
      * intros b [<-|[]]. now apply ZFcReg_ZF, ZFc_rep.
      * apply gen_closed.
        -- intros b sigma [<-|[]]. now apply bounded_0_subst, ft_closed.
        -- apply (forall_times_inst (n := k)); [apply Ctx; now left | exact Hk].
  - exists [ax_reg]. split; [intros b [<-|[]]; apply ZFcReg_reg | rewrite embed_reg; apply Ctx; now left].
Qed.

Lemma collect {X Y : Type} (Q : Y -> Prop) (R : list Y -> X -> Prop) A :
  (forall L L' x, R L x -> L <<= L' -> R L' x) ->
  (forall a, a el A -> exists L, (forall b, b el L -> Q b) /\ R L a) ->
  exists L, (forall b, b el L -> Q b) /\ forall a, a el A -> R L a.
Proof.
  intros Hmono. induction A as [|a A IH]; intros HA.
  - exists []. split; [intros b [] | intros a' []].
  - destruct (HA a (or_introl eq_refl)) as [L1 [H1 H2]].
    destruct IH as [L2 [H3 H4]]; [intros b Hb; apply HA; now right |].
    exists (L1 ++ L2). split.
    + intros b [Hb|Hb]%in_app_iff; auto.
    + intros b [<-|Hb]; eapply Hmono; eauto.
Qed.

Lemma step1 : ZFclReg ⊢TC ⊥ -> ZFcReg ⊢TC ⊥.
Proof.
  intros [A [HA H]]. apply prv_embed in H.
  destruct (collect (R := fun L (a : form') => L ⊢C embed a) (Q := ZFcReg) (A := A)) as [L [HL1 HL2]].
  - intros L L' x Hx HL. apply (Weak Hx HL).
  - intros a Ha. now apply embed_axiom, HA.
  - exists L. split; trivial. apply (prv_cut H). intros psi [a [<- Ha]]%in_map_iff. now apply HL2.
Qed.

(* ** Step 3: from the rich signature back to the minimal one *)

Lemma closed_ZFcl n psi : minZFeq psi -> bounded n psi -> ZFcl_closed (forall_times n psi).
Proof. intros H Hb. split; [now exists n, psi | now apply ft_closed]. Qed.

Lemma minZFeq'_bounded psi : psi el minZFeq' -> bounded 0 psi.
Proof.
  intros Hb. unfold minZFeq', minZF' in Hb.
  repeat (destruct Hb as [<-|Hb]; [apply bounded_comp_eq; compute; repeat split; lia |]). destruct Hb.
Qed.

Lemma rm_const_axiom a : ZFc a ->
  exists L, (forall b, b el L -> ZFcl_min b) /\ L ⊢C rm_const_fm a.
Proof.
  assert (Hbase : forall b, b el minZFeq' -> ZFcl_min b) by (intros b Hb; now left).
  intros [phi H | phi n Hb | phi n Hb].
  - exists minZFeq'. split; trivial. now apply prv_to_min.
  - rewrite rm_const_forall_times. destruct (find_bounded (ax_sep' (rm_const_fm phi))) as [k Hk].
    exists (forall_times k (ax_sep' (rm_const_fm phi)) :: minZFeq'). split.
    + intros b [<-|Hb']; [| now apply Hbase]. right. left. eexists _, _. split; [reflexivity | now apply ft_closed].
    + apply gen_closed.
      * intros b sigma [<-|Hb']; [| now apply minZFeq'_closed].
        now apply bounded_0_subst, ft_closed.
      * eapply IE; [apply minZF_sep; auto |].
        apply (forall_times_inst (n := k)); [apply Ctx; now left | exact Hk].
  - rewrite rm_const_forall_times. destruct (find_bounded (ax_rep' (rm_const_fm phi))) as [k Hk].
    exists (forall_times k (ax_rep' (rm_const_fm phi)) :: minZFeq'). split.
    + intros b [<-|Hb']; [| now apply Hbase]. right. right. eexists _, _. split; [reflexivity | now apply ft_closed].
    + apply gen_closed.
      * intros b sigma [<-|Hb']; [| now apply minZFeq'_closed].
        now apply bounded_0_subst, ft_closed.
      * eapply IE; [apply minZF_rep; auto |].
        apply (forall_times_inst (n := k)); [apply Ctx; now left | exact Hk].
Qed.

Lemma step3 : ZFc ⊢TC ⊥ -> ZFcl_min ⊢TC ⊥.
Proof.
  intros [A [HA H]]. assert (H' : (A ++ ZFeq') ⊢C ⊥) by (apply (Weak H); auto).
  apply rm_const_prv in H'. cbn in H'.
  destruct (collect (R := fun L (a : form) => L ⊢C rm_const_fm a) (Q := ZFcl_min) (A := A)) as [L [HL1 HL2]].
  - intros L L' x Hx HL. apply (Weak Hx HL).
  - intros a Ha. now apply rm_const_axiom, HA.
  - exists (L ++ minZFeq'). split.
    + intros b [Hb|Hb]%in_app_iff; [now apply HL1 | now left].
    + apply (prv_cut H'). intros psi [[a [<- Ha]]%in_map_iff | Hb]%in_app_iff.
      * apply (Weak (HL2 a Ha)). auto.
      * apply Ctx. auto.
Qed.

(* ** Main theorem in the minimal signature *)

Theorem regularity_relcon_min : ZFclReg ⊢TC ⊥ -> ZFcl_min ⊢TC ⊥.
Proof. intros H. now apply step3, regularity_relcon, step1. Qed.

(* Any axiomatization T between ZFcl_min and ZFcl_all works, e.g. ZFcl_closed or ZFcl_all. *)
Corollary regularity_relcon_min' (T : form' -> Prop) :
  (forall phi, ZFcl_min phi -> T phi) -> (forall phi, T phi -> ZFcl_all phi) ->
  (fun phi => T phi \/ phi = ax_reg') ⊢TC ⊥ -> T ⊢TC ⊥.
Proof.
  intros H1 H2 H. apply (Weak_T (T1 := ZFcl_min)); [| intros phi Hphi; now apply H1].
  apply regularity_relcon_min. apply (Weak_T H). intros phi [Hphi | ->]; [left; now apply H2 | now right].
Qed.

Lemma ZFcl_min_closed phi : ZFcl_min phi -> ZFcl_closed phi.
Proof.
  intros [H | [(n & psi & -> & Hb) | (n & psi & -> & Hb)]].
  - split; [exists 0, phi; split; [now constructor | reflexivity] | now apply minZFeq'_bounded].
  - split; [exists n, (ax_sep' psi); split; [apply minZFeq_sep | reflexivity] | exact Hb].
  - split; [exists n, (ax_rep' psi); split; [apply minZFeq_rep | reflexivity] | exact Hb].
Qed.

Corollary regularity_relcon_closed : (fun phi => ZFcl_closed phi \/ phi = ax_reg') ⊢TC ⊥ -> ZFcl_closed ⊢TC ⊥.
Proof. apply regularity_relcon_min'; [apply ZFcl_min_closed | now intros phi []]. Qed.

Corollary regularity_relcon_all : ZFclReg ⊢TC ⊥ -> ZFcl_all ⊢TC ⊥.
Proof. apply regularity_relcon_min'; [intros phi H; apply ZFcl_min_closed, H | trivial]. Qed.

(* ** Bridge between the closed theories in the two signatures *)

Lemma bridge_to_rich : ZFcl_all ⊢TC ⊥ -> ZFc ⊢TC ⊥.
Proof.
  intros [A [HA H]]. apply prv_embed in H.
  destruct (collect (R := fun L (a : form') => L ⊢C embed a) (Q := ZFc) (A := A)) as [L [HL1 HL2]].
  - intros L L' x Hx HL. apply (Weak Hx HL).
  - intros a Ha. now apply embed_axiom_ZF, HA.
  - exists L. split; trivial. apply (prv_cut H). intros psi [a [<- Ha]]%in_map_iff. now apply HL2.
Qed.

Theorem bridge (T : form' -> Prop) :
  (forall phi, ZFcl_min phi -> T phi) -> (forall phi, T phi -> ZFcl_all phi) ->
  T ⊢TC ⊥ <-> ZFc ⊢TC ⊥.
Proof.
  intros H1 H2. split; intros H.
  - apply bridge_to_rich, (Weak_T H). exact H2.
  - apply (Weak_T (step3 H)). exact H1.
Qed.

Theorem bridge_reg (T : form' -> Prop) :
  (forall phi, ZFcl_min phi -> T phi) -> (forall phi, T phi -> ZFcl_all phi) ->
  (fun phi => T phi \/ phi = ax_reg') ⊢TC ⊥ <-> ZFcReg ⊢TC ⊥.
Proof.
  intros H1 H2. split; intros H.
  - apply step1, (Weak_T H). intros phi [Hphi | ->]; [left; now apply H2 | now right].
  - apply regularity_relcon in H. apply (Weak_T (step3 H)). intros phi Hphi. left. now apply H1.
Qed.
