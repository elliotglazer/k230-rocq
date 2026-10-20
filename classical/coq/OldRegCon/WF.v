(** * The class WF of well-founded sets, and derived rules for it

    WF(x) :<-> exists t, t transitive, t well-founded (every nonempty subset has an
    ∈-minimal element), and x ∈ t.

    All derivations are classical natural deduction over the library's ZF signature. *)

Require Import OldUndecidability.FOL.ZF.
Require Import OldUndecidability.FOL.Syntax.Facts.
Require Import OldUndecidability.FOL.Sets.ZF.
Require Import OldUndecidability.FOL.Reductions.PCPb_to_ZFD.
From OldUndecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations ListAutomationHints.
Require Import Lia.

#[local] Hint Constructors prv : core.
#[local] Instance pc : peirce := class.

Open Scope syn.

(* ** Formula builders *)

Definition transitive (x : term) : form := ∀ ($0 ∈ x`[↑] → sub $0 x`[↑]).
Definition nonempty (s : term) : form := ∃ ($0 ∈ s`[↑]).
Definition minel (m s : term) : form := m ∈ s ∧ ∀ ($0 ∈ m`[↑] → ¬ ($0 ∈ s`[↑])).
Definition minimal (s : term) : form := ∃ minel $0 s`[↑].
Definition wellf (t : term) : form := ∀ (sub $0 t`[↑] → nonempty $0 → minimal $0).
Definition tw (t : term) : form := transitive t ∧ wellf t.
Definition WF (x : term) : form := ∃ (tw $0 ∧ x`[↑] ∈ $0).

Arguments sub : simpl never.
Arguments transitive : simpl never.
Arguments nonempty : simpl never.
Arguments minel : simpl never.
Arguments minimal : simpl never.
Arguments wellf : simpl never.
Arguments tw : simpl never.
Arguments WF : simpl never.

Lemma sub_subst x y sigma : (sub x y)[sigma] = sub x`[sigma] y`[sigma].
Proof. unfold sub. cbn. now rewrite !up_term. Qed.

Lemma transitive_subst x sigma : (transitive x)[sigma] = transitive x`[sigma].
Proof. unfold transitive. cbn. rewrite sub_subst. cbn. now rewrite up_term. Qed.

Lemma nonempty_subst x sigma : (nonempty x)[sigma] = nonempty x`[sigma].
Proof. unfold nonempty. cbn. now rewrite up_term. Qed.

Lemma minel_subst m s sigma : (minel m s)[sigma] = minel m`[sigma] s`[sigma].
Proof. unfold minel. cbn. now rewrite !up_term. Qed.

Lemma minimal_subst s sigma : (minimal s)[sigma] = minimal s`[sigma].
Proof. unfold minimal. cbn. rewrite minel_subst. cbn. now rewrite up_term. Qed.

Lemma wellf_subst t sigma : (wellf t)[sigma] = wellf t`[sigma].
Proof. unfold wellf. cbn. rewrite sub_subst, nonempty_subst, minimal_subst. cbn. now rewrite up_term. Qed.

Lemma tw_subst t sigma : (tw t)[sigma] = tw t`[sigma].
Proof. unfold tw. cbn. now rewrite transitive_subst, wellf_subst. Qed.

Lemma WF_subst x sigma : (WF x)[sigma] = WF x`[sigma].
Proof. unfold WF. cbn. rewrite tw_subst. cbn. now rewrite up_term. Qed.

#[export] Hint Rewrite sub_subst transitive_subst nonempty_subst minel_subst minimal_subst
  wellf_subst tw_subst WF_subst : wfsubst.

Ltac simp := cbn; autorewrite with wfsubst; cbn; subsimpl.
Ltac simp_in H := cbn in H; autorewrite with wfsubst in H; cbn in H; subsimpl_in H.

(* ** Generic list-context helpers *)

Lemma prv_weak1 T phi psi : T ⊢ phi -> (psi :: T) ⊢ phi.
Proof. intros H. apply (Weak H). auto. Qed.

Lemma conj_split T phi psi chi : (phi :: psi :: T) ⊢ chi -> (phi ∧ psi :: T) ⊢ chi.
Proof.
  intros H. apply (prv_cut H). intros a [<-|[<-|Ha]].
  - eapply CE1, Ctx. auto.
  - eapply CE2, Ctx. auto.
  - apply Ctx. auto.
Qed.

(* ** Introduction and elimination rules for the builders *)


Lemma sub_intro T x y : (forall z, (z ∈ x :: T) ⊢ z ∈ y) -> T ⊢ sub x y.
Proof. intros H. unfold sub. apply AllI_named. intros z. simp. apply II, H. Qed.

Lemma sub_elim T x y z : T ⊢ sub x y -> T ⊢ z ∈ x -> T ⊢ z ∈ y.
Proof. intros H1 H2. unfold sub in H1. apply (AllE z) in H1. simp_in H1. eapply IE; eassumption. Qed.

Lemma trans_intro T x : (forall y z, (z ∈ y :: y ∈ x :: T) ⊢ z ∈ x) -> T ⊢ transitive x.
Proof.
  intros H. unfold transitive. apply AllI_named. intros y. simp.
  apply II. apply sub_intro. intros z. apply H.
Qed.

Lemma trans_elim T x y z : T ⊢ transitive x -> T ⊢ y ∈ x -> T ⊢ z ∈ y -> T ⊢ z ∈ x.
Proof.
  intros H1 H2 H3. unfold transitive in H1. apply (AllE y) in H1. simp_in H1.
  eapply sub_elim; [eapply IE; eassumption | exact H3].
Qed.

Lemma ne_intro T s w : T ⊢ w ∈ s -> T ⊢ nonempty s.
Proof. intros H. unfold nonempty. apply (ExI w). simp. exact H. Qed.

Lemma ne_elim T s phi : T ⊢ nonempty s -> (forall w, (w ∈ s :: T) ⊢ phi) -> T ⊢ phi.
Proof. intros H1 H2. unfold nonempty in H1. apply (ExE_named H1). intros w. simp. apply H2. Qed.

Lemma minel_intro T m s : T ⊢ m ∈ s -> (forall z, (z ∈ s :: z ∈ m :: T) ⊢ ⊥) -> T ⊢ minel m s.
Proof.
  intros H1 H2. unfold minel. apply CI; trivial.
  apply AllI_named. intros z. simp. apply II, II. apply H2.
Qed.

Lemma minel_el T m s : T ⊢ minel m s -> T ⊢ m ∈ s.
Proof. intros H. unfold minel in H. eapply CE1, H. Qed.

Lemma minel_min T m s z : T ⊢ minel m s -> T ⊢ z ∈ m -> T ⊢ z ∈ s -> T ⊢ ⊥.
Proof.
  intros H1 H2 H3. unfold minel in H1. apply CE2, (AllE z) in H1. simp_in H1.
  eapply IE; [eapply IE|]; eassumption.
Qed.

Lemma min_intro T m s : T ⊢ minel m s -> T ⊢ minimal s.
Proof. intros H. unfold minimal. apply (ExI m). simp. exact H. Qed.

Lemma min_elim T s phi : T ⊢ minimal s -> (forall m, (minel m s :: T) ⊢ phi) -> T ⊢ phi.
Proof. intros H1 H2. unfold minimal in H1. apply (ExE_named H1). intros m. simp. apply H2. Qed.

Lemma wf_intro T t : (forall s w, (w ∈ s :: sub s t :: T) ⊢ minimal s) -> T ⊢ wellf t.
Proof.
  intros H. unfold wellf. apply AllI_named. intros s. simp.
  apply II, II. eapply ne_elim; [apply Ctx; auto |]. intros w.
  apply (Weak (H s w)). intros a [<-|[<-|Ha]]; auto.
Qed.

Lemma wf_elim T t s w : T ⊢ wellf t -> T ⊢ sub s t -> T ⊢ w ∈ s -> T ⊢ minimal s.
Proof.
  intros H1 H2 H3. unfold wellf in H1. apply (AllE s) in H1. simp_in H1.
  eapply IE; [eapply IE|]; [exact H1 | exact H2 | eapply ne_intro, H3].
Qed.

Lemma tw_intro T t : T ⊢ transitive t -> T ⊢ wellf t -> T ⊢ tw t.
Proof. intros H1 H2. unfold tw. now apply CI. Qed.

Lemma tw_trans T t : T ⊢ tw t -> T ⊢ transitive t.
Proof. intros H. unfold tw in H. eapply CE1, H. Qed.

Lemma tw_wf T t : T ⊢ tw t -> T ⊢ wellf t.
Proof. intros H. unfold tw in H. eapply CE2, H. Qed.

Lemma WF_intro T x t : T ⊢ tw t -> T ⊢ x ∈ t -> T ⊢ WF x.
Proof. intros H1 H2. unfold WF. apply (ExI t). simp. now apply CI. Qed.

Lemma WF_elim T x phi : T ⊢ WF x -> (forall t, (tw t :: x ∈ t :: T) ⊢ phi) -> T ⊢ phi.
Proof.
  intros H1 H2. unfold WF in H1. apply (ExE_named H1). intros t. simp.
  apply conj_split, H2.
Qed.

(* ** Basic facts about WF *)

Lemma ctx1 T phi : (phi :: T) ⊢ phi.
Proof. apply Ctx. auto. Qed.

Lemma ctx2 T phi psi : (psi :: phi :: T) ⊢ phi.
Proof. apply Ctx. auto. Qed.

Lemma ctx3 T phi psi chi : (chi :: psi :: phi :: T) ⊢ phi.
Proof. apply Ctx. auto. Qed.

Lemma ctx4 T phi psi chi th : (th :: chi :: psi :: phi :: T) ⊢ phi.
Proof. apply Ctx. auto. Qed.

#[export] Hint Resolve ctx1 ctx2 ctx3 ctx4 : core.

Ltac wk H := apply (Weak H); auto.

Lemma WF_el T x y : T ⊢ WF x -> T ⊢ y ∈ x -> T ⊢ WF y.
Proof.
  intros H1 H2. apply (WF_elim H1). intros t. apply WF_intro with t; auto.
  eapply trans_elim; [apply tw_trans; auto | auto | wk H2].
Qed.

Lemma WF_eq T x y : ZFeq' <<= T -> T ⊢ WF x -> T ⊢ y ≡ x -> T ⊢ WF y.
Proof.
  intros HT H1 H2. apply (WF_elim H1). intros t. apply WF_intro with t; auto.
  eapply ZF_eq_elem; [auto | | apply ZF_refl'; auto | apply ctx2].
  apply ZF_sym'; [auto | wk H2].
Qed.

Lemma wf_sub T t u : T ⊢ wellf t -> T ⊢ sub u t -> T ⊢ wellf u.
Proof.
  intros H1 H2. apply wf_intro. intros s w. apply wf_elim with t w; auto.
  - wk H1.
  - apply sub_intro. intros z. apply sub_elim with u; [wk H2 |].
    apply sub_elim with s; auto.
Qed.

(* ** The class as a formula with one free variable *)

#[local] Instance ZF_funcs_dec : eq_dec ZF_func_sig.
Proof. intros x y. unfold dec. decide equality. Defined.

#[local] Instance ZF_preds_dec : eq_dec ZF_pred_sig.
Proof. intros x y. unfold dec. decide equality. Defined.

Definition Mwf : form := WF $0.

Lemma Mwf_bounded : bounded 1 Mwf.
Proof.
  apply bounded_comp_eq. unfold Mwf, WF, tw, transitive, wellf, sub, nonempty, minimal, minel.
  cbn. repeat split; lia.
Qed.

Lemma Mwf_inst t : Mwf[t..] = WF t.
Proof. unfold Mwf. now simp. Qed.

(* ** Using separation and replacement instances *)

Lemma cut_with T G a b : G ⊢ a -> (a :: T) ⊢ b -> T <<= G -> G ⊢ b.
Proof. intros H1 H2 H3. eapply IE; [| exact H1]. apply (Weak (II H2) H3). Qed.

Definition sepspec (Z X : term) (phi : form) : form := ∀ ($0 ∈ Z`[↑] ↔ $0 ∈ X`[↑] ∧ phi).
Arguments sepspec : simpl never.

Lemma sep_norm (phi : form) X Z :
  phi[$0 .: Nat.add 3 >> var][up (up (X..))][up (Z..)] = phi.
Proof. rewrite !subst_comp. apply subst_id. intros [|j]; reflexivity. Qed.

Lemma sep_elim T phi X psi : T ⊢ ax_sep phi -> (forall Z, (sepspec Z X phi :: T) ⊢ psi) -> T ⊢ psi.
Proof.
  intros H1 H2. unfold ax_sep in H1. apply (AllE X) in H1. cbn in H1.
  apply (ExE_named H1). intros Z. specialize (H2 Z). unfold sepspec in H2. cbn in *.
  rewrite sep_norm. subsimpl. exact H2.
Qed.

Lemma sep_in T Z X phi V : T ⊢ sepspec Z X phi -> T ⊢ V ∈ Z -> T ⊢ V ∈ X ∧ phi[V..].
Proof.
  intros H1 H2. unfold sepspec in H1. apply (AllE V) in H1. cbn in H1. subsimpl_in H1.
  eapply IE; [eapply CE1, H1 | exact H2].
Qed.

Lemma sep_out T Z X phi V : T ⊢ sepspec Z X phi -> T ⊢ V ∈ X -> T ⊢ phi[V..] -> T ⊢ V ∈ Z.
Proof.
  intros H1 H2 H3. unfold sepspec in H1. apply (AllE V) in H1. cbn in H1. subsimpl_in H1.
  eapply IE; [eapply CE2, H1 | now apply CI].
Qed.

Lemma ax_sep_subst phi sigma : (ax_sep phi)[sigma] = ax_sep (phi[up sigma]).
Proof.
  unfold ax_sep. cbn [subst_form]. assert (E : phi[$0 .: Nat.add 3 >> var][up (up (up sigma))] =
    phi[up sigma][$0 .: Nat.add 3 >> var]).
  { rewrite !subst_comp. apply subst_ext. intros [|j]; cbn; trivial.
    unfold funcomp. rewrite !subst_term_comp. apply subst_term_ext. reflexivity. }
  rewrite E. reflexivity.
Qed.

Definition repspec (Z X : term) (phi : form) : form := ∀ ($0 ∈ Z`[↑] ↔ ∃ ($0 ∈ X`[↑]`[↑] ∧ phi)).
Arguments repspec : simpl never.

Lemma rep_norm (phi : form) X Z :
  phi[$0 .: $1 .: Nat.add 4 >> var][up (up (up (X..)))][up (up (Z..))] = phi.
Proof. rewrite !subst_comp. apply subst_id. intros [|[|j]]; reflexivity. Qed.

Lemma rep_elim T phi X psi : T ⊢ ax_rep phi -> T ⊢ fun_rel phi ->
  (forall Z, (repspec Z X phi :: T) ⊢ psi) -> T ⊢ psi.
Proof.
  intros H1 H0 H2. unfold ax_rep in H1. pose proof (IE H1 H0) as H3. clear H1. rename H3 into H1.
  apply (AllE X) in H1. cbn in H1.
  apply (ExE_named H1). intros Z. specialize (H2 Z). unfold repspec in H2. cbn in *.
  rewrite rep_norm. subsimpl. exact H2.
Qed.

Lemma rep_inst_norm (phi : form) U V : phi[up (U..)][V..] = phi[V .: U..].
Proof. rewrite subst_comp. apply subst_ext. intros [|j]; cbn; trivial. apply subst_term_shift. Qed.

Lemma rep_in T Z X phi U psi : T ⊢ repspec Z X phi -> T ⊢ U ∈ Z ->
  (forall V, (V ∈ X :: phi[V .: U..] :: T) ⊢ psi) -> T ⊢ psi.
Proof.
  intros H1 H2 H3. unfold repspec in H1. apply (AllE U) in H1. cbn in H1. subsimpl_in H1.
  pose proof (IE (CE1 H1) H2) as H4. apply (ExE_named H4). intros V. cbn. subsimpl.
  rewrite rep_inst_norm. apply conj_split. apply (Weak (H3 V)). intros a [<-|[<-|Ha]]; auto.
Qed.

Lemma rep_out T Z X phi U V : T ⊢ repspec Z X phi -> T ⊢ V ∈ X -> T ⊢ phi[V .: U..] -> T ⊢ U ∈ Z.
Proof.
  intros H1 H2 H3. unfold repspec in H1. apply (AllE U) in H1. cbn in H1. subsimpl_in H1.
  eapply IE; [eapply CE2, H1 |]. apply (ExI V). cbn. subsimpl. rewrite rep_inst_norm. now apply CI.
Qed.

Ltac term_eq := unfold funcomp; rewrite ?subst_term_comp;
  first [reflexivity | apply subst_term_id; intros; reflexivity
        | apply subst_term_ext; intros; cbn; rewrite ?subst_term_comp; reflexivity].

Lemma fun_rel_intro T phi :
  (forall X Y Y', (phi[X .: Y'..] :: phi[X .: Y..] :: T) ⊢ Y ≡ Y') -> T ⊢ fun_rel phi.
Proof.
  intros H. unfold fun_rel. apply AllI_named. intros X. cbn. apply AllI_named. intros Y. cbn.
  apply AllI_named. intros Y'. cbn. subsimpl. apply II, II.
  assert (E : forall Y0, phi[$2 .: Y0 .: Nat.add 3 >> var][up (up (X..))][up (Y..)][Y'..] = phi[X .: (Y0`[up (up (X..))]`[up (Y..)]`[Y'..])..]).
  { intros Y0. rewrite !subst_comp. apply subst_ext. intros [|[|j]]; cbn; trivial; term_eq. }
  rewrite !E. cbn. subsimpl. apply H.
Qed.

Lemma ax_rep_subst phi sigma : (ax_rep phi)[sigma] = ax_rep (phi[up (up sigma)]).
Proof.
  unfold ax_rep, fun_rel. cbn [subst_form].
  assert (E1 : forall a b, phi[a .: b .: Nat.add 3 >> var][up (up (up sigma))] =
    phi[up (up sigma)][a`[up (up (up sigma))] .: b`[up (up (up sigma))] .: Nat.add 3 >> var]).
  { intros a b. rewrite !subst_comp. apply subst_ext. intros [|[|j]]; cbn; trivial.
    unfold funcomp. rewrite !subst_term_comp. apply subst_term_ext. reflexivity. }
  assert (E2 : phi[$0 .: $1 .: Nat.add 4 >> var][up (up (up (up sigma)))] =
    phi[up (up sigma)][$0 .: $1 .: Nat.add 4 >> var]).
  { rewrite !subst_comp. apply subst_ext. intros [|[|j]]; cbn; trivial.
    unfold funcomp. rewrite !subst_term_comp. apply subst_term_ext. reflexivity. }
  rewrite !E1, E2. reflexivity.
Qed.

(* ** Union, power set, infinity *)

Lemma ax_in T phi : phi el T -> T ⊢ phi.
Proof. intros H. now apply Ctx. Qed.

Lemma union_elim T x z phi : ZFeq' <<= T -> T ⊢ z ∈ ⋃ x ->
  (forall y, (y ∈ x :: z ∈ y :: T) ⊢ phi) -> T ⊢ phi.
Proof.
  intros HT H1 H2. assert (HU : T ⊢ ax_union) by (apply ax_in, HT; cbn; tauto).
  unfold ax_union in HU. apply (AllE x), (AllE z) in HU. cbn in HU. subsimpl_in HU.
  pose proof (IE (CE1 HU) H1) as H3. apply (ExE_named H3). intros y. cbn. subsimpl.
  apply conj_split, H2.
Qed.

Lemma power_el T x z : ZFeq' <<= T -> T ⊢ z ∈ PP x -> T ⊢ sub z x.
Proof.
  intros HT H. assert (HP : T ⊢ ax_power) by (apply ax_in, HT; cbn; tauto).
  unfold ax_power in HP. apply (AllE x), (AllE z) in HP. simp_in HP.
  eapply IE; [eapply CE1, HP | exact H].
Qed.

(* ** Canonical transitive well-founded witnesses *)

Definition chi (y v : term) : form := ∀ (transitive $0 → y`[↑] ∈ $0 → v`[↑] ∈ $0).
Definition canon (y u : term) : form :=
  transitive u ∧ (y ∈ u ∧ ∀ ($0 ∈ u`[↑] → chi y`[↑] $0)).
Definition canonw (y u : term) : form := canon y u ∧ wellf u.
Arguments chi : simpl never.
Arguments canon : simpl never.
Arguments canonw : simpl never.

Lemma chi_subst y v sigma : (chi y v)[sigma] = chi y`[sigma] v`[sigma].
Proof. unfold chi. cbn. rewrite transitive_subst. cbn. now rewrite !up_term. Qed.

Lemma canon_subst y u sigma : (canon y u)[sigma] = canon y`[sigma] u`[sigma].
Proof. unfold canon. cbn. rewrite transitive_subst, chi_subst. cbn. now rewrite !up_term. Qed.

Lemma canonw_subst y u sigma : (canonw y u)[sigma] = canonw y`[sigma] u`[sigma].
Proof. unfold canonw. cbn. now rewrite canon_subst, wellf_subst. Qed.

#[export] Hint Rewrite chi_subst canon_subst canonw_subst : wfsubst.

Definition CsepT : form := ∀ ax_sep (chi $1 $0).
Definition CsepS : form := ∀ ax_sep ($0 ∈ $1).
Definition Crep : form := ax_rep (canonw $0 $1).
Definition Csepw : form := ax_sep (WF $0).
Definition Wax : list form := [CsepT; CsepS; Crep; Csepw].

Lemma chi_intro T y v : (forall s, (y ∈ s :: transitive s :: T) ⊢ v ∈ s) -> T ⊢ chi y v.
Proof. intros H. unfold chi. apply AllI_named. intros s. simp. apply II, II, H. Qed.

Lemma chi_elim T y v s : T ⊢ chi y v -> T ⊢ transitive s -> T ⊢ y ∈ s -> T ⊢ v ∈ s.
Proof.
  intros H1 H2 H3. unfold chi in H1. apply (AllE s) in H1. simp_in H1.
  eapply IE; [eapply IE|]; eassumption.
Qed.

Lemma canon_intro T y u : T ⊢ transitive u -> T ⊢ y ∈ u ->
  (forall v, (v ∈ u :: T) ⊢ chi y v) -> T ⊢ canon y u.
Proof.
  intros H1 H2 H3. unfold canon. apply CI; trivial. apply CI; trivial.
  apply AllI_named. intros v. simp. apply II, H3.
Qed.

Lemma canon_trans T y u : T ⊢ canon y u -> T ⊢ transitive u.
Proof. intros H. unfold canon in H. eapply CE1, H. Qed.

Lemma canon_in T y u : T ⊢ canon y u -> T ⊢ y ∈ u.
Proof. intros H. unfold canon in H. eapply CE1, CE2, H. Qed.

Lemma canon_chi T y u v : T ⊢ canon y u -> T ⊢ v ∈ u -> T ⊢ chi y v.
Proof.
  intros H1 H2. unfold canon in H1. apply CE2, CE2, (AllE v) in H1. simp_in H1.
  eapply IE; eassumption.
Qed.

Lemma canonw_canon T y u : T ⊢ canonw y u -> T ⊢ canon y u.
Proof. intros H. unfold canonw in H. eapply CE1, H. Qed.

Lemma canonw_wf T y u : T ⊢ canonw y u -> T ⊢ wellf u.
Proof. intros H. unfold canonw in H. eapply CE2, H. Qed.

Lemma canonw_tw T y u : T ⊢ canonw y u -> T ⊢ tw u.
Proof.
  intros H. apply tw_intro; [eapply canon_trans, canonw_canon, H | eapply canonw_wf, H].
Qed.

Lemma canon_fun T y u u' : ZFeq' <<= T -> T ⊢ canon y u -> T ⊢ canon y u' -> T ⊢ u ≡ u'.
Proof.
  intros HT H1 H2. apply ZF_ext'; trivial.
  - apply sub_intro. intros v. eapply chi_elim.
    + eapply canon_chi; [wk H1 | auto].
    + eapply canon_trans. wk H2.
    + eapply canon_in. wk H2.
  - apply sub_intro. intros v. eapply chi_elim.
    + eapply canon_chi; [wk H2 | auto].
    + eapply canon_trans. wk H1.
    + eapply canon_in. wk H1.
Qed.

Lemma canon_exists T y phi : ZFeq' <<= T -> Wax <<= T -> T ⊢ WF y ->
  (forall u, (canonw y u :: T) ⊢ phi) -> T ⊢ phi.
Proof.
  intros HT HW H1 H2. apply (WF_elim H1). intros t.
  assert (Hs : (tw t :: y ∈ t :: T) ⊢ ax_sep (chi y`[↑] $0)).
  { assert (H : (tw t :: y ∈ t :: T) ⊢ CsepT) by (apply ax_in; right; right; apply HW; cbn; tauto).
    unfold CsepT in H. apply (AllE y) in H. rewrite ax_sep_subst in H. simp_in H. exact H. }
  apply (sep_elim (X := t) Hs). intros Z.
  assert (Hin : forall G v, (sepspec Z t (chi y`[↑] $0) :: tw t :: y ∈ t :: T) <<= G ->
            G ⊢ v ∈ Z -> G ⊢ v ∈ t ∧ chi y v).
  { intros G v HG Hv. assert (H := sep_in (Ctx (HG _ (or_introl eq_refl))) Hv). simp_in H. exact H. }
  assert (Hout : forall G v, (sepspec Z t (chi y`[↑] $0) :: tw t :: y ∈ t :: T) <<= G ->
            G ⊢ v ∈ t -> G ⊢ chi y v -> G ⊢ v ∈ Z).
  { intros G v HG Hv1 Hv2. apply (sep_out (Ctx (HG _ (or_introl eq_refl))) Hv1). simp. exact Hv2. }
  eapply cut_with; [| apply H2 |]; [| auto].
  unfold canonw. apply CI.
  - apply canon_intro.
    + apply trans_intro. intros v w. apply Hout; [auto | |].
      * eapply trans_elim; [apply tw_trans; auto | eapply CE1, Hin; auto | auto].
      * apply chi_intro. intros s. eapply trans_elim; [auto | | auto].
        eapply chi_elim; [eapply CE2, Hin; auto | auto | auto].
    + apply Hout; [auto | auto |]. apply chi_intro. intros s. auto.
    + intros v. eapply CE2, Hin; auto.
  - eapply wf_sub; [apply tw_wf; auto |]. apply sub_intro. intros v. eapply CE1, Hin; auto.
Qed.

(* ** Closure: a set all of whose elements are in WF is in WF *)

Lemma incl_ext (A B C : list form) : A <<= B -> B <<= C -> A <<= C.
Proof. intros H1 H2 a Ha. apply H2, H1, Ha. Qed.

Ltac inc := solve [repeat first [apply incl_refl | assumption | (eapply incl_ext; eassumption) | apply incl_tl]].
Ltac ctx := solve [apply Ctx; repeat first [apply in_eq | apply in_cons]].
#[local] Hint Extern 3 (incl _ _) => inc : core.
#[local] Hint Extern 3 (_ ⊢ _) => ctx : core.

Lemma WF_closure T x : ZFeq' <<= T -> Wax <<= T -> T ⊢ ∀ ($0 ∈ x`[↑] → WF $0) -> T ⊢ WF x.
Proof.
  intros HT HW Hx.
  Local Ltac incZ := solve [eapply incl_ext; [eassumption | inc]].
  assert (Hxe : forall G y, T <<= G -> G ⊢ y ∈ x -> G ⊢ WF y).
  { intros G y HG Hy. apply (AllE y) in Hx. simp_in Hx. eapply IE; [wk Hx | exact Hy]. }
  assert (Hrep : T ⊢ Crep) by (apply ax_in, HW; cbn; tauto).
  assert (Hfun : T ⊢ fun_rel (canonw $0 $1)).
  { apply fun_rel_intro. intros X Y Y'. simp. apply canon_fun with X; auto.
    - eapply canonw_canon; auto.
    - eapply canonw_canon; auto. }
  apply (rep_elim (X := x) Hrep Hfun). intros Z.
  pose (G1 := repspec Z x (canonw $0 $1) :: T).
  assert (HG1 : T <<= G1) by (unfold G1; auto).
  assert (HZin : forall G u phi, G1 <<= G -> G ⊢ u ∈ Z ->
            (forall V, (V ∈ x :: canonw V u :: G) ⊢ phi) -> G ⊢ phi).
  { intros G u phi HG Hu H. apply (rep_in (Ctx (HG _ (or_introl eq_refl))) Hu).
    intros V. simp. apply H. }
  assert (HZout : forall G u V, G1 <<= G -> G ⊢ V ∈ x -> G ⊢ canonw V u -> G ⊢ u ∈ Z).
  { intros G u V HG HV Hu. apply (rep_out (Ctx (HG _ (or_introl eq_refl))) HV). simp. exact Hu. }
  assert (F1 : forall G y, G1 <<= G -> G ⊢ y ∈ x -> G ⊢ y ∈ ⋃ Z).
  { intros G y HG Hy. assert (HTG : T <<= G) by (eapply incl_ext; eassumption).
    apply (canon_exists (y := y)); [eapply incl_ext; eassumption | eapply incl_ext; eassumption |
      apply (Hxe G y HTG Hy) |].
    intros u. apply ZF_union_el' with u; [incZ |].
    apply CI.
    - eapply HZout; [auto | wk Hy | auto].
    - eapply canon_in, canonw_canon. auto. }
  assert (Uel : forall G w phi, G1 <<= G -> G ⊢ w ∈ ⋃ Z ->
            (forall u, (tw u :: w ∈ u :: u ∈ Z :: G) ⊢ phi) -> G ⊢ phi).
  { intros G w phi HG Hw H. apply (union_elim (x := Z) (z := w)); trivial.
    - eapply incl_ext; [eassumption|]. eapply incl_ext; eassumption.
    - intros u. eapply HZin; [auto | auto |]. intros V.
      eapply cut_with; [| apply H |].
      + eapply canonw_tw. auto.
      + intros a [<-|[<-|Ha]]; auto. }
  apply WF_intro with ((⋃ Z) ∪ {x; x}).
  - apply tw_intro.
    + (* transitive *)
      apply trans_intro. intros w v.
      eapply DE; [apply ZF_bunion_inv; [incZ | auto] | |].
      * apply Uel with (w := w); [auto | auto |]. intros u.
        apply ZF_bunion_el'; [incZ |]. apply DI1.
        apply ZF_union_el' with u; [incZ |]. apply CI; [auto |].
        eapply trans_elim; [apply tw_trans; auto | auto | apply Ctx; auto].
      * apply ZF_bunion_el'; [incZ |]. apply DI1.
        apply F1; [auto |].
        eapply ZF_eq_elem; [incZ | apply ZF_refl'; incZ | | auto].
        apply ZF_sing_iff; [incZ | auto].
    + (* well-founded *)
      apply wf_intro. intros s w0.
      apply XMc with (phi := ∃ ($0 ∈ s`[↑] ∧ $0 ∈ (⋃ Z)`[↑])).
      * eapply ExE_named; [auto |]. intros w. cbn. subsimpl. apply conj_split.
        apply Uel with (w := w); [auto | auto |]. intros u.
        assert (Hs : forall G, G1 <<= G -> G ⊢ ax_sep ($0 ∈ s`[↑])).
        { intros G HG. assert (H : G ⊢ CsepS) by (apply ax_in, HG; right; apply HW; cbn; tauto).
          unfold CsepS in H. apply (AllE s) in H. rewrite ax_sep_subst in H. exact H. }
        eapply (sep_elim (X := u)); [apply Hs; inc |]. intros S'.
        assert (Hin : forall G v, (sepspec S' u ($0 ∈ s`[↑]) :: tw u :: w ∈ u :: u ∈ Z :: w ∈ s :: w ∈ ⋃ Z :: ∃ ($0 ∈ s`[↑] ∧ $0 ∈ (⋃ Z)`[↑]) :: w0 ∈ s :: sub s ((⋃ Z) ∪ {x; x}) :: G1) <<= G ->
                  G ⊢ v ∈ S' -> G ⊢ v ∈ u ∧ v ∈ s).
        { intros G v HG Hv. assert (H := sep_in (Ctx (HG _ (or_introl eq_refl))) Hv). cbn in H. subsimpl_in H. exact H. }
        assert (Hout : forall G v, (sepspec S' u ($0 ∈ s`[↑]) :: tw u :: w ∈ u :: u ∈ Z :: w ∈ s :: w ∈ ⋃ Z :: ∃ ($0 ∈ s`[↑] ∧ $0 ∈ (⋃ Z)`[↑]) :: w0 ∈ s :: sub s ((⋃ Z) ∪ {x; x}) :: G1) <<= G ->
                  G ⊢ v ∈ u -> G ⊢ v ∈ s -> G ⊢ v ∈ S').
        { intros G v HG Hv1 Hv2. apply (sep_out (Ctx (HG _ (or_introl eq_refl))) Hv1). cbn. subsimpl. exact Hv2. }
        eapply min_elim.
        { apply wf_elim with u w.
          - apply tw_wf. auto.
          - apply sub_intro. intros v. eapply CE1, Hin; auto.
          - apply Hout; auto. }
        intros m. apply min_intro with m. apply minel_intro.
        -- eapply CE2, Hin; [auto | eapply minel_el; auto].
        -- intros z. eapply minel_min; [auto | auto |]. apply Hout; [auto | | auto].
           eapply trans_elim; [apply tw_trans; apply Ctx; auto | eapply CE1, Hin; [auto | eapply minel_el; auto] | auto].
      * assert (Hw0 : (¬ (∃ ($0 ∈ s`[↑] ∧ $0 ∈ (⋃ Z)`[↑])) :: w0 ∈ s :: sub s ((⋃ Z) ∪ {x; x}) :: G1) ⊢ w0 ∈ (⋃ Z) ∪ {x; x}).
        { eapply sub_elim; auto. }
        eapply DE; [apply ZF_bunion_inv; [incZ | exact Hw0] | |].
        -- apply Exp. eapply IE; [apply Ctx; auto |]. apply (ExI w0). cbn. subsimpl. apply CI; auto.
        -- apply min_intro with w0. apply minel_intro; [apply Ctx; auto |]. intros z.
           eapply IE; [apply Ctx; auto |]. apply (ExI z). cbn. subsimpl. apply CI; [auto |].
           apply F1; [auto |].
           eapply ZF_eq_elem; [incZ | apply ZF_refl'; incZ | | auto].
           apply ZF_sing_iff; [incZ | apply Ctx; auto].
  - apply ZF_bunion_el'; [incZ |]. apply DI2.
    apply ZF_sing_iff; [incZ |]. apply ZF_refl'. incZ.
Qed.

(* ** WF is closed under the function symbols *)

Section Closure.

Variable T : list form.
Hypothesis HT : ZFeq' <<= T.
Hypothesis HW : Wax <<= T.

Lemma WF_eset : T ⊢ WF ∅.
Proof.
  apply WF_closure; trivial. apply AllI_named. intros z. simp. apply II.
  apply Exp. eapply IE; [apply ZF_eset'; auto | auto].
Qed.

Lemma WF_pair a b : T ⊢ WF a -> T ⊢ WF b -> T ⊢ WF ({a; b}).
Proof.
  intros Ha Hb. apply WF_closure; trivial. apply AllI_named. intros z. simp. apply II.
  eapply DE; [apply ZF_pair_el'; auto | |].
  - eapply WF_eq; [auto | wk Ha | auto].
  - eapply WF_eq; [auto | wk Hb | auto].
Qed.

Lemma WF_union a : T ⊢ WF a -> T ⊢ WF (⋃ a).
Proof.
  intros Ha. apply WF_closure; trivial. apply AllI_named. intros z. simp. apply II.
  apply (union_elim (x := a) (z := z)); [auto | auto |]. intros y.
  eapply WF_el; [eapply WF_el; [wk Ha | auto] | auto].
Qed.

Lemma WF_power a : T ⊢ WF a -> T ⊢ WF (PP a).
Proof.
  intros Ha. apply WF_closure; trivial. apply AllI_named. intros z. simp. apply II.
  apply WF_closure; auto. apply AllI_named. intros w. simp. apply II.
  eapply WF_el; [wk Ha |]. eapply sub_elim; [apply power_el; auto | auto].
Qed.

Lemma WF_sigma a : T ⊢ WF a -> T ⊢ WF (σ a).
Proof. intros Ha. apply WF_union, WF_pair; trivial. now apply WF_pair. Qed.

End Closure.

Lemma WF_om T : ZFeq' <<= T -> Wax <<= T -> T ⊢ WF ω.
Proof.
  intros HT HW. assert (Hs : T ⊢ ax_sep (WF $0)) by (apply ax_in, HW; cbn; tauto).
  apply (sep_elim (X := ω) Hs). intros Z.
  assert (H1 : T ⊢ ax_om1) by (apply ax_in, HT; cbn; tauto).
  assert (H2 : T ⊢ ax_om2) by (apply ax_in, HT; cbn; tauto).
  unfold ax_om1, ax_om2, inductive in *.
  apply WF_closure; auto. apply AllI_named. intros z. simp. apply II.
  enough (Hz : (z ∈ ω :: sepspec Z ω (WF $0) :: T) ⊢ z ∈ Z).
  { pose proof (sep_in (ctx2 _ _ _) Hz) as H. simp_in H. eapply CE2, H. }
  apply (AllE Z) in H2. cbn in H2. simp_in H2.
  eapply sub_elim; [| auto]. eapply IE; [wk H2 |]. apply CI.
  - apply (sep_out (ctx2 _ _ _)); [eapply CE1; wk H1 | simp; apply WF_eset; auto].
  - apply AllI_named. intros y. cbn. subsimpl. apply II.
    assert (Hy : (y ∈ Z :: z ∈ ω :: sepspec Z ω (WF $0) :: T) ⊢ y ∈ ω ∧ (WF $0)[y..])
      by (eapply sep_in; auto). simp_in Hy.
    eapply sep_out; [auto | |].
    + eapply IE; [| eapply CE1, Hy]. eapply CE2 in H1. apply (AllE y) in H1. cbn in H1. subsimpl_in H1. wk H1.
    + simp. apply WF_sigma; auto. eapply CE2, Hy.
Qed.
