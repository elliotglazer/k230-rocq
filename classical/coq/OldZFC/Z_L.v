(** * Z_L: the constructible hierarchy L_α (α ↦ [LL α Y], "Y = L_α") and the class L ([Lform]).

      L_0 = ∅,  L_{α+1} = Def(L_α),  L_λ = ⋃_{β<λ} L_β,   L = ⋃_α L_α.

    Defined by the recursion theorem of Z_trec with the step formula [SL]; everything is Sigma. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From OldZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** v = ⋃_{η ∈ ξ} f(η) *)
Definition LimU (f xi v : term) : form :=
  (∀ ($0 ∈' v`[↑] → ∃ ($0 ∈' xi`[↑]`[↑] ∧ ∃ (App0 f`[↑]`[↑]`[↑] $1 $0 ∧ $2 ∈' $0)))) ∧
  PairsAll f ($1 ∈' xi`[↑]`[↑] → Sub0 $0 v`[↑]`[↑]).
#[global] Arguments LimU : simpl never.
Lemma LimU_subst f xi v sg : (LimU f xi v)[sg] = LimU f`[sg] xi`[sg] v`[sg].
Proof. psubst LimU. Qed.
#[global] Hint Rewrite LimU_subst : fsub.

(** recursion step: f = $0, ξ = $1, v = $2 (the parameter $3 is unused) *)
Definition SL : form :=
  (Emp0 $1 → Emp0 $2) ∧ (∀ ($0 ∈' $2 → Succ0 $0 $2 → ∃ (App0 $2 $1 $0 ∧ Def0 $0 $4))) ∧ (Lim0 $1 → LimU $0 $1 $2).

(** Y = L_α *)
Definition LL (a Y : term) : form :=
  ∃ (∃ (Succ0 a`[↑]`[↑] $1 ∧ Fun0 $0 ∧ Dom0 $0 $1 ∧ RecOK SL a`[↑]`[↑] $0 ∧ App0 $0 a`[↑]`[↑] Y`[↑]`[↑])).
#[global] Arguments LL : simpl never.
Lemma LL_subst a Y sg : (LL a Y)[sg] = LL a`[sg] Y`[sg].
Proof. psubst LL. Qed.
#[global] Hint Rewrite LL_subst : fsub.

(** the class L, a formula in $0 *)
Definition Lform : form := ∃ (∃ (Ord0 $1 ∧ LL $1 $0 ∧ $2 ∈' $0)).
Definition InL (x : term) : form := Lform[x..].

Ltac fbsolve' := cbn; repeat match goal with |- _ /\ _ => split | |- _ < _ => lia | |- True => exact I end.
Lemma fb_SL : fb 4 SL.
Proof. fbcomp. Qed.
Lemma fb_Lform : fb 1 Lform.
Proof. fbcomp. Qed.
Lemma bounded_Lform : bounded 1 Lform.
Proof. apply fb_bounded, fb_Lform. Qed.
Lemma InL_eq x : InL x = ∃ (∃ (Ord0 $1 ∧ LL $1 $0 ∧ x`[↑]`[↑] ∈' $0)).
Proof. unfold InL, Lform. cbn. autorewrite with fsub. cbn. fix_up. reflexivity. Qed.

(** ** Helper formulas and the fixed instances *)
(** separation formula for ⋃_{η∈ξ} f(η): $0 = z, $1 = f, $2 = ξ *)
Definition limu_form : form := ∃ ($0 ∈' $3 ∧ ∃ (App0 $3 $1 $0 ∧ $2 ∈' $0)).
(** the induction hypothesis for the hierarchy *)
Definition LLind (a : term) : form :=
  ∀ (LL a`[↑] $0 → Trans0 $0 ∧ (Sub0 a`[↑] $0 ∧ ∀ ($0 ∈' $1 → Ord0 $0 → $0 ∈' a`[↑]`[↑])) ∧
     ∀ ($0 ∈' a`[↑]`[↑] → ∀ (LL $1 $0 → $0 ∈' $2 ∧ Sub0 $0 $2))).
#[global] Arguments LLind : simpl never.
Lemma LLind_subst a sg : (LLind a)[sg] = LLind a`[sg].
Proof. psubst LLind. Qed.
#[global] Hint Rewrite LLind_subst : fsub.
Lemma fb_limu : fb 3 limu_form.
Proof. fbcomp. Qed.
Lemma fb_LLind : fb 1 (¬ LLind $0).
Proof. fbcomp. Qed.
Definition L_insts : list form := [forall_times 2 (ax_sep' limu_form); least_inst 0 (¬ LLind $0)].
Lemma L_insts_ok a : In a L_insts -> ZFR a.
Proof. intros [<-|[<-|[]]]; [exact (ZFR_sep 2 _ fb_limu) | exact (ZFR_sep 0 _ fb_LLind)]. Qed.

(** fixed instances: Ax_cl, rec_insts SL, and L_insts *)
Definition Ax_L : list form := Ax_cl ++ rec_insts SL ++ L_insts.
Lemma Ax_L_ok a : In a Ax_L -> ZFR a.
Proof.
  intros [H|[H|H]%in_app_iff]%in_app_iff;
    [now apply Ax_cl_ok | exact (rec_insts_ok SL a fb_SL H) | now apply L_insts_ok].
Qed.
Lemma Ax_L_cl G : incl Ax_L G -> incl Ax_cl G.
Proof. intros H a Ha. apply H, in_app_iff. now left. Qed.
Lemma Ax_L_rec G : incl Ax_L G -> incl (rec_insts SL) G.
Proof. intros H a Ha. apply H, in_app_iff. right. apply in_app_iff. now left. Qed.
Lemma in_limu G : incl Ax_L G -> In (forall_times 2 (ax_sep' limu_form)) G.
Proof. intros H. apply H, in_app_iff. right. apply in_app_iff. right. now left. Qed.
Lemma in_LLind G : incl Ax_L G -> In (least_inst 0 (¬ LLind $0)) G.
Proof. intros H. apply H, in_app_iff. right. apply in_app_iff. right. right. now left. Qed.

(** ** Wrappers for upstream lemmas with a uniform signature *)
Local Ltac zh := first [ assumption | apply Ax_L_cl; assumption | apply Ax_cl_ord, Ax_L_cl; assumption
  | apply Ax_ord_prim, Ax_cl_ord, Ax_L_cl; assumption | apply Ax_L_rec; assumption | exact fb_SL ].

Section W.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G).

Lemma w_pairsall_use f B u v : G ⊢C PairsAll f B -> G ⊢C App0 f u v -> G ⊢C B[v .: u .: var].
Proof using HG HR HOm HL. intros H1 H2. eapply pairsall_use; [zh..|exact H1|exact H2]. Qed.
Lemma w_pairsall_intro f B :
  (forall G' u v, incl G G' -> G' ⊢C App0 f u v -> G' ⊢C B[v .: u .: var]) -> G ⊢C PairsAll f B.
Proof using HG HR HOm HL. intros H. eapply pairsall_intro; [zh..|exact H]. Qed.
Lemma w_fun0_app f u v v' : G ⊢C Fun0 f -> G ⊢C App0 f u v -> G ⊢C App0 f u v' -> G ⊢C v ≡' v'.
Proof using HG HR HOm HL. intros H1 H2 H3. eapply fun0_app; [zh..|exact H1|exact H2|exact H3]. Qed.
Lemma w_dom0_app f d u : G ⊢C Dom0 f d -> G ⊢C u ∈' d -> G ⊢C ∃ App0 f`[↑] u`[↑] $0.
Proof using HG HR HOm HL. intros H1 H2. eapply dom0_app; [zh..|exact H1|exact H2]. Qed.
Lemma w_dom0_in f d u v : G ⊢C Dom0 f d -> G ⊢C App0 f u v -> G ⊢C u ∈' d.
Proof using HG HR HOm HL. intros H1 H2. eapply dom0_in; [zh..|exact H1|exact H2]. Qed.
Lemma w_emp0_ex : G ⊢C ∃ Emp0 $0.
Proof using HG HR HOm HL. eapply emp0_ex; zh. Qed.
Lemma w_emp0_unique e e' : G ⊢C Emp0 e -> G ⊢C Emp0 e' -> G ⊢C e ≡' e'.
Proof using HG HR HOm HL. intros H1 H2. eapply emp0_unique; [zh..|exact H1|exact H2]. Qed.
Lemma w_succ0_ex x : G ⊢C ∃ Succ0 x`[↑] $0.
Proof using HG HR HOm HL. eapply succ0_ex; zh. Qed.
Lemma w_union0_ex x : G ⊢C ∃ Union0 x`[↑] $0.
Proof using HG HR HOm HL. eapply union0_ex; zh. Qed.

Lemma w_no_self x : G ⊢C x ∈' x -> G ⊢C ⊥.
Proof using HG HR HOm HL. intros H1. eapply no_self; [zh..|exact H1]. Qed.
Lemma w_no_cycle2 x y : G ⊢C x ∈' y -> G ⊢C y ∈' x -> G ⊢C ⊥.
Proof using HG HR HOm HL. intros H1 H2. eapply no_cycle2; [zh..|exact H1|exact H2]. Qed.
Lemma w_ord_el a x : G ⊢C Ord0 a -> G ⊢C x ∈' a -> G ⊢C Ord0 x.
Proof using HG HR HOm HL. intros H1 H2. eapply ord_el; [zh..|exact H1|exact H2]. Qed.
Lemma w_ord_tr a x y : G ⊢C Ord0 a -> G ⊢C x ∈' y -> G ⊢C y ∈' a -> G ⊢C x ∈' a.
Proof using HG HR HOm HL. intros H1 H2 H3. eapply ord_tr; [zh..|exact H1|exact H2|exact H3]. Qed.
Lemma w_ord_sub a b : G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C Sub0 a b -> G ⊢C a ∈' b ∨ a ≡' b.
Proof using HG HR HOm HL. intros H1 H2 H3. eapply ord_sub; [zh..|exact H1|exact H2|exact H3]. Qed.
Lemma w_ord_emp e : G ⊢C Emp0 e -> G ⊢C Ord0 e.
Proof using HG HR HOm HL. intros H1. eapply ord_emp; [zh..|exact H1]. Qed.
Lemma w_ord_succ a s : G ⊢C Ord0 a -> G ⊢C Succ0 a s -> G ⊢C Ord0 s.
Proof using HG HR HOm HL. intros H1 H2. eapply ord_succ; [zh..|exact H1|exact H2]. Qed.
Lemma w_ord_cases a : G ⊢C Ord0 a -> G ⊢C Emp0 a ∨ (∃ (Ord0 $0 ∧ Succ0 $0 a`[↑])) ∨ Lim0 a.
Proof using HG HR HOm HL. intros H1. eapply ord_cases; [zh..|exact H1]. Qed.
Lemma w_lim_succ l a s : G ⊢C Lim0 l -> G ⊢C a ∈' l -> G ⊢C Succ0 a s -> G ⊢C s ∈' l.
Proof using HG HR HOm HL. intros H1 H2 H3. eapply lim_succ; [zh..|exact H1|exact H2|exact H3]. Qed.
Lemma w_ord_max a b : G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C ∃ (Ord0 $0 ∧ Sub0 a`[↑] $0 ∧ Sub0 b`[↑] $0).
Proof using HG HR HOm HL. intros H1 H2. eapply ord_max; [zh..|exact H1|exact H2]. Qed.
Lemma w_ord_ind psi a : fb 1 psi -> In (least_inst 0 (¬ psi)) G ->
  G ⊢C ∀ (Ord0 $0 → (∀ ($0 ∈' $1 → psi[up (var >> subst_term ↑)])) → psi[up var]) ->
  G ⊢C Ord0 a -> G ⊢C psi[a .: var].
Proof using HG HR HOm HL. intros H1 H2 H3 H4. eapply ord_ind; [zh..|exact H1|exact H2|exact H3|exact H4]. Qed.

Lemma w_rec_ex p d : G ⊢C SLoc SL p -> G ⊢C STot SL p -> G ⊢C SFun SL p -> G ⊢C Ord0 d ->
  G ⊢C ∃ (Fun0 $0 ∧ Dom0 $0 d`[↑] ∧ RecOK SL p`[↑] $0).
Proof using HG HR HOm HL. intros H1 H2 H3 H4. eapply rec_ex; [zh..|exact H1|exact H2|exact H3|exact H4]. Qed.
Lemma w_rec_agree p d d' f f' xi u u' : G ⊢C SLoc SL p -> G ⊢C SFun SL p ->
  G ⊢C Ord0 d -> G ⊢C Fun0 f -> G ⊢C Dom0 f d -> G ⊢C RecOK SL p f ->
  G ⊢C Ord0 d' -> G ⊢C Fun0 f' -> G ⊢C Dom0 f' d' -> G ⊢C RecOK SL p f' ->
  G ⊢C xi ∈' d -> G ⊢C xi ∈' d' -> G ⊢C App0 f xi u -> G ⊢C App0 f' xi u' -> G ⊢C u ≡' u'.
Proof using HG HR HOm HL.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
  eapply rec_agree; [zh..|exact H1|exact H2|exact H3|exact H4|exact H5|exact H6|exact H7|exact H8|exact H9
    |exact H10|exact H11|exact H12|exact H13|exact H14].
Qed.

Lemma w_def_ex A : G ⊢C ∃ Def0 A`[↑] $0.
Proof using HG HR HOm HL. eapply def_ex; zh. Qed.
Lemma w_def_unique A D D' : G ⊢C Def0 A D -> G ⊢C Def0 A D' -> G ⊢C D ≡' D'.
Proof using HG HR HOm HL. intros H1 H2. eapply def_unique; [zh..|exact H1|exact H2]. Qed.
Lemma w_def_sub A D z : G ⊢C Def0 A D -> G ⊢C z ∈' D -> G ⊢C Sub0 z A.
Proof using HG HR HOm HL. intros H1 H2. eapply def_sub; [zh..|exact H1|exact H2]. Qed.
Lemma w_def_self A D : G ⊢C Def0 A D -> G ⊢C A ∈' D.
Proof using HG HR HOm HL. intros H1. eapply def_self; [zh..|exact H1]. Qed.
Lemma w_def_trans A D : G ⊢C Trans0 A -> G ⊢C Def0 A D -> G ⊢C Sub0 A D.
Proof using HG HR HOm HL. intros H1 H2. eapply def_trans; [zh..|exact H1|exact H2]. Qed.
Lemma w_definable0 phi A D : fb 1 phi -> G ⊢C Def0 A D ->
  G ⊢C ∃ ($0 ∈' D`[↑] ∧ ∀ ($0 ∈' $1 ↔ $0 ∈' A`[↑]`[↑] ∧ relS A`[↑]`[↑] (phi[up (var >> subst_term ↑)]))).
Proof using HG HR HOm HL.
  intros H1 H2. eapply definable with (m := 0) (sg := var); [zh..|exact H1|exact H2|intros k Hk; lia].
Qed.

End W.

(** ** Basic helpers (stated for an arbitrary context, so they survive context extensions) *)
Lemma sub_use {G} x y z : G ⊢C Sub0 x y -> G ⊢C z ∈' x -> G ⊢C z ∈' y.
Proof. intros H Hz. unfold Sub0 in H. finst H z. exact (IE H Hz). Qed.
Lemma emp_use {G} x z : G ⊢C Emp0 x -> G ⊢C z ∈' x -> G ⊢C ⊥.
Proof. intros H Hz. unfold Emp0 in H. finst H z. exact (IE H Hz). Qed.
Lemma succ_self0 {G} x s : G ⊢C Succ0 x s -> G ⊢C x ∈' s.
Proof. intros H. unfold Succ0 in H. exact (CE1 (CE1 H)). Qed.
Lemma succ_sub0 {G} x s : G ⊢C Succ0 x s -> G ⊢C Sub0 x s.
Proof. intros H. unfold Succ0 in H. exact (CE2 (CE1 H)). Qed.
Lemma succ_el0 {G} x s z : G ⊢C Succ0 x s -> G ⊢C z ∈' s -> G ⊢C z ∈' x ∨ z ≡' x.
Proof. intros H Hz. unfold Succ0 in H. pose proof (CE2 H) as H2. finst H2 z. exact (IE H2 Hz). Qed.
Lemma lim_ord0 {G} l : G ⊢C Lim0 l -> G ⊢C Ord0 l.
Proof. intros H. unfold Lim0 in H. exact (CE1 (CE1 H)). Qed.
Lemma lim_ne0 {G} l : G ⊢C Lim0 l -> G ⊢C ∃ ($0 ∈' l`[↑] ∧ $0 ≡' $0).
Proof. intros H. unfold Lim0 in H. exact (CE2 (CE1 H)). Qed.
Lemma lim_up0 {G} l x : G ⊢C Lim0 l -> G ⊢C x ∈' l -> G ⊢C ∃ ($0 ∈' l`[↑] ∧ x`[↑] ∈' $0).
Proof. intros H Hx. unfold Lim0 in H. pose proof (CE2 H) as H2. finst H2 x. exact (IE H2 Hx). Qed.
Lemma union_in0 {G} x u y z : G ⊢C Union0 x u -> G ⊢C y ∈' x -> G ⊢C z ∈' y -> G ⊢C z ∈' u.
Proof.
  intros H Hy Hz. unfold Union0 in H. pose proof (CE2 H) as H2. finst H2 y. fmp H2 Hy. finst H2 z.
  exact (IE H2 Hz).
Qed.
Lemma sub_refl0 {G} x : G ⊢C Sub0 x x.
Proof. unfold Sub0. fall z. fintro Hz. exact Hz. Qed.
Lemma sub_tr0 {G} x y z : G ⊢C Sub0 x y -> G ⊢C Sub0 y z -> G ⊢C Sub0 x z.
Proof.
  intros H1 H2. unfold Sub0 in H1, H2 |- *. fall w. fintro Hw. finst H1 w. finst H2 w. fmp H1 Hw. exact (IE H2 H1).
Qed.
Lemma emp_lim0 {G} a : G ⊢C Emp0 a -> G ⊢C Lim0 a -> G ⊢C ⊥.
Proof. intros H1 H2. pose proof (lim_ne0 a H2) as T. fex T z Hz. exact (emp_use a z H1 (CE1 Hz)). Qed.

Lemma op0_val {G} u w q : G ⊢C OP0 u w q -> G ⊢C ∃ ($0 ∈' q`[↑] ∧ w`[↑] ∈' $0).
Proof.
  intros H. unfold OP0 in H. pose proof (CE2 (CE1 H)) as T. fex T r Hr. fdestr Hr Hr1 Hr2.
  fexists r. fsplit; [exact Hr1|]. unfold Pair0 in Hr2. exact (CE2 (CE1 Hr2)).
Qed.

(** successor and limit are exclusive; successors are unique (regularity) *)
Lemma succ_lim0 {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) e s :
  G ⊢C Succ0 e s -> G ⊢C Lim0 s -> G ⊢C ⊥.
Proof.
  intros H1 H2. pose proof (lim_up0 s e H2 (succ_self0 e s H1)) as T. fex T y Hy. fdestr Hy Hy1 Hy2.
  pose proof (succ_el0 e s y H1 Hy1) as C. fcases C C1 C2.
  - exact (w_no_cycle2 HG HR HOm HL e y Hy2 C1).
  - frew_in C2 (e`[↑] ∈' $0) Hy2. exact (w_no_self HG HR HOm HL e Hy2).
Qed.
Lemma succ_inj0 {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) e e' s :
  G ⊢C Succ0 e s -> G ⊢C Succ0 e' s -> G ⊢C e ≡' e'.
Proof.
  intros H1 H2. pose proof (succ_el0 e' s e H2 (succ_self0 e s H1)) as C. fcases C C1 C2; [|exact C2].
  pose proof (succ_el0 e s e' H1 (succ_self0 e' s H2)) as C. fcases C C3 C4.
  - fabsurd. exact (w_no_cycle2 HG HR HOm HL e e' C1 C3).
  - apply (eq_sym' HG). exact C4.
Qed.

(** ** The step formula *)
Definition SLf (f xi v : term) : form :=
  (Emp0 xi → Emp0 v) ∧ (∀ ($0 ∈' xi`[↑] → Succ0 $0 xi`[↑] → ∃ (App0 f`[↑]`[↑] $1 $0 ∧ Def0 $0 v`[↑]`[↑]))) ∧
  (Lim0 xi → LimU f xi v).
Lemma SR_SL f xi v p : SR SL f xi v p = SLf f xi v.
Proof. unfold SR, SL, SLf. simp. reflexivity. Qed.
Lemma RecOK_SL p q f : RecOK SL p f = RecOK SL q f.
Proof. unfold RecOK. now rewrite !SR_SL. Qed.

Lemma slf_emp {G} f xi v : G ⊢C SLf f xi v -> G ⊢C Emp0 xi -> G ⊢C Emp0 v.
Proof. intros H H1. unfold SLf in H. exact (IE (CE1 (CE1 H)) H1). Qed.
Lemma slf_succ {G} f e xi v : G ⊢C SLf f xi v -> G ⊢C Succ0 e xi -> G ⊢C ∃ (App0 f`[↑] e`[↑] $0 ∧ Def0 $0 v`[↑]).
Proof.
  intros H H1. unfold SLf in H. pose proof (CE2 (CE1 H)) as H2. finst H2 e.
  fmp H2 (succ_self0 e xi H1). exact (IE H2 H1).
Qed.
Lemma slf_lim {G} f xi v : G ⊢C SLf f xi v -> G ⊢C Lim0 xi -> G ⊢C LimU f xi v.
Proof. intros H H1. unfold SLf in H. exact (IE (CE2 H) H1). Qed.
Lemma limu_el {G} f xi v z : G ⊢C LimU f xi v -> G ⊢C z ∈' v ->
  G ⊢C ∃ ($0 ∈' xi`[↑] ∧ ∃ (App0 f`[↑]`[↑] $1 $0 ∧ z`[↑]`[↑] ∈' $0)).
Proof. intros H Hz. unfold LimU in H. pose proof (CE1 H) as H1. finst H1 z. exact (IE H1 Hz). Qed.
Lemma limu_sub {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) f xi v e w :
  G ⊢C LimU f xi v -> G ⊢C App0 f e w -> G ⊢C e ∈' xi -> G ⊢C Sub0 w v.
Proof.
  intros H Hw He. unfold LimU in H. pose proof (w_pairsall_use HG HR HOm HL _ _ e w (CE2 H) Hw) as T.
  simp_in T. exact (IE T He).
Qed.

Lemma recok_use {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) p f u v :
  G ⊢C RecOK SL p f -> G ⊢C App0 f u v -> G ⊢C SLf f u v.
Proof.
  intros H Hv. unfold RecOK in H. pose proof (w_pairsall_use HG HR HOm HL _ _ u v H Hv) as T.
  simp_in T. rewrite SR_SL in T. exact T.
Qed.
#[global] Arguments SLf : simpl never.
Lemma SLf_subst f xi v sg : (SLf f xi v)[sg] = SLf f`[sg] xi`[sg] v`[sg].
Proof. psubst SLf. Qed.
#[global] Hint Rewrite SLf_subst : fsub.

(** lift all facts to a larger context *)
Local Ltac lift HG' :=
  match type of HG' with incl ?G0 ?G1 =>
    repeat match goal with
    | H : G0 ⊢C ?phi |- _ => let T := fresh in
        assert (T : G1 ⊢C phi) by (eapply Weak; [exact H|exact HG']); clear H; rename T into H
    | H : incl ?L G0 |- _ => apply (fun h => incl_tran h HG') in H
    | H : In ?a G0 |- _ => apply HG' in H
    end
  end.

Lemma agree_use {G} f g xi e w : G ⊢C Agree f g xi -> G ⊢C e ∈' xi -> G ⊢C App0 f e w -> G ⊢C App0 g e w.
Proof. intros H He Hw. unfold Agree in H. finst H e. fmp H He. finst H w. exact (iff_l _ _ _ H Hw). Qed.
Lemma agree_use_r {G} f g xi e w : G ⊢C Agree f g xi -> G ⊢C e ∈' xi -> G ⊢C App0 g e w -> G ⊢C App0 f e w.
Proof. intros H He Hw. unfold Agree in H. finst H e. fmp H He. finst H w. exact (iff_r _ _ _ H Hw). Qed.

Lemma limu_ex {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) f xi :
  G ⊢C ∃ LimU f`[↑] xi`[↑] $0.
Proof.
  fobtain (w_union0_ex HG HR HOm HL f) as U1 HU1.
  fobtain (w_union0_ex HG HR HOm HL U1) as U2 HU2.
  fobtain (w_union0_ex HG HR HOm HL U2) as U3 HU3.
  pose proof (sep_use _ 2 limu_form (f .: xi .: var) U3 (in_limu _ HL) fb_limu) as HX.
  unfold limu_form in HX. simp_in HX. fex HX X HXc.
  fexists X. unfold LimU. fsplit.
  - fall z. fintro Hz. pose proof HXc as H. finst H z. exact (CE2 (iff_l _ _ _ H Hz)).
  - apply (w_pairsall_intro HG HR HOm HL). intros G' u w HG' Hw. simp. lift HG'.
    fintro Hu. unfold Sub0. fall z. fintro Hz. pose proof HXc as H. finst H z. apply (iff_r _ _ _ H). fsplit.
    + apply (union_in0 U2 U3 w z HU3); [|exact Hz].
      pose proof Hw as Hw'. unfold App0 in Hw'. fex Hw' q Hq. fdestr Hq Hq1 Hq2.
      pose proof (op0_val u w q Hq2) as T. fex T r Hr. fdestr Hr Hr1 Hr2.
      apply (union_in0 U1 U2 r w HU2); [|exact Hr2]. exact (union_in0 f U1 q r HU1 Hq1 Hr1).
    + fexists u. fsplit; [exact Hu|]. fexists w. fsplit; [exact Hw|exact Hz].
Qed.

Lemma limu_unique {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) f xi v v' :
  G ⊢C LimU f xi v -> G ⊢C LimU f xi v' -> G ⊢C v ≡' v'.
Proof.
  intros H1 H2. apply (ext_rule HG); unfold sub'; fall z; fintro Hz.
  - pose proof (limu_el f xi v z H1 Hz) as T. fex T e He. fdestr He He1 He2. fex He2 w Hw. fdestr Hw Hw1 Hw2.
    exact (sub_use w v' z (limu_sub HG HR HOm HL f xi v' e w H2 Hw1 He1) Hw2).
  - pose proof (limu_el f xi v' z H2 Hz) as T. fex T e He. fdestr He He1 He2. fex He2 w Hw. fdestr Hw Hw1 Hw2.
    exact (sub_use w v z (limu_sub HG HR HOm HL f xi v e w H1 Hw1 He1) Hw2).
Qed.

Lemma SL_loc {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) p :
  G ⊢C SLoc SL p.
Proof.
  unfold SLoc. fall f. fall g. fall xi. fall v. rewrite !SR_SL.
  fintro Hf. fintro Hg. fintro Hxi. fintro HA. fintro H.
  unfold SLf in H |- *. fdestr H H12 H3. fdestr H12 H1 H2.
  fsplit; [fsplit|].
  - exact H1.
  - fall e. fintro He. fintro Hs. finst H2 e. fmp H2 He. fmp H2 Hs. fex H2 w Hw. fdestr Hw Hw1 Hw2.
    fexists w. fsplit; [exact (agree_use f g xi e w HA He Hw1)|exact Hw2].
  - fintro Hl. fmp H3 Hl. unfold LimU in H3 |- *. fdestr H3 H31 H32. fsplit.
    + fall z. fintro Hz. finst H31 z. fmp H31 Hz. fex H31 e He. fdestr He He1 He2. fex He2 w Hw.
      fdestr Hw Hw1 Hw2.
      fexists e. fsplit; [exact He1|]. fexists w. fsplit; [exact (agree_use f g xi e w HA He1 Hw1)|exact Hw2].
    + apply (w_pairsall_intro HG HR HOm HL). intros G' u w HG' Hw. simp. lift HG'. fintro Hu.
      pose proof (w_pairsall_use HG HR HOm HL _ _ u w H32 (agree_use_r f g xi u w HA Hu Hw)) as T.
      simp_in T. exact (IE T Hu).
Qed.

Lemma SL_tot {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) p :
  G ⊢C STot SL p.
Proof.
  unfold STot. fall f. fall xi. rewrite SR_SL. fintro Hf. fintro Hxi. fintro Htot.
  pose proof (w_ord_cases HG HR HOm HL xi Hxi) as C. fcases C C12 C3; [fcases C12 C1 C2|].
  - fobtain (w_emp0_ex HG HR HOm HL) as e He. fexists e. unfold SLf. fsplit; [fsplit|].
    + fintro Hx. exact He.
    + fall e'. fintro He'. fabsurd. exact (emp_use xi e' C1 He').
    + fintro Hl. fabsurd. exact (emp_lim0 xi C1 Hl).
  - fex C2 e He. fdestr He He1 He2.
    pose proof Htot as T. finst T e. fmp T (succ_self0 e xi He2). fex T w Hw.
    fobtain (w_def_ex HG HR HOm HL w) as v Hv. fexists v. unfold SLf. fsplit; [fsplit|].
    + fintro Hemp. fabsurd. exact (emp_use xi e Hemp (succ_self0 e xi He2)).
    + fall e'. fintro He'. fintro Hs'. fexists w. fsplit; [|exact Hv].
      pose proof (succ_inj0 HG HR HOm HL e e' xi He2 Hs') as E. frew_in E (App0 f`[↑] $0 w`[↑]) Hw. exact Hw.
    + fintro Hl. fabsurd. exact (succ_lim0 HG HR HOm HL e xi He2 Hl).
  - fobtain (limu_ex HG HR HOm HL f xi) as v Hv. fexists v. unfold SLf. fsplit; [fsplit|].
    + fintro Hemp. fabsurd. exact (emp_lim0 xi Hemp C3).
    + fall e. fintro He. fintro Hs. fabsurd. exact (succ_lim0 HG HR HOm HL e xi Hs C3).
    + fintro Hx. exact Hv.
Qed.

Lemma SL_fun {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) p :
  G ⊢C SFun SL p.
Proof.
  unfold SFun. fall f. fall xi. fall v. fall v'. rewrite !SR_SL. fintro Hf. fintro Hxi. fintro H. fintro H'.
  pose proof (w_ord_cases HG HR HOm HL xi Hxi) as C. fcases C C12 C3; [fcases C12 C1 C2|].
  - exact (w_emp0_unique HG HR HOm HL v v' (slf_emp f xi v H C1) (slf_emp f xi v' H' C1)).
  - fex C2 e He. fdestr He He1 He2.
    pose proof (slf_succ f e xi v H He2) as T. fex T w Hw. fdestr Hw Hw1 Hw2.
    pose proof (slf_succ f e xi v' H' He2) as T. fex T w' Hw'. fdestr Hw' Hw1' Hw2'.
    pose proof (w_fun0_app HG HR HOm HL f e w w' Hf Hw1 Hw1') as E.
    frew_in E (Def0 $0 v'`[↑]) Hw2'. exact (w_def_unique HG HR HOm HL w v v' Hw2 Hw2').
  - exact (limu_unique HG HR HOm HL f xi v v' (slf_lim f xi v H C3) (slf_lim f xi v' H' C3)).
Qed.

(** ** The hierarchy: existence, uniqueness, recursion equations *)
Local Ltac lldestr H d f Hs Hfun Hdom Hrec Happ :=
  let T := fresh "T" in let T1 := fresh "T" in let T2 := fresh "T" in let T3 := fresh "T" in
  unfold LL in H; fex H d T; fex T f T1; fdestr T1 T2 Happ; fdestr T2 T3 Hrec; fdestr T3 T1 Hdom;
  fdestr T1 Hs Hfun.

Lemma LL_intro {G} a Y d f : G ⊢C Succ0 a d -> G ⊢C Fun0 f -> G ⊢C Dom0 f d -> G ⊢C RecOK SL a f ->
  G ⊢C App0 f a Y -> G ⊢C LL a Y.
Proof.
  intros H1 H2 H3 H4 H5. unfold LL. fexists d. fexists f.
  fsplit; [|exact H5]. fsplit; [|exact H4]. fsplit; [|exact H3]. fsplit; [exact H1|exact H2].
Qed.

Lemma trans_el {G} Y a b : G ⊢C Trans0 Y -> G ⊢C a ∈' Y -> G ⊢C b ∈' a -> G ⊢C b ∈' Y.
Proof. intros H Ha Hb. unfold Trans0 in H. finst H a. fmp H Ha. finst H b. exact (IE H Hb). Qed.

Section LLg.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G).

Lemma LL_fun_eq p d f e w Y : G ⊢C Ord0 d -> G ⊢C Fun0 f -> G ⊢C Dom0 f d -> G ⊢C RecOK SL p f ->
  G ⊢C App0 f e w -> G ⊢C LL e Y -> G ⊢C w ≡' Y.
Proof using HG HR HOm HL.
  intros Hd Hf Hdom Hrec Hw HY.
  pose proof (w_dom0_in HG HR HOm HL f d e w Hdom Hw) as He.
  pose proof (w_ord_el HG HR HOm HL d e Hd He) as Heo.
  lldestr HY d' g Hs Hg Hgdom Hgrec Hgapp.
  rewrite (RecOK_SL e p) in Hgrec.
  exact (w_rec_agree HG HR HOm HL p d d' f g e w Y (SL_loc HG HR HOm HL p) (SL_fun HG HR HOm HL p)
    Hd Hf Hdom Hrec (w_ord_succ HG HR HOm HL e d' Heo Hs) Hg Hgdom Hgrec He (succ_self0 e d' Hs) Hw Hgapp).
Qed.
End LLg.

Lemma LL_ex_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) a :
  G ⊢C Ord0 a -> G ⊢C ∃ LL a`[↑] $0.
Proof.
  intros Ha. fobtain (w_succ0_ex HG HR HOm HL a) as d Hd.
  pose proof (w_ord_succ HG HR HOm HL a d Ha Hd) as Hdo.
  pose proof (w_rec_ex HG HR HOm HL a d (SL_loc HG HR HOm HL a) (SL_tot HG HR HOm HL a)
    (SL_fun HG HR HOm HL a) Hdo) as T.
  fex T f Hf. fdestr Hf Hf12 Hf3. fdestr Hf12 Hf1 Hf2.
  pose proof (w_dom0_app HG HR HOm HL f d a Hf2 (succ_self0 a d Hd)) as T. fex T Y HY.
  fexists Y. exact (LL_intro a Y d f Hd Hf1 Hf2 Hf3 HY).
Qed.

Lemma LL_unique_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) a Y Y' :
  G ⊢C Ord0 a -> G ⊢C LL a Y -> G ⊢C LL a Y' -> G ⊢C Y ≡' Y'.
Proof.
  intros Ha H1 H2. lldestr H1 d f Hs Hf Hdom Hrec Happ.
  exact (LL_fun_eq HG HR HOm HL a d f a Y Y' (w_ord_succ HG HR HOm HL a d Ha Hs) Hf Hdom Hrec Happ H2).
Qed.

Lemma LL_of_fun {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) p d f e w :
  G ⊢C Ord0 d -> G ⊢C Fun0 f -> G ⊢C Dom0 f d -> G ⊢C RecOK SL p f -> G ⊢C App0 f e w -> G ⊢C LL e w.
Proof.
  intros Hd Hf Hdom Hrec Hw.
  pose proof (w_dom0_in HG HR HOm HL f d e w Hdom Hw) as He.
  pose proof (w_ord_el HG HR HOm HL d e Hd He) as Heo.
  pose proof (LL_ex_g HG HR HOm HL e Heo) as T. fex T Y HY.
  pose proof (LL_fun_eq HG HR HOm HL p d f e w Y Hd Hf Hdom Hrec Hw HY) as E.
  frew_in E (LL e`[↑] $0) HY. exact HY.
Qed.

Lemma LL_zero_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) a Y :
  G ⊢C Emp0 a -> G ⊢C LL a Y -> G ⊢C Emp0 Y.
Proof.
  intros Ha HY. lldestr HY d f Hs Hf Hdom Hrec Happ.
  exact (slf_emp f a Y (recok_use HG HR HOm HL a f a Y Hrec Happ) Ha).
Qed.

Lemma LL_succ_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) a s Y Y' :
  G ⊢C Ord0 a -> G ⊢C Succ0 a s -> G ⊢C LL a Y -> G ⊢C LL s Y' -> G ⊢C Def0 Y Y'.
Proof.
  intros Ha Hs HY HY'. pose proof (w_ord_succ HG HR HOm HL a s Ha Hs) as Hso.
  lldestr HY' d g Hd Hg Hgdom Hgrec Hgapp.
  pose proof (w_ord_succ HG HR HOm HL s d Hso Hd) as Hdo.
  pose proof (slf_succ g a s Y' (recok_use HG HR HOm HL s g s Y' Hgrec Hgapp) Hs) as T.
  fex T w Hw. fdestr Hw Hw1 Hw2.
  pose proof (LL_fun_eq HG HR HOm HL s d g a w Y Hdo Hg Hgdom Hgrec Hw1 HY) as E.
  frew_in E (Def0 $0 Y'`[↑]) Hw2. exact Hw2.
Qed.

Lemma LL_lim_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) l Y :
  G ⊢C Lim0 l -> G ⊢C LL l Y ->
  G ⊢C ∀ ($0 ∈' Y`[↑] → ∃ ($0 ∈' l`[↑]`[↑] ∧ ∃ (LL $1 $0 ∧ $2 ∈' $0))).
Proof.
  intros Hl HY. pose proof (lim_ord0 l Hl) as Hlo. lldestr HY d f Hd Hf Hdom Hrec Happ.
  pose proof (w_ord_succ HG HR HOm HL l d Hlo Hd) as Hdo.
  pose proof (slf_lim f l Y (recok_use HG HR HOm HL l f l Y Hrec Happ) Hl) as HU.
  fall z. fintro Hz. pose proof (limu_el f l Y z HU Hz) as T. fex T e He. fdestr He He1 He2.
  fex He2 w Hw. fdestr Hw Hw1 Hw2.
  fexists e. fsplit; [exact He1|]. fexists w. fsplit; [|exact Hw2].
  exact (LL_of_fun HG HR HOm HL l d f e w Hdo Hf Hdom Hrec Hw1).
Qed.

Lemma LL_lim_sub {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) l Y e Ye :
  G ⊢C Lim0 l -> G ⊢C LL l Y -> G ⊢C e ∈' l -> G ⊢C LL e Ye -> G ⊢C Sub0 Ye Y.
Proof.
  intros Hl HY He HYe. pose proof (lim_ord0 l Hl) as Hlo. lldestr HY d f Hd Hf Hdom Hrec Happ.
  pose proof (w_ord_succ HG HR HOm HL l d Hlo Hd) as Hdo.
  pose proof (slf_lim f l Y (recok_use HG HR HOm HL l f l Y Hrec Happ) Hl) as HU.
  pose proof (w_dom0_app HG HR HOm HL f d e Hdom (sub_use l d e (succ_sub0 l d Hd) He)) as T. fex T w Hw.
  pose proof (limu_sub HG HR HOm HL f l Y e w HU Hw He) as Hsub.
  pose proof (LL_fun_eq HG HR HOm HL l d f e w Ye Hdo Hf Hdom Hrec Hw HYe) as E.
  frew_in E (Sub0 $0 Y`[↑]) Hsub. exact Hsub.
Qed.

(** ** L_α ∩ On: absoluteness of Ord0 for transitive sets, and α ∈ Def(L_α) *)
#[local] Hint Rewrite @relS_subst : fsub.

Lemma ord_abs {G} Y x : G ⊢C Trans0 Y -> G ⊢C x ∈' Y -> G ⊢C relS Y (Ord0 x) ↔ Ord0 x.
Proof.
  intros HT Hx. unfold Ord0, Trans0. cbn. fsplit.
  - fintro H. fdestr H H1 H2. fsplit.
    + fall y. fintro Hy. fall z. fintro Hz.
      pose proof (trans_el Y x y HT Hx Hy) as HyY. pose proof (trans_el Y y z HT HyY Hz) as HzY.
      finst H1 y. fmp H1 HyY. fmp H1 Hy. finst H1 z. fmp H1 HzY. exact (IE H1 Hz).
    + fall y. fintro Hy. fall z. fintro Hz. fall w. fintro Hw.
      pose proof (trans_el Y x y HT Hx Hy) as HyY. pose proof (trans_el Y y z HT HyY Hz) as HzY.
      pose proof (trans_el Y z w HT HzY Hw) as HwY.
      finst H2 y. fmp H2 HyY. fmp H2 Hy. finst H2 z. fmp H2 HzY. fmp H2 Hz. finst H2 w. fmp H2 HwY.
      exact (IE H2 Hw).
  - fintro H. fdestr H H1 H2. fsplit.
    + fall y. fintro HyY. fintro Hy. fall z. fintro HzY. fintro Hz. finst H1 y. fmp H1 Hy. finst H1 z.
      exact (IE H1 Hz).
    + fall y. fintro HyY. fintro Hy. fall z. fintro HzY. fintro Hz. fall w. fintro HwY. fintro Hw.
      finst H2 y. fmp H2 Hy. finst H2 z. fmp H2 Hz. finst H2 w. exact (IE H2 Hw).
Qed.

Lemma ord_in_def {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) c Yc D :
  G ⊢C Ord0 c -> G ⊢C Trans0 Yc -> G ⊢C Sub0 c Yc -> G ⊢C ∀ ($0 ∈' Yc`[↑] → Ord0 $0 → $0 ∈' c`[↑]) ->
  G ⊢C Def0 Yc D -> G ⊢C c ∈' D.
Proof.
  intros Hc HT Hsub Hon HD.
  assert (Hfb : fb 1 (Ord0 $0)) by fbcomp.
  pose proof (w_definable0 HG HR HOm HL (Ord0 $0) Yc D Hfb HD) as T. simp_in T. fex T z Hz. fdestr Hz Hz1 Hz2.
  fassert E : (z ≡' c).
  { apply (ext_rule HG); unfold sub'; fall x; fintro Hx.
    - pose proof Hz2 as H. finst H x. pose proof (iff_l _ _ _ H Hx) as T. fdestr T T1 T2.
      pose proof (iff_l _ _ _ (ord_abs Yc x HT T1) T2) as Hxo.
      pose proof Hon as H'. finst H' x. fmp H' T1. exact (IE H' Hxo).
    - pose proof Hz2 as H. finst H x. apply (iff_r _ _ _ H). pose proof (sub_use c Yc x Hsub Hx) as HxY.
      fsplit; [exact HxY|]. apply (iff_r _ _ _ (ord_abs Yc x HT HxY)).
      exact (w_ord_el HG HR HOm HL c x Hc Hx). }
  frew_in E ($0 ∈' D`[↑]) Hz1. exact Hz1.
Qed.

(** ** The simultaneous induction *)
Lemma llind_use {G} a Y : G ⊢C LLind a -> G ⊢C LL a Y ->
  G ⊢C (Trans0 Y ∧ (Sub0 a Y ∧ ∀ ($0 ∈' Y`[↑] → Ord0 $0 → $0 ∈' a`[↑]))) ∧
       ∀ ($0 ∈' a`[↑] → ∀ (LL $1 $0 → $0 ∈' Y`[↑]`[↑] ∧ Sub0 $0 Y`[↑]`[↑])).
Proof. intros H HY. unfold LLind in H. finst H Y. exact (IE H HY). Qed.

Lemma LL_step {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) :
  G ⊢C ∀ (Ord0 $0 → (∀ ($0 ∈' $1 → LLind $0)) → LLind $0).
Proof.
  fall a. fintro Ha. fintro IH. unfold LLind. fall Y. fintro HY.
  pose proof (w_ord_cases HG HR HOm HL a Ha) as C. fcases C C12 C3; [fcases C12 C1 C2|].
  - (* zero *)
    pose proof (LL_zero_g HG HR HOm HL a Y C1 HY) as HE.
    fsplit; [fsplit; [|fsplit]|].
    + unfold Trans0. fall x. fintro Hx. fabsurd. exact (emp_use Y x HE Hx).
    + unfold Sub0. fall x. fintro Hx. fabsurd. exact (emp_use a x C1 Hx).
    + fall x. fintro Hx. fabsurd. exact (emp_use Y x HE Hx).
    + fall b. fintro Hb. fabsurd. exact (emp_use a b C1 Hb).
  - (* successor a = c+1 *)
    fex C2 c Hc. fdestr Hc Hco Hcs.
    pose proof (succ_self0 c a Hcs) as Hca.
    pose proof IH as IHc. finst IHc c. fmp IHc Hca.
    pose proof (LL_ex_g HG HR HOm HL c Hco) as T. fex T Yc HYc.
    pose proof (LL_succ_g HG HR HOm HL c a Yc Y Hco Hcs HYc HY) as HD.
    pose proof (llind_use c Yc IHc HYc) as IH'. fdestr IH' IH12 IH3. fdestr IH12 IHt IH2. fdestr IH2 IHs IHo.
    pose proof (w_def_trans HG HR HOm HL Yc Y IHt HD) as HYcY.
    pose proof (ord_in_def HG HR HOm HL c Yc Y Hco IHt IHs IHo HD) as Hc_in.
    fsplit; [fsplit; [|fsplit]|].
    + unfold Trans0. fall x. fintro Hx. fall y. fintro Hy.
      pose proof (w_def_sub HG HR HOm HL Yc Y x HD Hx) as Hx'. exact (sub_use Yc Y y HYcY (sub_use x Yc y Hx' Hy)).
    + unfold Sub0. fall b. fintro Hb. pose proof (succ_el0 c a b Hcs Hb) as C. fcases C C4 C5.
      * exact (sub_use Yc Y b HYcY (sub_use c Yc b IHs C4)).
      * frew C5 ($0 ∈' Y`[↑]). exact Hc_in.
    + fall x. fintro Hx. fintro Hxo.
      pose proof (w_def_sub HG HR HOm HL Yc Y x HD Hx) as Hx'.
      fassert Hxc : (Sub0 x c).
      { unfold Sub0. fall z. fintro Hz. pose proof (sub_use x Yc z Hx' Hz) as HzY.
        pose proof IHo as T. finst T z. fmp T HzY. exact (IE T (w_ord_el HG HR HOm HL x z Hxo Hz)). }
      pose proof (w_ord_sub HG HR HOm HL x c Hxo Hco Hxc) as C. fcases C C4 C5.
      * exact (sub_use c a x (succ_sub0 c a Hcs) C4).
      * frew C5 ($0 ∈' a`[↑]). exact Hca.
    + fall b. fintro Hb. fall Yb. fintro HYb. pose proof (succ_el0 c a b Hcs Hb) as C. fcases C C4 C5.
      * pose proof IH3 as T. finst T b. fmp T C4. finst T Yb. fmp T HYb. fdestr T T1 T2.
        fsplit; [exact (sub_use Yc Y Yb HYcY T1)|exact (sub_tr0 Yb Yc Y T2 HYcY)].
      * frew_in C5 (LL $0 Yb`[↑]) HYb.
        pose proof (LL_unique_g HG HR HOm HL c Yb Yc Hco HYb HYc) as E.
        frew E ($0 ∈' Y`[↑] ∧ Sub0 $0 Y`[↑]). fsplit; [exact (w_def_self HG HR HOm HL Yc Y HD)|exact HYcY].
  - (* limit *)
    pose proof (LL_lim_g HG HR HOm HL a Y C3 HY) as HU.
    fsplit; [fsplit; [|fsplit]|].
    + unfold Trans0. fall x. fintro Hx. fall y. fintro Hy.
      pose proof HU as T. finst T x. fmp T Hx. fex T e He. fdestr He He1 He2. fex He2 Ye HYe.
      fdestr HYe HYe1 HYe2.
      pose proof IH as IHe. finst IHe e. fmp IHe He1.
      pose proof (CE1 (CE1 (llind_use e Ye IHe HYe1))) as HTe.
      pose proof (LL_lim_sub HG HR HOm HL a Y e Ye C3 HY He1 HYe1) as Hs.
      exact (sub_use Ye Y y Hs (trans_el Ye x y HTe HYe2 Hy)).
    + unfold Sub0. fall b. fintro Hb.
      fobtain (w_succ0_ex HG HR HOm HL b) as s Hs.
      pose proof (w_lim_succ HG HR HOm HL a b s C3 Hb Hs) as Hsa.
      pose proof (w_ord_el HG HR HOm HL a s Ha Hsa) as Hso.
      pose proof (LL_ex_g HG HR HOm HL s Hso) as T. fex T Ys HYs.
      pose proof IH as IHs. finst IHs s. fmp IHs Hsa.
      pose proof (CE1 (CE2 (CE1 (llind_use s Ys IHs HYs)))) as Hss.
      exact (sub_use Ys Y b (LL_lim_sub HG HR HOm HL a Y s Ys C3 HY Hsa HYs) (sub_use s Ys b Hss (succ_self0 b s Hs))).
    + fall x. fintro Hx. fintro Hxo.
      pose proof HU as T. finst T x. fmp T Hx. fex T e He. fdestr He He1 He2. fex He2 Ye HYe.
      fdestr HYe HYe1 HYe2.
      pose proof IH as IHe. finst IHe e. fmp IHe He1.
      pose proof (CE2 (CE2 (CE1 (llind_use e Ye IHe HYe1)))) as Ho. finst Ho x. fmp Ho HYe2. fmp Ho Hxo.
      exact (w_ord_tr HG HR HOm HL a x e Ha Ho He1).
    + fall b. fintro Hb. fall Yb. fintro HYb.
      fobtain (w_succ0_ex HG HR HOm HL b) as s Hs.
      pose proof (w_lim_succ HG HR HOm HL a b s C3 Hb Hs) as Hsa.
      pose proof (w_ord_el HG HR HOm HL a s Ha Hsa) as Hso.
      pose proof (LL_ex_g HG HR HOm HL s Hso) as T. fex T Ys HYs.
      pose proof IH as IHs. finst IHs s. fmp IHs Hsa.
      pose proof (CE2 (llind_use s Ys IHs HYs)) as T. finst T b. fmp T (succ_self0 b s Hs). finst T Yb.
      fmp T HYb. fdestr T T1 T2.
      pose proof (LL_lim_sub HG HR HOm HL a Y s Ys C3 HY Hsa HYs) as HsY.
      fsplit; [exact (sub_use Ys Y Yb HsY T1)|exact (sub_tr0 Yb Ys Y T2 HsY)].
Qed.

Lemma LLind_all {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) a :
  G ⊢C Ord0 a -> G ⊢C LLind a.
Proof.
  intros Ha. assert (Hfb : fb 1 (LLind $0)) by fbcomp.
  pose proof (w_ord_ind HG HR HOm HL (LLind $0) a Hfb (in_LLind _ HL)) as T.
  simp_in T. apply T; [|exact Ha]. exact (LL_step HG HR HOm HL).
Qed.

(** ** Consequences of the induction *)
Lemma LL_mono_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) a b Ya Yb :
  G ⊢C Ord0 a -> G ⊢C b ∈' a -> G ⊢C LL a Ya -> G ⊢C LL b Yb -> G ⊢C Yb ∈' Ya ∧ Sub0 Yb Ya.
Proof.
  intros Ha Hb HYa HYb. pose proof (CE2 (llind_use a Ya (LLind_all HG HR HOm HL a Ha) HYa)) as T.
  finst T b. fmp T Hb. finst T Yb. exact (IE T HYb).
Qed.

Lemma LL_trans_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) a Y :
  G ⊢C Ord0 a -> G ⊢C LL a Y -> G ⊢C Trans0 Y.
Proof. intros Ha HY. exact (CE1 (CE1 (llind_use a Y (LLind_all HG HR HOm HL a Ha) HY))). Qed.

Lemma LL_ord_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) a Y :
  G ⊢C Ord0 a -> G ⊢C LL a Y -> G ⊢C Sub0 a Y ∧ ∀ ($0 ∈' Y`[↑] → Ord0 $0 → $0 ∈' a`[↑]).
Proof. intros Ha HY. exact (CE2 (CE1 (llind_use a Y (LLind_all HG HR HOm HL a Ha) HY))). Qed.

Lemma LL_sub_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) a b Ya Yb :
  G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C Sub0 b a -> G ⊢C LL a Ya -> G ⊢C LL b Yb -> G ⊢C Sub0 Yb Ya.
Proof.
  intros Ha Hb Hs HYa HYb. pose proof (w_ord_sub HG HR HOm HL b a Hb Ha Hs) as C. fcases C C1 C2.
  - exact (CE2 (LL_mono_g HG HR HOm HL a b Ya Yb Ha C1 HYa HYb)).
  - frew_in C2 (LL $0 Yb`[↑]) HYb. pose proof (LL_unique_g HG HR HOm HL a Yb Ya Ha HYb HYa) as E.
    frew E (Sub0 $0 Ya`[↑]). exact (sub_refl0 Ya).
Qed.

(** ** The class L *)
Lemma InL_intro {G} a Y x : G ⊢C Ord0 a -> G ⊢C LL a Y -> G ⊢C x ∈' Y -> G ⊢C InL x.
Proof. intros H1 H2 H3. rewrite InL_eq. fexists a. fexists Y. fsplit; [fsplit|]; assumption. Qed.

Lemma L_transC_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) :
  G ⊢C TransC Lform.
Proof.
  unfold TransC. apply AllI_named. intros x.
  change ((Lform → ∀ ($0 ∈' $1 → Lform))[x..]) with (InL x → ∀ ($0 ∈' x`[↑] → Lform[up x..])).
  rewrite (M_up' Lform bounded_Lform). apply II. ctx_push Hx.
  apply AllI_named. intros y. change ((($0 ∈' x`[↑]) → Lform)[y..]) with (y ∈' x`[↑]`[y..] → InL y).
  rewrite subst_term_shift. apply II. ctx_push Hy.
  rewrite InL_eq in Hx. fex Hx a Ha. fex Ha Y HY. fdestr HY H12 H3. fdestr H12 H1 H2.
  exact (InL_intro a Y y H1 H2 (trans_el Y x y (LL_trans_g HG HR HOm HL a Y H1 H2) H3 Hy)).
Qed.

Lemma L_ord_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) a :
  G ⊢C Ord0 a -> G ⊢C InL a.
Proof.
  intros Ha. fobtain (w_succ0_ex HG HR HOm HL a) as s Hs.
  pose proof (w_ord_succ HG HR HOm HL a s Ha Hs) as Hso.
  pose proof (LL_ex_g HG HR HOm HL s Hso) as T. fex T Ys HYs.
  pose proof (CE1 (LL_ord_g HG HR HOm HL s Ys Hso HYs)) as Hsub.
  exact (InL_intro s Ys a Hso HYs (sub_use s Ys a Hsub (succ_self0 a s Hs))).
Qed.

Lemma L_LL_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) a Y :
  G ⊢C Ord0 a -> G ⊢C LL a Y -> G ⊢C InL Y.
Proof.
  intros Ha HY. fobtain (w_succ0_ex HG HR HOm HL a) as s Hs.
  pose proof (w_ord_succ HG HR HOm HL a s Ha Hs) as Hso.
  pose proof (LL_ex_g HG HR HOm HL s Hso) as T. fex T Ys HYs.
  pose proof (LL_succ_g HG HR HOm HL a s Y Ys Ha Hs HY HYs) as HD.
  exact (InL_intro s Ys Y Hso HYs (w_def_self HG HR HOm HL Y Ys HD)).
Qed.

Lemma L_ex_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) :
  G ⊢C ∃ Lform.
Proof.
  fobtain (w_emp0_ex HG HR HOm HL) as e He. apply (ExI e).
  exact (L_ord_g HG HR HOm HL e (w_ord_emp HG HR HOm HL e He)).
Qed.

Lemma L_above_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) x a :
  G ⊢C InL x -> G ⊢C Ord0 a ->
  G ⊢C ∃ (∃ (Ord0 $1 ∧ Sub0 a`[↑]`[↑] $1 ∧ LL $1 $0 ∧ x`[↑]`[↑] ∈' $0)).
Proof.
  intros Hx Ha. rewrite InL_eq in Hx. fex Hx b Hb. fex Hb Yb HYb. fdestr HYb H12 H3. fdestr H12 H1 H2.
  pose proof (w_ord_max HG HR HOm HL a b Ha H1) as T. fex T c Hc. fdestr Hc Hc12 Hc3. fdestr Hc12 Hc1 Hc2.
  pose proof (LL_ex_g HG HR HOm HL c Hc1) as T. fex T Yc HYc.
  pose proof (LL_sub_g HG HR HOm HL c b Yc Yb Hc1 H1 Hc3 HYc H2) as Hs.
  fexists c. fexists Yc. fsplit; [fsplit; [fsplit|]|].
  - exact Hc1.
  - exact Hc2.
  - exact HYc.
  - exact (sub_use Yb Yc x Hs H3).
Qed.

Lemma L_def_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) a Y D z :
  G ⊢C Ord0 a -> G ⊢C LL a Y -> G ⊢C Def0 Y D -> G ⊢C z ∈' D -> G ⊢C InL z.
Proof.
  intros Ha HY HD Hz. fobtain (w_succ0_ex HG HR HOm HL a) as s Hs.
  pose proof (w_ord_succ HG HR HOm HL a s Ha Hs) as Hso.
  pose proof (LL_ex_g HG HR HOm HL s Hso) as T. fex T Ys HYs.
  pose proof (LL_succ_g HG HR HOm HL a s Y Ys Ha Hs HY HYs) as HD'.
  pose proof (w_def_unique HG HR HOm HL Y D Ys HD HD') as E.
  exact (InL_intro s Ys z Hso HYs (elem_r HG z D Ys E Hz)).
Qed.

Section L.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G).

(** ** The hierarchy *)
Lemma LL_ex a : G ⊢C Ord0 a -> G ⊢C ∃ LL a`[↑] $0.
Proof using HG HR HOm HL. exact (LL_ex_g HG HR HOm HL a). Qed.
Lemma LL_unique a Y Y' : G ⊢C Ord0 a -> G ⊢C LL a Y -> G ⊢C LL a Y' -> G ⊢C Y ≡' Y'.
Proof using HG HR HOm HL. exact (LL_unique_g HG HR HOm HL a Y Y'). Qed.
Lemma LL_zero a Y : G ⊢C Emp0 a -> G ⊢C LL a Y -> G ⊢C Emp0 Y.
Proof using HG HR HOm HL. exact (LL_zero_g HG HR HOm HL a Y). Qed.
Lemma LL_succ a s Y Y' : G ⊢C Ord0 a -> G ⊢C Succ0 a s -> G ⊢C LL a Y -> G ⊢C LL s Y' -> G ⊢C Def0 Y Y'.
Proof using HG HR HOm HL. exact (LL_succ_g HG HR HOm HL a s Y Y'). Qed.
Lemma LL_lim l Y : G ⊢C Lim0 l -> G ⊢C LL l Y ->
  G ⊢C ∀ ($0 ∈' Y`[↑] → ∃ ($0 ∈' l`[↑]`[↑] ∧ ∃ (LL $1 $0 ∧ $2 ∈' $0))).
Proof using HG HR HOm HL. exact (LL_lim_g HG HR HOm HL l Y). Qed.
(** monotonicity: β ∈ α → L_β ∈ L_α and L_β ⊆ L_α *)
Lemma LL_mono a b Ya Yb : G ⊢C Ord0 a -> G ⊢C b ∈' a -> G ⊢C LL a Ya -> G ⊢C LL b Yb ->
  G ⊢C Yb ∈' Ya ∧ Sub0 Yb Ya.
Proof using HG HR HOm HL. exact (LL_mono_g HG HR HOm HL a b Ya Yb). Qed.
Lemma LL_sub a b Ya Yb : G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C Sub0 b a -> G ⊢C LL a Ya -> G ⊢C LL b Yb ->
  G ⊢C Sub0 Yb Ya.
Proof using HG HR HOm HL. exact (LL_sub_g HG HR HOm HL a b Ya Yb). Qed.
Lemma LL_trans a Y : G ⊢C Ord0 a -> G ⊢C LL a Y -> G ⊢C Trans0 Y.
Proof using HG HR HOm HL. exact (LL_trans_g HG HR HOm HL a Y). Qed.
(** L_α ∩ On = α *)
Lemma LL_ord a Y : G ⊢C Ord0 a -> G ⊢C LL a Y -> G ⊢C Sub0 a Y ∧ ∀ ($0 ∈' Y`[↑] → Ord0 $0 → $0 ∈' a`[↑]).
Proof using HG HR HOm HL. exact (LL_ord_g HG HR HOm HL a Y). Qed.

(** ** The class L *)
Lemma L_transC : G ⊢C TransC Lform.
Proof using HG HR HOm HL. exact (L_transC_g HG HR HOm HL). Qed.
Lemma L_ord a : G ⊢C Ord0 a -> G ⊢C InL a.
Proof using HG HR HOm HL. exact (L_ord_g HG HR HOm HL a). Qed.
Lemma L_LL a Y : G ⊢C Ord0 a -> G ⊢C LL a Y -> G ⊢C InL Y.
Proof using HG HR HOm HL. exact (L_LL_g HG HR HOm HL a Y). Qed.
Lemma L_ex : G ⊢C ∃ Lform.
Proof using HG HR HOm HL. exact (L_ex_g HG HR HOm HL). Qed.
(** every element of L appears at a level above any given ordinal *)
Lemma L_above x a : G ⊢C InL x -> G ⊢C Ord0 a ->
  G ⊢C ∃ (∃ (Ord0 $1 ∧ Sub0 a`[↑]`[↑] $1 ∧ LL $1 $0 ∧ x`[↑]`[↑] ∈' $0)).
Proof using HG HR HOm HL. exact (L_above_g HG HR HOm HL x a). Qed.
(** elements of Def(L_α) are in L (they lie in L_{α+1}) *)
Lemma L_def a Y D z : G ⊢C Ord0 a -> G ⊢C LL a Y -> G ⊢C Def0 Y D -> G ⊢C z ∈' D -> G ⊢C InL z.
Proof using HG HR HOm HL. exact (L_def_g HG HR HOm HL a Y D z). Qed.

End L.

