(** Pure logical completeness infrastructure for the K230 calculus. *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_F Std_tr Std_H Std_alpha Std_gen
 Std_iface Std_iface2 Std_setnd Std_setbase Std_glue Std_breq Std_brnd.
From K230S Require Import KP0.
From K230L Require Import Codes230 Thm230 CD230 Comp_Prop230.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
Definition Q (a : wff) : Prop := thm230 (tau a).

Lemma Q_lprov a b : lprov (Wim a b) -> Q a -> Q b.
Proof. intros H Ha. pose proof (lprov_thm _ H) as H'. cbn [tau] in H'. exact (T_mp _ _ Ha H'). Qed.

Lemma Q_of_lprov a : lprov a -> Q a.
Proof. apply lprov_thm. Qed.

Lemma Q_genall n a : Q a -> Q (genall n a).
Proof. induction n; cbn; [auto|]. intro H. apply T_gen, IHn, H. Qed.

Lemma Q_tr_cl eta n a : Q a -> maxfr a < n -> Q (tr eta (dB var (genall n a))).
Proof.
  intros Ha Hn. set (th := dB var (genall n a)).
  assert (Hfb : fb 0 th) by now apply fb_cl.
  assert (E : dB var (tr eta th) = dB var (genall n a)).
  { rewrite (dB_tr th 0 eta var (frag_dB _ _) Hfb) by (intros; lia).
    rewrite (subst_ext_fb _ 0 _ var Hfb) by (intros; lia). apply subst_var. }
  destruct (alpha_dB _ _ var injective_var E) as [_ H2].
  exact (Q_lprov _ _ H2 (Q_genall n a Ha)).
Qed.

Lemma Q_discharge G c : lprov (foldi G c) -> (forall h, In h G -> Q h) -> Q c.
Proof.
  intros H HG. revert c H; induction G as [|h G IH]; intros c H; [exact (Q_of_lprov _ H)|].
  cbn [foldi fold_left] in H. specialize (IH (fun h' Hh' => HG h' (or_intror Hh')) _ H).
  unfold Q in IH. cbn [tau] in IH. exact (T_mp _ _ (HG h (or_introl eq_refl)) IH).
Qed.

Definition TB (th : form) : Prop := exists a n, Q a /\ maxfr a < n /\ th = Lib n a.

Lemma TB_Lib a n : Q a -> maxfr a < n -> TB (Lib n a).
Proof. intros H1 H2. now exists a, n. Qed.

Theorem TB_to_thm : thm TB falsity -> thm230 1.
Proof.
  intros [C [HC Dv]].
  pose proof (nd_sound C falsity Dv eta0 oddenv_eta0) as S. cbn [tr] in S.
  apply der_foldi in S.
  assert (Hb : Q botw).
  { apply (Q_discharge _ _ S). intros h Hh. apply in_map_iff in Hh as [th [<- Hth]].
    destruct (HC th Hth) as (a & n & Ha & Hn & ->). exact (Q_tr_cl eta0 n a Ha Hn). }
  assert (H0 : Q (Wal 0 (Weq 0 0))) by (apply Q_of_lprov, LGEN, leq_refl).
  unfold Q in Hb, H0. cbn [tau botw] in Hb, H0. exact (T_mp _ _ H0 Hb).
Qed.

(** ** Equality axioms and IR *)
Lemma Lib_eq_thm a n psi : Q a -> maxfr a < n -> Lib n a = psi -> thm TB psi.
Proof. intros H1 H2 <-. apply thm_ax. now apply TB_Lib. Qed.

Lemma lprov_trans_eq : lprov (Wim (Weq 2 1) (Wim (Weq 1 0) (Weq 2 0))).
Proof.
  apply der_lprov. do 2 apply L1_LMeta.ded.
  apply (L1_LMeta.dmp _ (Weq 1 0)); [|apply L1_LMeta.dhyp; simpl; tauto].
  apply (L1_LMeta.dmp _ (Weq 1 2)); [apply L1_LMeta.dthm, LB8a|].
  apply (L1_LMeta.dmp _ (Weq 2 1)); [apply L1_LMeta.dthm, leq_sym | apply L1_LMeta.dhyp; simpl; tauto].
Qed.

Lemma TB_EqAx_mem psi : In psi EqAx -> TB psi.
Proof.
  intros H. repeat destruct H as [<-|H]; [| | | | destruct H].
  - exists (Weq 0 0), 1. repeat split; [apply Q_of_lprov, leq_refl | cbv; lia].
  - exists (Wim (Weq 1 0) (Weq 0 1)), 2. repeat split; [apply Q_of_lprov, leq_sym | cbv; lia].
  - exists (Wim (Weq 2 1) (Wim (Weq 1 0) (Weq 2 0))), 3. repeat split; [apply Q_of_lprov, lprov_trans_eq | cbv; lia].
  - exists (Wim (Weq 3 1) (Wim (Weq 2 0) (Wim (Wel 3 2) (Wel 1 0)))), 4.
    repeat split; [apply Q_of_lprov, leq_tr_el | cbv; lia].
Qed.

Lemma TB_EqAx psi : In psi EqAx -> thm TB psi.
Proof. intro H. apply thm_ax. now apply TB_EqAx_mem. Qed.

(** IR is the closure of  -. v0 e. v0, whose code is F -> F *)
Lemma TB_IR : thm TB irreflexivity.
Proof.
  apply (Lib_eq_thm (Wn (Wel 0 0)) 1); [unfold Q; cbn [tau]; apply thm_I | cbv; lia | reflexivity].
Qed.

