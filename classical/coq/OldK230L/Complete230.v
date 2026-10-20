(** Ordinary core proofs have finite proofs in the numeric K230 calculus. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_tr Std_alpha Std_gen
  Std_F Std_iface Std_iface2 Std_setnd Std_setbase Std_breq Std_brnd.
From OldK230S Require Import KP0 KP0Use KPrimeCore KPrimeTheory KDecodeBundle
  KDecodeEncode KDecodeTranslate KDecodeLogic KDecodeCore KDecodeComplete.
From OldK230L Require Import Codes230 Thm230 Comp_Prop230 CompleteBase230.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma tau_encode230 p : tau p = encode230 p.
Proof.
  induction p as [x y|x y|p IHp q IHq|p IHp|x p IHp]; cbn [tau encode230].
  - reflexivity.
  - reflexivity.
  - now rewrite IHp, IHq.
  - unfold wn, F. now rewrite IHp.
  - now rewrite IHp.
Qed.

(* Conversion must compare constructor expressions, not expand their enormous
   unary arithmetic values. This is only a reduction strategy. *)
Local Opaque KCode230.P KCode230.wim KCode230.wal KCode230.wel KCode230.weq.

Lemma tau_bundle230 a b c p : tau (KBundle a b c p) =
  wa (kcore a b c (tau p)) (vacuity230 a b c).
Proof.
  unfold KBundle, KCore, KSubset, KRequest, KVacuity, Logic.Wa, Logic.Wex.
  unfold kcore, ksubset, krequest, vacuity230, KCode230.wa, KCode230.wex,
    KCode230.wn, KCode230.F.
  cbn [tau]. reflexivity.
Qed.

Lemma ordinary_named_core_Q phi :
  Q (KCore 1 3 (ordinary_code230 phi) (tr source_names phi)).
Proof.
  set (p := tr source_names phi).
  set (pp := Wn (Wn p)).
  set (c := ordinary_code230 phi).
  assert (Hc : 3 < c) by (unfold c, ordinary_code230; apply padded230_gt_three).
  assert (Htau : tau pp = c) by
    (unfold pp, c, ordinary_code230, padded230, p; rewrite tau_encode230; reflexivity).
  assert (Hbundle : Q (KBundle 1 3 c pp)).
  { unfold Q. rewrite tau_bundle230, Htau.
    change (thm230 (bundle 1 3 c)). apply T_bundle; lia. }
  apply (Q_lprov (KBundle 1 3 c pp)); [|exact Hbundle].
  apply (lsyl _ (KCore 1 3 c pp)).
  - unfold KBundle. apply lpc_andl.
  - assert (Hmatrix : leqv pp p).
    { unfold pp. split; [apply lpc_nn_elim|apply lpc_nn_intro]. }
    exact (proj1 (KCore_matrix_equiv 1 3 c pp p Hmatrix)).
Qed.

Lemma TB_closed a : TB a -> closedf a.
Proof. intros (p & n & Hp & Hn & ->). apply Lib_closed, Hn. Qed.

Lemma TB_kprime n phi : TB ⊢TC forall_times n (kprime_core phi).
Proof.
  set (p := KCore 1 3 (ordinary_code230 phi) (tr source_names phi)).
  set (N := S (maxfr p)).
  set (B := EqAx ++ [Lib N p]).
  assert (HE : incl EqAx B) by (intros a Ha; apply in_or_app; now left).
  assert (HB : forall a, In a B -> TB a).
  { intros a Ha. apply in_app_or in Ha as [Ha|[<-|[]]].
    - apply TB_EqAx_mem, Ha.
    - apply TB_Lib; [apply ordinary_named_core_Q|unfold N; lia]. }
  destruct (fb_exists phi) as [m Hm]. exists B. split; [exact HB|].
  apply forall_times_intro_closed; [intros a Ha; apply TB_closed, HB, Ha|].
  apply (named_source_to_kprime B phi m (ordinary_code230 phi) HE Hm).
  - unfold ordinary_code230. apply padded230_gt_three.
  - apply ordinary_code230_fresh.
  - intros rho. unfold p in *.
    apply (Lib_inst B N _ rho); [unfold N; lia|].
    apply Ctx, in_or_app. right. now left.
Qed.

Lemma KPrimeOrd_TB a : KPrimeOrd a -> TB ⊢TC a.
Proof.
  intros [b Ha|phi n Hc].
  - exact (TB_EqAx b Ha).
  - apply TB_kprime.
Qed.

Theorem KPrimeOrdIR_to_thm : KPrimeOrdIR ⊢TC ⊥ -> thm230 1.
Proof.
  intros H. apply TB_to_thm. apply (theory_derivation_map KPrimeOrdIR TB ⊥); [|exact H].
  intros a [Ha| ->]; [apply KPrimeOrd_TB, Ha|exact TB_IR].
Qed.
