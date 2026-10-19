(** From the common reflected bound to an ordinary core instance in L. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From RegCon Require Import Rel.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_refl Z_axL.
From K230S Require Import KP0Use KPSeed KPrimeCore KUpperCore KUpperLift KUpperReflect.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
#[local] Arguments Lform : simpl never.
#[local] Arguments InL : simpl never.
#[local] Hint Rewrite Lform_up Lform_inst InL_subst relL_subst : fsub.
Unset Implicit Arguments.

Definition upper_core_insts n phi : list form :=
  upper_insts n phi ++ sepL_insts (S n) (trace_predicate phi).

Lemma upper_core_insts_ok n phi q : fb (S (S n)) phi ->
  In q (upper_core_insts n phi) -> ZFR q.
Proof.
  intros Hphi Hq. apply in_app_or in Hq as [Hq|Hq].
  - exact (upper_insts_ok n phi q Hphi Hq).
  - apply (sepL_insts_ok (S n) (trace_predicate phi) q).
    + apply trace_predicate_bounded, Hphi.
    + exact Hq.
Qed.

Lemma L_output_from_bound G
  (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G)
  (HL : incl Ax_L G) n phi sg a x :
  fb (S (S n)) phi -> incl (upper_insts n phi) G ->
  G ⊢C rel Lform (forall_times (S n) (ax_sep' (trace_predicate phi))) ->
  G ⊢C InL a -> G ⊢C InL x -> (forall k, G ⊢C InL (sg k)) ->
  G ⊢C rel Lform (upper_conclusion phi sg a x).
Proof.
  intros Hphi HI Hsep Ha Hx Hsg.
  fobtain (L_bound_exists G HG HR HOm HL n phi sg a x Hphi HI Ha Hx
    ltac:(intros k Hk; apply Hsg)) as Y HY.
  unfold L_bound in HY. simp_in HY.
  fdestr HY HY1 HY2. fdestr HY1 HYL HaY. fdestr HY2 HxY HY3. fdestr HY3 HS HW.
  apply (bounded_output_root_rel_terms _ n phi sg Y a x Lform bounded_Lform Hphi).
  - exact HYL.
  - exact Ha.
  - exact Hx.
  - exact Hsg.
  - exact Hsep.
  - exact HaY.
  - exact HxY.
  - exact HS.
  - unfold witness_closed, matrix_request. cbn [rel].
    autorewrite with fsub. kconv HW.
Qed.

Lemma L_kprime_core G
  (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G)
  (HL : incl Ax_L G) n phi :
  fb (S (S n)) phi -> incl (upper_core_insts n phi) G ->
  G ⊢C rel Lform (forall_times n (kprime_core phi)).
Proof.
  intros Hphi HI.
  assert (HU : incl (upper_insts n phi) G) by
    (intros q Hq; apply HI, in_or_app; now left).
  assert (HS : incl (sepL_insts (S n) (trace_predicate phi)) G) by
    (intros q Hq; apply HI, in_or_app; now right).
  pose proof (axL_sep HG HR HOm HL (S n) (trace_predicate phi)
    (trace_predicate_bounded n phi Hphi) HS) as Hsep.
  fobtain (L_ex HG HR HOm HL) as e He.
  assert (Hclosed : bounded 0 (rel Lform (forall_times n (kprime_core phi)))).
  { apply rel_bounded; [exact bounded_Lform|]. apply fb_bounded, kprime_core_closed, Hphi. }
  replace (rel Lform (forall_times n (kprime_core phi)))
    with ((rel Lform (forall_times n (kprime_core phi)))[fun _ => e])
    by (apply bounded_0_subst; exact Hclosed).
  apply (rel_ft Lform bounded_Lform). intros G' tau HGG Htau Htail. lift HGG.
  assert (Hall : forall k, G' ⊢C InL (tau k)).
  { intros k. destruct (Nat.lt_ge_cases k n) as [Hk|Hk].
    - exact (Htau k Hk).
    - replace k with (n + (k-n)) by lia. rewrite Htail. exact He. }
  rewrite relL_subst. unfold kprime_core, output_root. cbn [rel subst_form].
  fall a. fintro Ha. fall x. fintro Hx.
  pose proof (L_output_from_bound _ HG HR HOm HL n phi tau a x Hphi HU Hsep Ha Hx Hall) as H.
  unfold upper_conclusion, emitted_closure in H |- *. simp_in H. cbn. kconv H.
Qed.
