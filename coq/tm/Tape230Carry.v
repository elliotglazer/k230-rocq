(** Prefix-carry register operations for the literal K230 table. *)
From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From K230 Require Import TM230 Zip Boot230 Runtime230Core Tape230Blocks.
Import ListNotations.

Definition carryR (vs : list nat) : list bool :=
  flat_map (fun v => true :: false :: ones v) vs.

Lemma carryR_cons v vs : carryR (v :: vs) = true :: false :: ones v ++ carryR vs.
Proof. reflexivity. Qed.

Lemma carryR_app a b : carryR (a ++ b) = carryR a ++ carryR b.
Proof. apply flat_map_app. Qed.

Lemma carryR_final vs : carryR vs ++ [true] = true :: sepsR vs.
Proof.
  induction vs as [|v vs IH]; [reflexivity|].
  rewrite carryR_cons, sepsR_cons. cbn [app].
  rewrite <- app_assoc, IH, rep_comm. reflexivity.
Qed.

Lemma carryR_rev vs l : true :: rev (carryR vs) ++ l = rev (sepsR vs) ++ true :: l.
Proof.
  pose proof (f_equal (@rev bool) (carryR_final vs)) as E.
  rewrite rev_app_distr in E. cbn [rev app] in E.
  change ((true :: rev (carryR vs)) ++ l = rev (sepsR vs) ++ true :: l).
  rewrite E, <- app_assoc. reflexivity.
Qed.

Lemma carry_fwd pre l X :
  zc (st 0) l (sepsR pre ++ X) -->*
  zc (st 0) (rev (carryR pre) ++ l) X.
Proof.
  revert l. induction pre as [|p pre IH]; intros l; [apply evstep_refl|].
  rewrite sepsR_cons. cbn [app]. rewrite <- app_assoc.
  go. go. eapply evstep_trans; [apply (scanR _ true true p), tm_st; reflexivity|].
  eapply evstep_trans; [apply IH|].
  apply eq_ev. rewrite carryR_cons.
  change (true :: false :: ones p ++ carryR pre) with ([true; false] ++ ones p ++ carryR pre).
  rewrite !rev_app_distr, rev_ones, <- !app_assoc. reflexivity.
Qed.

Lemma rollback_block v l Y :
  zl (st 97) (rev (true :: false :: ones v) ++ l) Y -->*
  zl (st 97) l (sepsR [v] ++ Y).
Proof.
  change (true :: false :: ones v) with ([true; false] ++ ones v).
  rewrite rev_app_distr, rev_ones. cbn [rev app]. rewrite <- app_assoc.
  eapply evstep_trans; [apply (scanL _ true true v), tm_st; reflexivity|].
  cbn [app]. rewrite zl_c. go. rewrite zl_c. go.
  apply eq_ev. rewrite sepsR_one. reflexivity.
Qed.

Lemma rollback pre l Y :
  zl (st 97) (rev (carryR pre) ++ l) Y -->*
  zl (st 97) l (sepsR pre ++ Y).
Proof.
  revert l Y. induction pre as [|v pre IH]; intros l Y; [apply evstep_refl|].
  rewrite carryR_cons.
  change (true :: false :: ones v ++ carryR pre) with ((true :: false :: ones v) ++ carryR pre).
  rewrite rev_app_distr, <- app_assoc.
  eapply evstep_trans; [apply IH|].
  eapply evstep_trans; [apply rollback_block|].
  apply eq_ev. rewrite app_assoc, <- sepsR_app. reflexivity.
Qed.

Lemma ret_file_any vs l Y :
  zl (st 40) (rev (sepsR vs) ++ l) Y -->*
  zl (st 40) l (sepsR vs ++ Y).
Proof.
  destruct vs as [|v vs]; [apply evstep_refl|].
  apply (ret_file 54 40); try reflexivity; discriminate.
Qed.

Lemma box_decp r l vs : r < 9 -> 10 <= length vs -> nth r vs 0 <> 0 ->
  zc (st 0) l (sepsM r vs) -->* zl (st 40) (true :: l) (sepsR (decr r vs)).
Proof.
  intros Hr Hl Hz. destruct (split_at vs r) as (pre & v & rest & -> & <-); [lia|].
  rewrite nth_split in Hz. destruct v as [|v]; [contradiction|].
  rewrite sepsM_split, decr_split. cbn [pred].
  eapply evstep_trans; [apply carry_fwd|].
  go. go. go. rewrite zl_c. go.
  rewrite carryR_rev.
  eapply evstep_trans; [apply ret_file_any|].
  apply eq_ev. rewrite sepsR_app, sepsR_cons. reflexivity.
Qed.

Lemma box_dec0 r l vs : r < 9 -> 10 <= length vs -> nth r vs 0 = 0 ->
  zc (st 0) l (sepsM r vs) -->* zl (st 97) l (sepsR vs).
Proof.
  intros Hr Hl Hz. destruct (split_at vs r) as (pre & v & rest & -> & Hpre); [lia|].
  subst r. rewrite nth_split in Hz. subst v.
  assert (Hrest : rest <> []).
  { intro E. subst rest. rewrite length_app in Hl. cbn [length] in Hl. lia. }
  destruct rest as [|w rest]; [contradiction|].
  rewrite sepsM_split, sepsR_cons. cbn [app].
  eapply evstep_trans; [apply carry_fwd|].
  go. go. go. go. rewrite zl_c. go. rewrite zl_c. go. rewrite zl_c. go.
  eapply evstep_trans; [apply rollback|].
  apply eq_ev. rewrite sepsR_app, !sepsR_cons. reflexivity.
Qed.

Lemma box_inc r l vs : r < 9 -> 10 <= length vs ->
  zc (st 64) l (sepsM r vs) -->* zl (st 40) l (sepsR (incr r vs ++ [1])).
Proof.
  intros Hr Hl. destruct (split_at vs r) as (pre & v & rest & -> & <-); [lia|].
  rewrite sepsM_split, incr_split.
  eapply evstep_trans; [apply (fwd 64 74); reflexivity|].
  go. go. eapply evstep_trans; [apply (scanR _ true true v), tm_st; reflexivity|].
  rewrite <- (app_nil_r (sepsR rest)) at 1.
  eapply evstep_trans; [apply carry_fwd|].
  rewrite zc_blank. go. rewrite zc_blank. go.
  rewrite zc_blank. go. rewrite zc_blank. go.
  rewrite zl_c. go. rewrite zl_c. go.
  rewrite carryR_rev.
  assert (E : rev (sepsR rest) ++ true :: ones v ++ true :: false :: rev (sepsR pre) ++ l =
              rev (sepsR (pre ++ S v :: rest)) ++ l).
  { rewrite sepsR_app, sepsR_cons.
    change (false :: true :: ones (S v) ++ sepsR rest) with
      ([false; true] ++ ones (S v) ++ sepsR rest).
    rewrite !rev_app_distr, rev_ones. cbn [rev app repeat].
    rewrite <- !app_assoc. cbn [app]. reflexivity. }
  rewrite E. eapply evstep_trans; [apply ret_file_any|].
  apply eq_ev. rewrite (sepsR_app (pre ++ S v :: rest) [1]). reflexivity.
Qed.
