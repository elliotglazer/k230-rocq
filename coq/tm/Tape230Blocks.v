(** List-tape proofs for the frozen K230 runtime. Initial list, scan,
    and marker proofs adapted from Jeff's pinned m254 Box.v. *)
From Coq Require Import Lists.Streams Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From K230 Require Import Table230 TM230 Zip Boot230 Runtime230Core.
Import ListNotations.

(** ** List facts *)
Definition sepsL (vs : list nat) : list bool := flat_map (fun v => ones (S v) ++ [false]) vs.

Lemma rev_ones n : rev (ones n) = ones n.
Proof. induction n as [|n IH]; [reflexivity|]. simpl. rewrite IH. symmetry. apply (rep_snoc true n). Qed.

Lemma sepsR_app A B : sepsR (A ++ B) = sepsR A ++ sepsR B.
Proof. unfold sepsR. apply flat_map_app. Qed.

Lemma sepsR_cons v vs : sepsR (v :: vs) = false :: true :: ones v ++ sepsR vs.
Proof. reflexivity. Qed.

Lemma sepsL_cons v vs : sepsL (v :: vs) = true :: ones v ++ false :: sepsL vs.
Proof. unfold sepsL. simpl. rewrite <- app_assoc. reflexivity. Qed.

Lemma sepsL_app A B : sepsL (A ++ B) = sepsL A ++ sepsL B.
Proof. unfold sepsL. apply flat_map_app. Qed.

Lemma rev_sepsR vs : rev (sepsR vs) = sepsL (rev vs).
Proof.
  induction vs as [|v vs IH]; [reflexivity|].
  change (sepsR (v :: vs)) with ((false :: ones (S v)) ++ sepsR vs).
  rewrite rev_app_distr, IH.
  change (rev (false :: ones (S v))) with (rev (ones (S v)) ++ [false]).
  rewrite rev_ones. change (rev (v :: vs)) with (rev vs ++ [v]).
  rewrite sepsL_app. f_equal. unfold sepsL. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma split_at (vs : list nat) r : r < length vs ->
  exists pre v rest, vs = pre ++ v :: rest /\ length pre = r.
Proof.
  revert r. induction vs as [|x vs IH]; intros r H; [simpl in H; lia|].
  destruct r as [|r].
  - exists (@nil nat), x, vs. split; reflexivity.
  - destruct (IH r) as (pre & v & rest & E & L); [simpl in H; lia|].
    exists (x :: pre), v, rest. subst. split; reflexivity.
Qed.

Lemma nth_split (pre rest : list nat) (v d : nat) : nth (length pre) (pre ++ v :: rest) d = v.
Proof. induction pre; simpl; auto. Qed.

Lemma incr_split pre v rest : incr (length pre) (pre ++ v :: rest) = pre ++ S v :: rest.
Proof. induction pre; simpl; f_equal; auto. Qed.

Lemma decr_split pre v rest : decr (length pre) (pre ++ v :: rest) = pre ++ pred v :: rest.
Proof. induction pre; simpl; f_equal; auto. Qed.

Lemma sepsM_split pre v rest :
  sepsM (length pre) (pre ++ v :: rest) = sepsR pre ++ false :: false :: ones v ++ sepsR rest.
Proof.
  induction pre as [|p pre IH]; [reflexivity|].
  cbn [length app sepsM]. rewrite IH, sepsR_cons. cbn [app]. rewrite <- app_assoc. reflexivity.
Qed.

(* the left context after crossing [pre] rightwards *)
Lemma rev_sepsR_snoc pre w : rev (sepsR (pre ++ [w])) = ones w ++ true :: false :: sepsL (rev pre).
Proof.
  rewrite rev_sepsR, rev_app_distr. cbn [rev app]. rewrite sepsL_cons, rep_comm. reflexivity.
Qed.

Lemma rev_sepsR_cons p pre l : rev (sepsR (p :: pre)) ++ l = rev (sepsR pre) ++ ones p ++ true :: false :: l.
Proof.
  rewrite sepsR_cons. change (false :: true :: ones p ++ sepsR pre) with ([false; true] ++ ones p ++ sepsR pre).
  rewrite !rev_app_distr, rev_ones. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma sepsR_one w Y : sepsR [w] ++ Y = false :: true :: ones w ++ Y.
Proof. unfold sepsR. simpl. rewrite app_nil_r. reflexivity. Qed.

(** ** Single steps *)
Lemma stR q b w q' l r X : tmn q b = Some (w, R, q') ->
  zc (st q') (w :: l) r -->* X -> zc (st q) l (b :: r) -->* X.
Proof. intros T H. eapply evstep_step; [apply zR, tm_st, T | exact H]. Qed.

Lemma stL q b w q' l r X : tmn q b = Some (w, L, q') ->
  zl (st q') l (w :: r) -->* X -> zc (st q) l (b :: r) -->* X.
Proof. intros T H. eapply evstep_step; [apply zL, tm_st, T | exact H]. Qed.

Ltac go := first [ eapply stR; [reflexivity|] | eapply stL; [reflexivity|] ].

Lemma zl_c q x l r : zl q (x :: l) r = zc q l (x :: r).
Proof. reflexivity. Qed.

Lemma zc_blank q l : zc q l [] = zc q l [false].
Proof. reflexivity. Qed.

Lemma zl_blank q l : zl q l [] = zl q l [false].
Proof. unfold zl. symmetry. apply (zc_padr _ _ [hd false l] 1). Qed.

(** ** Generic scans across register blocks *)
Section Scans.
Variables qa qb : nat.

(* rightwards: [qa] crosses ones, a 0 sends it to [qb], which returns to [qa] on a 1 *)
Hypothesis F1 : tmn qa true = Some (true, R, qa).
Hypothesis F2 : tmn qa false = Some (false, R, qb).
Hypothesis F3 : tmn qb true = Some (true, R, qa).

Lemma fwd pre l X : zc (st qa) l (sepsR pre ++ X) -->* zc (st qa) (rev (sepsR pre) ++ l) X.
Proof.
  revert l. induction pre as [|p pre IH]; intros l; [apply evstep_refl|].
  rewrite sepsR_cons. cbn [app]. rewrite <- app_assoc.
  eapply stR; [exact F2|]. eapply stR; [exact F3|].
  eapply evstep_trans; [apply scanR, tm_st, F1|].
  eapply evstep_trans; [apply IH|].
  rewrite <- sepsR_cons, rev_sepsR_cons. apply evstep_refl.
Qed.
End Scans.

Section Ret.
Variables qa qb : nat.

(* leftwards: the same pattern, ending one cell left of the file in state [qb] *)
Hypothesis R1 : tmn qa true = Some (true, L, qa).
Hypothesis R2 : tmn qa false = Some (false, L, qb).
Hypothesis R3 : tmn qb true = Some (true, L, qa).

Lemma ret rp w l Y q : tmn q true = Some (true, L, qa) ->
  zc (st q) (ones w ++ false :: sepsL rp ++ l) (true :: Y) -->* zl (st qb) l (sepsR (rev rp ++ [w]) ++ Y).
Proof.
  revert w Y q. induction rp as [|w' rp IH]; intros w Y q T.
  - eapply stL; [exact T|]. eapply evstep_trans; [apply scanL, tm_st, R1|].
    rewrite zl_c. eapply stL; [exact R2|]. apply eq_ev.
    change (rev [] ++ [w]) with [w]. rewrite sepsR_one, rep_comm. reflexivity.
  - eapply stL; [exact T|]. eapply evstep_trans; [apply scanL, tm_st, R1|].
    rewrite zl_c. eapply stL; [exact R2|].
    rewrite sepsL_cons. cbn [app]. rewrite <- app_assoc. cbn [app]. rewrite zl_c.
    eapply evstep_trans; [apply IH, R3|].
    apply eq_ev. f_equal. change (rev (w' :: rp)) with (rev rp ++ [w']).
    rewrite (sepsR_app (rev rp ++ [w']) [w]), <- app_assoc, sepsR_one, rep_comm. reflexivity.
Qed.

(* the same from a zl configuration on the last 1 of a nonempty file *)
Lemma ret_file vs l Y q : vs <> [] -> tmn q true = Some (true, L, qa) ->
  zl (st q) (rev (sepsR vs) ++ l) Y -->* zl (st qb) l (sepsR vs ++ Y).
Proof.
  intros Hne T. destruct (exists_last Hne) as (pre & w & ->).
  rewrite rev_sepsR_snoc, <- app_assoc. cbn [app]. rewrite rep_comm, zl_c.
  eapply evstep_trans; [apply (ret (rev pre) w l Y q T)|].
  rewrite rev_involutive. apply evstep_refl.
Qed.
End Ret.

(** ** The skip chain *)
Definition sk (j : nat) : nat := nth j [51; 36; 25; 48; 32; 33; 22; 55; 60] 0.

Lemma sk_self j : j < 9 -> tmn (sk j) true = Some (true, R, sk j).
Proof. intros H. do 9 (destruct j as [|j]; [reflexivity|]). lia. Qed.

Lemma sk_next j : j < 8 -> tmn (sk (S j)) false = Some (false, R, sk j).
Proof. intros H. do 8 (destruct j as [|j]; [reflexivity|]). lia. Qed.

Lemma skip_target_sk q r : skip_target q = Some r -> q = sk r /\ r < 9.
Proof.
  intros H. unfold skip_target in H.
  do 61 (destruct q as [|q]; [simpl in H; first [discriminate | injection H as <-; split; [reflexivity | lia]]|]).
  simpl in H. discriminate.
Qed.

Lemma skip pre m l X : length pre + m < 9 ->
  zc (st (sk (length pre + m))) l (sepsR pre ++ X) -->* zc (st (sk m)) (rev (sepsR pre) ++ l) X.
Proof.
  revert l. induction pre as [|p pre IH]; intros l H; [apply evstep_refl|].
  simpl length in *. rewrite Nat.add_succ_l in *. rewrite sepsR_cons. cbn [app]. rewrite <- app_assoc.
  eapply stR; [apply (sk_next (length pre + m)); lia|].
  eapply evstep_trans; [apply (scanR _ true true (S p)), tm_st, (sk_self (length pre + m)); lia|].
  eapply evstep_trans; [apply IH; lia|].
  rewrite <- sepsR_cons, rev_sepsR_cons. apply eq_ev. f_equal. f_equal. simpl. rewrite rep_comm. reflexivity.
Qed.

Lemma box_mark q r l vs : skip_target q = Some r -> 10 <= length vs ->
  zc (st q) l (sepsR vs) -->* zl (st (mark_exit r)) l (sepsM r vs).
Proof.
  intros Hq Hl. apply skip_target_sk in Hq as [-> Hr].
  destruct (split_at vs r) as (pre & v & rest & -> & <-); [lia|].
  rewrite sepsR_app, sepsM_split.
  replace (sk (length pre)) with (sk (length pre + 0)) by (rewrite Nat.add_0_r; reflexivity).
  eapply evstep_trans; [apply skip; lia|]. rewrite sepsR_cons.
  go. go. rewrite zl_c. go.
  destruct pre as [|p pre'].
  - apply evstep_refl.
  - change (mark_exit (length (p :: pre'))) with 3.
    eapply evstep_trans; [apply (ret_file 2 3); try reflexivity; discriminate|]. apply evstep_refl.
Qed.

