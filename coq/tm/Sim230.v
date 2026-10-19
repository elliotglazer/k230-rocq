(** K230 simulation invariant, adapted from Jeff's pinned m254 Sim.v. *)
From Coq Require Import Lists.Streams Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From K230 Require Import RM RMEquiv Prog230 Interpreter230Leaves TM230 Zip Boot230 Runtime230Core Tape230Blocks Tape230Carry Interpreter230Sites Interpreter230Check.
Import ListNotations.

(** ** The site theorems, with the register lemmas of Box.v *)
Definition site_run' := site_run box_mark box_inc box_dec0 box_decp.
Definition site_halt' := site_halt box_mark box_inc box_dec0 box_decp.

(** ** Registers on the tape *)
Lemma vregs_length Rg ext : ext <> [] -> 10 <= length (vregs Rg ++ ext).
Proof. destruct ext; [contradiction|]. rewrite length_app. simpl. lia. Qed.

Lemma nth_vregs r Rg ext : r < 9 -> nth (phys_of r) (vregs Rg ++ ext) 0 = Rg r.
Proof. intros H. do 9 (destruct r as [|r]; [reflexivity|]). lia. Qed.

Lemma incr_vregs r Rg ext : r < 9 ->
  incr (phys_of r) (vregs Rg ++ ext) = vregs (upd Rg r (S (Rg r))) ++ ext.
Proof. intros H. do 9 (destruct r as [|r]; [reflexivity|]). lia. Qed.

Lemma decr_vregs r Rg ext : r < 9 ->
  decr (phys_of r) (vregs Rg ++ ext) = vregs (upd Rg r (pred (Rg r))) ++ ext.
Proof. intros H. do 9 (destruct r as [|r]; [reflexivity|]). lia. Qed.

(** ** Path lengths *)
Lemma inc_rev_length l : length (inc_rev l) = length l.
Proof. induction l as [|[|] l IH]; simpl; auto. Qed.

Lemma inc_path_length P : length (inc_path P) = length P.
Proof. unfold inc_path. rewrite length_rev, inc_rev_length, length_rev. reflexivity. Qed.

Lemma strip_rev_length b l : forall k, length (strip_rev b k l) <= length l.
Proof.
  induction l as [|x l IH]; intros [|k]; simpl; try lia.
  destruct (Bool.eqb x b); [specialize (IH k) | specialize (IH (S k))]; lia.
Qed.

Lemma strip_path_length b k P : length (strip_path b k P) <= length P.
Proof. unfold strip_path. rewrite length_rev. rewrite <- (length_rev P). apply strip_rev_length. Qed.

Lemma brk_length k P : length (brk k P) <= length P.
Proof. unfold brk. rewrite inc_path_length. apply strip_path_length. Qed.

Lemma cont_length k P : length (cont k P) <= length P.
Proof. apply strip_path_length. Qed.

(** ** Splitting the tape at the walk depth (no stray ones beyond it) *)
Lemma forall_false l : Forall (fun b => b = false) l -> l = zeros (length l).
Proof. induction 1 as [|x l Hx _ IH]; [reflexivity|]. simpl. rewrite Hx, <- IH. reflexivity. Qed.

Lemma firstn_rep {A} (x : A) a b : firstn a (repeat x b) = repeat x (Nat.min a b).
Proof. revert b. induction a as [|a IH]; intros [|b]; simpl; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma split_tape P k d :
  Forall (fun b => b = false) (skipn d P) -> d <= length P + k ->
  P ++ zeros k = firstn d (P ++ repeat false d) ++ zeros (length P + k - d).
Proof.
  intros Hs Hd. destruct (le_lt_dec d (length P)) as [Hle|Hlt].
  - rewrite firstn_app. replace (d - length P) with 0 by lia. simpl. rewrite app_nil_r.
    rewrite <- (firstn_skipn d P) at 1. rewrite (forall_false _ Hs), length_skipn.
    rewrite <- app_assoc, <- rep_add. f_equal. f_equal. lia.
  - rewrite firstn_app, firstn_all2 by lia. rewrite firstn_rep.
    replace (Nat.min (d - length P) d) with (d - length P) by lia.
    rewrite <- app_assoc, <- rep_add. f_equal. f_equal. lia.
Qed.

Lemma firstn_pad_length P d : length (firstn d (P ++ repeat false d)) = d.
Proof. rewrite length_firstn, length_app, repeat_length. lia. Qed.

(** ** The invariant *)
Definition Inv (N : nat) (T : Q * tape) : Prop :=
  exists P Rg k ext,
    rm_run p230 N ([], R0) = Some (P, Rg) /\ D0 <= length P + k /\ ext <> [] /\
    T = zc (st 84) [true] (P ++ zeros k ++ true :: sepsR (vregs Rg ++ ext)).

Lemma inv_boot : Inv 0 (zc (st 84) [true] boot_right).
Proof.
  exists (@nil bool), R0, 181, (repeat 1 167). split; [reflexivity|]. split; [unfold D0; simpl; lia|].
  split; [discriminate|reflexivity].
Qed.

Lemma rm_run_snoc N c :
  rm_run p230 (S N) c = match rm_run p230 N c with Some c1 => rm_step p230 c1 | None => None end.
Proof.
  rewrite <- Nat.add_1_r, rm_run_add. destruct (rm_run p230 N c) as [c1|]; [|reflexivity].
  simpl. destruct (rm_step p230 c1); reflexivity.
Qed.

(* the dispatch configuration seen from the leaf reached by the walk *)
Lemma inv_view N T P Rg :
  Inv N T -> rm_run p230 N ([], R0) = Some (P, Rg) ->
  exists e d k ext,
    walk p230 (nnodes p230 + 1) (root p230) P 0 = Some (e, d) /\
    check_edge (firstn d (P ++ repeat false d)) e = true /\ d <= 40 /\
    T = zc (st 84) [true] (firstn d (P ++ repeat false d) ++
                           zeros ((length P + k - D0) + (D0 - length (firstn d (P ++ repeat false d)))) ++
                           true :: sepsR (vregs Rg ++ ext)) /\
    D0 <= length P + k /\ ext <> [].
Proof.
  intros (P' & Rg' & k & ext & Hr & Hk & Hext & ->) Hr'. rewrite Hr in Hr'. injection Hr' as <- <-.
  destruct (wf_walk p230 p230_wf P') as (e & d & W).
  pose proof (leaf_check _ _ _ W) as C.
  assert (Hd : d <= 40).
  { unfold check_edge in C. rewrite firstn_pad_length in C. destruct (Nat.leb d 40) eqn:E; [|discriminate].
    apply Nat.leb_le, E. }
  exists e, d, k, ext. split; [exact W|]. split; [exact C|]. split; [exact Hd|]. split; [|exact (conj Hk Hext)].
  rewrite firstn_pad_length. f_equal.
  rewrite app_assoc, (split_tape P' k d (no_stray p230 R0 N P' Rg' e d Hr W)) by (unfold D0 in *; lia).
  rewrite <- app_assoc. f_equal. f_equal. f_equal. unfold D0 in *. lia.
Qed.

(** ** One RM step is a positive run of the machine *)
Lemma inv_step N T c' : Inv N T -> rm_run p230 (S N) ([], R0) = Some c' ->
  exists T', Inv (S N) T' /\ T -->+ T'.
Proof.
  intros HI Hr'. rewrite rm_run_snoc in Hr'.
  destruct (rm_run p230 N ([], R0)) as [[P Rg]|] eqn:Hr; [|discriminate].
  destruct (inv_view N T P Rg HI Hr) as (e & d & k & ext & W & C & Hd & -> & Hk & Hext).
  set (Q0 := firstn d (P ++ repeat false d)) in *.
  assert (HQ : length Q0 = d) by apply firstn_pad_length.
  set (n := length P + k - D0) in *.
  unfold rm_step in Hr'. rewrite W in Hr'. fold Q0 in Hr'.
  pose proof (vregs_length Rg ext Hext) as Hl.
  unfold check_edge in C. rewrite HQ in C. destruct (Nat.leb d 40); [|discriminate].
  destruct e as [m|r|r|kk|kk|]; try discriminate.
  - (* inc *)
    destruct (Nat.ltb r 9) eqn:Er; [|discriminate]. apply Nat.ltb_lt in Er.
    injection Hr' as <-. cbn [check_site] in C.
    pose proof (site_run' _ _ _ _ _ C n (vregs Rg ++ ext) (conj Hl I)) as S1. cbn [box_list growth] in S1. rewrite ?Nat.add_0_r in S1.
    rewrite incr_vregs, <- app_assoc in S1 by exact Er.
    refine (ex_intro _ _ (conj _ S1)).
    exists (inc_path Q0), (upd Rg r (S (Rg r))), (n + (D0 + (if allones Q0 then 1 else 0) - length (inc_path Q0))), (ext ++ [1]).
    split; [rewrite rm_run_snoc, Hr; unfold rm_step; rewrite W; reflexivity|].
    split; [rewrite inc_path_length; unfold D0 in *; lia |].
    split; [intro E; apply app_eq_nil in E; destruct E; discriminate|exact eq_refl].
  - (* decnz *)
    destruct (Nat.ltb r 9) eqn:Er; [|discriminate]. apply Nat.ltb_lt in Er.
    cbn [check_site] in C. apply andb_prop in C as [C0 C1].
    destruct (Rg r) as [|v] eqn:Ev.
    + injection Hr' as <-.
      assert (V : valid (Some (phys_of r, true)) (vregs Rg ++ ext)).
      { split; [exact Hl|]. rewrite nth_vregs by exact Er. exact Ev. }
      pose proof (site_run' _ _ _ _ _ C0 n _ V) as S1. cbn [box_list growth] in S1. rewrite ?Nat.add_0_r in S1.
      refine (ex_intro _ _ (conj _ S1)).
      exists (brk 1 Q0), Rg,
        (n + (D0 + (if allones (strip_path false 1 Q0) then 1 else 0) - length (brk 1 Q0))), ext.
      split; [rewrite rm_run_snoc, Hr; unfold rm_step; rewrite W; fold Q0; rewrite Ev; reflexivity|].
      pose proof (brk_length 1 Q0). split; [unfold D0 in *; lia | exact (conj Hext eq_refl)].
    + injection Hr' as <-.
      assert (V : valid (Some (phys_of r, false)) (vregs Rg ++ ext)).
      { split; [exact Hl|]. rewrite nth_vregs by exact Er. rewrite Ev. discriminate. }
      pose proof (site_run' _ _ _ _ _ C1 n _ V) as S1. cbn [box_list growth] in S1. rewrite ?Nat.add_0_r in S1.
      rewrite decr_vregs, Ev in S1 by exact Er. simpl pred in S1.
      refine (ex_intro _ _ (conj _ S1)).
      exists (inc_path Q0), (upd Rg r v),
        (n + (D0 + (if allones Q0 then 1 else 0) + 1 - length (inc_path Q0))), ext.
      split; [rewrite rm_run_snoc, Hr; unfold rm_step; rewrite W; fold Q0; rewrite Ev; reflexivity|].
      split; [rewrite inc_path_length; unfold D0 in *; lia | exact (conj Hext eq_refl)].
  - (* break *)
    injection Hr' as <-. cbn [check_site] in C.
    pose proof (site_run' _ _ _ _ _ C n (vregs Rg ++ ext) (conj Hl I)) as S1. cbn [box_list growth] in S1. rewrite ?Nat.add_0_r in S1.
    refine (ex_intro _ _ (conj _ S1)).
    exists (brk kk Q0), Rg,
      (n + (D0 + (if allones (strip_path false kk Q0) then 1 else 0) - length (brk kk Q0))), ext.
    split; [rewrite rm_run_snoc, Hr; unfold rm_step; rewrite W; reflexivity|].
    pose proof (brk_length kk Q0). split; [unfold D0 in *; lia | exact (conj Hext eq_refl)].
  - (* continue *)
    injection Hr' as <-. cbn [check_site] in C.
    pose proof (site_run' _ _ _ _ _ C n (vregs Rg ++ ext) (conj Hl I)) as S1. cbn [box_list growth] in S1. rewrite ?Nat.add_0_r in S1.
    refine (ex_intro _ _ (conj _ S1)).
    exists (cont kk Q0), Rg, (n + (D0 + 0 - length (cont kk Q0))), ext.
    split; [rewrite rm_run_snoc, Hr; unfold rm_step; rewrite W; reflexivity|].
    pose proof (cont_length kk Q0). split; [unfold D0 in *; lia | exact (conj Hext eq_refl)].
Qed.

(** ** Either the RM is at its halt leaf, or it takes another step *)
Lemma inv_next N T : Inv N T ->
  (exists c, rm_run p230 N ([], R0) = Some c /\ at_halt p230 c) \/
  (exists c', rm_run p230 (S N) ([], R0) = Some c').
Proof.
  intros HI. destruct HI as (P & Rg & k & ext & Hr & _ & _).
  destruct (wf_walk p230 p230_wf P) as (e & d & W).
  pose proof (walk_gt _ _ _ _ _ _ _ W) as [_ Hn].
  destruct e as [m|r|r|kk|kk|]; try discriminate.
  - right. rewrite rm_run_snoc, Hr. unfold rm_step. rewrite W. eexists. reflexivity.
  - right. rewrite rm_run_snoc, Hr. unfold rm_step. rewrite W. destruct (Rg r); eexists; reflexivity.
  - right. rewrite rm_run_snoc, Hr. unfold rm_step. rewrite W. eexists. reflexivity.
  - right. rewrite rm_run_snoc, Hr. unfold rm_step. rewrite W. eexists. reflexivity.
  - left. exists (P, Rg). split; [exact Hr|]. exists d. exact W.
Qed.

(** ** An RM halt is a machine halt *)
Lemma inv_halt N T c : Inv N T -> rm_run p230 N ([], R0) = Some c -> at_halt p230 c -> halts tm T.
Proof.
  intros HI Hr [d' Ha]. destruct c as [P Rg].
  destruct (inv_view N T P Rg HI Hr) as (e & d & k & ext & W & C & _ & -> & _ & Hext).
  cbn [fst] in Ha. rewrite W in Ha. injection Ha as -> _.
  unfold check_edge in C. destruct (Nat.leb _ 40); [|discriminate]. cbn [check_site] in C.
  destruct (site_halt' _ C (length P + k - D0) (vregs Rg ++ ext) (vregs_length Rg ext Hext)) as (c & Hc & Hh).
  apply halts_evstep with (c' := c); [|apply progress_evstep, Hc].
  exists 0, c. split; [constructor | exact Hh].
Qed.

(** ** Reachability *)
Lemma reach N c : rm_run p230 N ([], R0) = Some c -> exists T, c0 -->* T /\ Inv N T.
Proof.
  revert c. induction N as [|N IH]; intros c Hr.
  - exists (zc (st 84) [true] boot_right). split; [exact boot | exact inv_boot].
  - pose proof Hr as Hr'. rewrite rm_run_snoc in Hr'.
    destruct (rm_run p230 N ([], R0)) as [c1|] eqn:E1; [|discriminate].
    destruct (IH c1 eq_refl) as (T & HT & HI).
    destruct (inv_step N T c HI Hr) as (T' & HI' & HT').
    exists T'. split; [eapply evstep_trans; [exact HT | apply progress_evstep, HT'] | exact HI'].
Qed.
