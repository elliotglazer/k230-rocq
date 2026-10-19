(** Generic certificate checker adapted from pinned m254/prog/Bisim.v. *)
(** * Bisim: halting equivalence of two RM.v programs from a checked certificate.

    Two programs are compared in the path semantics of RM.v ([rm_halts]).  Between two register
    tests (decnz leaves) a program only runs increment, break and continue leaves, which never read
    a register; [seg] runs such a segment on the IP alone and returns the incremented registers and
    the IP of the next test (or halt) leaf.  A certificate is a list of related pairs of test IPs
    [(P1, P2, j, k)]: both are halt leaves, or both are [decnz r] leaves with the same [r], and for
    each outcome of the test (nonzero: successor entry [j]; zero: entry [k]) the two segments
    increment every register equally often and end at the IPs of that entry.  The start pair
    (segments from the empty IP) is entry 0.

    [check_sound]: a passing certificate gives [rm_halts p1 ([], R) -> rm_halts p2 ([], R)] for every
    register file [R].  Applied to the certificate and its mirror image this is an equivalence.

    For speed the checker never calls [nodes] while walking: a program is first converted into an
    inductive binary tree ([to_tree], one [nodes] lookup per tree node) and [walk] is proved equal
    to the walk in that tree ([walk_tree]). *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia NArith.
From K230 Require Import RM.
Import ListNotations.

(** ** The program as an inductive tree *)
Inductive tree : Type := TX | TL (e : edge) | TN (a b : tree).

Fixpoint to_tree (p : prog) (f : nat) (n : nat) : tree :=
  match f with
  | 0 => TX
  | S f => let '(a, b) := nodes p n in
           TN (match a with ENode m => to_tree p f m | _ => TL a end)
              (match b with ENode m => to_tree p f m | _ => TL b end)
  end.

Fixpoint twalk (t : tree) (P : list bool) (i : nat) : option (edge * nat) :=
  match t with
  | TN a b =>
      if bit P i
      then match b with TX => None | TL e => Some (e, S i) | TN _ _ => twalk b P (S i) end
      else match a with TX => None | TL e => Some (e, S i) | TN _ _ => twalk a P (S i) end
  | _ => None
  end.

Lemma walk_tree p f n P i : walk p f n P i = twalk (to_tree p f n) P i.
Proof.
  revert n i. induction f as [|f IH]; intros n i; [reflexivity|].
  cbn [walk to_tree]. destruct (nodes p n) as [a b]. cbn [twalk].
  destruct (bit P i); [destruct b as [m| | | | |] | destruct a as [m| | | | |]]; try reflexivity;
    rewrite IH; destruct f as [|f]; try reflexivity; cbn [to_tree]; destruct (nodes p m); reflexivity.
Qed.

Definition ptree (p : prog) : tree := to_tree p (nnodes p + 1) (root p).

(* the leaf reached from IP [P], with the bits actually read *)
Definition tsite (t : tree) (P : list bool) : option (edge * list bool) :=
  match twalk t P 0 with
  | Some (e, d) => Some (e, firstn d (P ++ repeat false d))
  | None => None
  end.

Definition lres (e : edge) (Q : list bool) (R : regs) : option conf :=
  match e with
  | ENode _ => None
  | EInc r => Some (inc_path Q, upd R r (S (R r)))
  | EDecnz r => match R r with
                | 0 => Some (brk 1 Q, R)
                | S v => Some (inc_path Q, upd R r v)
                end
  | EBreak k => Some (brk k Q, R)
  | EContinue k => Some (cont k Q, R)
  | EHalt => None
  end.

Lemma step_tsite p P R :
  rm_step p (P, R) = match tsite (ptree p) P with Some (e, Q) => lres e Q R | None => None end.
Proof.
  unfold rm_step, tsite, ptree. rewrite walk_tree.
  destruct (twalk _ P 0) as [[e d]|]; [destruct e|]; reflexivity.
Qed.

Lemma at_halt_tsite p P R : at_halt p (P, R) <-> exists Q, tsite (ptree p) P = Some (EHalt, Q).
Proof.
  unfold at_halt, tsite, ptree. cbn [fst]. rewrite walk_tree. split.
  - intros [d ->]. eauto.
  - intros [Q H]. destruct (twalk _ P 0) as [[e d]|]; [|discriminate].
    injection H as -> _. eauto.
Qed.

(** ** Runs and halting *)
Lemma rm_run_add p a b c :
  rm_run p (a + b) c = match rm_run p a c with Some c' => rm_run p b c' | None => None end.
Proof.
  revert c. induction a as [|a IH]; intro c; [reflexivity|].
  cbn [Nat.add rm_run]. destruct (rm_step p c); auto.
Qed.

Lemma halts_pre p n c c' : rm_run p n c = Some c' -> rm_halts p c' -> rm_halts p c.
Proof.
  intros H1 (m & c'' & H2 & Ha). exists (n + m), c''. rewrite rm_run_add, H1. auto.
Qed.

(* halts after exactly [N] steps *)
Definition hn (p : prog) (N : nat) (c : conf) : Prop :=
  exists c', rm_run p N c = Some c' /\ at_halt p c'.

Lemma hn_step p N P R e Q c' :
  tsite (ptree p) P = Some (e, Q) -> e <> EHalt -> lres e Q R = Some c' ->
  hn p N (P, R) -> exists N', N = S N' /\ hn p N' c'.
Proof.
  intros Hs He Hl (c'' & Hr & Ha). destruct N as [|N].
  - injection Hr as <-. apply at_halt_tsite in Ha as [Q' Ha]. rewrite Hs in Ha.
    injection Ha as E _. contradiction.
  - exists N. split; [reflexivity|]. exists c''. split; [|exact Ha].
    cbn [rm_run] in Hr. rewrite step_tsite, Hs, Hl in Hr. exact Hr.
Qed.

(** ** Segments between tests *)
Fixpoint seg (t : tree) (f : nat) (P : list bool) : option (list nat * list bool) :=
  match f with
  | 0 => None
  | S f =>
    match tsite t P with
    | Some (EInc r, Q) => match seg t f (inc_path Q) with Some (l, P') => Some (r :: l, P') | None => None end
    | Some (EBreak k, Q) => seg t f (brk k Q)
    | Some (EContinue k, Q) => seg t f (cont k Q)
    | Some (EDecnz _, _) | Some (EHalt, _) => Some ([], P)
    | _ => None
    end
  end.

Definition cnt (l : list nat) (i : nat) : nat := length (filter (Nat.eqb i) l).

Lemma upd_inc R r i : upd R r (S (R r)) i = R i + (if Nat.eqb i r then 1 else 0).
Proof. unfold upd. destruct (Nat.eqb_spec i r) as [->|]; lia. Qed.

Lemma seg_run p f P l P' R : seg (ptree p) f P = Some (l, P') ->
  exists n R', rm_run p n (P, R) = Some (P', R') /\ forall i, R' i = R i + cnt l i.
Proof.
  revert P l R. induction f as [|f IH]; intros P l R Hs; [discriminate|].
  cbn [seg] in Hs. destruct (tsite (ptree p) P) as [[e Q]|] eqn:Ht; [|discriminate].
  destruct e as [m|r|r|k|k|]; try discriminate.
  - destruct (seg _ f (inc_path Q)) as [[l1 P1]|] eqn:E; [|discriminate]. injection Hs as <- ->.
    destruct (IH _ _ (upd R r (S (R r))) E) as (n & R' & Hr & HR).
    exists (S n), R'. split.
    + cbn [rm_run]. rewrite step_tsite, Ht. exact Hr.
    + intros i. rewrite HR, upd_inc. unfold cnt. cbn [filter].
      destruct (Nat.eqb i r); cbn [length]; lia.
  - injection Hs as <- <-. exists 0, R. split; [reflexivity|]. intros i. unfold cnt. cbn. lia.
  - destruct (IH _ _ R Hs) as (n & R' & Hr & HR). exists (S n), R'. split; [|exact HR].
    cbn [rm_run]. rewrite step_tsite, Ht. exact Hr.
  - destruct (IH _ _ R Hs) as (n & R' & Hr & HR). exists (S n), R'. split; [|exact HR].
    cbn [rm_run]. rewrite step_tsite, Ht. exact Hr.
  - injection Hs as <- <-. exists 0, R. split; [reflexivity|]. intros i. unfold cnt. cbn. lia.
Qed.

Lemma seg_hn p f P l P' R N : seg (ptree p) f P = Some (l, P') -> hn p N (P, R) ->
  exists N' R', N' <= N /\ hn p N' (P', R') /\ forall i, R' i = R i + cnt l i.
Proof.
  revert P l R N. induction f as [|f IH]; intros P l R N Hs Hh; [discriminate|].
  cbn [seg] in Hs. destruct (tsite (ptree p) P) as [[e Q]|] eqn:Ht; [|discriminate].
  destruct e as [m|r|r|k|k|]; try discriminate.
  - destruct (seg _ f (inc_path Q)) as [[l1 P1]|] eqn:E; [|discriminate]. injection Hs as <- ->.
    destruct (hn_step p N P R _ Q _ Ht ltac:(discriminate) eq_refl Hh) as (N1 & -> & H1).
    destruct (IH _ _ _ _ E H1) as (N' & R' & Hle & H' & HR).
    exists N', R'. split; [lia|]. split; [exact H'|].
    intros i. rewrite HR, upd_inc. unfold cnt. cbn [filter].
    destruct (Nat.eqb i r); cbn [length]; lia.
  - injection Hs as <- <-. exists N, R. split; [lia|]. split; [exact Hh|].
    intros i. unfold cnt. cbn. lia.
  - destruct (hn_step p N P R _ Q _ Ht ltac:(discriminate) eq_refl Hh) as (N1 & -> & H1).
    destruct (IH _ _ _ _ Hs H1) as (N' & R' & Hle & H' & HR). exists N', R'. auto with arith.
  - destruct (hn_step p N P R _ Q _ Ht ltac:(discriminate) eq_refl Hh) as (N1 & -> & H1).
    destruct (IH _ _ _ _ Hs H1) as (N' & R' & Hle & H' & HR). exists N', R'. auto with arith.
  - injection Hs as <- <-. exists N, R. split; [lia|]. split; [exact Hh|].
    intros i. unfold cnt. cbn. lia.
Qed.

(** ** The certificate checker *)
Definition entry : Type := (list bool * list bool * N * N)%type.

Definition seg_fuel : nat := 1000.

Definition cnt_eq (l1 l2 : list nat) : bool := forallb (fun i => Nat.eqb (cnt l1 i) (cnt l2 i)) (l1 ++ l2).

Lemma cnt_eq_ok l1 l2 : cnt_eq l1 l2 = true -> forall i, cnt l1 i = cnt l2 i.
Proof.
  unfold cnt_eq. rewrite forallb_forall. intros H i.
  destruct (in_dec Nat.eq_dec i (l1 ++ l2)) as [Hi | Hi].
  - apply Nat.eqb_eq, H, Hi.
  - assert (Z : forall l, ~ In i l -> cnt l i = 0).
    { intros l Hl. unfold cnt. induction l as [|x l IHl]; [reflexivity|]. cbn [filter].
      destruct (Nat.eqb_spec i x) as [->|]; [exfalso; apply Hl; now left|].
      apply IHl. intros Hin; apply Hl; now right. }
    rewrite !Z; [reflexivity | |]; intros Hin; apply Hi, in_or_app; auto.
Qed.

Fixpoint lbeq (a b : list bool) : bool :=
  match a, b with
  | [], [] => true
  | x :: a, y :: b => Bool.eqb x y && lbeq a b
  | _, _ => false
  end.

Lemma lbeq_ok a b : lbeq a b = true -> a = b.
Proof.
  revert b. induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  cbn in H. apply andb_prop in H as [H1 H2]. apply Bool.eqb_prop in H1. f_equal; auto.
Qed.

Definition getc (C : list entry) (j : N) : option (list bool * list bool) :=
  match nth_error C (N.to_nat j) with Some (a, b, _, _) => Some (a, b) | None => None end.

Definition branch_ok (t1 t2 : tree) (C : list entry) (A B : list bool) (j : N) : bool :=
  match seg t1 seg_fuel A, seg t2 seg_fuel B, getc C j with
  | Some (l1, P1), Some (l2, P2), Some (Q1, Q2) => cnt_eq l1 l2 && lbeq P1 Q1 && lbeq P2 Q2
  | _, _, _ => false
  end.

Definition entry_ok (t1 t2 : tree) (C : list entry) (x : entry) : bool :=
  let '(P1, P2, j, k) := x in
  match tsite t1 P1, tsite t2 P2 with
  | Some (EHalt, _), Some (EHalt, _) => true
  | Some (EDecnz r1, Q1), Some (EDecnz r2, Q2) =>
      Nat.eqb r1 r2 && branch_ok t1 t2 C (inc_path Q1) (inc_path Q2) j
                    && branch_ok t1 t2 C (brk 1 Q1) (brk 1 Q2) k
  | _, _ => false
  end.

Definition check (t1 t2 : tree) (C : list entry) : bool :=
  branch_ok t1 t2 C [] [] 0 && forallb (entry_ok t1 t2 C) C.

Definition mirror (C : list entry) : list entry := map (fun '(a, b, j, k) => (b, a, j, k)) C.

(** ** Soundness *)
Section Sound.
Variables p1 p2 : prog.
Variable C : list entry.
Hypothesis HC : forallb (entry_ok (ptree p1) (ptree p2) C) C = true.

Lemma getc_in j P1 P2 : getc C j = Some (P1, P2) -> exists j' k', In (P1, P2, j', k') C.
Proof.
  unfold getc. destruct (nth_error C (N.to_nat j)) as [[[[a b] j'] k']|] eqn:E; [|discriminate].
  intros H. injection H as <- <-. exists j', k'. eapply nth_error_In; eauto.
Qed.

(* one branch: the p1 side halts within N steps from the branch IP => the p2 side halts *)
Lemma branch_sim N A B j R1 R2 (IH : forall N', N' < S N -> forall P1 P2 j' k' R1 R2,
    In (P1, P2, j', k') C -> (forall i, R1 i = R2 i) -> hn p1 N' (P1, R1) -> rm_halts p2 (P2, R2)) :
  branch_ok (ptree p1) (ptree p2) C A B j = true -> (forall i, R1 i = R2 i) ->
  hn p1 N (A, R1) -> rm_halts p2 (B, R2).
Proof.
  unfold branch_ok. intros Hb HR Hh.
  destruct (seg (ptree p1) seg_fuel A) as [[l1 Q1]|] eqn:E1; [|discriminate].
  destruct (seg (ptree p2) seg_fuel B) as [[l2 Q2]|] eqn:E2; [|discriminate].
  destruct (getc C j) as [[P1 P2]|] eqn:Eg; [|discriminate].
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [Hc H1].
  apply lbeq_ok in H1, H2. subst P1 P2. pose proof (cnt_eq_ok _ _ Hc) as Hc'.
  destruct (getc_in _ _ _ Eg) as (j' & k' & Hin).
  destruct (seg_hn p1 _ _ _ _ R1 N E1 Hh) as (N' & R1' & Hle & Hh' & HR1).
  destruct (seg_run p2 _ _ _ _ R2 E2) as (n & R2' & Hr & HR2).
  apply (halts_pre p2 n _ _ Hr). apply (IH N' ltac:(lia) _ _ j' k' R1' R2' Hin); [|exact Hh'].
  intros i. rewrite HR1, HR2, HR, Hc'. reflexivity.
Qed.

Lemma sim N : forall P1 P2 j k R1 R2, In (P1, P2, j, k) C -> (forall i, R1 i = R2 i) ->
  hn p1 N (P1, R1) -> rm_halts p2 (P2, R2).
Proof.
  induction N as [N IH] using lt_wf_ind. intros P1 P2 j k R1 R2 Hin HR Hh.
  rewrite forallb_forall in HC. pose proof (HC _ Hin) as He. cbn [entry_ok] in He.
  destruct (tsite (ptree p1) P1) as [[e1 Q1]|] eqn:T1; [|discriminate].
  destruct (tsite (ptree p2) P2) as [[e2 Q2]|] eqn:T2; [|destruct e1; discriminate].
  destruct e1; try discriminate; destruct e2; try discriminate.
  - (* decnz *)
    apply andb_prop in He as [He Hk]. apply andb_prop in He as [Hr Hj].
    apply Nat.eqb_eq in Hr. subst.
    destruct N as [|N].
    { destruct Hh as (c & Hc & Ha). injection Hc as <-. apply at_halt_tsite in Ha as [Q Ha].
      rewrite T1 in Ha. discriminate. }
    destruct (R1 r0) as [|v] eqn:Ev.
    + assert (Hs : lres (EDecnz r0) Q1 R1 = Some (brk 1 Q1, R1)) by (cbn; rewrite Ev; reflexivity).
      destruct (hn_step p1 _ _ _ _ _ _ T1 ltac:(discriminate) Hs Hh) as (N' & E & Hh').
      assert (N' = N) by congruence; subst N'.
      apply (halts_pre p2 1 _ (brk 1 Q2, R2)).
      { cbn [rm_run]. rewrite step_tsite, T2. cbn. rewrite <- HR, Ev. reflexivity. }
      exact (branch_sim N (brk 1 Q1) (brk 1 Q2) k R1 R2 IH Hk HR Hh').
    + assert (Hs : lres (EDecnz r0) Q1 R1 = Some (inc_path Q1, upd R1 r0 v)) by (cbn; rewrite Ev; reflexivity).
      destruct (hn_step p1 _ _ _ _ _ _ T1 ltac:(discriminate) Hs Hh) as (N' & E & Hh').
      assert (N' = N) by congruence; subst N'.
      apply (halts_pre p2 1 _ (inc_path Q2, upd R2 r0 v)).
      { cbn [rm_run]. rewrite step_tsite, T2. cbn. rewrite <- HR, Ev. reflexivity. }
      apply (branch_sim N (inc_path Q1) (inc_path Q2) j (upd R1 r0 v) (upd R2 r0 v) IH Hj); auto.
      intros i. unfold upd. rewrite HR. reflexivity.
  - (* halt *)
    exists 0, (P2, R2). split; [reflexivity|]. apply at_halt_tsite. eauto.
Qed.

End Sound.

Theorem check_sound p1 p2 C : check (ptree p1) (ptree p2) C = true ->
  forall R, rm_halts p1 ([], R) -> rm_halts p2 ([], R).
Proof.
  unfold check. intros Hc R (N & c & Hr & Ha). apply andb_prop in Hc as [Hb HC].
  assert (IH : forall N', N' < S N -> forall P1 P2 j' k' R1 R2, In (P1, P2, j', k') C ->
      (forall i, R1 i = R2 i) -> hn p1 N' (P1, R1) -> rm_halts p2 (P2, R2))
    by (intros N' _; apply (sim p1 p2 C HC N')).
  apply (branch_sim p1 p2 C N [] [] 0 R R IH Hb); [reflexivity|]. exists c. auto.
Qed.

Theorem check_iff p1 p2 C :
  check (ptree p1) (ptree p2) C = true -> check (ptree p2) (ptree p1) (mirror C) = true ->
  forall R, rm_halts p1 ([], R) <-> rm_halts p2 ([], R).
Proof. intros H1 H2 R. split; [apply (check_sound p1 p2 C H1) | apply (check_sound p2 p1 _ H2)]. Qed.
