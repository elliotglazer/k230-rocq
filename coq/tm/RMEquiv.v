(** * RMEquiv: equivalence of the path small-step semantics and the structured big-step
    semantics of RM.v, generically in the program, under a decidable well-formedness
    condition [wf]; plus the "no stray ones" invariant of reachable IPs.

    Main results:
    - [rm_halts_iff_iter : wf p -> forall R, rm_halts p ([], R) <-> iter_halts p R]
    - [wf_wf_run : wf p -> wf_run p]
    - [wf_walk : wf p -> forall P, exists e d, walk p (nnodes p + 1) (root p) P 0 = Some (e, d)]
    - [no_stray] / [reachable_clean]: reachable IPs carry no one at or beyond the walk depth
    - [wf_check_with_sound]: a boolean checker for [wf] given candidate tables.

    Copied from zf/v335/coq/RMEquiv.v; only the zf2-specific lemma [zf2_wf] is removed. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
From K230 Require Import RM.
Import ListNotations.

(** ** Paths in the (unfolded) program tree *)

Definition child (p : prog) (n : nat) (b : bool) : edge :=
  if b then snd (nodes p n) else fst (nodes p n).

(* follow exactly the bits of [Q] starting at edge [e] *)
Fixpoint fol (p : prog) (e : edge) (Q : list bool) : option edge :=
  match Q with
  | [] => Some e
  | b :: Q => match e with ENode n => fol p (child p n b) Q | _ => None end
  end.

Definition is_node (e : edge) : bool := match e with ENode _ => true | _ => false end.

(* IPs equal up to trailing zeros *)
Definition ipeq (P P' : list bool) : Prop := forall i, bit P i = bit P' i.

(** ** Well-formedness *)

Definition edge_ok (p : prog) (e : edge) : Prop :=
  match e with
  | ENode n => n < nnodes p
  | EBreak k | EContinue k => 0 < k
  | _ => True
  end.

(* height of an edge w.r.t. a height table *)
Definition hE (H : nat -> nat) (e : edge) : nat := match e with ENode m => H m | _ => 0 end.
(* largest break / continue level an edge can exit with, w.r.t. tables *)
Definition bE (B : nat -> nat) (e : edge) : nat :=
  match e with ENode m => B m | EDecnz _ => 1 | EBreak k => k | _ => 0 end.
Definition cE (C : nat -> nat) (e : edge) : nat :=
  match e with ENode m => C m | EContinue k => k | _ => 0 end.

Record wf (p : prog) : Prop := {
  wf_root : root p < nnodes p;
  (* children of used nodes are used nodes or leaves; break/continue leaves have k >= 1 *)
  wf_edges : forall n b, n < nnodes p -> edge_ok p (child p n b);
  (* acyclic, and every walk from the root ends within the fuel [nnodes p + 1] *)
  wf_height : exists H : nat -> nat, H (root p) <= nnodes p + 1 /\
      forall n b, n < nnodes p -> hE H (child p n b) < H n;
  (* no break / continue escapes the root *)
  wf_escape : exists B C : nat -> nat, B (root p) = 0 /\ C (root p) = 0 /\
      forall n, n < nnodes p ->
        bE B (fst (nodes p n)) <= S (B n) /\ bE B (snd (nodes p n)) <= B n /\
        cE C (fst (nodes p n)) <= C n /\ cE C (snd (nodes p n)) <= S (C n)
}.

(** ** Elementary facts *)

Lemma bit_nil i : bit [] i = false.
Proof. destruct i; reflexivity. Qed.

Lemma bit_app_l Q T i : i < length Q -> bit (Q ++ T) i = bit Q i.
Proof. intros. unfold bit. apply app_nth1. assumption. Qed.

Lemma ipeq_refl P : ipeq P P.
Proof. intro; reflexivity. Qed.

Lemma ipeq_sym P P' : ipeq P P' -> ipeq P' P.
Proof. intros E i. symmetry. apply E. Qed.

Lemma ipeq_trans P1 P2 P3 : ipeq P1 P2 -> ipeq P2 P3 -> ipeq P1 P3.
Proof. intros E1 E2 i. rewrite E1. apply E2. Qed.

Lemma ipeq_app_false Q : ipeq (Q ++ [false]) Q.
Proof.
  intro i. destruct (lt_dec i (length Q)).
  - apply bit_app_l. assumption.
  - unfold bit. rewrite app_nth2 by lia. rewrite (nth_overflow Q) by lia.
    destruct (i - length Q) as [|[|j]]; reflexivity.
Qed.

Lemma bits_shift a P i d : map (bit (a :: P)) (seq (S i) d) = map (bit P) (seq i d).
Proof. rewrite <- seq_shift, map_map. reflexivity. Qed.

Lemma bits_self Q : map (bit Q) (seq 0 (length Q)) = Q.
Proof.
  induction Q as [|a Q IH]; [reflexivity|].
  simpl length. simpl seq. simpl map. rewrite bits_shift, IH. reflexivity.
Qed.

Lemma pad_bits P d : firstn d (P ++ repeat false d) = map (bit P) (seq 0 d).
Proof.
  apply nth_ext with (d := false) (d' := false).
  - rewrite length_firstn, length_app, repeat_length, length_map, length_seq. lia.
  - intros j Hj. rewrite length_firstn, length_app, repeat_length in Hj.
    rewrite nth_firstn. replace (j <? d) with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite (nth_indep (map (bit P) (seq 0 d)) false (bit P 0)) by (rewrite length_map, length_seq; lia).
    rewrite map_nth, seq_nth by lia. simpl. unfold bit.
    destruct (lt_dec j (length P)).
    + apply app_nth1. assumption.
    + rewrite app_nth2 by lia. rewrite nth_repeat. rewrite nth_overflow by lia. reflexivity.
Qed.

Lemma pad_eq P Q : ipeq P Q -> firstn (length Q) (P ++ repeat false (length Q)) = Q.
Proof.
  intros E. rewrite pad_bits. rewrite (map_ext (bit P) (bit Q) E). apply bits_self.
Qed.

(** ** Path arithmetic at the right end *)

Lemma inc_path_app_false Q : inc_path (Q ++ [false]) = Q ++ [true].
Proof. unfold inc_path. rewrite rev_unit. simpl. rewrite rev_involutive. reflexivity. Qed.

Lemma inc_path_app_true Q : inc_path (Q ++ [true]) = inc_path Q ++ [false].
Proof. unfold inc_path. rewrite rev_unit. reflexivity. Qed.

Lemma strip_rev0 b l : strip_rev b 0 l = l.
Proof. destruct l; reflexivity. Qed.

Lemma strip0 b Q : strip_path b 0 Q = Q.
Proof. unfold strip_path. rewrite strip_rev0. apply rev_involutive. Qed.

Lemma strip_app_same b k Q : strip_path b (S k) (Q ++ [b]) = strip_path b k Q.
Proof. unfold strip_path. rewrite rev_unit. simpl. rewrite eqb_reflx. reflexivity. Qed.

Lemma strip_app_other b k Q : strip_path b (S k) (Q ++ [negb b]) = strip_path b (S k) Q.
Proof. unfold strip_path. rewrite rev_unit. destruct b; reflexivity. Qed.

Lemma brk0 Q : brk 0 Q = inc_path Q.
Proof. unfold brk. rewrite strip0. reflexivity. Qed.

Lemma brk_car1 Q : brk 1 (Q ++ [false]) = inc_path Q.
Proof. unfold brk. rewrite strip_app_same, strip0. reflexivity. Qed.

Lemma brk_carS k Q : brk (S (S k)) (Q ++ [false]) = brk (S k) Q.
Proof. unfold brk. rewrite strip_app_same. reflexivity. Qed.

Lemma brk_cdr k Q : brk (S k) (Q ++ [true]) = brk (S k) Q.
Proof. unfold brk. exact (f_equal inc_path (strip_app_other false k Q)). Qed.

Lemma cont_car k Q : cont (S k) (Q ++ [false]) = cont (S k) Q.
Proof. unfold cont. exact (strip_app_other true k Q). Qed.

Lemma cont_cdr1 Q : cont 1 (Q ++ [true]) = Q.
Proof. unfold cont. rewrite strip_app_same. apply strip0. Qed.

Lemma cont_cdrS k Q : cont (S (S k)) (Q ++ [true]) = cont (S k) Q.
Proof. unfold cont. apply strip_app_same. Qed.

(** ** Following paths *)

Lemma fol_app p e A B :
  fol p e (A ++ B) = match fol p e A with Some e' => fol p e' B | None => None end.
Proof.
  revert e. induction A as [|b A IH]; intros e; simpl; [reflexivity|].
  destruct e; auto.
Qed.

Lemma fol_snoc p e0 Q n b :
  fol p e0 Q = Some (ENode n) -> fol p e0 (Q ++ [b]) = Some (child p n b).
Proof. intros F. rewrite fol_app, F. reflexivity. Qed.

Lemma fol_ok p (W : wf p) e Q e' : edge_ok p e -> fol p e Q = Some e' -> edge_ok p e'.
Proof.
  revert e. induction Q as [|b Q IH]; intros e Ok F; simpl in F.
  - injection F as <-. assumption.
  - destruct e as [n| | | | |]; try discriminate F.
    apply (IH _ (wf_edges p W n b Ok) F).
Qed.

(** ** Walks *)

Lemma walk_S p f n P i :
  walk p (S f) n P i =
  match child p n (bit P i) with ENode m => walk p f m P (S i) | e => Some (e, S i) end.
Proof.
  unfold child. simpl. destruct (nodes p n) as [a b]. simpl.
  destruct (bit P i); [destruct b | destruct a]; reflexivity.
Qed.

Lemma walk_ipeq p f n P P' i : ipeq P P' -> walk p f n P i = walk p f n P' i.
Proof.
  intros E. revert n i. induction f as [|f IH]; intros n i; [reflexivity|].
  rewrite !walk_S, E. destruct (child p n (bit P' i)); auto.
Qed.

Lemma walk_gt p f n P i e d : walk p f n P i = Some (e, d) -> i < d /\ is_node e = false.
Proof.
  revert n i. induction f as [|f IH]; intros n i W; [discriminate|].
  rewrite walk_S in W. destruct (child p n (bit P i)) as [m| | | | |];
    try (injection W as <- <-; split; [lia | reflexivity]).
  apply IH in W as [? ?]. split; [lia | assumption].
Qed.

Lemma walk_fol p f n P i e d :
  walk p f n P i = Some (e, d) -> fol p (ENode n) (map (bit P) (seq i (d - i))) = Some e.
Proof.
  revert n i. induction f as [|f IH]; intros n i W; [discriminate|].
  pose proof (walk_gt _ _ _ _ _ _ _ W) as [Hd _].
  rewrite walk_S in W. replace (d - i) with (S (d - S i)) by lia. simpl.
  destruct (child p n (bit P i)) as [m| | | | |];
    try (injection W as <- <-; rewrite Nat.sub_diag; reflexivity).
  apply IH. assumption.
Qed.

(* the walk goes at least as deep as any path [T] the IP agrees with *)
Lemma walk_ge p f n P i e d T e' :
  walk p f n P i = Some (e, d) -> fol p (ENode n) T = Some e' ->
  (forall j, j < length T -> bit P (i + j) = nth j T false) ->
  i + length T + (if is_node e' then 1 else 0) <= d.
Proof.
  revert f n i e'. induction T as [|b T IH]; intros f n i e' W F A.
  - simpl in F. injection F as <-. apply walk_gt in W. simpl. lia.
  - destruct f as [|f]; [discriminate|]. rewrite walk_S in W.
    assert (Hb : bit P i = b).
    { specialize (A 0). rewrite Nat.add_0_r in A. apply A. simpl. lia. }
    rewrite Hb in W. simpl in F. revert W F.
    destruct (child p n b) as [m| | | | |]; intros W F.
    2-6: destruct T; [|discriminate]; injection F as <-; injection W as _ <-; simpl; lia.
    specialize (IH f m (S i) e' W F). simpl length.
    enough (S i + length T + (if is_node e' then 1 else 0) <= d) by lia.
    apply IH. intros j Hj. replace (S i + j) with (i + S j) by lia. apply (A (S j)). simpl. lia.
Qed.

Section WithHeight.
Variable p : prog.
Hypothesis W : wf p.
Variable H : nat -> nat.
Hypothesis HH : forall n b, n < nnodes p -> hE H (child p n b) < H n.

Lemma walk_path f n P i Q e :
  n < nnodes p -> H n <= f -> fol p (ENode n) Q = Some e -> is_node e = false ->
  (forall j, j < length Q -> bit P (i + j) = nth j Q false) ->
  walk p f n P i = Some (e, i + length Q).
Proof.
  revert f n i. induction Q as [|b Q IHQ]; intros f n i Hn Hf F Hl A.
  - simpl in F. injection F as <-. discriminate Hl.
  - pose proof (HH n b Hn) as Hc.
    destruct f as [|f]; [lia|]. rewrite walk_S.
    assert (Hb : bit P i = b).
    { specialize (A 0). rewrite Nat.add_0_r in A. apply A. simpl. lia. }
    rewrite Hb. simpl in F. pose proof (wf_edges p W n b Hn) as Ok. revert F Hc Ok.
    destruct (child p n b) as [m| | | | |]; intros F Hc Ok.
    2-6: destruct Q; [|discriminate]; injection F as <-; simpl; do 2 f_equal; lia.
    simpl in Hc, Ok. simpl length. replace (i + S (length Q)) with (S i + length Q) by lia.
    apply IHQ; auto; [lia|].
    intros j Hj. replace (S i + j) with (i + S j) by lia. apply (A (S j)). simpl. lia.
Qed.

Lemma walk_some f n P i :
  n < nnodes p -> H n <= f -> exists e d, walk p f n P i = Some (e, d).
Proof.
  revert n i. induction f as [|f IH]; intros n i Hn Hf.
  - pose proof (HH n false Hn). lia.
  - rewrite walk_S. pose proof (HH n (bit P i) Hn) as Hc.
    pose proof (wf_edges p W n (bit P i) Hn) as Ok. revert Hc Ok.
    destruct (child p n (bit P i)) as [m| | | | |]; intros Hc Ok; eauto.
    simpl in Hc, Ok. apply IH; [assumption | lia].
Qed.

End WithHeight.

Lemma wf_walk p : wf p -> forall P, exists e d, walk p (nnodes p + 1) (root p) P 0 = Some (e, d).
Proof.
  intros W P. destruct (wf_height p W) as (H & Hr & HH).
  apply (walk_some p W H HH); [apply (wf_root p W) | assumption].
Qed.

Lemma walk_leaf p (W : wf p) Q e P :
  fol p (ENode (root p)) Q = Some e -> is_node e = false -> ipeq P Q ->
  walk p (nnodes p + 1) (root p) P 0 = Some (e, length Q).
Proof.
  intros F Hl E. destruct (wf_height p W) as (H & Hr & HH).
  change (length Q) with (0 + length Q).
  apply (walk_path p W H HH); auto. apply (wf_root p W).
Qed.

(** ** One step of the path semantics at a leaf *)

Definition leaf_res (e : edge) (Q : list bool) (R : regs) : option conf :=
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

Lemma leaf_step p Q e P R :
  wf p -> fol p (ENode (root p)) Q = Some e -> is_node e = false -> ipeq P Q ->
  rm_step p (P, R) = leaf_res e Q R.
Proof.
  intros W F Hl E. unfold rm_step. cbv beta iota zeta.
  rewrite (walk_leaf p W Q e P F Hl E), (pad_eq P Q E).
  destruct e; reflexivity.
Qed.

Lemma step_ipeq p P P' R : ipeq P P' -> rm_step p (P, R) = rm_step p (P', R).
Proof.
  intros E. unfold rm_step. cbv beta iota zeta.
  rewrite (walk_ipeq _ _ _ _ _ _ E).
  destruct (walk p (nnodes p + 1) (root p) P' 0) as [[e d]|]; [|reflexivity].
  rewrite !pad_bits, (map_ext (bit P) (bit P') E). reflexivity.
Qed.

(** ** Runs *)

Lemma rm_run_S p N c :
  rm_run p (S N) c = match rm_step p c with None => None | Some c' => rm_run p N c' end.
Proof. reflexivity. Qed.

Lemma rm_run_add p a b c :
  rm_run p (a + b) c = match rm_run p a c with Some c' => rm_run p b c' | None => None end.
Proof.
  revert c. induction a as [|a IH]; intro c; [reflexivity|].
  simpl plus. rewrite !rm_run_S. destruct (rm_step p c); auto.
Qed.

(* halts after exactly [N] steps *)
Definition hn (p : prog) (N : nat) (c : conf) : Prop :=
  exists c', rm_run p N c = Some c' /\ at_halt p c'.

Lemma hn_pre p N1 N2 c c1 : rm_run p N1 c = Some c1 -> hn p N2 c1 -> hn p (N1 + N2) c.
Proof. intros H1 (c' & H2 & Ha). exists c'. rewrite rm_run_add, H1. auto. Qed.

Lemma hn_S p N c : hn p (S N) c -> exists c1, rm_step p c = Some c1 /\ hn p N c1.
Proof.
  intros (c' & H & Ha). rewrite rm_run_S in H.
  destruct (rm_step p c) as [c1|]; [|discriminate]. exists c1. split; [reflexivity|]. exists c'. auto.
Qed.

Lemma hn_ipeq p N P P' R : ipeq P P' -> hn p N (P, R) -> hn p N (P', R).
Proof.
  intros E (c' & H & Ha). destruct N as [|N].
  - injection H as <-. exists (P', R). split; [reflexivity|].
    destruct Ha as [d Hd]. exists d. cbn [fst] in *. rewrite <- (walk_ipeq _ _ _ _ _ _ E). exact Hd.
  - exists c'. split; [|assumption]. rewrite rm_run_S in *. rewrite <- (step_ipeq _ _ _ _ E). exact H.
Qed.

(** ** Exit positions *)

Definition target (Q : list bool) (x : exit) : list bool :=
  match x with
  | XNormal => inc_path Q
  | XBreak k => brk k Q
  | XContinue k => cont k Q
  | XHalt => Q
  end.

Lemma run_pos p e R x R' :
  run p e R x R' -> match x with XBreak k | XContinue k => 0 < k | _ => True end.
Proof. induction 1; simpl in *; auto; lia. Qed.

Lemma run_bound p (W : wf p) B C
  (HBC : forall n, n < nnodes p ->
        bE B (fst (nodes p n)) <= S (B n) /\ bE B (snd (nodes p n)) <= B n /\
        cE C (fst (nodes p n)) <= C n /\ cE C (snd (nodes p n)) <= S (C n))
  e R x R' :
  run p e R x R' -> edge_ok p e ->
  match x with XBreak k => k <= bE B e | XContinue k => k <= cE C e | _ => True end.
Proof.
  induction 1; intros Ok;
    try (pose proof (HBC n Ok) as (? & ? & ? & ?);
         pose proof (wf_edges p W n false Ok) as Oa; pose proof (wf_edges p W n true Ok) as Ob;
         cbn [child] in Oa, Ob);
    repeat match goal with
           | IH : edge_ok p _ -> _ |- _ => specialize (IH ltac:(first [exact Oa | exact Ob | exact Ok]))
           end;
    first [assumption | simpl in *; lia | simpl; auto].
Qed.

Lemma wf_wf_run p : wf p -> wf_run p.
Proof.
  intros W R x R' Hr. destruct (wf_escape p W) as (B & C & HB & HC & HBC).
  pose proof (run_bound p W B C HBC _ _ _ _ Hr (wf_root p W)) as Hb.
  pose proof (run_pos _ _ _ _ _ Hr) as Hp.
  destruct x; simpl in Hb, Hp; auto; lia.
Qed.

(** ** Big-step => small-step *)

Definition reaches (p : prog) (c : conf) (Q : list bool) (x : exit) (R' : regs) : Prop :=
  match x with
  | XHalt => exists N, hn p N c
  | _ => exists N P', rm_run p N c = Some (P', R') /\ ipeq P' (target Q x)
  end.

Lemma reaches_pre p N c c1 Q x R' :
  rm_run p N c = Some c1 -> reaches p c1 Q x R' -> reaches p c Q x R'.
Proof.
  intros H1. destruct x; cbn [reaches].
  4: intros (N2 & Hn); exists (N + N2); eapply hn_pre; eauto.
  all: intros (N2 & P' & H2 & E); exists (N + N2), P'; rewrite rm_run_add, H1; auto.
Qed.

Ltac prep_car p Q P n F E IH1 :=
  let Fa := fresh "Fa" in let Fb := fresh "Fb" in let Ea := fresh "Ea" in
  pose proof (fol_snoc p _ Q n false F) as Fa; pose proof (fol_snoc p _ Q n true F) as Fb;
  assert (Ea : ipeq P (Q ++ [false]))
    by (eapply ipeq_trans; [exact E | apply ipeq_sym, ipeq_app_false]);
  specialize (IH1 (Q ++ [false]) P Fa Ea); cbn [reaches target] in IH1.
Ltac prep_cdr p Q P n IH1 IH2 :=
  let N1 := fresh "N1" in let P1 := fresh "P1" in let Hr1 := fresh "Hr1" in let E1 := fresh "E1" in
  destruct IH1 as (N1 & P1 & Hr1 & E1); rewrite inc_path_app_false in E1;
  specialize (IH2 (Q ++ [true]) P1 ltac:(assumption) E1); cbn [reaches target] in IH2.

Lemma fwd p (W : wf p) e R x R' :
  run p e R x R' ->
  forall Q P, fol p (ENode (root p)) Q = Some e -> ipeq P Q -> reaches p (P, R) Q x R'.
Proof.
  induction 1 as [r R|r R v Hv|r R Hv|R|k R|k R|R
                 |n R R' H1 IH1|n k R R' H1 IH1|n k R R' H1 IH1|n R R' H1 IH1
                 |n R R1 R' H1 IH1 H2 IH2|n k R R1 R' H1 IH1 H2 IH2
                 |n R R1 R2 x R' H1 IH1 H2 IH2 H3 IH3|n k R R1 R' H1 IH1 H2 IH2
                 |n R R1 R' H1 IH1 H2 IH2];
    intros Q P F E; cbn [reaches target].
  (* leaves *)
  - exists 1, (inc_path Q). rewrite rm_run_S, (leaf_step p Q _ P R W F eq_refl E).
    split; [reflexivity | apply ipeq_refl].
  - exists 1, (inc_path Q). rewrite rm_run_S, (leaf_step p Q _ P R W F eq_refl E).
    cbn [leaf_res]. rewrite Hv. split; [reflexivity | apply ipeq_refl].
  - exists 1, (brk 1 Q). rewrite rm_run_S, (leaf_step p Q _ P R W F eq_refl E).
    cbn [leaf_res]. rewrite Hv. split; [reflexivity | apply ipeq_refl].
  - exists 1, (brk 0 Q). rewrite rm_run_S, (leaf_step p Q _ P R W F eq_refl E).
    split; [reflexivity | rewrite brk0; apply ipeq_refl].
  - exists 1, (brk (S k) Q). rewrite rm_run_S, (leaf_step p Q _ P R W F eq_refl E).
    split; [reflexivity | apply ipeq_refl].
  - exists 1, (cont (S k) Q). rewrite rm_run_S, (leaf_step p Q _ P R W F eq_refl E).
    split; [reflexivity | apply ipeq_refl].
  - exists 0, (P, R). split; [reflexivity|]. exists (length Q). cbn [fst].
    apply (walk_leaf p W Q EHalt P F eq_refl E).
  (* cons cells *)
  - prep_car p Q P n F E IH1.
    destruct IH1 as (N1 & P1 & Hr1 & E1). rewrite brk_car1 in E1. eauto.
  - prep_car p Q P n F E IH1.
    destruct IH1 as (N1 & P1 & Hr1 & E1). rewrite brk_carS in E1. eauto.
  - prep_car p Q P n F E IH1.
    destruct IH1 as (N1 & P1 & Hr1 & E1). rewrite cont_car in E1. eauto.
  - prep_car p Q P n F E IH1. exact IH1.
  (* the car finished normally, the cdr runs from [Q ++ [true]] *)
  - prep_car p Q P n F E IH1. prep_cdr p Q P n IH1 IH2.
    destruct IH2 as (N2 & P2 & Hr2 & E2). rewrite inc_path_app_true in E2.
    exists (N1 + N2), P2. rewrite rm_run_add, Hr1. split; [exact Hr2|].
    eapply ipeq_trans; [exact E2 | apply ipeq_app_false].
  - prep_car p Q P n F E IH1. prep_cdr p Q P n IH1 IH2.
    destruct IH2 as (N2 & P2 & Hr2 & E2). rewrite brk_cdr in E2.
    exists (N1 + N2), P2. rewrite rm_run_add, Hr1. auto.
  - prep_car p Q P n F E IH1. prep_cdr p Q P n IH1 IH2.
    destruct IH2 as (N2 & P2 & Hr2 & E2). rewrite cont_cdr1 in E2.
    specialize (IH3 Q P2 F E2).
    assert (Hr : rm_run p (N1 + N2) (P, R) = Some (P2, R2)) by (rewrite rm_run_add, Hr1; exact Hr2).
    pose proof (reaches_pre p _ _ _ Q x R' Hr IH3) as G.
    destruct x; exact G.
  - prep_car p Q P n F E IH1. prep_cdr p Q P n IH1 IH2.
    destruct IH2 as (N2 & P2 & Hr2 & E2). rewrite cont_cdrS in E2.
    exists (N1 + N2), P2. rewrite rm_run_add, Hr1. auto.
  - prep_car p Q P n F E IH1. prep_cdr p Q P n IH1 IH2.
    destruct IH2 as (N2 & Hn). exists (N1 + N2). eapply hn_pre; eauto.
Qed.

(** ** Small-step => big-step *)

Definition bwd_goal (p : prog) (N : nat) (e : edge) (Q : list bool) (R : regs) : Prop :=
  exists x R', run p e R x R' /\
    (x = XHalt \/ exists m, 1 <= m <= N /\ hn p (N - m) (target Q x, R')).

Lemma bwd_leaf p (W : wf p) N e Q P R :
  fol p (ENode (root p)) Q = Some e -> is_node e = false -> ipeq P Q -> hn p N (P, R) ->
  bwd_goal p N e Q R.
Proof.
  intros F Hl E Hn.
  pose proof (fol_ok p W (ENode (root p)) Q _ (wf_root p W) F) as Ok.
  destruct e as [n|r|r|k|k|]; try discriminate Hl.
  5: exists XHalt, R; split; [apply run_halt | left; reflexivity].
  all: destruct N as [|N];
    [ exfalso; destruct Hn as (c' & H0 & (d & Hd)); injection H0 as <-; cbn [fst] in Hd;
      rewrite (walk_leaf p W Q _ P F eq_refl E) in Hd; discriminate Hd
    | apply hn_S in Hn; destruct Hn as (c1 & Hs & Hn);
      rewrite (leaf_step p Q _ P R W F eq_refl E) in Hs; cbn [leaf_res] in Hs ].
  - injection Hs as <-. exists XNormal, (upd R r (S (R r))).
    split; [apply run_inc | right; exists 1; split; [lia | rewrite Nat.sub_succ, Nat.sub_0_r; exact Hn]].
  - destruct (R r) as [|v] eqn:Er; injection Hs as <-.
    + exists (XBreak 1), R. split; [now apply run_decnz_zero | right; exists 1; split; [lia | rewrite Nat.sub_succ, Nat.sub_0_r; exact Hn]].
    + exists XNormal, (upd R r v). split; [now apply run_decnz_pos | right; exists 1; split; [lia | rewrite Nat.sub_succ, Nat.sub_0_r; exact Hn]].
  - destruct k as [|k]; [simpl in Ok; lia|]. injection Hs as <-.
    exists (XBreak (S k)), R. split; [apply run_breakS | right; exists 1; split; [lia | rewrite Nat.sub_succ, Nat.sub_0_r; exact Hn]].
  - destruct k as [|k]; [simpl in Ok; lia|]. injection Hs as <-.
    exists (XContinue (S k)), R. split; [apply run_continue | right; exists 1; split; [lia | rewrite Nat.sub_succ, Nat.sub_0_r; exact Hn]].
Qed.

Lemma bwd p (W : wf p) : forall N e Q P R,
  fol p (ENode (root p)) Q = Some e -> ipeq P Q -> hn p N (P, R) -> bwd_goal p N e Q R.
Proof.
  destruct (wf_height p W) as (H & _ & HH).
  intros N. induction N as [N IHN] using lt_wf_ind.
  assert (Hh : forall h e Q P R, hE H e <= h -> fol p (ENode (root p)) Q = Some e -> ipeq P Q ->
                 hn p N (P, R) -> bwd_goal p N e Q R).
  { induction h as [|h IHh]; intros e Q P R He F E Hn;
      (destruct (is_node e) eqn:Hl; [|eapply bwd_leaf; eauto]);
      destruct e as [n| | | | |]; try (cbn in Hl; discriminate Hl);
      pose proof (fol_ok p W (ENode (root p)) Q _ (wf_root p W) F) as Ok; cbn [edge_ok] in Ok;
      pose proof (HH n false Ok) as Ha; pose proof (HH n true Ok) as Hb;
      cbn [child] in Ha, Hb; cbn [hE] in He.
    - lia.
    - pose proof (fol_snoc p _ Q n false F) as Fa; pose proof (fol_snoc p _ Q n true F) as Fb.
      cbn [child] in Fa, Fb.
      assert (Ea : ipeq P (Q ++ [false]))
        by (eapply ipeq_trans; [exact E | apply ipeq_sym, ipeq_app_false]).
      destruct (IHh (fst (nodes p n)) (Q ++ [false]) P R ltac:(lia) Fa Ea Hn)
        as (x1 & R1 & Hr1 & [-> | (m1 & Hm1 & Hn1)]).
      { exists XHalt, R1. split; [now apply run_node_car_halt | now left]. }
      pose proof (run_pos _ _ _ _ _ Hr1) as Hp1.
      destruct x1 as [|k1|k1|]; cbn [target] in Hn1.
      + (* car normal: run the cdr *)
        rewrite inc_path_app_false in Hn1.
        destruct (IHN (N - m1) ltac:(lia) (snd (nodes p n)) (Q ++ [true]) (Q ++ [true]) R1
                    Fb (ipeq_refl _) Hn1) as (x2 & R2 & Hr2 & [-> | (m2 & Hm2 & Hn2)]).
        { exists XHalt, R2. split; [eapply run_node_cdr_halt; eauto | now left]. }
        pose proof (run_pos _ _ _ _ _ Hr2) as Hp2.
        replace (N - m1 - m2) with (N - (m1 + m2)) in Hn2 by lia.
        destruct x2 as [|[|k2]|[|[|k2]]|]; cbn [target] in Hn2; simpl in Hp2; try lia.
        * exists XNormal, R2. split; [eapply run_node_cdr_normal; eauto|].
          right. exists (m1 + m2). split; [lia|]. cbn [target].
          rewrite inc_path_app_true in Hn2. eapply hn_ipeq; [apply ipeq_app_false | exact Hn2].
        * exists (XBreak (S k2)), R2. split; [eapply run_node_cdr_break; eauto|].
          right. exists (m1 + m2). split; [lia|]. cbn [target].
          rewrite brk_cdr in Hn2. exact Hn2.
        * (* continue 1: the cons cell restarts *)
          rewrite cont_cdr1 in Hn2.
          destruct (IHN (N - (m1 + m2)) ltac:(lia) (ENode n) Q Q R2 F (ipeq_refl _) Hn2)
            as (x3 & R3 & Hr3 & Hx3).
          exists x3, R3. split; [eapply run_node_cdr_continue1; eauto|].
          destruct Hx3 as [-> | (m3 & Hm3 & Hn3)]; [now left|].
          right. exists (m1 + m2 + m3). split; [lia|].
          replace (N - (m1 + m2 + m3)) with (N - (m1 + m2) - m3) by lia. exact Hn3.
        * exists (XContinue (S k2)), R2. split; [eapply run_node_cdr_continueS; eauto|].
          right. exists (m1 + m2). split; [lia|]. cbn [target].
          rewrite cont_cdrS in Hn2. exact Hn2.
        * exists XHalt, R2. split; [eapply run_node_cdr_halt; eauto | now left].
      + destruct k1 as [|[|k1]]; simpl in Hp1; [lia| |].
        * exists XNormal, R1. split; [now apply run_node_car_break1|].
          right. exists m1. split; [lia|]. cbn [target]. rewrite brk_car1 in Hn1. exact Hn1.
        * exists (XBreak (S k1)), R1. split; [now apply run_node_car_breakS|].
          right. exists m1. split; [lia|]. cbn [target]. rewrite brk_carS in Hn1. exact Hn1.
      + destruct k1 as [|k1]; simpl in Hp1; [lia|].
        exists (XContinue (S k1)), R1. split; [now apply run_node_car_continue|].
        right. exists m1. split; [lia|]. cbn [target]. rewrite cont_car in Hn1. exact Hn1.
      + exists XHalt, R1. split; [now apply run_node_car_halt | now left]. }
  intros e Q P R. apply (Hh (hE H e)). lia.
Qed.

(** ** The equivalence *)

Theorem rm_halts_iff_iter p : wf p -> forall R, rm_halts p ([], R) <-> iter_halts p R.
Proof.
  intros W R. split.
  - intros (N & c' & Hr & Ha). assert (Hn : hn p N ([], R)) by (exists c'; auto).
    clear c' Hr Ha. revert R Hn. induction N as [N IHN] using lt_wf_ind. intros R Hn.
    destruct (bwd p W N (ENode (root p)) [] [] R eq_refl (ipeq_refl _) Hn)
      as (x & R' & Hr & [-> | (m & Hm & Hn')]).
    + eapply iter_halt; eauto.
    + destruct (wf_wf_run p W R x R' Hr) as [-> | ->].
      * eapply iter_next; [exact Hr|]. apply (IHN (N - m)); [lia | exact Hn'].
      * eapply iter_halt; eauto.
  - induction 1 as [R R' Hr | R R' Hr _ IH].
    + destruct (fwd p W _ _ _ _ Hr [] [] eq_refl (ipeq_refl _)) as (N & c' & Hc & Ha).
      exists N, c'. auto.
    + destruct (fwd p W _ _ _ _ Hr [] [] eq_refl (ipeq_refl _)) as (N1 & P1 & Hr1 & E1).
      destruct IH as (N2 & c' & Hr2 & Ha).
      assert (Hn : hn p N2 (P1, R')).
      { apply hn_ipeq with (P := []); [apply ipeq_sym; exact E1 | exists c'; auto]. }
      destruct (hn_pre p N1 N2 _ _ Hr1 Hn) as (c'' & Hc & Ha').
      exists (N1 + N2), c''. auto.
Qed.

(** ** No stray ones: a reachable IP has only zeros at and beyond the depth of its leaf *)

Lemma inc_rev_shape l :
  (exists m, l = repeat true m /\ inc_rev l = repeat false m) \/
  (exists m l', l = repeat true m ++ false :: l' /\ inc_rev l = repeat false m ++ true :: l').
Proof.
  induction l as [|[|] l IH].
  - left. exists 0. auto.
  - destruct IH as [(m & -> & E) | (m & l' & -> & E)]; simpl; rewrite E.
    + left. exists (S m). auto.
    + right. exists (S m), l'. auto.
  - right. exists 0, l. auto.
Qed.

Lemma inc_path_shape S :
  (exists m, S = repeat true m /\ inc_path S = repeat false m) \/
  (exists m A, S = A ++ false :: repeat true m /\ inc_path S = A ++ true :: repeat false m).
Proof.
  unfold inc_path.
  destruct (inc_rev_shape (rev S)) as [(m & E1 & E2) | (m & l' & E1 & E2)]; rewrite E2.
  - left. exists m. rewrite <- (rev_involutive S), E1, !rev_repeat. auto.
  - right. exists m, (rev l'). rewrite <- (rev_involutive S), E1, !rev_app_distr, !rev_repeat.
    simpl. rewrite <- !app_assoc. auto.
Qed.

Lemma strip_rev_suffix b k l : exists l1, l = l1 ++ strip_rev b k l.
Proof.
  revert k. induction l as [|a l IH]; intros [|k]; simpl; try (exists []; reflexivity).
  destruct (Bool.eqb a b); [destruct (IH k) as [l1 E] | destruct (IH (S k)) as [l1 E]];
    exists (a :: l1); simpl; f_equal; exact E.
Qed.

Lemma strip_path_prefix b k Q : exists T, Q = strip_path b k Q ++ T.
Proof.
  destruct (strip_rev_suffix b k (rev Q)) as [l1 E]. exists (rev l1).
  unfold strip_path. rewrite <- rev_app_distr, <- E. symmetry. apply rev_involutive.
Qed.

Definition clean (p : prog) (P : list bool) : Prop :=
  forall e d, walk p (nnodes p + 1) (root p) P 0 = Some (e, d) -> forall i, d <= i -> bit P i = false.

Lemma clean_prefix p Q e S T : fol p (ENode (root p)) Q = Some e -> Q = S ++ T -> clean p S.
Proof.
  intros F -> e' d Wk i Hi. rewrite fol_app in F.
  destruct (fol p (ENode (root p)) S) as [eS|] eqn:FS; [|discriminate].
  pose proof (walk_ge p _ _ S 0 _ _ S eS Wk FS (fun j _ => eq_refl)) as G.
  unfold bit. apply nth_overflow. lia.
Qed.

Lemma clean_inc p Q e S T :
  fol p (ENode (root p)) Q = Some e -> is_node e = false -> Q = S ++ T -> clean p (inc_path S).
Proof.
  intros F Hl ->.
  destruct (inc_path_shape S) as [(m & _ & ->) | (m & A & -> & ->)].
  - intros e' d _ i _. unfold bit. apply nth_repeat.
  - intros e' d Wk i Hi. rewrite <- app_assoc, fol_app in F.
    destruct (fol p (ENode (root p)) A) as [eA|] eqn:FA; [|discriminate].
    destruct eA as [nA| | | | |]; try discriminate F.
    assert (A' : forall j, j < length A -> bit (A ++ true :: repeat false m) (0 + j) = nth j A false)
      by (intros j Hj; apply bit_app_l; assumption).
    pose proof (walk_ge p _ _ _ 0 _ _ A _ Wk FA A') as G. simpl in G.
    unfold bit. rewrite app_nth2 by lia.
    destruct (i - length A) as [|j] eqn:Ej; [lia|]. simpl. apply nth_repeat.
Qed.

Lemma step_clean p P R P' R' : rm_step p (P, R) = Some (P', R') -> clean p P'.
Proof.
  unfold rm_step. cbv beta iota zeta.
  destruct (walk p (nnodes p + 1) (root p) P 0) as [[e d]|] eqn:Wk; [|discriminate].
  pose proof (walk_fol _ _ _ _ _ _ _ Wk) as F. rewrite Nat.sub_0_r in F.
  pose proof (walk_gt _ _ _ _ _ _ _ Wk) as [_ Hl].
  rewrite pad_bits. set (Q := map (bit P) (seq 0 d)) in *.
  destruct e as [n|r|r|k|k|]; try discriminate.
  - intros Hs. injection Hs as <- _. apply (clean_inc p Q _ Q [] F Hl). symmetry. apply app_nil_r.
  - destruct (R r); intros Hs; injection Hs as <- _.
    + unfold brk. destruct (strip_path_prefix false 1 Q) as [T E]. exact (clean_inc p Q _ _ T F Hl E).
    + apply (clean_inc p Q _ Q [] F Hl). symmetry. apply app_nil_r.
  - intros Hs. injection Hs as <- _.
    unfold brk. destruct (strip_path_prefix false k Q) as [T E]. exact (clean_inc p Q _ _ T F Hl E).
  - intros Hs. injection Hs as <- _.
    unfold cont. destruct (strip_path_prefix true k Q) as [T E]. exact (clean_prefix p Q _ _ T F E).
Qed.

Lemma run_reach p N c c' : rm_run p N c = Some c' -> c' = c \/ exists c0, rm_step p c0 = Some c'.
Proof.
  revert c. induction N as [|N IH]; intros c Hr.
  - injection Hr as <-. now left.
  - rewrite rm_run_S in Hr. destruct (rm_step p c) as [c1|] eqn:Es; [|discriminate].
    destruct (IH c1 Hr) as [-> | Hc]; [right; eauto | right; exact Hc].
Qed.

Lemma forall_skipn P d : (forall i, d <= i -> bit P i = false) -> Forall (fun b => b = false) (skipn d P).
Proof.
  revert d. induction P as [|a P IH]; intros d Hb.
  - rewrite skipn_nil. constructor.
  - destruct d as [|d].
    + constructor; [apply (Hb 0); lia|].
      apply (IH 0). intros i _. apply (Hb (S i)). lia.
    + simpl. apply IH. intros i Hi. apply (Hb (S i)). lia.
Qed.

Theorem no_stray p R0 N P R e d :
  rm_run p N ([], R0) = Some (P, R) ->
  walk p (nnodes p + 1) (root p) P 0 = Some (e, d) ->
  Forall (fun b => b = false) (skipn d P).
Proof.
  intros Hr Wk. apply forall_skipn.
  destruct (run_reach p N _ _ Hr) as [E | ([P0 R1] & Es)].
  - injection E as -> ->. intros i _. apply bit_nil.
  - exact (step_clean p P0 R1 P R Es e d Wk).
Qed.

Corollary reachable_clean p R0 N P R :
  wf p -> rm_run p N ([], R0) = Some (P, R) ->
  exists e d, walk p (nnodes p + 1) (root p) P 0 = Some (e, d) /\
              Forall (fun b => b = false) (skipn d P).
Proof.
  intros W Hr. destruct (wf_walk p W P) as (e & d & Wk).
  exists e, d. split; [exact Wk | exact (no_stray p R0 N P R e d Hr Wk)].
Qed.

(** ** A boolean checker for [wf] *)

Fixpoint iterate {A} (n : nat) (f : A -> A) (x : A) : A :=
  match n with 0 => x | S n => iterate n f (f x) end.

Definition lk (t : list nat) (n : nat) : nat := nth n t 0.
Definition table (p : prog) (f : nat -> nat) : list nat := map f (seq 0 (nnodes p)).

Definition h_step (p : prog) (t : list nat) : list nat :=
  table p (fun n => S (Nat.max (hE (lk t) (fst (nodes p n))) (hE (lk t) (snd (nodes p n))))).
Definition b_step (p : prog) (t : list nat) : list nat :=
  table p (fun n => Nat.max (bE (lk t) (fst (nodes p n)) - 1) (bE (lk t) (snd (nodes p n)))).
Definition c_step (p : prog) (t : list nat) : list nat :=
  table p (fun n => Nat.max (cE (lk t) (fst (nodes p n))) (cE (lk t) (snd (nodes p n)) - 1)).
(* least fixpoints by iteration from 0 (they stabilise after (depth + 1) rounds on a DAG) *)
Definition fix_tab (p : prog) (step : prog -> list nat -> list nat) : list nat :=
  iterate (S (nnodes p)) (step p) (repeat 0 (nnodes p)).

Definition edge_okb (p : prog) (e : edge) : bool :=
  match e with
  | ENode n => n <? nnodes p
  | EBreak k | EContinue k => 0 <? k
  | _ => true
  end.

Definition node_okb (p : prog) (tH tB tC : list nat) (n : nat) : bool :=
  let a := fst (nodes p n) in
  let b := snd (nodes p n) in
  edge_okb p a && edge_okb p b &&
  (hE (lk tH) a <? lk tH n) && (hE (lk tH) b <? lk tH n) &&
  (bE (lk tB) a <=? S (lk tB n)) && (bE (lk tB) b <=? lk tB n) &&
  (cE (lk tC) a <=? lk tC n) && (cE (lk tC) b <=? S (lk tC n)).

Definition wf_check_with (p : prog) (tH tB tC : list nat) : bool :=
  (root p <? nnodes p) && (lk tH (root p) <=? nnodes p + 1) &&
  (lk tB (root p) =? 0) && (lk tC (root p) =? 0) &&
  forallb (node_okb p tH tB tC) (seq 0 (nnodes p)).

Definition wf_check (p : prog) : bool :=
  wf_check_with p (fix_tab p h_step) (fix_tab p b_step) (fix_tab p c_step).

Lemma edge_okb_ok p e : edge_okb p e = true -> edge_ok p e.
Proof. destruct e; simpl; auto; intros H; apply Nat.ltb_lt; assumption. Qed.

Ltac split_bool :=
  repeat match goal with
  | H : _ && _ = true |- _ => apply andb_prop in H; destruct H
  | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
  | H : (_ <=? _) = true |- _ => apply Nat.leb_le in H
  | H : (_ =? _) = true |- _ => apply Nat.eqb_eq in H
  end.

Lemma wf_check_with_sound p tH tB tC : wf_check_with p tH tB tC = true -> wf p.
Proof.
  unfold wf_check_with. intros Hc.
  apply andb_prop in Hc as [Hc Hall]. split_bool.
  rewrite forallb_forall in Hall.
  assert (Hn : forall n, n < nnodes p -> node_okb p tH tB tC n = true)
    by (intros n Hlt; apply Hall, in_seq; lia).
  constructor.
  - assumption.
  - intros n b Hlt. specialize (Hn n Hlt). unfold node_okb in Hn.
    apply andb_prop in Hn as [Hn _]. repeat (apply andb_prop in Hn as [Hn ?]).
    destruct b; apply edge_okb_ok; assumption.
  - exists (lk tH). split; [assumption|].
    intros n b Hlt. specialize (Hn n Hlt). unfold node_okb in Hn. split_bool.
    destruct b; assumption.
  - exists (lk tB), (lk tC). split; [assumption|]. split; [assumption|].
    intros n Hlt. specialize (Hn n Hlt). unfold node_okb in Hn. split_bool. auto.
Qed.

Lemma wf_check_sound p : wf_check p = true -> wf p.
Proof. apply wf_check_with_sound. Qed.

Print Assumptions rm_halts_iff_iter.
Print Assumptions no_stray.
