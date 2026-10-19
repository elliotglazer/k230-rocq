(** Adapted from the pinned m254/L1_Comp254.v; same command calculus with K230 bundle. *)
(** * L1_Comp230: [thm230 1] implies that the enumerator halts.

    A derivation compiles to a command list (zf/m230/logic/compiler.py, validated there through
    spec.enum_step).  Block contract for a code X:
        [blk X L] :  for all T w,  exec L (T, w, 0, 0) is a halt or ends in (X, w, 0, 0).
    Blocks: Discard, a leaf per AX row and per bundle, GEN, and an MP node.  The program
    START ++ Build_F ++ [DROP; NIP; NIP] halts from every retained state, and every candidate
    number is reached unless the enumerator halts earlier. *)
From Coq Require Import Arith Lia Bool List.
From K230L Require Import Codes230 Enum230 Thm230.
Import ListNotations.

(** ** Commands and their encoding *)
Inductive cmd : Type := CMP (x : nat) | CDROP | CNIP | CAX (c x y u : nat).

Definition fields (k : cmd) : list nat :=
  match k with
  | CMP x => [0; x] | CDROP => [1; 0] | CNIP => [2; 0] | CAX c x y u => [S (S (S c)); x; y; u]
  end.

Definition enc_fields (fs : list nat) (r : nat) : nat := fold_right P r fs.

Fixpoint enc_tail (L : list cmd) : nat :=
  match L with [] => 0 | k :: L => S (enc_fields (fields k) (enc_tail L)) end.

(** ** Command semantics on (current, stack, counter, cache) *)
Definition tup : Type := (nat * nat * nat * nat)%type.

Definition xstep (k : cmd) (q : tup) : option tup :=
  let '(t, w, dd, hh) := q in
  match k with
  | CMP x => Some (if Nat.eqb (wim t (dd + x)) hh then (dd + x, P 0 w, dd + x, 0) else (0, w, dd + x, 0))
  | CDROP => Some (hh, P t w, dd, hh)
  | CNIP => if Nat.eqb hh 1 then None else Some (t, snd (unP w), dd, fst (unP w))
  | CAX c x y u => Some (gate (dd + x) (hh + y) c, ax_stack (dd + x) hh (hh + y) c u t w, 0, 0)
  end.

Fixpoint exec (L : list cmd) (q : tup) : option tup :=
  match L with
  | [] => Some q
  | k :: L => match xstep k q with Some q' => exec L q' | None => None end
  end.

Lemma exec_app L1 L2 q :
  exec (L1 ++ L2) q = match exec L1 q with Some q' => exec L2 q' | None => None end.
Proof.
  revert q; induction L1 as [|k L1 IH]; intro q; [reflexivity|].
  cbn. destruct (xstep k q); [apply IH | reflexivity].
Qed.

Definition tupof (s : state) : tup := (tw s, ws s, d s, h s).

(** ** One enumerator step executes one command *)
Lemma step_read s k r np1 :
  (pl s = S (enc_fields (fields k) r) /\ np1 = np s) \/
  (pl s = 0 /\ np s = enc_fields (fields k) r /\ np1 = S (np s)) ->
  enum_step s = match xstep k (tupof s) with
                | Some (t, w, dd, hh) => Some (mkState r np1 t w dd hh)
                | None => None
                end.
Proof.
  intro H. unfold enum_step.
  assert (E : (if Nat.eqb (pl s) 0 then (np s, S (np s)) else (pred (pl s), np s))
              = (enc_fields (fields k) r, np1)).
  { destruct H as [[-> ->] | [-> [-> ->]]]; reflexivity. }
  rewrite E. clear E H. unfold tupof.
  destruct s as [pl0 np0 t w dd hh]; cbn [tw ws d h].
  destruct k as [x| | |c x y u]; cbn [fields enc_fields fold_right]; rewrite !unP_P; cbn [xstep].
  - destruct (Nat.eqb (wim t (dd + x)) hh); reflexivity.
  - now rewrite Nat.add_0_r.
  - rewrite Nat.add_0_r. destruct (Nat.eqb hh 1); [reflexivity|]. now destruct (unP w).
  - reflexivity.
Qed.

Definition halts_from (s : state) : Prop := exists n s', run n s = Some s' /\ enum_step s' = None.

Lemma halts_from_step s s' : enum_step s = Some s' -> halts_from s' -> halts_from s.
Proof. intros E [n [s2 [H1 H2]]]. exists (S n), s2. cbn. now rewrite E. Qed.

Lemma run_tail L : forall s, pl s = enc_tail L -> exec L (tupof s) = None -> halts_from s.
Proof.
  induction L as [|k L IH]; intros s Hp He; [discriminate|].
  cbn [exec] in He. pose proof (step_read s k (enc_tail L) (np s) (or_introl (conj Hp eq_refl))) as E.
  destruct (xstep k (tupof s)) as [[[[t w] dd] hh]|] eqn:X.
  - eapply halts_from_step; [exact E|]. apply IH; [reflexivity | exact He].
  - exists 0, s. split; [reflexivity | exact E].
Qed.

Lemma run_first k L s : pl s = 0 -> np s = enc_fields (fields k) (enc_tail L) ->
  exec (k :: L) (tupof s) = None -> halts_from s.
Proof.
  intros Hp Hn He. cbn [exec] in He.
  pose proof (step_read s k (enc_tail L) (S (np s)) (or_intror (conj Hp (conj Hn eq_refl)))) as E.
  destruct (xstep k (tupof s)) as [[[[t w] dd] hh]|] eqn:X.
  - eapply halts_from_step; [exact E|]. apply (run_tail L); [reflexivity | exact He].
  - exists 0, s. split; [reflexivity | exact E].
Qed.

(** ** Every candidate is reached (unless the enumerator halts earlier) *)
Lemma step_pl s s' : enum_step s = Some s' ->
  pl s' <= (if Nat.eqb (pl s) 0 then np s else pred (pl s)) /\
  np s' = (if Nat.eqb (pl s) 0 then S (np s) else np s).
Proof.
  unfold enum_step. destruct (if Nat.eqb (pl s) 0 then _ else _) as [pl1 np1] eqn:E.
  assert (Hl : pl1 = (if Nat.eqb (pl s) 0 then np s else pred (pl s)) /\
               np1 = (if Nat.eqb (pl s) 0 then S (np s) else np s))
    by (destruct (Nat.eqb (pl s) 0); now injection E as <- <-).
  destruct Hl as [-> ->]. clear E.
  set (z := if Nat.eqb (pl s) 0 then np s else pred (pl s)).
  pose proof (unP_le z) as [_ L1].
  destruct (unP z) as [ac pl2] eqn:E2. cbn in L1.
  pose proof (unP_le pl2) as [_ L2].
  destruct (unP pl2) as [x pl3] eqn:E3. cbn in L2.
  destruct ac as [|[|[|c]]].
  - destruct (Nat.eqb (wim (tw s) (d s + x)) (h s)); intro H; injection H as <-; cbn [pl np]; lia.
  - intro H; injection H as <-; cbn [pl np]; lia.
  - destruct (Nat.eqb (h s) 1); [discriminate|]. destruct (unP (ws s)).
    intro H; injection H as <-; cbn [pl np]; lia.
  - pose proof (unP_le pl3) as [_ L3]. destruct (unP pl3) as [y pl4] eqn:E4. cbn in L3.
    pose proof (unP_le pl4) as [_ L4]. destruct (unP pl4) as [u pl5] eqn:E5. cbn in L4.
    intro H; injection H as <-; cbn [pl np]; lia.
Qed.

Lemma run_add n m s :
  run (n + m) s = match run n s with Some s' => run m s' | None => None end.
Proof.
  revert s; induction n as [|n IH]; intro s; [reflexivity|].
  cbn. destruct (enum_step s); [apply IH | reflexivity].
Qed.

Lemma drain k : forall s, pl s <= k ->
  halts_from s \/ exists n s', run n s = Some s' /\ pl s' = 0 /\ np s' = np s.
Proof.
  induction k as [|k IH]; intros s Hk.
  - right. exists 0, s. split; [reflexivity|]. split; [lia | reflexivity].
  - destruct (pl s) as [|p] eqn:Ep.
    + right. exists 0, s. split; [reflexivity | now split].
    + destruct (enum_step s) as [s1|] eqn:E.
      * pose proof (step_pl s s1 E) as [H1 H2]. rewrite Ep in H1, H2. cbn in H1, H2.
        destruct (IH s1 ltac:(lia)) as [Hh | [n [s2 [R [P0 N0]]]]].
        -- left. exact (halts_from_step s s1 E Hh).
        -- right. exists (S n), s2. cbn. rewrite E. split; [exact R|]. split; [exact P0|]. lia.
      * left. exists 0, s. split; [reflexivity | exact E].
Qed.

Lemma reach m : enum230_halts \/ exists n s, run n s0 = Some s /\ pl s = 0 /\ np s = m.
Proof.
  induction m as [|m [Hh | [n [s [R [P0 N0]]]]]].
  - right. exists 0, s0. repeat split.
  - left. exact Hh.
  - destruct (enum_step s) as [s1|] eqn:E.
    + pose proof (step_pl s s1 E) as [H1 H2]. rewrite P0 in H1, H2. cbn in H1, H2.
      destruct (drain (pl s1) s1 (le_n _)) as [[k [s2 [R2 H2']]] | [k [s2 [R2 [P2 N2]]]]].
      * left. exists (n + S k), s2. split; [|exact H2'].
        rewrite run_add, R. cbn. now rewrite E.
      * right. exists (n + S k), s2. split; [rewrite run_add, R; cbn; now rewrite E|].
        split; [exact P2 | lia].
    + left. exists n, s. now split.
Qed.

Lemma halts_from_reach n s : run n s0 = Some s -> halts_from s -> enum230_halts.
Proof.
  intros R [k [s' [R' H]]]. exists (n + k), s'. split; [|exact H].
  rewrite run_add, R. exact R'.
Qed.

(** ** Facts used by the block computations *)
Lemma eqb_ne1 v : v <> 1 -> Nat.eqb v 1 = false.
Proof. apply Nat.eqb_neq. Qed.

Lemma gate_ne1 a b c : gate a b c <> 1.
Proof.
  unfold gate. destruct (Nat.eqb c a || Nat.eqb c b); [lia | apply bundle_ne_F].
Qed.

Lemma gate_same a b : gate a b a = 0.
Proof. unfold gate. now rewrite Nat.eqb_refl. Qed.

Lemma gate_bundle a b c : c <> a -> c <> b -> gate a b c = bundle a b c.
Proof.
  intros H1 H2. unfold gate. apply Nat.eqb_neq in H1, H2. now rewrite H1, H2.
Qed.

Lemma wim_T1_ne0 T : wim T 1 <> 0.
Proof. apply wim_pos_r. lia. Qed.

Ltac ne1 := first [ apply gate_ne1 | apply wim_ne_F | apply wal_ne_F | apply wex_ne_F
                  | unfold rho1, rho2, rho3, rho4, rho5, rho6, rho7, rho8; first [apply wim_ne_F | apply wex_ne_F]
                  | lia ].

(** one command at a time, keeping the stack terms shared *)
Lemma ex_nip t x w dd hh L : hh <> 1 -> exec (CNIP :: L) (t, P x w, dd, hh) = exec L (t, w, dd, x).
Proof. intro H. cbn [exec xstep]. rewrite (eqb_ne1 hh H), unP_P. reflexivity. Qed.
Lemma ex_nip1 t w dd L : exec (CNIP :: L) (t, w, dd, 1) = None.
Proof. reflexivity. Qed.
Lemma ex_drop t w dd hh L : exec (CDROP :: L) (t, w, dd, hh) = exec L (hh, P t w, dd, hh).
Proof. reflexivity. Qed.
Lemma ex_ax c x y u t w dd hh L : exec (CAX c x y u :: L) (t, w, dd, hh) =
  exec L (gate (dd + x) (hh + y) c, ax_stack (dd + x) hh (hh + y) c u t w, 0, 0).
Proof. reflexivity. Qed.
Lemma ex_mp_ok t x w dd hh L : wim t (dd + x) = hh ->
  exec (CMP x :: L) (t, w, dd, hh) = exec L (dd + x, P 0 w, dd + x, 0).
Proof. intro H. cbn [exec xstep]. now rewrite H, Nat.eqb_refl. Qed.
Lemma ex_mp_fail t x w dd hh L : wim t (dd + x) <> hh ->
  exec (CMP x :: L) (t, w, dd, hh) = exec L (0, w, dd + x, 0).
Proof. intro H. cbn [exec xstep]. apply Nat.eqb_neq in H. now rewrite H. Qed.
Lemma ex_nil q : exec [] q = Some q.
Proof. reflexivity. Qed.

Ltac xrun :=
  repeat first
    [ progress cbn [repeat app Nat.sub]
    | rewrite ex_drop
    | rewrite ex_ax
    | rewrite ex_nip by ne1
    | rewrite ex_nil
    | progress unfold ax_stack
    | rewrite gate_same
    | progress (cbn [Nat.add]; rewrite ?Nat.add_0_r) ].

Definition blk (X : nat) (L : list cmd) : Prop :=
  forall T w, exec L (T, w, 0, 0) = None \/ exec L (T, w, 0, 0) = Some (X, w, 0, 0).


Definition DISCARD : list cmd := [CMP 1; CAX 1 0 0 0] ++ repeat CNIP 10.

Lemma discard T w : exec DISCARD (T, w, 0, 0) = Some (0, w, 0, 0).
Proof.
  unfold DISCARD. cbn [repeat app]. rewrite ex_mp_fail by apply wim_T1_ne0. xrun. reflexivity.
Qed.

Lemma blk_true : blk 0 DISCARD.
Proof. intros T w. right. apply discard. Qed.

(** leaves *)
Definition leaf (j a b c u : nat) : list cmd :=
  DISCARD ++ [CAX c a b u] ++ repeat CNIP j ++ [CDROP] ++ repeat CNIP (11 - j).

Ltac leaf_tac := intros T w; right; unfold leaf; rewrite exec_app, discard; xrun; reflexivity.

Lemma blk_r1 a b c u : blk (rho1 a b) (leaf 1 a b c u).       Proof. leaf_tac. Qed.
Lemma blk_r2 a b c u : blk (rho2 a b c) (leaf 2 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_r3 a b c u : blk (rho3 a b c) (leaf 3 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_r4 a b c u : blk (rho4 a b c) (leaf 4 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_r5 a b c u : blk (rho5 a b c) (leaf 5 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_r6 a b c u : blk (rho6 a c) (leaf 6 a b c u).       Proof. leaf_tac. Qed.
Lemma blk_r7 a b c u : blk (rho7 a b c) (leaf 7 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_r8 a b c u : blk (rho8 a b c u) (leaf 8 a b c u).   Proof. leaf_tac. Qed.

Definition leafB (a b c : nat) : list cmd := DISCARD ++ [CAX c a b 0] ++ repeat CNIP 10.

Lemma blk_bundle a b c : c <> a -> c <> b -> blk (bundle a b c) (leafB a b c).
Proof.
  intros H1 H2 T w. right. unfold leafB. rewrite exec_app, discard. xrun.
  now rewrite gate_bundle.
Qed.

(** GEN *)
Definition genb (i : nat) (L : list cmd) : list cmd :=
  L ++ [CDROP; CNIP; CAX i i 0 0] ++ repeat CNIP 9 ++ [CDROP; CNIP; CNIP].

Lemma blk_gen i X L : blk X L -> blk (wal i X) (genb i L).
Proof.
  intros HL T w. unfold genb. rewrite exec_app.
  destruct (HL T w) as [-> | ->]; [now left|]. right.
  xrun. reflexivity.
Qed.

(** MP node *)
Definition mpb (B : nat) (LA LI : list cmd) : list cmd :=
  LA ++ [CDROP] ++ LI ++ [CNIP; CDROP; CNIP; CMP B; CAX B 0 0 0] ++ repeat CNIP 10 ++ [CDROP; CNIP; CNIP].

Lemma blk_mp A B LA LI : blk A LA -> blk (wim A B) LI -> blk B (mpb B LA LI).
Proof.
  intros HA HI T w. unfold mpb. rewrite exec_app.
  destruct (HA T w) as [-> | ->]; [now left|].
  cbn [app]. rewrite ex_drop, exec_app.
  destruct (HI 0 (P A w)) as [-> | ->]; [now left|].
  cbn [repeat app]. rewrite ex_nip by lia. rewrite ex_drop.
  destruct (Nat.eq_dec A 1) as [EA | EA].
  { left. subst A. apply ex_nip1. }
  rewrite (ex_nip _ _ _ _ _ _ EA). rewrite ex_mp_ok by reflexivity. cbn [Nat.add]. xrun.
  destruct (Nat.eq_dec B 1) as [EB | EB].
  { left. subst B. apply ex_nip1. }
  rewrite (ex_nip _ _ _ _ _ _ EB). xrun. right. reflexivity.
Qed.

(** ** Compilation of derivations *)
Lemma compile X : thm230 X -> exists L, blk X L.
Proof.
  induction 1 as [| t b _ [LA HA] _ [LI HI] | a hh _ [L HL]
                  | a b | a b c | a b c | a b c | a b c | a b | a b c | a b c u | a b c H1 H2].
  - exists DISCARD. exact blk_true.
  - exists (mpb b LA LI). exact (blk_mp t b LA LI HA HI).
  - exists (genb a L). exact (blk_gen a hh L HL).
  - exists (leaf 1 a b 0 0). apply blk_r1.
  - exists (leaf 2 a b c 0). apply blk_r2.
  - exists (leaf 3 a b c 0). apply blk_r3.
  - exists (leaf 4 a b c 0). apply blk_r4.
  - exists (leaf 5 a b c 0). apply blk_r5.
  - exists (leaf 6 a 0 b 0). apply blk_r6.
  - exists (leaf 7 a b c 0). apply blk_r7.
  - exists (leaf 8 a b c u). apply blk_r8.
  - exists (leafB a b c). now apply blk_bundle.
Qed.

(** ** The whole program halts from every retained state *)
Definition START : cmd := CAX 0 1 1 0.
Definition SUFFIX : list cmd := [CDROP; CNIP; CNIP].

Lemma program_halts L : blk 1 L -> forall q, exec (START :: L ++ SUFFIX) q = None.
Proof.
  intros HL [[[t w] dd] hh]. unfold START. rewrite ex_ax, exec_app.
  destruct (HL (gate (dd + 1) (hh + 1) 0) (ax_stack (dd + 1) hh (hh + 1) 0 0 t w)) as [-> | ->];
    [reflexivity|].
  unfold SUFFIX. rewrite ex_drop, ex_nip by lia. apply ex_nip1.
Qed.

Theorem enum_complete : thm230 1 -> enum230_halts.
Proof.
  intro H. destruct (compile 1 H) as [L HL].
  set (N := enc_fields (fields START) (enc_tail (L ++ SUFFIX))).
  destruct (reach N) as [Hh | [n [s [R [P0 N0]]]]]; [exact Hh|].
  apply (halts_from_reach n s R).
  apply (run_first START (L ++ SUFFIX) s P0 N0).
  apply program_halts. exact HL.
Qed.
