(** The bootstrap starts candidate 3 with parameter counter 3. The proof
    search is complete from that state even though it is not the all-zero seed. *)
From Coq Require Import Arith Lia List.
From K230L Require Import Codes230 Thm230 Enum230 L1_Sound230 L1_Comp230.
Import ListNotations.

Definition seed230 : state := mkState 0 3 0 0 3 0.

Lemma reach_from seed k : pl seed = 0 ->
  halts_from seed \/ exists n s, run n seed = Some s /\ pl s = 0 /\ np s = np seed + k.
Proof.
  intros Hseed. induction k as [|k [Hh | [n [s [R [P0 N0]]]]]].
  - right. exists 0, seed. split; [reflexivity|]. split; [exact Hseed|lia].
  - left. exact Hh.
  - destruct (enum_step s) as [s1|] eqn:E.
    + pose proof (step_pl s s1 E) as [H1 H2]. rewrite P0 in H1, H2. cbn in H1, H2.
      destruct (drain (pl s1) s1 (le_n _)) as [[j [s2 [R2 Hhalt]]] | [j [s2 [R2 [P2 N2]]]]].
      * left. exists (n + S j), s2. split; [|exact Hhalt].
        rewrite run_add, R. cbn. now rewrite E.
      * right. exists (n + S j), s2. split; [rewrite run_add, R; cbn; now rewrite E|].
        split; [exact P2|lia].
    + left. exists n, s. now split.
Qed.

Lemma halts_from_reached seed n s : run n seed = Some s ->
  halts_from s -> halts_from seed.
Proof.
  intros R [j [s' [R' H]]]. exists (n + j), s'. split; [|exact H].
  rewrite run_add, R. exact R'.
Qed.

Theorem seed230_complete : thm230 1 -> halts_from seed230.
Proof.
  intros H. destruct (compile 1 H) as [L HL].
  set (N := enc_fields (fields START) (enc_tail (L ++ SUFFIX))).
  assert (HN : 3 <= N).
  { unfold N, START, fields, enc_fields. cbn [fold_right]. apply P_ge_l. }
  destruct (reach_from seed230 (N - 3) eq_refl) as [Hh | [n [s [R [P0 N0]]]]];
    [exact Hh|].
  apply (halts_from_reached seed230 n s R).
  apply (run_first START (L ++ SUFFIX) s P0).
  - change (np s = N). unfold seed230 in N0. cbn [np] in N0. lia.
  - apply program_halts, HL.
Qed.

Theorem seed230_sound : halts_from seed230 -> thm230 1.
Proof.
  intros [n [s [Hr Hs]]]. apply (halt_step s); [|exact Hs].
  apply (Inv_run n seed230 s); [|exact Hr].
  repeat split; [exact T_true|exact T_true|exact good_0].
Qed.

Theorem seed230_iff_thm : halts_from seed230 <-> thm230 1.
Proof. split; [apply seed230_sound|apply seed230_complete]. Qed.
