(** The exact finite blank bootstrap lifted into every PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  TM230LiteralActions TM230TransitionArithmetic TM230BinaryStep TM230Paths.
From K230 Require Import Boot230 Zip.
From BusyCoq Require Import TM.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith PArith setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Module B230 := K230.Boot230.

Definition finite_bit M b := code_numeral M (machine230_bit b).
Fixpoint finite_word M (xs : list bool) : carrier M :=
  match xs with
  | [] => zeroM M
  | x :: xs => addM M (finite_bit M x)
      (mulM M (code_numeral M 2) (finite_word M xs))
  end.
Definition finite_config M (s : B230.lconf) :=
  let '(q,l,r) := s in
  machine230_mk_config (carrier M) (code_numeral M q) (finite_word M l)
    (finite_bit M (hd false r)) (finite_word M (tl r)).

Section FiniteLift.
Variable M : Model.
Local Notation O := (zeroM M).
Local Notation N := (code_numeral M).
Add Ring finite_boot_ring : (model_semiring M).

Lemma finite_word_split xs : finite_word M xs =
  addM M (finite_bit M (hd false xs))
    (mulM M (N 2) (finite_word M (tl xs))).
Proof.
  destruct xs; [|reflexivity].
  change (O = addM M O (mulM M (N 2) O)). ring.
Qed.

Lemma finite_table_entry q h w d n :
  Public230.tmn q h = Some(w,d,n) ->
  machine230_transition M (N q) (finite_bit M h) (finite_bit M w)
    (N (machine230_direction d)) (N n).
Proof.
  intro H. exists (q,h,w,d,n). split.
  - now apply (proj2 (machine230_action_exact q h w d n)).
  - repeat split; reflexivity.
Qed.

Lemma finite_step_right q l r w n :
  Public230.tmn q (hd false r) = Some(w,TM.R,n) ->
  machine230_step M (finite_config M (q,l,r))
    (finite_config M (n,w::l,tl r)).
Proof.
  intro H. unfold machine230_step,finite_config.
  cbn [machine230_state machine230_left machine230_head machine230_right].
  exists (finite_bit M w),(N 1). split.
  - exact (finite_table_entry q (hd false r) w TM.R n H).
  - split.
    + destruct (hd false (tl r)); [right|left]; reflexivity.
    + right. split; [reflexivity|]. split.
      * cbn [finite_word]. ring.
      * rewrite (finite_word_split (tl r)). ring.
Qed.

Lemma finite_step_left q l r w n :
  Public230.tmn q (hd false r) = Some(w,TM.L,n) ->
  machine230_step M (finite_config M (q,l,r))
    (finite_config M (n,tl l,hd false l::w::tl r)).
Proof.
  intro H. unfold machine230_step,finite_config.
  cbn [machine230_state machine230_left machine230_head machine230_right hd tl].
  exists (finite_bit M w),(N 0). split.
  - exact (finite_table_entry q (hd false r) w TM.L n H).
  - split.
    + destruct (hd false l); [right|left]; reflexivity.
    + left. split; [reflexivity|]. split.
      * cbn [finite_word]. ring.
      * rewrite (finite_word_split l). ring.
Qed.

Theorem finite_lstep_lift s t : B230.lstep s = Some t ->
  machine230_reaches M (finite_config M s) (finite_config M t).
Proof.
  destruct s as [[q l]r]. unfold B230.lstep.
  destruct (Public230.tmn q (hd false r)) as [[[w d]n]|] eqn:H;
    [destruct d|]; intro E; try discriminate; inversion E; subst t;
    apply machine230_reaches_step.
  - exact (finite_step_left q l r w n H).
  - exact (finite_step_right q l r w n H).
Qed.

Theorem finite_lrunp_lift p : forall s t, B230.lrunp p s = Some t ->
  machine230_reaches M (finite_config M s) (finite_config M t).
Proof.
  induction p as [p IH|p IH|]; intros s t H; cbn [B230.lrunp] in H.
  - destruct (B230.lstep s) as [s1|] eqn:E1; [|discriminate].
    destruct (B230.lrunp p s1) as [s2|] eqn:E2; [|discriminate].
    eapply machine230_reaches_trans; [exact (finite_lstep_lift s s1 E1)|].
    eapply machine230_reaches_trans; [exact (IH s1 s2 E2)|exact (IH s2 t H)].
  - destruct (B230.lrunp p s) as [s1|] eqn:E1; [|discriminate].
    eapply machine230_reaches_trans; [exact (IH s s1 E1)|exact (IH s1 t H)].
  - exact (finite_lstep_lift s t H).
Qed.

Local Opaque B230.lrunp.

Lemma finite_word_zeros n : finite_word M (zeros n) = O.
Proof.
  induction n; [reflexivity|].
  change (addM M O (mulM M (N 2) (finite_word M (zeros n))) = O).
  rewrite IHn. ring.
Qed.

Lemma finite_word_padding xs n : finite_word M (xs ++ zeros n) = finite_word M xs.
Proof. induction xs; [apply finite_word_zeros|]. cbn [app finite_word]. now rewrite IHxs. Qed.

Lemma finite_head_padding xs n : hd false (xs ++ zeros n) = hd false xs.
Proof. destruct xs; [destruct n|]; reflexivity. Qed.

Lemma finite_tail_padding xs n : finite_word M (tl (xs ++ zeros n)) = finite_word M (tl xs).
Proof. destruct xs; [destruct n; [reflexivity|apply finite_word_zeros]|apply finite_word_padding]. Qed.

Lemma finite_config_padding q l r n m :
  finite_config M (q,l ++ zeros n,r ++ zeros m) = finite_config M (q,l,r).
Proof.
  unfold finite_config. rewrite finite_word_padding,finite_head_padding,finite_tail_padding.
  reflexivity.
Qed.

Definition machine230_boot_config := finite_config M (84,[true],B230.boot_right).

Theorem machine230_uniform_boot :
  machine230_reaches M (machine230_seed M) machine230_boot_config.
Proof.
  pose proof B230.boot_ok_true as H.
  unfold B230.boot_ok in H.
  destruct (B230.lrunp 408419 (0,[],[])) as [[[q l]r]|] eqn:E; [|discriminate].
  apply andb_prop in H as [Hq H]. apply andb_prop in H as [Hl Hr].
  apply Nat.eqb_eq in Hq. subst q.
  destruct (list_eq_dec bool_dec (B230.trim l) [true]) as [El|]; [|discriminate].
  destruct (list_eq_dec bool_dec (B230.trim r) B230.boot_right) as [Er|]; [|discriminate].
  pose proof (finite_lrunp_lift 408419 (0,[],[]) (84,l,r) E) as HP.
  destruct (B230.trim_spec l) as [n Hn], (B230.trim_spec r) as [m Hm].
  rewrite Hn,Hm,El,Er,finite_config_padding in HP.
  exact HP.
Qed.
End FiniteLift.

Print Assumptions finite_lstep_lift.
Print Assumptions finite_lrunp_lift.
Print Assumptions machine230_uniform_boot.
