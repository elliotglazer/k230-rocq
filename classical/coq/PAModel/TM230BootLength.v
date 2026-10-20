(** Exact path length for the finite blank startup in every PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  TM230LiteralActions TM230BinaryStep TM230RunArithmetic TM230RunComposition
  TM230Paths TM230FiniteBoot.
From K230 Require Import Boot230.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith PArith Lia.
Import ListNotations.
Unset Implicit Arguments.

Lemma finite_numeral_add M a b :
  code_numeral M (a+b) = addM M (code_numeral M a) (code_numeral M b).
Proof.
  induction a; cbn [Nat.add code_numeral].
  - symmetry. apply Arithmetic.add_zero.
  - rewrite IHa,Arithmetic.add_succ. reflexivity.
Qed.

Lemma finite_paths_join M n m s u t b c d e :
  machine230_path M b c (code_numeral M n) s u ->
  machine230_path M d e (code_numeral M m) u t ->
  exists f g, machine230_path M f g (code_numeral M (n+m)) s t.
Proof. rewrite finite_numeral_add. apply machine230_path_join. Qed.

Lemma finite_lstep_path M s t : B230.lstep s = Some t ->
  exists b c, machine230_path M b c (code_numeral M 1)
    (finite_config M s) (finite_config M t).
Proof.
  destruct s as [[q l]r]. unfold B230.lstep.
  destruct (Public230.tmn q (hd false r)) as [[[w d]n]|] eqn:H;
    [destruct d|]; intro E; try discriminate; inversion E; subst t;
    apply machine230_path_one.
  - exact (finite_step_left M q l r w n H).
  - exact (finite_step_right M q l r w n H).
Qed.

Theorem finite_lrunp_path M p : forall s t, B230.lrunp p s = Some t ->
  exists b c, machine230_path M b c (code_numeral M (Pos.to_nat p))
    (finite_config M s) (finite_config M t).
Proof.
  induction p as [p IH|p IH|]; intros s t H; cbn [B230.lrunp] in H.
  - destruct (B230.lstep s) as [s1|] eqn:E1; [|discriminate].
    destruct (B230.lrunp p s1) as [s2|] eqn:E2; [|discriminate].
    destruct (finite_lstep_path M s s1 E1) as [b1 [c1 H1]].
    destruct (IH s1 s2 E2) as [b2 [c2 H2]].
    destruct (IH s2 t H) as [b3 [c3 H3]].
    destruct (finite_paths_join M 1 (Pos.to_nat p) _ _ _ b1 c1 b2 c2 H1 H2)
      as [d [e H12]].
    replace (Pos.to_nat (xI p)) with ((1+Pos.to_nat p)+Pos.to_nat p)%nat
      by (rewrite Pos2Nat.inj_xI; lia).
    exact (finite_paths_join M (1+Pos.to_nat p) (Pos.to_nat p) _ _ _ d e b3 c3 H12 H3).
  - destruct (B230.lrunp p s) as [s1|] eqn:E1; [|discriminate].
    destruct (IH s s1 E1) as [b1 [c1 H1]].
    destruct (IH s1 t H) as [b2 [c2 H2]].
    replace (Pos.to_nat (xO p)) with (Pos.to_nat p+Pos.to_nat p)%nat
      by (rewrite Pos2Nat.inj_xO; lia).
    exact (finite_paths_join M (Pos.to_nat p) (Pos.to_nat p) _ _ _ b1 c1 b2 c2 H1 H2).
  - exact (finite_lstep_path M s t H).
Qed.

Local Opaque B230.lrunp.
Theorem machine230_uniform_boot_exact M :
  exists b c, machine230_path M b c (code_numeral M (Pos.to_nat 408419))
    (machine230_seed M) (machine230_boot_config M).
Proof.
  pose proof B230.boot_ok_true as H. unfold B230.boot_ok in H.
  destruct (B230.lrunp 408419 (0,[],[])) as [[[q l]r]|] eqn:E; [|discriminate].
  apply andb_prop in H as [Hq H]. apply andb_prop in H as [Hl Hr].
  apply Nat.eqb_eq in Hq. subst q.
  destruct (list_eq_dec bool_dec (B230.trim l) [true]) as [El|]; [|discriminate].
  destruct (list_eq_dec bool_dec (B230.trim r) B230.boot_right) as [Er|]; [|discriminate].
  destruct (finite_lrunp_path M 408419 (0,[],[]) (84,l,r) E) as [b [c HP]].
  destruct (B230.trim_spec l) as [n Hn], (B230.trim_spec r) as [m Hm].
  rewrite Hn,Hm,El,Er,finite_config_padding in HP.
  exists b,c. exact HP.
Qed.

Lemma machine230_boot_config_fields M : machine230_boot_config M =
  machine230_mk_config (carrier M) (code_numeral M 84) (code_numeral M 1)
    (zeroM M) (finite_word M (tl B230.boot_right)).
Proof.
  change (machine230_mk_config (carrier M) (code_numeral M 84)
    (addM M (code_numeral M 1) (mulM M (code_numeral M 2) (zeroM M)))
    (zeroM M) (finite_word M (tl B230.boot_right)) =
    machine230_mk_config (carrier M) (code_numeral M 84) (code_numeral M 1)
      (zeroM M) (finite_word M (tl B230.boot_right))).
  rewrite (Arithmetic.mul_comm M (code_numeral M 2) (zeroM M)),
    Arithmetic.mul_zero,coding_add_zero_r. reflexivity.
Qed.

Print Assumptions finite_lrunp_path.
Print Assumptions machine230_uniform_boot_exact.
Print Assumptions machine230_boot_config_fields.
