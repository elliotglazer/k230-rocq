(** Exact standard finite-run packing; no claim of a nonstandard simulation. *)
From PAModel Require Import Model Arithmetic FiniteCoding BetaExtension CodeExpressions StandardModel
 TM230BinaryStep TM230RunArithmetic TM230StandardRun TM230StandardTermination TM230WordStep TM230LiteralActions.
From K230 Require TM230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma machine230_state_at_unique M b c i s t:
 machine230_state_at M b c i s -> machine230_state_at M b c i t -> s=t.
Proof.
 destruct s as[q l h r],t as[q' l' h' r'];unfold machine230_state_at;cbn.
 intros[Hq[Hl[Hh Hr]]][Hq'[Hl'[Hh' Hr']]].
 assert(q=q')by(eapply beta_unique;eassumption).
 assert(l=l')by(eapply beta_unique;eassumption).
 assert(h=h')by(eapply beta_unique;eassumption).
 assert(r=r')by(eapply beta_unique;eassumption). now subst.
Qed.
Lemma machine230_steps_sequence n s t:
 machine230_nat_steps n s t -> exists f:nat->machine230_config nat,
 f 0=s /\ f n=t /\ forall i,i<n->machine230_step natModel(f i)(f(S i)).
Proof.
 intro H. induction H as[s|n s t u Hstep Hsteps[f[Hstart[Hend Hall]]]].
 -exists(fun _=>s). repeat split;try reflexivity. intros;lia.
 -exists(fun i=>match i with 0=>s|S j=>f j end). split;[reflexivity|].
  split;[exact Hend|]. intros[|i]Hi;cbn;[now rewrite Hstart|apply Hall;lia].
Qed.
Lemma machine230_standard_beta_pack(f:nat->nat)n:
 exists b c,forall i,i<n->beta natModel b c i(f i).
Proof.
 induction n as[|n[b[c H]]].
 -exists 0,0. intros;lia.
 -destruct(beta_extension natModel b c n(f n))as[b'[c'[Hold Hnew]]].
  exists b',c'. intros i Hi. destruct(Nat.eq_dec i n)as[->|Hne];[exact Hnew|].
  eapply Hold;[apply machine230_lt_nat;lia|apply H;lia].
Qed.
Fixpoint machine230_config_stream(f:nat->machine230_config nat)(i:nat):nat:=
 match i with
 |0=>machine230_state(f 0)
 |1=>machine230_left(f 0)
 |2=>machine230_head(f 0)
 |3=>machine230_right(f 0)
 |S(S(S(S j)))=>machine230_config_stream(fun k=>f(S k))j
 end.
Lemma machine230_config_stream_fields i f:
 machine230_config_stream f(4*i+0)=machine230_state(f i) /\
 machine230_config_stream f(4*i+1)=machine230_left(f i) /\
 machine230_config_stream f(4*i+2)=machine230_head(f i) /\
 machine230_config_stream f(4*i+3)=machine230_right(f i).
Proof.
 revert f. induction i as[|i IH];intro f;[repeat split;reflexivity|].
 replace(4*S i+0)with(S(S(S(S(4*i+0)))))by lia.
 replace(4*S i+1)with(S(S(S(S(4*i+1)))))by lia.
 replace(4*S i+2)with(S(S(S(S(4*i+2)))))by lia.
 replace(4*S i+3)with(S(S(S(S(4*i+3)))))by lia.
 cbn[machine230_config_stream]. apply IH.
Qed.
Lemma machine230_pack_sequence f n:
 exists b c,forall i,i<=n->machine230_state_at natModel b c i(f i).
Proof.
 destruct(machine230_standard_beta_pack(machine230_config_stream f)(4*(S n)))as[b[c H]].
 exists b,c. intros i Hi. destruct(machine230_config_stream_fields i f)as[Hq[Hl[Hh Hr]]].
 unfold machine230_state_at,machine230_state_index.
 change(beta natModel b c(4*i+0)(machine230_state(f i)) /\
 (beta natModel b c(4*i+1)(machine230_left(f i)) /\
 (beta natModel b c(4*i+2)(machine230_head(f i)) /\
 beta natModel b c(4*i+3)(machine230_right(f i))))).
 split;[exact(eq_ind _ (fun v=>beta natModel b c(4*i+0)v)(H(4*i+0)ltac:(lia)) _ Hq)|].
 split;[exact(eq_ind _ (fun v=>beta natModel b c(4*i+1)v)(H(4*i+1)ltac:(lia)) _ Hl)|].
 split;[exact(eq_ind _ (fun v=>beta natModel b c(4*i+2)v)(H(4*i+2)ltac:(lia)) _ Hh)|exact(eq_ind _ (fun v=>beta natModel b c(4*i+3)v)(H(4*i+3)ltac:(lia)) _ Hr)].
Qed.
Theorem machine230_steps_arithmetic_halt n t:
 machine230_nat_steps n(machine230_seed natModel)t ->machine230_state t=230 ->
 machine230_arithmetical_halts natModel.
Proof.
 intros HS Hterminal.
 destruct(machine230_steps_sequence n(machine230_seed natModel)t HS)as[f[Hstart[Hend Hsteps]]].
 destruct(machine230_pack_sequence f n)as[b[c Hstate]].
 exists b,c,n. split.
 -split;[rewrite <-Hstart;apply Hstate;lia|].
  intros i s u Hi Hs Hu. apply machine230_lt_nat in Hi.
  assert(Es:s=f i)by(eapply machine230_state_at_unique;[exact Hs|apply Hstate;lia]).
  assert(Eu:u=f(S i))by(eapply machine230_state_at_unique;[exact Hu|apply Hstate;lia]).
  subst s u. apply Hsteps;exact Hi.
 -pose proof(Hstate n ltac:(lia))as[Hq _].
  exact(eq_ind _ (fun v=>beta natModel b c(machine230_state_index natModel n 0)v)Hq _
   (eq_trans(f_equal (fun t=>machine230_state t)Hend)Hterminal)).
Qed.
Theorem machine230_public_halts_arithmetic:
 Public230.TM230.halts Public230.tm Public230.TM230.c0 ->machine230_arithmetical_halts natModel.
Proof.
 intros[n H].
 change(Public230.TM230.halts_in Public230.tm(machine230_word_tape 0 [] false [])n)in H.
 destruct(machine230_public_termination_steps n 0 [] false [] ltac:(lia) H)as[t[Hsteps Hstate]].
 exact(machine230_steps_arithmetic_halt n t Hsteps Hstate).
Qed.
Theorem machine230_standard_halts_iff:
 machine230_arithmetical_halts natModel <->Public230.TM230.halts Public230.tm Public230.TM230.c0.
Proof. split;[apply machine230_arithmetic_halts_public|apply machine230_public_halts_arithmetic]. Qed.
Print Assumptions machine230_standard_beta_pack.
Print Assumptions machine230_steps_arithmetic_halt.
Print Assumptions machine230_standard_halts_iff.
