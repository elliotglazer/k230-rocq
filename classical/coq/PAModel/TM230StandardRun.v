(** Standard arithmetic traces give literal runs of the frozen public machine. *)
From PAModel Require Import Model FiniteCoding CodeExpressions StandardModel
 TM230LiteralActions TM230BinaryStep TM230RunArithmetic TM230WordStep TM230WordDecoding.
From K230 Require Zip TM230.
From BusyCoq Require TM.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma machine230_state_at_total M b c i:exists s,machine230_state_at M b c i s.
Proof.
 destruct(beta_total M b c(machine230_state_index M i 0))as[q Hq].
 destruct(beta_total M b c(machine230_state_index M i 1))as[l Hl].
 destruct(beta_total M b c(machine230_state_index M i 2))as[h Hh].
 destruct(beta_total M b c(machine230_state_index M i 3))as[r Hr].
 exists(machine230_mk_config(carrier M)q l h r). unfold machine230_state_at;cbn. auto.
Qed.
Lemma machine230_lt_nat a b:coding_lt natModel a b<->a<b.
Proof.
 change((exists d,b=S(a+d))<->a<b). split;[intros[d H];lia|].
 intro H. exists(b-S a). lia.
Qed.
Theorem machine230_arithmetic_run_public b c N:
 machine230_run natModel b c N->
 exists q l h r,
 machine230_state_at natModel b c N(machine230_word_config q l h r)/\
 Public230.TM230.multistep Public230.tm N Public230.TM230.c0
 (K230.Zip.zc(Public230.st q)l(h::r)).
Proof.
 intros[Hseed Hrun].
 assert(HP:forall i,i<=N->exists q l h r,
 machine230_state_at natModel b c i(machine230_word_config q l h r)/\
 Public230.TM230.multistep Public230.tm i Public230.TM230.c0
 (K230.Zip.zc(Public230.st q)l(h::r))).
 {induction i as[|i IH];intro Hi.
  -exists 0,[],false,[]. split;[exact Hseed|]. apply Public230.TM230.multistep_0.
  -destruct(IH ltac:(lia))as(q&l&h&r&Hstate&Hpublic).
   destruct(machine230_state_at_total natModel b c(S i))as[t Ht].
   assert(HS:machine230_step natModel(machine230_word_config q l h r)t).
   {apply(Hrun i(machine230_word_config q l h r)t);[apply machine230_lt_nat;lia|exact Hstate|exact Ht]. }
   destruct(machine230_word_step_complete q l h r t HS)as(q'&l'&h'&r'&E&Hstep).
   subst t. exists q',l',h',r'. split;[exact Ht|].
   replace(S i)with(i+1)by lia. eapply Public230.TM230.multistep_trans;[exact Hpublic|].
   eapply Public230.TM230.multistep_S;[exact Hstep|apply Public230.TM230.multistep_0]. }
 apply HP. lia.
Qed.
Theorem machine230_arithmetic_halts_public:
 machine230_arithmetical_halts natModel->
 Public230.TM230.halts Public230.tm Public230.TM230.c0.
Proof.
 intros(b&c&N&Hrun&Hhalt).
 destruct(machine230_arithmetic_run_public b c N Hrun)as(q&l&h&r&Hstate&Hpublic).
 destruct Hstate as[Hq _].
 pose proof(beta_unique natModel b c(machine230_state_index natModel N 0)q(code_numeral natModel 230)Hq Hhalt)as E.
 rewrite numeral_natModel in E. subst q.
 exists N,(K230.Zip.zc(Public230.st 230)l(h::r)). split;[exact Hpublic|].
 change(Public230.tm(Public230.st 230,h)=None). apply Public230.tm_halt.
Qed.
Print Assumptions machine230_arithmetic_run_public.
Print Assumptions machine230_arithmetic_halts_public.
