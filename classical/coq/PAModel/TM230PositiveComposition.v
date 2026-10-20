(** Positive paths compose with arbitrary actual internally coded paths. *)
From PAModel Require Import Model Arithmetic FiniteCoding TM230Paths TM230ExactPaths TM230MacroProgress.
Unset Implicit Arguments.
Theorem machine230_progresses_reaches_trans M s u t:
 machine230_progresses M s u->machine230_reaches M u t->machine230_progresses M s t.
Proof.
 intros[b[c[n[Hn H1]]]][db[dc[k H2]]].
 destruct(machine230_reaches_in_join M n k s u t(ex_intro _ b(ex_intro _ c H1))
  (ex_intro _ db(ex_intro _ dc H2)))as[eb[ec HP]].
 exists eb,ec,(addM M n k);split;[|exact HP].
 destruct Hn as[r Hr]. rewrite coding_add_zero in Hr. rewrite Hr,Arithmetic.add_succ.
 apply coding_zero_lt_succ.
Qed.
Theorem machine230_reaches_progresses_trans M s u t:
 machine230_reaches M s u->machine230_progresses M u t->machine230_progresses M s t.
Proof.
 intros[b[c[n H1]]][db[dc[k[Hk H2]]]].
 destruct(machine230_reaches_in_join M n k s u t(ex_intro _ b(ex_intro _ c H1))
  (ex_intro _ db(ex_intro _ dc H2)))as[eb[ec HP]].
 exists eb,ec,(addM M n k);split;[|exact HP].
 destruct Hk as[r Hr]. rewrite coding_add_zero in Hr. rewrite Hr,Arithmetic.add_comm,Arithmetic.add_succ.
 apply coding_zero_lt_succ.
Qed.
Print Assumptions machine230_progresses_reaches_trans.
Print Assumptions machine230_reaches_progresses_trans.

