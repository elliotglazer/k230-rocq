(** Arithmetic graph laws for the native AX constant folding. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230AXSymbolic Program230AXRegisterGraph Program230AXNativeSymbolic.
From Stdlib Require Import Arith.Arith.
Unset Implicit Arguments.
Lemma p230_ax_native_succ_graph M env x a:
 code_relation M env x a->code_relation M env(p230_ax_native_succ x)(succM M a).
Proof.
 destruct x as[n|i|x y|x y|x y];cbn[p230_ax_native_succ].
 -intro H;change(a=code_numeral M n)in H;subst a;reflexivity.
 -intro H;exists a,(code_numeral M 1);split;[exact H|]. split;[reflexivity|apply succ_as_add].
 -destruct y as[n|i|u v|u v|u v];cbn[p230_ax_native_succ].
  +intros[b[c[Hb[Hc E]]]];change(c=code_numeral M n)in Hc;subst c a.
   exists b,(code_numeral M(S n));split;[exact Hb|]. split;[reflexivity|].
   cbn[code_numeral];rewrite(add_comm M b(succM M(code_numeral M n))),add_succ,add_comm;reflexivity.
  +intro H;exists a,(code_numeral M 1);split;[exact H|]. split;[reflexivity|apply succ_as_add].
  +intro H;exists a,(code_numeral M 1);split;[exact H|]. split;[reflexivity|apply succ_as_add].
  +intro H;exists a,(code_numeral M 1);split;[exact H|]. split;[reflexivity|apply succ_as_add].
  +intro H;exists a,(code_numeral M 1);split;[exact H|]. split;[reflexivity|apply succ_as_add].
 -intro H;exists a,(code_numeral M 1);split;[exact H|]. split;[reflexivity|apply succ_as_add].
 -intro H;exists a,(code_numeral M 1);split;[exact H|]. split;[reflexivity|apply succ_as_add].
Qed.
Lemma p230_ax_native_add_graph M env x y a b:
 env 2=addM M(env 1)(env 11)->code_relation M env x a->code_relation M env y b->
 code_relation M env(p230_ax_native_add x y)(addM M a b).
Proof.
 intro HE;destruct x as[n|i|u v|u v|u v];try(apply p230_ax_add_graph).
 destruct i as[|[|i]];try(apply p230_ax_add_graph).
 destruct y as[n|j|u v|u v|u v];try(apply p230_ax_add_graph).
 do 11(destruct j as[|j];[apply p230_ax_add_graph|]).
 destruct j as[|j];[|apply p230_ax_add_graph].
 intros HA HB;change(a=env 1)in HA;change(b=env 11)in HB;subst a b;exact(eq_sym HE).
Qed.
Print Assumptions p230_ax_native_succ_graph.
Print Assumptions p230_ax_native_add_graph.
