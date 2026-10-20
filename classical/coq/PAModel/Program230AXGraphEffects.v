(** Literal graph preservation for the native AX register actions. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions NumericalProofs
 Program230Configurations Program230TransferStates Program230AXSymbolic Program230AXSymbolicGraphs
 Program230AXRegisterGraph Program230AXNativeSymbolic Program230AXNativeArithmetic.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
Unset Implicit Arguments.
Definition p230_ax_actual_set M(s:program230_configuration(carrier M))i value pc:=
 program230_transfer_state i i s pc value value.
Lemma p230_ax_actual_set_register M s i value pc j:
 (j<9)%nat->program230_register(p230_ax_actual_set M s i value pc)j=
 if Nat.eqb j i then value else program230_register s j.
Proof. intro Hj;unfold p230_ax_actual_set;rewrite program230_transfer_register by exact Hj;destruct(Nat.eqb j i);reflexivity. Qed.
Lemma p230_ax_graph_actual_set M env symbolic actual i expression value pc:
 p230_ax_register_graph M env symbolic actual ->code_relation M env expression value ->
 p230_ax_register_graph M env(p230_ax_set symbolic i expression)(p230_ax_actual_set M actual i value pc).
Proof. apply p230_ax_register_graph_set. Qed.
Lemma p230_ax_pair_graph M env x y a b out:
 code_relation M env x a->code_relation M env y b->pair_graph M a b out->
 code_relation M env(CEpair x y)out.
Proof. intros HX HY HP;exists a,b;exact(conj HX(conj HY HP)). Qed.
Lemma p230_ax_implication_graph M env x y a b out:
 code_relation M env x a->code_relation M env y b->implication_graph M a b out->
 code_relation M env(E_wim x y)out.
Proof.
 intros HX HY [four[pair[Hfour[[aa[bb[HA[HB HP]]]] HO]]]].
 change(four=code_numeral M 4)in Hfour;change(aa=a)in HA;change(bb=b)in HB.
 subst four aa bb;exists(code_numeral M 4),pair;split;[reflexivity|].
 exact(conj(p230_ax_pair_graph M env x y a b pair HX HY HP)HO).
Qed.

Lemma p230_ax_graph_push M env symbolic actual word pc:
 p230_ax_register_graph M env symbolic actual ->
 pair_graph M(program230_register actual 1)(program230_register actual 2)word ->
 p230_ax_register_graph M env(p230_ax_push symbolic(CEconst 0))
 (p230_ax_actual_set M(p230_ax_actual_set M actual 2 word pc)1(zeroM M)pc).
Proof.
 intros HG HP;unfold p230_ax_push;apply p230_ax_graph_actual_set;[|reflexivity].
 apply p230_ax_graph_actual_set;[exact HG|].
 apply(p230_ax_pair_graph M env _ _ _ _ _ (HG 1 ltac:(lia))(HG 2 ltac:(lia))HP).
Qed.
Lemma p230_ax_graph_load M env symbolic actual r pc:
 p230_ax_register_graph M env symbolic actual ->(r<9)%nat->
 p230_ax_register_graph M env(p230_ax_set symbolic 1(program230_register symbolic r))
 (p230_ax_actual_set M actual 1(program230_register actual r)pc).
Proof. intros HG Hr;apply p230_ax_graph_actual_set;[exact HG|exact(HG r Hr)]. Qed.
Lemma p230_ax_graph_inc M env symbolic actual pc:
 p230_ax_register_graph M env symbolic actual ->
 p230_ax_register_graph M env(p230_ax_set symbolic 1(p230_ax_native_succ(program230_register symbolic 1)))
 (p230_ax_actual_set M actual 1(succM M(program230_register actual 1))pc).
Proof. intro HG;apply p230_ax_graph_actual_set;[exact HG|apply p230_ax_native_succ_graph;exact(HG 1 ltac:(lia))]. Qed.
Lemma p230_ax_graph_transfer M env symbolic actual a b pc:
 env 2=addM M(env 1)(env 11)->p230_ax_register_graph M env symbolic actual ->
 (a<9)%nat->(b<9)%nat->
 p230_ax_register_graph M env
 (p230_ax_set(p230_ax_set symbolic b(p230_ax_native_add(program230_register symbolic b)(program230_register symbolic a)))a(CEconst 0))
 (p230_ax_actual_set M(p230_ax_actual_set M actual b(addM M(program230_register actual b)(program230_register actual a))pc)a(zeroM M)pc).
Proof.
 intros HE HG Ha Hb;apply p230_ax_graph_actual_set;[|reflexivity].
 apply p230_ax_graph_actual_set;[exact HG|apply p230_ax_native_add_graph;[exact HE|exact(HG b Hb)|exact(HG a Ha)]].
Qed.
Lemma p230_ax_graph_cons M env symbolic actual x tail value rest out pc:
 p230_ax_register_graph M env symbolic actual ->program230_register symbolic 2=CEpair x tail ->
 code_relation M env x value ->code_relation M env tail rest ->
 implication_graph M value(program230_register actual 1)out ->
 p230_ax_register_graph M env(p230_ax_set(p230_ax_set symbolic 1(E_wim x(program230_register symbolic 1)))2 tail)
 (p230_ax_actual_set M(p230_ax_actual_set M actual 1 out pc)2 rest pc).
Proof.
 intros HG HS HX HT HI;apply p230_ax_graph_actual_set;[|exact HT].
 apply p230_ax_graph_actual_set;[exact HG|].
 apply(p230_ax_implication_graph M env _ _ _ _ _ HX(HG 1 ltac:(lia))HI).
Qed.
Lemma p230_ax_graph_unpair M env symbolic actual x y ix iy pc:
 p230_ax_register_graph M env symbolic actual ->x=env ix ->y=env iy ->
 p230_ax_register_graph M env
 (p230_ax_set(p230_ax_set(p230_ax_set symbolic 8(CEconst 0))6(CEvar ix))7(CEvar iy))
 (p230_ax_actual_set M(p230_ax_actual_set M(p230_ax_actual_set M actual 8(zeroM M)pc)6 x pc)7 y pc).
Proof.
 intros HG HX HY;apply p230_ax_graph_actual_set;[|exact HY].
 apply p230_ax_graph_actual_set;[|exact HX]. apply p230_ax_graph_actual_set;[exact HG|reflexivity].
Qed.
Print Assumptions p230_ax_implication_graph.
Print Assumptions p230_ax_graph_push.
Print Assumptions p230_ax_graph_transfer.
Print Assumptions p230_ax_graph_cons.
