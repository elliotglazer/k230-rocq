(** Pointwise symbolic register updates, without functional extensionality. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230TransferStates Program230RootHistory
 Program230AXSymbolic Program230AXSymbolicGraphs.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
Unset Implicit Arguments.
Lemma p230_ax_set_register s i expression j:
 (j<9)%nat->program230_register(p230_ax_set s i expression)j=
 (if Nat.eqb j i then expression else program230_register s j).
Proof.
 intro Hj;unfold p230_ax_set,program230_register.
 rewrite program230_config_of_fields by lia;reflexivity.
Qed.
Lemma p230_ax_register_graph_update M env symbolic actual next i expression value:
 p230_ax_register_graph M env symbolic actual ->code_relation M env expression value ->
 program230_register next i=value ->
 (forall j,(j<9)%nat->j<>i->program230_register next j=program230_register actual j) ->
 p230_ax_register_graph M env(p230_ax_set symbolic i expression)next.
Proof.
 intros HG HE HI HF j Hj;rewrite p230_ax_set_register by exact Hj.
 destruct(Nat.eqb j i)eqn:EQ.
 -apply Nat.eqb_eq in EQ;subst j;now rewrite HI.
 -apply Nat.eqb_neq in EQ;rewrite(HF j Hj EQ);apply HG;exact Hj.
Qed.
Lemma p230_ax_register_graph_set M env symbolic actual i expression value pc:
 p230_ax_register_graph M env symbolic actual ->code_relation M env expression value ->
 p230_ax_register_graph M env(p230_ax_set symbolic i expression)
 (program230_transfer_state i i actual pc value value).
Proof.
 intros HG HE j Hj;rewrite p230_ax_set_register by exact Hj.
 rewrite program230_transfer_register by exact Hj.
 destruct(Nat.eqb j i);[exact HE|apply HG;exact Hj].
Qed.
Lemma p230_ax_register_graph_pc M env symbolic actual pc:
 p230_ax_register_graph M env symbolic actual ->
 p230_ax_register_graph M env symbolic(program230_with_pc actual pc).
Proof. intros H i Hi;rewrite program230_with_pc_register;exact(H i Hi). Qed.
Lemma p230_ax_add_graph M env x y a b:
 code_relation M env x a->code_relation M env y b->
 code_relation M env(p230_ax_add x y)(addM M a b).
Proof.
 intros HX HY;unfold p230_ax_add.
 destruct x as[n|i|x1 x2|x1 x2|x1 x2];destruct y as[m|j|y1 y2|y1 y2|y1 y2];
 try(exists a,b;exact(conj HX(conj HY eq_refl))).
 all: try(destruct n as[|n];[cbn in HX;subst a;now rewrite coding_add_zero|]).
 all: try(destruct m as[|m];[cbn in HY;subst b;now rewrite coding_add_zero_r|]).
 all: exists a,b;exact(conj HX(conj HY eq_refl)).
Qed.
Print Assumptions p230_ax_register_graph_update.
Print Assumptions p230_ax_register_graph_set.
Print Assumptions p230_ax_add_graph.
