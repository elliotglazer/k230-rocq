(** Finite control tables for literal primitive cycles. *)
From PAModel Require Import Model Arithmetic Program230Configurations Program230Histories
 Program230PathCode Program230Edges Program230Copy2States.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_control_row:Type:=(list bool*list bool*edge)%type.
Fixpoint program230_control_table_formula(rows:list program230_control_row):form:=
 match rows with []=>⊥|((source,Q),e)::rest=>
 program230_control_leaf_formula source Q e ∨program230_control_table_formula rest end.
Lemma program230_control_table_correct M rows s t:
 Program230Histories.program230_step M(program230_control_table_formula rows)s t<->
 exists source Q e,In((source,Q),e)rows /\program230_pc s = program230_path_value M source /\
 program230_edge_step M Q e(program230_register s)(program230_register t)(program230_pc t).
Proof.
 induction rows as[|[[src Q]e]rows IH];[split;[contradiction|intros[x[y[z[H _]]]];contradiction]|].
 change((Program230Histories.program230_step M(program230_control_leaf_formula src Q e)s t \/
 Program230Histories.program230_step M(program230_control_table_formula rows)s t)<->
 exists source Q' e',In((source,Q'),e')(((src,Q),e)::rows) /\program230_pc s = program230_path_value M source /\
 program230_edge_step M Q' e'(program230_register s)(program230_register t)(program230_pc t)).
 rewrite program230_control_leaf_correct,IH;split.
 -intros[H|[x[y[z[HI H]]]]];[exists src,Q,e;split;[now left|exact H]|exists x,y,z;split;[now right|exact H]].
 -intros[x[y[z[[E|HI]H]]]];[inversion E;subst;now left|right;exists x,y,z;auto].
Qed.
Lemma program230_control_table_intro M rows source Q e s t:
 In((source,Q),e)rows->program230_pc s = program230_path_value M source->
 program230_edge_step M Q e(program230_register s)(program230_register t)(program230_pc t)->
 Program230Histories.program230_step M(program230_control_table_formula rows)s t.
Proof. intros HI HP HE;apply program230_control_table_correct;exists source,Q,e;auto. Qed.
Lemma program230_true_extension P n:(P++repeat true n)++[true] = P++repeat true(S n).
Proof. rewrite <-app_assoc;f_equal;induction n;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma program230_true_increment P n:
 inc_path((P++repeat true n)++[false]) = P++repeat true(S n).
Proof. rewrite inc_path_app_false;apply program230_true_extension. Qed.
Lemma program230_true_continue P n:cont(S n)(P++repeat true(S n)) = P.
Proof.
 induction n as[|n IH];[apply cont_cdr1|].
 rewrite <-program230_true_extension,cont_cdrS;exact IH.
Qed.
Print Assumptions program230_control_table_correct.
