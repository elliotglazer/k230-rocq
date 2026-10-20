(** Actual adjacency and boundary states of the symbolic native AX trace. *)
From PAModel Require Import CodeExpressions Program230Configurations Program230AXSymbolic
 Program230AXNativeSymbolic Program230AXSymbolicTrace.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Fixpoint p230_ax_trace_links(before:program230_configuration code_expr)(rows:list p230_ax_native_row)(final:program230_configuration code_expr):Prop:=
 match rows with []=>before=final|(_,old,next)::tail=>old=before /\p230_ax_trace_links next tail final end.
Lemma p230_ax_trace_and_execute_links ops start rows final:
 p230_ax_native_trace ops start=Some rows->p230_ax_native_execute ops start=Some final->
 p230_ax_trace_links start rows final.
Proof.
 induction ops as[|op tail IH]in start,rows,final|-*;cbn[p230_ax_native_trace p230_ax_native_execute].
 -intros E F;injection E as <-;injection F as <-;reflexivity.
 -destruct(p230_ax_native_step op start)as[next|]eqn:HS;[|discriminate].
  destruct(p230_ax_native_trace tail next)as[rest|]eqn:HT;[|discriminate].
  intros E HF;injection E as <-;split;[reflexivity|]. exact(IH next rest final HT HF).
Qed.
Theorem p230_ax_native_rows_linked:
 p230_ax_trace_links p230_ax_symbolic_initial p230_ax_native_rows p230_ax_symbolic_final.
Proof.
 eapply(p230_ax_trace_and_execute_links p230_ax_native_program).
 -vm_compute;reflexivity.
 -exact p230_ax_native_normalization.
Qed.
Print Assumptions p230_ax_trace_and_execute_links.
Print Assumptions p230_ax_native_rows_linked.
