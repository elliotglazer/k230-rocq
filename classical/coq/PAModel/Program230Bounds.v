(** Every register action in the unchanged5124-node program uses logical0..8. *)
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_edge_register_supported(e:edge):Prop:=
 match e with EInc r|EDecnz r=>(r<9)%nat|_=>True end.
Definition program230_edge_register_check(e:edge):bool:=
 match e with EInc r|EDecnz r=>Nat.ltb r 9|_=>true end.
Lemma program230_edge_register_check_correct e:
 program230_edge_register_check e=true<->program230_edge_register_supported e.
Proof. destruct e;unfold program230_edge_register_check,program230_edge_register_supported;try tauto;apply Nat.ltb_lt. Qed.
Lemma program230_table_length:length p230_tab=nnodes p230.
Proof. reflexivity. Qed.
Lemma program230_register_check:
 forallb(fun row=>program230_edge_register_check(cv(fst row))&&
   program230_edge_register_check(cv(snd row)))p230_tab=true.
Proof. vm_compute;reflexivity. Qed.

Theorem program230_node_register_supported n b:
 (n<nnodes p230)%nat->program230_edge_register_supported(child p230 n b).
Proof.
 intro Hn.
 assert(Hin:In(nth n p230_tab(CH,CH))p230_tab).
 { apply nth_In;rewrite program230_table_length;exact Hn. }
 destruct(nth n p230_tab(CH,CH))as[a c]eqn:E.
 pose proof program230_register_check as HC. rewrite forallb_forall in HC.
 specialize(HC(a,c)Hin);cbn[fst snd]in HC. apply andb_true_iff in HC as[Ha Hc].
 assert(Hnodes:nodes p230 n=(cv a,cv c)).
 {change((let '(a,c) := nth n p230_tab(CH,CH) in (cv a,cv c))=(cv a,cv c));now rewrite E. }
 unfold child;rewrite Hnodes;destruct b;apply program230_edge_register_check_correct;assumption.
Qed.

Theorem program230_walk_register_supported fuel n P i e depth:
 (n<nnodes p230)%nat->walk p230 fuel n P i=Some(e,depth)->
 program230_edge_register_supported e.
Proof.
 induction fuel as[|fuel IH]in n,i|-*;intros Hn HW;[discriminate|].
 rewrite walk_S in HW.
 pose proof(program230_node_register_supported n(bit P i)Hn)as HS.
 pose proof(wf_edges p230 p230_wf n(bit P i)Hn)as HO.
 destruct(child p230 n(bit P i))as[m|r|r|k|k|]eqn:E.
 -apply(IH m(S i));[exact HO|exact HW].
 -injection HW as <- <-;exact HS.
 -injection HW as <- <-;exact HS.
 -injection HW as <- <-;exact HS.
 -injection HW as <- <-;exact HS.
 -injection HW as <- <-;exact HS.
Qed.
Corollary program230_root_register_supported P e depth:
 walk p230(nnodes p230+1)(root p230)P 0=Some(e,depth)->
 program230_edge_register_supported e.
Proof. apply program230_walk_register_supported;exact(wf_root p230 p230_wf). Qed.
Print Assumptions program230_register_check.
Print Assumptions program230_root_register_supported.
