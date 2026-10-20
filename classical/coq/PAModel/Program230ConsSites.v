(** Every literal cons119 implication-construction site in the public program. *)
From PAModel Require Import Model Arithmetic FiniteCoding NumericalProofs Pairing
 Program230PathCode Program230Configurations Program230TransferProgram Program230Copy2Program
 Program230StackStates Program230Scale4States Program230Scale4Program Program230ConsTail Program230ConsGeneric Program230UnpairSites.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Record cons_site := mkConsSite {cons_path:list bool; cons_node:nat; cons_unpair_index:nat}.
Definition cons_site_checked e :=
 let P:=cons_path e in let n:=cons_node e in
 nth_error p230_unpair_sites(cons_unpair_index e)=Some(P++[false;false],2,n+2) /\
 program230_transfer_occurrence p230(P++[false;true])7 2(n+9)(n+10) /\
 program230_copy2_occurrence p230((P++[true;false])++[false])1 7 6(n+13)(n+14)(n+15) /\
 program230_transfer_occurrence p230((P++[true;false])++[true;true;false;true])6 1(n+19)(n+20) /\
 fol p230(ENode(root p230))((P++[true;false])++[true;false])=Some(EDecnz 6) /\
 fol p230(ENode(root p230))((P++[true;false])++[true;true;false;false])=Some(EInc 7) /\
 fol p230(ENode(root p230))((P++[true;false])++[true;true;true])=Some(EContinue 3) /\
 fol p230(ENode(root p230))((P++[true;true])++[false])=Some(EDecnz 7) /\
 fol p230(ENode(root p230))(program230_scale4_leaf(P++[true;true])0)=Some(EInc 1) /\
 fol p230(ENode(root p230))(program230_scale4_leaf(P++[true;true])1)=Some(EInc 1) /\
 fol p230(ENode(root p230))(program230_scale4_leaf(P++[true;true])2)=Some(EInc 1) /\
 fol p230(ENode(root p230))(program230_scale4_leaf(P++[true;true])3)=Some(EInc 1) /\
 fol p230(ENode(root p230))((P++[true;true])++[true;true])=Some(EContinue 2).
Lemma cons_site_shape e:cons_site_checked e->program230_cons_shape(cons_path e).
Proof.
 cbn[cons_site_checked];intros[HU[HT[HC[HPT[HD[HI[HPC[HSD[H0[H1[H2[H3 HSC]]]]]]]]]]]].
 exists(cons_node e+2),(cons_node e+9),(cons_node e+10);split.
 -eapply nth_error_In;exact HU.
 -split;[exact HT|]. split.
  +split;[exists(cons_node e+13),(cons_node e+14),(cons_node e+15);exact HC|].
   split;[exists(cons_node e+19),(cons_node e+20);exact HPT|].
   exact(conj HD(conj HI HPC)).
  +split;[exact HSD|]. split;[|exact HSC].
   intros j Hj;destruct j as[|[|[|[|j]]]];try lia;assumption.
Qed.
Definition p230_cons_sites:list cons_site :=[
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;false;true;false] 100 2;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;false;true;true] 203 5;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;true;true] 255 6;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;false;true] 334 7;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;false;true;false] 414 8;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;false;true;true] 440 9;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;false] 467 10;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;false;true;true;false] 547 11;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;true;true;true;false] 628 12;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;false;false;true;false] 714 13;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;true;false;false] 743 14;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;true;false;true] 769 15;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;false;true;false] 874 16;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;false;false;true] 923 17;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;false;true;false;false] 951 18;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;false;true;true;true] 998 19;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;false] 1052 20;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;false;true;true;false] 1132 21;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;true;true;true;false] 1213 22;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;false;true;false] 1294 23;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;false;false;false] 1323 24;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;false;false;true] 1349 25;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;false;false;false] 1454 26;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;false;true] 1481 27;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;false;true;false] 1591 28;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;false;false;false] 1621 29;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;false;true] 1648 30;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;true;false;true;false] 1728 31;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;false;true;true;false] 1810 32;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;true;true;false] 1889 33;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;false;false;false] 1918 34;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;false;false;true] 1944 35;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;true;false] 2047 36;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;true;true;false] 2074 37;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;false;true;false] 2156 38;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;false;true;false] 2237 39;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;true;false;false] 2266 40;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;true;false;true] 2292 41;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;false;false;true;false] 2398 42;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;false;false;true] 2447 43;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;false;true;false;false] 2475 44;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;false;true;true;true] 2522 45;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;false;true;true;false] 2654 46;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;false] 2683 47;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;false;true;true;false] 2789 48;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;false;true;true;false] 2973 49;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;true;true;false] 3052 50;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;false;false] 3081 51;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;false;true;false] 3108 52;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;true;true;false] 3292 53;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;false;false;true] 3340 54;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;false;true;false] 3367 55;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;false;true;true;true] 3413 56;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;true;false;true] 3460 57;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;true;true;false;false] 3488 58;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;true;true;true;true;true] 3535 59;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;false;false] 3563 60;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;false;true;false] 3590 61;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;false;false] 3620 62;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;false;true;false] 3647 63;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;false;false;true] 3696 64;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;false;true;false] 3723 65;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;false;true;true;true] 3769 66;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;true;false;true] 3816 67;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;true;true;false;false] 3844 68;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;false;true;true;true;true;true] 3891 69;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;false;false] 3919 70;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;false;true;false] 3946 71;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;false;false;true] 3995 72;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;false;true;false] 4022 73;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;false;true;true;true] 4068 74;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;true;false;true] 4115 75;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;true;true;false;false] 4143 76;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;true;true;true;true;true;true;true;true] 4190 77;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;false;true;false] 4271 78;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;false;true;false] 4377 79;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;false;false;false] 4406 80;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;false;true] 4433 81;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;true;false;true;false] 4513 82;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;false;true;false;true;false] 4622 83;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;false;false;false] 4652 84;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;false;true] 4679 85;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;false;false;true] 4727 86;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;false;true;false] 4754 87;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;false;true;true;true] 4800 88;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;true;false;false;true] 4848 89;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;true;false;true;false] 4875 90;
 mkConsSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;true;true;true;false;true;true;true] 4921 91;
 mkConsSite [true;true;true;true;false;false;true] 5060 93].
Lemma p230_cons_sites_correct:Forall cons_site_checked p230_cons_sites.
Proof.
 unfold p230_cons_sites;repeat(apply Forall_cons;[vm_compute;repeat split;reflexivity|]);constructor.
Qed.
Theorem p230_cons_site_history M e base tw stack x rest out:
 In e p230_cons_sites->pair_graph M x rest stack->implication_graph M x tw out->exists u v time,
 program230_program_history M p230 u v time
  (program230_stack_state base(program230_path_value M(cons_path e))tw stack(zeroM M)(zeroM M)) /\
 program230_state_at M u v time
  (program230_stack_state base(program230_path_value M(inc_path(cons_path e++[true;true])))out rest(zeroM M)(zeroM M)) /\
 coding_lt M(zeroM M)time.
Proof.
 intro HE;apply(program230_cons_history M(cons_path e)base tw stack x rest out).
 apply cons_site_shape;exact(proj1(Forall_forall _ _)p230_cons_sites_correct e HE).
Qed.
Print Assumptions p230_cons_sites_correct.
Print Assumptions p230_cons_site_history.
