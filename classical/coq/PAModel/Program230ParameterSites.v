(** All literal push-then-load-parameter sequences in the public tree. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing Program230PathCode
 Program230Configurations Program230TransferProgram Program230Copy2Program Program230StackStates
 Program230PushSites Program230PushParts Program230ParameterLoad Program230ParameterPushGeneric.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma program230_ipeq_zero_extension P n:ipeq(P++repeat false n)P.
Proof.
 unfold ipeq,bit;intro i;destruct(lt_dec i(length P))as[Hlt|Hge].
 -now rewrite app_nth1 by exact Hlt.
 -rewrite app_nth2 by lia;rewrite nth_repeat;symmetry;apply nth_overflow;lia.
Qed.
Definition program230_parameter_node_graph Q r n:=
 fol p230(ENode(root p230))Q=Some(ENode n) /\
 nodes p230 n=(ENode(n+1),ENode(n+4)) /\
 nodes p230(n+1)=(EDecnz r,ENode(n+2)) /\nodes p230(n+2)=(EInc 1,ENode(n+3)) /\
 nodes p230(n+3)=(EInc 6,EContinue 3) /\nodes p230(n+4)=(EDecnz 6,ENode(n+5)) /\
 nodes p230(n+5)=(EInc r,EContinue 2).
Lemma program230_parameter_node_shape Q r n:
 program230_parameter_node_graph Q r n->program230_parameter_shape Q r.
Proof.
 intros[H0[Hn[H1[H2[H3[H4 H5]]]]]]. split.
 -exists(n+1),(n+2),(n+3);unfold program230_copy2_occurrence;split.
  +rewrite fol_app,H0;cbn[fol child];rewrite Hn;reflexivity.
  +repeat split;assumption.
 -exists(n+4),(n+5);unfold program230_transfer_occurrence;split.
  +rewrite fol_app,H0;cbn[fol child];rewrite Hn;reflexivity.
  +split;assumption.
Qed.
Record parameter_site := mkParameterSite {
 parameter_push:list bool; parameter_load:list bool; parameter_register:nat;
 parameter_load_node:nat; parameter_push_index:nat; parameter_push_node:nat;
 parameter_padding:nat; parameter_load_shorter:bool }.
Definition parameter_site_checked e :=
 (3<=parameter_register e<=5)%nat /\
 nth_error p230_push_site_rows(parameter_push_index e)=Some(parameter_push e,parameter_push_node e) /\
 program230_parameter_node_graph(parameter_load e)(parameter_register e)(parameter_load_node e) /\
 (if parameter_load_shorter e then
  inc_path(parameter_push e++[true;true;true])=parameter_load e++repeat false(parameter_padding e)
 else parameter_load e=inc_path(parameter_push e++[true;true;true])++repeat false(parameter_padding e)).
Definition p230_parameter_sites:list parameter_site:=[
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;false;false;true;false] 4 68 0 49 2 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;false;false;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;false;false;true;true;true] 5 93 1 75 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;false;false;false;true] 3 165 2 147 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;true;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;false;false;true;true;false;true] 4 249 4 231 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;false;false;false;true] 4 303 5 285 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;false;false;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;false;false;true;true] 3 328 6 310 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;false;false;false;true] 5 382 7 364 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;false;false;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;false;false;true;true] 3 407 8 389 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;false;false;true] 3 514 9 496 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;false;true;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;false;true;false;true] 4 540 10 522 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;true;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;true;true;false;false;false;true] 3 597 11 579 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;true;true;false;false;true] [true;true;true;false;true;false;false;true;false;false;true;false;true;false;true;true;true;true;true;true;false;true] 5 621 12 603 4 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;false;false;false;true;false] 4 682 13 663 2 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;false;false;false;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;false;false;false;true;true;true] 5 707 14 689 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;false;true;true;true;true] 4 814 15 796 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;false;false;false;true] 4 842 16 824 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;false;false;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;false;false;true;true] 3 867 17 849 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;false;true;true;true;true] 3 1043 20 1025 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;false;false;true] 3 1099 21 1081 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;false;true;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;false;true;false;true] 4 1125 22 1107 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;true;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;true;true;false;false;false;true] 3 1182 23 1164 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;true;true;false;false;true] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;false;true;true;true;false;true] 5 1206 24 1188 4 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;false;false;true;false] 4 1262 25 1243 2 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;false;false;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;false;false;true;true;true] 5 1287 26 1269 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;false;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;false;true;true] 4 1394 27 1376 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;true;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;true;false;true] 5 1420 28 1402 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;false;true;true;true;true] 3 1445 29 1427 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;false;true] 5 1531 30 1513 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;false;false;false;true] 4 1559 31 1541 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;false;false;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;false;false;true;true] 3 1584 32 1566 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;true;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;true;false;false;true;false] 4 1696 33 1677 2 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;true;false;false;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;false;true;true;true;false;false;true;true;true] 5 1721 34 1703 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;false;false;true] 3 1777 35 1759 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;false;true;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;false;true;false;true] 4 1803 36 1785 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;true;false;false;false;true] 3 1858 37 1840 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;true;false;false;true] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;false;true;false;true] 5 1882 38 1864 4 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;false;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;false;true;true] 4 1989 39 1971 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;true;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;true;false;true] 5 2015 40 1997 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;false;true;true;true;false;true;true;true;true;true;true] 3 2040 41 2022 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;false;false;true;false] 4 2124 42 2105 2 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;false;false;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;false;false;true;true;true] 5 2149 43 2131 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;false;false;false;true] 4 2205 44 2187 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;false;false;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;false;false;true;true] 3 2230 45 2212 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;false;true;true;true;true] 4 2337 46 2319 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;false;false;false;true;false] 4 2366 47 2347 2 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;false;false;false;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;false;false;false;true;true;true] 5 2391 48 2373 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;false;true;true;true;true;true;true] 3 2567 51 2549 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;false;false;true] 3 2595 52 2577 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;false;true;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;false;true;false;false;true] 5 2622 53 2604 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;false;true;false;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;false;true;false;true;true] 3 2647 54 2629 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;false;false;true] 5 2730 55 2712 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;false;true;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;false;true;false;false;true] 5 2757 56 2739 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;false;true;false;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;false;true;false;true;true] 3 2782 57 2764 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;true;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;true;false;true] 4 2835 58 2817 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;false;true;true;true;true] 3 2860 59 2842 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;false;false;true] 4 2888 60 2870 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;false;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;false;true;true] 3 2913 61 2895 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;false;false;true] 3 2940 62 2922 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;false;true;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;false;true;false;true] 4 2966 63 2948 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;true;false;false;false;true] 3 3021 64 3003 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;true;false;false;true] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;false;true;true;false;true] 5 3045 65 3027 4 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;false;false;true] 5 3157 66 3139 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;false;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;false;true;true] 3 3182 67 3164 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;true;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;true;false;true] 5 3208 68 3190 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;false;true;true;true] 3 3233 69 3215 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;true;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;true;false;false;true] 5 3260 70 3242 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;true;false;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;false;true;false;true;true;false;true;true;false;true;true] 3 3285 71 3267 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;false;false;true;false] 4 4239 84 4220 2 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;false;false;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;false;false;true;true;true] 5 4264 85 4246 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;false;true] 3 4317 86 4299 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;false;false;true;false] 4 4345 87 4326 2 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;false;false;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;false;false;true;true;true] 5 4370 88 4352 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;true;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;true;false;false;true;false] 4 4481 89 4462 2 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;true;false;false;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;false;true;true;true;true;false;false;true;true;true] 5 4506 90 4488 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;false;false;true] 3 4562 91 4544 3 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;false;true;false;false;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;false;true;false;false;true;false] 4 4590 92 4571 2 true;
 mkParameterSite [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;false;true;false;false;true;true;false] [true;true;true;false;true;false;false;true;false;false;true;false;true;true;true;true;true;false;false;true;false;false;true;true;true] 5 4615 93 4597 3 true;
 mkParameterSite [true;true;true;false;true;false;true;false] [true;true;true;false;true;false;true;true] 5 5026 98 5008 3 true;
 mkParameterSite [true;true;true;true;false;false;false;false] [true;true;true;true;false;false;false;true] 4 5054 99 5036 3 true;
 mkParameterSite [true;true;true;true;true;true;false] [true;true;true;true;true;true;true] 4 5118 100 5100 3 true].

Lemma p230_parameter_site_count:length p230_parameter_sites=80.
Proof. reflexivity. Qed.
Lemma p230_parameter_sites_checked:Forall parameter_site_checked p230_parameter_sites.
Proof. unfold p230_parameter_sites;repeat(apply Forall_cons;[vm_compute;repeat constructor|]);constructor. Qed.
Theorem p230_parameter_site_history M entry base tw ws value:
 In entry p230_parameter_sites->pair_graph M tw ws value->exists u v time,
 program230_program_history M p230 u v time
  (program230_stack_state base(program230_path_value M(parameter_push entry))tw ws(zeroM M)(zeroM M)) /\
 Program230Configurations.program230_state_at M u v time
  (program230_stack_state base(program230_path_value M(inc_path(parameter_load entry++[true])))
   (program230_register base(parameter_register entry))value(zeroM M)(zeroM M)) /\coding_lt M(zeroM M)time.
Proof.
 intros HE HP.
 pose proof(proj1(Forall_forall _ _)p230_parameter_sites_checked entry HE)as[Hr[HI[HN HC]]].
 assert(Hmem:In(parameter_push entry,parameter_push_node entry)p230_push_site_rows)by(eapply nth_error_In;exact HI).
 pose proof(proj1(Forall_forall _ _)p230_push_site_rows_correct _ Hmem)as HG.
 apply(program230_parameter_push_history M(parameter_push entry)(parameter_load entry)(parameter_register entry)
 base tw ws value);try lia.
 -exact(program230_push_node_shape _ _ HG).
 -exact(program230_parameter_node_shape _ _ _ HN).
 -destruct(parameter_load_shorter entry)eqn:HD.
  +rewrite HC;apply ipeq_sym,program230_ipeq_zero_extension.
  +rewrite HC;apply program230_ipeq_zero_extension.
 -exact HP.
Qed.
Print Assumptions p230_parameter_sites_checked.
Print Assumptions p230_parameter_site_history.
