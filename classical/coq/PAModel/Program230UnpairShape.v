(** Reusable literal shape of every public unpair body. *)
From PAModel Require Import Program230TransferProgram.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_unpair_occurrence P a n0 n1 n2 n3 n4 n5 n6:=
 fol p230(ENode(root p230))P=Some(ENode n0) /\
 nodes p230 n0=(EDecnz a,ENode n1) /\nodes p230 n1=(EInc 7,ENode n2) /\
 nodes p230 n2=(ENode n3,EContinue 3) /\nodes p230 n3=(ENode n4,ENode n5) /\
 nodes p230 n4=(EDecnz 6,EBreak 1) /\nodes p230 n5=(EDecnz 7,ENode n6) /\
 nodes p230 n6=(EInc 6,EContinue 2).
Lemma program230_unpair_occurrence_leaves P a n0 n1 n2 n3 n4 n5 n6:
 program230_unpair_occurrence P a n0 n1 n2 n3 n4 n5 n6->
 fol p230(ENode(root p230))(P++[false])=Some(EDecnz a) /\
 fol p230(ENode(root p230))(P++[true;false])=Some(EInc 7) /\
 fol p230(ENode(root p230))(P++[true;true;false;false;false])=Some(EDecnz 6) /\
 fol p230(ENode(root p230))(P++[true;true;false;false;true])=Some(EBreak 1) /\
 fol p230(ENode(root p230))(P++[true;true;true])=Some(EContinue 3) /\
 program230_transfer_occurrence p230(P++[true;true;false;true])7 6 n5 n6.
Proof.
 intros[HP[H0[H1[H2[H3[H4[H5 H6]]]]]]].
 unfold program230_transfer_occurrence;rewrite !fol_app,HP;cbn[fol child].
 rewrite H0;cbn[fst snd fol child];rewrite H1;cbn[fst snd fol child];rewrite H2;
 cbn[fst snd fol child];rewrite H3;cbn[fst snd fol child];rewrite H4;
 cbn[fst snd fol child];repeat split;assumption.
Qed.
Local Ltac path_simpl:=unfold brk,cont,strip_path,inc_path;
 rewrite ?rev_involutive;rewrite !rev_app_distr;cbn[rev inc_rev strip_rev Bool.eqb app];
 rewrite ?rev_involutive;cbn[strip_rev app];rewrite ?strip_rev0,?rev_involutive;repeat rewrite <-app_assoc;reflexivity.
Lemma program230_unpair_inc_input P:inc_path(P++[false])=P++[true].
Proof. apply inc_path_app_false. Qed.
Lemma program230_unpair_inc_right_path P:inc_path(P++[true;false])=P++[true;true].
Proof. path_simpl. Qed.
Lemma program230_unpair_positive_path P:
 inc_path(P++[true;true;false;false;false])=P++[true;true;false;false;true].
Proof. path_simpl. Qed.
Lemma program230_unpair_zero_path P:
 brk 1(P++[true;true;false;false;false])=P++[true;true;false;true].
Proof. path_simpl. Qed.
Lemma program230_unpair_break_path P:
 brk 1(P++[true;true;false;false;true])=P++[true;true;true].
Proof. path_simpl. Qed.
Lemma program230_unpair_transfer_path P:
 inc_path(P++[true;true;false;true])=P++[true;true;true;false].
Proof. path_simpl. Qed.
Lemma program230_unpair_continue_path P:cont 3(P++[true;true;true])=P.
Proof. path_simpl. Qed.
Print Assumptions program230_unpair_occurrence_leaves.
Print Assumptions program230_unpair_continue_path.
