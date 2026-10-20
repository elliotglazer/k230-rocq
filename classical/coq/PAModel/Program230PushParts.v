(** Finite transfer pieces of pushwff171, retaining padded control words. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions Pairing
 Program230PathCode Program230Configurations Program230TransferProgram Program230TransferLoop
 Program230TransferEntry Program230StackStates Program230PairShape Program230PairEntry.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_push_shape P:=
 (exists n m,program230_transfer_occurrence p230(P++[false])1 6 n m) /\
 (exists n m,program230_transfer_occurrence p230(P++[true;false])2 1 n m) /\
 program230_pair_shape(P++[true;true;false]) /\
 (exists n m,program230_transfer_occurrence p230(P++[true;true;true])7 2 n m).
Section Pieces.
Variable M:Model.
Variable P:list bool.
Hypothesis Hshape:program230_push_shape P.
Local Notation Z:=(zeroM M).
Local Notation cfg:=program230_stack_state.
Local Ltac input := rewrite program230_stack_register by lia;reflexivity.
Local Ltac other HO i Hi := rewrite(HO i Hi ltac:(lia)ltac:(lia));
 rewrite program230_stack_register by exact Hi;
 repeat match goal with H:?i<>?n |- context[Nat.eqb ?i ?n] => rewrite(proj2(Nat.eqb_neq i n)H)end;reflexivity.
Lemma program230_push_first base tw ws:
 exists u v final,program230_program_history M p230 u v(program230_transfer_time M tw)
 (cfg base(program230_path_value M P)tw ws Z Z) /\
 Program230Configurations.program230_state_at M u v(program230_transfer_time M tw)final /\
 final=cfg base(program230_path_value M(P++[true]))Z ws tw Z.
Proof.
 destruct Hshape as[[n[m Hocc]] _].
 set(start:=cfg base(program230_path_value M P)tw ws Z Z).
 destruct(p230_transfer_padded_entry M(P++[false])P 1 6 n m start tw
 ltac:(lia)ltac:(lia)ltac:(lia)Hocc eq_refl(ipeq_sym _ _(ipeq_app_false P))ltac:(unfold start;input))
 as[u[v[final[HR[HT[HP[H1[H6 HO]]]]]]]].
 exists u,v,final;split;[exact HR|]. split;[exact HT|].
 apply program230_stack_frame.
 -rewrite HP,inc_path_app_false;reflexivity.
 -exact H1.
 -rewrite(HO 2 ltac:(lia)ltac:(lia)ltac:(lia));unfold start;input.
 -rewrite H6;unfold start;rewrite program230_stack_register by lia;apply coding_add_zero.
 -rewrite(HO 7 ltac:(lia)ltac:(lia)ltac:(lia));unfold start;input.
 -intros i Hi Hi1 Hi2 Hi6 Hi7;unfold start in HO;other HO i Hi.
Qed.
Lemma program230_push_second base tw ws:
 exists u v final,program230_program_history M p230 u v(program230_transfer_time M ws)
 (cfg base(program230_path_value M(P++[true]))Z ws tw Z) /\
 Program230Configurations.program230_state_at M u v(program230_transfer_time M ws)final /\
 final=cfg base(program230_path_value M(P++[true;true]))ws Z tw Z.
Proof.
 destruct Hshape as[_[[n[m Hocc]] _]].
 set(start:=cfg base(program230_path_value M(P++[true]))Z ws tw Z).
 assert(Heq:ipeq(P++[true])(P++[true;false])).
 {replace(P++[true;false])with((P++[true])++[false])by(rewrite <-app_assoc;reflexivity).
  apply ipeq_sym,ipeq_app_false. }
 destruct(p230_transfer_padded_entry M(P++[true;false])(P++[true])2 1 n m start ws
 ltac:(lia)ltac:(lia)ltac:(lia)Hocc eq_refl Heq ltac:(unfold start;input))
 as[u[v[final[HR[HT[HP[H2[H1 HO]]]]]]]].
 exists u,v,final;split;[exact HR|]. split;[exact HT|].
 apply program230_stack_frame.
 -rewrite HP,Program230PairShape.program230_pair_dec_path;reflexivity.
 -rewrite H1;unfold start;rewrite program230_stack_register by lia;apply coding_add_zero.
 -exact H2.
 -rewrite(HO 6 ltac:(lia)ltac:(lia)ltac:(lia));unfold start;input.
 -rewrite(HO 7 ltac:(lia)ltac:(lia)ltac:(lia));unfold start;input.
 -intros i Hi Hi1 Hi2 Hi6 Hi7;unfold start in HO;other HO i Hi.
Qed.
Lemma program230_push_last base value:
 exists u v final,program230_program_history M p230 u v(program230_transfer_time M value)
 (cfg base(program230_path_value M(P++[true;true;true;false]))Z Z Z value) /\
 Program230Configurations.program230_state_at M u v(program230_transfer_time M value)final /\
 final=cfg base(program230_path_value M(inc_path(P++[true;true;true])))Z value Z Z.
Proof.
 destruct Hshape as[_[_[_[n[m Hocc]]]]].
 set(start:=cfg base(program230_path_value M(P++[true;true;true;false]))Z Z Z value).
 assert(Heq:ipeq(P++[true;true;true;false])(P++[true;true;true])).
 {replace(P++[true;true;true;false])with((P++[true;true;true])++[false])by(rewrite <-app_assoc;reflexivity).
  apply ipeq_app_false. }
 destruct(p230_transfer_padded_entry M(P++[true;true;true])(P++[true;true;true;false])7 2 n m start value
 ltac:(lia)ltac:(lia)ltac:(lia)Hocc eq_refl Heq ltac:(unfold start;input))
 as[u[v[final[HR[HT[HP[H7[H2 HO]]]]]]]].
 exists u,v,final;split;[exact HR|]. split;[exact HT|].
 apply program230_stack_frame.
 -exact HP.
 -rewrite(HO 1 ltac:(lia)ltac:(lia)ltac:(lia));unfold start;input.
 -rewrite H2;unfold start;rewrite program230_stack_register by lia;apply coding_add_zero.
 -rewrite(HO 6 ltac:(lia)ltac:(lia)ltac:(lia));unfold start;input.
 -exact H7.
 -intros i Hi Hi1 Hi2 Hi6 Hi7;unfold start in HO;other HO i Hi.
Qed.
End Pieces.
Print Assumptions program230_push_first.
Print Assumptions program230_push_second.
Print Assumptions program230_push_last.
