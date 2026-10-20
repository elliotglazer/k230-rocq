(** Checked copy and transfer subruns of the first pair constructor. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230Configurations Program230Histories Program230HistoryConstructors Program230HistoryJoin
 Program230TransferStates Program230TransferLoop Program230TransferProgram Program230Copy2States Program230Copy2Loop
 Program230Copy2Program Program230ThreeFieldFrame Program230InstructionFormula
 Program230PairConstructorIteration Program230PairShape.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Section Parts.
Variable M:Model.
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Notation N := (code_numeral M).
Variable P:list bool.
Hypothesis Hshape:program230_pair_shape P.
Local Notation cfg := program230_pair_state.
Lemma program230_pair_shape_copy_prefix base x y z:
 exists u v,program230_history M p230_instruction_formula u v(program230_copy2_time M y)
 (cfg base(program230_path_value M(P++[false]))x y z) /\
 program230_state_at M u v(program230_copy2_time M y)
 (cfg base(program230_path_value M(P++[true]))(addM M x y)Z(addM M z y)).
Proof.
 destruct Hshape as[[n[m[k Hocc]]] _].
 set(start:=cfg base(program230_path_value M(P++[false]))x y z).
 assert(Hy:program230_register start 1 = y).
 {unfold start,program230_pair_state;rewrite program230_copy2_register by lia;reflexivity. }
 destruct(program230_copy2_program_history M p230(P++[false])1 7 6 n m k start y
 ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Hocc eq_refl Hy)
 as[u[v[final[HR[HT[HP[H1[H7[H6 HO]]]]]]]]].
 assert(E:final = cfg base(program230_path_value M(P++[true]))(addM M x y)Z(addM M z y)).
 {apply program230_three_field_frame.
  -rewrite HP,inc_path_app_false;reflexivity.
  -rewrite H6;unfold start,program230_pair_state;rewrite program230_copy2_register by lia;reflexivity.
  -exact H1.
  -rewrite H7;unfold start,program230_pair_state;rewrite program230_copy2_register by lia;reflexivity.
  -intros i Hi Hi6 Hi1 Hi7;rewrite(HO i Hi Hi1 Hi7 Hi6).
   unfold start,program230_pair_state;rewrite program230_copy2_register by exact Hi.
   now rewrite(proj2(Nat.eqb_neq i 6)Hi6),(proj2(Nat.eqb_neq i 1)Hi1),(proj2(Nat.eqb_neq i 7)Hi7). }
 exists u,v;split;[apply(proj2(p230_instruction_history_correct M u v(program230_copy2_time M y)start));exact HR|].
 now rewrite <-E.
Qed.
Lemma program230_pair_shape_transfer_tail base k z:
 exists u v,program230_history M p230_instruction_formula u v(program230_transfer_time M k)
 (cfg base(program230_path_value M(P++[true;true;false;true]))k Z z) /\
 program230_state_at M u v(program230_transfer_time M k)
 (cfg base(program230_path_value M(P++[true;true;true;false]))Z k z).
Proof.
 destruct Hshape as[_[[n[m Hocc]] _]].
 set(start:=cfg base(program230_path_value M(P++[true;true;false;true]))k Z z).
 assert(Hk:program230_register start 6 = k).
 {unfold start,program230_pair_state;rewrite program230_copy2_register by lia;reflexivity. }
 destruct(program230_transfer_program_history M p230(P++[true;true;false;true])6 1 n m start k
 ltac:(lia)ltac:(lia)ltac:(lia)Hocc eq_refl Hk)
 as[u[v[final[HR[HT[HP[H6[H1 HO]]]]]]]].
 assert(E:final = cfg base(program230_path_value M(P++[true;true;true;false]))Z k z).
 {apply program230_three_field_frame.
  -rewrite HP,program230_pair_transfer_path;reflexivity.
  -exact H6.
  -rewrite H1;unfold start,program230_pair_state;rewrite program230_copy2_register by lia;apply coding_add_zero.
  -rewrite(HO 7 ltac:(lia)ltac:(lia)ltac:(lia));unfold start,program230_pair_state;rewrite program230_copy2_register by lia;reflexivity.
  -intros i Hi Hi6 Hi1 Hi7;rewrite(HO i Hi Hi6 Hi1).
   unfold start,program230_pair_state;rewrite program230_copy2_register by exact Hi.
   now rewrite(proj2(Nat.eqb_neq i 6)Hi6),(proj2(Nat.eqb_neq i 1)Hi1),(proj2(Nat.eqb_neq i 7)Hi7). }
 exists u,v;split;[apply(proj2(p230_instruction_history_correct M u v(program230_transfer_time M k)start));exact HR|].
 now rewrite <-E.
Qed.
Lemma program230_pair_shape_positive_tail base k z:
 exists u v time,program230_history M p230_instruction_formula u v time
 (cfg base(program230_path_value M(P++[true]))(S k)Z z) /\
 program230_state_at M u v time(cfg base(program230_path_value M P)Z k(S z)) /\coding_lt M Z time.
Proof.
 destruct(program230_history_one M p230_instruction_formula _ _(program230_pair_shape_dec_positive M P Hshape base k z))as[u[v[HR HT]]].
 destruct(program230_history_extend M p230_instruction_formula u v(N 1)_ _ _ HR HT
 (program230_pair_shape_inc M P Hshape base k z))as[d[e[HD[HE _]]]].
 destruct(program230_pair_shape_transfer_tail base k(S z))as[f[g[HF HG]]].
 destruct(program230_history_join M p230_instruction_formula d e(N 2)f g(program230_transfer_time M k)_ _ HD HE HF)
 as[b[c[HB[HL HH]]]].
 pose proof(proj1(HH(program230_transfer_time M k)_(coding_lt_succ M(program230_transfer_time M k)))HG)as HC.
 destruct(program230_history_extend M p230_instruction_formula b c(addM M(N 2)(program230_transfer_time M k))_ _ _ HB HC
 (program230_pair_shape_continue M P Hshape base k(S z)))as[i[j[HI[HJ _]]]].
 exists i,j,(S(addM M(N 2)(program230_transfer_time M k)));split;[exact HI|].
 split;[exact HJ|apply coding_zero_lt_succ].
Qed.
End Parts.
Print Assumptions program230_pair_shape_copy_prefix.
Print Assumptions program230_pair_shape_transfer_tail.
Print Assumptions program230_pair_shape_positive_tail.
