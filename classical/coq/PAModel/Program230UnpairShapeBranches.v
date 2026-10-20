(** Concrete positive and zero branches of the actual node-12 unpair body. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230Configurations Program230Histories Program230HistoryJoin Program230HistoryConstructors
 Program230TransferStates Program230TransferLoop Program230TransferProgram Program230Copy2States
 Program230ThreeFieldFrame Program230InstructionFormula Program230UnpairOuter Program230UnpairControl Program230UnpairShape Program230UnpairShapeControl Program230UnpairShapeReturn.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Section ShapeBranches.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Variable P:list bool.
Variables(a p0 p1 p2 p3 p4 p5 p6:nat).
Hypotheses(Ha:(a<9)%nat)(Ha6:a<>6)(Ha7:a<>7)
 (HO:program230_unpair_occurrence P a p0 p1 p2 p3 p4 p5 p6).
Local Definition dinput:=program230_unpair_shape_dec_input M P a p0 p1 p2 p3 p4 p5 p6 Ha Ha6 Ha7 HO.
Local Definition iright:=program230_unpair_shape_inc_right M P a p0 p1 p2 p3 p4 p5 p6 Ha Ha6 Ha7 HO.
Local Definition dleftp:=program230_unpair_shape_dec_left_positive M P a p0 p1 p2 p3 p4 p5 p6 Ha Ha6 Ha7 HO.
Local Definition dleftz:=program230_unpair_shape_dec_left_zero M P a p0 p1 p2 p3 p4 p5 p6 Ha Ha6 Ha7 HO.
Local Definition posbreak:=program230_unpair_shape_positive_break M P a p0 p1 p2 p3 p4 p5 p6 HO.
Local Definition ret:=program230_unpair_shape_continue M P a p0 p1 p2 p3 p4 p5 p6 HO.
Local Definition retz:=program230_unpair_shape_transfer_return M P a p0 p1 p2 p3 p4 p5 p6 HO.
Local Notation cfg:=(program230_copy2_state a 6 7).
Lemma program230_unpair_shape_zero_transfer base n y:
 exists u v,
 program230_history M p230_instruction_formula u v(program230_transfer_time M y)
 (cfg base(program230_path_value M(P++[true;true;false;true]))n Z y) /\
 program230_state_at M u v(program230_transfer_time M y)
 (cfg base(program230_path_value M(P++[true;true;true;false]))n y Z).
Proof.
 set(start:=cfg base(program230_path_value M(P++[true;true;false;true]))n Z y).
 assert(Hy:program230_register start 7=y).
 {unfold start;rewrite program230_copy2_register by lia;
   rewrite ?Nat.eqb_refl;try rewrite(proj2(Nat.eqb_neq 7 a)ltac:(congruence));reflexivity. }
 destruct(program230_transfer_program_history M p230(P++[true;true;false;true])7 6 p5 p6 start y
 ltac:(lia)ltac:(lia)ltac:(lia)(program230_unpair_shape_transfer_occurrence P a p0 p1 p2 p3 p4 p5 p6 HO)eq_refl Hy)
 as[u[v[final[HR[HT[HP[H7[H6 Hother]]]]]]]].
 assert(E:final=cfg base(program230_path_value M(P++[true;true;true;false]))n y Z).
 {apply program230_three_field_frame.
  -rewrite HP;f_equal;apply program230_unpair_transfer_path.
  -rewrite(Hother a Ha Ha7 Ha6);unfold start;rewrite program230_copy2_register by exact Ha;now rewrite Nat.eqb_refl.
  -rewrite H6;unfold start;rewrite program230_copy2_register by lia;
   rewrite(proj2(Nat.eqb_neq 6 a)ltac:(congruence));apply coding_add_zero.
  -exact H7.
  -intros i Hi Hia Hi6 Hi7. rewrite(Hother i Hi Hi7 Hi6);unfold start;rewrite program230_copy2_register by exact Hi.
   now rewrite(proj2(Nat.eqb_neq i a)Hia),(proj2(Nat.eqb_neq i 6)Hi6),(proj2(Nat.eqb_neq i 7)Hi7).
 }
 exists u,v;split;[apply(proj2(p230_instruction_history_correct M u v(program230_transfer_time M y)start));exact HR|].
 now rewrite <-E.
Qed.
Lemma program230_unpair_shape_prefix base n x y:
 exists u v,program230_history M p230_instruction_formula u v(N 2)
 (cfg base(program230_path_value M P)(S n)x y) /\
 program230_state_at M u v(N 2)(cfg base(program230_path_value M(P++[true;true]))n x(S y)).
Proof.
 destruct(program230_history_one M p230_instruction_formula _ _(dinput base n x y))
 as[u[v[HR HT]]].
 destruct(program230_history_extend M p230_instruction_formula u v(N 1)_ _ _ HR HT
 (iright base n x y))as[d[e[HD[HE _]]]].
 exists d,e;exact(conj HD HE).
Qed.
Lemma program230_unpair_shape_positive_tail base n x y:
 exists u v,program230_history M p230_instruction_formula u v(N 3)
 (cfg base(program230_path_value M(P++[true;true]))n(S x)y) /\
 program230_state_at M u v(N 3)(cfg base(program230_path_value M P)n x y).
Proof.
 destruct(program230_history_one M p230_instruction_formula _ _(dleftp base n x y))
 as[u[v[HR HT]]].
 destruct(program230_history_extend M p230_instruction_formula u v(N 1)_ _ _ HR HT
 (posbreak base n x y))as[d[e[HD[HE _]]]].
 destruct(program230_history_extend M p230_instruction_formula d e(N 2)_ _ _ HD HE
 (ret base n x y))as[f[g[HF[HG _]]]].
 exists f,g;exact(conj HF HG).
Qed.
Lemma program230_unpair_shape_zero_tail base n y:
 exists u v time,program230_history M p230_instruction_formula u v time
 (cfg base(program230_path_value M(P++[true;true]))n Z y) /\
 program230_state_at M u v time(cfg base(program230_path_value M P)n y Z).
Proof.
 destruct(program230_history_one M p230_instruction_formula _ _(dleftz base n y))
 as[u[v[HR HT]]].
 destruct(program230_unpair_shape_zero_transfer base n y)as[d[e[HD HE]]].
 destruct(program230_history_join M p230_instruction_formula u v(N 1)d e(program230_transfer_time M y)
 _ _ HR HT HD)as[f[g[HF[HL HH]]]].
 pose proof(proj1(HH(program230_transfer_time M y)_(coding_lt_succ M(program230_transfer_time M y)))HE)as HG.
 destruct(program230_history_extend M p230_instruction_formula f g(addM M(N 1)(program230_transfer_time M y))_ _ _ HF HG
 (retz base n y Z))as[b[c[HB[HC _]]]].
 exists b,c,(S(addM M(N 1)(program230_transfer_time M y)));exact(conj HB HC).
Qed.
End ShapeBranches.
Print Assumptions program230_unpair_shape_zero_transfer.
Print Assumptions program230_unpair_shape_positive_tail.
Print Assumptions program230_unpair_shape_zero_tail.
