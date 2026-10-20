(** The actual first unpair body and its unconditional public-program loop. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing Program230PairWalkFacts
 Program230PathCode Program230Configurations Program230Histories Program230HistoryJoin
 Program230InstructionFormula Program230Copy2States Program230TransferProgram
 Program230PairIteration Program230UnpairOuter Program230UnpairShape Program230UnpairShapeBranches.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Section ShapeBody.
Variable M:Model.
Variable P:list bool.
Variables(a p0 p1 p2 p3 p4 p5 p6:nat).
Hypotheses(Ha:(a<9)%nat)(Ha6:a<>6)(Ha7:a<>7)
 (HO:program230_unpair_occurrence P a p0 p1 p2 p3 p4 p5 p6).
Theorem program230_unpair_shape_walk base input x y:
 exists b c time x' y',
 program230_history M p230_instruction_formula b c time
 (program230_copy2_state a 6 7 base(program230_path_value M P)(succM M input)x y) /\
 program230_state_at M b c time
 (program230_copy2_state a 6 7 base(program230_path_value M P)input x' y') /\
 pair_walk M x y x' y'.
Proof.
 destruct(program230_pair_walk_total M x y)as[x'[y' HW]].
 destruct HW as[[Hx[Hx' Hy']]|[z[Hx[Hx' Hy']]]];subst x x' y'.
 -destruct(program230_unpair_shape_prefix M P a p0 p1 p2 p3 p4 p5 p6 Ha Ha6 Ha7 HO base input(zeroM M)y)as[u[v[HR HT]]].
  destruct(program230_unpair_shape_zero_tail M P a p0 p1 p2 p3 p4 p5 p6 Ha Ha6 Ha7 HO base input(succM M y))as[d[e[K[HD HE]]]].
  destruct(program230_history_join M p230_instruction_formula u v(code_numeral M 2)d e K _ _ HR HT HD)
   as[b[c[HB[HL HH]]]].
  exists b,c,(addM M(code_numeral M 2)K),(succM M y),(zeroM M);split;[exact HB|].
  split;[apply(proj1(HH K _ (coding_lt_succ M K)));exact HE|left;repeat split;reflexivity].
 -destruct(program230_unpair_shape_prefix M P a p0 p1 p2 p3 p4 p5 p6 Ha Ha6 Ha7 HO base input(succM M z)y)as[u[v[HR HT]]].
  destruct(program230_unpair_shape_positive_tail M P a p0 p1 p2 p3 p4 p5 p6 Ha Ha6 Ha7 HO base input z(succM M y))as[d[e[HD HE]]].
  destruct(program230_history_join M p230_instruction_formula u v(code_numeral M 2)d e(code_numeral M 3)
   _ _ HR HT HD)as[b[c[HB[HL HH]]]].
  exists b,c,(addM M(code_numeral M 2)(code_numeral M 3)),z,(succM M y);split;[exact HB|].
  split;[apply(proj1(HH(code_numeral M 3)_(coding_lt_succ M(code_numeral M 3))));exact HE|].
  right;exists z;repeat split;reflexivity.
Qed.
Theorem program230_unpair_shape_body:
 program230_unpair_body M P a.
Proof.
 intros base input x y index HP.
 destruct(program230_unpair_shape_walk base input x y)as[b[c[time[x'[y'[HR[HT HW]]]]]]].
 exists b,c,time,x',y';split;[apply p230_instruction_history_correct;exact HR|].
 split;[exact HT|exact(program230_pair_walk_successor M x y x' y' index HP HW)].
Qed.
Theorem program230_unpair_shape_history start count:
 program230_pc start=program230_path_value M P->program230_register start a=count->
 program230_register start 6=zeroM M->program230_register start 7=zeroM M->
 exists b c time final,program230_program_history M p230 b c time start /\
 program230_state_at M b c time final /\program230_pc final=program230_path_value M(inc_path P) /\
 program230_register final a=zeroM M /\
 pair_graph M(program230_register final 6)(program230_register final 7)count /\
 (forall i,(i<9)%nat->i<>a->i<>6->i<>7->program230_register final i=program230_register start i).
Proof.
 pose proof(program230_unpair_occurrence_leaves P a p0 p1 p2 p3 p4 p5 p6 HO)as[HD _].
 exact(program230_unpair_clean M P a start count Ha Ha6 Ha7 HD program230_unpair_shape_body).
Qed.
End ShapeBody.
Print Assumptions program230_unpair_shape_body.
Print Assumptions program230_unpair_shape_history.
