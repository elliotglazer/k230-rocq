(** The actual first pair162 body, including finite-PC padding at entry. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing
 Program230PathCode Program230Configurations Program230Histories Program230HistoryConstructors Program230HistoryJoin
 Program230TransferStates Program230TransferProgram Program230Copy2States Program230Copy2Loop Program230InstructionFormula
 Program230RootHistory Program230PairConstructorIteration Program230PairShape Program230PairShapeParts.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Section Body.
Variable M:Model.
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Notation N := (code_numeral M).
Variable P:list bool.
Hypothesis Hshape:program230_pair_shape P.
Local Notation cfg := program230_pair_state.
Add Ring pair_body_ring:(model_semiring M).
Lemma program230_pair_shape_copy_positive y:program230_copy2_time M y <> Z.
Proof.
 unfold program230_copy2_time;change(addM M(mulM M(N 4)y)(S Z)<>Z).
 assert(E:addM M(mulM M(N 4)y)(S Z)=S(mulM M(N 4)y))
  by(symmetry;apply succ_as_add).
 rewrite E;exact(fun H=>zero_ne_succ M _ (eq_sym H)).
Qed.
Lemma program230_pair_shape_copy_entry base x y z:
 exists u v,program230_history M p230_instruction_formula u v(program230_copy2_time M y)
 (cfg base(program230_path_value M P)x y z) /\
 program230_state_at M u v(program230_copy2_time M y)
 (cfg base(program230_path_value M(P++[true]))(addM M x y)Z(addM M z y)).
Proof.
 destruct(program230_pair_shape_copy_prefix M P Hshape base x y z)as[u[v[HR HT]]].
 destruct(p230_history_ipeq_endpoint M u v(program230_copy2_time M y)
 (cfg base(program230_path_value M(P++[false]))x y z)(P++[false])P
 (cfg base(program230_path_value M(P++[true]))(addM M x y)Z(addM M z y))
 eq_refl(ipeq_app_false P)HR(program230_pair_shape_copy_positive y)HT)as[d[e[HD[HE _]]]].
 assert(E:program230_with_pc(cfg base(program230_path_value M(P++[false]))x y z)(program230_path_value M P)=
 cfg base(program230_path_value M P)x y z).
 {apply program230_configuration_ext;intros j Hj;destruct j as[|j];[reflexivity|].
  change(program230_register(program230_with_pc(cfg base(program230_path_value M(P++[false]))x y z)(program230_path_value M P))j=
   program230_register(cfg base(program230_path_value M P)x y z)j).
  rewrite program230_with_pc_register;unfold program230_pair_state;rewrite !program230_copy2_register by lia;reflexivity. }
 exists d,e;split;[now rewrite <-E|exact HE].
Qed.
Theorem program230_pair_shape_actual_cycle:program230_pair_cycle M P.
Proof.
 intros base x y z k Hsum.
 destruct(program230_pair_shape_copy_entry base x y z)as[u[v[HR HT]]].
 rewrite Hsum in HT.
 destruct(program230_pair_shape_positive_tail M P Hshape base k(addM M z y))as[d[e[K[HK[HU HKpos]]]]].
 destruct(program230_history_join M p230_instruction_formula u v(program230_copy2_time M y)d e K _ _ HR HT HK)
 as[f[g[HG[HL HH]]]].
 exists f,g,(addM M(program230_copy2_time M y)K);split.
 -apply p230_instruction_history_correct;exact HG.
 -split;[|apply program230_duration_add;exact HKpos].
  assert(E:S(addM M z y)=addM M(addM M z y)(S Z))by(apply succ_as_add).
  rewrite <-E;exact(proj1(HH K _ (coding_lt_succ M K))HU).
Qed.
Theorem program230_pair_shape_actual_exit:program230_pair_exit M P ((inc_path P)++[false]).
Proof.
 intros base z;destruct(program230_pair_shape_copy_entry base Z Z z)as[u[v[HR HT]]].
 rewrite coding_add_zero,coding_add_zero_r in HT.
 destruct(program230_history_extend M p230_instruction_formula u v(program230_copy2_time M Z)_ _ _ HR HT
 (program230_pair_shape_dec_zero M P Hshape base z))as[d[e[HD[HE _]]]].
 exists d,e,(S(program230_copy2_time M Z));split;[apply p230_instruction_history_correct;exact HD|].
 split;[exact HE|apply coding_zero_lt_succ].
Qed.
Theorem program230_pair_shape_history base x y z value:
 pair_graph M x y value->exists u v time,
 program230_program_history M p230 u v time(cfg base(program230_path_value M P)x y z) /\
 program230_state_at M u v time(cfg base(program230_path_value M ((inc_path P)++[false]))Z Z(addM M z value)) /\
 coding_lt M Z time.
Proof.
 intro HP;destruct(program230_pair_constructor_rank M P ((inc_path P)++[false])
 program230_pair_shape_actual_cycle program230_pair_shape_actual_exit base(addM M x y)x y z value eq_refl HP)
 as[u[v[time[HR HT]]]].
 exists u,v,time;split;[apply p230_instruction_history_correct;exact HR|exact HT].
Qed.
End Body.
Print Assumptions program230_pair_shape_actual_cycle.
Print Assumptions program230_pair_shape_actual_exit.
Print Assumptions program230_pair_shape_history.
