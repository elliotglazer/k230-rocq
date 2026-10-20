(** PA rank induction for pair162, with exact finite-cycle premises. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing
 Program230PathCode Program230Configurations Program230Histories Program230HistoryJoin
 Program230TransferStates Program230Copy2States Program230ThreeFieldFrame Program230TransferProgram
 Program230InstructionFormula Program230Edges Program230PairRank.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List Arith.Arith Lia setoid_ring.Ring.
Unset Implicit Arguments.
Definition program230_pair_state {D}(base:program230_configuration D)pc x y z:=program230_copy2_state 6 1 7 base pc x y z.
Definition program230_pair_cycle M P:=forall base x y z k,addM M x y = succM M k->
 exists u v N,program230_program_history M K230.Prog230.p230 u v N
 (program230_pair_state base(program230_path_value M P)x y z) /\
 program230_state_at M u v N(program230_pair_state base(program230_path_value M P)(zeroM M)k
  (addM M(addM M z y)(succM M(zeroM M)))) /\coding_lt M(zeroM M)N.
Definition program230_pair_exit M P exit:=forall base z,exists u v N,
 program230_program_history M K230.Prog230.p230 u v N(program230_pair_state base(program230_path_value M P)(zeroM M)(zeroM M)z) /\
 program230_state_at M u v N(program230_pair_state base(program230_path_value M exit)(zeroM M)(zeroM M)z) /\coding_lt M(zeroM M)N.
Definition program230_pair_property M P exit base rank:=forall x y z value,
 addM M x y = rank->pair_graph M x y value->exists u v N,
 program230_history M p230_instruction_formula u v N(program230_pair_state base(program230_path_value M P)x y z) /\
 program230_state_at M u v N(program230_pair_state base(program230_path_value M exit)(zeroM M)(zeroM M)(addM M z value)) /\
 coding_lt M(zeroM M)N.
Definition program230_pair_parameters:=program230_config_of(fun j =>$ (8+j)).
Definition program230_pair_property_formula P exit:form:=∀∀∀∀
 (($3⊕$2)==$4→pair_formula $3 $2 $0→∃∃∃
 (program230_history_formula p230_instruction_formula $2 $1 $0
 (program230_pair_state program230_pair_parameters(program230_path_term P)$6 $5 $4) ∧
 (program230_state_at_formula $2 $1 $0
 (program230_pair_state program230_pair_parameters(program230_path_term exit)zero zero($4⊕$3)) ∧Peano.sless zero $0))).
Lemma program230_pair_parameters_eval M base rank x y z value u v N:
 program230_eval_config M(N.:v.:u.:value.:z.:y.:x.:rank.:program230_field base)program230_pair_parameters = base.
Proof. apply program230_configuration_ext;intros j Hj;rewrite program230_eval_field by exact Hj.
 unfold program230_pair_parameters;rewrite program230_config_of_fields by exact Hj;reflexivity. Qed.
Local Opaque holds program230_history_formula program230_state_at_formula pair_formula program230_copy2_state.
Lemma program230_pair_property_definable M P exit base:Definable1 M(program230_pair_property M P exit base).
Proof.
 exists(program230_pair_property_formula P exit),(program230_field base);intro rank.
 unfold program230_pair_property_formula,program230_pair_property,program230_pair_state.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp. repeat setoid_rewrite holds_ex.
 repeat setoid_rewrite holds_and. setoid_rewrite program230_holds_equal.
 setoid_rewrite pair_formula_correct. setoid_rewrite program230_history_formula_correct.
 setoid_rewrite program230_state_at_formula_correct. setoid_rewrite less_formula_correct.
 setoid_rewrite program230_copy2_eval. setoid_rewrite program230_pair_parameters_eval.
 setoid_rewrite program230_path_term_correct;reflexivity.
Qed.
Section Induction.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Infix "+":=(addM M).
Add Ring pair_constructor_ring:(model_semiring M).
Lemma program230_duration_add N K:coding_lt M Z K->coding_lt M Z(N+K).
Proof. intros[d H];rewrite coding_add_zero in H;rewrite H.
 exists(N+d);rewrite coding_add_zero,(succ_as_add M d),(succ_as_add M(N+d));ring. Qed.
Theorem program230_pair_constructor_rank P exit:
 program230_pair_cycle M P->program230_pair_exit M P exit->
 forall base rank,program230_pair_property M P exit base rank.
Proof.
 intros HC HE base.
 apply(definable_induction M(program230_pair_property M P exit base)
 (program230_pair_property_definable M P exit base)).
 -intros x y z value Hsum HP.
  destruct(program230_pair_rank_zero M x y value Hsum HP)as[Hx[Hy Hv]];subst x y value.
  destruct(HE base z)as[u[v[N[HR[HT HN]]]]].
  apply(proj2(p230_instruction_history_correct M u v N _))in HR.
  exists u,v,N;split;[exact HR|]. split;[now rewrite coding_add_zero_r|exact HN].
 -intros rank IH x y z value Hsum HP.
  destruct(pair_total M Z rank)as[rest Hrest].
  pose proof(program230_pair_rank_step M x y rank value rest Hsum HP Hrest)as EV.
  destruct(HC base x y z rank Hsum)as[u[v[N[HR[HT HN]]]]].
  apply(proj2(p230_instruction_history_correct M u v N _))in HR.
  destruct(IH Z rank((z+y)+S Z)rest(coding_add_zero M rank)Hrest)
   as[d[e[K[HK[HU HKpos]]]]].
  destruct(program230_history_join M p230_instruction_formula u v N d e K
   (program230_pair_state base(program230_path_value M P)x y z)
   (program230_pair_state base(program230_path_value M P)Z rank((z+y)+S Z))HR HT HK)
   as[f[g[HG[HL HH]]]].
  exists f,g,(N+K);split;[exact HG|]. split;[|apply program230_duration_add;exact HKpos].
  assert(E:(z+y+S Z)+rest = z+value)by(rewrite EV,(succ_as_add M rest);ring).
  rewrite <-E;exact(proj1(HH K _ (coding_lt_succ M K))HU).
Qed.
End Induction.
Print Assumptions program230_pair_property_definable.
Print Assumptions program230_pair_constructor_rank.
