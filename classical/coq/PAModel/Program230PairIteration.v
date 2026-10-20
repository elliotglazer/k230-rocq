(** Uniform outer unpair iteration; its concrete body certificate remains explicit. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs Pairing
 Program230PathCode Program230Edges Program230Read Program230Walk Program230Transition Program230InstructionFormula
 Program230Configurations Program230Histories Program230HistoryConstructors Program230HistoryJoin
 Program230TransferProgram Program230TransferStates Program230Copy2States.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_unpair_body M P a:=forall base input x y index,
 pair_graph M x y index->exists u v N x' y',
 program230_program_history M p230 u v N
 (program230_copy2_state a 6 7 base(program230_path_value M P)(succM M input)x y) /\
 program230_state_at M u v N(program230_copy2_state a 6 7 base(program230_path_value M P)input x' y') /\
 pair_graph M x' y'(succM M index).
Definition program230_unpair_property M P a base input:=forall x y index,
 pair_graph M x y index->exists u v N x' y',
 program230_history M p230_instruction_formula u v N
 (program230_copy2_state a 6 7 base(program230_path_value M P)input x y) /\
 program230_state_at M u v N(program230_copy2_state a 6 7 base(program230_path_value M(inc_path P))(zeroM M)x' y') /\
 pair_graph M x' y'(addM M index input).
Definition program230_unpair_parameters:=program230_config_of(fun j =>$ (9+j)).
Definition program230_unpair_property_formula P a:form:=∀∀∀
 (pair_formula $2 $1 $0→∃∃∃∃∃
  (program230_history_formula p230_instruction_formula $4 $3 $2
   (program230_copy2_state a 6 7 program230_unpair_parameters(program230_path_term P)$8 $7 $6) ∧
  (program230_state_at_formula $4 $3 $2
   (program230_copy2_state a 6 7 program230_unpair_parameters(program230_path_term(inc_path P))zero $1 $0) ∧
   pair_formula $1 $0($5⊕$8)))).
Lemma program230_unpair_parameters_eval M base n x y index u v N x' y':
 program230_eval_config M(y'.:x'.:N.:v.:u.:index.:y.:x.:n.:program230_field base)program230_unpair_parameters = base.
Proof.
 apply program230_configuration_ext;intros j Hj. rewrite program230_eval_field by exact Hj.
 unfold program230_unpair_parameters;rewrite program230_config_of_fields by exact Hj;reflexivity.
Qed.
Local Opaque holds program230_history_formula program230_state_at_formula program230_copy2_state pair_formula.
Lemma program230_unpair_property_definable M P a base:
 Definable1 M(program230_unpair_property M P a base).
Proof.
 exists(program230_unpair_property_formula P a),(program230_field base);intro n.
 unfold program230_unpair_property_formula,program230_unpair_property.
 repeat setoid_rewrite holds_all. setoid_rewrite holds_imp. repeat setoid_rewrite holds_ex.
 repeat setoid_rewrite holds_and. setoid_rewrite pair_formula_correct.
 setoid_rewrite program230_history_formula_correct. setoid_rewrite program230_state_at_formula_correct.
 setoid_rewrite program230_copy2_eval. setoid_rewrite program230_unpair_parameters_eval.
 setoid_rewrite program230_path_term_correct;reflexivity.
Qed.
Lemma program230_unpair_exit M P a base x y:
 (a<9)%nat->fol p230(ENode(root p230))(P++[false]) = Some(EDecnz a)->
 Program230Histories.program230_step M p230_instruction_formula
 (program230_copy2_state a 6 7 base(program230_path_value M P)(zeroM M)x y)
 (program230_copy2_state a 6 7 base(program230_path_value M(inc_path P))(zeroM M)x y).
Proof.
 intros Ha HF;apply p230_instruction_formula_correct.
 exists(EDecnz a),(P++[false]),(succM M(zeroM M));split.
 -split;[apply program230_read_path_zero|split;[exact HF|reflexivity]].
 -cbn[program230_edge_step];split;[exact Ha|]. left;split.
  +rewrite program230_copy2_register by exact Ha;now rewrite Nat.eqb_refl.
  +split;[rewrite brk_car1;reflexivity|]. intros i Hi;rewrite !program230_copy2_register by exact Hi;reflexivity.
Qed.
Theorem program230_unpair_iteration M P a:
 (a<9)%nat->fol p230(ENode(root p230))(P++[false]) = Some(EDecnz a)->
 program230_unpair_body M P a->forall base input,program230_unpair_property M P a base input.
Proof.
 intros Ha HF HB base.
 apply(definable_induction M(program230_unpair_property M P a base)
 (program230_unpair_property_definable M P a base)).
 -intros x y index HP.
  destruct(program230_history_one M p230_instruction_formula _ _(program230_unpair_exit M P a base x y Ha HF))as[u[v[HR HT]]].
  exists u,v,(succM M(zeroM M)),x,y;split;[exact HR|]. split;[exact HT|].
  now rewrite coding_add_zero_r.
 -intros input IH x y index HP.
  destruct(HB base input x y index HP)as[u[v[N[x'[y'[HR[HT HP']]]]]]].
  apply(proj2(p230_instruction_history_correct M u v N _))in HR.
  destruct(IH x' y'(succM M index)HP')as[d[e[K[xx[yy[HK[HU HPP]]]]]]].
  destruct(program230_history_join M p230_instruction_formula u v N d e K
   (program230_copy2_state a 6 7 base(program230_path_value M P)(succM M input)x y)
   (program230_copy2_state a 6 7 base(program230_path_value M P)input x' y')HR HT HK)
   as[f[g[HG[HL HH]]]].
  exists f,g,(addM M N K),xx,yy;split;[exact HG|]. split.
  +apply(proj1(HH K _ (coding_lt_succ M K)));exact HU.
  +replace(addM M index(succM M input))with(addM M(succM M index)input).
   *exact HPP.
   *rewrite(Arithmetic.add_succ M index input),(Arithmetic.add_comm M index(succM M input)),(Arithmetic.add_succ M input index).
    now rewrite(Arithmetic.add_comm M input index).
Qed.
Print Assumptions program230_unpair_property_definable.
Print Assumptions program230_unpair_iteration.
