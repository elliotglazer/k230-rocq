(** The exact PA formula for a simulated endpoint of an internal program
    history. The endpoint, four tape fields and elapsed time are all internal. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230Configurations Program230Histories TM230BinaryStep TM230ExactPaths
 TM230PhysicalRegisters TM230SimulationState TM230SimulationFormula.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Arith.Arith Lia.
Unset Implicit Arguments.
Lemma machine230_simulation_registers_ext M pc R T s:
 (forall j,(j<9)%nat->R j=T j)->
 (machine230_simulation_state M pc R s<->machine230_simulation_state M pc T s).
Proof.
 intro HR. pose proof(machine230_physical_list_ext M R T HR)as E.
 unfold machine230_simulation_state;now rewrite E.
Qed.
Definition machine230_config_simulation_formula(p:program230_configuration term)(q l h r:term):=
 machine230_simulation_formula(program230_pc p)(program230_register p)q l h r.
Theorem machine230_config_simulation_formula_correct M rho p q l h r:
 holds M rho(machine230_config_simulation_formula p q l h r)<->
 machine230_simulation_state M(program230_pc(program230_eval_config M rho p))
  (program230_register(program230_eval_config M rho p))
  (machine230_mk_config(carrier M)(evalM M rho q)(evalM M rho l)(evalM M rho h)(evalM M rho r)).
Proof.
 unfold machine230_config_simulation_formula;rewrite machine230_simulation_formula_correct.
 assert(EPC:program230_pc(program230_eval_config M rho p)=evalM M rho(program230_pc p))by reflexivity.
 rewrite EPC;apply machine230_simulation_registers_ext;intros j Hj.
 unfold program230_register;symmetry;apply program230_eval_field;lia.
Qed.
Definition machine230_history_simulation_at M b c start idx:=
 exists p q time slack,program230_state_at M b c idx p /\
 machine230_reaches_in M time start q /\time=addM M idx slack /\
 machine230_simulation_state M(program230_pc p)(program230_register p)q.
Definition machine230_history_endpoint_terms:program230_configuration term:=
 program230_config_of(fun j=>$(15-j)).
Definition machine230_history_simulation_formula(b c idx q l h r:term):form:=
 ∃∃∃∃∃∃∃∃∃∃∃∃∃∃∃∃(program230_state_at_formula(program230_lift 16 b)(program230_lift 16 c)
  (program230_lift 16 idx)machine230_history_endpoint_terms ∧
 (machine230_reaches_in_formula $1(program230_lift 16 q)(program230_lift 16 l)
  (program230_lift 16 h)(program230_lift 16 r)$5 $4 $3 $2 ∧
 ($1==program230_lift 16 idx⊕$0 ∧
 machine230_config_simulation_formula machine230_history_endpoint_terms $5 $4 $3 $2))).
Lemma machine230_history_lift16_eval M rho p a0 a1 a2 a3 a4 a5 a6 a7 a8 q l h r time slack t:
 evalM M(slack.:time.:r.:h.:l.:q.:a8.:a7.:a6.:a5.:a4.:a3.:a2.:a1.:a0.:p.:rho)
  (program230_lift 16 t)=evalM M rho t.
Proof. unfold evalM;cbn[program230_lift];now rewrite !eval_up. Qed.
Local Opaque holds program230_state_at_formula machine230_reaches_in_formula machine230_config_simulation_formula.
Theorem machine230_history_simulation_formula_correct M rho b c idx q l h r:
 holds M rho(machine230_history_simulation_formula b c idx q l h r)<->
 machine230_history_simulation_at M(evalM M rho b)(evalM M rho c)
  (machine230_mk_config(carrier M)(evalM M rho q)(evalM M rho l)(evalM M rho h)(evalM M rho r))
  (evalM M rho idx).
Proof.
 unfold machine230_history_simulation_formula,machine230_history_simulation_at.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite program230_state_at_formula_correct.
 setoid_rewrite machine230_reaches_in_formula_correct.
 setoid_rewrite machine230_config_simulation_formula_correct.
 setoid_rewrite machine230_holds_equal. setoid_rewrite machine230_eval_add.
 repeat setoid_rewrite machine230_history_lift16_eval.
 cbn[machine230_history_endpoint_terms program230_eval_config program230_config_of program230_field evalM].
 split.
 -intros(p&a0&a1&a2&a3&a4&a5&a6&a7&a8&q'&l'&h'&r'&time&slack&HP&HT&HE&HS).
  exists(mkProgram230Configuration(carrier M)p a0 a1 a2 a3 a4 a5 a6 a7 a8),
   (machine230_mk_config(carrier M)q' l' h' r'),time,slack;auto.
 -intros([p a0 a1 a2 a3 a4 a5 a6 a7 a8]&[q' l' h' r']&time&slack&HP&HT&HE&HS).
  exists p,a0,a1,a2,a3,a4,a5,a6,a7,a8,q',l',h',r',time,slack;auto.
Qed.
Definition machine230_history_progress M b c N start idx:=
 coding_lt M idx(succM M N)->machine230_history_simulation_at M b c start idx.
Theorem machine230_history_progress_definable M b c N start:
 Definable1 M(machine230_history_progress M b c N start).
Proof.
 exists(Peano.sless $0(σ $3)→machine230_history_simulation_formula $1 $2 $0 $4 $5 $6 $7),
  (b.:c.:N.:machine230_state start.:machine230_left start.:machine230_head start.:machine230_right start.:(fun _=>zeroM M)).
 intro idx. unfold machine230_history_progress. rewrite holds_imp,less_formula_correct,
  machine230_history_simulation_formula_correct. destruct start;reflexivity.
Qed.
Print Assumptions machine230_config_simulation_formula_correct.
Print Assumptions machine230_history_simulation_formula_correct.
Print Assumptions machine230_history_progress_definable.
