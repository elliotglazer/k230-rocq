(** Uniform multiplier-four loop: the PA model itself supplies every internal iteration. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230Edges Program230Configurations Program230Histories
 Program230HistoryJoin Program230HistoryConstructors Program230TransferCycle Program230TransferStates Program230Scale4States.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv.
From Stdlib Require Import Lists.List Arith.Arith Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_scale4_time M n:=addM M(mulM M(code_numeral M 6)n)(code_numeral M 1).
Definition program230_scale4_property M P a b base n:=forall y,exists u v,
 program230_history M(program230_scale4_formula P a b)u v(program230_scale4_time M n)
 (program230_transfer_state a b base(program230_path_value M P)n y) /\
 program230_state_at M u v(program230_scale4_time M n)
 (program230_transfer_state a b base(program230_path_value M(inc_path P))(zeroM M)(addM M y(mulM M(code_numeral M 4)n))).
Definition program230_transfer_parameters:program230_configuration term:=program230_config_of(fun j=>$ (4+j)).
Definition program230_scale4_property_formula P a b:form:=∀∃∃
 (program230_history_formula(program230_scale4_formula P a b)$1 $0(num 6⊗$3⊕num 1)
  (program230_transfer_state a b program230_transfer_parameters(program230_path_term P)$3 $2) ∧
  program230_state_at_formula $1 $0(num 6⊗$3⊕num 1)
  (program230_transfer_state a b program230_transfer_parameters(program230_path_term(inc_path P))zero($2⊕(num 4⊗$3)))).
Lemma program230_transfer_parameters_eval M base n y u v:
 program230_eval_config M(v.:u.:y.:n.:program230_field base)program230_transfer_parameters = base.
Proof. apply program230_configuration_ext;intros j Hj.
 rewrite program230_eval_field by exact Hj. unfold program230_transfer_parameters.
 rewrite program230_config_of_fields by exact Hj. reflexivity. Qed.
Local Opaque holds program230_history_formula program230_state_at_formula program230_transfer_state.
Lemma program230_scale4_property_definable M P a b base:
 Definable1 M(program230_scale4_property M P a b base).
Proof.
 exists(program230_scale4_property_formula P a b),(program230_field base). intro n.
 unfold program230_scale4_property_formula,program230_scale4_property.
 rewrite holds_all. repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
 setoid_rewrite program230_history_formula_correct.
 setoid_rewrite program230_state_at_formula_correct.
 setoid_rewrite program230_transfer_eval.
 setoid_rewrite program230_transfer_parameters_eval.
 setoid_rewrite program230_path_term_correct.

 unfold program230_scale4_time.
 reflexivity.
Qed.
Section Loop.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring transfer_loop_ring:(model_semiring M).
Variables(P:list bool)(a b:nat).
Hypotheses(Ha:(a<9)%nat)(Hb:(b<9)%nat)(Hab:a<>b).
Local Notation cfg := (program230_transfer_state a b).
Theorem program230_scale4_loop_uniform base n:program230_scale4_property M P a b base n.
Proof.
 apply(definable_induction M(program230_scale4_property M P a b base)
 (program230_scale4_property_definable M P a b base)).
 -intro y. destruct(program230_history_one M(program230_scale4_formula P a b)_ _
  (program230_scale4_exit M P a b Ha base y))as[u[v[HR HT]]].
  exists u,v. unfold program230_scale4_time.
  replace(N 6*Z+N 1)with(N 1)by ring.
  replace(N 4*Z)with Z by ring. rewrite coding_add_zero_r. exact(conj HR HT).
 -intros k IH y.
  destruct(program230_scale4_six M P a b Ha Hb Hab base k y)as[u[v[H3 HT3]]].
  destruct(IH(S(S(S(S y)))))as[d[e[HI HTI]]].
  destruct(program230_history_join M(program230_scale4_formula P a b)
   u v(N 6)d e(program230_scale4_time M k)
   (cfg base(program230_path_value M P)(S k)y)
   (cfg base(program230_path_value M P)k(S(S(S(S y)))))H3 HT3 HI)
   as[f[g[HR[HL HT]]]].
  assert(ET:N 6+program230_scale4_time M k = program230_scale4_time M(S k)).
  {unfold program230_scale4_time. rewrite(succ_as_add M k). ring. }
  assert(EV:S(S(S(S y)))+N 4*k = y+N 4*S k).
  {cbn[code_numeral]. repeat multimatch goal with
   | |- context[succM M ?x]=>lazymatch x with zeroM _=>fail 0|_=>rewrite(succ_as_add M x)end
   end;ring. }

  exists f,g. split;[now rewrite <-ET|].
  rewrite <-ET,<-EV. apply(HT(program230_scale4_time M k)
    (cfg base(program230_path_value M(inc_path P))Z(S(S(S(S y)))+N 4*k))
    (coding_lt_succ M(program230_scale4_time M k))). exact HTI.
Qed.
Theorem program230_scale4_loop Mstart n:
 program230_pc Mstart = program230_path_value M P ->program230_register Mstart a = n ->
 exists u v final,program230_history M(program230_scale4_formula P a b)u v(program230_scale4_time M n)Mstart /\
 program230_state_at M u v(program230_scale4_time M n)final /\
 program230_pc final = program230_path_value M(inc_path P) /\
 program230_register final a = Z /\
 program230_register final b = program230_register Mstart b+N 4*n /\
 (forall i,(i<9)%nat->i<>a->i<>b->program230_register final i = program230_register Mstart i).
Proof.
 intros HP HA. destruct(program230_scale4_loop_uniform Mstart n(program230_register Mstart b))
 as[u[v[HR HT]]].
 rewrite(program230_transfer_state_restore a b Mstart(program230_path_value M P)n
  (program230_register Mstart b)HP HA eq_refl)in HR.
 exists u,v,(cfg Mstart(program230_path_value M(inc_path P))Z(program230_register Mstart b+N 4*n)).
 split;[exact HR|]. split;[exact HT|]. split;[reflexivity|].
 split;[apply program230_transfer_source;exact Ha|].
 split;[apply program230_transfer_target;assumption|].
 intros i Hi Hia Hib. rewrite program230_transfer_register by exact Hi.
 rewrite(proj2(Nat.eqb_neq i a)Hia),(proj2(Nat.eqb_neq i b)Hib). reflexivity.
Qed.
End Loop.
Print Assumptions program230_scale4_property_definable.
Print Assumptions program230_scale4_loop_uniform.
Print Assumptions program230_scale4_loop.
