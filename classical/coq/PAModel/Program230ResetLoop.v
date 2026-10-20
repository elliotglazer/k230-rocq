(** Actual internal reset-loop histories, with the source's Continue1 leaf. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230PathPop Program230Read Program230Walk Program230Edges Program230Transition
 Program230Configurations Program230Histories Program230HistoryJoin Program230HistoryConstructors
 Program230TransferCycle Program230TransferStates Program230TransferProgram.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_record_edge_formula Q e:=program230_edge_formula Q e
 (fun i =>$ (S i))(fun i =>$ (11+i))$10.
Lemma program230_record_edge_formula_correct M Q e s t:
 Program230Histories.program230_step M(program230_record_edge_formula Q e)s t<->
 program230_edge_step M Q e(program230_register s)(program230_register t)(program230_pc t).
Proof.
 unfold Program230Histories.program230_step,program230_record_edge_formula.
 rewrite program230_edge_formula_correct.
 change(program230_edge_step M Q e
 (fun i =>program230_transition_env(zeroM M)s t(S i))
 (fun i =>program230_transition_env(zeroM M)s t(11+i))(program230_pc t)<->
 program230_edge_step M Q e(program230_register s)(program230_register t)(program230_pc t)).
 apply program230_edge_step_ext;intros i Hi;
 [apply program230_transition_register_before|apply program230_transition_register_after];exact Hi.
Qed.
Definition program230_reset_formula P a:form:=
 ($0==program230_path_term P ∧program230_record_edge_formula(P++[false])(EDecnz a)) ∨
 ($0==program230_path_term(P++[true]) ∧program230_record_edge_formula(P++[true])(EContinue 1)).
Definition program230_reset_cycle M P a s t:=
 (program230_pc s = program230_path_value M P /\
 program230_edge_step M(P++[false])(EDecnz a)(program230_register s)(program230_register t)(program230_pc t)) \/
 (program230_pc s = program230_path_value M(P++[true]) /\
 program230_edge_step M(P++[true])(EContinue 1)(program230_register s)(program230_register t)(program230_pc t)).
Lemma program230_reset_formula_correct M P a s t:
 Program230Histories.program230_step M(program230_reset_formula P a)s t<->program230_reset_cycle M P a s t.
Proof.
 unfold program230_reset_formula,program230_reset_cycle,Program230Histories.program230_step.
 rewrite holds_or,!holds_and,!program230_holds_equal,!program230_path_term_correct.
 change(((program230_pc s = program230_path_value M P /\
 Program230Histories.program230_step M(program230_record_edge_formula(P++[false])(EDecnz a))s t) \/
 (program230_pc s = program230_path_value M(P++[true]) /\
 Program230Histories.program230_step M(program230_record_edge_formula(P++[true])(EContinue 1))s t))<->
 program230_reset_cycle M P a s t).
 now rewrite !program230_record_edge_formula_correct.
Qed.
Definition program230_reset_state {D} a base pc value:=@program230_transfer_state D a a base pc value value.
Definition program230_reset_time M n:=addM M(mulM M(code_numeral M 2)n)(code_numeral M 1).
Definition program230_reset_property M P a base n:=exists b c,
 program230_history M(program230_reset_formula P a)b c(program230_reset_time M n)
 (program230_reset_state a base(program230_path_value M P)n) /\
 program230_state_at M b c(program230_reset_time M n)
 (program230_reset_state a base(program230_path_value M(inc_path P))(zeroM M)).
Definition program230_reset_parameters:=program230_config_of(fun j =>$ (3+j)).
Definition program230_reset_property_formula P a:=∃∃
 (program230_history_formula(program230_reset_formula P a)$1 $0(num 2⊗$2⊕num 1)
 (program230_reset_state a program230_reset_parameters(program230_path_term P)$2) ∧
 program230_state_at_formula $1 $0(num 2⊗$2⊕num 1)
 (program230_reset_state a program230_reset_parameters(program230_path_term(inc_path P))zero)).
Lemma program230_reset_parameters_eval M base n b c:
 program230_eval_config M(c.:b.:n.:program230_field base)program230_reset_parameters = base.
Proof. apply program230_configuration_ext;intros j Hj.
 rewrite program230_eval_field by exact Hj. unfold program230_reset_parameters.
 rewrite program230_config_of_fields by exact Hj;reflexivity. Qed.
Local Opaque holds program230_history_formula program230_state_at_formula program230_transfer_state.
Lemma program230_reset_property_definable M P a base:Definable1 M(program230_reset_property M P a base).
Proof.
 exists(program230_reset_property_formula P a),(program230_field base);intro n.
 unfold program230_reset_property_formula,program230_reset_property,program230_reset_state.
 repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
 setoid_rewrite program230_history_formula_correct;setoid_rewrite program230_state_at_formula_correct.
 setoid_rewrite program230_transfer_eval;setoid_rewrite program230_reset_parameters_eval.
 setoid_rewrite program230_path_term_correct. unfold program230_reset_time;reflexivity.
Qed.
Section Reset.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring reset_loop_ring:(model_semiring M).
Variables(P:list bool)(a:nat).
Hypothesis Ha:(a<9)%nat.
Local Notation cfg:=(program230_reset_state a).
Lemma program230_reset_exit base:
 Program230Histories.program230_step M(program230_reset_formula P a)
 (cfg base(program230_path_value M P)Z)(cfg base(program230_path_value M(inc_path P))Z).
Proof.
 apply program230_reset_formula_correct;left;split;[reflexivity|].
 cbn[program230_edge_step];split;[exact Ha|]. left;split.
 -apply program230_transfer_source;exact Ha.
 -split;[rewrite brk_car1;reflexivity|]. intros i Hi.
  unfold program230_reset_state;rewrite !program230_transfer_register by exact Hi;reflexivity.
Qed.
Lemma program230_reset_decrement base n:
 Program230Histories.program230_step M(program230_reset_formula P a)
 (cfg base(program230_path_value M P)(S n))(cfg base(program230_path_value M(P++[true]))n).
Proof.
 apply program230_reset_formula_correct;left;split;[reflexivity|].
 cbn[program230_edge_step];split;[exact Ha|]. right;exists n;split.
 -apply program230_transfer_source;exact Ha.
 -split;[rewrite inc_path_app_false;reflexivity|]. intros i Hi.
  unfold program230_reset_state;rewrite !program230_transfer_register by exact Hi.
  destruct(Nat.eqb i a);reflexivity.
Qed.
Lemma program230_reset_continue base n:
 Program230Histories.program230_step M(program230_reset_formula P a)
 (cfg base(program230_path_value M(P++[true]))n)(cfg base(program230_path_value M P)n).
Proof.
 apply program230_reset_formula_correct;right;split;[reflexivity|].
 cbn[program230_edge_step];split;[rewrite cont_cdr1;reflexivity|]. intros i Hi.
 unfold program230_reset_state;rewrite !program230_transfer_register by exact Hi;reflexivity.
Qed.
Theorem program230_reset_uniform base n:program230_reset_property M P a base n.
Proof.
 apply(definable_induction M(program230_reset_property M P a base)
 (program230_reset_property_definable M P a base)).
 -destruct(program230_history_one M(program230_reset_formula P a)_ _(program230_reset_exit base))as[b[c[HR HT]]].
  exists b,c. unfold program230_reset_time. replace(N 2*Z+N 1)with(N 1)by ring. exact(conj HR HT).
 -intros k[b[c[HR HT]]].
  destruct(program230_history_one M(program230_reset_formula P a)_ _(program230_reset_decrement base k))as[d[e[HD HU]]].
  destruct(program230_history_extend M(program230_reset_formula P a)d e(N 1)_ _ _ HD HU
   (program230_reset_continue base k))as[f[g[HF[HV _]]]].
  destruct(program230_history_join M(program230_reset_formula P a)f g(N 2)b c(program230_reset_time M k)
   (cfg base(program230_path_value M P)(S k))(cfg base(program230_path_value M P)k)HF HV HR)
   as[u[v[Hrun[HL Hright]]]].
  assert(E:N 2+program230_reset_time M k = program230_reset_time M(S k)).
  {unfold program230_reset_time;rewrite(succ_as_add M k);ring. }
  exists u,v;split;[now rewrite <-E|]. rewrite <-E.
  apply(Hright(program230_reset_time M k)(cfg base(program230_path_value M(inc_path P))Z)
   (coding_lt_succ M(program230_reset_time M k)));exact HT.
Qed.
End Reset.
Definition program230_reset_occurrence p P a n:=
 fol p(ENode(root p))P = Some(ENode n) /\nodes p n = (EDecnz a,EContinue 1).
Lemma program230_reset_in_program M p P a n s t:
 program230_reset_occurrence p P a n->program230_reset_cycle M P a s t->
 Program230Transition.program230_step M p(program230_pc s)(program230_register s)(program230_register t)(program230_pc t).
Proof.
 intros[HP HN][[Hs HE]|[Hs HE]].
 -exists(EDecnz a),(P++[false]),(succM M(zeroM M));split;[|exact HE].
  split;[rewrite Hs;apply program230_read_path_zero|]. split;[|reflexivity].
  rewrite fol_app,HP. cbn[fol child]. now rewrite HN.
 -exists(EContinue 1),(P++[true]),(succM M(zeroM M));split;[|exact HE].
  split;[rewrite Hs;apply program230_read_exact_path|]. split;[|reflexivity].
  rewrite fol_app,HP. cbn[fol child]. now rewrite HN.
Qed.
Theorem program230_reset_program_history M p P a n start count:
 (a<9)%nat->program230_reset_occurrence p P a n->
 program230_pc start = program230_path_value M P->program230_register start a = count->
 exists b c final,program230_program_history M p b c(program230_reset_time M count)start /\
 program230_state_at M b c(program230_reset_time M count)final /\
 program230_pc final = program230_path_value M(inc_path P) /\program230_register final a = zeroM M /\
 (forall i,(i<9)%nat->i<>a->program230_register final i = program230_register start i).
Proof.
 intros Ha HO HP HA. destruct(program230_reset_uniform M P a Ha start count)as[b[c[HR HT]]].
 unfold program230_reset_state in HR,HT.
 rewrite(program230_transfer_state_restore a a start(program230_path_value M P)count count HP HA HA)in HR.
 exists b,c,(program230_reset_state a start(program230_path_value M(inc_path P))(zeroM M)).
 split.
 -destruct HR as[H0 HS];split;[exact H0|]. intros i s t Hi Hs Ht.
  apply(program230_reset_in_program M p P a n s t HO). apply program230_reset_formula_correct.
  exact(HS i s t Hi Hs Ht).
 -split;[exact HT|]. split;[reflexivity|]. split;[apply program230_transfer_source;exact Ha|].
  intros i Hi Hia. unfold program230_reset_state;rewrite program230_transfer_register by exact Hi.
  now rewrite(proj2(Nat.eqb_neq i a)Hia).
Qed.
Print Assumptions program230_reset_uniform.
Print Assumptions program230_reset_program_history.
