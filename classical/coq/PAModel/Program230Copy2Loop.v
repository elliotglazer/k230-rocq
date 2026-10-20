(** PA-definable two-target copying, including arbitrary nonstandard source counts. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230Configurations Program230Histories Program230HistoryJoin
 Program230HistoryConstructors Program230TransferStates Program230Copy2States.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv.
From Stdlib Require Import Lists.List Arith.Arith Lia setoid_ring.Ring.
Unset Implicit Arguments.
Definition program230_copy2_time M n:=addM M(mulM M(code_numeral M 4)n)(code_numeral M 1).
Definition program230_copy2_property M P a b c base n:=forall y z,exists u v,
 program230_history M(program230_copy2_formula P a b c)u v(program230_copy2_time M n)
 (program230_copy2_state a b c base(program230_path_value M P)n y z) /\
 program230_state_at M u v(program230_copy2_time M n)
 (program230_copy2_state a b c base(program230_path_value M(inc_path P))(zeroM M)(addM M y n)(addM M z n)).
Definition program230_copy2_parameters:=program230_config_of(fun j =>$ (5+j)).
Definition program230_copy2_property_formula P a b c:form:=∀∀∃∃
 (program230_history_formula(program230_copy2_formula P a b c)$1 $0(num 4⊗$4⊕num 1)
  (program230_copy2_state a b c program230_copy2_parameters(program230_path_term P)$4 $3 $2) ∧
 program230_state_at_formula $1 $0(num 4⊗$4⊕num 1)
  (program230_copy2_state a b c program230_copy2_parameters(program230_path_term(inc_path P))zero($3⊕$4)($2⊕$4))).
Lemma program230_copy2_parameters_eval M base n y z u v:
 program230_eval_config M(v.:u.:z.:y.:n.:program230_field base)program230_copy2_parameters = base.
Proof. apply program230_configuration_ext;intros j Hj.
 rewrite program230_eval_field by exact Hj. unfold program230_copy2_parameters.
 rewrite program230_config_of_fields by exact Hj;reflexivity. Qed.
Local Opaque holds program230_history_formula program230_state_at_formula program230_copy2_state.
Lemma program230_copy2_property_definable M P a b c base:
 Definable1 M(program230_copy2_property M P a b c base).
Proof.
 exists(program230_copy2_property_formula P a b c),(program230_field base);intro n.
 unfold program230_copy2_property_formula,program230_copy2_property.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
 setoid_rewrite program230_history_formula_correct. setoid_rewrite program230_state_at_formula_correct.
 setoid_rewrite program230_copy2_eval. setoid_rewrite program230_copy2_parameters_eval.
 setoid_rewrite program230_path_term_correct. unfold program230_copy2_time;reflexivity.
Qed.
Section Copying.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring copy2_ring:(model_semiring M).
Variables(P:list bool)(a b c:nat).
Hypotheses(Ha:(a<9)%nat)(Hb:(b<9)%nat)(Hc:(c<9)%nat)(Hab:a<>b)(Hac:a<>c)(Hbc:b<>c).
Local Notation cfg:=(program230_copy2_state a b c).
Theorem program230_copy2_uniform base n:program230_copy2_property M P a b c base n.
Proof.
 apply(definable_induction M(program230_copy2_property M P a b c base)
  (program230_copy2_property_definable M P a b c base)).
 -intros y z. destruct(program230_history_one M(program230_copy2_formula P a b c)_ _
  (program230_copy2_exit M P a b c Ha base y z))as[u[v[HR HT]]].
  exists u,v. unfold program230_copy2_time.
  replace(N 4*Z+N 1)with(N 1)by ring.
  rewrite !coding_add_zero_r;exact(conj HR HT).
 -intros k IH y z.
  destruct(program230_copy2_four M P a b c Ha Hb Hc Hab Hac Hbc base k y z)as[u[v[H4 HT4]]].
  destruct(IH(S y)(S z))as[d[e[HI HTI]]].
  destruct(program230_history_join M(program230_copy2_formula P a b c)
   u v(N 4)d e(program230_copy2_time M k)
   (cfg base(program230_path_value M P)(S k)y z)
   (cfg base(program230_path_value M P)k(S y)(S z))H4 HT4 HI)as[f[g[HR[HL HT]]]].
  assert(ET:N 4+program230_copy2_time M k = program230_copy2_time M(S k)).
  {unfold program230_copy2_time;rewrite(succ_as_add M k);ring. }
  assert(EY:S y+k = y+S k)by(rewrite(succ_as_add M y),(succ_as_add M k);ring).
  assert(EZ:S z+k = z+S k)by(rewrite(succ_as_add M z),(succ_as_add M k);ring).
  exists f,g;split;[now rewrite <-ET|]. rewrite <-ET,<-EY,<-EZ.
  exact(proj1(HT(program230_copy2_time M k)
   (cfg base(program230_path_value M(inc_path P))Z(S y+k)(S z+k))
   (coding_lt_succ M(program230_copy2_time M k)))HTI).
Qed.
Theorem program230_copy2_loop start count:
 program230_pc start = program230_path_value M P->program230_register start a = count->
 exists u v final,program230_history M(program230_copy2_formula P a b c)u v(program230_copy2_time M count)start /\
 program230_state_at M u v(program230_copy2_time M count)final /\
 program230_pc final = program230_path_value M(inc_path P) /\
 program230_register final a = Z /\
 program230_register final b = program230_register start b+count /\
 program230_register final c = program230_register start c+count /\
 (forall i,(i<9)%nat->i<>a->i<>b->i<>c->program230_register final i = program230_register start i).
Proof.
 intros HP HA. destruct(program230_copy2_uniform start count(program230_register start b)(program230_register start c))as[u[v[HR HT]]].
 rewrite(program230_copy2_restore a b c start(program230_path_value M P)count
 (program230_register start b)(program230_register start c)HP HA eq_refl eq_refl)in HR.
 exists u,v,(cfg start(program230_path_value M(inc_path P))Z(program230_register start b+count)(program230_register start c+count)).
 split;[exact HR|]. split;[exact HT|]. split;[reflexivity|].
 split;[rewrite program230_copy2_register by exact Ha;now rewrite Nat.eqb_refl|].
 split;[rewrite program230_copy2_register by exact Hb;now rewrite(proj2(Nat.eqb_neq b a)ltac:(congruence)),Nat.eqb_refl|].
 split;[rewrite program230_copy2_register by exact Hc;now rewrite(proj2(Nat.eqb_neq c a)ltac:(congruence)),(proj2(Nat.eqb_neq c b)ltac:(congruence)),Nat.eqb_refl|].
 intros i Hi Hia Hib Hic;rewrite program230_copy2_register by exact Hi.
 now rewrite(proj2(Nat.eqb_neq i a)Hia),(proj2(Nat.eqb_neq i b)Hib),(proj2(Nat.eqb_neq i c)Hic).
Qed.
End Copying.
Print Assumptions program230_copy2_property_definable.
Print Assumptions program230_copy2_uniform.
Print Assumptions program230_copy2_loop.
