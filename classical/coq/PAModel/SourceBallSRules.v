(** Arithmetic syntax of the literal ballS step. Its table rows carry the
    count, carrier index, matrix code and output code. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes CodeTuples NumericalTraces SentenceBounds NumericalSubstitutionMaps.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition balls_record M n y body out r :=tuple7_graph M n y body out(zeroM M)(zeroM M)(zeroM M)r.
Definition balls_record_formula(n y body out r:term):form:=tuple7_formula n y body out zero zero zero r.
Theorem balls_record_formula_correct M rho n y body out r:
  holds M rho(balls_record_formula n y body out r)<->
  balls_record M(evalM M rho n)(evalM M rho y)(evalM M rho body)(evalM M rho out)(evalM M rho r).
Proof. apply tuple7_formula_correct. Qed.
Theorem balls_record_total M n y body out:exists r,balls_record M n y body out r.
Proof. apply tuple7_total. Qed.
Theorem balls_record_injective M n y body out n' y' body' out' r:
  balls_record M n y body out r ->balls_record M n' y' body' out' r ->
  n=n'/\y=y'/\body=body'/\out=out'.
Proof.
  intros H H'. destruct(tuple7_injective M n y body out _ _ _ n' y' body' out' _ _ _ r H H')
    as(Hn&Hy&Hbody&Hout&_). auto.
Qed.

Definition balls_step M y previous out:=exists atom point,
  sf_relation M SFMember(zeroM M)(succM M y)atom /\
  sf_relation M SFImpl atom previous point /\sf_relation M SFAll point(zeroM M)out.
Definition balls_step_formula(y previous out:term):form:=∃∃(
  sf_formula SFMember zero(σ(code_lift2 y))$1 ∧
  sf_formula SFImpl $1(code_lift2 previous)$0 ∧sf_formula SFAll $0 zero(code_lift2 out)).
Local Opaque sf_formula.
Theorem balls_step_formula_correct M rho y previous out:
  holds M rho(balls_step_formula y previous out)<->
  balls_step M(evalM M rho y)(evalM M rho previous)(evalM M rho out).
Proof.
  unfold balls_step_formula,balls_step. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite sf_formula_correct.
  setoid_rewrite substitution_map_eval_succ. repeat setoid_rewrite code_eval_lift2.
  change((exists a p,(sf_relation M SFMember(zeroM M)(succM M(evalM M rho y))a /\
    sf_relation M SFImpl a(evalM M rho previous)p) /\sf_relation M SFAll p(zeroM M)(evalM M rho out))<->
    exists a p,sf_relation M SFMember(zeroM M)(succM M(evalM M rho y))a /\
    sf_relation M SFImpl a(evalM M rho previous)p /\sf_relation M SFAll p(zeroM M)(evalM M rho out)).
  split;intros(a&p&H);exists a,p;tauto.
Qed.
Theorem balls_step_total M y previous:exists out,balls_step M y previous out.
Proof.
  destruct(sf_relation_total M SFMember(zeroM M)(succM M y))as(a&HA).
  destruct(sf_relation_total M SFImpl a previous)as(p&HP).
  destruct(sf_relation_total M SFAll p(zeroM M))as(out&HO).
  exists out,a,p. auto.
Qed.
Theorem balls_step_functional M y previous out out':
  balls_step M y previous out ->balls_step M y previous out' ->out=out'.
Proof.
  intros(a&p&HA&HP&HO)(a'&p'&HA'&HP'&HO').
  pose proof(sf_relation_functional M SFMember(zeroM M)(succM M y)a a' HA HA')as E. subst a'.
  pose proof(sf_relation_functional M SFImpl a previous p p' HP HP')as E. subst p'.
  exact(sf_relation_functional M SFAll p(zeroM M)out out' HO HO').
Qed.

Definition balls_base M r:=exists y body,balls_record M(zeroM M)y body body r.
Definition balls_base_formula:form:=∃∃balls_record_formula zero $1 $0 $0 $2.
Local Opaque balls_record_formula balls_step_formula.
Theorem balls_base_formula_correct M rho r:
  holds M(r .:rho)balls_base_formula<->balls_base M r.
Proof.
  unfold balls_base_formula,balls_base. repeat setoid_rewrite holds_ex.
  setoid_rewrite balls_record_formula_correct. reflexivity.
Qed.
Definition balls_unary M r p:=exists n y body out previous,
  balls_record M(succM M n)y body out r /\
  balls_record M n(succM M y)body previous p /\balls_step M y previous out.
Definition balls_unary_formula:form:=∃∃∃∃∃(
  balls_record_formula(σ $4)$3 $2 $1 $5 ∧
  balls_record_formula $4(σ $3)$2 $0 $6 ∧balls_step_formula $3 $0 $1).
Theorem balls_unary_formula_correct M rho r p:
  holds M(r .:p .:rho)balls_unary_formula<->balls_unary M r p.
Proof.
  unfold balls_unary_formula,balls_unary. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite balls_record_formula_correct.
  setoid_rewrite balls_step_formula_correct. setoid_rewrite substitution_map_eval_succ.
  split;intros(n&y&body&out&previous&H);exists n,y,body,out,previous;tauto.
Qed.
Lemma balls_base_bound:bounded 1 balls_base_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Lemma balls_unary_bound:bounded 2 balls_unary_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Lemma balls_binary_bound:bounded 3(⊥:form).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Definition source_balls_rules:NumericalRules:={|
  rule_base_formula:=balls_base_formula;rule_base_bound:=balls_base_bound;
  rule_unary_formula:=balls_unary_formula;rule_unary_bound:=balls_unary_bound;
  rule_binary_formula:=⊥;rule_binary_bound:=balls_binary_bound|}.
Theorem balls_rule_base M r:trace_base M source_balls_rules r<->balls_base M r.
Proof. apply balls_base_formula_correct. Qed.
Theorem balls_rule_unary M r p:trace_unary M source_balls_rules r p<->balls_unary M r p.
Proof. apply balls_unary_formula_correct. Qed.
Print Assumptions balls_step_formula_correct.
Print Assumptions balls_unary_formula_correct.





