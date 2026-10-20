(** Actual least-Cond existence, uniformly over internally finite piece
    tables. The varying Cond code is supplied to the proved internal
    least-ordinal construction, and ex_cond is generated internally. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes SourceBounded
  SourceOrdinalPredicate SourceLFixed SourceHierarchySyntax SourcePieceConjunctionBounds
  SourceReflectionCondition SourceReflectionConditionBounds SourceReflectionExistenceGoal SourceReflectionExistence
  SourceLeastOrdinalGoal SourceLeastOrdinalCalibration SourceLeastOrdinalZFR
  SourceDescriptorClosure SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Local Opaque code_numeral source_L_domain source_ordinal_predicate source_ordinal_predicate_code source_L_domain_code
  source_reflection_condition source_least_ordinal_graph.

Definition source_reflection_least_graph M level sb sc n x least:=exists condition,
  source_reflection_condition M(source_L_domain_code M)level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)condition /\
  source_least_ordinal_graph M condition least.
Definition source_reflection_least_formula(level sb sc n x least:term):form:=∃(
  source_reflection_condition_formula(num(sf_encode source_L_domain))(level`[↑])(num(sf_encode source_ordinal_predicate))
    (sb`[↑])(sc`[↑])(n`[↑])(σ(x`[↑]))zero $0 ∧source_least_ordinal_formula $0(least`[↑])).
Local Opaque holds source_reflection_condition_formula source_least_ordinal_formula.

Local Transparent source_L_domain_code source_ordinal_predicate_code.

Theorem source_reflection_least_formula_correct M rho level sb sc n x least:
  holds M rho(source_reflection_least_formula level sb sc n x least) <->
  source_reflection_least_graph M(evalM M rho level)(evalM M rho sb)(evalM M rho sc)(evalM M rho n)(evalM M rho x)(evalM M rho least).
Proof.
  unfold source_reflection_least_formula,source_reflection_least_graph.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite source_reflection_condition_formula_correct. setoid_rewrite source_least_ordinal_formula_correct.
  repeat setoid_rewrite code_eval_num.
  setoid_rewrite condition_eval_succ. setoid_rewrite condition_eval_zero. setoid_rewrite condition_eval_var.
  unfold evalM. repeat setoid_rewrite eval_up.
  unfold source_L_domain_code,source_ordinal_predicate_code. reflexivity.
Qed.

Local Opaque source_L_domain_code source_ordinal_predicate_code.
Local Transparent code_numeral.

Theorem source_reflection_least_total M level sb sc n x:exists least,source_reflection_least_graph M level sb sc n x least.
Proof.
  destruct(source_reflection_condition_total M(source_L_domain_code M)level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)) as(condition&HC).
  destruct(source_least_ordinal_total M condition) as(least&HL). exists least,condition. auto.
Qed.

Theorem source_reflection_least_functional M level sb sc n x a b:
  source_reflection_least_graph M level sb sc n x a ->source_reflection_least_graph M level sb sc n x b ->a=b.
Proof.
  intros(condition&HC&HA)(condition'&HC'&HB).
  pose proof(source_reflection_condition_functional M(source_L_domain_code M)level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)condition' condition HC' HC) as E.
  subst condition'. exact(source_least_ordinal_functional M condition a b HA HB).
Qed.

Theorem source_reflection_least_bounded M level sb sc n x least k:
  source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc n ->coding_lt M x k ->
  source_reflection_least_graph M level sb sc n x least ->source_bounded M least k.
Proof.
  intros HL HV HX(condition&HC&HLeast).
  apply(source_least_ordinal_bound M condition least k);[|exact HLeast].
  exact(source_reflection_condition_bounded M(source_L_domain_code M)level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)condition(succM M k)
    (numerical_L_domain_bounded M)HL(source_ordinal_predicate_bounded M)HV(proj2(FiniteCRT.coding_lt_succ_cancel M x k)HX)
    (coding_zero_lt_succ M k)HC).
Qed.

Theorem source_zfr_reflection_least M level sb sc n x least:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc n ->
  source_reflection_least_graph M level sb sc n x least ->source_zfr_provable M least.
Proof.
  intros HLevel HV(condition&HC&HLeast).
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel) as HL.
  pose proof(source_reflection_condition_bounded M(source_L_domain_code M)level(source_ordinal_predicate_code M)sb sc n(succM M x)(zeroM M)condition(succM M(succM M x))
    (numerical_L_domain_bounded M)HL(source_ordinal_predicate_bounded M)HV(coding_lt_succ M(succM M x))(coding_zero_lt_succ M(succM M x))HC) as BC.
  destruct(sf_relation_total M SFAnd(source_ordinal_predicate_code M)condition) as(body&HBody).
  destruct(sf_relation_total M SFEx body(zeroM M)) as(input&HInput).
  assert(HExist:source_reflection_existence_goal M(source_L_domain_code M)level sb sc n x input).
  { exists condition,body. auto. }
  pose proof(source_zfr_reflection_existence M level sb sc n x input HLevel HV HExist) as PExist.
  destruct(sf_relation_total M SFImpl input least) as(implication&HImp).
  pose proof(source_zfr_least_ordinal M condition(succM M x)least body input implication BC HLeast HBody HInput HImp) as PImp.
  apply(proj1(source_zfr_descriptor_provable M least)).
  exact(source_descriptor_provable_mp M ZFRSourceDescriptor input least implication
    (proj2(source_zfr_descriptor_provable M input)PExist)(proj2(source_zfr_descriptor_provable M implication)PImp)HImp).
Qed.

Theorem source_zfr_reflection_least_total M level sb sc n x:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc n ->
  exists least,source_reflection_least_graph M level sb sc n x least /\source_zfr_provable M least.
Proof.
  intros HL HV. destruct(source_reflection_least_total M level sb sc n x) as(least&HG).
  exists least. split;[exact HG|exact(source_zfr_reflection_least M level sb sc n x least HL HV HG)].
Qed.

Print Assumptions source_reflection_least_formula_correct.
Print Assumptions source_reflection_least_total.
Print Assumptions source_reflection_least_functional.
Print Assumptions source_reflection_least_bounded.
Print Assumptions source_zfr_reflection_least.
Print Assumptions source_zfr_reflection_least_total.
