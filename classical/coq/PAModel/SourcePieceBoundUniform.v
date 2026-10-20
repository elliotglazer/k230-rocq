(** Uniform ordinal closure of every internally finite table of genuine
    reflection pieces. The induction is PA-definable and its conclusion is
    an actual source ZFR derivation in an arbitrary PA model. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FiniteCRTFormula Pairing CodeExpressions NumericalProofs
  SetFormulaCodes SourceBounded NumericalInstantiation SourceLFixed SourceOrdinalPredicate SourceDomainInstances SourceHierarchySyntax
  SourcePieceConjunctionBounds SourcePieceBoundGoal SourcePieceBoundBase SourcePieceBoundSuccessor
  SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Local Opaque source_ordinal_predicate_code source_L_domain_code.

Definition source_pcf_bound_proof_at M domain level n:=forall sb sc g X ordinal goal implication k,
  source_piece_table_valid M sb sc n ->coding_lt M g k ->coding_lt M X k ->
  numerical_instantiation M(source_ordinal_predicate_code M)g ordinal ->
  source_pcf_bound_goal M domain level sb sc n g X goal ->sf_relation M SFImpl ordinal goal implication ->
  source_descriptor_provable M ZFRSourceDescriptor implication.
Definition source_pcf_bound_proof_formula:form:=
  ∀∀∀∀∀∀∀∀(source_piece_table_valid_formula $7 $6 $8 →Peano.sless $5 $0 →Peano.sless $4 $0 →
    numerical_instantiation_formula(num(sf_encode source_ordinal_predicate))$5 $3 →
    source_pcf_bound_goal_formula $9 $10 $7 $6 $8 $5 $4 $2 →sf_formula SFImpl $3 $2 $1 →
    source_descriptor_provable_formula ZFRSourceDescriptor $1).
Local Opaque holds source_piece_table_valid_formula Peano.sless numerical_instantiation_formula
  source_pcf_bound_goal_formula sf_formula source_descriptor_provable_formula.

Theorem source_pcf_bound_proof_definable M domain level:Definable1 M(source_pcf_bound_proof_at M domain level).
Proof.
  exists source_pcf_bound_proof_formula,(domain.:level.:fun _=>zeroM M). intro n.
  unfold source_pcf_bound_proof_formula,source_pcf_bound_proof_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_piece_table_valid_formula_correct. setoid_rewrite less_formula_correct.
  setoid_rewrite numerical_instantiation_formula_correct. setoid_rewrite source_pcf_bound_goal_formula_correct.
  setoid_rewrite sf_formula_correct. setoid_rewrite source_descriptor_provable_formula_correct.
  repeat setoid_rewrite code_eval_num. reflexivity.
Qed.

Theorem source_pcf_bound_proof_all M level:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  forall n,source_pcf_bound_proof_at M(source_L_domain_code M)level n.
Proof.
  intro HLevel.
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HLevel) as HL.
  apply(definable_induction M(source_pcf_bound_proof_at M(source_L_domain_code M)level)
    (source_pcf_bound_proof_definable M(source_L_domain_code M)level)).
  - intros sb sc g X ordinal goal implication k HV HG HX HOrd HGoal HImp.
    apply(proj2(source_zfr_descriptor_provable M implication)).
    exact(source_zfr_pcf_bound_zero M(source_L_domain_code M)level sb sc g X ordinal goal implication k
      (numerical_L_domain_bounded M)HL HG HX HOrd HGoal HImp).
  - intros n IH sb sc g X ordinal goal implication k HV HG HX HOrd HGoal HImp.
    pose proof(source_piece_table_valid_prefix M sb sc n HV) as HPrefix.
    destruct(beta_total M sb sc n) as(entry&HE).
    destruct(pair_surjective M entry) as(count&phi&HP).
    destruct(source_pcf_bound_goal_total M(source_L_domain_code M)level sb sc n g X) as(previous&HPrevious).
    destruct(sf_relation_total M SFImpl ordinal previous) as(oldImp&HOldImp).
    pose proof(IH sb sc g X ordinal previous oldImp k HPrefix HG HX HOrd HPrevious HOldImp) as POld.
    apply(proj2(source_zfr_descriptor_provable M implication)).
    exact(source_zfr_pcf_bound_successor M level sb sc n count phi entry g X ordinal previous goal oldImp implication k
      HLevel HV HG HX HOrd HPrevious HGoal HE HP HOldImp HImp(proj1(source_zfr_descriptor_provable M oldImp)POld)).
Qed.

Theorem source_zfr_pcf_bound_uniform M level sb sc n g X ordinal goal implication k:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc n ->
  coding_lt M g k ->coding_lt M X k ->numerical_instantiation M(source_ordinal_predicate_code M)g ordinal ->
  source_pcf_bound_goal M(source_L_domain_code M)level sb sc n g X goal ->
  sf_relation M SFImpl ordinal goal implication ->source_zfr_provable M implication.
Proof.
  intros HL HV HG HX HOrd HGoal HImp.
  exact(proj1(source_zfr_descriptor_provable M implication)
    (source_pcf_bound_proof_all M level HL n sb sc g X ordinal goal implication k HV HG HX HOrd HGoal HImp)).
Qed.

Theorem source_zfr_pcf_bound_total M level sb sc n g X k:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc n ->
  coding_lt M g k ->coding_lt M X k ->exists ordinal goal implication,
  numerical_instantiation M(source_ordinal_predicate_code M)g ordinal /\
  source_pcf_bound_goal M(source_L_domain_code M)level sb sc n g X goal /\sf_relation M SFImpl ordinal goal implication /\
  source_zfr_provable M implication.
Proof.
  intros HL HV HG HX.
  destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)g) as(ordinal&HOrd).
  destruct(source_pcf_bound_goal_total M(source_L_domain_code M)level sb sc n g X) as(goal&HGoal).
  destruct(sf_relation_total M SFImpl ordinal goal) as(implication&HImp).
  exists ordinal,goal,implication. repeat split;try assumption.
  exact(source_zfr_pcf_bound_uniform M level sb sc n g X ordinal goal implication k HL HV HG HX HOrd HGoal HImp).
Qed.

Print Assumptions source_pcf_bound_proof_definable.
Print Assumptions source_pcf_bound_proof_all.
Print Assumptions source_zfr_pcf_bound_uniform.
Print Assumptions source_zfr_pcf_bound_total.
