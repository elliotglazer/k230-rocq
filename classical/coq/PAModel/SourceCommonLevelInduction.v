(** Genuine PA-definable induction on the internally finite number of L
    parameters. Produces ordinary source ZFR proofs, including at nonstandard
    parameter counts. No schema-provability premise is assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes NumericalProofs
  SourceBounded SourceQuantifierRules SourceOrdinalPredicate SourceLFixed NumericalInstantiation SourceDomainInstances
  SourcePredicateBlocks SourcePredicateBlockProofs SourceCommonLevelRecipe SourceCommonLevelWitness
  SourceCommonLevelBase SourceCommonLevelSuccessorZFR SourceCommonLevelPrograms SourceZFRProvability.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Local Opaque source_ordinal_predicate_code source_L_domain_code.

Definition source_common_level_proof_at M count :=forall start block target result,
  source_predicate_block M start(source_L_domain_code M)count block ->
  source_common_level_recipe M start count target ->sf_relation M SFImpl block target result ->
  source_zfr_provable M result.
Definition source_common_level_proof_formula :form :=
  ∀∀∀∀ (source_predicate_block_formula $3 $6 $4 $2 →
    source_common_level_formula $5 $3 $4 $1 →sf_formula SFImpl $2 $1 $0 →source_zfr_provable_formula $0).
Local Opaque holds source_predicate_block_formula source_common_level_formula sf_formula source_zfr_provable_formula.
Lemma source_common_level_proof_definable M :Definable1 M(source_common_level_proof_at M).
Proof.
  exists source_common_level_proof_formula,
    (source_ordinal_predicate_code M .:source_L_domain_code M .:fun _=>zeroM M). intro count.
  unfold source_common_level_proof_formula,source_common_level_proof_at,source_common_level_recipe.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_predicate_block_formula_correct.
  setoid_rewrite source_common_level_formula_correct.
  setoid_rewrite sf_formula_correct. setoid_rewrite source_zfr_provable_formula_correct. reflexivity.
Qed.

Theorem source_zfr_common_level_proof M :forall count,source_common_level_proof_at M count.
Proof.
  apply(definable_induction M(source_common_level_proof_at M)(source_common_level_proof_definable M)).
  - intros start block target result HBlock HTarget HResult.
    apply(source_zfr_common_ignore M block target result(zeroM M)).
    + apply source_predicate_block_zero in HBlock.
      apply(proj2(source_bounded_accept_binary M SFImpl(zeroM M)(zeroM M)block(zeroM M)
        (or_intror(or_intror eq_refl))HBlock)). split;apply source_bounded_accept_falsity.
    + apply(source_common_level_recipe_bounded M start(zeroM M)target(zeroM M));[|exact HTarget].
      intros i HI. exfalso. exact(coding_not_lt_zero M i HI).
    + exact HResult.
    + exact(source_zfr_common_level_zero M start target HTarget).
  - intros count IH start block target result HBlock HTarget HResult.
    apply source_predicate_block_succ in HBlock.
    destruct HBlock as(previousBlock&ly&HPreviousBlock&HLY&HAnd).
    destruct(source_common_level_recipe_total M start count) as(old&HOld).
    destruct(sf_relation_total M SFImpl previousBlock old) as(previous&HPrevious).
    pose proof(IH start previousBlock old previous HPreviousBlock HOld HPrevious) as PPrevious.
    destruct(sf_relation_total M SFImpl ly target) as(tail&HTail).
    destruct(sf_relation_total M SFImpl old tail) as(successor&HSuccessor).
    pose proof(source_zfr_common_level_successor M start count old ly target tail successor
      HOld HLY HTarget HTail HSuccessor) as PSuccessor.
    set(k:=succM M(addM M count start)).
    assert(HNames:forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i start)k).
    { intros i HI. exact(source_common_parameter_bound M i count start HI). }
    assert(HNamesPrefix:forall i,coding_lt M i count ->coding_lt M(addM M i start)k).
    { intros i HI. exact(HNames i(coding_lt_trans M i count(succM M count)HI(coding_lt_succ M count))). }
    pose proof(source_predicate_block_bound M start(source_L_domain_code M)count previousBlock k
      HNamesPrefix(numerical_L_domain_bounded M)HPreviousBlock) as BPreviousBlock.
    pose proof(source_domain_instance_bound M(source_L_domain_code M)(addM M count start)ly k
      (numerical_L_domain_bounded M)(coding_lt_succ M(addM M count start))HLY) as BLY.
    pose proof(source_common_level_recipe_bounded M start count old k HNamesPrefix HOld) as BOld.
    pose proof(source_common_level_recipe_bounded M start(succM M count)target k HNames HTarget) as BTarget.
    exact(source_zfr_common_step M previousBlock ly old target previous tail successor block result k
      BPreviousBlock BLY BOld BTarget HPrevious HTail HSuccessor HAnd HResult PPrevious PSuccessor).
Qed.

Theorem source_zfr_common_level_from_L_parameters M start count block target result :
  source_predicate_block M start(source_L_domain_code M)count block ->
  source_common_level_recipe M start count target ->sf_relation M SFImpl block target result ->
  source_zfr_provable M result.
Proof. exact(source_zfr_common_level_proof M count start block target result). Qed.
Print Assumptions source_common_level_proof_definable.
Print Assumptions source_zfr_common_level_proof.
Print Assumptions source_zfr_common_level_from_L_parameters.
