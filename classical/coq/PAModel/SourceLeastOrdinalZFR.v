(** Uniform least-ordinal theorem inside every PA model. The input is an
    arbitrary internally coded predicate, not a decoded standard formula.
    The output is an actual internally coded source ZFR derivation. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded SourceBoundMonotone NumericalSourceFull
  NumericalRenaming SourceQuantifierRules SourceFiniteCutoffShift SourceLeastOrdinalGoal
  SourceLeastOrdinalShift SourceOrdinalPredicate SourceDomainInstances
  SourceLeastOrdinalZFRWitness SourceExistsImplication SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_zfr_least_ordinal M phi count least body inputex implication :
  source_bounded M phi (succM M count) ->source_least_ordinal_graph M phi least ->
  sf_relation M SFAnd (source_ordinal_predicate_code M) phi body ->
  sf_relation M SFEx body (zeroM M) inputex ->sf_relation M SFImpl inputex least implication ->
  source_zfr_provable M implication.
Proof.
  intros HB HG HBody HInput HImp.
  destruct (source_cutoff_shift_total M 1 phi) as (p1&HP1).
  destruct (numerical_renaming_total M least (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (shifted&HShifted).
  pose proof (source_least_ordinal_shift M phi p1 least shifted (succM M count)
    HB HP1 HG HShifted) as HShiftedGoal.
  destruct (sf_relation_total M SFImpl body shifted) as (witnessimp&HWitness).
  destruct (source_zfr_least_ordinal_witness M phi p1 shifted count body witnessimp
    HB HP1 HShiftedGoal HBody HWitness) as (b&c&n&HC&PWitness).
  exists b,c,n. split;[exact HC|].
  assert (HOrd:source_bounded M (source_ordinal_predicate_code M) (succM M count)).
  { exact (source_domain_instance_bound M _ (zeroM M) _ (succM M count)
      (source_ordinal_predicate_bounded M) (coding_zero_lt_succ M count)
      (source_domain_instance_zero M _ (source_ordinal_predicate_bounded M))). }
  assert (HBodyBound:source_bounded M body (succM M count)).
  { exact (proj2 (source_bounded_accept_binary M SFAnd _ _ body _ (or_introl eq_refl) HBody)
      (conj HOrd HB)). }
  assert (HInputBound:source_bounded M inputex count).
  { exact (proj2 (source_bounded_accept_unary M SFEx body inputex count (or_intror eq_refl) HInput) HBodyBound). }
  exact (source_full_exists_implication M b c n count body inputex least shifted witnessimp implication
    (source_zfr_context_closed M b c n HC) HInputBound (source_least_ordinal_bound M phi least count HB HG)
    HInput HShifted HWitness HImp PWitness).
Qed.

Theorem source_zfr_least_ordinal_total M phi count :
  source_bounded M phi (succM M count) ->
  exists least body inputex implication,
    source_least_ordinal_graph M phi least /\
    sf_relation M SFAnd (source_ordinal_predicate_code M) phi body /\
    sf_relation M SFEx body (zeroM M) inputex /\
    sf_relation M SFImpl inputex least implication /\source_zfr_provable M implication.
Proof.
  intro HB. destruct (source_least_ordinal_total M phi) as (least&HG).
  destruct (sf_relation_total M SFAnd (source_ordinal_predicate_code M) phi) as (body&HBody).
  destruct (sf_relation_total M SFEx body (zeroM M)) as (inputex&HInput).
  destruct (sf_relation_total M SFImpl inputex least) as (implication&HImp).
  exists least,body,inputex,implication. split;[exact HG|]. split;[exact HBody|].
  split;[exact HInput|]. split;[exact HImp|].
  exact (source_zfr_least_ordinal M phi count least body inputex implication HB HG HBody HInput HImp).
Qed.

Print Assumptions source_zfr_least_ordinal.
Print Assumptions source_zfr_least_ordinal_total.
