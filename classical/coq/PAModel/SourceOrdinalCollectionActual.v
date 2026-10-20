(** The actual uniform ZFR ordinal-collection theorem, with only the
    literal source syntax and its original matrix bound as inputs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalRenaming NumericalInstantiation SourceOrdinalPredicate SourceOrdinalInitialMonoMaps
  SourceOrdinalInitialTotality SourceOrdinalInitialMonotonicity SourceOrdinalMonotoneUse
  SourceOrdinalUpperMembers SourcePropositionalTemplates SourceOrdinalInitialBounds
  SourceOrdinalCoverageSyntax SourceOrdinalCollectionTheorem SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_zfr_ordinal_collection_theorem M phi total mono output tail implication count :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_initial_totality_graph M phi total ->source_oc_initial_monotonicity_graph M phi mono ->
  source_oc_output_graph M phi (code_numeral M 1) output ->
  sf_relation M SFImpl mono output tail ->sf_relation M SFImpl total tail implication ->
  source_zfr_provable M implication.
Proof.
  intros HB HT HM HO HTail HImp.
  exact (source_zfr_ordinal_collection_theorem_bounded M phi total mono output tail implication count
    (succM M count) HB HT HM HO
    (source_oc_initial_totality_bounded M phi total count HB HT)
    (source_oc_initial_monotonicity_bounded M phi mono count HB HM) HTail HImp).
Qed.

Theorem source_oc_initial_monotonicity_total M phi :
  exists mono,source_oc_initial_monotonicity_graph M phi mono.
Proof.
  destruct (numerical_renaming_total M phi (code_numeral M 9) (code_numeral M 3)
    (code_numeral M 2) (code_numeral M 2)) as (left&HL).
  destruct (numerical_renaming_total M phi (code_numeral M 16) (code_numeral M 3)
    (code_numeral M 2) (code_numeral M 2)) as (right&HR).
  destruct (numerical_instantiation_total M (source_ordinal_predicate_code M) (code_numeral M 1))
    as (ordD&ab&ac&HHead&HD).
  destruct (source_oc_subset_total M (code_numeral M 1) (zeroM M)) as (subset&HS).
  destruct (code_relation_total M (source_prop_expression source_oc_mono_template)
    (source_oc_mono_environment ordD (source_ordinal_predicate_code M) subset left right)) as (point&HP).
  destruct (sf_relation_total M SFAll point (zeroM M)) as (inner&HI).
  destruct (sf_relation_total M SFAll inner (zeroM M)) as (middle&HM).
  destruct (sf_relation_total M SFAll middle (zeroM M)) as (mono&HO).
  exists mono,left,right,ordD,subset,point,inner,middle. split;[exact HL|]. split;[exact HR|].
  split;[exists ab,ac;auto|]. split;[exact HS|]. split;[exact HP|]. split;[exact HI|]. split;assumption.
Qed.

Theorem source_zfr_ordinal_collection_theorem_total M phi count :
  source_bounded M phi (succM M (succM M count)) ->
  exists total mono output tail implication,
    source_oc_initial_totality_graph M phi total /\source_oc_initial_monotonicity_graph M phi mono /\
    source_oc_output_graph M phi (code_numeral M 1) output /\
    sf_relation M SFImpl mono output tail /\sf_relation M SFImpl total tail implication /\
    source_zfr_provable M implication.
Proof.
  intro HB.
  destruct (source_oc_initial_totality_total M phi) as (total&HT).
  destruct (source_oc_initial_monotonicity_total M phi) as (mono&HM).
  destruct (source_oc_output_total M phi (code_numeral M 1)) as (output&HO).
  destruct (sf_relation_total M SFImpl mono output) as (tail&HTail).
  destruct (sf_relation_total M SFImpl total tail) as (implication&HImp).
  exists total,mono,output,tail,implication. split;[exact HT|]. split;[exact HM|].
  split;[exact HO|]. split;[exact HTail|]. split;[exact HImp|].
  exact (source_zfr_ordinal_collection_theorem M phi total mono output tail implication count HB HT HM HO HTail HImp).
Qed.

Print Assumptions source_zfr_ordinal_collection_theorem.
Print Assumptions source_oc_initial_monotonicity_total.
Print Assumptions source_zfr_ordinal_collection_theorem_total.
