(** Foundation minimum extraction from an actually nonempty filtered set.
    Nonemptiness is proved by specializing its profile at the supplied
    ordinary witness, rather than assumed as a derivability closure. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SchemaConstructorBounds SourceBounded NumericalContexts NumericalInstantiation
  NumericalSourceFull SourceInstantiationConstructors SourcePropositionalRebase
  SourceLeastOrdinalGoal SourceOrdinalPredicate SourceLeastOrdinalFixed
  SourceCanonicalFilteredMinimum SourceFilterMemberIntroduction SourceRegularMinimumShell.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Lemma canonical_regular_minimum_split M rho law :
  code_relation M rho (least_fixed_parameter_expression LeastRegularMinimum) law ->
  exists premise minimum,
    sf_relation M SFImpl premise minimum law /\
    sf_relation M SFMember (rho 1) (rho 0) premise /\
    code_relation M (fun _=>rho 0) canonical_raw_minimum minimum.
Proof.
  intro H.
  destruct (source_regular_minimum_shell M rho law H)
    as (premise&minimum&body&member&allexclusion&exclusion&member01&memberS&neg
      &HL&HP&HEx&HBody&HMember&HAll&HExc&H01&HNeg&HMemberS).
  exists premise,minimum. split;[exact HL|]. split.
  - exact HP.
  - destruct (code_relation_total M canonical_raw_minimum (fun _=>rho 0)) as (minimum'&HG).
    destruct (canonical_raw_minimum_split M (rho 0) minimum' HG)
      as (body'&member'&allexclusion'&exclusion'&member01'&memberS'&neg'
        &HEx'&HBody'&HMember'&HAll'&HExc'&H01'&HNeg'&HMemberS').
    pose proof (sf_relation_functional M SFMember _ _ member' member HMember' HMember) as E.
    subst member'.
    pose proof (sf_relation_functional M SFMember _ _ member01' member01 H01' H01) as E.
    subst member01'.
    pose proof (sf_relation_functional M SFMember _ _ memberS' memberS HMemberS' HMemberS) as E.
    subst memberS'.
    pose proof (sf_relation_functional M SFImpl _ _ neg' neg HNeg' HNeg) as E. subst neg'.
    pose proof (sf_relation_functional M SFImpl _ _ exclusion' exclusion HExc' HExc) as E.
    subst exclusion'.
    pose proof (sf_relation_functional M SFAll _ _ allexclusion' allexclusion HAll' HAll) as E.
    subst allexclusion'.
    pose proof (sf_relation_functional M SFAnd _ _ body' body HBody' HBody) as E. subst body'.
    pose proof (sf_relation_functional M SFEx _ _ minimum' minimum HEx' HEx) as E.
    now subst minimum'.
Qed.

Theorem source_full_filter_to_least M b c n k s a t phi instance
    ordinal law regularlaw allprofile memberA target :
  context_bounded M b c n k ->
  coding_lt M s k ->coding_lt M a k ->coding_lt M t k ->
  source_bounded M phi (succM M k) ->
  numerical_instantiation M (source_ordinal_predicate_code M) a ordinal ->
  numerical_instantiation M phi t instance ->
  code_relation M (fun _=>a) (least_fixed_parameter_expression LeastOrdinalMember) law ->
  code_relation M (schema_env3 s t (zeroM M))
    (least_fixed_parameter_expression LeastRegularMinimum) regularlaw ->
  code_relation M (canonical_filter_environment phi s a) canonical_filter_profile allprofile ->
  sf_relation M SFMember t a memberA ->source_least_ordinal_graph M phi target ->
  source_full_prv M b c n allprofile ->source_full_prv M b c n ordinal ->
  source_full_prv M b c n law ->source_full_prv M b c n regularlaw ->
  source_full_prv M b c n memberA ->source_full_prv M b c n instance ->
  source_full_prv M b c n target.
Proof.
  intros HC HS HA HT HB HO HI HL HR HP HMA HG PP PO PL PR PA PI.
  destruct (canonical_regular_minimum_split M (schema_env3 s t (zeroM M)) regularlaw HR)
    as (memberS&rawex&HReg&HMS&HRaw).
  pose proof (source_full_filter_member_introduction M b c n k s a t phi instance
    allprofile memberS memberA HC HT HS HA HB HP HI HMS HMA PP PA PI) as PS.
  assert (PMinimum:source_full_prv M b c n rawex).
  { exact (full_source_IE M b c n memberS rawex regularlaw
      (source_wf_binary_right M b c n SFImpl memberS rawex regularlaw
        (or_intror (or_intror eq_refl)) HReg (source_full_prv_wellformed M b c n regularlaw PR))
      PR PS HReg). }
  exact (source_full_canonical_filtered_minimum M b c n k s a phi ordinal law
    allprofile rawex target HC HS HA HB HO HL HP HRaw HG PP PO PL PMinimum).
Qed.

Print Assumptions canonical_regular_minimum_split.
Print Assumptions source_full_filter_to_least.
