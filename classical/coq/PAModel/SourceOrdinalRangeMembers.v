(** Every member of the literal Replacement range of least ordinals is
    ordinal. The proof uses the actual RepC syntax and ordinary source
    existential elimination, with no semantic range assertion. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SchemaConstructorBounds SourceBounded NumericalRenaming
  NumericalInstantiation SchemaRenamingDescriptors SourceDomainInstances
  SourceOrdinalPredicate SourceOrdinalCollectionRecipe SourceOrdinalCollectionMaps
  SourcePropositionalRebase SourceWFSeparationConstructor SourceFunctionalityShells
  SourceReplacementCollector SourceReplacementDecoration NumericalSourceFull SourceQuantifierRules.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_oc_repc_decoration M phi oc matrix ordinal1 :
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->
  schema_renaming M RepC oc matrix ->
  source_formula_shift M (source_ordinal_predicate_code M) ordinal1 ->
  exists theta tail inner,sf_relation M SFAnd ordinal1 theta inner /\sf_relation M SFAnd inner tail matrix.
Proof.
  intros (ord&swapped&tail&inner&HO&HQ&HT&HI&HOC) HR HShift.
  apply (proj1 (numerical_renaming_binary M SFAnd inner tail oc _ _ _ _ matrix
    (or_introl eq_refl) HOC)) in HR.
  destruct HR as (inner'&tail'&RI&RT&HMatrix).
  apply (proj1 (numerical_renaming_binary M SFAnd ord swapped inner _ _ _ _ inner'
    (or_introl eq_refl) HI)) in RI.
  destruct RI as (ord'&theta&RO&RQ&HInner).
  pose proof (source_collection_domain_instance_renaming M (source_ordinal_predicate_code M)
    (code_numeral M 1) ord (code_numeral M (schema_dividend RepC))
    (code_numeral M (schema_modulus RepC)) (code_numeral M (schema_length RepC))
    (code_numeral M (schema_delta RepC)) ord' (code_numeral M 1)
    (source_ordinal_predicate_bounded M) HO RO
    (proj2 (schema_lookup_second M RepC (code_numeral M 1)) eq_refl)) as HOrd'.
  pose proof (source_domain_instance_shift M _ (zeroM M) _ ordinal1
    (source_ordinal_predicate_bounded M)
    (source_domain_instance_zero M _ (source_ordinal_predicate_bounded M)) HShift) as HOrdinal1.
  pose proof (numerical_instantiation_functional M _ (code_numeral M 1) ord' ordinal1 HOrd' HOrdinal1) as E.
  subst ord'. exists theta,tail',inner'. auto.
Qed.

Definition source_ordinal_members_graph M members :=code_relation M
  (fun _=>source_ordinal_predicate_code M) (E_sf_all (E_sf SFImpl (E_sf_mem 0 1) (CEvar 0))) members.

Lemma source_range_iff_split M env A B a b point :
  code_relation M env A a ->code_relation M env B b ->code_relation M env (E_sf_iff A B) point ->
  exists forward reverse,sf_relation M SFImpl a b forward /\sf_relation M SFImpl b a reverse /\
    sf_relation M SFAnd forward reverse point.
Proof.
  intros HA HB HP. unfold E_sf_iff in HP.
  destruct (schema_expression_split M env SFAnd _ _ point HP) as (forward&reverse&HF&HR&HAnd).
  exists forward,reverse. split.
  - exact (proj1 (schema_expression_graph M env SFImpl A B a b forward HA HB) HF).
  - split;[|exact HAnd]. exact (proj1 (schema_expression_graph M env SFImpl B A b a reverse HB HA) HR).
Qed.

Theorem source_full_oc_range_members M b c n phi oc matrix profile :
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->
  schema_renaming M RepC oc matrix ->source_replacement_profile_graph M matrix profile ->
  source_full_prv M b c n profile ->
  exists members,source_ordinal_members_graph M members /\source_full_prv M b c n members.
Proof.
  intros HOC HMatrix HProfile PProfile.
  destruct (numerical_renaming_total M (source_ordinal_predicate_code M)
    (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)) as (ord1&HOrdShift).
  destruct (source_oc_repc_decoration M phi oc matrix ord1 HOC HMatrix HOrdShift)
    as (theta&tail&inner&HInner&HMatrixGraph).
  unfold source_replacement_profile_graph,E_source_replacement_profile in HProfile.
  destruct (schema_expression_quantifier_split M _ SFAll _ profile HProfile) as (point&HP&HAll).
  destruct (code_relation_total M (E_sf_mem 0 1) (fun _=>matrix)) as (left&HLeftCode).
  destruct (code_relation_total M (E_sf_ex (E_sf SFAnd (E_sf_mem 0 3) (CEvar 0)))
    (fun _=>matrix)) as (ex&HExCode).
  destruct (source_range_iff_split M (fun _=>matrix) _ _ left ex point HLeftCode HExCode HP)
    as (forward&reverse&HForward&HReverse&HPoint).
  destruct (schema_expression_quantifier_split M _ SFEx _ ex HExCode) as (body&HBodyCode&HEx).
  destruct (schema_expression_split M _ SFAnd _ _ body HBodyCode) as (input&matrix'&HInput&HMatrixCode&HBody).
  change (matrix'=matrix) in HMatrixCode. subst matrix'.
  assert (HLeft:sf_relation M SFMember (zeroM M) (code_numeral M 1) left).
  { exact (proj1 (schema_expression_graph M (fun _=>matrix) SFMember (CEconst 0) (CEconst 1)
      (zeroM M) (code_numeral M 1) left eq_refl eq_refl) HLeftCode). }
  destruct (sf_relation_total M SFImpl left (source_ordinal_predicate_code M)) as (targetpoint&HTargetPoint).
  destruct (sf_relation_total M SFAll targetpoint (zeroM M)) as (members&HTargetAll).
  exists members. split.
  - unfold source_ordinal_members_graph,E_sf_all,E_sf_mem. functionality_graph.
  - exact (source_full_replacement_decoration_members M b c n (source_ordinal_predicate_code M)
      ord1 theta tail input inner matrix body ex left forward reverse point profile targetpoint members
      (source_ordinal_predicate_bounded M) HOrdShift HInner HMatrixGraph HBody HEx
      HForward HPoint HAll HTargetPoint HTargetAll PProfile).
Qed.

Print Assumptions source_oc_repc_decoration.
Print Assumptions source_full_oc_range_members.
