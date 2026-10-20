(** A total arithmetic recipe packages the intermediate coverage syntax.
    Its universally generalized least theorem is actually proved in ZFR. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  SourceFiniteCutoffShift SourceQfFunctionality NumericalRenaming NumericalSubstitution RenamingSubstitution
  SchemaRenamingDescriptors SourceOrdinalPredicate SourceOrdinalCollectionRecipe SourceOrdinalCoveragePreparation
  SourceOrdinalTotality SourceOrdinalCoverageSyntax SourceOrdinalCoverageAll SourceOrdinalWitnessRange
  SourceReplacementMemberAt SourceOrdinalUpperMembers SourceOrdinalMonotoneUse NumericalSourceFull
  SourceZFRProvability SourceDomainInstances.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Definition source_oc_coverage_plan M phi oc x total leastAll :=
  exists phiV phiD ocV ocD leastbody least inputbody exOrd input totalpoint leastImp,
    source_cutoff_shift M 2 phi phiV /\source_cutoff_shift M 2 phiV phiD /\
    source_cutoff_shift M 2 oc ocV /\source_cutoff_shift M 2 ocV ocD /\
    numerical_renaming M ocD (code_numeral M 3) (code_numeral M 1)
      (code_numeral M 2) (zeroM M) leastbody /\sf_relation M SFEx leastbody (zeroM M) least /\
    sf_relation M SFAnd (source_ordinal_predicate_code M) phiD inputbody /\
    sf_relation M SFEx inputbody (zeroM M) exOrd /\sf_relation M SFMember (zeroM M) (succM M x) input /\
    sf_relation M SFImpl input exOrd totalpoint /\sf_relation M SFAll totalpoint (zeroM M) total /\
    sf_relation M SFImpl exOrd least leastImp /\sf_relation M SFAll leastImp (zeroM M) leastAll.

Theorem source_oc_coverage_plan_total M phi oc x total count :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->source_oc_totality_graph M phi x total ->
  exists leastAll,source_oc_coverage_plan M phi oc x total leastAll /\source_zfr_provable M leastAll.
Proof.
  intros HB HO HT.
  destruct (source_oc_coverage_preparation M phi oc x total count HB HO HT)
    as (phiV&phiD&ocV&ocD&leastbody&least&inputbody&exOrd&input&totalpoint&leastImp&leastAll&H).
  exists leastAll. destruct H as (H1&H2&H3&H4&H5&H6&H7&H8&H9&H10&H11&H12&H13&P).
  split;[|exact P]. exists phiV,phiD,ocV,ocD,leastbody,least,inputbody,exOrd,input,totalpoint,leastImp.
  repeat split;assumption.
Qed.

Theorem source_full_oc_coverage_prepared M b c n phi oc matrix x total leastAll cover
    profile upper mono s count :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->schema_renaming M RepC oc matrix ->
  source_oc_coverage_plan M phi oc x total leastAll ->source_oc_cover_graph M phi x cover ->
  source_replacement_profile_at_graph M s x matrix profile ->source_oc_upper_point_graph M s (zeroM M) upper ->
  source_oc_monotonicity_graph M phi mono ->source_full_prv M b c n total ->
  source_full_prv M b c n leastAll ->source_full_prv M b c n profile ->source_full_prv M b c n upper ->
  source_full_prv M b c n (source_ordinal_predicate_code M) ->source_full_prv M b c n mono ->
  source_full_prv M b c n cover.
Proof.
  intros HB HO HM
    (phiV&phiD&ocV&ocD&leastbody&least&inputbody&exOrd&input&totalpoint&leastImp&
      HCv&HCd&HOv&HOd&HSwap&HEx&HIB&HIE&HI&HTp&HT&HLp&HL)
    (phiV'&result&input'&coverpoint&HCv'&HR&HI'&HCp&HC) HP HU HMono PT PL PP PU PO PM.
  pose proof (source_cutoff_shift_functional M 2 phi phiV' phiV HCv' HCv) as E. subst phiV'.
  pose proof (sf_relation_functional M SFMember _ _ input' input HI' HI) as E. subst input'.
  pose proof (proj1 (numerical_renaming_substitution M phiV (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M) result) HR) as HResult.
  rewrite coding_add_zero_r in HResult.
  exact (source_full_oc_coverage_all M b c n phi phiV phiD oc ocV ocD matrix
    leastbody least inputbody exOrd input totalpoint total leastImp leastAll
    result coverpoint cover profile upper (source_ordinal_predicate_code M) mono
    (code_numeral M 3) (code_numeral M 1) s x (zeroM M) count
    HB HCv HCd HO HOv HOd HM HSwap HEx HIB HIE HI HTp HT HLp HL
    (source_fixed_swap_reopening M) HResult HCp HC HP HU
    (source_domain_instance_zero M _ (source_ordinal_predicate_bounded M)) HMono PT PL PP PU PO PM).
Qed.

Print Assumptions source_oc_coverage_plan_total.
Print Assumptions source_full_oc_coverage_prepared.
