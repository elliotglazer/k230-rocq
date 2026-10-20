(** Generate the actual universally generalized least-witness theorem
    matching a given totality graph, and all internally coded syntax for
    the subsequent coverage proof. No least-witness proof is assumed. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceFiniteCutoffShift SourceOrdinalPredicate SourceOrdinalCollectionRecipe SourceOrdinalCollectionCutoff
  SourceOrdinalCollectionMinimum SourceOrdinalTotality SourceZFRProvability
  SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_oc_coverage_preparation M phi oc x total count :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->source_oc_totality_graph M phi x total ->
  exists phiV phiD ocV ocD leastbody least inputbody exOrd input totalpoint leastImp leastAll,
    source_cutoff_shift M 2 phi phiV /\source_cutoff_shift M 2 phiV phiD /\
    source_cutoff_shift M 2 oc ocV /\source_cutoff_shift M 2 ocV ocD /\
    NumericalRenaming.numerical_renaming M ocD (code_numeral M 3) (code_numeral M 1)
      (code_numeral M 2) (zeroM M) leastbody /\sf_relation M SFEx leastbody (zeroM M) least /\
    sf_relation M SFAnd (source_ordinal_predicate_code M) phiD inputbody /\
    sf_relation M SFEx inputbody (zeroM M) exOrd /\sf_relation M SFMember (zeroM M) (succM M x) input /\
    sf_relation M SFImpl input exOrd totalpoint /\sf_relation M SFAll totalpoint (zeroM M) total /\
    sf_relation M SFImpl exOrd least leastImp /\sf_relation M SFAll leastImp (zeroM M) leastAll /\
    source_zfr_provable M leastAll.
Proof.
  intros HB HO (phiV&phiD&inputbody&exOrd&input&totalpoint&HCv&HCd&HIB&HIE&HI&HTp&HT).
  pose proof (source_cutoff_shift_bounded M 2 phi phiV count HB HCv) as HBv.
  pose proof (source_cutoff_shift_bounded M 2 phiV phiD (succM M count) HBv HCd) as HBd.
  destruct (source_cutoff_shift_total M 2 oc) as (ocV&HOv).
  destruct (source_cutoff_shift_total M 2 ocV) as (ocD&HOd).
  pose proof (source_oc_form_cutoff_two M phi phiV oc ocV (succM M (succM M count)) HB HO HCv HOv) as HOV.
  pose proof (source_oc_form_cutoff_two M phiV phiD ocV ocD (succM M (succM M (succM M count)))
    HBv HOV HCd HOd) as HOD.
  destruct (source_zfr_oc_least_witnesses M phiD ocD (succM M (succM M count)) HBd HOD)
    as (least&leastbody&inputbody'&exOrd'&leastImp&HSwap&HEx&HIB'&HIE'&HImp&PImp).
  pose proof (sf_relation_functional M SFAnd _ _ inputbody' inputbody HIB' HIB) as E. subst inputbody'.
  pose proof (sf_relation_functional M SFEx _ _ exOrd' exOrd HIE' HIE) as E. subst exOrd'.
  destruct (sf_relation_total M SFAll leastImp (zeroM M)) as (leastAll&HAll).
  assert (PAll:source_zfr_provable M leastAll).
  { apply (proj1 (source_zfr_descriptor_provable M leastAll)).
    exact (source_descriptor_provable_all M ZFRSourceDescriptor leastImp leastAll
      (proj2 (source_zfr_descriptor_provable M leastImp) PImp) HAll). }
  exists phiV,phiD,ocV,ocD,leastbody,least,inputbody,exOrd,input,totalpoint,leastImp,leastAll.
  split;[exact HCv|]. split;[exact HCd|]. split;[exact HOv|]. split;[exact HOd|].
  split;[exact HSwap|]. split;[exact HEx|]. split;[exact HIB|]. split;[exact HIE|].
  split;[exact HI|]. split;[exact HTp|]. split;[exact HT|]. split;[exact HImp|].
  split;[exact HAll|exact PAll].
Qed.

Print Assumptions source_oc_coverage_preparation.
