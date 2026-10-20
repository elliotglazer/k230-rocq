(** Bounded output-root existence from an actual ZFR Separation proof,
    with no trace-existence or emitted-closure certificate premise. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceUpperTraceProfile SourceUpperTraceExists SourceUpperWitnessRecipes SourceUpperTraceFrame
  SourceBoundedOutputRoot SourceZFRProvability SourceSetTheoryDescriptors SourceDescriptorProvability
  SourceFiniteProofContexts.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_zfr_bounded_output_root M phi n witness subsetclosed x p xb pb target :
  source_bounded M phi (succM M (succM M n)) ->
  source_upper_witness_closed_recipe M phi (code_numeral M 1)(zeroM M) witness ->
  source_subset_closed_graph M (zeroM M) subsetclosed ->
  sf_relation M SFMember x (zeroM M) xb ->sf_relation M SFMember p (zeroM M) pb ->
  source_trace_output_root_recipe M phi x p target ->
  source_zfr_provable M witness ->source_zfr_provable M subsetclosed ->
  source_zfr_provable M xb ->source_zfr_provable M pb ->source_zfr_provable M target.
Proof.
  intros HP HW HSC HXB HPB HTarget PW PSC PXB PPB.
  destruct (source_zfr_upper_trace_exists_total M phi n HP) as (profile&exprofile&HProfile&HEx&PEx).
  assert (Premises:forall f,In f [exprofile;witness;subsetclosed;xb;pb] ->
      source_descriptor_provable M ZFRSourceDescriptor f).
  { intros f [<-|[<-|[<-|[<-|[<-|[]]]]]];
      apply (proj2 (source_zfr_descriptor_provable M _));assumption. }
  destruct (source_descriptor_finite_common_context M ZFRSourceDescriptor _ Premises)
    as (cb&cc&cn&HC&P).
  exists cb,cc,cn. split;[apply (proj1 (source_zfr_descriptor_context M cb cc cn));exact HC|].
  apply (source_full_bounded_output_root M cb cc cn phi n profile exprofile witness subsetclosed
    x p xb pb target HP HProfile HEx HW HSC HXB HPB HTarget);
    apply P;cbn;tauto.
Qed.

Theorem source_zfr_bounded_output_root_total M phi n witness subsetclosed x p xb pb :
  source_bounded M phi (succM M (succM M n)) ->
  source_upper_witness_closed_recipe M phi (code_numeral M 1)(zeroM M) witness ->
  source_subset_closed_graph M (zeroM M) subsetclosed ->
  sf_relation M SFMember x (zeroM M) xb ->sf_relation M SFMember p (zeroM M) pb ->
  source_zfr_provable M witness ->source_zfr_provable M subsetclosed ->
  source_zfr_provable M xb ->source_zfr_provable M pb ->
  exists target,source_trace_output_root_recipe M phi x p target /\source_zfr_provable M target.
Proof.
  intros HP HW HSC HXB HPB PW PSC PXB PPB.
  destruct (source_trace_output_root_recipe_total M phi x p) as [target HT].
  exists target. split;[exact HT|].
  exact (source_zfr_bounded_output_root M phi n witness subsetclosed x p xb pb target
    HP HW HSC HXB HPB HT PW PSC PXB PPB).
Qed.

Print Assumptions source_zfr_bounded_output_root.
Print Assumptions source_zfr_bounded_output_root_total.
