(** Ordinary Refl use with an arbitrary internally coded short-prefix
 substitution, including the genuine native diagonal and point maps. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 NumericalSubstitutionMaps NumericalSubstitution SourceSubstitutionBounds SourceReflectionSubstitutionPrefix
 SourceRelativization SourceSetRelativization SourceIffGraphs SourceHierarchySyntax SourceOrdinaryReflectionSyntax
 SourceOrdinaryReflectionAssignment SourceBallSElimination.
Unset Implicit Arguments.
Theorem source_full_ordinary_reflection_substitution M domain count phi d refl carrier level rb rc rn base
 phi' left right equiv gb gc gn k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->context_bounded M gb gc gn k ->
 coding_lt M d k ->coding_lt M carrier k ->substitution_maps_bound M rb rc rn base count k ->
 source_ordinary_reflection M domain count phi d refl ->source_LL_instance M d carrier level ->
 numerical_substitution M phi rb rc rn base phi' ->source_relativization M domain phi' left ->
 source_set_relativization M carrier phi' right ->source_iff_graph M left right equiv ->
 source_full_prv M gb gc gn refl ->source_full_prv M gb gc gn level ->
 (forall i t member,coding_lt M i count ->substitution_lookup M rb rc rn base i t ->
   sf_relation M SFMember t carrier member ->source_full_prv M gb gc gn member) ->source_full_prv M gb gc gn equiv.
Proof.
 intros HD HP HC HDK HY HM HRefl HLevel HSub HLeft HRight HEquiv PRefl PLevel HMembers.
 destruct(source_substitution_live_prefix_total M rb rc rn base count)as(pb&pc&HPrefix).
 assert(HSubPrefix:numerical_substitution M phi pb pc count(zeroM M)phi').
 { apply(numerical_substitution_live_prefix M phi count rb rc rn base phi' pb pc k HP HM HSub).
   intros i v HI HV. exact(proj2(HPrefix i v HI)HV). }
 assert(HBound:substitution_maps_bound M pb pc count(zeroM M)count k).
 { intros i v HI HV. exact(HM i v HI(proj1(HPrefix i v HI)HV)). }
 apply(source_full_ordinary_reflection_assignment M domain count phi d refl carrier level pb pc phi' left right equiv gb gc gn k
  HD HP HC HDK HY HBound HRefl HLevel HSubPrefix HLeft HRight HEquiv PRefl PLevel).
 intros i t member HI HT HMember.
 apply(HMembers i t member HI);[|exact HMember]. apply(proj1(HPrefix i t HI)).
 exact(proj2(substitution_lookup_inside M pb pc count(zeroM M)i t HI)HT).
Qed.
Print Assumptions source_full_ordinary_reflection_substitution.
