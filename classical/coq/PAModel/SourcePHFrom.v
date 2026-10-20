(** The pinned PH_from mathematics as an actual internally coded source
    proof. All antecedents are ordinary K/hierarchy geometry; the parameter
    count and recognized piece table are arbitrary elements of the PA model. *)
From PAModel Require Import Model FiniteCoding CodeExpressions Pairing SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull NumericalRenamingMaps NumericalRenaming NumericalInstantiation
 SourceOrdinalPredicate SourceDomainInstances SourceCofinalGeometry SourceHierarchySyntax SourceMembershipBlocks SourceMembershipBlockProofs
 SourceReflectionGeometryPredicates SourceRecursionPrimitiveRelations SourceReflectionKF SourcePieceConjunctionBounds
 SourceEwMonotone SourceEwAtSyntax SourceFiniteTelescope SourceZFRFiniteRule SourceZFRProvability
 SourceCofinalRequest SourceCofinalCommonRecipe SourceCofinalCommonInduction SourcePHGeometryFrame SourcePHCommonElimination.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Theorem source_zfr_PH_from M domain level sb sc count K beta Lb seed start
 entry params phi rb rc rn phi' member ordinals cover ob subsets lb whole block goal law bound:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 context_member M sb sc count entry ->pair_graph M params phi entry ->
 sf_relation M SFMember seed K member ->source_cofinal_ordinals M K ordinals ->source_cofinal_cover M K Lb cover ->
 numerical_instantiation M(source_ordinal_predicate_code M)beta ob ->
 source_reflection_geometry_instance M ReflectionSubsets(source_rec_env2 K beta)subsets ->source_LL_instance M beta Lb lb ->
 source_reflection_KF M domain level sb sc count K whole ->source_membership_block M start Lb params block ->
 renaming_lift M(zeroM M)(zeroM M)(zeroM M)start rb rc rn ->numerical_renaming M phi rb rc rn start phi' ->
 source_ew_at M domain phi' Lb goal ->source_bounded M phi'(succM M bound) ->
 coding_lt M K bound ->coding_lt M beta bound ->coding_lt M Lb bound ->coding_lt M seed bound ->
 (forall i,coding_lt M i params ->coding_lt M(addM M i start)bound) ->
 source_finite_telescope M[member;ordinals;cover;ob;subsets;lb;whole;block]goal law ->source_zfr_provable M law.
Proof.
 intros HD HL HLg HV HE HP HM HO HC HOB HSub HLb HW HB HRL HR HG BMatrix BK Bbeta BLb BSeed HNames HLaw.
 destruct(source_cofinal_common_recipe_total M start params K)as(common&HCommon).
 destruct(source_finite_telescope_total M[member;ordinals;cover;block]common)as(commonLaw&HCommonLaw).
 pose proof(source_zfr_cofinal_common_parameters M start params K Lb seed member ordinals cover block common commonLaw
  HM HO HC HB HCommon(proj2(source_cofinal_request_telescope M member ordinals cover block common commonLaw)HCommonLaw))as PCommon.
 set(frame:=[ordinals;ob;subsets;lb;whole]).
 assert(HFrame:source_PH_geometry_frame M domain level sb sc count K beta Lb frame).
 { exists ordinals,ob,subsets,lb,whole. auto 10. }
 destruct(source_finite_telescope_total M(frame++[common])goal)as(pointLaw&HPointLaw).
 pose proof(source_zfr_PH_common_elimination M domain level sb sc count K beta Lb start
  entry params phi rb rc rn phi' frame common goal pointLaw bound
  HD HL HLg HV HE HP HFrame HCommon HRL HR HG BMatrix BK Bbeta BLb HNames HPointLaw)as PPoint.
 pose proof(source_PH_geometry_frame_bounded M domain level sb sc count K beta Lb frame bound HD HL HV BK Bbeta BLb HFrame)as BFrame.
 pose proof(proj2(source_bounded_accept_atom M SFMember seed K member bound(or_introl eq_refl)HM)(conj BSeed BK))as BM.
 pose proof(source_cofinal_cover_bounded M K Lb cover bound BK BLb HC)as BC.
 pose proof(source_membership_block_bound M start Lb params block bound HNames BLb HB)as BB.
 pose proof(source_ew_at_bounded M domain phi' Lb goal bound HD BMatrix BLb HG)as BG.
 apply(source_zfr_finite_rule M[commonLaw;pointLaw][member;ordinals;cover;ob;subsets;lb;whole;block]goal law bound).
 - intros f[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];try assumption;apply BFrame;unfold frame;cbn;tauto.
 - exact BG.
 - exact HLaw.
 - intros f[<-|[<-|[]]];assumption.
 - intros gb gc gn BCtx Laws Premises.
   assert(PCommonHere:source_full_prv M gb gc gn common).
   { apply(source_full_finite_telescope_apply M[member;ordinals;cover;block]common commonLaw HCommonLaw gb gc gn
      (Laws commonLaw ltac:(cbn;tauto))).
     intros f[<-|[<-|[<-|[<-|[]]]]];apply Premises;cbn;tauto. }
   apply(source_full_finite_telescope_apply M(frame++[common])goal pointLaw HPointLaw gb gc gn
    (Laws pointLaw ltac:(cbn;tauto))).
   intros f HF. apply in_app_or in HF. destruct HF as[HF|[<-|[]]];[|exact PCommonHere].
   apply Premises. unfold frame in HF. cbn in HF|-*. tauto.
Qed.
Print Assumptions source_zfr_PH_from.
