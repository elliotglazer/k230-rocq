(** The actual KF law supplies its successor; only the common-level
    point and ordinary outer geometry remain as antecedents. *)
From PAModel Require Import Model FiniteCoding CodeExpressions Pairing SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull NumericalInstantiation NumericalRenamingMaps NumericalRenaming
 SourceHierarchySyntax SourceEwMonotone SourceEwAtSyntax SourceMembershipBlocks SourceMembershipBlockProofs
 SourceOrdinalPredicate SourceDomainInstances SourceCofinalGeometry SourceCofinalCommonPoint
 SourceReflectionGeometryPredicates SourceRecursionPrimitiveRelations SourcePieceConjunctionBounds
 SourceReflectionKF SourceReflectionKFNext SourceReflectionKFUse SourceConjunctionRules
 SourceFiniteTelescope SourceZFRFiniteRule SourceZFRProvability SourcePHSuccessorElimination.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Theorem source_zfr_PH_level_point M domain level sb sc count K whole k member X lk beta Lb start
 entry params phi rb rc rn phi' block ordinals ob subsets lb goal law bound:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 context_member M sb sc count entry ->pair_graph M params phi entry ->
 source_reflection_KF M domain level sb sc count K whole ->sf_relation M SFMember k K member ->
 source_LL_instance M k X lk ->source_membership_block M start X params block ->
 renaming_lift M(zeroM M)(zeroM M)(zeroM M)start rb rc rn ->numerical_renaming M phi rb rc rn start phi' ->
 source_cofinal_ordinals M K ordinals ->numerical_instantiation M(source_ordinal_predicate_code M)beta ob ->
 source_reflection_geometry_instance M ReflectionSubsets(source_rec_env2 K beta)subsets ->source_LL_instance M beta Lb lb ->
 source_ew_at M domain phi' Lb goal ->source_bounded M phi'(succM M bound) ->
 coding_lt M K bound ->coding_lt M k bound ->coding_lt M X bound ->coding_lt M beta bound ->coding_lt M Lb bound ->
 (forall i,coding_lt M i params ->coding_lt M(addM M i start)bound) ->
 source_finite_telescope M[ordinals;ob;subsets;lb;whole;member;lk;block]goal law ->source_zfr_provable M law.
Proof.
 intros HD HL HLg HV HE HP HWhole HM HK HBlock HRL HR HO HOB HSubsets HLb HEGoal BMatrix BK Bk BX Bbeta BLb HNames HLaw.
 destruct(source_reflection_KF_next_total M domain level sb sc count K k)as(next&HNext).
 destruct(source_finite_telescope_total M[lk;block;ordinals;ob;subsets;lb;next]goal)as(pointLaw&HPointLaw).
 pose proof(source_zfr_PH_successor_elimination M domain level sb sc count K k next X lk beta Lb start
  entry params phi rb rc rn phi' block ordinals ob subsets lb goal pointLaw bound
  HD HL HLg HV HE HP HNext HK HBlock HRL HR HO HOB HSubsets HLb HEGoal BMatrix BK Bk BX Bbeta BLb HNames HPointLaw)as PPoint.
 pose proof(source_cofinal_ordinals_bounded M K ordinals bound BK HO)as BO.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)beta ob bound(source_ordinal_predicate_bounded M)Bbeta HOB)as BOB.
 assert(BSubsets:source_bounded M subsets bound).
 { apply(source_reflection_geometry_instance_bounded M ReflectionSubsets(source_rec_env2 K beta)subsets bound);[|exact HSubsets].
   intros[|[|i]]HI;cbn in HI;try lia;assumption. }
 pose proof(source_LL_instance_bounded M beta Lb lb bound Bbeta BLb HLb)as BLB.
 pose proof(source_reflection_KF_bounded M domain level sb sc count K whole bound HD HL HV BK HWhole)as BW.
 pose proof(proj2(source_bounded_accept_atom M SFMember k K member bound(or_introl eq_refl)HM)(conj Bk BK))as BM.
 pose proof(source_LL_instance_bounded M k X lk bound Bk BX HK)as BLK.
 pose proof(source_membership_block_bound M start X params block bound HNames BX HBlock)as BB.
 pose proof(source_ew_at_bounded M domain phi' Lb goal bound HD BMatrix BLb HEGoal)as BG.
 apply(source_zfr_finite_rule M[pointLaw][ordinals;ob;subsets;lb;whole;member;lk;block]goal law bound).
 - intros f[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];assumption.
 - exact BG.
 - exact HLaw.
 - intros f[<-|[]]. exact PPoint.
 - intros gb gc gn HC Laws Premises.
   pose proof(source_full_reflection_KF_use M domain level sb sc count K k whole member next gb gc gn
    HD HL HV HWhole HM HNext(Premises whole ltac:(cbn;tauto))(Premises member ltac:(cbn;tauto)))as PNext.
   apply(source_full_finite_telescope_apply M[lk;block;ordinals;ob;subsets;lb;next]goal pointLaw HPointLaw gb gc gn
    (Laws pointLaw ltac:(cbn;tauto))).
   intros f[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];try(apply Premises;cbn;tauto). exact PNext.
Qed.
Theorem source_zfr_PH_common_point M domain level sb sc count K whole k X common beta Lb start
 entry params phi rb rc rn phi' ordinals ob subsets lb goal law bound:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 context_member M sb sc count entry ->pair_graph M params phi entry ->
 source_reflection_KF M domain level sb sc count K whole ->source_cofinal_common_point M start params K k X common ->
 renaming_lift M(zeroM M)(zeroM M)(zeroM M)start rb rc rn ->numerical_renaming M phi rb rc rn start phi' ->
 source_cofinal_ordinals M K ordinals ->numerical_instantiation M(source_ordinal_predicate_code M)beta ob ->
 source_reflection_geometry_instance M ReflectionSubsets(source_rec_env2 K beta)subsets ->source_LL_instance M beta Lb lb ->
 source_ew_at M domain phi' Lb goal ->source_bounded M phi'(succM M bound) ->
 coding_lt M K bound ->coding_lt M k bound ->coding_lt M X bound ->coding_lt M beta bound ->coding_lt M Lb bound ->
 (forall i,coding_lt M i params ->coding_lt M(addM M i start)bound) ->
 source_finite_telescope M[ordinals;ob;subsets;lb;whole;common]goal law ->source_zfr_provable M law.
Proof.
 intros HD HL HLg HV HE HP HWhole HCommon HRL HR HO HOB HSubsets HLb HEGoal BMatrix BK Bk BX Bbeta BLb HNames HLaw.
 pose proof HCommon as(c&member&(block&ordinal&lk&pair&HBlock&HOrd&HK&HPair&HC)&HM&HAnd).
 destruct(source_finite_telescope_total M[ordinals;ob;subsets;lb;whole;member;lk;block]goal)as(pointLaw&HPointLaw).
 pose proof(source_zfr_PH_level_point M domain level sb sc count K whole k member X lk beta Lb start
  entry params phi rb rc rn phi' block ordinals ob subsets lb goal pointLaw bound
  HD HL HLg HV HE HP HWhole HM HK HBlock HRL HR HO HOB HSubsets HLb HEGoal BMatrix BK Bk BX Bbeta BLb HNames HPointLaw)as PPoint.
 pose proof(source_cofinal_ordinals_bounded M K ordinals bound BK HO)as BO.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)beta ob bound(source_ordinal_predicate_bounded M)Bbeta HOB)as BOB.
 assert(BSubsets:source_bounded M subsets bound).
 { apply(source_reflection_geometry_instance_bounded M ReflectionSubsets(source_rec_env2 K beta)subsets bound);[|exact HSubsets].
   intros[|[|i]]HI;cbn in HI;try lia;assumption. }
 pose proof(source_LL_instance_bounded M beta Lb lb bound Bbeta BLb HLb)as BLB.
 pose proof(source_reflection_KF_bounded M domain level sb sc count K whole bound HD HL HV BK HWhole)as BW.
 pose proof(source_cofinal_common_point_bounded M start params K k X common bound HNames BK Bk BX HCommon)as BC.
 pose proof(source_ew_at_bounded M domain phi' Lb goal bound HD BMatrix BLb HEGoal)as BG.
 apply(source_zfr_finite_rule M[pointLaw][ordinals;ob;subsets;lb;whole;common]goal law bound).
 - intros f[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];assumption.
 - exact BG.
 - exact HLaw.
 - intros f[<-|[]]. exact PPoint.
 - intros gb gc gn BCtx Laws Premises.
   pose proof(Premises common ltac:(cbn;tauto))as PC.
   pose proof(source_full_conjunction_left M gb gc gn member c common HAnd PC)as PM.
   pose proof(source_full_conjunction_right M gb gc gn member c common HAnd PC)as PCC.
   pose proof(source_full_conjunction_left M gb gc gn pair block c HC PCC)as PP.
   pose proof(source_full_conjunction_right M gb gc gn pair block c HC PCC)as PB.
   pose proof(source_full_conjunction_right M gb gc gn ordinal lk pair HPair PP)as PLK.
   apply(source_full_finite_telescope_apply M[ordinals;ob;subsets;lb;whole;member;lk;block]goal pointLaw HPointLaw gb gc gn
    (Laws pointLaw ltac:(cbn;tauto))).
   intros f[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];try(apply Premises;cbn;tauto);assumption.
Qed.
Print Assumptions source_zfr_PH_level_point.
Print Assumptions source_zfr_PH_common_point.
