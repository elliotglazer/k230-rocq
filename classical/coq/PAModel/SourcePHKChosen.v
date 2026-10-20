(** Ordinary K-ordinal and K-subset laws discharge the chosen successor's
    ordinal/subset obligations. The remaining witness is exactly KF's one. *)
From PAModel Require Import Model FiniteCoding CodeExpressions Pairing SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull NumericalInstantiation NumericalRenamingMaps NumericalRenaming
 SourceHierarchySyntax SourceEwMonotone SourceEwAtSyntax SourceRawSubset SourceMembershipBlocks SourceMembershipBlockProofs
 SourceOrdinalPredicate SourceDomainInstances SourceCofinalGeometry SourceCofinalOrdinalsUse
 SourceReflectionGeometryPredicates SourceReflectionSubsetsUse SourceRecursionPrimitiveRelations
 SourcePieceConjunctionBounds SourceReflectionKFWitness SourceConjunctionRules SourceFiniteTelescope SourceZFRFiniteRule
 SourceZFRProvability SourcePHHierarchyOrdinals.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Theorem source_zfr_PH_K_chosen M domain level sb sc count K k w witness X lk beta Lb start
 entry params phi rb rc rn phi' block ordinals ob subsets lb goal law bound:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 context_member M sb sc count entry ->pair_graph M params phi entry ->
 source_reflection_KF_witness M domain level sb sc count K k w witness ->source_LL_instance M k X lk ->
 source_membership_block M start X params block ->
 renaming_lift M(zeroM M)(zeroM M)(zeroM M)start rb rc rn ->numerical_renaming M phi rb rc rn start phi' ->
 source_cofinal_ordinals M K ordinals ->numerical_instantiation M(source_ordinal_predicate_code M)beta ob ->
 source_reflection_geometry_instance M ReflectionSubsets(source_rec_env2 K beta)subsets ->source_LL_instance M beta Lb lb ->
 source_ew_at M domain phi' Lb goal ->source_bounded M phi'(succM M bound) ->
 coding_lt M K bound ->coding_lt M k bound ->coding_lt M w bound ->coding_lt M X bound ->coding_lt M beta bound ->coding_lt M Lb bound ->
 (forall i,coding_lt M i params ->coding_lt M(addM M i start)bound) ->
 source_finite_telescope M[lk;block;ordinals;ob;subsets;lb;witness]goal law ->source_zfr_provable M law.
Proof.
 intros HD HL HLg HV HE HP HW HK HBlock HRL HR HO HOB HSubsets HLb HEGoal BMatrix BK Bk BW BX Bbeta BLb HNames HLaw.
 destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)w)as(ow&HOW).
 destruct(source_raw_subset_total M w beta)as(subset&HSub).
 destruct(source_finite_telescope_total M[witness;lk;block;ow;ob;subset;lb]goal)as(pointLaw&HPointLaw).
 pose proof(source_zfr_PH_hierarchy_ordinals M domain level sb sc count K k w witness X lk beta Lb start
  entry params phi rb rc rn phi' block ow ob subset lb goal pointLaw bound
  HD HL HLg HV HE HP HW HK HBlock HRL HR HOW HOB HSub HLb HEGoal BMatrix BK Bk BW BX Bbeta BLb HNames HPointLaw)as PPoint.
 pose proof(source_reflection_KF_witness_bounded M domain level sb sc count K k w witness bound HD HL HV BK Bk BW HW)as BWit.
 pose proof(source_LL_instance_bounded M k X lk bound Bk BX HK)as BLK.
 pose proof(source_membership_block_bound M start X params block bound HNames BX HBlock)as BB.
 pose proof(source_cofinal_ordinals_bounded M K ordinals bound BK HO)as BO.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)beta ob bound(source_ordinal_predicate_bounded M)Bbeta HOB)as BOB.
 assert(BSubsets:source_bounded M subsets bound).
 { apply(source_reflection_geometry_instance_bounded M ReflectionSubsets(source_rec_env2 K beta)subsets bound);[|exact HSubsets].
   intros[|[|i]]HI;cbn in HI;try lia;assumption. }
 pose proof(source_LL_instance_bounded M beta Lb lb bound Bbeta BLb HLb)as BLB.
 pose proof(source_ew_at_bounded M domain phi' Lb goal bound HD BMatrix BLb HEGoal)as BG.
 apply(source_zfr_finite_rule M[pointLaw][lk;block;ordinals;ob;subsets;lb;witness]goal law bound).
 - intros f[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];assumption.
 - exact BG.
 - exact HLaw.
 - intros f[<-|[]]. exact PPoint.
 - intros gb gc gn HC Laws Premises.
   pose proof(Premises witness ltac:(cbn;tauto))as PW.
   destruct HW as(member&next&lev&pc&point&all&inner&HM&HN&HLev&HPC&HPoint&HAll&HInner&HWhole).
   pose proof(source_full_conjunction_left M gb gc gn member inner witness HWhole PW)as PM.
   pose proof(source_full_cofinal_ordinals_use M K w ordinals member ow gb gc gn HO HM HOW
    (Premises ordinals ltac:(cbn;tauto))PM)as POW.
   pose proof(source_full_reflection_subsets_use M K beta w subsets member subset gb gc gn HSubsets HM HSub
    (Premises subsets ltac:(cbn;tauto))PM)as PS.
   apply(source_full_finite_telescope_apply M[witness;lk;block;ow;ob;subset;lb]goal pointLaw HPointLaw gb gc gn
    (Laws pointLaw ltac:(cbn;tauto))).
   intros f[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];try(apply Premises;cbn;tauto);assumption.
Qed.
Print Assumptions source_zfr_PH_K_chosen.
