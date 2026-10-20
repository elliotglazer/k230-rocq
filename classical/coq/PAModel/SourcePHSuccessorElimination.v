(** Actual ExE removes the K-successor selected by KF. The resulting
    telescope retains only ordinary geometry and KF's existential conclusion. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions Pairing SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull NumericalInstantiation NumericalRenamingMaps NumericalRenaming
 SourceOrdinalPredicate SourceDomainInstances SourceCofinalGeometry SourceHierarchySyntax SourceHierarchyShifts
 SourceEwMonotone SourceEwAtSyntax SourceEwShift SourceFiniteCutoffShift SourceImplicationAllShift
 SourceMembershipBlocks SourceMembershipBlockProofs SourceCommonLevelWitness SourceRecursionPrimitiveRelations
 SourceReflectionGeometryPredicates SourceReflectionKFWitness SourceReflectionKFNext SourcePieceConjunctionBounds
 SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRProvability SourcePieceOffsetShift SourcePHGeometryShifts SourcePHKChosen.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Theorem source_zfr_PH_successor_elimination M domain level sb sc count K k next X lk beta Lb start
 entry params phi rb rc rn phi' block ordinals ob subsets lb goal law bound:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 context_member M sb sc count entry ->pair_graph M params phi entry ->
 source_reflection_KF_next M domain level sb sc count K k next ->source_LL_instance M k X lk ->source_membership_block M start X params block ->
 renaming_lift M(zeroM M)(zeroM M)(zeroM M)start rb rc rn ->numerical_renaming M phi rb rc rn start phi' ->
 source_cofinal_ordinals M K ordinals ->numerical_instantiation M(source_ordinal_predicate_code M)beta ob ->
 source_reflection_geometry_instance M ReflectionSubsets(source_rec_env2 K beta)subsets ->source_LL_instance M beta Lb lb ->
 source_ew_at M domain phi' Lb goal ->source_bounded M phi'(succM M bound) ->
 coding_lt M K bound ->coding_lt M k bound ->coding_lt M X bound ->coding_lt M beta bound ->coding_lt M Lb bound ->
 (forall i,coding_lt M i params ->coding_lt M(addM M i start)bound) ->
 source_finite_telescope M[lk;block;ordinals;ob;subsets;lb;next]goal law ->source_zfr_provable M law.
Proof.
 intros HD HL HLg HV HE HP HNext HK HBlock HRL HR HO HOB HSubsets HLb HEGoal BMatrix BK Bk BX Bbeta BLb HNames HLaw.
 assert(BS:forall x,coding_lt M x bound ->coding_lt M(succM M x)(succM M bound)).
 { intros x HX. exact(proj2(coding_lt_succ_cancel M x bound)HX). }
 destruct(source_cutoff_shift_total M 1 phi')as(phi2&HCut).
 pose proof(source_cutoff_shift_bounded M 1 phi' phi2 bound BMatrix HCut)as BMatrix2.
 destruct(renaming_lift_total M(zeroM M)(zeroM M)(zeroM M)(succM M start))as(rb2&rc2&rn2&HRL2).
 pose proof(source_piece_offset_shift M params start phi phi' phi2 rb rc rn rb2 rc2 rn2(HV entry params phi HE HP)HRL HR HCut HRL2)as HR2.
 destruct(source_LL_instance_total M(succM M k)(succM M X))as(lk1&HK1).
 destruct(source_membership_block_total M(succM M start)(succM M X)params)as(block1&HB1).
 destruct(source_cofinal_ordinals_total M(succM M K))as(ord1&HO1).
 destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)(succM M beta))as(ob1&HOB1).
 destruct(source_reflection_geometry_instance_total M ReflectionSubsets(source_rec_env2(succM M K)(succM M beta)))as(subsets1&HSubsets1).
 destruct(source_LL_instance_total M(succM M beta)(succM M Lb))as(lb1&HLb1).
 destruct(source_ew_at_total M domain phi2(succM M Lb))as(goal1&HEG1).
 assert(HNames1:forall i,coding_lt M i params ->coding_lt M(addM M i(succM M start))(succM M bound)).
 { intros i HI. rewrite source_common_add_successor. exact(BS _ (HNames i HI)). }
 pose proof HNext as(body&HBody&HEx).
 destruct(source_finite_telescope_total M[lk1;block1;ord1;ob1;subsets1;lb1;body]goal1)as(branch&HBranch).
 pose proof(source_zfr_PH_K_chosen M domain level sb sc count(succM M K)(succM M k)(zeroM M)body(succM M X)lk1
  (succM M beta)(succM M Lb)(succM M start)entry params phi rb2 rc2 rn2 phi2 block1 ord1 ob1 subsets1 lb1 goal1 branch(succM M bound)
  HD HL HLg HV HE HP HBody HK1 HB1 HRL2 HR2 HO1 HOB1 HSubsets1 HLb1 HEG1 BMatrix2
  (BS _ BK)(BS _ Bk)(coding_zero_lt_succ M bound)(BS _ BX)(BS _ Bbeta)(BS _ BLb)HNames1 HBranch)as PBranch.
 pose proof(source_LL_instance_bounded M k X lk bound Bk BX HK)as BLK.
 pose proof(source_membership_block_bound M start X params block bound HNames BX HBlock)as BB.
 pose proof(source_cofinal_ordinals_bounded M K ordinals bound BK HO)as BO.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)beta ob bound(source_ordinal_predicate_bounded M)Bbeta HOB)as BOB.
 assert(BSubsets:source_bounded M subsets bound).
 { apply(source_reflection_geometry_instance_bounded M ReflectionSubsets(source_rec_env2 K beta)subsets bound);[|exact HSubsets].
   intros[|[|i]]HI;cbn in HI;try lia;assumption. }
 pose proof(source_LL_instance_bounded M beta Lb lb bound Bbeta BLb HLb)as BLB.
 pose proof(source_reflection_KF_next_bounded M domain level sb sc count K k next bound HD HL HV BK Bk HNext)as BNext.
 pose proof(source_ew_at_bounded M domain phi' Lb goal bound HD BMatrix BLb HEGoal)as BG.
 apply(source_zfr_finite_telescope_exists M[lk;block;ordinals;ob;subsets;lb][lk1;block1;ord1;ob1;subsets1;lb1]body next goal goal1 branch law bound).
 - intros f[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];assumption.
 - exact BNext.
 - exact BG.
 - constructor;[exact(source_LL_shift_to M k X lk lk1 HK HK1)|].
   constructor;[exact(source_membership_block_shift M start X params block block1 HBlock HB1)|].
   constructor;[exact(source_cofinal_ordinals_shift M K ordinals ord1 HO HO1)|].
   constructor;[exact(source_domain_shift_to M(source_ordinal_predicate_code M)beta ob ob1(source_ordinal_predicate_bounded M)HOB HOB1)|].
   constructor;[exact(source_PH_subsets_shift M K beta subsets subsets1 HSubsets HSubsets1)|].
   constructor;[exact(source_LL_shift_to M beta Lb lb lb1 HLb HLb1)|constructor].
 - exact HEx.
 - exact(source_ew_at_shift M domain phi' phi2 Lb goal goal1 HD HCut HEGoal HEG1).
 - exact HBranch.
 - exact HLaw.
 - exact PBranch.
Qed.
Print Assumptions source_zfr_PH_successor_elimination.
