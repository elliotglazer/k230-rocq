(** Eliminate the ordinary hierarchy/subset carrier witness in PH.
    All five chosen-level antecedents are supplied by actual source proofs. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions Pairing NumericalProofs SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull NumericalRenamingMaps NumericalRenaming SourceQuantifierRules SourceImplicationAllShift
 SourceHierarchySyntax SourceHierarchyShifts SourceEwMonotone SourceEwAtSyntax SourceEwShift SourceFiniteCutoffShift
 SourceRawSubset SourceRawSubsetBounds SourceMembershipBlocks SourceMembershipBlockProofs SourceCommonLevelWitness
 SourcePieceConjunctionBounds SourceReflectionKFWitness SourceReflectionKFWitnessTransport
 SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule SourceZFRProvability SourceConjunctionRules
 SourcePieceOffsetShift SourcePHChosenPoint.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_PH_hierarchy_elimination M domain level sb sc count K k w witness X lk Lb start
 entry params phi rb rc rn phi' block lw included body ex goal law bound:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 context_member M sb sc count entry ->pair_graph M params phi entry ->
 source_reflection_KF_witness M domain level sb sc count K k w witness ->source_LL_instance M k X lk ->
 source_membership_block M start X params block ->
 renaming_lift M(zeroM M)(zeroM M)(zeroM M)start rb rc rn ->numerical_renaming M phi rb rc rn start phi' ->
 source_LL_instance M(succM M w)(zeroM M)lw ->source_raw_subset_graph M(zeroM M)(succM M Lb)included ->
 sf_relation M SFAnd lw included body ->sf_relation M SFEx body(zeroM M)ex ->
 source_ew_at M domain phi' Lb goal ->source_bounded M phi'(succM M bound) ->
 coding_lt M K bound ->coding_lt M k bound ->coding_lt M w bound ->coding_lt M X bound ->coding_lt M Lb bound ->
 (forall i,coding_lt M i params ->coding_lt M(addM M i start)bound) ->
 source_finite_telescope M[witness;lk;block;ex]goal law ->source_zfr_provable M law.
Proof.
 intros HD HL HLg HV HE HP HW HK HBlock HRL HR HY HIncluded HBody HEx HEGoal BMatrix
  BK Bk BW BX BLb HNames HLaw.
 assert(BS:forall x,coding_lt M x bound ->coding_lt M(succM M x)(succM M bound)).
 { intros x HX. exact(proj2(coding_lt_succ_cancel M x bound)HX). }
 destruct(source_cutoff_shift_total M 1 phi')as(phi2&HCut).
 pose proof(source_cutoff_shift_bounded M 1 phi' phi2 bound BMatrix HCut)as BMatrix2.
 destruct(renaming_lift_total M(zeroM M)(zeroM M)(zeroM M)(succM M start))as(rb2&rc2&rn2&HRL2).
 pose proof(source_piece_offset_shift M params start phi phi' phi2 rb rc rn rb2 rc2 rn2(HV entry params phi HE HP)HRL HR HCut HRL2)as HR2.
 destruct(source_reflection_KF_witness_total M domain level sb sc count(succM M K)(succM M k)(succM M w))as(wit1&HW1).
 destruct(source_LL_instance_total M(succM M k)(succM M X))as(lk1&HK1).
 destruct(source_membership_block_total M(succM M start)(succM M X)params)as(block1&HB1).
 destruct(source_ew_at_total M domain phi2(succM M Lb))as(goal1&HEG1).
 assert(HNames1:forall i,coding_lt M i params ->coding_lt M(addM M i(succM M start))(succM M bound)).
 { intros i HI. rewrite source_common_add_successor. exact(BS _ (HNames i HI)). }
 destruct(source_finite_telescope_total M[wit1;lk1;lw;included;block1]goal1)as(pointLaw&HPointLaw).
 pose proof(source_zfr_PH_chosen_point M domain level sb sc count(succM M K)(succM M k)(succM M w)wit1
  (succM M X)lk1(zeroM M)lw(succM M Lb)included goal1 entry params phi(succM M start)rb2 rc2 rn2 phi2 block1 pointLaw(succM M bound)
  HD HL HLg HV HE HP HW1 HK1 HY HIncluded HB1 HRL2 HR2 HEG1 BMatrix2(BS _ BK)(BS _ Bk)(BS _ BW)(BS _ BX)
  (coding_zero_lt_succ M bound)(BS _ BLb)HNames1 HPointLaw)as PPoint.
 pose proof(source_reflection_KF_witness_bounded M domain level sb sc count K k w witness bound HD HL HV BK Bk BW HW)as BWit.
 pose proof(source_LL_instance_bounded M k X lk bound Bk BX HK)as BLK.
 pose proof(source_membership_block_bound M start X params block bound HNames BX HBlock)as BB.
 pose proof(source_ew_at_bounded M domain phi' Lb goal bound HD BMatrix BLb HEGoal)as BG.
 pose proof(source_reflection_KF_witness_shift M domain level sb sc count K k w witness wit1 HD HL HV HW HW1)as SW.
 pose proof(source_LL_shift_to M k X lk lk1 HK HK1)as SK.
 pose proof(source_membership_block_shift M start X params block block1 HBlock HB1)as SB.
 pose proof(source_ew_at_shift M domain phi' phi2 Lb goal goal1 HD HCut HEGoal HEG1)as SG.
 pose proof(source_LL_instance_bounded M(succM M w)(zeroM M)lw(succM M bound)(BS _ BW)(coding_zero_lt_succ M bound)HY)as BLY.
 pose proof(source_raw_subset_bounded M(zeroM M)(succM M Lb)included(succM M bound)(coding_zero_lt_succ M bound)(BS _ BLb)HIncluded)as BI.
 pose proof(proj2(source_bounded_accept_binary M SFAnd lw included body(succM M bound)(or_introl eq_refl)HBody)(conj BLY BI))as BBody.
 pose proof(proj2(source_bounded_accept_unary M SFEx body ex bound(or_intror eq_refl)HEx)BBody)as BEx.
 destruct(source_finite_telescope_total M[wit1;lk1;block1;body]goal1)as(branch&HBranch).
 assert(PBranch:source_zfr_provable M branch).
 { apply(source_zfr_finite_rule M[pointLaw][wit1;lk1;block1;body]goal1 branch(succM M bound)).
   - intros f[<-|[<-|[<-|[<-|[]]]]].
     + exact(source_shift_bound M witness wit1 bound BWit SW).
     + exact(source_shift_bound M lk lk1 bound BLK SK).
     + exact(source_shift_bound M block block1 bound BB SB).
     + exact BBody.
   - exact(source_shift_bound M goal goal1 bound BG SG).
   - exact HBranch.
   - intros f[<-|[]]. exact PPoint.
   - intros gb gc gn HC Laws Premises.
     pose proof(Premises body ltac:(cbn;tauto))as PB.
     apply(source_full_finite_telescope_apply M[wit1;lk1;lw;included;block1]goal1 pointLaw HPointLaw gb gc gn
       (Laws pointLaw ltac:(cbn;tauto))).
     intros f[<-|[<-|[<-|[<-|[<-|[]]]]]];try(apply Premises;cbn;tauto).
     + exact(source_full_conjunction_left M gb gc gn lw included body HBody PB).
     + exact(source_full_conjunction_right M gb gc gn lw included body HBody PB). }
 apply(source_zfr_finite_telescope_exists M[witness;lk;block][wit1;lk1;block1]body ex goal goal1 branch law bound).
 - intros f[<-|[<-|[<-|[]]]];assumption.
 - exact BEx.
 - exact BG.
 - constructor;[exact SW|]. constructor;[exact SK|]. constructor;[exact SB|constructor].
 - exact HEx.
 - exact SG.
 - exact HBranch.
 - exact HLaw.
 - exact PBranch.
Qed.
Print Assumptions source_zfr_PH_hierarchy_elimination.
