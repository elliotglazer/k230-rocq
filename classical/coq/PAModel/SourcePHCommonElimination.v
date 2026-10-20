(** Actual elimination of both cofinal common-level witnesses. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions Pairing SetFormulaCodes SourceBounded
 NumericalContexts NumericalRenamingMaps NumericalRenaming SourceHierarchySyntax SourceEwMonotone SourceEwAtSyntax SourceEwShift
 SourceMembershipBlocks SourceCommonLevelWitness SourceCofinalCommonPoint SourceCofinalCommonRecipe SourceCofinalCommonWitness
 SourcePieceConjunctionBounds SourceFiniteCutoffShift SourceImplicationAllShift SourcePieceOffsetShift
 SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRProvability SourcePHGeometryFrame SourcePHLevelPoint.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_PH_common_point_frame M domain level sb sc count K k X common beta Lb start
 entry params phi rb rc rn phi' frame goal law bound:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 context_member M sb sc count entry ->pair_graph M params phi entry ->
 source_PH_geometry_frame M domain level sb sc count K beta Lb frame ->source_cofinal_common_point M start params K k X common ->
 renaming_lift M(zeroM M)(zeroM M)(zeroM M)start rb rc rn ->numerical_renaming M phi rb rc rn start phi' ->
 source_ew_at M domain phi' Lb goal ->source_bounded M phi'(succM M bound) ->
 coding_lt M K bound ->coding_lt M k bound ->coding_lt M X bound ->coding_lt M beta bound ->coding_lt M Lb bound ->
 (forall i,coding_lt M i params ->coding_lt M(addM M i start)bound) ->
 source_finite_telescope M(frame++[common])goal law ->source_zfr_provable M law.
Proof.
 intros HD HL HLg HV HE HP(o&ob&subsets&lb&whole&HO&HOB&HS&HLb&HW&->)HC HRL HR HGoal BMatrix BK Bk BX BB BL HNames HLaw.
 exact(source_zfr_PH_common_point M domain level sb sc count K whole k X common beta Lb start
  entry params phi rb rc rn phi' o ob subsets lb goal law bound
  HD HL HLg HV HE HP HW HC HRL HR HO HOB HS HLb HGoal BMatrix BK Bk BX BB BL HNames HLaw).
Qed.
Theorem source_zfr_PH_common_elimination M domain level sb sc count K beta Lb start
 entry params phi rb rc rn phi' frame common goal law bound:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 context_member M sb sc count entry ->pair_graph M params phi entry ->
 source_PH_geometry_frame M domain level sb sc count K beta Lb frame ->source_cofinal_common_recipe M start params K common ->
 renaming_lift M(zeroM M)(zeroM M)(zeroM M)start rb rc rn ->numerical_renaming M phi rb rc rn start phi' ->
 source_ew_at M domain phi' Lb goal ->source_bounded M phi'(succM M bound) ->
 coding_lt M K bound ->coding_lt M beta bound ->coding_lt M Lb bound ->
 (forall i,coding_lt M i params ->coding_lt M(addM M i start)bound) ->
 source_finite_telescope M(frame++[common])goal law ->source_zfr_provable M law.
Proof.
 intros HD HL HLg HV HE HP HFrame HCommon HRL HR HGoal BMatrix BK BB BL HNames HLaw.
 assert(BS:forall x,coding_lt M x bound ->coding_lt M(succM M x)(succM M bound)).
 { intros x HX. exact(proj2(coding_lt_succ_cancel M x bound)HX). }
 assert(BSS:forall x,coding_lt M x bound ->coding_lt M(succM M(succM M x))(succM M(succM M bound))).
 { intros x HX. exact(proj2(coding_lt_succ_cancel M(succM M x)(succM M bound))(BS x HX)). }
 destruct(source_PH_geometry_frame_total M domain level sb sc count(succM M K)(succM M beta)(succM M Lb))as(frame1&HFrame1).
 destruct(source_PH_geometry_frame_total M domain level sb sc count(succM M(succM M K))(succM M(succM M beta))(succM M(succM M Lb)))as(frame2&HFrame2).
 pose proof(source_PH_geometry_frame_shift M domain level sb sc count K beta Lb frame frame1 HD HL HV HFrame HFrame1)as HF1.
 pose proof(source_PH_geometry_frame_shift M domain level sb sc count(succM M K)(succM M beta)(succM M Lb)frame1 frame2 HD HL HV HFrame1 HFrame2)as HF2.
 destruct(source_cutoff_shift_total M 1 phi')as(phi1&HShift1).
 destruct(source_cutoff_shift_total M 1 phi1)as(phi2&HShift2).
 pose proof(source_cutoff_shift_bounded M 1 phi' phi1 bound BMatrix HShift1)as BMatrix1.
 pose proof(source_cutoff_shift_bounded M 1 phi1 phi2(succM M bound)BMatrix1 HShift2)as BMatrix2.
 destruct(renaming_lift_total M(zeroM M)(zeroM M)(zeroM M)(succM M start))as(rb1&rc1&rn1&HRL1).
 destruct(renaming_lift_total M(zeroM M)(zeroM M)(zeroM M)(succM M(succM M start)))as(rb2&rc2&rn2&HRL2).
 pose proof(source_piece_offset_shift M params start phi phi' phi1 rb rc rn rb1 rc1 rn1(HV entry params phi HE HP)HRL HR HShift1 HRL1)as HR1.
 pose proof(source_piece_offset_shift M params(succM M start)phi phi1 phi2 rb1 rc1 rn1 rb2 rc2 rn2(HV entry params phi HE HP)HRL1 HR1 HShift2 HRL2)as HR2.
 destruct(source_ew_at_total M domain phi1(succM M Lb))as(goal1&HGoal1).
 destruct(source_ew_at_total M domain phi2(succM M(succM M Lb)))as(goal2&HGoal2).
 pose proof(source_ew_at_shift M domain phi' phi1 Lb goal goal1 HD HShift1 HGoal HGoal1)as HG1.
 pose proof(source_ew_at_shift M domain phi1 phi2(succM M Lb)goal1 goal2 HD HShift2 HGoal1 HGoal2)as HG2.
 pose proof HCommon as(point&exY&HPoint&HY&HX).
 destruct(source_finite_telescope_total M(frame2++[point])goal2)as(branch&HBranch).
 assert(HNames2:forall i,coding_lt M i params ->coding_lt M(addM M i(succM M(succM M start)))(succM M(succM M bound))).
 { intros i HI. rewrite !source_common_add_successor. exact(BSS _ (HNames i HI)). }
 pose proof(source_zfr_PH_common_point_frame M domain level sb sc count(succM M(succM M K))(code_numeral M 1)(zeroM M)point
  (succM M(succM M beta))(succM M(succM M Lb))(succM M(succM M start))
  entry params phi rb2 rc2 rn2 phi2 frame2 goal2 branch(succM M(succM M bound))
  HD HL HLg HV HE HP HFrame2 HPoint HRL2 HR2 HGoal2 BMatrix2(BSS _ BK)
  (proj2(coding_lt_succ_cancel M(zeroM M)(succM M bound))(coding_zero_lt_succ M bound))
  (coding_zero_lt_succ M(succM M bound))(BSS _ BB)(BSS _ BL)HNames2 HBranch)as PBranch.
 pose proof(source_cofinal_common_recipe_bounded M start params K common bound HNames BK HCommon)as BC.
 pose proof(proj1(source_bounded_accept_unary M SFEx exY common bound(or_intror eq_refl)HX)BC)as BExY.
 pose proof(source_ew_at_bounded M domain phi' Lb goal bound HD BMatrix BL HGoal)as BG.
 pose proof(source_shift_bound M goal goal1 bound BG HG1)as BG1.
 destruct(source_finite_telescope_total M(frame1++[exY])goal1)as(inner&HInner).
 pose proof(source_zfr_finite_telescope_exists M frame1 frame2 point exY goal1 goal2 branch inner(succM M bound)
  (source_PH_geometry_frame_bounded M domain level sb sc count(succM M K)(succM M beta)(succM M Lb)frame1(succM M bound)
   HD HL HV(BS _ BK)(BS _ BB)(BS _ BL)HFrame1)BExY BG1 HF2 HY HG2 HBranch HInner PBranch)as PInner.
 exact(source_zfr_finite_telescope_exists M frame frame1 exY common goal goal1 inner law bound
  (source_PH_geometry_frame_bounded M domain level sb sc count K beta Lb frame bound HD HL HV BK BB BL HFrame)
  BC BG HF1 HX HG1 HInner HLaw PInner).
Qed.
Print Assumptions source_zfr_PH_common_point_frame.
Print Assumptions source_zfr_PH_common_elimination.
