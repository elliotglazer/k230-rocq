(** Actual ZFR theorem for the chosen-level PH branch. The antecedents
    are ordinary first-order formulas, including the real membership block. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions Pairing SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
 SourceHierarchySyntax SourcePieceConjunctionBounds SourceEwMonotone SourceEwAtSyntax SourceRawSubset SourceRawSubsetBounds
 SourceMembershipBlocks SourceMembershipBlockProofs SourceBallSMembershipBlock SourceFiniteTelescope SourceZFRFiniteRule
 SourceZFRProvability SourcePieceOffsetMatrix SourceReflectionKFWitness SourceReflectionChosenWitness.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_PH_chosen_point M domain level sb sc count K k w witness X lk Y lw Lb subset goal
 entry params phi start rb rc rn phi' block law bound:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
 source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
 context_member M sb sc count entry ->pair_graph M params phi entry ->
 source_reflection_KF_witness M domain level sb sc count K k w witness ->
 source_LL_instance M k X lk ->source_LL_instance M w Y lw ->source_raw_subset_graph M Y Lb subset ->
 source_membership_block M start X params block ->
 renaming_lift M(zeroM M)(zeroM M)(zeroM M)start rb rc rn ->numerical_renaming M phi rb rc rn start phi' ->
 source_ew_at M domain phi' Lb goal ->source_bounded M phi'(succM M bound) ->
 coding_lt M K bound ->coding_lt M k bound ->coding_lt M w bound ->coding_lt M X bound ->
 coding_lt M Y bound ->coding_lt M Lb bound ->
 (forall i,coding_lt M i params ->coding_lt M(addM M i start)bound) ->
 source_finite_telescope M[witness;lk;lw;subset;block]goal law ->source_zfr_provable M law.
Proof.
 intros HD HL HLg HV HE HP HW HLevelK HLevelW HSubset HBlock HRL HR HEGoal BMatrix
  BK Bk BW BX BY BLb HNames HLaw.
 pose proof(source_reflection_KF_witness_bounded M domain level sb sc count K k w witness bound HD HL HV BK Bk BW HW)as BWit.
 pose proof(source_LL_instance_bounded M k X lk bound Bk BX HLevelK)as BLK.
 pose proof(source_LL_instance_bounded M w Y lw bound BW BY HLevelW)as BLW.
 pose proof(source_raw_subset_bounded M Y Lb subset bound BY BLb HSubset)as BS.
 pose proof(source_membership_block_bound M start X params block bound HNames BX HBlock)as BB.
 pose proof(source_ew_at_bounded M domain phi' Lb goal bound HD BMatrix BLb HEGoal)as BG.
 destruct(balls_offset_assignment_total M start params)as(pb&pC&HOffset).
 destruct(substitution_lift_total M pb pC params(zeroM M))as(ub&uc&un&HU).
 pose proof(source_piece_offset_matrix M params start pb pC ub uc un rb rc rn phi phi'(HV entry params phi HE HP)HOffset HU HRL HR)as HMatrix.
 apply(source_zfr_finite_rule M[][witness;lk;lw;subset;block]goal law bound).
 - intros f[<-|[<-|[<-|[<-|[<-|[]]]]]];assumption.
 - exact BG.
 - exact HLaw.
 - intros f HF;contradiction.
 - intros gb gc gn HC Laws Premises.
   apply(source_full_reflection_chosen_witness M domain level sb sc count K k w witness X lk Y lw Lb subset goal
    entry params phi pb pC ub uc un phi' gb gc gn bound HD HL HLg HV HE HP HW HLevelK HLevelW HSubset HU HMatrix);
    try assumption;try(apply Premises;cbn;tauto).
   intros i value member HI HV0 HMember. pose proof(proj1(HOffset i value HI)HV0)as E. subst value.
   exact(source_full_membership_block_project M start X params block gb gc gn bound i member HNames BX HBlock HC
    (Premises block ltac:(cbn;tauto))HI HMember).
Qed.
Print Assumptions source_zfr_PH_chosen_point.
