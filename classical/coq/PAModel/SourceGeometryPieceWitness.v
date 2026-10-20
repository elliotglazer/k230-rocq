(** Genuine witness closure from the actual geometry payload and a supplied
    hierarchy. Every PH witness, name bound and parameter binder is discharged. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions Pairing SetFormulaCodes
  SourceBounded SourceBoundMonotone NumericalContexts NumericalRenaming SourceFiniteFamilyBounds
  SourcePieceConjunctionBounds SourceHierarchySyntax SourceCofinalGeometry SourceReflectionGeometryPoint
  SourceReflectionGeometryRenaming SourceReflectionGeometryPredicates SourceRecursionPrimitiveRelations
  SourceOrdinalPredicate NumericalInstantiation SourcePieceWitnessInstance SourcePieceWitnessFromPoint
  SourceMembershipBlocks SourceMembershipBlockProofs SourceEwAtSyntax SourceEwMonotone
  SourceFiniteTelescope SourcePHInitial SourcePHGeometryPayload SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_zfr_geometry_piece_witness M domain level sb sc count seed K beta Y payload lb
    entry params phi wh law:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_piece_table_valid M sb sc count ->
  context_member M sb sc count entry ->pair_graph M params phi entry ->
  source_reflection_geometry_point M domain level sb sc count seed K beta payload ->
  source_LL_instance M beta Y lb ->source_piece_witness_instance M domain params phi Y wh ->
  source_finite_telescope M[payload;lb]wh law ->source_zfr_provable M law.
Proof.
  intros HD HL HLg HV HE HP HGeometry HLevel HWh HLaw.
  pose proof(HV entry params phi HE HP)as BPhi.
  destruct(source_finite_names_bound M[seed;K;beta;Y])as(k&BN).
  assert(BSeed:coding_lt M seed k)by(apply BN;cbn;tauto).
  assert(BK:coding_lt M K k)by(apply BN;cbn;tauto).
  assert(BBeta:coding_lt M beta k)by(apply BN;cbn;tauto).
  assert(BY:coding_lt M Y k)by(apply BN;cbn;tauto).
  pose proof(source_reflection_geometry_point_bounded M domain level sb sc count seed K beta payload k HD HL HV BSeed BK BBeta HGeometry)as BPayload.
  pose proof(source_LL_instance_bounded M beta Y lb k BBeta BY HLevel)as BLb.
  set(seedS:=addM M seed params). set(KS:=addM M K params).
  set(betaS:=addM M beta params). set(YS:=addM M Y params).
  destruct(source_reflection_geometry_point_total M domain level sb sc count seedS KS betaS)as(payloadS&HGeometryS).
  pose proof(source_reflection_geometry_point_shift_by M domain level sb sc count seed K beta payload params payloadS
    HD HL HV HGeometry HGeometryS)as SGeometry.
  destruct(source_LL_instance_total M betaS YS)as(lbS&HLevelS).
  pose proof(source_LL_instance_shift_by M beta Y lb params lbS HLevel HLevelS)as SLevel.
  destruct(source_ew_at_total M domain phi YS)as(ew&HEw).
  destruct(source_membership_block_total M(zeroM M)YS params)as(block&HBlock).
  destruct(source_finite_names_bound M[seedS;KS;betaS;YS;params])as(wide&BNS).
  assert(BSeedS:coding_lt M seedS wide)by(apply BNS;cbn;tauto).
  assert(BKS:coding_lt M KS wide)by(apply BNS;cbn;tauto).
  assert(BBetaS:coding_lt M betaS wide)by(apply BNS;cbn;tauto).
  assert(BYS:coding_lt M YS wide)by(apply BNS;cbn;tauto).
  assert(BParams:coding_lt M params wide)by(apply BNS;cbn;tauto).
  assert(BMatrix:source_bounded M phi(succM M wide)).
  { apply(source_bounded_monotone M phi(succM M params)(succM M wide)BPhi).
    apply(proj2(coding_lt_succ_cancel M params(succM M wide))).
    apply(proj2(coding_lt_succ_cases M params wide)). now left. }
  pose proof(source_reflection_geometry_point_bounded M domain level sb sc count seedS KS betaS payloadS wide
    HD HL HV BSeedS BKS BBetaS HGeometryS)as BPayloadS.
  pose proof(source_LL_instance_bounded M betaS YS lbS wide BBetaS BYS HLevelS)as BLbS.
  assert(BBlock:source_bounded M block wide).
  { apply(source_membership_block_bound M(zeroM M)YS params block wide);[|exact BYS|exact HBlock].
    intros i HI. rewrite coding_add_zero_r. exact(coding_lt_trans M i params wide HI BParams). }
  pose proof(source_ew_at_bounded M domain phi YS ew wide HD BMatrix BYS HEw)as BEw.
  pose proof HGeometryS as(member&ordinals&kf&union&ob&limit&memberBeta&subsets&HM&HO&HKF&HU&HOB&HLimit&HMemberBeta&HSubsets&HGraph).
  destruct(source_cofinal_cover_total M KS YS)as(cover&HCover).
  destruct(source_finite_telescope_total M[member;ordinals;cover;ob;subsets;lbS;kf;block]ew)as(pointLaw&HPoint).
  pose proof(source_zfr_PH_initial M domain level sb sc count KS betaS YS seedS
    entry params phi member ordinals cover ob subsets lbS kf block ew pointLaw
    HD HL HLg HV HE HP HM HO HCover HOB HSubsets HLevelS HKF HBlock HEw HPoint)as PPoint.
  destruct(source_finite_telescope_total M[payloadS;lbS;block]ew)as(shortLaw&HShort).
  pose proof(source_zfr_PH_geometry_payload M KS betaS YS member ordinals kf union ob limit memberBeta subsets
    payloadS lbS cover block ew pointLaw shortLaw wide HO HU HLimit HLevelS HCover HGraph
    BPayloadS BLbS BBlock BEw HPoint HShort PPoint)as PShort.
  assert(HShift:Forall2(fun a shifted=>numerical_renaming M a(zeroM M)(zeroM M)(zeroM M)params shifted)
    [payload;lb][payloadS;lbS]).
  { constructor;[exact SGeometry|]. constructor;[exact SLevel|constructor]. }
  apply(source_zfr_piece_witness_from_point M domain params phi Y wh ew block
    [payload;lb][payloadS;lbS]shortLaw law k HD BPhi BY HWh).
  - unfold YS in HEw. now rewrite(Arithmetic.add_comm M params Y).
  - unfold YS in HBlock. now rewrite(Arithmetic.add_comm M params Y).
  - exact HShift.
  - intros a[EA|[EA|[]]];subst a;assumption.
  - exact HShort.
  - exact HLaw.
  - exact PShort.
Qed.

Print Assumptions source_zfr_geometry_piece_witness.
