(** Actual guarded universal projection from KF to the no-last K-family law. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceFiniteTelescope SourceFiniteTelescopeQuantifier SourceZFRFiniteRule NumericalContexts NumericalSourceFull
 SourcePieceConjunctionBounds SourceReflectionGeometryPredicates SourceReflectionNoLastShell SourceReflectionNoLastNext
 SourceReflectionKF SourceReflectionKFNext SourceReflectionKFTransport SourceReflectionKFUse SourceReflectionKFNextNoLast SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_reflection_KF_no_last M domain level sb sc count K old target law k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->coding_lt M K k ->
 source_reflection_KF M domain level sb sc count K old ->source_reflection_geometry_instance M ReflectionNoLast(fun _=>K)target ->
 source_finite_telescope M[old]target law ->source_zfr_provable M law.
Proof.
 intros HD HL HV BK HO HT HLaw.
 pose proof(source_reflection_KF_bounded M domain level sb sc count K old k HD HL HV BK HO)as BO.
 pose proof(source_reflection_geometry_instance_bounded M ReflectionNoLast(fun _=>K)target k ltac:(intros i HI;exact BK)HT)as BT.
 destruct(source_reflection_no_last_shell M K target HT)as(guard&next&point&HG&HN&HP&HAll).
 pose proof(proj1(source_bounded_accept_unary M SFAll point target k(or_introl eq_refl)HAll)BT)as BPoint.
 destruct(source_reflection_KF_total M domain level sb sc count(succM M K))as(oldS&HOS).
 pose proof(source_reflection_KF_shift M domain level sb sc count K old oldS HD HL HV HO HOS)as HS.
 destruct(source_finite_telescope_total M[oldS]point)as(branch&HBranch).
 assert(HBranchTel:source_finite_telescope M[oldS;guard]next branch).
 { apply(source_finite_telescope_prefix M[oldS][guard]point next branch HBranch). exists next. split;[reflexivity|exact HP]. }
 destruct(source_reflection_KF_next_total M domain level sb sc count(succM M K)(zeroM M))as(complex&HC).
 destruct(source_finite_telescope_total M[complex]next)as(projection&HProjection).
 pose proof(source_zfr_reflection_KF_next_no_last M domain level sb sc count(succM M K)(zeroM M)complex next projection(succM M k)
  HD HL HV(proj2(coding_lt_succ_cancel M K k)BK)(coding_zero_lt_succ M k)HC HN HProjection)as PProjection.
 pose proof(source_reflection_KF_bounded M domain level sb sc count(succM M K)oldS(succM M k)HD HL HV(proj2(coding_lt_succ_cancel M K k)BK)HOS)as BOS.
 pose proof(proj2(source_bounded_accept_atom M SFMember _ _ guard(succM M k)(or_introl eq_refl)HG)
  (conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M K k)BK)))as BG.
 pose proof(source_reflection_no_last_next_bounded M(succM M K)(zeroM M)next(succM M k)(proj2(coding_lt_succ_cancel M K k)BK)(coding_zero_lt_succ M k)HN)as BN.
 assert(PBranch:source_zfr_provable M branch).
 { apply(source_zfr_finite_rule M[projection][oldS;guard]next branch(succM M k)).
   - intros f[<-|[<-|[]]];assumption.
   - exact BN.
   - exact HBranchTel.
   - intros f[<-|[]]. exact PProjection.
   - intros b c n BC Laws Premises.
     pose proof(source_full_reflection_KF_use M domain level sb sc count(succM M K)(zeroM M)oldS guard complex b c n
      HD HL HV HOS HG HC(Premises oldS(or_introl eq_refl))(Premises guard(or_intror(or_introl eq_refl))))as PC.
     apply(source_full_finite_telescope_apply M[complex]next projection HProjection b c n(Laws projection(or_introl eq_refl))).
     intros f[<-|[]]. exact PC. }
 exact(source_zfr_finite_telescope_all M[old][oldS]point target branch law k
  ltac:(intros f[<-|[]];exact BO)BPoint ltac:(constructor;[exact HS|constructor])HAll HBranch HLaw PBranch).
Qed.
Print Assumptions source_zfr_reflection_KF_no_last.
