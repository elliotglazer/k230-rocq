(** Actual successor ExE drops only the PCf conjunct from KF. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull SourceConjunctionRules SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourcePieceConjunctionBounds SourceReflectionKFNext SourceReflectionKFWitness SourceReflectionNoLastNext SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_reflection_KF_next_no_last M domain level sb sc count K x old target law k:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 coding_lt M K k ->coding_lt M x k ->source_reflection_KF_next M domain level sb sc count K x old ->source_reflection_no_last_next M K x target ->
 source_finite_telescope M[old]target law ->source_zfr_provable M law.
Proof.
 intros HD HL HV BK BX HO HT HLaw.
 pose proof(source_reflection_KF_next_bounded M domain level sb sc count K x old k HD HL HV BK BX HO)as BO.
 pose proof(source_reflection_no_last_next_bounded M K x target k BK BX HT)as BT.
 destruct HO as(body&HB&HEx).
 destruct(source_reflection_no_last_next_total M(succM M K)(succM M x))as(targetS&HTS).
 pose proof(source_reflection_no_last_next_shift M K x target targetS HT HTS)as STarget.
 pose proof(source_reflection_KF_witness_bounded M domain level sb sc count(succM M K)(succM M x)(zeroM M)body(succM M k)
  HD HL HV(proj2(coding_lt_succ_cancel M K k)BK)(proj2(coding_lt_succ_cancel M x k)BX)(coding_zero_lt_succ M k)HB)as BB.
 pose proof(source_reflection_no_last_next_bounded M(succM M K)(succM M x)targetS(succM M k)
  (proj2(coding_lt_succ_cancel M K k)BK)(proj2(coding_lt_succ_cancel M x k)BX)HTS)as BTS.
 destruct(source_finite_telescope_total M[body]targetS)as(branch&HBranch).
 assert(PBranch:source_zfr_provable M branch).
 { apply(source_zfr_finite_rule M[][body]targetS branch(succM M k)).
   - intros f[<-|[]]. exact BB.
   - exact BTS.
   - exact HBranch.
   - intros f HF. contradiction.
   - intros b c n BC Laws Premises.
     destruct HB as(member&next&lev&pc&point&all&inner&HM&HN&HLev&HPC&HP&HA&HI&HF).
     pose proof(Premises body(or_introl eq_refl))as PBody.
     pose proof(source_full_conjunction_left M b c n member inner body HF PBody)as PM.
     pose proof(source_full_conjunction_right M b c n member inner body HF PBody)as PI.
     pose proof(source_full_conjunction_left M b c n next all inner HI PI)as PN.
     exact(source_full_reflection_no_last_next_intro M b c n(succM M K)(succM M x)(zeroM M)member next targetS(succM M k)
      (proj2(coding_lt_succ_cancel M K k)BK)(proj2(coding_lt_succ_cancel M x k)BX)BC HM HN HTS PM PN). }
 exact(source_zfr_finite_telescope_exists M[][]body old target targetS branch law k
  ltac:(intros f HF;contradiction)BO BT ltac:(constructor)HEx STarget HBranch HLaw PBranch).
Qed.
Print Assumptions source_zfr_reflection_KF_next_no_last.
