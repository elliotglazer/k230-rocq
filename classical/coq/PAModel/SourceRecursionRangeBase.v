(** Eliminate the genuine initial-attempt witness to obtain RR-range base membership. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourcePieceBoundMaxJoint
 SourceQuantifierRules SourceDerivedRules SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceRecursionPrimitiveRelations SourceRecursionStructureGraphs SourceRecursionStructureBounds SourceRecursionInitialAttempt SourceRecursionInitialAttemptZFR
 SourceRecursionRangeChart SourceRecursionRangeBaseChosen SourceRecursionAtomicShift SourceRecursionExAAdjoin SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_range_base M phi o a N Y nonzero member chart target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M Y k ->
 source_rec_nonzero M o N nonzero ->sf_relation M SFMember o N member ->source_rec_range_chart M phi o a N Y chart ->sf_relation M SFMember a Y target ->
 source_finite_telescope M[nonzero;member;chart]target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BY HNZ HM HC HTarget HLaw. set(s:=succM M).
 pose proof(source_rec_nonzero_bounded M o N nonzero k BO BN HNZ)as BNZ.
 pose proof(proj2(source_bounded_accept_atom M SFMember o N member k(or_introl eq_refl)HM)(conj BO BN))as BM.
 pose proof(source_rec_range_chart_bounded M phi o a N Y chart k BP BO BA BN BY HC)as BC.
 pose proof(proj2(source_bounded_accept_atom M SFMember a Y target k(or_introl eq_refl)HTarget)(conj BA BY))as BTarget.
 destruct(source_rec_initial_attempt_total M phi o a N)as(initial&HInitial).
 pose proof(source_rec_initial_attempt_bounded M phi o a N initial k BP BO BA BN HInitial)as BInitial.
 destruct(sf_relation_total M SFImpl nonzero initial)as(initialLaw&HInitialLaw).
 pose proof(source_zfr_rec_initial_attempt M phi o a N nonzero initial initialLaw k BP BO BA BN HNZ HInitial HInitialLaw)as PInitialLaw.
 destruct HInitial as(att&app&body&HT&HA&HAnd&HEx).
 destruct(sf_relation_total M SFMember(s o)(s N))as(memberS&HMS).
 destruct(source_rec_range_chart_total M phi(s o)(s a)(s N)(s Y))as(chartS&HCS).
 destruct(sf_relation_total M SFMember(s a)(s Y))as(targetS&HTargetS).
 pose proof(source_rec_member_shift M o N member memberS HM HMS)as SM.
 pose proof(source_rec_range_chart_shift M phi o a N Y chart chartS BP HC HCS)as SC.
 pose proof(source_rec_member_shift M a Y target targetS HTarget HTargetS)as STarget.
 pose proof(source_rec_range_chart_bounded M phi(s o)(s a)(s N)(s Y)chartS(s k)BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HCS)as BCS.
 pose proof(proj2(source_bounded_accept_atom M SFMember(s o)(s N)memberS(s k)(or_introl eq_refl)HMS)
  (conj(proj2(coding_lt_succ_cancel M o k)BO)(proj2(coding_lt_succ_cancel M N k)BN)))as BMS.
 pose proof(proj2(source_bounded_accept_atom M SFMember(s a)(s Y)targetS(s k)(or_introl eq_refl)HTargetS)
  (conj(proj2(coding_lt_succ_cancel M a k)BA)(proj2(coding_lt_succ_cancel M Y k)BY)))as BTargetS.
 pose proof(proj1(source_bounded_accept_unary M SFEx body initial k(or_intror eq_refl)HEx)BInitial)as BBody.
 destruct(source_finite_telescope_total M[memberS;chartS;body]targetS)as(branch&HBranch).
 assert(PBranch:source_zfr_provable M branch).
 { destruct(source_finite_telescope_total M[memberS;chartS;att;app]targetS)as(chosen&HChosen).
   pose proof(source_zfr_rec_range_base_chosen M phi(s o)(s a)(s N)(zeroM M)(s Y)memberS chartS att app targetS chosen(s k)
    BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HMS HCS HT HA HTargetS HChosen)as PChosen.
   apply(source_zfr_finite_rule M[chosen][memberS;chartS;body]targetS branch(s k)).
   - intros x[<-|[<-|[<-|[]]]];assumption.
   - exact BTargetS.
   - exact HBranch.
   - intros x[<-|[]]. exact PChosen.
   - intros cb cc cn BContext Laws Premises.
     destruct(source_full_piece_conjunction_components M cb cc cn att app body HAnd(Premises body ltac:(cbn;tauto)))as[PT PA].
     apply(source_full_finite_telescope_apply M[memberS;chartS;att;app]targetS chosen HChosen cb cc cn).
     + apply Laws. now left.
     + intros x[<-|[<-|[<-|[<-|[]]]]];first[exact PT|exact PA|apply Premises;cbn;tauto]. }
 destruct(source_finite_telescope_total M[member;chart;initial]target)as(exLaw&HExLaw).
 assert(PExLaw:source_zfr_provable M exLaw).
 { apply(source_zfr_finite_telescope_exists M[member;chart][memberS;chartS]body initial target targetS branch exLaw k).
   - intros x[<-|[<-|[]]];assumption.
   - exact BInitial.
   - exact BTarget.
   - repeat(constructor;[assumption|]). constructor.
   - exact HEx.
   - exact STarget.
   - exact HBranch.
   - exact HExLaw.
   - exact PBranch. }
 apply(source_zfr_finite_rule M[initialLaw;exLaw][nonzero;member;chart]target law k).
 - intros x[<-|[<-|[<-|[]]]];assumption.
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[<-|[]]];assumption.
 - intros cb cc cn BContext Laws Premises.
   pose proof(source_full_modus_ponens M cb cc cn nonzero initial initialLaw HInitialLaw(Laws initialLaw(or_introl eq_refl))(Premises nonzero(or_introl eq_refl)))as PI.
   apply(source_full_finite_telescope_apply M[member;chart;initial]target exLaw HExLaw cb cc cn).
   + apply Laws. right. now left.
   + intros x[<-|[<-|[<-|[]]]];first[exact PI|apply Premises;cbn;tauto].
Qed.
Print Assumptions source_zfr_rec_range_base.
