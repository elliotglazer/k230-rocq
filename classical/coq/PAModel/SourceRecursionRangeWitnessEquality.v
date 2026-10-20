(** Both attempt witnesses in RR value equality are eliminated in the source calculus. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 NumericalContexts NumericalSourceFull SourcePieceBoundMaxJoint SourceQuantifierRules
 SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceRecursionPrimitiveRelations SourceRecursionAttemptApp SourceRecursionFunctionality SourceRecursionFunctionalityClosed
 SourceRecursionInductionGraphs SourceRecursionInductionBounds SourceRecursionInductionShift SourceRecursionInductionTransport
 SourceRecursionExtensionInputShift SourceRecursionAtomicShift SourceRecursionEqualShift SourceRecursionRangeOneWitness SourceRecursionExAAdjoin SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_range_witness_equality M phi o a N z v w funlaw totality induction member mz left right equal law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M z k ->coding_lt M v k ->coding_lt M w k ->
 source_rec_functionality M phi funlaw ->source_rec_totality M N totality ->source_rec_induction M o N induction ->sf_relation M SFMember o N member ->
 sf_relation M SFMember z N mz ->source_rec_attempt_app M phi z v o a N left ->source_rec_attempt_app M phi z w o a N right ->sf_relation M SFEqual v w equal ->
 source_finite_telescope M[funlaw;totality;induction;member;mz;right;left]equal law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BZ BV BW HFun HT HI HM HMZ HLeft HRight HE HLaw. set(s:=succM M).
 set(A:=[funlaw;totality;induction;member;mz;right]).
 pose proof(source_rec_totality_bounded M N totality k BN HT)as BT.
 pose proof(source_rec_induction_bounded M o N induction k BO BN HI)as BI.
 pose proof(source_bounded_monotone M funlaw(zeroM M)k(source_rec_functionality_closed M phi funlaw BP HFun)(coding_zero_lt_succ M k))as BFun.
 pose proof(proj2(source_bounded_accept_atom M SFMember o N member k(or_introl eq_refl)HM)(conj BO BN))as BM.
 pose proof(proj2(source_bounded_accept_atom M SFMember z N mz k(or_introl eq_refl)HMZ)(conj BZ BN))as BMZ.
 pose proof(source_rec_attempt_app_bounded M phi z v o a N left k BP BZ BV BO BA BN HLeft)as BLeft.
 pose proof(source_rec_attempt_app_bounded M phi z w o a N right k BP BZ BW BO BA BN HRight)as BRight.
 pose proof(proj2(source_bounded_accept_atom M SFEqual v w equal k(or_intror eq_refl)HE)(conj BV BW))as BE.
 assert(Bounds:forall x,In x A ->source_bounded M x k)by(intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];assumption).
 destruct HLeft as(af&appf&body&HAF&HAppF&HBody&HEx).
 destruct(source_rec_totality_total M(s N))as(totalityS&HTS).
 destruct(source_rec_induction_total M(s o)(s N))as(inductionS&HIS).
 destruct(sf_relation_total M SFMember(s o)(s N))as(memberS&HMS).
 destruct(sf_relation_total M SFMember(s z)(s N))as(mzS&HMZS).
 destruct(source_rec_attempt_app_total M phi(s z)(s w)(s o)(s a)(s N))as(rightS&HRightS).
 destruct(sf_relation_total M SFEqual(s v)(s w))as(equalS&HES).
 set(AS:=[funlaw;totalityS;inductionS;memberS;mzS;rightS]).
 assert(HShift:Forall2(source_formula_shift M)A AS).
 { constructor;[exact(source_rec_functionality_shift M phi funlaw BP HFun)|].
   constructor;[exact(source_rec_totality_shift M N totality totalityS HT HTS)|].
   constructor;[exact(source_rec_induction_shift M o N induction inductionS HI HIS)|].
   constructor;[exact(source_rec_member_shift M o N member memberS HM HMS)|].
   constructor;[exact(source_rec_member_shift M z N mz mzS HMZ HMZS)|].
   constructor;[exact(source_rec_attempt_app_shift M phi z w o a N right rightS BP HRight HRightS)|constructor]. }
 pose proof(source_rec_equal_shift M v w equal equalS HE HES)as SE.
 pose proof(proj1(source_bounded_accept_unary M SFEx body left k(or_intror eq_refl)HEx)BLeft)as BBody.
 pose proof(proj2(source_bounded_accept_atom M SFEqual(s v)(s w)equalS(s k)(or_intror eq_refl)HES)
  (conj(proj2(coding_lt_succ_cancel M v k)BV)(proj2(coding_lt_succ_cancel M w k)BW)))as BES.
 destruct(source_finite_telescope_total M(AS++[body])equalS)as(deep&HDeep).
 assert(PDeep:source_zfr_provable M deep).
 { destruct(source_finite_telescope_total M[funlaw;af;totalityS;inductionS;memberS;mzS;appf;rightS]equalS)as(point&HPoint).
   pose proof(source_zfr_rec_range_one_witness M phi(s o)(s a)(s N)(zeroM M)(s z)(s v)(s w)
    funlaw af totalityS inductionS memberS mzS appf rightS equalS point(s k)BP
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)
    HFun HAF HTS HIS HMS HMZS HAppF HRightS HES HPoint)as PPoint.
   apply(source_zfr_finite_rule M[point](AS++[body])equalS deep(s k));[|exact BES|exact HDeep| |].
   - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(source_finite_shifted_bounds M A AS k HShift Bounds x HX)|exact BBody].
   - intros x[<-|[]]. exact PPoint.
   - intros cb cc cn BC Laws Premises.
     assert(PBody:source_full_prv M cb cc cn body)by(apply Premises,in_or_app;right;now left).
     destruct(source_full_piece_conjunction_components M cb cc cn af appf body HBody PBody)as[PAF PAppF].
     apply(source_full_finite_telescope_apply M[funlaw;af;totalityS;inductionS;memberS;mzS;appf;rightS]equalS point HPoint cb cc cn).
     + apply Laws. now left.
     + intros x[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];first[exact PAF|exact PAppF|apply Premises,in_or_app;left;unfold AS;cbn;tauto]. }
 exact(source_zfr_finite_telescope_exists M A AS body left equal equalS deep law k Bounds BLeft BE HShift HEx SE HDeep HLaw PDeep).
Qed.
Print Assumptions source_zfr_rec_range_witness_equality.
