(** Actual ZFR successor preservation of attempt agreement. Both value
    quantifiers and all six ordinary hypotheses are discharged. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionShiftGraphs
 SourceRecursionAgreement SourceRecursionFunctionality SourceRecursionFunctionalityClosed SourceRecursionAtomicShift
 SourceRecursionSuccessorValues SourceFiniteTelescope SourceFiniteTelescopeQuantifier SourceZFRProvability SourceImplicationAllShift SourceQuantifierRules.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_agreement_successor M phi o a N f g z z' funlaw af ag member successor agr next law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->
 coding_lt M z k ->coding_lt M z' k ->source_rec_functionality M phi funlaw ->
 source_rec_attempt M phi o a N f af ->source_rec_attempt M phi o a N g ag ->sf_relation M SFMember z N member ->
 source_rec_successor M z z' successor ->source_rec_agreement M f g z agr ->source_rec_agreement M f g z' next ->
 source_finite_telescope M[funlaw;af;ag;member;successor;agr]next law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BG BZ BZ' HFun HAF HAG HM HS HA HNext HLaw.
 pose proof(source_rec_agreement_bounded M f g z' next k BF BG BZ' HNext)as BNext.
 destruct(source_rec_agreement_shell M f g z' next HNext)as(left&right&equal&rhs&point&inner&HLeft&HRight&HEqual&HRhs&HPoint&HInner&HOuter).
 pose proof(proj1(source_bounded_accept_unary M SFAll inner next k(or_introl eq_refl)HOuter)BNext)as BInner.
 pose proof(proj1(source_bounded_accept_unary M SFAll point inner(succM M k)(or_introl eq_refl)HInner)BInner)as BPoint.
 destruct(source_rec_attempt_total M phi(succM M o)(succM M a)(succM M N)(succM M f))as(af1&HAF1).
 destruct(source_rec_attempt_total M phi(succM M o)(succM M a)(succM M N)(succM M g))as(ag1&HAG1).
 destruct(source_rec_attempt_total M phi(succM M(succM M o))(succM M(succM M a))(succM M(succM M N))(succM M(succM M f)))as(af2&HAF2).
 destruct(source_rec_attempt_total M phi(succM M(succM M o))(succM M(succM M a))(succM M(succM M N))(succM M(succM M g)))as(ag2&HAG2).
 pose proof(source_rec_attempt_shift M phi o a N f af af1 BP HAF HAF1)as SAF1.
 pose proof(source_rec_attempt_shift M phi o a N g ag ag1 BP HAG HAG1)as SAG1.
 pose proof(source_rec_attempt_shift M phi(succM M o)(succM M a)(succM M N)(succM M f)af1 af2 BP HAF1 HAF2)as SAF2.
 pose proof(source_rec_attempt_shift M phi(succM M o)(succM M a)(succM M N)(succM M g)ag1 ag2 BP HAG1 HAG2)as SAG2.
 destruct(sf_relation_total M SFMember(succM M z)(succM M N))as(member1&HM1).
 destruct(sf_relation_total M SFMember(succM M(succM M z))(succM M(succM M N)))as(member2&HM2).
 pose proof(source_rec_member_shift M z N member member1 HM HM1)as SM1.
 pose proof(source_rec_member_shift M(succM M z)(succM M N)member1 member2 HM1 HM2)as SM2.
 destruct(source_rec_successor_total M(succM M z)(succM M z'))as(successor1&HS1).
 destruct(source_rec_successor_total M(succM M(succM M z))(succM M(succM M z')))as(successor2&HS2).
 pose proof(source_rec_successor_shift M z z' successor successor1 HS HS1)as SS1.
 pose proof(source_rec_successor_shift M(succM M z)(succM M z')successor1 successor2 HS1 HS2)as SS2.
 destruct(source_rec_agreement_total M(succM M f)(succM M g)(succM M z))as(agr1&HA1).
 destruct(source_rec_agreement_total M(succM M(succM M f))(succM M(succM M g))(succM M(succM M z)))as(agr2&HA2).
 pose proof(source_rec_agreement_shift M f g z agr agr1 HA HA1)as SA1.
 pose proof(source_rec_agreement_shift M(succM M f)(succM M g)(succM M z)agr1 agr2 HA1 HA2)as SA2.
 pose proof(source_rec_functionality_shift M phi funlaw BP HFun)as SFun.
 set(A0:=[funlaw;af;ag;member;successor;agr]).
 set(A1:=[funlaw;af1;ag1;member1;successor1;agr1]).
 set(A2:=[funlaw;af2;ag2;member2;successor2;agr2]).
 assert(HShift1:Forall2(source_formula_shift M)A0 A1).
 { unfold A0,A1. repeat(constructor;[assumption|]). constructor. }
 assert(HShift2:Forall2(source_formula_shift M)A1 A2).
 { unfold A1,A2. repeat(constructor;[assumption|]). constructor. }
 assert(BAF:source_bounded M af k)by exact(source_rec_attempt_bounded M phi o a N f af k BP BO BA BN BF HAF).
 assert(BAG:source_bounded M ag k)by exact(source_rec_attempt_bounded M phi o a N g ag k BP BO BA BN BG HAG).
 assert(BFun:source_bounded M funlaw k)by exact(source_bounded_monotone M funlaw(zeroM M)k
  (source_rec_functionality_closed M phi funlaw BP HFun)(coding_zero_lt_succ M k)).
 assert(BM:source_bounded M member k)by exact(proj2(source_bounded_accept_atom M SFMember z N member k(or_introl eq_refl)HM)(conj BZ BN)).
 assert(BS:source_bounded M successor k)by exact(source_rec_successor_bounded M z z' successor k BZ BZ' HS).
 assert(BAgr:source_bounded M agr k)by exact(source_rec_agreement_bounded M f g z agr k BF BG BZ HA).
 assert(Bounds0:forall x,In x A0 ->source_bounded M x k).
 { intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];assumption. }
 assert(Bounds1:forall x,In x A1 ->source_bounded M x(succM M k)).
 { intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
   - exact(source_shift_bound M funlaw funlaw k BFun SFun).
   - exact(source_shift_bound M af af1 k BAF SAF1).
   - exact(source_shift_bound M ag ag1 k BAG SAG1).
   - exact(source_shift_bound M member member1 k BM SM1).
   - exact(source_shift_bound M successor successor1 k BS SS1).
   - exact(source_shift_bound M agr agr1 k BAgr SA1). }
 destruct(source_finite_telescope_total M A2 point)as(pointLaw&HPointLaw).
 assert(HValueLaw:source_finite_telescope M[funlaw;af2;ag2;member2;successor2;agr2;left;right]equal pointLaw).
 { apply(source_finite_telescope_prefix M A2[left;right]point equal pointLaw HPointLaw).
   exists rhs. split;[exists equal;split;[reflexivity|exact HRhs]|exact HPoint]. }
 pose proof(source_zfr_rec_successor_values M phi(succM M(succM M o))(succM M(succM M a))(succM M(succM M N))
  (succM M(succM M f))(succM M(succM M g))(succM M(succM M z))(succM M(succM M z'))(code_numeral M 1)(zeroM M)
  funlaw af2 ag2 member2 successor2 agr2 left right equal pointLaw(succM M(succM M k))
  BP (proj2(coding_lt_succ_cancel M(succM M o)(succM M k))(proj2(coding_lt_succ_cancel M o k)BO)) (proj2(coding_lt_succ_cancel M(succM M a)(succM M k))(proj2(coding_lt_succ_cancel M a k)BA)) (proj2(coding_lt_succ_cancel M(succM M N)(succM M k))(proj2(coding_lt_succ_cancel M N k)BN)) (proj2(coding_lt_succ_cancel M(succM M f)(succM M k))(proj2(coding_lt_succ_cancel M f k)BF)) (proj2(coding_lt_succ_cancel M(succM M g)(succM M k))(proj2(coding_lt_succ_cancel M g k)BG)) (proj2(coding_lt_succ_cancel M(succM M z)(succM M k))(proj2(coding_lt_succ_cancel M z k)BZ)) (proj2(coding_lt_succ_cancel M(succM M z')(succM M k))(proj2(coding_lt_succ_cancel M z' k)BZ')) (proj2(coding_lt_succ_cancel M(zeroM M)(succM M k))(coding_zero_lt_succ M k)) (coding_zero_lt_succ M(succM M k)) HFun HAF2 HAG2 HM2 HS2 HA2 HLeft HRight HEqual HValueLaw)as PPointLaw.
 destruct(source_finite_telescope_total M A1 inner)as(innerLaw&HInnerLaw).
 pose proof(source_zfr_finite_telescope_all M A1 A2 point inner pointLaw innerLaw(succM M k)
  Bounds1 BPoint HShift2 HInner HPointLaw HInnerLaw PPointLaw)as PInnerLaw.
 exact(source_zfr_finite_telescope_all M A0 A1 inner next innerLaw law k Bounds0 BInner HShift1 HOuter HInnerLaw HLaw PInnerLaw).
Qed.
Print Assumptions source_zfr_rec_agreement_successor.
