(** The successor value argument, with both predecessor existentials
    already eliminated by an actual ZFR certificate. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts SourceTraceBounds NumericalSourceFull SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds
 SourceRecursionAttemptStep SourceRecursionAttemptStepShell SourceRecursionValuePairs SourceRecursionAgreement
 SourceRecursionFunctionality SourceRecursionFunctionalityClosed SourceRecursionWitnessAgreement SourceFiniteTelescope
 SourceProofWeakening SourceZFRProvability SourceBoundMonotone.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_successor_values M phi o a N f g z z' v w funlaw af ag member successor agr appF appG equal law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->
 coding_lt M z k ->coding_lt M z' k ->coding_lt M v k ->coding_lt M w k ->
 source_rec_functionality M phi funlaw ->source_rec_attempt M phi o a N f af ->source_rec_attempt M phi o a N g ag ->
 sf_relation M SFMember z N member ->source_rec_successor M z z' successor ->source_rec_agreement M f g z agr ->
 source_rec_app M f z' v appF ->source_rec_app M g z' w appG ->sf_relation M SFEqual v w equal ->
 source_finite_telescope M[funlaw;af;ag;member;successor;agr;appF;appG]equal law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BG BZ BZ' BV BW HFun HAF HAG HM HS HA HAppF HAppG HE HLaw.
 destruct(source_rec_transition_witness_total M phi f z v)as(exF&HEF).
 destruct(source_rec_transition_witness_total M phi g z w)as(exG&HEG).
 destruct(sf_relation_total M SFImpl exG equal)as(t3&H3).
 destruct(sf_relation_total M SFImpl exF t3)as(t2&H2).
 destruct(sf_relation_total M SFImpl agr t2)as(t1&H1).
 destruct(sf_relation_total M SFImpl funlaw t1)as(witnessLaw&HWitness).
 pose proof(source_zfr_rec_witness_agreement M phi funlaw f g z v w agr exF exG equal t3 t2 t1 witnessLaw k
  BP BF BG BZ BV BW HFun HA HEF HEG HE H3 H2 H1 HWitness)as PWitness.
 destruct PWitness as(cb&cc&cn&HClosed&PWitness).
 assert(BAF:source_bounded M af k)by exact(source_rec_attempt_bounded M phi o a N f af k BP BO BA BN BF HAF).
 assert(BAG:source_bounded M ag k)by exact(source_rec_attempt_bounded M phi o a N g ag k BP BO BA BN BG HAG).
 assert(BFun:source_bounded M funlaw k)by exact(source_bounded_monotone M funlaw(zeroM M)k
  (source_rec_functionality_closed M phi funlaw BP HFun)(coding_zero_lt_succ M k)).
 assert(BMember:source_bounded M member k)by exact(proj2(source_bounded_accept_atom M SFMember z N member k(or_introl eq_refl)HM)(conj BZ BN)).
 assert(BSuccessor:source_bounded M successor k)by exact(source_rec_successor_bounded M z z' successor k BZ BZ' HS).
 assert(BAgr:source_bounded M agr k)by exact(source_rec_agreement_bounded M f g z agr k BF BG BZ HA).
 assert(BAppF:source_bounded M appF k)by exact(source_rec_app_bounded M f z' v appF k BF BZ' BV HAppF).
 assert(BAppG:source_bounded M appG k)by exact(source_rec_app_bounded M g z' w appG k BG BZ' BW HAppG).
 assert(BEqual:source_bounded M equal k)by exact(proj2(source_bounded_accept_atom M SFEqual v w equal k(or_intror eq_refl)HE)(conj BV BW)).
 pose proof(context_bounded_monotone M cb cc cn(zeroM M)k(source_zfr_context_closed M cb cc cn HClosed)(coding_zero_lt_succ M k))as C0.
 exists cb,cc,cn. split;[exact HClosed|].
 apply(source_full_finite_telescope M[funlaw;af;ag;member;successor;agr;appF;appG]equal law k).
 - intros x[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];assumption.
 - exact BEqual.
 - exact HLaw.
 - exact C0.
 - intros b c n BC Included Premises.
   assert(P_funlaw:source_full_prv M b c n funlaw)by(apply Premises;cbn;tauto).
   assert(P_af:source_full_prv M b c n af)by(apply Premises;cbn;tauto).
   assert(P_ag:source_full_prv M b c n ag)by(apply Premises;cbn;tauto).
   assert(P_member:source_full_prv M b c n member)by(apply Premises;cbn;tauto).
   assert(P_successor:source_full_prv M b c n successor)by(apply Premises;cbn;tauto).
   assert(P_agr:source_full_prv M b c n agr)by(apply Premises;cbn;tauto).
   assert(P_appF:source_full_prv M b c n appF)by(apply Premises;cbn;tauto).
   assert(P_appG:source_full_prv M b c n appG)by(apply Premises;cbn;tauto).
   pose proof(source_full_rec_attempt_step M b c n phi o a N f af z z' v member successor appF exF BP HAF HM HS HAppF HEF
    P_af P_member P_successor P_appF)as PExF.
   pose proof(source_full_rec_attempt_step M b c n phi o a N g ag z z' w member successor appG exG BP HAG HM HS HAppG HEG
    P_ag P_member P_successor P_appG)as PExG.
   pose proof(source_full_prv_weaken_bounded M cb cc cn b c n witnessLaw k PWitness Included BC)as PWL.
   apply(source_full_finite_telescope_apply M[funlaw;agr;exF;exG]equal witnessLaw).
   + exists t1. split;[exists t2;split;[exists t3;split;[exists equal;split;[reflexivity|exact H3]|exact H2]|exact H1]|exact HWitness].
   + exact PWL.
   + intros x[<-|[<-|[<-|[<-|[]]]]];assumption.
Qed.
Print Assumptions source_zfr_rec_successor_values.
