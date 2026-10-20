(** The agreement subset contains the initial recursion index. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone NumericalContexts NumericalSourceFull
 SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds
 SourceRecursionAgreement SourceRecursionAgreementZero SourceRecursionAgreementSubset SourceRecursionSubsetBounds SourceRecursionSubsetRules SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_subset_zero M phi o a N f g X af ag chart mn mx law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->coding_lt M X k ->
 source_rec_attempt M phi o a N f af ->source_rec_attempt M phi o a N g ag ->source_rec_subset_chart M f g N X chart ->
 sf_relation M SFMember o N mn ->sf_relation M SFMember o X mx ->source_finite_telescope M[af;ag;chart;mn]mx law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BG BX HAF HAG HChart HMN HMX HLaw.
 destruct(source_rec_agreement_total M f g o)as(agr&HA).
 destruct(sf_relation_total M SFImpl ag agr)as(tail&HT).
 destruct(sf_relation_total M SFImpl af tail)as(baseLaw&HB).
 pose proof(source_zfr_rec_agreement_zero M phi o a N f g af ag agr tail baseLaw k BP BO BA BN BF BG HAF HAG HA HT HB)as PBase.
 pose proof(source_rec_attempt_bounded M phi o a N f af k BP BO BA BN BF HAF)as BAF.
 pose proof(source_rec_attempt_bounded M phi o a N g ag k BP BO BA BN BG HAG)as BAG.
 pose proof(source_rec_subset_chart_bounded M f g N X chart k BF BG BN BX HChart)as BChart.
 assert(BMN:source_bounded M mn k)by exact(proj2(source_bounded_accept_atom M SFMember o N mn k(or_introl eq_refl)HMN)(conj BO BN)).
 assert(BMX:source_bounded M mx k)by exact(proj2(source_bounded_accept_atom M SFMember o X mx k(or_introl eq_refl)HMX)(conj BO BX)).
 apply(source_zfr_finite_rule M[baseLaw][af;ag;chart;mn]mx law k).
 - intros x[<-|[<-|[<-|[<-|[]]]]];assumption.
 - exact BMX.
 - exact HLaw.
 - intros x[<-|[]]. exact PBase.
 - intros cb cc cn BC Laws Premises.
   assert(PAF:source_full_prv M cb cc cn af)by(apply Premises;cbn;tauto).
   assert(PAG:source_full_prv M cb cc cn ag)by(apply Premises;cbn;tauto).
   assert(PChart:source_full_prv M cb cc cn chart)by(apply Premises;cbn;tauto).
   assert(PMN:source_full_prv M cb cc cn mn)by(apply Premises;cbn;tauto).
   assert(PAgr:source_full_prv M cb cc cn agr).
   { apply(source_full_finite_telescope_apply M[af;ag]agr baseLaw).
     - exists tail. split;[exists agr;split;[reflexivity|exact HT]|exact HB].
     - apply Laws. now left.
     - intros x[<-|[<-|[]]];assumption. }
   exact(source_full_rec_subset_chart_in M cb cc cn f g N X o chart mx mn agr HChart HMX HMN HA PChart PMN PAgr).
Qed.
Print Assumptions source_zfr_rec_subset_zero.
