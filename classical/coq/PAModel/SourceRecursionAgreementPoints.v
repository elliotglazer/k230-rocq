(** The genuine base and successor value arguments in attempt agreement.
    Premises are ordinary source proofs, not semantic truth assumptions. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalSourceFull SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptZero
 SourceRecursionBinaryInstance SourceRecursionFunctionality SourceRecursionAgreement SourceDerivedRules
 SourceBinaryEqualityTransport SourceConditionalProofs SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_full_rec_agreement_zero_values M cb cc cn phi o a N f g af ag v w appf appg va wa vw tail law:
 source_rec_attempt M phi o a N f af ->source_rec_attempt M phi o a N g ag ->
 source_rec_app M f o v appf ->source_rec_app M g o w appg ->
 sf_relation M SFEqual v a va ->sf_relation M SFEqual w a wa ->sf_relation M SFEqual v w vw ->
 sf_relation M SFImpl wa vw tail ->sf_relation M SFImpl va tail law ->
 source_full_prv M cb cc cn af ->source_full_prv M cb cc cn ag ->source_full_prv M cb cc cn appf ->
 source_full_prv M cb cc cn appg ->source_full_prv M cb cc cn law ->source_full_prv M cb cc cn vw.
Proof.
 intros HAF HAG HAppF HAppG HVA HWA HVW HT HL PAF PAG PF PG PL.
 pose proof(source_full_rec_attempt_at_zero M cb cc cn phi o a N f af v appf va HAF HAppF HVA PAF PF)as PVA.
 pose proof(source_full_rec_attempt_at_zero M cb cc cn phi o a N g ag w appg wa HAG HAppG HWA PAG PG)as PWA.
 exact(source_full_modus_ponens M cb cc cn wa vw tail HT
  (source_full_modus_ponens M cb cc cn va tail law HL PL PVA)PWA).
Qed.

Theorem source_full_rec_agreement_predecessors M cb cc cn phi funlaw f g z agr u v x y appf appg gx gy gx' uv xy point move:
 source_bounded M phi(code_numeral M 2) ->source_rec_functionality M phi funlaw ->source_rec_agreement M f g z agr ->
 source_rec_app M f z u appf ->source_rec_app M g z v appg ->
 source_rec_binary M phi u x gx ->source_rec_binary M phi v y gy ->source_rec_binary M phi u y gx' ->
 sf_relation M SFEqual u v uv ->sf_relation M SFEqual x y xy ->
 sf_relation M SFImpl gy gx' point ->sf_relation M SFImpl uv point move ->
 source_full_prv M cb cc cn funlaw ->source_full_prv M cb cc cn agr ->
 source_full_prv M cb cc cn appf ->source_full_prv M cb cc cn appg ->
 source_full_prv M cb cc cn gx ->source_full_prv M cb cc cn gy ->source_full_prv M cb cc cn move ->
 source_full_prv M cb cc cn xy.
Proof.
 intros BP HF HA HAF HAG HGX HGY HGX' HUV HXY HP HM PF PA PAF PAG PGX PGY PM.
 pose proof(source_full_rec_agreement_use M cb cc cn f g z agr u v appf appg uv HA HAF HAG HUV PA PAF PAG)as PUV.
 pose proof(source_full_modus_ponens M cb cc cn gy gx' point HP
  (source_full_modus_ponens M cb cc cn uv point move HM PM PUV)PGY)as PGX'.
 exact(source_full_rec_functionality_use M cb cc cn phi funlaw u x y gx gx' xy BP HF HGX HGX' HXY PF PGX PGX').
Qed.
Theorem source_zfr_rec_agreement_transport M phi u v y before after equal point law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M u k ->coding_lt M v k ->coding_lt M y k ->
 source_rec_binary M phi u y after ->source_rec_binary M phi v y before ->sf_relation M SFEqual u v equal ->
 sf_relation M SFImpl before after point ->sf_relation M SFImpl equal point law ->source_zfr_provable M law.
Proof.
 intros BP BU BV BY HA HB HE HP HL.
 exact(proj2(source_binary_input_equality M phi u v y after before equal k BP BU BV BY HA HB HE)point HP law HL).
Qed.
Print Assumptions source_full_rec_agreement_zero_values.
Print Assumptions source_full_rec_agreement_predecessors.
Print Assumptions source_zfr_rec_agreement_transport.
