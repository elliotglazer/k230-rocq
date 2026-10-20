(** A real extended attempt and value yield the successor ExA formula. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceDerivedRules SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds
 SourceRecursionStructureGraphs SourceRecursionStructureBounds SourceRecursionSetOperations SourceRecursionPrimitiveShifts
 SourceRecursionExtensionInputs SourceRecursionAttemptExtension SourceRecursionAdjoinRight SourceRecursionExistsAttempt
 SourceRecursionExAIntroduction SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_exa_extension_point M phi o a N f q g z next p w nonzero A target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M q k ->coding_lt M g k ->
 coding_lt M z k ->coding_lt M next k ->coding_lt M p k ->coding_lt M w k ->source_rec_nonzero M o N nonzero ->
 source_rec_extension_inputs M phi o a N f q g z next p w A ->source_rec_exa M phi next o a N target ->
 source_finite_telescope M(nonzero::A)target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BQ BG BZ BNext BP' BW HNZ HInputs HTarget HLaw.
 pose proof(source_rec_nonzero_bounded M o N nonzero k BO BN HNZ)as BNZ.
 pose proof(source_rec_extension_inputs_bounded M phi o a N f q g z next p w A k BP BO BA BN BF BQ BG BZ BNext BP' BW HInputs)as Bounds.
 pose proof(source_rec_exa_bounded M phi next o a N target k BP BNext BO BA BN HTarget)as BTarget.
 destruct(source_rec_attempt_total M phi o a N g)as(attg&HAttG).
 destruct(source_finite_telescope_total M(nonzero::A)attg)as(attLaw&HAttLaw).
 pose proof(source_zfr_rec_attempt_extension M phi o a N f q g z next p w nonzero A attg attLaw k
 BP BO BA BN BF BQ BG BZ BNext BP' BW HNZ HInputs HAttG HAttLaw)as PAttLaw.
 destruct HInputs as(inj&att&mz&sz&appf&adj&op&binary&E&HI&HAtt&HMZ&HSZ&HAF&HA&HO&HBinary). subst A.
 destruct(source_rec_app_total M g next w)as(appg&HAppG).
 destruct(sf_relation_total M SFImpl op appg)as(point&HPoint).
 destruct(sf_relation_total M SFImpl adj point)as(appLaw&HAppLaw).
 pose proof(source_zfr_rec_adjoin_right M f q g next w adj op appg point appLaw HA HO HAppG HPoint HAppLaw)as PAppLaw.
 apply(source_zfr_finite_rule M[attLaw;appLaw][nonzero;inj;att;mz;sz;appf;adj;op;binary]target law k).
 - intros x[<-|HX];[exact BNZ|exact(Bounds x HX)].
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[<-|[]]];assumption.
 - intros cb cc cn BC Laws Premises.
   assert(PT:source_full_prv M cb cc cn attg).
   { apply(source_full_finite_telescope_apply M[nonzero;inj;att;mz;sz;appf;adj;op;binary]attg attLaw HAttLaw cb cc cn).
     - apply Laws. now left.
     - exact Premises. }
   assert(PG:source_full_prv M cb cc cn appg).
   { pose proof(source_full_modus_ponens M cb cc cn adj point appLaw HAppLaw(Laws appLaw(or_intror(or_introl eq_refl)))(Premises adj ltac:(cbn;tauto)))as PP.
     exact(source_full_modus_ponens M cb cc cn op appg point HPoint PP(Premises op ltac:(cbn;tauto))). }
   exact(source_full_rec_exa_intro M cb cc cn phi next o a N target g w attg appg k BP BNext BO BA BN BG BC HTarget HAttG HAppG PT PG).
Qed.
Print Assumptions source_zfr_rec_exa_extension_point.
