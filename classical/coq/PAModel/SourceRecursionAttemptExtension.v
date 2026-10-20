(** Actual uniform one-pair extension of an arbitrary internally coded attempt. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourcePieceBoundMaxJoint
 SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionStructureGraphs SourceRecursionStructureBounds
 SourceRecursionExtensionInputs SourceRecursionExtensionStep SourceRecursionZeroExtensionShell SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_attempt_extension M phi o a N f q g z next p w nonzero A target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M q k ->coding_lt M g k ->
 coding_lt M z k ->coding_lt M next k ->coding_lt M p k ->coding_lt M w k ->source_rec_nonzero M o N nonzero ->
 source_rec_extension_inputs M phi o a N f q g z next p w A ->source_rec_attempt M phi o a N g target ->
 source_finite_telescope M(nonzero::A)target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BQ BG BZ BNext BP' BW HNZ HInputs HTarget HLaw.
 pose proof(source_rec_nonzero_bounded M o N nonzero k BO BN HNZ)as BNZ.
 pose proof(source_rec_extension_inputs_bounded M phi o a N f q g z next p w A k BP BO BA BN BF BQ BG BZ BNext BP' BW HInputs)as Bounds.
 pose proof(source_rec_attempt_bounded M phi o a N g target k BP BO BA BN BG HTarget)as BTarget.
 destruct HTarget as(firstG&stepG&HFg&HSg&HNewAnd).
 destruct(source_finite_telescope_total M A stepG)as(stepLaw&HStepLaw).
 pose proof(source_zfr_rec_extension_step M phi o a N f q g z next p w A stepG stepLaw k BP BO BA BN BF BQ BG BZ BNext BP' BW HInputs HSg HStepLaw)as PStepLaw.
 destruct HInputs as(inj&att&mz&sz&appf&adj&op&binary&E&HI&HAtt&HMZ&HSZ&HAF&HA&HO&HBinary). subst A.
 destruct HAtt as(firstF&stepF&HFf&HSf&HOldAnd).
 destruct(source_zfr_rec_zero_extension_total M o a N f z next w q g)
  as(nonzero'&member'&successor'&adj'&op'&firstF'&firstG'&zeroLaw&HNZ'&HMZ'&HSZ'&HA'&HO'&HFf'&HFg'&HZeroLaw&PZeroLaw).
 pose proof(code_relation_functional M _ _ nonzero' nonzero HNZ' HNZ)as E. subst nonzero'.
 pose proof(sf_relation_functional M SFMember z N member' mz HMZ' HMZ)as E. subst member'.
 pose proof(code_relation_functional M _ _ successor' sz HSZ' HSZ)as E. subst successor'.
 pose proof(code_relation_functional M _ _ adj' adj HA' HA)as E. subst adj'.
 pose proof(code_relation_functional M _ _ op' op HO' HO)as E. subst op'.
 pose proof(source_rec_attempt_zero_functional M o a f firstF' firstF HFf' HFf)as E. subst firstF'.
 pose proof(source_rec_attempt_zero_functional M o a g firstG' firstG HFg' HFg)as E. subst firstG'.
 apply(source_zfr_finite_rule M[zeroLaw;stepLaw](nonzero::[inj;att;mz;sz;appf;adj;op;binary])target law k).
 - intros x[<-|HX];[exact BNZ|exact(Bounds x HX)].
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[<-|[]]];assumption.
 - intros cb cc cn BC Laws Premises.
   assert(PAtt:source_full_prv M cb cc cn att)by(apply Premises;cbn;tauto).
   pose proof(proj1(source_full_piece_conjunction_components M cb cc cn firstF stepF att HOldAnd PAtt))as PFirstF.
   assert(PFirstG:source_full_prv M cb cc cn firstG).
   { apply(source_full_finite_telescope_apply M[nonzero;mz;sz;adj;op;firstF]firstG zeroLaw HZeroLaw cb cc cn).
     - apply Laws. now left.
     - intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];first[exact PFirstF|apply Premises;cbn;tauto]. }
   assert(PStepG:source_full_prv M cb cc cn stepG).
   { apply(source_full_finite_telescope_apply M[inj;att;mz;sz;appf;adj;op;binary]stepG stepLaw HStepLaw cb cc cn).
     - apply Laws. right. now left.
     - intros x HX. apply Premises. now right. }
   exact(full_source_CI M cb cc cn firstG stepG target(ex_intro _ k(conj BTarget BC))PFirstG PStepG HNewAnd).
Qed.
Print Assumptions source_zfr_rec_attempt_extension.
