(** Genuine uniform initial-attempt existence. The varying matrix is
    transported by actual quantified source proofs, not a finite-proof promise. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourceDerivedRules
 SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionPrimitiveRelations SourceRecursionStructureGraphs SourceRecursionStructureBounds
 SourceRecursionInitialAttempt SourceRecursionBottomBaseFixed SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_initial_attempt M phi o a N nonzero target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->
 source_rec_nonzero M o N nonzero ->source_rec_initial_attempt M phi o a N target ->sf_relation M SFImpl nonzero target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN HN HT HL.
 destruct(source_zfr_rec_bottom_base_total M o a N)as(nonzero'&bottom&baseLaw&HN'&HBottom&HBaseLaw&PBaseLaw).
 pose proof(code_relation_functional M _ _ nonzero' nonzero HN' HN)as E. subst nonzero'.
 destruct(sf_relation_total M SFImpl bottom target)as(mapLaw&HMapLaw).
 pose proof(source_zfr_rec_initial_attempt_from_bottom M phi o a N bottom target k BP BO BA BN HBottom HT mapLaw HMapLaw)as PMapLaw.
 pose proof(source_rec_nonzero_bounded M o N nonzero k BO BN HN)as BNonzero.
 pose proof(source_rec_initial_attempt_bounded M phi o a N target k BP BO BA BN HT)as BTarget.
 apply(source_zfr_finite_rule M[baseLaw;mapLaw][nonzero]target law k).
 - intros x[<-|[]]. exact BNonzero.
 - exact BTarget.
 - exists target. split;[reflexivity|exact HL].
 - intros x[<-|[<-|[]]];assumption.
 - intros cb cc cn BC Laws Premises.
   pose proof(source_full_modus_ponens M cb cc cn nonzero bottom baseLaw HBaseLaw(Laws baseLaw(or_introl eq_refl))(Premises nonzero(or_introl eq_refl)))as PBottom.
   exact(source_full_modus_ponens M cb cc cn bottom target mapLaw HMapLaw(Laws mapLaw(or_intror(or_introl eq_refl)))PBottom).
Qed.
Print Assumptions source_zfr_rec_initial_attempt.
