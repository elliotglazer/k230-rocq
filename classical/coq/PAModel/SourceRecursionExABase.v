(** Genuine uniform base existence of an attempt at the initial index. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourceDerivedRules
 SourceFiniteTelescope SourceZFRFiniteRule SourceZFRPositiveMaps SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionInitialAttempt SourceRecursionInitialAttemptZFR
 SourceRecursionAppExists SourceRecursionExistsAttempt SourceRecursionStructureGraphs SourceRecursionStructureBounds SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_app_exists_map M f z v app some k:
 coding_lt M f k ->coding_lt M z k ->coding_lt M v k ->source_rec_app M f z v app ->source_rec_app_exists M f z some ->source_zfr_map M app some.
Proof.
 intros BF BZ BV HA HS law HL.
 pose proof(source_rec_app_bounded M f z v app k BF BZ BV HA)as BA.
 pose proof(source_rec_app_exists_bounded M f z some k BF BZ HS)as BS.
 apply(source_zfr_finite_rule M[][app]some law k).
 - intros x[<-|[]]. exact BA.
 - exact BS.
 - exists some. split;[reflexivity|exact HL].
 - intros x HX. contradiction.
 - intros cb cc cn BC Laws Premises. exact(source_full_rec_app_exists_intro M cb cc cn f z v app some k BF BZ BC HA HS(Premises app(or_introl eq_refl))).
Qed.
Theorem source_zfr_rec_initial_attempt_exa M phi o a N initial target k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->
 source_rec_initial_attempt M phi o a N initial ->source_rec_exa M phi o o a N target ->source_zfr_map M initial target.
Proof.
 intros BP BO BA BN HI HT.
 pose proof(source_rec_initial_attempt_bounded M phi o a N initial k BP BO BA BN HI)as BI.
 pose proof(source_rec_exa_bounded M phi o o a N target k BP BO BO BA BN HT)as BT.
 destruct HI as(att&app&body&HA&HApp&HB&HE).
 destruct HT as(att'&some&body'&HA'&HS&HB'&HE').
 pose proof(source_rec_attempt_functional M phi(succM M o)(succM M a)(succM M N)(zeroM M)att' att HA' HA)as E. subst att'.
 pose proof(proj1(source_bounded_accept_unary M SFEx body initial k(or_intror eq_refl)HE)BI)as BBody.
 pose proof(proj1(source_bounded_accept_unary M SFEx body' target k(or_intror eq_refl)HE')BT)as BBody'.
 destruct(proj1(source_bounded_accept_binary M SFAnd att app body(succM M k)(or_introl eq_refl)HB)BBody)as[BAtt BApp].
 destruct(proj1(source_bounded_accept_binary M SFAnd att some body'(succM M k)(or_introl eq_refl)HB')BBody')as[BAtt' BSome].
 apply(source_zfr_map_quantifier M SFEx body body' initial target k(or_intror eq_refl)BBody BBody' HE HE').
 apply(source_zfr_map_right M SFAnd att app some body body'(succM M k)(or_introl eq_refl)BAtt BApp BSome HB HB').
 exact(source_zfr_rec_app_exists_map M(zeroM M)(succM M o)(succM M a)app some(succM M k)(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M o k)BO)(proj2(coding_lt_succ_cancel M a k)BA)HApp HS).
Qed.
Theorem source_zfr_rec_exa_base M phi o a N nonzero target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->source_rec_nonzero M o N nonzero ->
 source_rec_exa M phi o o a N target ->sf_relation M SFImpl nonzero target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN HN HT HL.
 destruct(source_rec_initial_attempt_total M phi o a N)as(initial&HI).
 destruct(sf_relation_total M SFImpl nonzero initial)as(initialLaw&HInitialLaw).
 pose proof(source_zfr_rec_initial_attempt M phi o a N nonzero initial initialLaw k BP BO BA BN HN HI HInitialLaw)as PInitial.
 destruct(sf_relation_total M SFImpl initial target)as(mapLaw&HMapLaw).
 pose proof(source_zfr_rec_initial_attempt_exa M phi o a N initial target k BP BO BA BN HI HT mapLaw HMapLaw)as PMap.
 pose proof(source_rec_nonzero_bounded M o N nonzero k BO BN HN)as BNZ.
 pose proof(source_rec_exa_bounded M phi o o a N target k BP BO BO BA BN HT)as BT.
 apply(source_zfr_finite_rule M[initialLaw;mapLaw][nonzero]target law k).
 - intros x[<-|[]]. exact BNZ.
 - exact BT.
 - exists target. split;[reflexivity|exact HL].
 - intros x[<-|[<-|[]]];assumption.
 - intros cb cc cn BC Laws Premises.
   pose proof(source_full_modus_ponens M cb cc cn nonzero initial initialLaw HInitialLaw(Laws initialLaw(or_introl eq_refl))(Premises nonzero(or_introl eq_refl)))as PI.
   exact(source_full_modus_ponens M cb cc cn initial target mapLaw HMapLaw(Laws mapLaw(or_intror(or_introl eq_refl)))PI).
Qed.
Print Assumptions source_zfr_rec_app_exists_map.
Print Assumptions source_zfr_rec_initial_attempt_exa.
Print Assumptions source_zfr_rec_exa_base.
