(** The old-App branch of an arbitrary-matrix attempt extension. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourceDerivedRules
 SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionAttemptStep
 SourceRecursionAttemptStepShell SourceRecursionValuePairs SourceRecursionSetOperations SourceRecursionSetOperationTransport SourceRecursionAdjoinWitness SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_old_step_branch M phi o a N f q g u nextu v att member successor adj app target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M q k ->coding_lt M g k ->
 coding_lt M u k ->coding_lt M nextu k ->coding_lt M v k ->source_rec_attempt M phi o a N f att ->sf_relation M SFMember u N member ->
 source_rec_successor M u nextu successor ->source_rec_adjoin M f q g adj ->source_rec_app M f nextu v app ->source_rec_transition_witness M phi g u v target ->
 source_finite_telescope M[att;member;successor;adj;app]target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BQ BG BU BNextU BV HAtt HM HS HA HApp HT HLaw.
 destruct(source_rec_transition_witness_total M phi f u v)as(old&HO).
 destruct(sf_relation_total M SFImpl old target)as(point&HP).
 destruct(sf_relation_total M SFImpl adj point)as(mapLaw&HMapLaw).
 pose proof(source_zfr_rec_transition_adjoin M phi f q g u v adj old target point mapLaw k BP BF BQ BG BU BV HA HO HT HP HMapLaw)as PMapLaw.
 pose proof(source_rec_attempt_bounded M phi o a N f att k BP BO BA BN BF HAtt)as BAtt.
 assert(BM:source_bounded M member k)by exact(proj2(source_bounded_accept_atom M SFMember u N member k(or_introl eq_refl)HM)(conj BU BN)).
 pose proof(source_rec_successor_bounded M u nextu successor k BU BNextU HS)as BS.
 pose proof(source_rec_adjoin_bounded M f q g adj k BF BQ BG HA)as BAdj.
 pose proof(source_rec_app_bounded M f nextu v app k BF BNextU BV HApp)as BApp.
 pose proof(source_rec_transition_witness_bounded M phi g u v target k BP BG BU BV HT)as BT.
 apply(source_zfr_finite_rule M[mapLaw][att;member;successor;adj;app]target law k).
 - intros x[<-|[<-|[<-|[<-|[<-|[]]]]]];assumption.
 - exact BT.
 - exact HLaw.
 - intros x[<-|[]]. exact PMapLaw.
 - intros cb cc cn BC Laws Premises.
   assert(PAtt:source_full_prv M cb cc cn att)by(apply Premises;cbn;tauto).
   assert(PMember:source_full_prv M cb cc cn member)by(apply Premises;cbn;tauto).
   assert(PSuccessor:source_full_prv M cb cc cn successor)by(apply Premises;cbn;tauto).
   assert(PAdj:source_full_prv M cb cc cn adj)by(apply Premises;cbn;tauto).
   assert(PApp:source_full_prv M cb cc cn app)by(apply Premises;cbn;tauto).
   pose proof(source_full_rec_attempt_step M cb cc cn phi o a N f att u nextu v member successor app old BP HAtt HM HS HApp HO PAtt PMember PSuccessor PApp)as POld.
   pose proof(source_full_modus_ponens M cb cc cn adj point mapLaw HMapLaw(Laws mapLaw(or_introl eq_refl))PAdj)as PPoint.
   exact(source_full_modus_ponens M cb cc cn old target point HP PPoint POld).
Qed.
Print Assumptions source_zfr_rec_old_step_branch.
