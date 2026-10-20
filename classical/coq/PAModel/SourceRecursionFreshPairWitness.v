(** The varying-matrix part of a fresh-pair attempt extension, with
    output equality consumed by actual Leibniz and existential rules. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourceDerivedRules
 SourceRecursionPrimitiveRelations SourceRecursionBinaryInstance SourceRecursionAttemptStepShell SourceRecursionValuePairs
 SourceBinaryOutputEquality SourceRecursionTransitionIntroduction SourceFiniteTelescope SourceZFRFiniteRule SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_fresh_pair_witness M phi g u p v w equal app binary target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M g k ->coding_lt M u k ->coding_lt M p k ->coding_lt M v k ->coding_lt M w k ->
 sf_relation M SFEqual v w equal ->source_rec_app M g u p app ->source_rec_binary M phi p w binary ->source_rec_transition_witness M phi g u v target ->
 source_finite_telescope M[equal;app;binary]target law ->source_zfr_provable M law.
Proof.
 intros BP BG BU BP' BV BW HE HA HG HT HLaw.
 destruct(source_rec_binary_total M phi p v)as(moved&HMoved).
 destruct(sf_relation_total M SFImpl binary moved)as(point&HPoint).
 destruct(sf_relation_total M SFImpl equal point)as(moveLaw&HMoveLaw).
 pose proof(proj2(source_binary_output_equality M phi p v w moved binary equal k BP BP' BV BW HMoved HG HE)point HPoint moveLaw HMoveLaw)as PMoveLaw.
 assert(BE:source_bounded M equal k)by exact(proj2(source_bounded_accept_atom M SFEqual v w equal k(or_intror eq_refl)HE)(conj BV BW)).
 pose proof(source_rec_app_bounded M g u p app k BG BU BP' HA)as BA.
 pose proof(source_rec_binary_bounded M phi p w binary k BP BP' BW HG)as BGit.
 pose proof(source_rec_transition_witness_bounded M phi g u v target k BP BG BU BV HT)as BT.
 apply(source_zfr_finite_rule M[moveLaw][equal;app;binary]target law k).
 - intros x[<-|[<-|[<-|[]]]];assumption.
 - exact BT.
 - exact HLaw.
 - intros x[<-|[]]. exact PMoveLaw.
 - intros cb cc cn BC Laws Premises.
   assert(PE:source_full_prv M cb cc cn equal)by(apply Premises;cbn;tauto).
   assert(PA:source_full_prv M cb cc cn app)by(apply Premises;cbn;tauto).
   assert(PG:source_full_prv M cb cc cn binary)by(apply Premises;cbn;tauto).
   pose proof(source_full_modus_ponens M cb cc cn equal point moveLaw HMoveLaw(Laws moveLaw(or_introl eq_refl))PE)as PPoint.
   pose proof(source_full_modus_ponens M cb cc cn binary moved point HPoint PPoint PG)as PMoved.
   exact(source_full_rec_transition_intro M cb cc cn phi g u v target p app moved k BP BG BU BV BC HT HA HMoved PA PMoved).
Qed.
Print Assumptions source_zfr_rec_fresh_pair_witness.
