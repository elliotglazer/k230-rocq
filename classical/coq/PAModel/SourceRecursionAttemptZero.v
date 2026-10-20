(** The actual attempt-at-zero rule, for an arbitrary internal binary
    matrix. The universal instance and its singleton substitution are built. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes NumericalContexts NumericalSourceFull
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SubstitutionSource SourceInstantiationConstructors
  SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport SourceRecursionAttempt
  SourcePieceBoundMaxJoint SourceDerivedRules SourceTraceBounds.
Unset Implicit Arguments.

Theorem source_full_rec_attempt_at_zero M b c l phi o a N f att v app equal:
  source_rec_attempt M phi o a N f att ->source_rec_app M f o v app ->sf_relation M SFEqual v a equal ->
  source_full_prv M b c l att ->source_full_prv M b c l app ->source_full_prv M b c l equal.
Proof.
  intros(first&second&(oldApp&oldEq&point&HApp&HEq&HPoint&HAll)&HSecond&HAtt)HApp' HEq' PAtt PApp.
  destruct(source_full_piece_conjunction_components M b c l first second att HAtt PAtt) as[PFirst PSecond].
  pose proof(source_rec_app_instantiation M f o oldApp v app HApp HApp') as HIApp.
  assert(HIEq:numerical_instantiation M oldEq v equal).
  { destruct(substitution_singleton_total M v) as(rb&rc&HHead&_). exists rb,rc. split;[exact HHead|].
    apply(proj2(numerical_substitution_equal M(zeroM M)(succM M a)oldEq rb rc(code_numeral M 1)(zeroM M)equal HEq)).
    exists v,a. exact(conj HHead(conj(substitution_singleton_tail M rb rc a)HEq')). }
  destruct(sf_relation_total M SFImpl app equal) as(instance&HInstance).
  pose proof(source_instantiation_binary M SFImpl oldApp oldEq point v app equal instance(or_intror(or_intror eq_refl))
    HPoint HIApp HIEq HInstance) as HI.
  assert(PInstance:source_full_prv M b c l instance).
  { exact(full_source_AllE M b c l point first v instance
      (source_wf_quantifier_instance M b c l SFAll point first v instance(or_introl eq_refl)HAll
        (source_full_prv_wellformed M b c l first PFirst)HI)PFirst HAll HI). }
  exact(source_full_modus_ponens M b c l app equal instance HInstance PInstance PApp).
Qed.

Print Assumptions source_full_rec_attempt_at_zero.
