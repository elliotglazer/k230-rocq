(** Actually specialize the hierarchy-set quantifier of D0 at an arbitrary
    internal name. The inserted matrix parameter is removed syntactically. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalInstantiation NumericalSubstitutionMaps SubstitutionSource NumericalSourceFull SourceDerivedRules
  SourceInstantiationConstructors SourceD0At SourceHierarchySyntax SourceEwMonotone SourceEwSubstitution.
Unset Implicit Arguments.

Theorem source_full_d0_at_specialization M b c n domain phi d out t level result k :
  source_bounded M domain (code_numeral M 1) ->source_bounded M phi k ->
  source_d0_at M domain phi d out ->source_LL_instance M d t level ->
  source_ew_at M domain phi t result ->source_full_prv M b c n out ->
  source_full_prv M b c n level ->source_full_prv M b c n result.
Proof.
  intros HD HB (s&rawL&rawE&point&HC&HL&HE&HP&HA) HLevel HResult POut PL.
  destruct (sf_relation_total M SFImpl level result) as (instance&HInstance).
  assert (HIL:numerical_instantiation M rawL t level).
  { apply (source_LL_instance_instantiation M (succM M d) (zeroM M) rawL d t level t HL HLevel).
    - intros ub uc HH. apply substitution_singleton_tail.
    - intros ub uc HH. exact HH. }
  pose proof (source_ew_at_specialization M domain phi s rawE result t k HD HB HC HE HResult) as HIE.
  pose proof (source_instantiation_binary M SFImpl rawL rawE point t level result instance
    (or_intror (or_intror eq_refl)) HP HIL HIE HInstance) as HI.
  pose proof (full_source_AllE M b c n point out t instance
    (source_wf_quantifier_instance M b c n SFAll point out t instance (or_introl eq_refl)
      HA (source_full_prv_wellformed M b c n out POut) HI) POut HA HI) as PInstance.
  exact (source_full_modus_ponens M b c n level result instance HInstance PInstance PL).
Qed.

Print Assumptions source_full_d0_at_specialization.
