(** Introduce actual membership in a Replacement image from an ordinary
    input/member proof and an ordinary relation proof. The two binder
    specializations are the literal internally coded substitutions. *)
From PAModel Require Import Model FiniteCoding SetFormulaCodes NumericalInstantiation
  NumericalSourceFull SourceQuantifierRules SourceInstantiationConstructors
  SourceConjunctionRules SourceDerivedRules.
Unset Implicit Arguments.

Theorem source_full_range_member_introduction M b c n point profile d instance
    body ex v witness input matrix forward reverse member :
  sf_relation M SFAll point (zeroM M) profile ->numerical_instantiation M point d instance ->
  sf_relation M SFAnd forward reverse instance ->sf_relation M SFImpl ex member reverse ->
  sf_relation M SFEx body (zeroM M) ex ->numerical_instantiation M body v witness ->
  sf_relation M SFAnd input matrix witness ->
  source_full_prv M b c n profile ->source_full_prv M b c n input ->source_full_prv M b c n matrix ->
  source_full_prv M b c n member.
Proof.
  intros HProfile HInstance HPair HReverse HEx HWitness HBody PProfile PInput PMatrix.
  assert (PInstance:source_full_prv M b c n instance).
  { exact (full_source_AllE M b c n point profile d instance
      (source_wf_quantifier_instance M b c n SFAll point profile d instance (or_introl eq_refl)
        HProfile (source_full_prv_wellformed M b c n profile PProfile) HInstance)
      PProfile HProfile HInstance). }
  pose proof (source_full_conjunction_right M b c n forward reverse instance HPair PInstance) as PReverse.
  assert (PWitness:source_full_prv M b c n witness).
  { exact (full_source_CI M b c n input matrix witness
      (source_wf_binary M b c n SFAnd input matrix witness (or_introl eq_refl) HBody
        (source_full_prv_wellformed M b c n input PInput)
        (source_full_prv_wellformed M b c n matrix PMatrix)) PInput PMatrix HBody). }
  assert (PEx:source_full_prv M b c n ex).
  { exact (full_source_ExI M b c n body ex v witness
      (source_wf_binary_left M b c n SFImpl ex member reverse (or_intror (or_intror eq_refl))
        HReverse (source_full_prv_wellformed M b c n reverse PReverse)) PWitness HEx HWitness). }
  exact (source_full_modus_ponens M b c n ex member reverse HReverse PReverse PEx).
Qed.

Print Assumptions source_full_range_member_introduction.
