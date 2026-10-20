(** An actual witness in the chosen set proves the corresponding Ew
    request, using ordinary source ExI and implication introduction. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalInstantiation NumericalSourceFull SourceD0Recipe
  SourceRelativizationRules SourceRelativizationBounds SourceInstantiationConstructors SourceFilterMemberIntroduction
  SourceProofWeakening SourceLeastOrdinalWitness.
Unset Implicit Arguments.

Theorem source_full_ew_recipe_witness M b c n k domain matrix ew t instance member :
  context_bounded M b c n k ->coding_lt M (zeroM M) k ->
  source_bounded M domain (code_numeral M 1) ->source_bounded M matrix (succM M k) ->coding_lt M t k ->
  source_ew_recipe M domain matrix ew ->numerical_instantiation M matrix t instance ->
  sf_relation M SFMember t (zeroM M) member ->source_full_prv M b c n member ->
  source_full_prv M b c n instance ->source_full_prv M b c n ew.
Proof.
  intros HC HK HD HM HT (atom&left&right&HA&HLeft&(body&HB&HE)&HEw) HInst HMember PM PI.
  pose proof (source_guarded_exists_bounded M domain matrix left k
    (sr_domain_bound_succ M domain k HD) HM HLeft) as HLeftBound.
  assert (HAtomBound:source_bounded M atom (succM M k)).
  { apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M) (code_numeral M 1) atom
      (succM M k) (or_introl eq_refl) HA)).
    split;[apply coding_zero_lt_succ|exact (proj2 (coding_lt_succ_cancel M (zeroM M) k) HK)]. }
  pose proof (proj2 (source_bounded_accept_binary M SFAnd atom matrix body (succM M k)
    (or_introl eq_refl) HB) (conj HAtomBound HM)) as HBodyBound.
  pose proof (proj2 (source_bounded_accept_unary M SFEx body right k
    (or_intror eq_refl) HE) HBodyBound) as HRightBound.
  pose proof (proj2 (source_bounded_accept_binary M SFImpl left right ew k
    (or_intror (or_intror eq_refl)) HEw) (conj HLeftBound HRightBound)) as HEwBound.
  destruct (sf_relation_total M SFAnd member instance) as (witness&HW).
  pose proof (source_instantiation_binary M SFAnd atom matrix body t member instance witness
    (or_introl eq_refl) HB (source_member_zero_successor_instantiation M (zeroM M) t atom member HA HMember)
    HInst HW) as HBodyInst.
  assert (PBody:source_full_prv M b c n witness).
  { exact (full_source_CI M b c n member instance witness
      (source_wf_binary M b c n SFAnd member instance witness (or_introl eq_refl) HW
        (source_full_prv_wellformed M b c n member PM) (source_full_prv_wellformed M b c n instance PI)) PM PI HW). }
  pose proof (full_source_ExI M b c n body right t witness
    (ex_intro _ k (conj HRightBound HC)) PBody HE HBodyInst) as PRight.
  destruct (environment_cons_total M b c n left) as (ub&uc&un&HCons).
  assert (HBranch:context_bounded M ub uc un k).
  { exact (proj2 (context_bounded_cons M b c n left ub uc un k HCons) (conj HLeftBound HC)). }
  exact (full_source_II M b c n left right ew ub uc un (ex_intro _ k (conj HEwBound HC))
    (source_full_prv_weaken_bounded M b c n ub uc un right k PRight
      (source_cons_tail_inclusion M b c n left ub uc un HCons) HBranch) HCons HEw).
Qed.

Print Assumptions source_full_ew_recipe_witness.
