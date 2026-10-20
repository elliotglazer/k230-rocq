(** A Replacement relation whose matrix contains a unary property of its
    output yields a range of objects satisfying that property. All proof
    steps are actual numerical source rules. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded SourceBoundMonotone NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalSourceFull SourceQuantifierRules SourceTraceBounds
  SourceRelativizationBounds SourceConjunctionRules SourceProofWeakening
  SourceDerivedRules SourceUniversalPropositional.
Unset Implicit Arguments.

Theorem source_full_exists_left_decoration M b c n domain domain1 theta tail input inner matrix body ex :
  source_bounded M domain (code_numeral M 1) ->source_formula_shift M domain domain1 ->
  sf_relation M SFAnd domain1 theta inner ->sf_relation M SFAnd inner tail matrix ->
  sf_relation M SFAnd input matrix body ->sf_relation M SFEx body (zeroM M) ex ->
  source_full_prv M b c n ex ->source_full_prv M b c n domain.
Proof.
  intros HD HS HI HM HB HE PEx.
  destruct (source_full_prv_wellformed M b c n ex PEx) as (k&HExBound&HC).
  pose proof (proj1 (source_bounded_accept_unary M SFEx body ex k (or_intror eq_refl) HE) HExBound) as HBodyBound.
  destruct (context_shift_total M b c n) as (s&t&HCtxShift).
  destruct (environment_cons_total M s t n body) as (u&v&l&HCons).
  pose proof (context_shift_preserves_bound M b c n s t k HCtxShift HC) as HCShift.
  assert (HBranch:context_bounded M u v l (succM M k)).
  { exact (proj2 (context_bounded_cons M s t n body u v l _ HCons) (conj HBodyBound HCShift)). }
  apply (full_source_ExE M b c n body ex domain domain1 s t u v l).
  - exists (succM M k). split;[exact (sr_domain_bound_succ M domain k HD)|].
    apply (context_bounded_monotone M b c n k (succM M k) HC).
    apply coding_lt_succ_cases. left. apply coding_lt_succ.
  - exact PEx.
  - apply (source_full_conjunction_left M u v l domain1 theta inner HI).
    apply (source_full_conjunction_left M u v l inner tail matrix HM).
    apply (source_full_conjunction_right M u v l input matrix body HB).
    apply full_source_Ctx;[exists (succM M k);auto|].
    apply (proj2 (context_member_cons M s t n body u v l body HCons)). now left.
  - exact HE.
  - exact HCtxShift.
  - exact HCons.
  - exact HS.
Qed.

Theorem source_full_replacement_decoration_point M b c n domain domain1 theta tail input inner matrix body ex
    left forward reverse point target :
  source_bounded M domain (code_numeral M 1) ->source_formula_shift M domain domain1 ->
  sf_relation M SFAnd domain1 theta inner ->sf_relation M SFAnd inner tail matrix ->
  sf_relation M SFAnd input matrix body ->sf_relation M SFEx body (zeroM M) ex ->
  sf_relation M SFImpl left ex forward ->sf_relation M SFAnd forward reverse point ->
  sf_relation M SFImpl left domain target ->source_full_prv M b c n point ->
  source_full_prv M b c n target.
Proof.
  intros HD HS HI HM HB HE HF HP HT PPoint.
  pose proof (source_full_conjunction_left M b c n forward reverse point HP PPoint) as PForward.
  destruct (source_full_prv_wellformed M b c n forward PForward) as (k&HForward&HC).
  pose proof (proj1 (proj1 (source_bounded_accept_binary M SFImpl left ex forward k
    (or_intror (or_intror eq_refl)) HF) HForward)) as HL.
  assert (HLe:coding_lt M k (succM M (succM M k)))
    by (apply coding_lt_succ_cases;left;apply coding_lt_succ).
  pose proof (context_bounded_monotone M b c n k (succM M k) HC HLe) as HC'.
  pose proof (source_bounded_monotone M left k (succM M k) HL HLe) as HL'.
  pose proof (sr_domain_bound_succ M domain k HD) as HD'.
  destruct (environment_cons_total M b c n left) as (u&v&l&HCons).
  assert (HBranch:context_bounded M u v l (succM M k)).
  { exact (proj2 (context_bounded_cons M b c n left u v l _ HCons) (conj HL' HC')). }
  apply (full_source_II M b c n left domain target u v l).
  - exists (succM M k). split;[|exact HC'].
    apply (proj2 (source_bounded_accept_binary M SFImpl left domain target _
      (or_intror (or_intror eq_refl)) HT)). auto.
  - apply (source_full_exists_left_decoration M u v l domain domain1 theta tail input inner matrix body ex
      HD HS HI HM HB HE).
    apply (source_full_modus_ponens M u v l left ex forward HF).
    + exact (source_full_prv_weaken_bounded M b c n u v l forward _ PForward
        ltac:(intros f H;apply (proj2 (context_member_cons M b c n left u v l f HCons));now right) HBranch).
    + apply full_source_Ctx;[exists (succM M k);auto|].
      apply (proj2 (context_member_cons M b c n left u v l left HCons)). now left.
  - exact HCons.
  - exact HT.
Qed.

Theorem source_full_replacement_decoration_members M b c n domain domain1 theta tail input inner matrix body ex
    left forward reverse point profile targetpoint targetall :
  source_bounded M domain (code_numeral M 1) ->source_formula_shift M domain domain1 ->
  sf_relation M SFAnd domain1 theta inner ->sf_relation M SFAnd inner tail matrix ->
  sf_relation M SFAnd input matrix body ->sf_relation M SFEx body (zeroM M) ex ->
  sf_relation M SFImpl left ex forward ->sf_relation M SFAnd forward reverse point ->
  sf_relation M SFAll point (zeroM M) profile ->
  sf_relation M SFImpl left domain targetpoint ->sf_relation M SFAll targetpoint (zeroM M) targetall ->
  source_full_prv M b c n profile ->source_full_prv M b c n targetall.
Proof.
  intros HD HS HI HM HB HE HF HP HProfile HT HA PProfile.
  destruct (source_full_prv_wellformed M b c n profile PProfile) as (k&HProfileBound&HC).
  pose proof (proj1 (source_bounded_accept_unary M SFAll point profile k
    (or_introl eq_refl) HProfile) HProfileBound) as HPoint.
  pose proof (proj1 (proj1 (source_bounded_accept_binary M SFAnd forward reverse point _
    (or_introl eq_refl) HP) HPoint)) as HForward.
  pose proof (proj1 (proj1 (source_bounded_accept_binary M SFImpl left ex forward _
    (or_intror (or_intror eq_refl)) HF) HForward)) as HL.
  assert (HTargetBound:source_bounded M targetall k).
  { apply (proj2 (source_bounded_accept_unary M SFAll targetpoint targetall k (or_introl eq_refl) HA)).
    apply (proj2 (source_bounded_accept_binary M SFImpl left domain targetpoint (succM M k)
      (or_intror (or_intror eq_refl)) HT)). split;[exact HL|exact (sr_domain_bound_succ M domain k HD)]. }
  destruct (context_shift_total M b c n) as (s&t&HCShift).
  apply (full_source_AllI M b c n targetpoint targetall s t
    (ex_intro _ k (conj HTargetBound HC)));[|exact HCShift|exact HA].
  exact (source_full_replacement_decoration_point M s t n domain domain1 theta tail input inner matrix body ex
    left forward reverse point targetpoint HD HS HI HM HB HE HF HP HT
    (source_full_all_shift M b c n point profile s t HProfile PProfile HCShift)).
Qed.

Print Assumptions source_full_exists_left_decoration.
Print Assumptions source_full_replacement_decoration_point.
Print Assumptions source_full_replacement_decoration_members.
