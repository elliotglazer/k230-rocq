(** The raw guarded Replacement profile proves that all members of its
    output satisfy the domain predicate. No extensionality is used. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded SourceBoundMonotone NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalSourceFull SourceQuantifierRules SourceTraceBounds
  SourceRelativizationBounds SourceProofWeakening SourceContextTransport SourceDerivedRules
  SourceUniversalPropositional SourceConjunctionRules SourceWFReplacementExistsMember.
Unset Implicit Arguments.

Theorem source_full_replacement_member_point M b c n domain domain1 theta input guards matrix body ex
    left forward reverse point target :
  source_bounded M domain (code_numeral M 1) ->source_formula_shift M domain domain1 ->
  sf_relation M SFAnd domain domain1 guards ->sf_relation M SFAnd guards theta matrix ->
  sf_relation M SFAnd input matrix body ->sf_relation M SFEx body (zeroM M) ex ->
  sf_relation M SFImpl left ex forward ->sf_relation M SFAnd forward reverse point ->
  sf_relation M SFImpl left domain target ->source_full_prv M b c n point ->
  source_full_prv M b c n target.
Proof.
  intros HD HS HG HM HB HE HF HP HT PPoint.
  pose proof (source_full_conjunction_left M b c n forward reverse point HP PPoint) as PForward.
  destruct (source_full_prv_wellformed M b c n forward PForward) as [k [HForward HC]].
  pose proof (proj1 (proj1 (source_bounded_accept_binary M SFImpl left ex forward k
    (or_intror (or_intror eq_refl)) HF) HForward)) as HL.
  assert (HLe:coding_lt M k (succM M (succM M k)))
    by (apply coding_lt_succ_cases;left;apply coding_lt_succ).
  pose proof (context_bounded_monotone M b c n k (succM M k) HC HLe) as HC'.
  pose proof (source_bounded_monotone M left k (succM M k) HL HLe) as HL'.
  pose proof (sr_domain_bound_succ M domain k HD) as HD'.
  destruct (environment_cons_total M b c n left) as [u [v [l HCons]]].
  assert (HBranch:context_bounded M u v l (succM M k))
    by exact (proj2 (context_bounded_cons M b c n left u v l _ HCons) (conj HL' HC')).
  apply (full_source_II M b c n left domain target u v l).
  - exists (succM M k). split;[|exact HC'].
    apply (proj2 (source_bounded_accept_binary M SFImpl left domain target _
      (or_intror (or_intror eq_refl)) HT)). now split.
  - apply (source_full_replacement_exists_domain M u v l domain domain1 theta input guards matrix body ex
      HD HS HG HM HB HE).
    apply (source_full_modus_ponens M u v l left ex forward HF).
    + apply (source_full_prv_weaken_bounded M b c n u v l forward (succM M k) PForward);[|exact HBranch].
      intros f H. apply (proj2 (context_member_cons M b c n left u v l f HCons)). now right.
    + apply (full_source_Ctx M u v l left).
      * exists (succM M k). now split.
      * apply (proj2 (context_member_cons M b c n left u v l left HCons)). now left.
  - exact HCons.
  - exact HT.
Qed.

Theorem source_full_replacement_members M b c n domain domain1 theta input guards matrix body ex
    left forward reverse point profile targetpoint targetall :
  source_bounded M domain (code_numeral M 1) ->source_formula_shift M domain domain1 ->
  sf_relation M SFAnd domain domain1 guards ->sf_relation M SFAnd guards theta matrix ->
  sf_relation M SFAnd input matrix body ->sf_relation M SFEx body (zeroM M) ex ->
  sf_relation M SFImpl left ex forward ->sf_relation M SFAnd forward reverse point ->
  sf_relation M SFAll point (zeroM M) profile ->
  sf_relation M SFImpl left domain targetpoint ->sf_relation M SFAll targetpoint (zeroM M) targetall ->
  source_full_prv M b c n profile ->source_full_prv M b c n targetall.
Proof.
  intros HD HS HG HM HB HE HF HP HProfile HT HA PProfile.
  destruct (source_full_prv_wellformed M b c n profile PProfile) as [k [HProfileBound HC]].
  pose proof (proj1 (source_bounded_accept_unary M SFAll point profile k (or_introl eq_refl) HProfile)
    HProfileBound) as HPoint.
  pose proof (proj1 (proj1 (source_bounded_accept_binary M SFAnd forward reverse point _
    (or_introl eq_refl) HP) HPoint)) as HForward.
  pose proof (proj1 (proj1 (source_bounded_accept_binary M SFImpl left ex forward _
    (or_intror (or_intror eq_refl)) HF) HForward)) as HL.
  assert (HTargetBound:source_bounded M targetall k).
  { apply (proj2 (source_bounded_accept_unary M SFAll targetpoint targetall k (or_introl eq_refl) HA)).
    apply (proj2 (source_bounded_accept_binary M SFImpl left domain targetpoint (succM M k)
      (or_intror (or_intror eq_refl)) HT)). split;[exact HL|exact (sr_domain_bound_succ M domain k HD)]. }
  destruct (context_shift_total M b c n) as [s [t HCShift]].
  apply (full_source_AllI M b c n targetpoint targetall s t
    (ex_intro _ k (conj HTargetBound HC)));[|exact HCShift|exact HA].
  exact (source_full_replacement_member_point M s t n domain domain1 theta input guards matrix body ex
    left forward reverse point targetpoint HD HS HG HM HB HE HF HP HT
    (source_full_all_shift M b c n point profile s t HProfile PProfile HCShift)).
Qed.

Print Assumptions source_full_replacement_member_point.
Print Assumptions source_full_replacement_members.
