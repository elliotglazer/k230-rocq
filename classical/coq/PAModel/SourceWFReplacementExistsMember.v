(** Every member of the guarded Replacement range satisfies the domain
    predicate, by literal existential elimination of its input witness. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  SourceBoundMonotone NumericalContexts NumericalEnvironments NumericalContextRenaming
  NumericalSourceFull SourceQuantifierRules SourceRelativizationBounds SourceTraceBounds
  SourceConjunctionRules.
Unset Implicit Arguments.

Theorem source_full_replacement_exists_domain M b c n domain domain1 theta input guards matrix body ex :
  source_bounded M domain (code_numeral M 1) ->source_formula_shift M domain domain1 ->
  sf_relation M SFAnd domain domain1 guards ->sf_relation M SFAnd guards theta matrix ->
  sf_relation M SFAnd input matrix body ->sf_relation M SFEx body (zeroM M) ex ->
  source_full_prv M b c n ex ->source_full_prv M b c n domain.
Proof.
  intros HD HS HG HM HB HE PEx.
  destruct (source_full_prv_wellformed M b c n ex PEx) as [k [HExBound HC]].
  pose proof (proj1 (source_bounded_accept_unary M SFEx body ex k (or_intror eq_refl) HE)
    HExBound) as HBodyBound.
  destruct (context_shift_total M b c n) as [s [t HCtxShift]].
  destruct (environment_cons_total M s t n body) as [u [v [l HCons]]].
  assert (HCShift:context_bounded M s t n (succM M k))
    by exact (context_shift_preserves_bound M b c n s t k HCtxShift HC).
  assert (HBranch:context_bounded M u v l (succM M k)).
  { exact (proj2 (context_bounded_cons M s t n body u v l _ HCons) (conj HBodyBound HCShift)). }
  apply (full_source_ExE M b c n body ex domain domain1 s t u v l).
  - exists (succM M k). split;[exact (sr_domain_bound_succ M domain k HD)|].
    apply (context_bounded_monotone M b c n k (succM M k) HC).
    apply coding_lt_succ_cases. left. apply coding_lt_succ.
  - exact PEx.
  - apply (source_full_conjunction_right M u v l domain domain1 guards HG).
    apply (source_full_conjunction_left M u v l guards theta matrix HM).
    apply (source_full_conjunction_right M u v l input matrix body HB).
    apply (full_source_Ctx M u v l body).
    + exists (succM M k). now split.
    + apply (proj2 (context_member_cons M s t n body u v l body HCons)). now left.
  - exact HE.
  - exact HCtxShift.
  - exact HCons.
  - exact HS.
Qed.

Print Assumptions source_full_replacement_exists_domain.
