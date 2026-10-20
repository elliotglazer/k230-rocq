(** Closing internally many domain-restricted universals from an actual
    open image proof. No domain-truth/nonemptiness premise is needed. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs NumericalSetClosure NumericalContexts NumericalEnvironments
  SetFormulaCodes SourceBounded SourceBoundMonotone SourceTraceBounds SourceSequents NumericalSourceFull
  SourceProofWeakening SourceClosedPrefixes SourceRelativizationRules
  SourceRelativization SourceRelativizationFunctionality SourceRelativizationBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Theorem source_full_domain_implication M domain b c n a guard :
  source_bounded M domain (code_numeral M 1) ->
  source_full_prv M b c n a -> sf_relation M SFImpl domain a guard ->
  source_full_prv M b c n guard.
Proof.
  intros HD PA HG.
  destruct (source_full_prv_wellformed M b c n a PA) as [k [HA HC]].
  assert (HStep:coding_lt M k (succM M (succM M k))).
  { apply coding_lt_succ_cases. left. apply coding_lt_succ. }
  assert (HA':source_bounded M a (succM M k)).
  { exact (source_bounded_monotone M a k (succM M k) HA HStep). }
  assert (HC':context_bounded M b c n (succM M k)).
  { exact (context_bounded_monotone M b c n k (succM M k) HC HStep). }
  pose proof (sr_domain_bound_succ M domain k HD) as HD'.
  destruct (environment_cons_total M b c n domain) as [u [v [l HCons]]].
  apply (full_source_II M b c n domain a guard u v l).
  - exists (succM M k). split;[|exact HC'].
    apply (proj2 (source_bounded_accept_binary M SFImpl domain a guard (succM M k)
      (or_intror (or_intror eq_refl)) HG)). split;assumption.
  - apply (source_full_prv_weaken_bounded M b c n u v l a (succM M k) PA).
    + intros h HH. apply (proj2 (context_member_cons M b c n domain u v l h HCons)). now right.
    + apply (proj2 (context_bounded_cons M b c n domain u v l (succM M k) HCons)).
      split;assumption.
  - exact HCons.
  - exact HG.
Qed.

Definition source_guarded_prefix_at M domain b c l body rbody n := forall f rf,
  all_prefix M n body f -> source_relativization M domain f rf ->
  source_full_prv M b c l rbody -> source_full_prv M b c l rf.
Definition source_guarded_prefix_formula : form :=
  ∀∀(all_prefix_formula $2 $7 $1 → source_relativization_formula $3 $1 $0 →
    source_full_prv_formula $4 $5 $6 $8 → source_full_prv_formula $4 $5 $6 $0).
Local Opaque holds all_prefix_formula source_relativization_formula source_full_prv_formula.

Lemma source_guarded_prefix_definable M domain b c l body rbody :
  Definable1 M (source_guarded_prefix_at M domain b c l body rbody).
Proof.
  exists source_guarded_prefix_formula,
    (domain .: b .: c .: l .: body .: rbody .: fun _=>zeroM M). intro n.
  unfold source_guarded_prefix_at,source_guarded_prefix_formula.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite all_prefix_formula_correct. setoid_rewrite source_relativization_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. reflexivity.
Qed.

Theorem source_full_guarded_prefix M domain b c l body rbody :
  context_bounded M b c l (zeroM M) ->
  source_bounded M domain (code_numeral M 1) -> source_relativization M domain body rbody ->
  forall n,source_guarded_prefix_at M domain b c l body rbody n.
Proof.
  intros HClosed HD HBody.
  apply (definable_induction M (source_guarded_prefix_at M domain b c l body rbody)
    (source_guarded_prefix_definable M domain b c l body rbody)).
  - intros f rf HP HR PB. apply all_prefix_zero_forward in HP. subst f.
    pose proof (source_relativization_functional M body domain rf rbody HR HBody) as E.
    now subst rf.
  - intros n IH f rf HP HR PB.
    destruct (all_prefix_succ_forward M n body f HP) as [previous [HPrevious HAll]].
    destruct (source_relativization_quantifier_inv M domain true previous f rf HAll HR)
      as [rprevious [HRPrevious [guard [HGuard HOutput]]]].
    pose proof (IH previous rprevious HPrevious HRPrevious PB) as PPrevious.
    apply (source_full_all_intro_closed M b c l guard rf HClosed HOutput).
    exact (source_full_domain_implication M domain b c l rprevious guard HD PPrevious HGuard).
Qed.

Print Assumptions source_full_domain_implication.
Print Assumptions source_guarded_prefix_definable.
Print Assumptions source_full_guarded_prefix.
