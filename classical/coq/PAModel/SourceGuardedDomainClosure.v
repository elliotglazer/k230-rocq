(** Close an internally finite table of domain hypotheses by actual guarded
    AllI rules. The ambient theory context is closed, and the induction
    predicate is arithmetic. No free domain assumption is silently erased. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  NumericalContexts NumericalEnvironments NumericalContextRenaming SourceBounded
  SourceBoundMonotone SourceTraceBounds SourceSequents SetFormulaCodes SourceQuantifierRules
  NumericalSourceFull NumericalSetClosure SourceProofWeakening SourceDomainContexts
  SourceDomainDischarge ContextCombination ContextUnionRenaming SourceClosedContextShift
  SourceRelativizationRules SourceRelativization SourceRelativizationFunctionality
  SourceRelativizationBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_prefix_body_all_at M body all n :=forall result,
  all_prefix M n all result ->all_prefix M (succM M n) body result.
Definition source_prefix_body_all_formula :form :=
  ∀(all_prefix_formula $1 $3 $0 →all_prefix_formula (σ $1) $2 $0).
Local Opaque holds all_prefix_formula.

Lemma source_prefix_body_all_definable M body all :
  Definable1 M (source_prefix_body_all_at M body all).
Proof.
  exists source_prefix_body_all_formula,(body .:all .:fun _=>zeroM M). intro n.
  unfold source_prefix_body_all_formula,source_prefix_body_all_at.
  setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite all_prefix_formula_correct. reflexivity.
Qed.

Theorem all_prefix_move_first M body all :sf_relation M SFAll body (zeroM M) all ->
  forall n,source_prefix_body_all_at M body all n.
Proof.
  intro HAll. apply(definable_induction M (source_prefix_body_all_at M body all)
    (source_prefix_body_all_definable M body all)).
  - intros result HP. apply all_prefix_zero_forward in HP. subst result.
    apply all_prefix_succ. exists body. split;[apply all_prefix_zero;reflexivity|exact HAll].
  - intros n IH result HP.
    destruct(all_prefix_succ_forward M n all result HP) as(previous&HPrevious&HOut).
    apply all_prefix_succ. exists previous. split;[exact(IH previous HPrevious)|exact HOut].
Qed.

Theorem all_prefix_remove_first M n body all result :
  sf_relation M SFAll body (zeroM M) all ->all_prefix M (succM M n) body result ->
  all_prefix M n all result.
Proof.
  intros HAll HP. destruct(all_prefix_total M n all) as(other&HO).
  pose proof(all_prefix_move_first M body all HAll n other HO) as HX.
  pose proof(all_prefix_functional M (succM M n) body other result HX HP) as E.
  now subst other.
Qed.

Definition source_guarded_domain_close_at M domain gb gc gn k :=
  forall body relative result rresult db dc ub uc ul,
  source_bounded M body k ->all_prefix M k body result ->
  source_relativization M domain body relative ->
  source_relativization M domain result rresult ->
  source_domain_context M domain k db dc ->context_union M gb gc gn db dc k ub uc ul ->
  source_full_prv M ub uc ul relative ->source_full_prv M gb gc gn rresult.
Definition source_guarded_domain_close_formula :form :=
  ∀∀∀∀∀∀∀∀∀(source_bounded_accept_formula $8 $9 →all_prefix_formula $9 $8 $6 →
    source_relativization_formula $10 $8 $7 →source_relativization_formula $10 $6 $5 →
    source_domain_context_formula $10 $9 $4 $3 →
    context_union_formula $11 $12 $13 $4 $3 $9 $2 $1 $0 →
    source_full_prv_formula $2 $1 $0 $7 →source_full_prv_formula $11 $12 $13 $5).
Local Opaque source_bounded_accept_formula source_relativization_formula
  source_domain_context_formula context_union_formula source_full_prv_formula.

Lemma source_guarded_domain_close_definable M domain gb gc gn :
  Definable1 M (source_guarded_domain_close_at M domain gb gc gn).
Proof.
  exists source_guarded_domain_close_formula,(domain .:gb .:gc .:gn .:fun _=>zeroM M). intro k.
  unfold source_guarded_domain_close_formula,source_guarded_domain_close_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite all_prefix_formula_correct.
  setoid_rewrite source_relativization_formula_correct.
  setoid_rewrite source_domain_context_formula_correct. setoid_rewrite context_union_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. reflexivity.
Qed.

Theorem source_full_guarded_domain_close M domain gb gc gn :
  context_bounded M gb gc gn (zeroM M) ->source_bounded M domain (code_numeral M 1) ->
  forall k,source_guarded_domain_close_at M domain gb gc gn k.
Proof.
  intros HClosed HD.
  apply(definable_induction M (source_guarded_domain_close_at M domain gb gc gn)
    (source_guarded_domain_close_definable M domain gb gc gn)).
  - intros body relative result rresult db dc ub uc ul HB HP HR HResult HT HU P.
    apply all_prefix_zero_forward in HP. subst result.
    pose proof(source_relativization_functional M body domain relative rresult HR HResult) as E.
    subst rresult. apply(source_full_prv_weaken_bounded M ub uc ul gb gc gn relative (zeroM M) P);
      [|exact HClosed].
    intros a HA. apply(proj2 HU a) in HA. destruct HA as[HA|HA];[exact HA|].
    exfalso. exact(context_empty M db dc a HA).
  - intros k IH body relative result rresult db dc ub uc ul HB HP HR HResult HT HU P.
    destruct(sf_relation_total M SFAll body (zeroM M)) as(all&HAll).
    destruct(source_relativization_total M domain all) as(rall&HRAll).
    destruct(source_relativization_quantifier_inv M domain true body all rall HAll HRAll)
      as(rbody&HRBody&guard&HGuard&HOutput).
    pose proof(source_relativization_functional M body domain relative rbody HR HRBody) as ER.
    subst rbody.
    destruct(source_domain_context_total M domain k) as(tb&tc&HTable).
    destruct(context_union_total M gb gc gn tb tc k) as(vb&vc&vl&HUnion).
    destruct(context_shift_total M tb tc k) as(tsb&tsc&HTableShift).
    destruct(context_shift_total M vb vc vl) as(vsb&vsc&HUnionShift).
    destruct(environment_cons_total M tsb tsc k domain) as(tb'&tc'&tk'&HTableCons).
    assert(ET:tk'=succM M k) by exact(proj1 HTableCons). subst tk'.
    destruct(environment_cons_total M vsb vsc vl domain) as(wb&wc&wl&HUnionCons).
    pose proof(source_domain_context_cons_shift M domain k tb tc tsb tsc tb' tc'
      (succM M k) HD HTable HTableShift HTableCons) as HCanonical.
    pose proof(context_union_renaming M gb gc gn tb tc k vb vc vl
      (zeroM M)(zeroM M)(zeroM M)(succM M(zeroM M)) gb gc tsb tsc vsb vsc
      HUnion (source_closed_context_shift_self M gb gc gn HClosed) HTableShift HUnionShift)
      as HShiftedUnion.
    pose proof(context_union_cons_right M gb gc gn tsb tsc k vsb vsc vl domain
      tb' tc' (succM M k) wb wc wl HShiftedUnion HTableCons HUnionCons) as HBranchUnion.
    assert(HContext:context_bounded M vb vc vl k).
    { apply(source_context_union_bounded M gb gc gn tb tc k vb vc vl k HUnion).
      - exact(context_bounded_monotone M gb gc gn (zeroM M) k HClosed (coding_zero_lt_succ M k)).
      - exact(source_domain_context_bounded M domain k tb tc HD HTable). }
    assert(HShiftContext:context_bounded M vsb vsc vl (succM M k)).
    { exact(context_shift_preserves_bound M vb vc vl vsb vsc k HUnionShift HContext). }
    assert(HBranchContext:context_bounded M wb wc wl (succM M k)).
    { apply(proj2(context_bounded_cons M vsb vsc vl domain wb wc wl (succM M k) HUnionCons)).
      split;[exact(sr_domain_bound_succ M domain k HD)|exact HShiftContext]. }
    assert(PBranch:source_full_prv M wb wc wl relative).
    { apply(source_full_prv_weaken_bounded M ub uc ul wb wc wl relative (succM M k) P);
        [|exact HBranchContext].
      intros a HA. apply(proj2 HU a) in HA. apply(proj2(proj2 HBranchUnion a)).
      destruct HA as[HA|HA];[now left|right].
      exact(source_domain_context_representation_included M domain (succM M k)
        db dc tb' tc' HT HCanonical a HA). }
    pose proof(source_relativization_preserves_bound M body domain (succM M k) relative HD HB HR)
      as HRelative.
    assert(HGuardBound:source_bounded M guard (succM M k)).
    { apply(proj2(source_bounded_accept_binary M SFImpl domain relative guard (succM M k)
        (or_intror(or_intror eq_refl)) HGuard)). split;[exact(sr_domain_bound_succ M domain k HD)|exact HRelative]. }
    assert(PGuard:source_full_prv M vsb vsc vl guard).
    { apply(full_source_II M vsb vsc vl domain relative guard wb wc wl).
      - exists(succM M k). split;assumption.
      - exact PBranch.
      - exact HUnionCons.
      - exact HGuard. }
    assert(PAll:source_full_prv M vb vc vl rall).
    { apply(full_source_AllI M vb vc vl guard rall vsb vsc).
      - exists k. split;[|exact HContext].
        exact(proj2(source_bounded_accept_unary M SFAll guard rall k (or_introl eq_refl) HOutput) HGuardBound).
      - exact PGuard.
      - exact HUnionShift.
      - exact HOutput. }
    apply(IH all rall result rresult tb tc vb vc vl).
    + exact(proj2(source_bounded_accept_unary M SFAll body all k (or_introl eq_refl) HAll) HB).
    + exact(all_prefix_remove_first M k body all result HAll HP).
    + exact HRAll.
    + exact HResult.
    + exact HTable.
    + exact HUnion.
    + exact PAll.
Qed.

Print Assumptions all_prefix_move_first.
Print Assumptions source_guarded_domain_close_definable.
Print Assumptions source_full_guarded_domain_close.
