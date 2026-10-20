(** Eliminate the domain table while retaining a fixed closed ambient
    source theory context. Nonemptiness is proved in that same context. *)
From PAModel Require Import Model CodeExpressions FiniteCoding NumericalProofs
  NumericalContexts NumericalEnvironments NumericalContextRenaming SourceBounded
  SourceBoundMonotone SourceTraceBounds SourceSequents SetFormulaCodes SourceQuantifierRules NumericalSourceFull
  SourceDomainContexts SourceProofWeakening SourceClosedShift SourceDomainDischarge
  ContextCombination ContextUnionRenaming SourceClosedContextShift.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_ambient_domain_discharge_at M domain f gb gc gn k := forall db dc ub uc ul,
  source_domain_context M domain k db dc -> context_union M gb gc gn db dc k ub uc ul ->
  source_full_prv M ub uc ul f -> source_full_prv M gb gc gn f.
Definition source_ambient_domain_discharge_formula : form :=
  ∀∀∀∀∀ (source_domain_context_formula $6 $5 $4 $3 →
    context_union_formula $8 $9 $10 $4 $3 $5 $2 $1 $0 →
    source_full_prv_formula $2 $1 $0 $7 → source_full_prv_formula $8 $9 $10 $7).
Local Opaque holds source_domain_context_formula context_union_formula source_full_prv_formula.

Theorem source_ambient_domain_discharge_definable M domain f gb gc gn :
  Definable1 M (source_ambient_domain_discharge_at M domain f gb gc gn).
Proof.
  exists source_ambient_domain_discharge_formula,
    (domain .: f .: gb .: gc .: gn .: fun _=>zeroM M). intro k.
  unfold source_ambient_domain_discharge_formula,source_ambient_domain_discharge_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_domain_context_formula_correct.
  setoid_rewrite context_union_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. reflexivity.
Qed.

Theorem source_ambient_domain_table_discharge M domain ex f gb gc gn :
  context_bounded M gb gc gn (zeroM M) ->
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex -> source_full_prv M gb gc gn ex ->
  source_bounded M f (zeroM M) ->
  forall k db dc ub uc ul,source_domain_context M domain k db dc ->
    context_union M gb gc gn db dc k ub uc ul ->
    source_full_prv M ub uc ul f -> source_full_prv M gb gc gn f.
Proof.
  intros HClosed HD HEx PEx HF.
  apply (definable_induction M (source_ambient_domain_discharge_at M domain f gb gc gn)
    (source_ambient_domain_discharge_definable M domain f gb gc gn)).
  - intros db dc ub uc ul HT HU P.
    apply (source_full_prv_weaken_bounded M ub uc ul gb gc gn f (zeroM M) P);[|exact HClosed].
    intros a HA. apply (proj2 HU a) in HA. destruct HA as [HA|HA];[exact HA|].
    exfalso. exact (context_empty M db dc a HA).
  - intros k IH db dc ub uc ul HT HU P.
    destruct (source_domain_context_total M domain k) as [tb [tc HTable]].
    destruct (context_union_total M gb gc gn tb tc k) as [vb [vc [vl HUnion]]].
    destruct (context_shift_total M tb tc k) as [tsb [tsc HTableShift]].
    destruct (context_shift_total M vb vc vl) as [vsb [vsc HUnionShift]].
    destruct (environment_cons_total M tsb tsc k domain) as [tb' [tc' [tk' HTableCons]]].
    assert (ET:tk'=succM M k) by exact (proj1 HTableCons). subst tk'.
    destruct (environment_cons_total M vsb vsc vl domain) as [wb [wc [wl HUnionCons]]].
    pose proof (source_domain_context_cons_shift M domain k tb tc tsb tsc tb' tc'
      (succM M k) HD HTable HTableShift HTableCons) as HCanonical.
    pose proof (context_union_renaming M gb gc gn tb tc k vb vc vl
      (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) gb gc tsb tsc vsb vsc
      HUnion (source_closed_context_shift_self M gb gc gn HClosed) HTableShift HUnionShift) as HShiftedUnion.
    pose proof (context_union_cons_right M gb gc gn tsb tsc k vsb vsc vl domain
      tb' tc' (succM M k) wb wc wl HShiftedUnion HTableCons HUnionCons) as HBranchUnion.
    assert (HContext:context_bounded M vb vc vl k).
    { apply (source_context_union_bounded M gb gc gn tb tc k vb vc vl k HUnion).
      - exact (context_bounded_monotone M gb gc gn (zeroM M) k HClosed (coding_zero_lt_succ M k)).
      - exact (source_domain_context_bounded M domain k tb tc HD HTable). }
    assert (HBranchContext:context_bounded M wb wc wl (succM M k)).
    { apply (source_context_union_bounded M gb gc gn tb' tc' (succM M k) wb wc wl
        (succM M k) HBranchUnion).
      - exact (context_bounded_monotone M gb gc gn (zeroM M) (succM M k) HClosed
          (coding_zero_lt_succ M (succM M k))).
      - exact (source_domain_context_bounded M domain (succM M k) tb' tc' HD HCanonical). }
    assert (PBranch:source_full_prv M wb wc wl f).
    { apply (source_full_prv_weaken_bounded M ub uc ul wb wc wl f (succM M k) P);[|exact HBranchContext].
      intros a HA. apply (proj2 HU a) in HA. apply (proj2 (proj2 HBranchUnion a)).
      destruct HA as [HA|HA];[now left|right].
      exact (source_domain_context_representation_included M domain (succM M k) db dc tb' tc' HT HCanonical a HA). }
    assert (PExist:source_full_prv M vb vc vl ex).
    { apply (source_full_prv_weaken_bounded M gb gc gn vb vc vl ex k PEx);[|exact HContext].
      exact (context_union_left M gb gc gn tb tc k vb vc vl HUnion). }
    apply (IH tb tc vb vc vl HTable HUnion).
    apply (full_source_ExE M vb vc vl domain ex f f vsb vsc wb wc wl).
    + exists k. split;[|exact HContext].
      exact (source_bounded_monotone M f (zeroM M) k HF (coding_zero_lt_succ M k)).
    + exact PExist.
    + exact PBranch.
    + exact HEx.
    + exact HUnionShift.
    + exact HUnionCons.
    + exact (source_closed_shift_self M f HF).
Qed.

Print Assumptions source_ambient_domain_discharge_definable.
Print Assumptions source_ambient_domain_table_discharge.
