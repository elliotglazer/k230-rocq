(** Bounds for the literal initial ordinal-collection hypotheses. The
    predicate and parameter count may be nonstandard PA-model elements. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded SourceBoundMonotone SourceRelativizationBounds SourceRenamingBounds
  SourceFiniteCutoffShift SourceOrdinalPredicate SourceDomainInstances SourcePropositionalTemplates
  SourceOrdinalInitialTotality SourceOrdinalInitialMonotonicity SourceOrdinalInitialMonoMaps
  NumericalRenamingMaps SourceOrdinalMonotoneMaps SourceOrdinalMonotoneUse SourceOrdinalUpperMembers.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_oc_initial_totality_bounded M phi total count :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_initial_totality_graph M phi total ->source_bounded M total (succM M count).
Proof.
  intros HB (phiD&body&ex&input&point&HD&HBod&HE&HI&HP&HT).
  pose proof (source_cutoff_shift_bounded M 2 phi phiD count HB HD) as HBD.
  apply (proj2 (source_bounded_accept_unary M SFAll point total (succM M count)
    (or_introl eq_refl) HT)).
  apply (proj2 (source_bounded_accept_binary M SFImpl input ex point (succM M (succM M count))
    (or_intror (or_intror eq_refl)) HP)). split.
  - apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M) (code_numeral M 1) input
      (succM M (succM M count)) (or_introl eq_refl) HI)).
    split;[apply coding_zero_lt_succ|].
    apply (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M count))). apply coding_zero_lt_succ.
  - apply (proj2 (source_bounded_accept_unary M SFEx body ex (succM M (succM M count))
      (or_intror eq_refl) HE)).
    apply (proj2 (source_bounded_accept_binary M SFAnd (source_ordinal_predicate_code M) phiD body
      (succM M (succM M (succM M count))) (or_introl eq_refl) HBod)).
    split;[apply sr_domain_bound_succ,source_ordinal_predicate_bounded|exact HBD].
Qed.

Lemma source_oc_initial_mono_matrix_bounded M right phi row count :
  source_bounded M phi (succM M (succM M count)) ->source_oc_initial_mono_matrix M right phi row ->
  source_bounded M row (succM M (succM M (succM M (succM M count)))).
Proof.
  intros HB HR. apply (numerical_renaming_preserves_bound M phi
    (code_numeral M (source_oc_mono_dividend right)) (code_numeral M 3)
    (code_numeral M 2) (code_numeral M 2) row (succM M (succM M count))
    (succM M (succM M (succM M (succM M count)))) HB HR).
  intros i j HI HJ.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[idx E]];subst i.
  - pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HJ
      (source_oc_initial_mono_first M right)) as E. subst j.
    destruct right;cbn [source_oc_mono_first code_numeral];
      try apply coding_zero_lt_succ.
    apply (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M (succM M (succM M count))))).
    apply coding_zero_lt_succ.
  - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) idx) as [E|[tail E]];subst idx.
    + pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HJ
        (source_oc_initial_mono_second M right)) as E. subst j.
      apply (proj2 (coding_lt_succ_cancel M (code_numeral M 1) (succM M (succM M (succM M count))))).
      apply (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M (succM M count)))).
      apply coding_zero_lt_succ.
    + pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HJ
        (source_oc_initial_mono_tail M right tail)) as E. subst j.
      repeat apply (proj2 (coding_lt_succ_cancel M _ _)).
      exact (proj1 (coding_lt_succ_cancel M tail count)
        (proj1 (coding_lt_succ_cancel M (succM M tail) (succM M count)) HI)).
Qed.

Theorem source_oc_initial_monotonicity_bounded M phi mono count :
  source_bounded M phi (succM M (succM M count)) ->
  source_oc_initial_monotonicity_graph M phi mono ->source_bounded M mono (succM M count).
Proof.
  intros HB (left&right&ordD&subset&point&inner&middle&HL&HR&HD&HS&HP&HI&HM&HO).
  pose proof (source_oc_initial_mono_matrix_bounded M false phi left count HB HL) as HBL.
  pose proof (source_oc_initial_mono_matrix_bounded M true phi right count HB HR) as HBR.
  set (k:=succM M (succM M (succM M (succM M count)))).
  assert (HOrdD:source_bounded M ordD k).
  { apply (source_domain_instance_bound M (source_ordinal_predicate_code M) (code_numeral M 1) ordD k
      (source_ordinal_predicate_bounded M));[|exact HD].
    apply (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M (succM M (succM M count))))).
    apply coding_zero_lt_succ. }
  assert (HOrd:source_bounded M (source_ordinal_predicate_code M) k).
  { apply sr_domain_bound_succ,source_ordinal_predicate_bounded. }
  assert (HSubset:source_bounded M subset k).
  { destruct HS as (a&d&p&HA&HDD&HPP&HAll).
    apply (proj2 (source_bounded_accept_unary M SFAll p subset k (or_introl eq_refl) HAll)).
    apply (proj2 (source_bounded_accept_binary M SFImpl a d p (succM M k)
      (or_intror (or_intror eq_refl)) HPP)). split.
    - apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M) (code_numeral M 2) a
        (succM M k) (or_introl eq_refl) HA)). split;[apply coding_zero_lt_succ|].
      apply (proj2 (coding_lt_succ_cancel M (code_numeral M 1) k)).
      apply (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M (succM M (succM M count))))).
      apply coding_zero_lt_succ.
    - apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M) (code_numeral M 1) d
        (succM M k) (or_introl eq_refl) HDD)). split;[apply coding_zero_lt_succ|].
      apply (proj2 (coding_lt_succ_cancel M (zeroM M) k)). apply coding_zero_lt_succ. }
  apply (proj2 (source_bounded_accept_unary M SFAll middle mono (succM M count) (or_introl eq_refl) HO)).
  apply (proj2 (source_bounded_accept_unary M SFAll inner middle (succM M (succM M count)) (or_introl eq_refl) HM)).
  apply (proj2 (source_bounded_accept_unary M SFAll point inner (succM M (succM M (succM M count)))
    (or_introl eq_refl) HI)).
  apply (source_prop_template_bound M (source_oc_mono_environment ordD (source_ordinal_predicate_code M)
    subset left right) source_oc_mono_template k);[|exact HP].
  intros [|[|[|[|i]]]];cbn [source_oc_mono_environment];assumption.
Qed.

Print Assumptions source_oc_initial_totality_bounded.
Print Assumptions source_oc_initial_monotonicity_bounded.
