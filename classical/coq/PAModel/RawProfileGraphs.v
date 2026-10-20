(** The exact arithmetic decomposition of one raw Collection profile.
    These are syntax-code witnesses, not semantic witnesses for its existentials. *)
From PAModel Require Import Model FiniteCoding CodeDescent CodeExpressions NumericalProofs
  NumericalVacuitySteps NamedLeibnizSteps QuotationPayloads QuotationFixedSource
  SetFormulaCodes StableContextSupport RawCollectionProfile RawClauseAlpha.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition raw_profile_parts M t a c u v theta profile dom coverage support allcoverage allsupport both :=
  membership_graph M t c dom /\
  code_relation M (raw_clause_parameters M t a c u v theta) E_raw_coverage_clause coverage /\
  code_relation M (raw_clause_parameters M t a c u v theta) E_raw_support_clause support /\
  universal_graph M u coverage allcoverage /\ universal_graph M v support allsupport /\
  quotation_binary M SFAnd allcoverage allsupport both /\ quotation_binary M SFAnd dom both profile.

Theorem raw_profile_parts_of_code M t a c u v theta profile :
  code_relation M (raw_clause_parameters M t a c u v theta)
    (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) profile ->
  exists dom coverage support allcoverage allsupport both,
    raw_profile_parts M t a c u v theta profile dom coverage support allcoverage allsupport both.
Proof.
  intro HP;set (rho:=raw_clause_parameters M t a c u v theta).
  destruct (code_relation_total M (E_wel (CEvar 0) (CEvar 2)) rho) as [dom HD].
  destruct (code_relation_total M E_raw_coverage_clause rho) as [coverage HC].
  destruct (code_relation_total M E_raw_support_clause rho) as [support HS].
  destruct (code_relation_total M (E_wal (CEvar 3) E_raw_coverage_clause) rho) as [allcoverage HAC].
  destruct (code_relation_total M (E_wal (CEvar 4) E_raw_support_clause) rho) as [allsupport HAS].
  destruct (code_relation_total M (E_wa (E_wal (CEvar 3) E_raw_coverage_clause)
    (E_wal (CEvar 4) E_raw_support_clause)) rho) as [both HB].
  exists dom,coverage,support,allcoverage,allsupport,both.
  split.
  - exact (proj1 (ns_atom_expression M rho false (CEvar 0) (CEvar 2) t c dom eq_refl eq_refl) HD).
  - split;[exact HC|]. split;[exact HS|].
    split.
    + exact (proj1 (expression_universal_iff M rho (CEvar 3) E_raw_coverage_clause u coverage allcoverage eq_refl HC) HAC).
    + split.
      * exact (proj1 (expression_universal_iff M rho (CEvar 4) E_raw_support_clause v support allsupport eq_refl HS) HAS).
      * split.
        -- exact (proj1 (quotation_binary_substitution_graph M rho SFAnd
            (E_wal (CEvar 3) E_raw_coverage_clause) (E_wal (CEvar 4) E_raw_support_clause)
            allcoverage allsupport both HAC HAS) HB).
        -- exact (proj1 (quotation_binary_substitution_graph M rho SFAnd (E_wel (CEvar 0) (CEvar 2))
            (E_wa (E_wal (CEvar 3) E_raw_coverage_clause) (E_wal (CEvar 4) E_raw_support_clause))
            dom both profile HD HB) HP).
Qed.

Theorem stable_raw_profile_parts M cb cc cn t a c u v theta profile dom coverage support allcoverage allsupport both :
  raw_profile_parts M t a c u v theta profile dom coverage support allcoverage allsupport both ->
  stable_context_support M cb cc cn profile ->
  stable_context_support M cb cc cn dom /\ stable_context_support M cb cc cn allcoverage /\
    stable_context_support M cb cc cn allsupport.
Proof.
  intros [_ [_ [_ [_ [_ [HBoth HProfile]]]]]] PP.
  assert (PB : stable_context_support M cb cc cn both).
  { exact (stable_context_support_conjunction_right M cb cc cn dom both profile HProfile PP). }
  split.
  - exact (stable_context_support_conjunction_left M cb cc cn dom both profile HProfile PP).
  - split.
    + exact (stable_context_support_conjunction_left M cb cc cn allcoverage allsupport both HBoth PB).
    + exact (stable_context_support_conjunction_right M cb cc cn allcoverage allsupport both HBoth PB).
Qed.

Print Assumptions raw_profile_parts_of_code.
Print Assumptions stable_raw_profile_parts.
