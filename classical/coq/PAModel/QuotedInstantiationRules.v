(** Guarded quotation rules at the successor fresh base. A source instance
    is quoted at succ(k), not at k. Domain membership is an explicit target
    assumption. Fresh-base conversion remains a separate obligation. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions CodeDescent NamedLeibnizSteps
  NumericalProofs ProofTemplates NumericalVacuity NamedSubstitutionRules NamedSubstitution
  NamedBinderFresh NamedBinderConstructors TemplateNamedSubstitution
  NumericalEnvironments QuotationHygiene QuotationPayloads QuotationRules NumericalQuotation
  QuotationFunctionality QuotationBinderFresh QuotationNamedSubstitution
  ContextualProofs ContextualGuardedQuantifiers SetFormulaCodes SourceBounded
  NumericalInstantiation QuotationInstantiation.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma environment_cons_head_replacement M eb ec en db dc dn fb fc fn k y :
  environment_below M eb ec en k ->
  environment_cons M eb ec en k db dc dn ->
  environment_cons M eb ec en y fb fc fn ->
  environment_named_replace M db dc dn fb fc fn k y.
Proof.
  intros HE HD HF i a a' HA HA'.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [E|[j E]];subst i.
  - apply (proj1 (environment_cons_head M eb ec en k db dc dn a HD)) in HA.
    apply (proj1 (environment_cons_head M eb ec en y fb fc fn a' HF)) in HA'.
    subst a a'. left;auto.
  - apply (proj1 (environment_cons_tail M eb ec en k db dc dn j a HD)) in HA.
    apply (proj1 (environment_cons_tail M eb ec en y fb fc fn j a' HF)) in HA'.
    assert (E : a=a') by exact (environment_lookup_functional M eb ec en j a a' HA HA').
    subst a'. right. split;[|reflexivity].
    intro E. apply (template_lt_different M a k (HE j a HA)). symmetry;exact E.
Qed.

Lemma quoted_cons_head_replacement M f eb ec en db dc dn fb fc fn k domain y body result :
  quotation_safe M eb ec en k domain -> coding_lt M y k ->
  environment_cons M eb ec en k db dc dn ->
  environment_cons M eb ec en y fb fc fn ->
  numerical_quotation M f db dc dn (succM M k) domain body ->
  numerical_quotation M f fb fc fn (succM M k) domain result ->
  named_substitution M body k y result.
Proof.
  intros [Ht HE] Hy HD HF HB HR.
  exact (numerical_quotation_head_replacement M f db dc dn fb fc fn k domain y body result
    Ht Hy (environment_cons_head_replacement M eb ec en db dc dn fb fc fn k y HE HD HF) HB HR).
Qed.

Lemma quoted_domain_named_substitution M domain k y dom dom' :
  coding_lt M domain k -> membership_graph M domain k dom ->
  membership_graph M domain y dom' -> named_substitution M dom k y dom'.
Proof.
  intros Ht HD HD'. apply (ns_combine_atom M false domain k dom domain y dom' k y HD HD').
  - right. split;[|reflexivity]. intro E.
    apply (template_lt_different M domain k Ht). symmetry;exact E.
  - left;auto.
Qed.

Theorem contextual_quoted_all_from_cons M cb cc cn f eb ec en db dc dn fb fc fn
    k domain y body result all dom' :
  quotation_safe M eb ec en k domain -> coding_lt M y k ->
  environment_cons M eb ec en k db dc dn -> environment_cons M eb ec en y fb fc fn ->
  numerical_quotation M f db dc dn (succM M k) domain body ->
  numerical_quotation M f fb fc fn (succM M k) domain result ->
  quotation_quantifier M true k domain body all -> membership_graph M domain y dom' ->
  contextually_provable M cb cc cn all -> contextually_provable M cb cc cn dom' ->
  contextually_provable M cb cc cn result.
Proof.
  intros Hsafe Hy HD HF HB HR HQ Hdom' PAll PD.
  destruct (code_relation_total M (E_wel (CEvar 0) (CEvar 1))
    (domain .: k .: fun _=>zeroM M)) as [dom Hdom].
  apply (proj1 (ns_atom_expression M (domain .: k .: fun _=>zeroM M) false
    (CEvar 0) (CEvar 1) domain k dom eq_refl eq_refl)) in Hdom.
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1)) (arguments2 dom body (zeroM M))) as [guard HG].
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1)) (arguments2 dom' result (zeroM M))) as [guard' HG'].
  assert (Hky : k<>y) by now apply template_lt_different.
  assert (HBk : named_binder_absent M body k).
  { exact (numerical_quotation_matrix_binder_absent M f db dc dn k domain body HB). }
  assert (HBy : named_binder_absent M body y).
  { exact (numerical_quotation_binder_fresh M f db dc dn (succM M k) domain body y HB
      (coding_lt_trans M y k (succM M k) Hy (coding_lt_succ M k))). }
  apply (contextual_guarded_all_specialize_parts M cb cc cn k y domain body result
    dom dom' guard guard' all Hky Hdom Hdom' HG HG').
  - apply (named_binder_absent_implication M dom body guard k HG);[|exact HBk].
    exact (named_binder_absent_membership M domain k dom k Hdom).
  - apply (named_binder_absent_implication M dom body guard y HG);[|exact HBy].
    exact (named_binder_absent_membership M domain k dom y Hdom).
  - exact (quoted_domain_named_substitution M domain k y dom dom' (proj1 Hsafe) Hdom Hdom').
  - exact (quoted_cons_head_replacement M f eb ec en db dc dn fb fc fn k domain y body result
      Hsafe Hy HD HF HB HR).
  - exact HQ.
  - exact PAll.
  - exact PD.
Qed.

Theorem contextual_quoted_exists_from_cons M cb cc cn f eb ec en db dc dn fb fc fn
    k domain y body result ex dom' :
  quotation_safe M eb ec en k domain -> coding_lt M y k ->
  environment_cons M eb ec en k db dc dn -> environment_cons M eb ec en y fb fc fn ->
  numerical_quotation M f db dc dn (succM M k) domain body ->
  numerical_quotation M f fb fc fn (succM M k) domain result ->
  quotation_quantifier M false k domain body ex -> membership_graph M domain y dom' ->
  contextually_provable M cb cc cn result -> contextually_provable M cb cc cn dom' ->
  contextually_provable M cb cc cn ex.
Proof.
  intros Hsafe Hy HD HF HB HR HQ Hdom' PR PD.
  destruct (code_relation_total M (E_wel (CEvar 0) (CEvar 1))
    (domain .: k .: fun _=>zeroM M)) as [dom Hdom].
  apply (proj1 (ns_atom_expression M (domain .: k .: fun _=>zeroM M) false
    (CEvar 0) (CEvar 1) domain k dom eq_refl eq_refl)) in Hdom.
  destruct (quotation_binary_total M SFAnd dom body) as [conj HC].
  destruct (quotation_binary_total M SFAnd dom' result) as [conj' HC'].
  assert (Hky : k<>y) by now apply template_lt_different.
  assert (Hk0 : k<>zeroM M).
  { intro E. subst k. exact (coding_not_lt_zero M y Hy). }
  assert (HBk : named_binder_absent M body k).
  { exact (numerical_quotation_matrix_binder_absent M f db dc dn k domain body HB). }
  assert (HBy : named_binder_absent M body y).
  { exact (numerical_quotation_binder_fresh M f db dc dn (succM M k) domain body y HB
      (coding_lt_trans M y k (succM M k) Hy (coding_lt_succ M k))). }
  apply (contextual_guarded_exists_intro M cb cc cn k y domain body result
    dom dom' conj conj' ex Hky Hdom Hdom' HC HC').
  - apply (quotation_binary_binder_absent M SFAnd dom body conj k HC);[|exact HBk].
    exact (named_binder_absent_membership M domain k dom k Hdom).
  - apply (quotation_binary_binder_absent M SFAnd dom body conj y HC);[|exact HBy].
    exact (named_binder_absent_membership M domain k dom y Hdom).
  - exact (quotation_binary_named_substitution M SFAnd dom body dom' result conj conj' k y Hk0
      (quoted_domain_named_substitution M domain k y dom dom' (proj1 Hsafe) Hdom Hdom')
      (quoted_cons_head_replacement M f eb ec en db dc dn fb fc fn k domain y body result
        Hsafe Hy HD HF HB HR) HC HC').
  - exact HQ.
  - exact PD.
  - exact PR.
Qed.

Theorem contextual_quoted_all_elimination_next M cb cc cn f term g bound h
    eb ec en k domain y all result dom' :
  quotation_safe M eb ec en k domain -> source_bounded M f bound ->
  numerical_instantiation M f term g -> sf_relation M SFAll f (zeroM M) h ->
  environment_lookup M eb ec en term y ->
  numerical_quotation M h eb ec en k domain all ->
  numerical_quotation M g eb ec en (succM M k) domain result ->
  membership_graph M domain y dom' ->
  contextually_provable M cb cc cn all -> contextually_provable M cb cc cn dom' ->
  contextually_provable M cb cc cn result.
Proof.
  intros Hsafe Hbound Hinst Hsource Hlookup HAll HResult Hdom PAll PD.
  destruct (numerical_quotation_unary_inv M true f h eb ec en k domain all Hsource HAll)
    as [db [dc [dn [body [HD [HB HQ]]]]]].
  destruct (environment_cons_total M eb ec en y) as [fb [fc [fn HF]]].
  destruct (numerical_quotation_total M f fb fc fn (succM M k) domain) as [v HV].
  pose proof (quotation_instantiation_cons M f term g bound eb ec en y fb fc fn
    (succM M k) domain v result Hbound Hinst Hlookup HF HV HResult) as E.
  subst v.
  exact (contextual_quoted_all_from_cons M cb cc cn f eb ec en db dc dn fb fc fn
    k domain y body result all dom' Hsafe ((proj2 Hsafe) term y Hlookup)
    HD HF HB HV HQ Hdom PAll PD).
Qed.

Theorem contextual_quoted_exists_introduction_next M cb cc cn f term g bound h
    eb ec en k domain y ex result dom' :
  quotation_safe M eb ec en k domain -> source_bounded M f bound ->
  numerical_instantiation M f term g -> sf_relation M SFEx f (zeroM M) h ->
  environment_lookup M eb ec en term y ->
  numerical_quotation M h eb ec en k domain ex ->
  numerical_quotation M g eb ec en (succM M k) domain result ->
  membership_graph M domain y dom' ->
  contextually_provable M cb cc cn result -> contextually_provable M cb cc cn dom' ->
  contextually_provable M cb cc cn ex.
Proof.
  intros Hsafe Hbound Hinst Hsource Hlookup HEx HResult Hdom PR PD.
  destruct (numerical_quotation_unary_inv M false f h eb ec en k domain ex Hsource HEx)
    as [db [dc [dn [body [HD [HB HQ]]]]]].
  destruct (environment_cons_total M eb ec en y) as [fb [fc [fn HF]]].
  destruct (numerical_quotation_total M f fb fc fn (succM M k) domain) as [v HV].
  pose proof (quotation_instantiation_cons M f term g bound eb ec en y fb fc fn
    (succM M k) domain v result Hbound Hinst Hlookup HF HV HResult) as E.
  subst v.
  exact (contextual_quoted_exists_from_cons M cb cc cn f eb ec en db dc dn fb fc fn
    k domain y body result ex dom' Hsafe ((proj2 Hsafe) term y Hlookup)
    HD HF HB HV HQ Hdom PR PD).
Qed.
