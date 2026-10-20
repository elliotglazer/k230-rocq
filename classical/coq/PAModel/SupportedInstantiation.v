(** Bounded instantiation rules preserve the supported source quotation
    invariant. The common trace bound ensures that each selected source
    term denotes a live environment entry with a supported domain fact. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions
  CodeDescent NumericalProofs NumericalEnvironments NumericalQuotation
  SourceSequents SourceTraceBounds SourceRuleBounds SourceBounded SourceBoundMonotone
  SetFormulaCodes ContextualProofs ContextSupport QuotedSameBaseRules
  SupportedQuotationInvariant SupportedQuotationContext.
Unset Implicit Arguments.

Lemma supported_instantiation_domain M bound eb ec en domain tb tc tn t y d :
  coding_lt M bound (succM M en) -> coding_lt M t bound ->
  quotation_domains_supported M eb ec en domain tb tc tn ->
  environment_lookup M eb ec en t y -> membership_graph M domain y d ->
  contextually_provable M tb tc tn d.
Proof.
  intros Hlen Ht HD HY Hd. apply context_support_provable.
  exact (HD t y d (source_bound_lt_le M t bound en Ht Hlen) HY Hd).
Qed.

Theorem source_supported_all_elimination M bound r p :
  source_row_at_bound M r bound -> source_supported_good M bound p ->
  source_AllE_at M r p bound -> source_supported_good M bound r.
Proof.
  intros HB IH [b [c [n [a [f [t [g [[Hr [Hp [HAll HI]]] Ht]]]]]]]].
  apply (source_supported_sequent_intro M bound r b c n g HB Hr).
  intros eb ec en fresh domain tb tc tn qg Hlen HS HC HD HG.
  destruct (source_row_bound_sequent M p bound b c n f (proj1 IH) Hp) as [HF _].
  assert (HA : source_bounded M a (succM M bound)).
  { exact (proj1 (source_bounded_accept_unary M SFAll a f bound
      (or_introl eq_refl) HAll) HF). }
  destruct (environment_lookup_total M eb ec en t) as [y HY].
  destruct (pair_total M domain y) as [pair HP].
  set (d := addM M (mulM M (code_numeral M 4) pair) (code_numeral M 1)).
  assert (Hd : membership_graph M domain y d).
  { exists pair. split;[exact HP|reflexivity]. }
  destruct (numerical_quotation_total M f eb ec en fresh domain) as [qf HQF].
  exact (contextual_quoted_all_elimination M tb tc tn a t g (succM M bound) f
    eb ec en fresh domain y qf qg d HS HA HI HAll HY HQF HG Hd
    (proj1 (proj2 IH) b c n f Hp eb ec en fresh domain tb tc tn qf Hlen HS HC HD HQF)
    (supported_instantiation_domain M bound eb ec en domain tb tc tn t y d
      Hlen Ht HD HY Hd)).
Qed.

Theorem source_supported_exists_introduction M bound r p :
  source_row_at_bound M r bound -> source_supported_good M bound p ->
  source_ExI_at M r p bound -> source_supported_good M bound r.
Proof.
  intros HB IH [b [c [n [a [f [t [g [[Hr [Hp [HEx HI]]] Ht]]]]]]]].
  apply (source_supported_sequent_intro M bound r b c n f HB Hr).
  intros eb ec en fresh domain tb tc tn qf Hlen HS HC HD HQF.
  destruct (source_row_bound_sequent M r bound b c n f HB Hr) as [HF _].
  assert (HA : source_bounded M a (succM M bound)).
  { exact (proj1 (source_bounded_accept_unary M SFEx a f bound
      (or_intror eq_refl) HEx) HF). }
  destruct (environment_lookup_total M eb ec en t) as [y HY].
  destruct (pair_total M domain y) as [pair HP].
  set (d := addM M (mulM M (code_numeral M 4) pair) (code_numeral M 1)).
  assert (Hd : membership_graph M domain y d).
  { exists pair. split;[exact HP|reflexivity]. }
  destruct (numerical_quotation_total M g eb ec en fresh domain) as [qg HG].
  exact (contextual_quoted_exists_introduction M tb tc tn a t g (succM M bound) f
    eb ec en fresh domain y qf qg d HS HA HI HEx HY HQF HG Hd
    (proj1 (proj2 IH) b c n g Hp eb ec en fresh domain tb tc tn qg Hlen HS HC HD HG)
    (supported_instantiation_domain M bound eb ec en domain tb tc tn t y d
      Hlen Ht HD HY Hd)).
Qed.

Print Assumptions source_supported_all_elimination.
Print Assumptions source_supported_exists_introduction.
