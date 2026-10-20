(** Propositional rules preserve the full supported quotation invariant. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  NumericalContexts NumericalEnvironments SourceSequents SourcePropositionalRules
  NumericalQuotation QuotationPayloads SetFormulaCodes SourceTraceBounds
  ContextualProofs ContextualPropositional SourceQuotationInvariant SourcePropositionalQuotation
  SupportedQuotationInvariant SupportedQuotationContext ContextSupport.
Unset Implicit Arguments.

Lemma source_supported_base M bound r : source_row_at_bound M r bound ->
  source_prop_base M r -> source_supported_good M bound r.
Proof.
  intros HB [_ [HC|HP]].
  - destruct HC as [b [c [n [f [Hr Hmem]]]]].
    apply (source_supported_sequent_intro M bound r b c n f HB Hr).
    intros eb ec en fresh domain tb tc tn g Hlen HS Hctx HD Hquote. apply context_support_provable. exact (Hctx f g Hmem Hquote).
  - destruct HP as [b [c [n [a [d [x [y [f [Hr [Hx [Hy Hf]]]]]]]]]]].
    apply (source_supported_sequent_intro M bound r b c n f HB Hr).
    intros eb ec en fresh domain tb tc tn g Hlen HS Hctx HD Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M d eb ec en fresh domain) as [qd Hqd].
    destruct (numerical_quotation_total M x eb ec en fresh domain) as [qx Hqx].
    destruct (numerical_quotation_total M y eb ec en fresh domain) as [qy Hqy].
    exact (contextual_peirce M tb tc tn qa qd qx qy g
      (source_quote_implication_payload M a d x eb ec en fresh domain qa qd qx Hx Hqa Hqd Hqx)
      (source_quote_implication_payload M x a y eb ec en fresh domain qx qa qy Hy Hqx Hqa Hqy)
      (source_quote_implication_payload M y a f eb ec en fresh domain qy qa g Hf Hqy Hqa Hquote)).
Qed.

Lemma source_supported_unary M bound r p : source_row_at_bound M r bound ->
  source_supported_good M bound p -> source_prop_unary M r p -> source_supported_good M bound r.
Proof.
  intros HB IH [_ [HII|[HE|[HC1|[HC2|[HD1|HD2]]]]]].
  - destruct HII as [b [c [n [a [d [f [u [v [l [Hr [Hp [Hcons Himp]]]]]]]]]]]].
    apply (source_supported_sequent_intro M bound r b c n f HB Hr).
    intros eb ec en fresh domain tb tc tn g Hlen HS Hctx HD Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M d eb ec en fresh domain) as [qd Hqd].
    destruct (quotation_support_context_extend M b c n a u v l eb ec en fresh domain tb tc tn qa
      Hctx Hqa Hcons) as [td [te [tm [Ht Hqctx]]]].
    apply (source_quote_discharge M tb tc tn qa td te tm qd g Ht).
    + exact (proj1 (proj2 IH) u v l d Hp eb ec en fresh domain td te tm qd Hlen HS Hqctx
        (quotation_domains_supported_target_cons M eb ec en domain tb tc tn qa td te tm HD Ht) Hqd).
    + exact (source_quote_implication_payload M a d f eb ec en fresh domain qa qd g
        Himp Hqa Hqd Hquote).
  - destruct HE as [b [c [n [f [Hr Hp]]]]].
    apply (source_supported_sequent_intro M bound r b c n f HB Hr).
    intros eb ec en fresh domain tb tc tn g Hlen HS Hctx HD Hquote. apply contextual_explosion.
    apply (proj1 (proj2 IH) b c n (zeroM M) Hp eb ec en fresh domain tb tc tn (code_numeral M 1) Hlen HS Hctx HD).
    apply numerical_quotation_leaf. left. split; [now left|reflexivity].
  - destruct HC1 as [b [c [n [a [d [f [Hr [Hp Hand]]]]]]]].
    apply (source_supported_sequent_intro M bound r b c n a HB Hr).
    intros eb ec en fresh domain tb tc tn g Hlen HS Hctx HD Hquote.
    destruct (numerical_quotation_total M d eb ec en fresh domain) as [qd Hqd].
    destruct (numerical_quotation_total M f eb ec en fresh domain) as [qf Hqf].
    apply (contextual_conjunction_left M tb tc tn g qd qf).
    + exact (source_quote_binary_payload M SFAnd a d f eb ec en fresh domain g qd qf
        (or_introl eq_refl) Hand Hquote Hqd Hqf).
    + exact (proj1 (proj2 IH) b c n f Hp eb ec en fresh domain tb tc tn qf Hlen HS Hctx HD Hqf).
  - destruct HC2 as [b [c [n [a [d [f [Hr [Hp Hand]]]]]]]].
    apply (source_supported_sequent_intro M bound r b c n d HB Hr).
    intros eb ec en fresh domain tb tc tn g Hlen HS Hctx HD Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M f eb ec en fresh domain) as [qf Hqf].
    apply (contextual_conjunction_right M tb tc tn qa g qf).
    + exact (source_quote_binary_payload M SFAnd a d f eb ec en fresh domain qa g qf
        (or_introl eq_refl) Hand Hqa Hquote Hqf).
    + exact (proj1 (proj2 IH) b c n f Hp eb ec en fresh domain tb tc tn qf Hlen HS Hctx HD Hqf).
  - destruct HD1 as [b [c [n [a [d [f [Hr [Hp Hor]]]]]]]].
    apply (source_supported_sequent_intro M bound r b c n f HB Hr).
    intros eb ec en fresh domain tb tc tn g Hlen HS Hctx HD Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M d eb ec en fresh domain) as [qd Hqd].
    apply (contextual_disjunction_left M tb tc tn qa qd g).
    + exact (source_quote_binary_payload M SFOr a d f eb ec en fresh domain qa qd g
        (or_intror (or_introl eq_refl)) Hor Hqa Hqd Hquote).
    + exact (proj1 (proj2 IH) b c n a Hp eb ec en fresh domain tb tc tn qa Hlen HS Hctx HD Hqa).
  - destruct HD2 as [b [c [n [a [d [f [Hr [Hp Hor]]]]]]]].
    apply (source_supported_sequent_intro M bound r b c n f HB Hr).
    intros eb ec en fresh domain tb tc tn g Hlen HS Hctx HD Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M d eb ec en fresh domain) as [qd Hqd].
    apply (contextual_disjunction_right M tb tc tn qa qd g).
    + exact (source_quote_binary_payload M SFOr a d f eb ec en fresh domain qa qd g
        (or_intror (or_introl eq_refl)) Hor Hqa Hqd Hquote).
    + exact (proj1 (proj2 IH) b c n d Hp eb ec en fresh domain tb tc tn qd Hlen HS Hctx HD Hqd).
Qed.

Lemma source_supported_binary M bound r p q : source_row_at_bound M r bound ->
  source_supported_good M bound p -> source_supported_good M bound q ->
  source_prop_binary M r p q -> source_supported_good M bound r.
Proof.
  intros HB IHp IHq [_ [HIE|[HCI|[HBP|HDE]]]].
  - destruct HIE as [b [c [n [a [d [f [Hr [Hp [Hq Himp]]]]]]]]].
    apply (source_supported_sequent_intro M bound r b c n d HB Hr).
    intros eb ec en fresh domain tb tc tn g Hlen HS Hctx HD Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M f eb ec en fresh domain) as [qf Hqf].
    exact (contextual_mp M tb tc tn qa g qf
      (proj1 (proj2 IHq) b c n a Hq eb ec en fresh domain tb tc tn qa Hlen HS Hctx HD Hqa)
      (proj1 (proj2 IHp) b c n f Hp eb ec en fresh domain tb tc tn qf Hlen HS Hctx HD Hqf)
      (source_quote_implication_payload M a d f eb ec en fresh domain qa g qf
        Himp Hqa Hquote Hqf)).
  - destruct HCI as [b [c [n [a [d [f [Hr [Hp [Hq Hand]]]]]]]]].
    apply (source_supported_sequent_intro M bound r b c n f HB Hr).
    intros eb ec en fresh domain tb tc tn g Hlen HS Hctx HD Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M d eb ec en fresh domain) as [qd Hqd].
    exact (contextual_conjunction_intro M tb tc tn qa qd g
      (proj1 (proj2 IHp) b c n a Hp eb ec en fresh domain tb tc tn qa Hlen HS Hctx HD Hqa)
      (proj1 (proj2 IHq) b c n d Hq eb ec en fresh domain tb tc tn qd Hlen HS Hctx HD Hqd)
      (source_quote_binary_payload M SFAnd a d f eb ec en fresh domain qa qd g
        (or_introl eq_refl) Hand Hqa Hqd Hquote)).
  - destruct HBP as [b [c [n [a [d [f [u [v [l [x [y [z
        [Hr [Hp [Hq [Hleft Hright]]]]]]]]]]]]]]]].
    apply (source_supported_branches_intro M bound r b c n a d f HB Hr).
    intros eb ec en fresh domain tb tc tn qa qd qf af df Hlen HS Hctx HD Hqa Hqd Hqf Haf Hdf.
    destruct (quotation_support_context_extend M b c n a u v l eb ec en fresh domain tb tc tn qa
      Hctx Hqa Hleft) as [ta [ua [na [Hta HqaCtx]]]].
    destruct (quotation_support_context_extend M b c n d x y z eb ec en fresh domain tb tc tn qd
      Hctx Hqd Hright) as [td [ud [nd [Htd HqdCtx]]]].
    split.
    + exact (source_quote_discharge M tb tc tn qa ta ua na qf af Hta
        (proj1 (proj2 IHp) u v l f Hp eb ec en fresh domain ta ua na qf Hlen HS HqaCtx
          (quotation_domains_supported_target_cons M eb ec en domain tb tc tn qa ta ua na HD Hta) Hqf) Haf).
    + exact (source_quote_discharge M tb tc tn qd td ud nd qf df Htd
        (proj1 (proj2 IHq) x y z f Hq eb ec en fresh domain td ud nd qf Hlen HS HqdCtx
          (quotation_domains_supported_target_cons M eb ec en domain tb tc tn qd td ud nd HD Htd) Hqf) Hdf).
  - destruct HDE as [b [c [n [a [d [f [disj [Hr [Hp [Hq Hor]]]]]]]]]].
    apply (source_supported_sequent_intro M bound r b c n f HB Hr).
    intros eb ec en fresh domain tb tc tn g Hlen HS Hctx HD Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M d eb ec en fresh domain) as [qd Hqd].
    destruct (numerical_quotation_total M disj eb ec en fresh domain) as [qdisj Hqdisj].
    destruct (source_quote_implication_total M qa g) as [af Haf].
    destruct (source_quote_implication_total M qd g) as [df Hdf].
    destruct (proj2 (proj2 IHq) b c n a d f Hq eb ec en fresh domain tb tc tn qa qd g af df
      Hlen HS Hctx HD Hqa Hqd Hquote Haf Hdf) as [Hafp Hdfp].
    exact (contextual_disjunction_elimination M tb tc tn qa qd g qdisj af df
      (source_quote_binary_payload M SFOr a d disj eb ec en fresh domain qa qd qdisj
        (or_intror (or_introl eq_refl)) Hor Hqa Hqd Hqdisj)
      Haf Hdf (proj1 (proj2 IHp) b c n disj Hp eb ec en fresh domain tb tc tn qdisj Hlen HS Hctx HD Hqdisj)
      Hafp Hdfp).
Qed.


Print Assumptions source_supported_base.
Print Assumptions source_supported_unary.
Print Assumptions source_supported_binary.
