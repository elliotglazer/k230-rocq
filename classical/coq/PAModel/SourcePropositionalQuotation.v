(** Actual preservation of internally finite propositional source proofs.
    The invariant includes both ordinary rows and the auxiliary DE branch pair. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  NumericalContexts NumericalEnvironments NumericalContextQuotation
  SourceSequents SourcePropositionalRules NumericalSourcePropositional
  SetFormulaCodes SetCodeDescent NumericalQuotation QuotationFunctionality QuotationPayloads
  ContextualProofs ContextualLogic ContextualDeduction ContextualPropositional
  SourceQuotationInvariant.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma source_quote_binary_payload M h a d f eb ec en fresh domain qa qd qf :
  sf_binary h -> sf_relation M h a d f ->
  numerical_quotation M a eb ec en fresh domain qa ->
  numerical_quotation M d eb ec en fresh domain qd ->
  numerical_quotation M f eb ec en fresh domain qf -> quotation_binary M h qa qd qf.
Proof.
  intros Hh Hf Ha Hd Hqf. destruct (quotation_binary_total M h qa qd) as [v Hv].
  pose proof (numerical_quotation_binary M h a d f eb ec en fresh domain qa qd v Hh Hf Ha Hd Hv) as Hqv.
  assert (v=qf) by exact (numerical_quotation_functional M f eb ec en fresh domain v qf Hqv Hqf).
  now subst v.
Qed.

Lemma source_quote_implication_payload M a d f eb ec en fresh domain qa qd qf :
  sf_relation M SFImpl a d f ->
  numerical_quotation M a eb ec en fresh domain qa ->
  numerical_quotation M d eb ec en fresh domain qd ->
  numerical_quotation M f eb ec en fresh domain qf -> implication_graph M qa qd qf.
Proof.
  intros Hf Ha Hd Hqf. apply (proj1 (quotation_implication_graph M qa qd qf)).
  exact (source_quote_binary_payload M SFImpl a d f eb ec en fresh domain qa qd qf
    (or_intror (or_intror eq_refl)) Hf Ha Hd Hqf).
Qed.

Lemma source_quotation_base M r : source_prop_base M r -> source_quotation_row_good M r.
Proof.
  intros [_ [HC|HP]].
  - destruct HC as [b [c [n [f [Hr Hmem]]]]].
    apply (source_quotation_sequent_intro M r b c n f Hr).
    intros eb ec en fresh domain tb tc g Hctx Hquote. apply contextual_hyp.
    apply (proj2 (context_quotation_member_iff M b c n eb ec en fresh domain tb tc g Hctx)).
    exists f. auto.
  - destruct HP as [b [c [n [a [d [x [y [f [Hr [Hx [Hy Hf]]]]]]]]]]].
    apply (source_quotation_sequent_intro M r b c n f Hr).
    intros eb ec en fresh domain tb tc g Hctx Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M d eb ec en fresh domain) as [qd Hqd].
    destruct (numerical_quotation_total M x eb ec en fresh domain) as [qx Hqx].
    destruct (numerical_quotation_total M y eb ec en fresh domain) as [qy Hqy].
    exact (contextual_peirce M tb tc n qa qd qx qy g
      (source_quote_implication_payload M a d x eb ec en fresh domain qa qd qx Hx Hqa Hqd Hqx)
      (source_quote_implication_payload M x a y eb ec en fresh domain qx qa qy Hy Hqx Hqa Hqy)
      (source_quote_implication_payload M y a f eb ec en fresh domain qy qa g Hf Hqy Hqa Hquote)).
Qed.

Lemma source_quotation_unary M r p : source_quotation_row_good M p ->
  source_prop_unary M r p -> source_quotation_row_good M r.
Proof.
  intros IH [_ [HII|[HE|[HC1|[HC2|[HD1|HD2]]]]]].
  - destruct HII as [b [c [n [a [d [f [u [v [l [Hr [Hp [Hcons Himp]]]]]]]]]]]].
    apply (source_quotation_sequent_intro M r b c n f Hr).
    intros eb ec en fresh domain tb tc g Hctx Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M d eb ec en fresh domain) as [qd Hqd].
    destruct (source_quote_context_extend M b c n a u v l eb ec en fresh domain tb tc qa
      Hctx Hqa Hcons) as [td [te [Ht Hqctx]]].
    apply (source_quote_discharge M tb tc n qa td te l qd g Ht).
    + exact (proj1 IH u v l d Hp eb ec en fresh domain td te qd Hqctx Hqd).
    + exact (source_quote_implication_payload M a d f eb ec en fresh domain qa qd g
        Himp Hqa Hqd Hquote).
  - destruct HE as [b [c [n [f [Hr Hp]]]]].
    apply (source_quotation_sequent_intro M r b c n f Hr).
    intros eb ec en fresh domain tb tc g Hctx Hquote. apply contextual_explosion.
    apply (proj1 IH b c n (zeroM M) Hp eb ec en fresh domain tb tc (code_numeral M 1) Hctx).
    apply numerical_quotation_leaf. left. split; [now left|reflexivity].
  - destruct HC1 as [b [c [n [a [d [f [Hr [Hp Hand]]]]]]]].
    apply (source_quotation_sequent_intro M r b c n a Hr).
    intros eb ec en fresh domain tb tc g Hctx Hquote.
    destruct (numerical_quotation_total M d eb ec en fresh domain) as [qd Hqd].
    destruct (numerical_quotation_total M f eb ec en fresh domain) as [qf Hqf].
    apply (contextual_conjunction_left M tb tc n g qd qf).
    + exact (source_quote_binary_payload M SFAnd a d f eb ec en fresh domain g qd qf
        (or_introl eq_refl) Hand Hquote Hqd Hqf).
    + exact (proj1 IH b c n f Hp eb ec en fresh domain tb tc qf Hctx Hqf).
  - destruct HC2 as [b [c [n [a [d [f [Hr [Hp Hand]]]]]]]].
    apply (source_quotation_sequent_intro M r b c n d Hr).
    intros eb ec en fresh domain tb tc g Hctx Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M f eb ec en fresh domain) as [qf Hqf].
    apply (contextual_conjunction_right M tb tc n qa g qf).
    + exact (source_quote_binary_payload M SFAnd a d f eb ec en fresh domain qa g qf
        (or_introl eq_refl) Hand Hqa Hquote Hqf).
    + exact (proj1 IH b c n f Hp eb ec en fresh domain tb tc qf Hctx Hqf).
  - destruct HD1 as [b [c [n [a [d [f [Hr [Hp Hor]]]]]]]].
    apply (source_quotation_sequent_intro M r b c n f Hr).
    intros eb ec en fresh domain tb tc g Hctx Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M d eb ec en fresh domain) as [qd Hqd].
    apply (contextual_disjunction_left M tb tc n qa qd g).
    + exact (source_quote_binary_payload M SFOr a d f eb ec en fresh domain qa qd g
        (or_intror (or_introl eq_refl)) Hor Hqa Hqd Hquote).
    + exact (proj1 IH b c n a Hp eb ec en fresh domain tb tc qa Hctx Hqa).
  - destruct HD2 as [b [c [n [a [d [f [Hr [Hp Hor]]]]]]]].
    apply (source_quotation_sequent_intro M r b c n f Hr).
    intros eb ec en fresh domain tb tc g Hctx Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M d eb ec en fresh domain) as [qd Hqd].
    apply (contextual_disjunction_right M tb tc n qa qd g).
    + exact (source_quote_binary_payload M SFOr a d f eb ec en fresh domain qa qd g
        (or_intror (or_introl eq_refl)) Hor Hqa Hqd Hquote).
    + exact (proj1 IH b c n d Hp eb ec en fresh domain tb tc qd Hctx Hqd).
Qed.

Lemma source_quotation_binary M r p q :
  source_quotation_row_good M p -> source_quotation_row_good M q ->
  source_prop_binary M r p q -> source_quotation_row_good M r.
Proof.
  intros IHp IHq [_ [HIE|[HCI|[HBP|HDE]]]].
  - destruct HIE as [b [c [n [a [d [f [Hr [Hp [Hq Himp]]]]]]]]].
    apply (source_quotation_sequent_intro M r b c n d Hr).
    intros eb ec en fresh domain tb tc g Hctx Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M f eb ec en fresh domain) as [qf Hqf].
    exact (contextual_mp M tb tc n qa g qf
      (proj1 IHq b c n a Hq eb ec en fresh domain tb tc qa Hctx Hqa)
      (proj1 IHp b c n f Hp eb ec en fresh domain tb tc qf Hctx Hqf)
      (source_quote_implication_payload M a d f eb ec en fresh domain qa g qf
        Himp Hqa Hquote Hqf)).
  - destruct HCI as [b [c [n [a [d [f [Hr [Hp [Hq Hand]]]]]]]]].
    apply (source_quotation_sequent_intro M r b c n f Hr).
    intros eb ec en fresh domain tb tc g Hctx Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M d eb ec en fresh domain) as [qd Hqd].
    exact (contextual_conjunction_intro M tb tc n qa qd g
      (proj1 IHp b c n a Hp eb ec en fresh domain tb tc qa Hctx Hqa)
      (proj1 IHq b c n d Hq eb ec en fresh domain tb tc qd Hctx Hqd)
      (source_quote_binary_payload M SFAnd a d f eb ec en fresh domain qa qd g
        (or_introl eq_refl) Hand Hqa Hqd Hquote)).
  - destruct HBP as [b [c [n [a [d [f [u [v [l [x [y [z
        [Hr [Hp [Hq [Hleft Hright]]]]]]]]]]]]]]]].
    apply (source_quotation_branches_intro M r b c n a d f Hr).
    intros eb ec en fresh domain tb tc qa qd qf af df Hctx Hqa Hqd Hqf Haf Hdf.
    destruct (source_quote_context_extend M b c n a u v l eb ec en fresh domain tb tc qa
      Hctx Hqa Hleft) as [ta [ua [Hta HqaCtx]]].
    destruct (source_quote_context_extend M b c n d x y z eb ec en fresh domain tb tc qd
      Hctx Hqd Hright) as [td [ud [Htd HqdCtx]]].
    split.
    + exact (source_quote_discharge M tb tc n qa ta ua l qf af Hta
        (proj1 IHp u v l f Hp eb ec en fresh domain ta ua qf HqaCtx Hqf) Haf).
    + exact (source_quote_discharge M tb tc n qd td ud z qf df Htd
        (proj1 IHq x y z f Hq eb ec en fresh domain td ud qf HqdCtx Hqf) Hdf).
  - destruct HDE as [b [c [n [a [d [f [disj [Hr [Hp [Hq Hor]]]]]]]]]].
    apply (source_quotation_sequent_intro M r b c n f Hr).
    intros eb ec en fresh domain tb tc g Hctx Hquote.
    destruct (numerical_quotation_total M a eb ec en fresh domain) as [qa Hqa].
    destruct (numerical_quotation_total M d eb ec en fresh domain) as [qd Hqd].
    destruct (numerical_quotation_total M disj eb ec en fresh domain) as [qdisj Hqdisj].
    destruct (source_quote_implication_total M qa g) as [af Haf].
    destruct (source_quote_implication_total M qd g) as [df Hdf].
    destruct (proj2 IHq b c n a d f Hq eb ec en fresh domain tb tc qa qd g af df
      Hctx Hqa Hqd Hquote Haf Hdf) as [Hafp Hdfp].
    exact (contextual_disjunction_elimination M tb tc n qa qd g qdisj af df
      (source_quote_binary_payload M SFOr a d disj eb ec en fresh domain qa qd qdisj
        (or_intror (or_introl eq_refl)) Hor Hqa Hqd Hqdisj)
      Haf Hdf (proj1 IHp b c n disj Hp eb ec en fresh domain tb tc qdisj Hctx Hqdisj)
      Hafp Hdfp).
Qed.

Theorem source_propositional_quotation_rows M r :
  source_prop_row M r -> source_quotation_row_good M r.
Proof.
  apply (source_prop_row_induction M (source_quotation_row_good M)).
  - apply source_quotation_row_good_definable.
  - apply source_quotation_base.
  - apply source_quotation_unary.
  - apply source_quotation_binary.
Qed.

Theorem source_propositional_quotation M b c n f eb ec en fresh domain tb tc g :
  source_prop_prv M b c n f ->
  context_quotation M b c n eb ec en fresh domain tb tc ->
  numerical_quotation M f eb ec en fresh domain g ->
  contextually_provable M tb tc n g.
Proof.
  intros [r [Hr HD]] Hctx Hquote.
  exact (proj1 (source_propositional_quotation_rows M r HD)
    b c n f Hr eb ec en fresh domain tb tc g Hctx Hquote).
Qed.

Theorem source_propositional_branch_quotation M b c n a d f eb ec en fresh domain tb tc qa qd qf af df :
  source_prop_branches M b c n a d f ->
  context_quotation M b c n eb ec en fresh domain tb tc ->
  numerical_quotation M a eb ec en fresh domain qa ->
  numerical_quotation M d eb ec en fresh domain qd ->
  numerical_quotation M f eb ec en fresh domain qf ->
  implication_graph M qa qf af -> implication_graph M qd qf df ->
  contextually_provable M tb tc n af /\ contextually_provable M tb tc n df.
Proof.
  intros [r [Hr HD]].
  exact (proj2 (source_propositional_quotation_rows M r HD)
    b c n a d f Hr eb ec en fresh domain tb tc qa qd qf af df).
Qed.

Theorem source_propositional_quotation_exists M b c n f eb ec en fresh domain :
  source_prop_prv M b c n f ->
  exists tb tc g, context_quotation M b c n eb ec en fresh domain tb tc /\
    numerical_quotation M f eb ec en fresh domain g /\
    contextually_provable M tb tc n g.
Proof.
  intro Hsrc.
  destruct (context_quotation_total M b c n eb ec en fresh domain) as [tb [tc Hctx]].
  destruct (numerical_quotation_total M f eb ec en fresh domain) as [g Hg].
  exists tb,tc,g. split; [exact Hctx|]. split; [exact Hg|].
  exact (source_propositional_quotation M b c n f eb ec en fresh domain tb tc g Hsrc Hctx Hg).
Qed.

Theorem source_propositional_false_to_numerical M b c :
  source_prop_prv M b c (zeroM M) (zeroM M) -> numerically_provable M (code_numeral M 1).
Proof.
  intro Hsrc.
  apply (contextual_sound M (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)).
  - intros f Hmem. exfalso. exact (context_empty M (zeroM M) (zeroM M) f Hmem).
  - apply (source_propositional_quotation M b c (zeroM M) (zeroM M)
      (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) (zeroM M)
      (zeroM M) (zeroM M) (code_numeral M 1) Hsrc).
    + apply context_quotation_empty.
    + apply numerical_quotation_leaf. left. split; [now left|reflexivity].
Qed.
