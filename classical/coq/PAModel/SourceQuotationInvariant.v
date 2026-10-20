(** Explicit arithmetic invariant for both kinds of propositional source rows. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes NumericalContexts NumericalEnvironments NumericalContextQuotation SourceSequents
  NumericalQuotation QuotationFunctionality QuotationPayloads QuotationRules
  ContextualProofs ContextualLogic ContextualDeduction ContextualPropositional
  NumericalVacuitySteps SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_sequent_quotation_good M r :=
  forall b c n f, source_sequent M b c n f r ->
  forall eb ec en fresh domain tb tc g,
    context_quotation M b c n eb ec en fresh domain tb tc ->
    numerical_quotation M f eb ec en fresh domain g ->
    contextually_provable M tb tc n g.

Definition source_branches_quotation_good M r :=
  forall b c n a d f, source_branches M b c n a d f r ->
  forall eb ec en fresh domain tb tc qa qd qf af df,
    context_quotation M b c n eb ec en fresh domain tb tc ->
    numerical_quotation M a eb ec en fresh domain qa ->
    numerical_quotation M d eb ec en fresh domain qd ->
    numerical_quotation M f eb ec en fresh domain qf ->
    implication_graph M qa qf af -> implication_graph M qd qf df ->
    contextually_provable M tb tc n af /\ contextually_provable M tb tc n df.

Definition source_quotation_row_good M r :=
  source_sequent_quotation_good M r /\ source_branches_quotation_good M r.

(** Twelve parameters: b11,c10,n9,f8,eb7,ec6,en5,fresh4,domain3,tb2,tc1,g0;
    the source row remains in slot12. *)
Definition source_sequent_quotation_good_formula : form :=
  ∀∀∀∀ (source_sequent_formula $3 $2 $1 $0 $4 →
  ∀∀∀∀∀∀∀∀ (context_quotation_formula $11 $10 $9 $7 $6 $5 $4 $3 $2 $1 →
     numerical_quotation_formula $8 $7 $6 $5 $4 $3 $0 →
     contextually_provable_formula $2 $1 $9 $0)).

(** Eighteen parameters: b17,c16,n15,a14,d13,f12,eb11,ec10,en9,
    fresh8,domain7,tb6,tc5,qa4,qd3,qf2,af1,df0; source row is18. *)
Definition source_branches_quotation_good_formula : form :=
  ∀∀∀∀∀∀ (source_branches_formula $5 $4 $3 $2 $1 $0 $6 →
  ∀∀∀∀∀∀∀∀∀∀∀∀ (context_quotation_formula $17 $16 $15 $11 $10 $9 $8 $7 $6 $5 →
     numerical_quotation_formula $14 $11 $10 $9 $8 $7 $4 →
     numerical_quotation_formula $13 $11 $10 $9 $8 $7 $3 →
     numerical_quotation_formula $12 $11 $10 $9 $8 $7 $2 →
     implication_formula $4 $2 $1 → implication_formula $3 $2 $0 →
     (contextually_provable_formula $6 $5 $15 $1 ∧
      contextually_provable_formula $6 $5 $15 $0))).

Definition source_quotation_row_good_formula : form :=
  source_sequent_quotation_good_formula ∧ source_branches_quotation_good_formula.

Local Opaque holds source_sequent_formula source_branches_formula context_quotation_formula
  numerical_quotation_formula contextually_provable_formula implication_formula.
Lemma source_quotation_row_good_formula_correct M rho :
  holds M rho source_quotation_row_good_formula <-> source_quotation_row_good M (rho 0).
Proof.
  unfold source_quotation_row_good_formula,source_quotation_row_good.
  rewrite holds_and. unfold source_sequent_quotation_good_formula,source_sequent_quotation_good,
    source_branches_quotation_good_formula,source_branches_quotation_good.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_sequent_formula_correct. setoid_rewrite source_branches_formula_correct.
  setoid_rewrite context_quotation_formula_correct. setoid_rewrite numerical_quotation_formula_correct.
  setoid_rewrite holds_and. setoid_rewrite implication_formula_correct.
  setoid_rewrite contextually_provable_formula_correct. reflexivity.
Qed.

Lemma source_quotation_row_good_definable M : Definable1 M (source_quotation_row_good M).
Proof.
  exists source_quotation_row_good_formula,(fun _ => zeroM M). intro r.
  symmetry. apply source_quotation_row_good_formula_correct.
Qed.

Lemma source_quotation_sequent_intro M r b c n f :
  source_sequent M b c n f r ->
  (forall eb ec en fresh domain tb tc g,
    context_quotation M b c n eb ec en fresh domain tb tc ->
    numerical_quotation M f eb ec en fresh domain g -> contextually_provable M tb tc n g) ->
  source_quotation_row_good M r.
Proof.
  intros Hr H. split.
  - intros b' c' n' f' Hr'.
    destruct (source_sequent_injective M b c n f b' c' n' f' r Hr Hr')
      as [<- [<- [<- <-]]]. exact H.
  - intros b' c' n' a d f' Hr'. exfalso.
    exact (source_row_kinds_disjoint M b c n f b' c' n' a d f' r Hr Hr').
Qed.

Lemma source_quotation_branches_intro M r b c n a d f :
  source_branches M b c n a d f r ->
  (forall eb ec en fresh domain tb tc qa qd qf af df,
    context_quotation M b c n eb ec en fresh domain tb tc ->
    numerical_quotation M a eb ec en fresh domain qa ->
    numerical_quotation M d eb ec en fresh domain qd ->
    numerical_quotation M f eb ec en fresh domain qf ->
    implication_graph M qa qf af -> implication_graph M qd qf df ->
    contextually_provable M tb tc n af /\ contextually_provable M tb tc n df) ->
  source_quotation_row_good M r.
Proof.
  intros Hr H. split.
  - intros b' c' n' f' Hr'. exfalso.
    exact (source_row_kinds_disjoint M b' c' n' f' b c n a d f r Hr' Hr).
  - intros b' c' n' a' d' f' Hr'.
    destruct (source_branches_injective M b c n a d f b' c' n' a' d' f' r Hr Hr')
      as [<- [<- [<- [<- [<- <-]]]]]. exact H.
Qed.

Lemma quotation_implication_graph M a d g :
  quotation_binary M SFImpl a d g <-> implication_graph M a d g.
Proof.
  unfold quotation_binary,quotation_binary_expression.
  exact (expression_implication_iff M (a .: d .: fun _ => zeroM M)
    (CEvar 0) (CEvar 1) a d g eq_refl eq_refl).
Qed.

Lemma source_quote_implication_total M a d : exists g, implication_graph M a d g.
Proof. apply code_relation_total. Qed.
Lemma source_quote_implication_functional M a d g h :
  implication_graph M a d g -> implication_graph M a d h -> g=h.
Proof. apply code_relation_functional. Qed.

Lemma source_quote_discharge M b c n a d e m f af :
  environment_cons M b c n a d e m -> contextually_provable M d e m f ->
  implication_graph M a f af -> contextually_provable M b c n af.
Proof.
  intros Hcons Hf Haf. destruct (contextual_deduction M b c n a d e m f Hcons Hf)
    as [g [Hg Hp]].
  assert (g=af) by exact (source_quote_implication_functional M a f g af Hg Haf).
  now subst g.
Qed.

Lemma source_quote_context_extend M b c n a b' c' n' eb ec en fresh domain tb tc qa :
  context_quotation M b c n eb ec en fresh domain tb tc ->
  numerical_quotation M a eb ec en fresh domain qa ->
  environment_cons M b c n a b' c' n' ->
  exists td te, environment_cons M tb tc n qa td te n' /\
    context_quotation M b' c' n' eb ec en fresh domain td te.
Proof.
  intros Hctx Hqa Hsource.
  destruct (environment_cons_total M tb tc n qa) as [td [te [tn Htarget]]].
  assert (tn=n') by (rewrite (proj1 Htarget),(proj1 Hsource); reflexivity).
  subst tn. exists td,te. split; [exact Htarget|].
  exact (context_quotation_cons M b c n eb ec en fresh domain tb tc a qa
    b' c' n' td te Hctx Hqa Hsource Htarget).
Qed.

Lemma source_quotation_row_good_formula_bound : bounded 1 source_quotation_row_good_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
