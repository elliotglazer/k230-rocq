(** A PA-definable invariant for source proof translation. Target contexts
    are arbitrary. Source assumptions have stable support, and every live
    environment entry has a supported membership in the interpreted domain. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions CodeDescent CodeTags
  NumericalProofs NumericalContexts NumericalEnvironments ContextualProofs
  ContextualDeduction ContextSupport NumericalEquivalence SourceSequents SourceTraceBounds
  NumericalQuotation QuotationHygiene SourceQuotationInvariant.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition quotation_assumptions_supported M sb sc sn eb ec en fresh domain tb tc tn :=
  forall f q,context_member M sb sc sn f ->
    numerical_quotation M f eb ec en fresh domain q -> context_support M tb tc tn q.
Definition quotation_assumptions_supported_formula (sb sc sn eb ec en fresh domain tb tc tn : term) : form :=
  ∀∀ (context_member_formula (code_lift2 sb) (code_lift2 sc) (code_lift2 sn) $1 →
    numerical_quotation_formula $1 (code_lift2 eb) (code_lift2 ec) (code_lift2 en)
      (code_lift2 fresh) (code_lift2 domain) $0 →
    context_support_formula (code_lift2 tb) (code_lift2 tc) (code_lift2 tn) $0).
Definition quotation_domains_supported M eb ec en domain tb tc tn :=
  forall i y d,coding_lt M i en -> environment_lookup M eb ec en i y ->
    membership_graph M domain y d -> context_support M tb tc tn d.
Definition support_lift3 (t : term) : term := t`[↑]`[↑]`[↑].
Definition quotation_domains_supported_formula (eb ec en domain tb tc tn : term) : form :=
  ∀∀∀ (Peano.sless $2 (support_lift3 en) →
    environment_lookup_formula (support_lift3 eb) (support_lift3 ec) (support_lift3 en) $2 $1 →
    tagged_pair_formula 1 (support_lift3 domain) $1 $0 →
    context_support_formula (support_lift3 tb) (support_lift3 tc) (support_lift3 tn) $0).

Local Opaque holds context_member_formula numerical_quotation_formula
  context_support_formula environment_lookup_formula tagged_pair_formula Peano.sless.
Lemma quotation_assumptions_supported_correct M rho sb sc sn eb ec en fresh domain tb tc tn :
  holds M rho (quotation_assumptions_supported_formula sb sc sn eb ec en fresh domain tb tc tn) <->
  quotation_assumptions_supported M (evalM M rho sb) (evalM M rho sc) (evalM M rho sn)
    (evalM M rho eb) (evalM M rho ec) (evalM M rho en) (evalM M rho fresh)
    (evalM M rho domain) (evalM M rho tb) (evalM M rho tc) (evalM M rho tn).
Proof.
  unfold quotation_assumptions_supported_formula,quotation_assumptions_supported.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite context_member_formula_correct. setoid_rewrite numerical_quotation_formula_correct.
  setoid_rewrite context_support_formula_correct. setoid_rewrite code_eval_lift2. reflexivity.
Qed.
Lemma quotation_domains_supported_correct M rho eb ec en domain tb tc tn :
  holds M rho (quotation_domains_supported_formula eb ec en domain tb tc tn) <->
  quotation_domains_supported M (evalM M rho eb) (evalM M rho ec) (evalM M rho en)
    (evalM M rho domain) (evalM M rho tb) (evalM M rho tc) (evalM M rho tn).
Proof.
  unfold quotation_domains_supported_formula,quotation_domains_supported.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite less_formula_correct. setoid_rewrite environment_lookup_formula_correct.
  setoid_rewrite tagged_pair_formula_correct. unfold membership_graph. setoid_rewrite context_support_formula_correct.
  unfold support_lift3,evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Definition source_supported_sequent M bound r :=
  forall b c n f,source_sequent M b c n f r ->
  forall eb ec en fresh domain tb tc tn g,
    coding_lt M bound (succM M en) -> quotation_safe M eb ec en fresh domain ->
    quotation_assumptions_supported M b c n eb ec en fresh domain tb tc tn ->
    quotation_domains_supported M eb ec en domain tb tc tn ->
    numerical_quotation M f eb ec en fresh domain g -> contextually_provable M tb tc tn g.
Definition source_supported_branches M bound r :=
  forall b c n a d f,source_branches M b c n a d f r ->
  forall eb ec en fresh domain tb tc tn qa qd qf af df,
    coding_lt M bound (succM M en) -> quotation_safe M eb ec en fresh domain ->
    quotation_assumptions_supported M b c n eb ec en fresh domain tb tc tn ->
    quotation_domains_supported M eb ec en domain tb tc tn ->
    numerical_quotation M a eb ec en fresh domain qa ->
    numerical_quotation M d eb ec en fresh domain qd ->
    numerical_quotation M f eb ec en fresh domain qf ->
    implication_graph M qa qf af -> implication_graph M qd qf df ->
    contextually_provable M tb tc tn af /\ contextually_provable M tb tc tn df.
Definition source_supported_good M bound r := source_row_at_bound M r bound /\
  source_supported_sequent M bound r /\ source_supported_branches M bound r.
Definition source_supported_sequent_formula : form :=
  ∀∀∀∀ (source_sequent_formula $3 $2 $1 $0 $4 →
  ∀∀∀∀∀∀∀∀∀ (Peano.sless $14 (σ $6) → quotation_safe_formula $8 $7 $6 $5 $4 →
    quotation_assumptions_supported_formula $12 $11 $10 $8 $7 $6 $5 $4 $3 $2 $1 →
    quotation_domains_supported_formula $8 $7 $6 $4 $3 $2 $1 →
    numerical_quotation_formula $9 $8 $7 $6 $5 $4 $0 →
    contextually_provable_formula $3 $2 $1 $0)).
Definition source_supported_branches_formula : form :=
  ∀∀∀∀∀∀ (source_branches_formula $5 $4 $3 $2 $1 $0 $6 →
  ∀∀∀∀∀∀∀∀∀∀∀∀∀ (Peano.sless $20 (σ $10) → quotation_safe_formula $12 $11 $10 $9 $8 →
    quotation_assumptions_supported_formula $18 $17 $16 $12 $11 $10 $9 $8 $7 $6 $5 →
    quotation_domains_supported_formula $12 $11 $10 $8 $7 $6 $5 →
    numerical_quotation_formula $15 $12 $11 $10 $9 $8 $4 →
    numerical_quotation_formula $14 $12 $11 $10 $9 $8 $3 →
    numerical_quotation_formula $13 $12 $11 $10 $9 $8 $2 →
    implication_formula $4 $2 $1 → implication_formula $3 $2 $0 →
    (contextually_provable_formula $7 $6 $5 $1 ∧ contextually_provable_formula $7 $6 $5 $0))).
Definition source_supported_good_formula : form := source_row_at_bound_formula $0 $1 ∧
  (source_supported_sequent_formula ∧ source_supported_branches_formula).
Local Opaque source_sequent_formula source_branches_formula source_row_at_bound_formula
  quotation_assumptions_supported_formula quotation_domains_supported_formula
  quotation_safe_formula contextually_provable_formula implication_formula.
Lemma source_supported_good_correct M rho :
  holds M rho source_supported_good_formula <-> source_supported_good M (rho 1) (rho 0).
Proof.
  unfold source_supported_good_formula,source_supported_good.
  rewrite holds_and,holds_and,source_row_at_bound_formula_correct.
  unfold source_supported_sequent_formula,source_supported_sequent,
    source_supported_branches_formula,source_supported_branches.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_sequent_formula_correct. setoid_rewrite source_branches_formula_correct.
  setoid_rewrite less_formula_correct. setoid_rewrite quotation_safe_formula_correct.
  setoid_rewrite quotation_assumptions_supported_correct. setoid_rewrite quotation_domains_supported_correct.
  setoid_rewrite numerical_quotation_formula_correct. setoid_rewrite implication_formula_correct.
  setoid_rewrite holds_and. setoid_rewrite contextually_provable_formula_correct. reflexivity.
Qed.
Lemma source_supported_good_definable M bound : Definable1 M (source_supported_good M bound).
Proof.
  exists source_supported_good_formula,(bound .: fun _=>zeroM M). intro r.
  symmetry. apply source_supported_good_correct.
Qed.

Lemma source_supported_sequent_intro M bound r b c n f :
  source_row_at_bound M r bound -> source_sequent M b c n f r ->
  (forall eb ec en fresh domain tb tc tn g,
    coding_lt M bound (succM M en) -> quotation_safe M eb ec en fresh domain ->
    quotation_assumptions_supported M b c n eb ec en fresh domain tb tc tn ->
    quotation_domains_supported M eb ec en domain tb tc tn ->
    numerical_quotation M f eb ec en fresh domain g -> contextually_provable M tb tc tn g) ->
  source_supported_good M bound r.
Proof.
  intros HB Hr H. split;[exact HB|]. split.
  - intros b' c' n' f' Hr'.
    destruct (source_sequent_injective M b c n f b' c' n' f' r Hr Hr')
      as [<- [<- [<- <-]]]. exact H.
  - intros b' c' n' a d f' Hr'. exfalso.
    exact (source_row_kinds_disjoint M b c n f b' c' n' a d f' r Hr Hr').
Qed.
Lemma source_supported_branches_intro M bound r b c n a d f :
  source_row_at_bound M r bound -> source_branches M b c n a d f r ->
  (forall eb ec en fresh domain tb tc tn qa qd qf af df,
    coding_lt M bound (succM M en) -> quotation_safe M eb ec en fresh domain ->
    quotation_assumptions_supported M b c n eb ec en fresh domain tb tc tn ->
    quotation_domains_supported M eb ec en domain tb tc tn ->
    numerical_quotation M a eb ec en fresh domain qa ->
    numerical_quotation M d eb ec en fresh domain qd ->
    numerical_quotation M f eb ec en fresh domain qf ->
    implication_graph M qa qf af -> implication_graph M qd qf df ->
    contextually_provable M tb tc tn af /\ contextually_provable M tb tc tn df) ->
  source_supported_good M bound r.
Proof.
  intros HB Hr H. split;[exact HB|]. split.
  - intros b' c' n' f' Hr'. exfalso.
    exact (source_row_kinds_disjoint M b' c' n' f' b c n a d f r Hr' Hr).
  - intros b' c' n' a' d' f' Hr'.
    destruct (source_branches_injective M b c n a d f b' c' n' a' d' f' r Hr Hr')
      as [<- [<- [<- [<- [<- <-]]]]]. exact H.
Qed.

Print Assumptions source_supported_good_correct.
Print Assumptions source_supported_good_definable.
