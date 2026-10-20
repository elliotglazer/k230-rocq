(** Elimination/introduction at one quotation base. The internal rebasing
    theorem removes the successor-base mismatch in QuotedInstantiationRules. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions CodeDescent NumericalProofs
  NumericalEquivalence NumericalEnvironments SourceBounded NumericalInstantiation
  SetFormulaCodes NumericalQuotation QuotationHygiene QuotationRebase
  ContextualProofs QuotedInstantiationRules.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Lemma quotation_safe_successor M b c n k domain :
  quotation_safe M b c n k domain -> quotation_safe M b c n (succM M k) domain.
Proof.
  intros [HD HE]. split.
  - exact (coding_lt_trans M domain k (succM M k) HD (coding_lt_succ M k)).
  - intros i x HX. exact (coding_lt_trans M x k (succM M k) (HE i x HX) (coding_lt_succ M k)).
Qed.

Lemma contextual_equivalent_forward M b c n a d :
  numerical_equivalent M a d -> contextually_provable M b c n a ->
  contextually_provable M b c n d.
Proof.
  intros [HAD HDA] HA.
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (a .: d .: fun _=>zeroM M)) as [imp HI].
  exact (contextual_mp M b c n a d imp HA (contextual_global M b c n imp (HAD imp HI)) HI).
Qed.

Theorem contextual_quoted_all_elimination M cb cc cn f term g bound h
    eb ec en k domain y all result dom :
  quotation_safe M eb ec en k domain -> source_bounded M f bound ->
  numerical_instantiation M f term g -> sf_relation M SFAll f (zeroM M) h ->
  environment_lookup M eb ec en term y ->
  numerical_quotation M h eb ec en k domain all ->
  numerical_quotation M g eb ec en k domain result ->
  membership_graph M domain y dom ->
  contextually_provable M cb cc cn all -> contextually_provable M cb cc cn dom ->
  contextually_provable M cb cc cn result.
Proof.
  intros HS HB HI HH HE HAll HR HD PA PD.
  destruct (numerical_quotation_total M g eb ec en (succM M k) domain) as [next HNext].
  pose proof (numerical_quotation_rebase_safe M g eb ec en k (succM M k) domain result next
    HS (quotation_safe_successor M eb ec en k domain HS) HR HNext) as EQ.
  apply (contextual_equivalent_forward M cb cc cn next result (numerical_equivalent_sym M result next EQ)).
  exact (contextual_quoted_all_elimination_next M cb cc cn f term g bound h eb ec en k domain
    y all next dom HS HB HI HH HE HAll HNext HD PA PD).
Qed.

Theorem contextual_quoted_exists_introduction M cb cc cn f term g bound h
    eb ec en k domain y ex result dom :
  quotation_safe M eb ec en k domain -> source_bounded M f bound ->
  numerical_instantiation M f term g -> sf_relation M SFEx f (zeroM M) h ->
  environment_lookup M eb ec en term y ->
  numerical_quotation M h eb ec en k domain ex ->
  numerical_quotation M g eb ec en k domain result ->
  membership_graph M domain y dom ->
  contextually_provable M cb cc cn result -> contextually_provable M cb cc cn dom ->
  contextually_provable M cb cc cn ex.
Proof.
  intros HS HB HI HH HE HEx HR HD PR PD.
  destruct (numerical_quotation_total M g eb ec en (succM M k) domain) as [next HNext].
  pose proof (numerical_quotation_rebase_safe M g eb ec en k (succM M k) domain result next
    HS (quotation_safe_successor M eb ec en k domain HS) HR HNext) as EQ.
  exact (contextual_quoted_exists_introduction_next M cb cc cn f term g bound h eb ec en k domain
    y ex next dom HS HB HI HH HE HEx HNext HD
    (contextual_equivalent_forward M cb cc cn result next EQ PR) PD).
Qed.

Print Assumptions contextual_quoted_all_elimination.
Print Assumptions contextual_quoted_exists_introduction.
