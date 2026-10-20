(** Closing a uniform open-matrix implication under any internally finite
    source prefix. The marker remains an explicit local assumption until
    the final deduction step. Fresh names are chosen above that context. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalSetClosure NumericalQuotation QuotationHygiene QuotationPrefixClosure
  NumericalContexts NumericalEnvironments ContextualProofs ContextualDeduction
  ContextSupport NumericalEquivalence.
Unset Implicit Arguments.

Theorem numerical_quotation_prefix_implication M body t marker :
  (forall b c len fresh q, quotation_safe M b c len fresh t ->
    numerical_quotation M body b c len fresh t q -> numerical_implies M marker q) ->
  forall n f b c len fresh q, all_prefix M n body f ->
    quotation_safe M b c len fresh t -> numerical_quotation M f b c len fresh t q ->
    numerical_implies M marker q.
Proof.
  intros HOpen n f b c len fresh q HPrefix HSafe HQuote.
  destruct (context_singleton_total M marker) as [mb [mc [mn HMarker]]].
  assert (HM : context_support M mb mc mn marker).
  { apply context_support_member. apply (proj2 (context_singleton_member M marker mb mc mn marker HMarker)).
    reflexivity. }
  assert (HBody : forall eb ec en k u, quotation_safe M eb ec en k t ->
    numerical_quotation M body eb ec en k t u -> contextually_provable M mb mc mn u).
  { intros eb ec en k u HS HQ. apply context_support_provable.
    exact (context_support_implies M mb mc mn marker u HM (HOpen eb ec en k u HS HQ)). }
  pose proof (numerical_quotation_prefix_closure M body t mb mc mn HBody
    n f b c len fresh q HPrefix HSafe HQuote) as HQ.
  destruct (contextual_deduction M (zeroM M) (zeroM M) (zeroM M)
    marker mb mc mn q HMarker HQ) as [imp [HImp PImp]].
  assert (PGlobal : numerically_provable M imp).
  { exact (proj1 (contextual_empty_iff M (zeroM M) (zeroM M) imp) PImp). }
  intros result HResult.
  assert (result=imp) by exact (code_relation_functional M _ _ result imp HResult HImp).
  now subst result.
Qed.

Print Assumptions numerical_quotation_prefix_implication.
