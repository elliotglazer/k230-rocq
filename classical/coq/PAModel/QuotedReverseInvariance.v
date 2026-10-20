(** The literal dmem template writes deqv(z,w), while its raw predicate
    is evaluated at w. Both directions of quotation congruence are used
    here, without identifying the two atom codes. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalEnvironments NumericalContexts NumericalQuotation QuotationHygiene
  SourceBounded SetFormulaCodes QuotationPayloads FreshNames SupportedQuotientEnvironments
  StableContextSupport RawQuotientAtomCongruence QuotedUnaryCongruence ContextualProofs
  ContextualDeduction ContextualPropositional ContextualEquivalence NumericalEquivalence.
Unset Implicit Arguments.

Theorem numerical_quoted_reverse_invariance_all M phi count eb ec en w z wb wc wn zb zc zn
    k l t marker marker_name atom_base eqcode f g fg gf iffcode result binder allresult :
  source_bounded M phi (succM M count) ->
  raw_empty_marker_graph M t marker_name marker ->
  quotient_pair_safe M t z w atom_base -> quotation_atom M true z w t atom_base eqcode ->
  environment_cons M eb ec en w wb wc wn -> environment_cons M eb ec en z zb zc zn ->
  quotation_safe M wb wc wn k t -> quotation_safe M zb zc zn l t ->
  numerical_quotation M phi wb wc wn k t f -> numerical_quotation M phi zb zc zn l t g ->
  implication_graph M f g fg -> implication_graph M g f gf ->
  quotation_binary M SFAnd fg gf iffcode -> implication_graph M eqcode iffcode result ->
  formula_fresh M marker binder -> universal_graph M binder result allresult ->
  numerical_implies M marker allresult.
Proof.
  intros HB HM HEqSafe HEq HW HZ HK HL HF HG Hfg Hgf HIff HResult HFresh HAll.
  destruct (context_singleton_total M marker) as [cb [cc [cn HC]]].
  destruct (environment_cons_total M cb cc cn eqcode) as [db [dc [dn HD]]].
  assert (HMarker : stable_context_support M db dc dn marker).
  { apply (stable_context_support_cons M cb cc cn eqcode db dc dn marker HD).
    apply stable_context_support_member.
    apply (proj2 (context_singleton_member M marker cb cc cn marker HC));reflexivity. }
  assert (HEqSupport : stable_context_support M db dc dn eqcode).
  { apply stable_context_support_member.
    apply (proj2 (context_member_cons M cb cc cn eqcode db dc dn eqcode HD)). now left. }
  pose proof (supported_quotient_pair_one_base M db dc dn t z w atom_base eqcode
    HEqSafe HEq HEqSupport) as HPair.
  destruct (quoted_unary_congruence M phi count eb ec en z w zb zc zn wb wc wn
    l k t db dc dn marker marker_name g f HB HM HMarker HPair HZ HW HL HK HG HF)
    as [HBackward HForward].
  pose proof (contextual_conjunction_intro M db dc dn fg gf iffcode
    (HForward fg Hfg) (HBackward gf Hgf) HIff) as HBoth.
  destruct (contextual_deduction M cb cc cn eqcode db dc dn iffcode HD HBoth)
    as [actual [HActual HProof]].
  assert (result=actual) by exact (code_relation_functional M _ _ result actual HResult HActual).
  subst actual.
  assert (HContextFresh : context_fresh M cb cc cn binder).
  { intros h HH. apply (proj1 (context_singleton_member M marker cb cc cn h HC)) in HH.
    now subst h. }
  pose proof (contextual_gen M cb cc cn binder result allresult HContextFresh HProof HAll) as HGeneral.
  destruct (contextual_deduction M (zeroM M) (zeroM M) (zeroM M)
    marker cb cc cn allresult HC HGeneral) as [out [HOut POut]].
  intros target HTarget. assert (target=out).
  { exact (code_relation_functional M _ _ target out HTarget HOut). }
  subst target. exact (proj1 (contextual_empty_iff M (zeroM M) (zeroM M) out) POut).
Qed.

Print Assumptions numerical_quoted_reverse_invariance_all.
