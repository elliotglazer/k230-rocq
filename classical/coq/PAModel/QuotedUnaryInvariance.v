(** Numerical deqv-invariance of an actual internally coded source
    quotation. The marker is discharged explicitly; arbitrary raw
    formulas are not admitted as invariant predicates. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalEnvironments NumericalContexts NumericalQuotation QuotationHygiene
  SourceBounded SetFormulaCodes QuotationPayloads FreshNames SupportedQuotientEnvironments StableContextSupport
  RawQuotientAtomCongruence QuotedUnaryCongruence ContextualProofs
  ContextualDeduction ContextualPropositional ContextualEquivalence NumericalEquivalence.
Unset Implicit Arguments.

Lemma contextual_quoted_unary_invariance M phi count eb ec en x y xb xc xn yb yc yn
    k l t cb cc cn marker marker_name atom_base eqcode f g fg gf iffcode result :
  source_bounded M phi (succM M count) ->
  raw_empty_marker_graph M t marker_name marker -> stable_context_support M cb cc cn marker ->
  quotient_pair_safe M t x y atom_base -> quotation_atom M true x y t atom_base eqcode ->
  environment_cons M eb ec en x xb xc xn -> environment_cons M eb ec en y yb yc yn ->
  quotation_safe M xb xc xn k t -> quotation_safe M yb yc yn l t ->
  numerical_quotation M phi xb xc xn k t f -> numerical_quotation M phi yb yc yn l t g ->
  implication_graph M f g fg -> implication_graph M g f gf ->
  quotation_binary M SFAnd fg gf iffcode -> implication_graph M eqcode iffcode result ->
  contextually_provable M cb cc cn result.
Proof.
  intros HB HM HMsafe HEqSafe HEq HX HY HK HL HF HG Hfg Hgf HIff HResult.
  destruct (environment_cons_total M cb cc cn eqcode) as [db [dc [dn HD]]].
  assert (HMarker : stable_context_support M db dc dn marker).
  { exact (stable_context_support_cons M cb cc cn eqcode db dc dn marker HD HMsafe). }
  assert (HEqSupport : stable_context_support M db dc dn eqcode).
  { apply stable_context_support_member.
    apply (proj2 (context_member_cons M cb cc cn eqcode db dc dn eqcode HD)). now left. }
  pose proof (supported_quotient_pair_one_base M db dc dn t x y atom_base eqcode
    HEqSafe HEq HEqSupport) as HPair.
  destruct (quoted_unary_congruence M phi count eb ec en x y xb xc xn yb yc yn
    k l t db dc dn marker marker_name f g HB HM HMarker HPair HX HY HK HL HF HG)
    as [HForward HBackward].
  pose proof (contextual_conjunction_intro M db dc dn fg gf iffcode
    (HForward fg Hfg) (HBackward gf Hgf) HIff) as HBoth.
  destruct (contextual_deduction M cb cc cn eqcode db dc dn iffcode HD HBoth)
    as [actual [HActual HProof]].
  assert (result=actual).
  { exact (code_relation_functional M _ _ result actual HResult HActual). }
  now subst result.
Qed.

Theorem numerical_quoted_unary_invariance M phi count eb ec en x y xb xc xn yb yc yn
    k l t marker marker_name atom_base eqcode f g fg gf iffcode result :
  source_bounded M phi (succM M count) ->
  raw_empty_marker_graph M t marker_name marker ->
  quotient_pair_safe M t x y atom_base -> quotation_atom M true x y t atom_base eqcode ->
  environment_cons M eb ec en x xb xc xn -> environment_cons M eb ec en y yb yc yn ->
  quotation_safe M xb xc xn k t -> quotation_safe M yb yc yn l t ->
  numerical_quotation M phi xb xc xn k t f -> numerical_quotation M phi yb yc yn l t g ->
  implication_graph M f g fg -> implication_graph M g f gf ->
  quotation_binary M SFAnd fg gf iffcode -> implication_graph M eqcode iffcode result ->
  numerical_implies M marker result.
Proof.
  intros HB HM HEqSafe HEq HX HY HK HL HF HG Hfg Hgf HIff HResult.
  destruct (context_singleton_total M marker) as [cb [cc [cn HC]]].
  assert (HMarker : stable_context_support M cb cc cn marker).
  { apply stable_context_support_member.
    apply (proj2 (context_singleton_member M marker cb cc cn marker HC));reflexivity. }
  pose proof (contextual_quoted_unary_invariance M phi count eb ec en x y xb xc xn yb yc yn
    k l t cb cc cn marker marker_name atom_base eqcode f g fg gf iffcode result
    HB HM HMarker HEqSafe HEq HX HY HK HL HF HG Hfg Hgf HIff HResult) as HP.
  destruct (contextual_deduction M (zeroM M) (zeroM M) (zeroM M)
    marker cb cc cn result HC HP) as [actual [HActual HProof]].
  intros out HOut. assert (out=actual).
  { exact (code_relation_functional M _ _ out actual HOut HActual). }
  subst out. exact (proj1 (contextual_empty_iff M (zeroM M) (zeroM M) actual) HProof).
Qed.

Theorem numerical_quoted_unary_invariance_all M phi count eb ec en x y xb xc xn yb yc yn
    k l t marker marker_name atom_base eqcode f g fg gf iffcode result binder allresult :
  source_bounded M phi (succM M count) ->
  raw_empty_marker_graph M t marker_name marker ->
  quotient_pair_safe M t x y atom_base -> quotation_atom M true x y t atom_base eqcode ->
  environment_cons M eb ec en x xb xc xn -> environment_cons M eb ec en y yb yc yn ->
  quotation_safe M xb xc xn k t -> quotation_safe M yb yc yn l t ->
  numerical_quotation M phi xb xc xn k t f -> numerical_quotation M phi yb yc yn l t g ->
  implication_graph M f g fg -> implication_graph M g f gf ->
  quotation_binary M SFAnd fg gf iffcode -> implication_graph M eqcode iffcode result ->
  formula_fresh M marker binder -> universal_graph M binder result allresult ->
  numerical_implies M marker allresult.
Proof.
  intros HB HM HEqSafe HEq HX HY HK HL HF HG Hfg Hgf HIff HResult HFresh HAll.
  destruct (context_singleton_total M marker) as [cb [cc [cn HC]]].
  assert (HMarker : stable_context_support M cb cc cn marker).
  { apply stable_context_support_member.
    apply (proj2 (context_singleton_member M marker cb cc cn marker HC));reflexivity. }
  pose proof (contextual_quoted_unary_invariance M phi count eb ec en x y xb xc xn yb yc yn
    k l t cb cc cn marker marker_name atom_base eqcode f g fg gf iffcode result
    HB HM HMarker HEqSafe HEq HX HY HK HL HF HG Hfg Hgf HIff HResult) as HP.
  assert (HContextFresh : context_fresh M cb cc cn binder).
  { intros h HH. apply (proj1 (context_singleton_member M marker cb cc cn h HC)) in HH.
    now subst h. }
  pose proof (contextual_gen M cb cc cn binder result allresult HContextFresh HP HAll) as HGeneral.
  destruct (contextual_deduction M (zeroM M) (zeroM M) (zeroM M)
    marker cb cc cn allresult HC HGeneral) as [actual [HActual HProof]].
  intros out HOut. assert (out=actual).
  { exact (code_relation_functional M _ _ out actual HOut HActual). }
  subst out. exact (proj1 (contextual_empty_iff M (zeroM M) (zeroM M) actual) HProof).
Qed.

Print Assumptions numerical_quoted_unary_invariance.
Print Assumptions numerical_quoted_unary_invariance_all.
