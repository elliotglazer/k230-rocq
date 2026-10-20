(** The literal dmem orientation of the checked representative-witness step. *)
(** The representative-witness step of quotient Separation for an actual
    source quotation. Only the raw guarded membership equivalence remains
    an input. Predicate invariance is supplied by the proved quotient laws. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalEnvironments NumericalContexts NumericalQuotation QuotationHygiene
  SourceBounded SetFormulaCodes QuotationPayloads FreshNames ProofTemplates
  TemplatePropositional NumericalVacuitySteps NumericalVacuity NumericalEquivalence NamedLeibnizSteps
  RawQuotientAtomCongruence SupportedQuotientEnvironments QuotedUnaryInvariance QuotedReverseInvariance QuotedSeparationPoint
  QuotientSeparationWitness ContextualProofs ContextualDeduction ContextualPropositional
  ContextualEquivalence StableContextSupport.
From Stdlib Require Import Lists.List.
From FOL Require Import FullSyntax Arithmetics.
Import ListNotations.
Unset Implicit Arguments.

Theorem numerical_quoted_selection_point_reverse M env W D C A E P Q
    phi count eb ec en w z wb wc wn zb zc zn k l t marker marker_name
    atom_base eqcode f g result :
  source_bounded M phi (succM M count) ->
  raw_empty_marker_graph M t marker_name marker ->
  quotient_pair_safe M t z w atom_base -> quotation_atom M true z w t atom_base eqcode ->
  environment_cons M eb ec en w wb wc wn -> environment_cons M eb ec en z zb zc zn ->
  quotation_safe M wb wc wn k t -> quotation_safe M zb zc zn l t ->
  numerical_quotation M phi wb wc wn k t f -> numerical_quotation M phi zb zc zn l t g ->
  code_relation M env W w -> code_relation M env E eqcode ->
  code_relation M env P f -> code_relation M env Q g ->
  formula_fresh M marker w -> formula_fresh M g w ->
  code_relation M env
    (E_wim (E_wal W (E_selection_raw D C A P))
      (E_selection_iff (E_wex W (E_selection_witness D C E))
        (E_wa (E_wex W (E_selection_witness D A E)) Q))) result ->
  numerical_implies M marker result.
Proof.
  intros HB HM HEqSafe HEq HW HZ HK HL HF HG EW EE EP EQ HMfresh HQfresh HResult.
  set (R := E_wal W (E_selection_raw D C A P)).
  set (I := E_wal W (E_selection_invariant E P Q)).
  set (O := E_selection_iff (E_wex W (E_selection_witness D C E))
    (E_wa (E_wex W (E_selection_witness D A E)) Q)).
  destruct (code_relation_total M (E_wim P Q) env) as [fg Efg].
  destruct (code_relation_total M (E_wim Q P) env) as [gf Egf].
  destruct (code_relation_total M (E_selection_iff P Q) env) as [iffcode Eiff].
  destruct (code_relation_total M (E_selection_invariant E P Q) env) as [inv Einv].
  destruct (code_relation_total M I env) as [allinv Eall].
  assert (Hfg : implication_graph M f g fg).
  { exact (proj1 (expression_implication_iff M env P Q f g fg EP EQ) Efg). }
  assert (Hgf : implication_graph M g f gf).
  { exact (proj1 (expression_implication_iff M env Q P g f gf EQ EP) Egf). }
  assert (Hiff : quotation_binary M SFAnd fg gf iffcode).
  { exact (proj1 (selection_expression_conjunction M env (E_wim P Q) (E_wim Q P)
      fg gf iffcode Efg Egf) Eiff). }
  assert (Hinv : implication_graph M eqcode iffcode inv).
  { exact (proj1 (expression_implication_iff M env E (E_selection_iff P Q)
      eqcode iffcode inv EE Eiff) Einv). }
  assert (Hall : universal_graph M w inv allinv).
  { exact (proj1 (expression_universal_iff M env W (E_selection_invariant E P Q)
      w inv allinv EW Einv) Eall). }
  pose proof (numerical_quoted_reverse_invariance_all M phi count eb ec en w z wb wc wn zb zc zn
    k l t marker marker_name atom_base eqcode f g fg gf iffcode inv w allinv
    HB HM HEqSafe HEq HW HZ HK HL HF HG Hfg Hgf Hiff Hinv HMfresh Hall) as HActualInvariant.
  assert (HVac : ns_proof M env (E_vac W Q)).
  { intros v EV. apply (numerical_vacuity M w g v HQfresh).
    exact (proj1 (expression_vacuity_graph M env W Q w g v EW EQ) EV). }
  pose proof (numerical_selection_witness M env W D C A E P Q HVac) as HWitness.
  destruct (context_singleton_total M marker) as [cb [cc [cn HC]]].
  assert (HMcontext : stable_context_support M cb cc cn marker).
  { apply stable_context_support_member.
    apply (proj2 (context_singleton_member M marker cb cc cn marker HC));reflexivity. }
  assert (HInvContext : contextual_expression M cb cc cn env I).
  { intros v EV. assert (v=allinv) by exact (code_relation_functional M I env v allinv EV Eall).
    subst v. apply stable_context_support_here.
    exact (stable_context_support_implies M cb cc cn marker allinv HActualInvariant HMcontext). }
  assert (HWhole : contextual_expression M cb cc cn env (E_wim R (E_wim I O))).
  { apply contextual_expression_global. exact HWitness. }
  assert (HSwapped : contextual_expression M cb cc cn env (E_wim I (E_wim R O))).
  { eapply contextual_expression_mp;[exact HWhole|].
    apply contextual_expression_template,selection_curry_order. }
  pose proof (contextual_expression_mp M cb cc cn env I (E_wim R O) HInvContext HSwapped
    result HResult) as HPoint.
  destruct (contextual_deduction M (zeroM M) (zeroM M) (zeroM M)
    marker cb cc cn result HC HPoint) as [actual [HActual HProof]].
  intros out HOut. assert (out=actual).
  { exact (code_relation_functional M _ _ out actual HOut HActual). }
  subst out. exact (proj1 (contextual_empty_iff M (zeroM M) (zeroM M) actual) HProof).
Qed.

Print Assumptions numerical_quoted_selection_point_reverse.
