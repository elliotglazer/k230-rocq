(** The extra container parameter of the generic ordinal-collection theorem
    is identified by an ordinary, internally coded instantiation. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SourceSubstitutionIdentity
  SourceCBCutoffCancellation SourceCBTotality SourceOrdinalInitialTotality SourceOrdinalPredicate.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_cb_oc_totality_instantiation M q old total k:
  source_bounded M q k ->source_oc_initial_totality_graph M q old ->
  source_cb_totality_graph M q total ->numerical_instantiation M old(zeroM M)total.
Proof.
  intros HB(qD&body&ex&input&point&HC&HBody&HEx&HInput&HPoint&HAll)
    (body'&ex'&input'&point'&HBody'&HEx'&HInput'&HPoint'&HAll').
  destruct(substitution_singleton_total M(zeroM M)) as(b&c&HHead&HTail).
  destruct(substitution_lift_total M b c(code_numeral M 1)(zeroM M)) as(ab&ac&an&HL1).
  destruct(substitution_lift_total M ab ac an(code_numeral M 1)) as(tb&tc&tn&HL2).
  pose proof(source_cutoff_two_singleton_double_lift_cancel M q qD k b c ab ac an tb tc tn
    HB HC HL1 HL2) as HQ.
  pose proof(numerical_substitution_lift_fixes_domain M(source_ordinal_predicate_code M)ab ac an
    (code_numeral M 1)tb tc tn(source_ordinal_predicate_bounded M)HL2) as HOrd.
  assert(HBodySub:numerical_substitution M body tb tc tn(code_numeral M 2)body').
  { apply(proj2(numerical_substitution_binary M SFAnd(source_ordinal_predicate_code M)qD body
      tb tc tn(code_numeral M 2)body'(or_introl eq_refl)HBody)).
    exists(source_ordinal_predicate_code M),q. repeat split;assumption. }
  assert(HExSub:numerical_substitution M ex ab ac an(code_numeral M 1)ex').
  { apply(proj2(numerical_substitution_quantifier M false body ex ab ac an(code_numeral M 1)ex' HEx)).
    exists tb,tc,tn,body'. split;[exact HL2|]. auto. }
  assert(HInputSub:numerical_substitution M input ab ac an(code_numeral M 1)input').
  { apply(proj2(numerical_substitution_member M(zeroM M)(code_numeral M 1)input
      ab ac an(code_numeral M 1)input' HInput)).
    exists(zeroM M),(code_numeral M 1). split.
    - exact(proj2(substitution_lift_head M b c(code_numeral M 1)(zeroM M)ab ac an(zeroM M)HL1)eq_refl).
    - split;[|exact HInput'].
      exact(proj2(substitution_lift_tail M b c(code_numeral M 1)(zeroM M)ab ac an(zeroM M)(zeroM M)HL1)HHead). }
  exists b,c. split;[exact HHead|].
  apply(proj2(numerical_substitution_quantifier M true point old b c(code_numeral M 1)(zeroM M)total HAll)).
  exists ab,ac,an,point'. split;[exact HL1|]. split;[|exact HAll'].
  apply(proj2(numerical_substitution_binary M SFImpl input ex point ab ac an(code_numeral M 1)point'
    (or_intror(or_intror eq_refl))HPoint)). exists input',ex'. repeat split;assumption.
Qed.

Print Assumptions source_cb_oc_totality_instantiation.
