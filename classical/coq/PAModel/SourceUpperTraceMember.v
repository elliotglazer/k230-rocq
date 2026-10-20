(** The complete canonical trace_member macro for an arbitrary internal
    source predicate. All intermediate instantiation graphs are constructed. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded SourceUpperTraceProfile SourceUpperTraceValues SourceTraceValueAlignment
  SourceTracePointRules SourceRoleReopening NumericalSubstitution NumericalSourceFull.
Unset Implicit Arguments.

Theorem source_full_upper_trace_parent M cb cc cn phi profile x left right :
  source_upper_trace_profile M phi profile ->
  sf_relation M SFMember x (zeroM M) left ->
  sf_relation M SFMember x (code_numeral M 1) right ->
  source_full_prv M cb cc cn profile -> source_full_prv M cb cc cn left ->
  source_full_prv M cb cc cn right.
Proof.
  intros [trace [theta [HT [HS HProfile]]]] HL HR PP PL.
  exact (source_full_trace_parent M cb cc cn theta profile x left right HProfile HL HR PP PL).
Qed.

Theorem source_full_upper_trace_member M cb cc cn phi count profile x p left right pb
    matrix rb rc :
  source_bounded M phi (succM M (succM M count)) ->
  source_upper_trace_profile M phi profile ->
  sf_relation M SFMember x (zeroM M) left ->
  sf_relation M SFMember x (code_numeral M 1) right ->
  sf_relation M SFMember p (code_numeral M 1) pb ->
  source_role_reopening M p x rb rc ->
  numerical_substitution M phi rb rc (code_numeral M 2) (code_numeral M 2) matrix ->
  source_full_prv M cb cc cn profile -> source_full_prv M cb cc cn right ->
  source_full_prv M cb cc cn pb -> source_full_prv M cb cc cn matrix ->
  source_full_prv M cb cc cn left.
Proof.
  intros HP [trace [theta [HT [HS HProfile]]]] HL HR HPb HMap HMatrix PP PR PPb PM.
  destruct (source_upper_trace_values_total M phi trace theta x p HT HS) as [value HValue].
  pose proof (source_trace_value_is_direct_substitution M phi trace theta x p value count rb rc
    HP HT HS HValue HMap) as HDirect.
  pose proof (numerical_substitution_functional M phi rb rc (code_numeral M 2)
    (code_numeral M 2) value matrix HDirect HMatrix) as E. subst value.
  destruct HValue as [some [inner [pair [pb' [HSome [HEx [HInst [HPb' HAnd]]]]]]]].
  pose proof (sf_relation_functional M SFMember p (code_numeral M 1) pb' pb HPb' HPb) as E.
  subst pb'.
  exact (source_full_trace_member M cb cc cn theta profile x p left right some inner pair pb matrix
    HProfile HL HR HSome HEx HInst HAnd PP PR PPb PM).
Qed.

Print Assumptions source_full_upper_trace_member.
Print Assumptions source_full_upper_trace_parent.
