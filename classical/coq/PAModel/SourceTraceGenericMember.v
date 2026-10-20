(** Complete trace-member construction at arbitrary container names and
    arbitrary model-valued parameter tail. No witness-branch proof is assumed. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SubstitutionSource
  SourceTraceDeltaValues SourceTraceRequestMap SourceTraceProfileShell SourceRoleReopening
  NumericalRenaming SourceBounded NumericalSourceFull.
Unset Implicit Arguments.

Definition source_trace_member_value M theta x p b value := exists some inner pair pb,
  numerical_instantiation M theta x some /\sf_relation M SFEx inner (zeroM M) some /\
  numerical_instantiation M inner p pair /\sf_relation M SFMember p b pb /\
  sf_relation M SFAnd pb value pair.

Theorem source_trace_member_value_total M theta atom matrix body x p b :
  sf_relation M SFMember (zeroM M) (succM M (succM M b)) atom ->
  sf_relation M SFAnd atom matrix body ->sf_relation M SFEx body (zeroM M) theta ->
  exists value,source_trace_member_value M theta x p b value.
Proof.
  intros HA HB HE.
  destruct (numerical_instantiation_total M theta x) as [some [sb [sc [HX HSome]]]].
  destruct (proj1 (numerical_substitution_quantifier M false body theta sb sc
    (code_numeral M 1) (zeroM M) some HE) HSome)
    as [d [e [l [inner [HL [HInner HEx]]]]]].
  destruct (proj1 (numerical_substitution_binary M SFAnd atom matrix body d e l
    (code_numeral M 1) inner (or_introl eq_refl) HB) HInner)
    as [atom' [matrix' [HAtom [HMatrix HBody]]]].
  destruct (proj1 (numerical_substitution_member M (zeroM M) (succM M (succM M b))
    atom d e l (code_numeral M 1) atom' HA) HAtom)
    as [u [v [HU [HV HAtom']]]].
  apply (proj1 (substitution_lift_head M sb sc (code_numeral M 1)
    (zeroM M) d e l u HL)) in HU. subst u.
  assert (HVB:substitution_lookup M d e l (code_numeral M 1)
    (succM M (succM M b)) (succM M b)).
  { apply (proj2 (substitution_lift_tail M sb sc (code_numeral M 1) (zeroM M) d e l
      (succM M b) b HL)). apply substitution_singleton_tail. }
  pose proof (substitution_lookup_functional M d e l (code_numeral M 1)
    (succM M (succM M b)) v (succM M b) HV HVB) as E. subst v.
  destruct (numerical_instantiation_total M inner p) as [pair [q [r [HP HPair]]]].
  destruct (proj1 (numerical_substitution_binary M SFAnd atom' matrix' inner q r
    (code_numeral M 1) (zeroM M) pair (or_introl eq_refl) HBody) HPair)
    as [pb [value [HPb [HValue HAnd]]]].
  destruct (proj1 (numerical_substitution_member M (zeroM M) (succM M b)
    atom' q r (code_numeral M 1) (zeroM M) pb HAtom') HPb)
    as [u [v [HU [HV' HPb']]]].
  pose proof (substitution_lookup_functional M q r (code_numeral M 1) (zeroM M)
    (zeroM M) u p HU HP) as E. subst u.
  pose proof (substitution_lookup_functional M q r (code_numeral M 1) (zeroM M)
    (succM M b) v b HV' (substitution_singleton_tail M q r b)) as E. subst v.
  exists value,some,inner,pair,pb. split;[now exists sb,sc|].
  split;[exact HEx|]. split;[now exists q,r|]. auto.
Qed.

Theorem source_full_trace_generic_member M cb cc cn phi k delta c b profile theta atom matrix body
    x p left right pb value rb rc :
  source_bounded M phi k ->
  numerical_renaming M phi (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) delta matrix ->
  sf_relation M SFMember (zeroM M) (succM M (succM M b)) atom ->
  sf_relation M SFAnd atom matrix body ->sf_relation M SFEx body (zeroM M) theta ->
  source_trace_profile_shell M theta c b profile ->
  sf_relation M SFMember x c left ->sf_relation M SFMember x b right ->
  sf_relation M SFMember p b pb ->source_role_reopening M p x rb rc ->
  numerical_substitution M phi rb rc (code_numeral M 2) delta value ->
  source_full_prv M cb cc cn profile ->source_full_prv M cb cc cn right ->
  source_full_prv M cb cc cn pb ->source_full_prv M cb cc cn value ->
  source_full_prv M cb cc cn left.
Proof.
  intros HP HA HAtom HBody HTheta HProfile HL HR HPb HMap HValue PP PR PPb PV.
  destruct (source_trace_member_value_total M theta atom matrix body x p b HAtom HBody HTheta)
    as [value' HMember].
  assert (HSyntax:source_trace_value_syntax M theta x p value').
  { destruct HMember as [some [inner [pair [pb' [HS [HE [HV [HB HP']]]]]]]].
    exists some,inner,pair,pb'. auto. }
  pose proof (source_trace_delta_value_alignment M phi theta atom matrix body x p value'
    k delta rb rc HP HA HBody HTheta HSyntax HMap) as HDirect.
  pose proof (numerical_substitution_functional M phi rb rc (code_numeral M 2) delta
    value' value HDirect HValue) as E. subst value'.
  destruct HMember as [some [inner [pair [pb' [HS [HE [HV [HB HP']]]]]]]].
  pose proof (sf_relation_functional M SFMember p b pb' pb HB HPb) as E. subst pb'.
  exact (source_full_trace_shell_member M cb cc cn theta c b profile x p left right some
    inner pair pb value HProfile HL HR HS HE HV HP' PP PR PPb PV).
Qed.

Print Assumptions source_trace_member_value_total.
Print Assumptions source_full_trace_generic_member.
