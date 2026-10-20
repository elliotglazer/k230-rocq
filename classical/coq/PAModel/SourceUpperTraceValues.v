(** The two actual binder eliminations inside a trace profile. The graph
    contains source syntax operations only; it contains no proof predicate. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
  SourceUpperTraceRecipe SourceFiniteCutoffShift NumericalSubstitutionMaps
  NumericalSubstitution NumericalInstantiation SubstitutionSource SourceNumeralLift
  SourceTracePointRules NumericalSourceFull.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_trace_theta_value M theta x p value := exists some inner pair pb,
  numerical_instantiation M theta x some /\ sf_relation M SFEx inner (zeroM M) some /\
  numerical_instantiation M inner p pair /\ sf_relation M SFMember p (code_numeral M 1) pb /\
  sf_relation M SFAnd pb value pair.
Definition source_trace_theta_value_formula (theta x p value:term) :form :=
  ∃∃∃∃ (numerical_instantiation_formula (lift4 theta) (lift4 x) $3 ∧
    (sf_formula SFEx $2 zero $3 ∧
    (numerical_instantiation_formula $2 (lift4 p) $1 ∧
    (sf_formula SFMember (lift4 p) (num 1) $0 ∧ sf_formula SFAnd $0 (lift4 value) $1)))).
Local Opaque holds numerical_instantiation_formula sf_formula.

Theorem source_trace_theta_value_formula_correct M rho theta x p value :
  holds M rho (source_trace_theta_value_formula theta x p value) <->
  source_trace_theta_value M (evalM M rho theta) (evalM M rho x)
    (evalM M rho p) (evalM M rho value).
Proof.
  unfold source_trace_theta_value_formula,source_trace_theta_value.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite numerical_instantiation_formula_correct. setoid_rewrite sf_formula_correct.
  repeat setoid_rewrite code_eval_num. unfold evalM,lift4.
  repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_upper_trace_theta_shape M phi trace theta :
  source_upper_trace M phi trace -> source_cutoff_shift M 1 trace theta ->
  exists atom matrix body,sf_relation M SFMember (zeroM M) (code_numeral M 3) atom /\
    sf_relation M SFAnd atom matrix body /\ sf_relation M SFEx body (zeroM M) theta.
Proof.
  intros [swapped [shifted [atom [body [HS [HT [HA [HB HE]]]]]]]]
    [b [c [n [HM HSub]]]].
  destruct (proj1 (numerical_substitution_quantifier M false body trace b c n
    (code_numeral M 2) theta HE) HSub) as [d [e [l [inner [HL [HInner HTheta]]]]]].
  destruct (proj1 (numerical_substitution_binary M SFAnd atom shifted body d e l
    (code_numeral M 3) inner (or_introl eq_refl) HB) HInner)
    as [atom' [matrix [HAtom [HMatrix HBody]]]].
  destruct (proj1 (numerical_substitution_member M (zeroM M) (code_numeral M 2)
    atom d e l (code_numeral M 3) atom' HA) HAtom)
    as [u [v [HU [HV HAtom']]]].
  apply (proj1 (substitution_lift_head M b c n (code_numeral M 2) d e l u HL)) in HU.
  subst u.
  assert (HV3:substitution_lookup M d e l (code_numeral M 3)
    (code_numeral M 2) (code_numeral M 3)).
  { apply (proj2 (substitution_lift_tail M b c n (code_numeral M 2) d e l
      (code_numeral M 1) (code_numeral M 2) HL)).
    exact (source_cutoff_shift_map_fixed_lookup M 1 b c n HM 1). }
  pose proof (substitution_lookup_functional M d e l (code_numeral M 3)
    (code_numeral M 2) v (code_numeral M 3) HV HV3) as E. subst v.
  exists atom',matrix,inner. auto.
Qed.

Theorem source_trace_theta_value_total M theta atom matrix body x p :
  sf_relation M SFMember (zeroM M) (code_numeral M 3) atom ->
  sf_relation M SFAnd atom matrix body -> sf_relation M SFEx body (zeroM M) theta ->
  exists value,source_trace_theta_value M theta x p value.
Proof.
  intros HA HB HE.
  destruct (numerical_instantiation_total M theta x) as [some HS].
  destruct HS as [b [c [HX HSome]]].
  destruct (proj1 (numerical_substitution_quantifier M false body theta b c
    (succM M (zeroM M)) (zeroM M) some HE) HSome)
    as [d [e [l [inner [HL [HInner HEx]]]]]].
  destruct (proj1 (numerical_substitution_binary M SFAnd atom matrix body d e l
    (code_numeral M 1) inner (or_introl eq_refl) HB) HInner)
    as [atom' [matrix' [HAtom [HMatrix HBody]]]].
  destruct (proj1 (numerical_substitution_member M (zeroM M) (code_numeral M 3)
    atom d e l (code_numeral M 1) atom' HA) HAtom)
    as [u [v [HU [HV HAtom']]]].
  apply (proj1 (substitution_lift_head M b c (succM M (zeroM M))
    (zeroM M) d e l u HL)) in HU. subst u.
  assert (HV2:substitution_lookup M d e l (code_numeral M 1)
    (code_numeral M 3) (code_numeral M 2)).
  { apply (proj2 (substitution_lift_tail M b c (succM M (zeroM M)) (zeroM M) d e l
      (code_numeral M 2) (code_numeral M 1) HL)). apply substitution_singleton_tail. }
  pose proof (substitution_lookup_functional M d e l (code_numeral M 1)
    (code_numeral M 3) v (code_numeral M 2) HV HV2) as EV. subst v.
  destruct (numerical_instantiation_total M inner p) as [pair [q [r [HP HPair]]]].
  destruct (proj1 (numerical_substitution_binary M SFAnd atom' matrix' inner q r
    (code_numeral M 1) (zeroM M) pair (or_introl eq_refl) HBody) HPair)
    as [pb [value [HPb [HValue HAnd]]]].
  destruct (proj1 (numerical_substitution_member M (zeroM M) (code_numeral M 2)
    atom' q r (code_numeral M 1) (zeroM M) pb HAtom') HPb)
    as [u [v [HU [HVp HPb']]]].
  pose proof (substitution_lookup_functional M q r (code_numeral M 1) (zeroM M)
    (zeroM M) u p HU HP) as EU. subst u.
  pose proof (substitution_lookup_functional M q r (code_numeral M 1) (zeroM M)
    (code_numeral M 2) v (code_numeral M 1) HVp (substitution_singleton_tail M q r (code_numeral M 1))) as EVp.
  subst v. exists value,some,inner,pair,pb. split;[now exists b,c|].
  split;[exact HEx|]. split;[now exists q,r|]. auto.
Qed.

Theorem source_upper_trace_values_total M phi trace theta x p :
  source_upper_trace M phi trace -> source_cutoff_shift M 1 trace theta ->
  exists value,source_trace_theta_value M theta x p value.
Proof.
  intros HT HS. destruct (source_upper_trace_theta_shape M phi trace theta HT HS)
    as [atom [matrix [body [HA [HB HE]]]]].
  exact (source_trace_theta_value_total M theta atom matrix body x p HA HB HE).
Qed.

Print Assumptions source_trace_theta_value_formula_correct.
Print Assumptions source_upper_trace_theta_shape.
Print Assumptions source_trace_theta_value_total.
Print Assumptions source_upper_trace_values_total.
