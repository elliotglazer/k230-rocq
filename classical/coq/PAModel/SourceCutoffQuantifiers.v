(** A cutoff insertion commutes with a literal source binder. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetCodeDescent SubstitutionSource SubstitutionPayloads NumericalSubstitutionMaps
  NumericalSubstitution SourceFiniteCutoffShift SourceQfFunctionality SourceBounded
  SourceUniversalDistribution SourceCutoffShiftCommutation.
Unset Implicit Arguments.

Theorem source_cutoff_quantifier_inv M depth universal a qa out :
  sf_relation M (substitution_source_quantifier universal) a (zeroM M) qa ->
  source_cutoff_shift M depth qa out ->exists b,
    sf_relation M (substitution_source_quantifier universal) b (zeroM M) out /\
    source_cutoff_shift M (S depth) a b.
Proof.
  intros HQ (sb&sc&sn&HM&HS).
  apply(proj1(numerical_substitution_quantifier M universal a qa sb sc sn
    (code_numeral M(S depth)) out HQ)) in HS.
  destruct HS as (rb&rc&rn&b&HL&HB&HOut).
  exists b. split;[exact HOut|]. exists rb,rc,rn. split;[|exact HB].
  exists sb,sc,sn. split;assumption.
Qed.

Theorem source_cutoff_quantifier_join M depth universal a b qa qb :
  sf_relation M (substitution_source_quantifier universal) a (zeroM M) qa ->
  sf_relation M (substitution_source_quantifier universal) b (zeroM M) qb ->
  source_cutoff_shift M (S depth) a b ->source_cutoff_shift M depth qa qb.
Proof.
  intros HA HB (rb&rc&rn&HRM&HS).
  destruct(source_cutoff_shift_map_total M depth) as (sb&sc&sn&HM).
  destruct(substitution_lift_total M sb sc sn(code_numeral M(S depth))) as (tb&tc&tn&HL).
  assert(HTM:source_cutoff_shift_map M(S depth) tb tc tn) by (exists sb,sc,sn;auto).
  assert(HBody:numerical_substitution M a tb tc tn(code_numeral M(S(S depth))) b).
  { exact(proj1(numerical_substitution_extensional M a rb rc rn tb tc tn
      (code_numeral M(S(S depth))) b
      (source_cutoff_shift_maps_equivalent M(S depth) rb rc rn tb tc tn HRM HTM)) HS). }
  exists sb,sc,sn. split;[exact HM|].
  apply(proj2(numerical_substitution_quantifier M universal a qa sb sc sn
    (code_numeral M(S depth)) qb HA)). exists tb,tc,tn,b. split;[exact HL|]. split;assumption.
Qed.

Theorem source_cutoff_two_three_commute M phi first phi' q k :
  source_bounded M phi k ->source_cutoff_shift M 2 phi first ->
  source_cutoff_shift M 2 phi phi' ->source_cutoff_shift M 3 first q ->
  source_cutoff_shift M 2 phi' q.
Proof.
  intros HB H1 H2 H3.
  destruct(sf_relation_total M SFAll phi(zeroM M)) as (a&HA).
  destruct(sf_relation_total M SFAll first(zeroM M)) as (b&HB0).
  destruct(sf_relation_total M SFAll phi'(zeroM M)) as (c&HC).
  destruct(sf_relation_total M SFAll q(zeroM M)) as (d&HD).
  pose proof(source_cutoff_quantifier_join M 1 true phi first a b HA HB0 H1) as H1'.
  pose proof(source_cutoff_quantifier_join M 1 true phi phi' a c HA HC H2) as H2'.
  pose proof(source_cutoff_quantifier_join M 2 true first q b d HB0 HD H3) as H3'.
  pose proof(source_cutoff_one_two_commute M a b c d k
    (source_bounded_universal_from_matrix M phi a k HB HA) H1' H2' H3') as HOut.
  destruct(source_cutoff_quantifier_inv M 1 true phi' c d HC HOut) as (q'&HQ'&HS).
  (* Injectivity fixes the body of the already chosen universal. *)
  pose proof(sf_relation_injective M SFAll SFAll q'(zeroM M) q(zeroM M) d HQ' HD) as HBody.
  destruct HBody as [_ [EQ _]]. now subst q'.
Qed.

Print Assumptions source_cutoff_quantifier_inv.
Print Assumptions source_cutoff_quantifier_join.
Print Assumptions source_cutoff_two_three_commute.
