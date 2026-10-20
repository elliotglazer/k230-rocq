(** The actual ordinal-collection conclusion and its exact shift after a
    fresh collector. Upper ordinal index0 remains protected. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution
  SourceFiniteCutoffShift SourceCutoffQuantifiers SourceCutoffTwoSwap SourceQfFunctionality SourceCutoffShiftCommutation
  SourceOrdinalPredicate SourceDomainInstances SourceSubstitutionIdentity SourceQuantifierRules
  SourceFixedSwap SourceRelativizationBounds.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Definition source_oc_cover_graph M phi x cover :=exists phiV result input point,
  source_cutoff_shift M 2 phi phiV /\
  numerical_renaming M phiV (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (zeroM M) result /\
  sf_relation M SFMember (zeroM M) (succM M x) input /\sf_relation M SFImpl input result point /\
  sf_relation M SFAll point (zeroM M) cover.
Definition source_oc_output_graph M phi x output :=exists cover body,
  source_oc_cover_graph M phi x cover /\sf_relation M SFAnd (source_ordinal_predicate_code M) cover body /\
  sf_relation M SFEx body (zeroM M) output.

Theorem source_oc_cover_total M phi x :exists cover,source_oc_cover_graph M phi x cover.
Proof.
  destruct (source_cutoff_shift_total M 2 phi) as (phiV&HV).
  destruct (numerical_renaming_total M phiV (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M)) as (result&HR).
  destruct (sf_relation_total M SFMember (zeroM M) (succM M x)) as (input&HI).
  destruct (sf_relation_total M SFImpl input result) as (point&HP).
  destruct (sf_relation_total M SFAll point (zeroM M)) as (cover&HA).
  exists cover,phiV,result,input,point. auto.
Qed.

Theorem source_oc_output_total M phi x :exists output,source_oc_output_graph M phi x output.
Proof.
  destruct (source_oc_cover_total M phi x) as (cover&HC).
  destruct (sf_relation_total M SFAnd (source_ordinal_predicate_code M) cover) as (body&HB).
  destruct (sf_relation_total M SFEx body (zeroM M)) as (output&HE).
  exists output,cover,body. auto.
Qed.

Theorem source_oc_cover_bounded M phi x cover count :
  source_bounded M phi (succM M (succM M count)) ->coding_lt M x (succM M (succM M count)) ->
  source_oc_cover_graph M phi x cover ->source_bounded M cover (succM M (succM M count)).
Proof.
  intros HB HX (phiV&result&input&point&HC&HR&HI&HP&HA).
  pose proof (source_cutoff_shift_bounded M 2 phi phiV count HB HC) as HBV.
  pose proof (source_fixed_swap_bounded M phiV result (succM M count) HBV HR) as HResult.
  apply (proj2 (source_bounded_accept_unary M SFAll point cover (succM M (succM M count))
    (or_introl eq_refl) HA)).
  apply (proj2 (source_bounded_accept_binary M SFImpl input result point
    (succM M (succM M (succM M count))) (or_intror (or_intror eq_refl)) HP)).
  split;[|exact HResult]. apply (proj2 (source_bounded_accept_atom M SFMember (zeroM M)
    (succM M x) input (succM M (succM M (succM M count))) (or_introl eq_refl) HI)).
  split;[apply coding_zero_lt_succ|exact (proj2 (coding_lt_succ_cancel M x (succM M (succM M count))) HX)].
Qed.

Theorem source_oc_output_bounded M phi x output count :
  source_bounded M phi (succM M (succM M count)) ->coding_lt M x (succM M (succM M count)) ->
  source_oc_output_graph M phi x output ->source_bounded M output (succM M count).
Proof.
  intros HB HX (cover&body&HC&HP&HE).
  pose proof (source_oc_cover_bounded M phi x cover count HB HX HC) as HCover.
  apply (proj2 (source_bounded_accept_unary M SFEx body output (succM M count)
    (or_intror eq_refl) HE)).
  apply (proj2 (source_bounded_accept_binary M SFAnd (source_ordinal_predicate_code M) cover body
    (succM M (succM M count)) (or_introl eq_refl) HP)).
  split;[exact (sr_domain_bound_succ M _ (succM M count) (source_ordinal_predicate_bounded M))|exact HCover].
Qed.

Theorem source_oc_cover_cutoff_one M phi phi' x cover cover' count :
  source_bounded M phi (succM M (succM M count)) ->source_cutoff_shift M 2 phi phi' ->
  source_oc_cover_graph M phi (succM M x) cover ->source_cutoff_shift M 1 cover cover' ->
  source_oc_cover_graph M phi' (succM M (succM M x)) cover'.
Proof.
  intros HB HC (phiV&result&input&point&HV&HR&HI&HP&HA) HCut.
  pose proof (source_cutoff_shift_functional M 2 phi phiV phi' HV HC) as E. subst phiV.
  pose proof (source_cutoff_shift_bounded M 2 phi phi' count HB HC) as HB'.
  destruct (source_cutoff_quantifier_inv M 1 true point cover cover' HA HCut)
    as (point'&HA'&sb&sc&sn&HM&HS).
  destruct (proj1 (numerical_substitution_binary M SFImpl input result point sb sc sn (code_numeral M 3)
    point' (or_intror (or_intror eq_refl)) HP) HS) as (input'&result'&HInput&HResult&HPoint).
  destruct (proj1 (numerical_substitution_member M (zeroM M) (succM M (succM M x)) input sb sc sn
    (code_numeral M 3) input' HI) HInput) as (a&d&HA0&HD0&HInput').
  pose proof (substitution_lookup_functional M sb sc sn (code_numeral M 3) _ a _ HA0
    (source_cutoff_shift_map_fixed_lookup M 2 sb sc sn HM 0)) as E. subst a.
  pose proof (substitution_lookup_functional M sb sc sn (code_numeral M 3) _ d _ HD0
    (SourceCutoffShiftCommutation.source_cutoff_shift_map_tail_lookup M 2 sb sc sn x HM)) as E. subst d.
  destruct (source_cutoff_shift_total M 2 phi') as (phiV'&HV').
  assert (HCResult:source_cutoff_shift M 2 result result') by (exists sb,sc,sn;auto).
  pose proof (source_cutoff_two_swap M phi' phiV' result result' (succM M (succM M (succM M count)))
    HB' HV' HR HCResult) as HR'.
  exists phiV',result',input',point'. split;[exact HV'|]. split;[exact HR'|].
  split;[exact HInput'|auto].
Qed.

Theorem source_oc_output_shift M phi phi' output output' count :
  source_bounded M phi (succM M (succM M count)) ->source_cutoff_shift M 2 phi phi' ->
  source_oc_output_graph M phi (code_numeral M 1) output ->source_formula_shift M output output' ->
  source_oc_output_graph M phi' (code_numeral M 2) output'.
Proof.
  intros HB HC (cover&body&HG&HP&HE) HR.
  assert (HCut:source_cutoff_shift M 0 output output').
  { exists (zeroM M),(zeroM M),(zeroM M). split;[repeat split;reflexivity|].
    pose proof (proj1 (numerical_renaming_substitution M output (zeroM M) (zeroM M) (zeroM M)
      (code_numeral M 1) output') HR) as HS.
    rewrite Arithmetic.add_zero in HS. exact HS. }
  destruct (source_cutoff_quantifier_inv M 0 false body output output' HE HCut)
    as (body'&HE'&sb&sc&sn&HM&HS).
  destruct (proj1 (numerical_substitution_binary M SFAnd (source_ordinal_predicate_code M) cover body
    sb sc sn (code_numeral M 2) body' (or_introl eq_refl) HP) HS)
    as (ord'&cover'&HO'&HC'&HP').
  assert (HOrdSelf:numerical_substitution M (source_ordinal_predicate_code M) sb sc sn
    (code_numeral M 2) (source_ordinal_predicate_code M)).
  { apply (numerical_substitution_identity_on_bound M _ sb sc sn (code_numeral M 2)
      (code_numeral M 1) (source_ordinal_predicate_bounded M)).
    intros i HI. rewrite (domain_index_below_one M i HI).
    exact (source_cutoff_shift_map_fixed_lookup M 1 sb sc sn HM 0). }
  pose proof (numerical_substitution_functional M _ sb sc sn (code_numeral M 2) ord'
    (source_ordinal_predicate_code M) HO' HOrdSelf) as E. subst ord'.
  exists cover',body'. split;[|auto].
  apply (source_oc_cover_cutoff_one M phi phi' (zeroM M) cover cover' count HB HC HG).
  exists sb,sc,sn. auto.
Qed.

Print Assumptions source_oc_cover_total.
Print Assumptions source_oc_output_total.
Print Assumptions source_oc_cover_cutoff_one.
Print Assumptions source_oc_output_shift.
Print Assumptions source_oc_cover_bounded.
Print Assumptions source_oc_output_bounded.
