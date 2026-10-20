(** Exact syntax tools for conditional Dn monotonicity. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs SetFormulaCodes
  NumericalEnvironments NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
  SourceBounded SourceRenamingIdentity SourceRenamingDiamond SourceRenamingBounds SourceQuantifierRules
  SourceImplicationAllShift NumericalContextRenaming SourceNumeralLift
  SourceDnStep SourceDnRotation4 SourceDnCutoffDiamonds SourceFiniteCutoffShift SourceCutoffQuantifiers
  SourceCutoffShiftCommutation SourceQfFunctionality SourceUniversalDistribution RenamingSubstitution.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma source_empty_identity_lookup M i :renaming_lookup M(zeroM M)(zeroM M)(zeroM M)(zeroM M) i i.
Proof. right. split;[apply coding_not_lt_zero|]. symmetry. apply coding_add_zero_r. Qed.

Theorem source_dn_rotate4_condition M condition shifted :
  source_bounded M condition(code_numeral M 2) ->source_formula_shift M condition shifted ->
  source_dn_rotate4 M condition shifted.
Proof.
  intros HC HS.
  pose proof(source_shift_bound M condition shifted(code_numeral M 2) HC HS) as HB.
  apply(numerical_source_renaming_diamond M condition(code_numeral M 2)
    (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 5475)(code_numeral M 6)(code_numeral M 4)(zeroM M)
    shifted condition shifted HC HS).
  - apply(numerical_renaming_identity_on_bound M condition _ _ _ _ (code_numeral M 2) HC).
    intros i HI. apply source_empty_identity_lookup.
  - apply(numerical_renaming_identity_on_bound M shifted _ _ _ _ (code_numeral M 3) HB).
    intros i HI. apply source_empty_identity_lookup.
  - intros i j l m HI HSI HTJ HRI.
    assert(EL:l=i) by(eapply renaming_lookup_functional;[exact HRI|apply source_empty_identity_lookup]). subst l.
    assert(EM:m=j) by(eapply renaming_lookup_functional;[exact HTJ|apply source_empty_identity_lookup]). subst m.
    assert(EJ:j=succM M i) by(exact(proj1(context_shift_lookup M i j) HSI)). subst j.
    destruct(source_numeral_initial_segment M 2 i HI) as(v&HV&->).
    destruct v as [|[|v]];try lia;
      [exact(source_dn_rotate4_fixed M 0 ltac:(lia))|exact(source_dn_rotate4_fixed M 1 ltac:(lia))].
Qed.

Theorem source_dn_successor_cutoff_inv M depth prev dn out : (depth<2)%nat ->
  source_dn_successor M prev dn ->source_cutoff_shift M depth dn out ->
  exists rotated target guard point,
    numerical_renaming M prev(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M) rotated /\
    source_cutoff_shift M(S depth) rotated target /\sf_relation M SFMember(zeroM M)(code_numeral M 3) guard /\
    sf_relation M SFImpl guard target point /\sf_relation M SFAll point(zeroM M) out.
Proof.
  intros HD (rot&guard&point&HR&HG&HP&HAll) HS.
  destruct(source_cutoff_quantifier_inv M depth true point dn out HAll HS) as(point'&HAll'&HC).
  destruct HC as(sb&sc&sn&HM&HPoint).
  apply(proj1(numerical_substitution_binary M SFImpl guard rot point sb sc sn(code_numeral M(S(S depth))) point'
    (or_intror(or_intror eq_refl)) HP)) in HPoint.
  destruct HPoint as(guard'&target&HGuard&HT&HPoint).
  apply(proj1(numerical_substitution_member M(zeroM M)(code_numeral M 2) guard sb sc sn
    (code_numeral M(S(S depth))) guard' HG)) in HGuard.
  destruct HGuard as(x&y&HX&HY&HGuard).
  assert(EX:x=zeroM M).
  { eapply substitution_lookup_functional;[exact HX|].
    destruct depth as [|[|depth]];try lia;
      exact(source_cutoff_shift_map_fixed_lookup M _ sb sc sn HM 0). }
  assert(EY:y=code_numeral M 3).
  { eapply substitution_lookup_functional;[exact HY|].
    destruct depth as [|[|depth]];try lia;
      exact(source_cutoff_shift_map_fixed_lookup M _ sb sc sn HM 2). }
  subst x y. exists rot,target,guard',point'. repeat split;try assumption.
  exists sb,sc,sn. auto.
Qed.

Print Assumptions source_dn_rotate4_condition.
Print Assumptions source_dn_successor_cutoff_inv.
