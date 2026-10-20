(** Raw subset elimination and shifting for arbitrary model-valued names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  NumericalRenamingMaps NumericalRenaming NumericalContextRenaming NumericalInstantiation
  SourceInstantiationConstructors SourceTracePointRules SourceDerivedRules NumericalSourceFull.
Unset Implicit Arguments.

Definition source_raw_subset_graph M x y out := exists left right point,
  sf_relation M SFMember (zeroM M) (succM M x) left /\
  sf_relation M SFMember (zeroM M) (succM M y) right /\
  sf_relation M SFImpl left right point /\ sf_relation M SFAll point (zeroM M) out.

Theorem source_raw_subset_total M x y : exists out,source_raw_subset_graph M x y out.
Proof.
  destruct (sf_relation_total M SFMember (zeroM M) (succM M x)) as (left&HL).
  destruct (sf_relation_total M SFMember (zeroM M) (succM M y)) as (right&HR).
  destruct (sf_relation_total M SFImpl left right) as (point&HP).
  destruct (sf_relation_total M SFAll point (zeroM M)) as (out&HO).
  exists out,left,right,point. repeat split;assumption.
Qed.

Theorem source_raw_subset_shift M x y out shifted :
  source_raw_subset_graph M x y out ->
  numerical_renaming M out (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) shifted ->
  source_raw_subset_graph M (succM M x) (succM M y) shifted.
Proof.
  intros (left&right&point&HL&HR&HP&HO) HS.
  apply (proj1 (numerical_renaming_quantifier M true point out (zeroM M) (zeroM M)
    (zeroM M) (code_numeral M 1) shifted HO)) in HS.
  destruct HS as (rb&rc&rn&point'&HMap&HRPoint&HOut).
  apply (proj1 (numerical_renaming_binary M SFImpl left right point rb rc rn
    (code_numeral M 1) point' (or_intror(or_intror eq_refl)) HP)) in HRPoint.
  destruct HRPoint as (left'&right'&HRLeft&HRRight&HPoint').
  assert (HAtom:forall z a a',sf_relation M SFMember (zeroM M) (succM M z) a ->
    numerical_renaming M a rb rc rn (code_numeral M 1) a' ->
    sf_relation M SFMember (zeroM M) (succM M(succM M z)) a').
  { intros z a a' HA HRA.
    apply (proj1 (numerical_renaming_member M (zeroM M) (succM M z) a rb rc rn
      (code_numeral M 1) a' HA)) in HRA.
    destruct HRA as (u&v&HU&HV&HUV).
    pose proof (renaming_lookup_functional M rb rc rn (code_numeral M 1)
      (zeroM M) u (zeroM M) HU (proj1(proj2 HMap))) as E. subst u.
    assert (HNext:renaming_lookup M rb rc rn (code_numeral M 1) (succM M z) (succM M(succM M z))).
    { apply (proj2(proj2 HMap)). apply context_shift_lookup. reflexivity. }
    pose proof (renaming_lookup_functional M rb rc rn (code_numeral M 1)
      (succM M z) v (succM M(succM M z)) HV HNext) as E. now subst v. }
  exists left',right',point'. split;[exact(HAtom x left left' HL HRLeft)|].
  split;[exact(HAtom y right right' HR HRRight)|]. split;assumption.
Qed.

Theorem source_full_raw_subset_member M b c n x y z subset left right :
  source_raw_subset_graph M x y subset -> sf_relation M SFMember z x left ->
  sf_relation M SFMember z y right -> source_full_prv M b c n subset ->
  source_full_prv M b c n left -> source_full_prv M b c n right.
Proof.
  intros (a&d&point&HA&HD&HP&HAll) HL HR PS PL.
  destruct (sf_relation_total M SFImpl left right) as (instance&HI).
  pose proof (source_instantiation_head_member M x a z left HA HL) as HIA.
  pose proof (source_instantiation_head_member M y d z right HD HR) as HID.
  pose proof (source_instantiation_binary M SFImpl a d point z left right instance
    (or_intror(or_intror eq_refl)) HP HIA HID HI) as HIP.
  pose proof (full_source_AllE M b c n point subset z instance
    (source_wf_quantifier_instance M b c n SFAll point subset z instance (or_introl eq_refl)
      HAll (source_full_prv_wellformed M b c n subset PS) HIP) PS HAll HIP) as PI.
  exact (source_full_modus_ponens M b c n left right instance HI PI PL).
Qed.

Print Assumptions source_raw_subset_shift.
Print Assumptions source_full_raw_subset_member.
