(** Forward transport from canonical closure coordinates to the named
    witness frame. The internally coded matrix is never assumed standard. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 NumericalRenamingMaps NumericalRenaming SourceRenamingIdentity SourceRenamingDiamond SourceShiftSpecialization
 RawBinderRenaming SourceNamedQuantifierRules SourceRepresentationNamedWitness SourceNamedFiniteCalibration
 SourceRepresentativeQuantifier SourceRepresentativeRenaming.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_named_representation_exists_forward M rep original namedex targetbody targetex rb rc rn delta :
 source_bounded M rep(code_numeral M 2) ->
 sf_relation M SFAnd(representation_named_member02 M)rep original ->
 source_named_quantifier M false(zeroM M)original namedex ->
 renaming_lookup M rb rc rn delta(zeroM M)(code_numeral M 1) ->
 renaming_lookup M rb rc rn delta(code_numeral M 2)(code_numeral M 2) ->
 sf_relation M SFAnd(code_numeral M(sf_make SFMember 0 3))rep targetbody ->
 sf_relation M SFEx targetbody(zeroM M)targetex ->
 numerical_renaming M targetex rb rc rn delta namedex.
Proof.
 intros BRep HOriginal(sb&sc&closed&HM&HClosed&HEx)HZero HTwo HTarget HTargetEx.
 destruct(proj1(numerical_renaming_binary M SFAnd(representation_named_member02 M)rep original
  sb sc(succM M(zeroM M))(code_numeral M 1)closed(or_introl eq_refl)HOriginal)HClosed)
  as(member&repr&HRMember&HRRep&HBody).
 assert(HMem:numerical_renaming M(representation_named_member02 M)sb sc(succM M(zeroM M))(code_numeral M 1)
   (code_numeral M(sf_make SFMember 0 3))).
 { apply(proj2(numerical_renaming_member M(zeroM M)(code_numeral M 2)(representation_named_member02 M)
    sb sc(succM M(zeroM M))(code_numeral M 1)(code_numeral M(sf_make SFMember 0 3))(sf_make_numeral M SFMember 0 2))).
   exists(zeroM M),(code_numeral M 3). split.
   - apply(proj2(HM(zeroM M)(zeroM M))). now left.
   - split;[|exact(sf_make_numeral M SFMember 0 3)].
     apply(proj2(HM(code_numeral M 2)(code_numeral M 3))). right.
     exact(conj(source_fixed_numeral_neq M 2 0 ltac:(lia))eq_refl). }
 rewrite(numerical_renaming_functional M _ sb sc _ _ member _ HRMember HMem)in HBody.
 destruct(renaming_lift_total M rb rc rn delta)as(lb&lc&ln&HLift).
 assert(HId:numerical_renaming M rep(zeroM M)(zeroM M)(zeroM M)(zeroM M)rep).
 { apply(numerical_renaming_identity_on_bound M rep _ _ _ _(code_numeral M 2)BRep).
   intros i _. apply source_empty_renaming_lookup. }
 assert(HRep:numerical_renaming M rep lb lc ln delta repr).
 { apply(numerical_source_renaming_diamond M rep(code_numeral M 2)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)
    sb sc(succM M(zeroM M))(code_numeral M 1)
    lb lc ln delta rep rep repr BRep HId HId HRRep).
   intros i j l m HI HJ HClose HL.
   rewrite(renaming_lookup_functional M _ _ _ _ i j i HJ(source_empty_renaming_lookup M i))in HClose.
   rewrite(renaming_lookup_functional M _ _ _ _ i l i HL(source_empty_renaming_lookup M i)).
   destruct(source_numeral_initial_segment M 2 i HI)as(index&HN&->).
   destruct index as[|[|index]];try lia.
   - apply(proj1(HM(zeroM M)m))in HClose. destruct HClose as[[_ ->]|[H _]];[|contradiction].
     exact(proj2(renaming_lift_head M rb rc rn delta lb lc ln(zeroM M)HLift)eq_refl).
   - apply(proj1(HM(code_numeral M 1)m))in HClose. destruct HClose as[[E _]|[_ ->]].
     + exfalso. exact(source_fixed_numeral_neq M 1 0 ltac:(lia)E).
     + exact(proj2(renaming_lift_tail M rb rc rn delta lb lc ln(zeroM M)(code_numeral M 1)HLift)HZero). }
 assert(HMember:numerical_renaming M(code_numeral M(sf_make SFMember 0 3))lb lc ln delta
   (code_numeral M(sf_make SFMember 0 3))).
 { apply(proj2(numerical_renaming_member M(zeroM M)(code_numeral M 3)(code_numeral M(sf_make SFMember 0 3))
    lb lc ln delta(code_numeral M(sf_make SFMember 0 3))(sf_make_numeral M SFMember 0 3))).
   exists(zeroM M),(code_numeral M 3). split.
   - exact(proj2(renaming_lift_head M rb rc rn delta lb lc ln(zeroM M)HLift)eq_refl).
   - split;[|exact(sf_make_numeral M SFMember 0 3)].
     exact(proj2(renaming_lift_tail M rb rc rn delta lb lc ln(code_numeral M 2)(code_numeral M 2)HLift)HTwo). }
 apply(proj2(numerical_renaming_quantifier M false targetbody targetex rb rc rn delta namedex HTargetEx)).
 exists lb,lc,ln,closed. split;[exact HLift|]. split;[|exact HEx].
 apply(proj2(numerical_renaming_binary M SFAnd(code_numeral M(sf_make SFMember 0 3))rep targetbody
  lb lc ln delta closed(or_introl eq_refl)HTarget)).
 exists(code_numeral M(sf_make SFMember 0 3)),repr. exact(conj HMember(conj HRep HBody)).
Qed.

Theorem source_auxiliary_representation_exists_forward M rep named r member matrix namedex targetbody targetex b c n delta :
 source_bounded M rep(code_numeral M 2) ->~coding_lt M r(code_numeral M 3) ->
 source_representative_renaming M r rep named ->sf_relation M SFMember r(code_numeral M 2)member ->
 sf_relation M SFAnd member named matrix ->source_named_quantifier M false r matrix namedex ->
 renaming_lookup M b c n delta(zeroM M)(code_numeral M 1) ->
 renaming_lookup M b c n delta(code_numeral M 2)(code_numeral M 2) ->
 sf_relation M SFAnd(code_numeral M(sf_make SFMember 0 3))rep targetbody ->sf_relation M SFEx targetbody(zeroM M)targetex ->
 numerical_renaming M targetex b c n delta namedex.
Proof.
 intros BRep HR HNamed HMember HMatrix HEx HZero HTwo HBody HTarget.
 destruct(sf_relation_total M SFAnd(representation_named_member02 M)rep)as(original&HO).
 destruct(source_named_quantifier_total M false(zeroM M)original)as(originalex&HOriginalEx).
 rewrite(source_representative_quantifier_normalization M false original matrix r(code_numeral M 3)namedex originalex
  (source_representation_witness_body_bound M rep original BRep HO) HR
  (source_representative_witness_body_renaming M r rep named member original matrix HNamed HMember HO HMatrix)HEx HOriginalEx).
 exact(source_named_representation_exists_forward M rep original originalex targetbody targetex b c n delta
  BRep HO HOriginalEx HZero HTwo HBody HTarget).
Qed.
Print Assumptions source_named_representation_exists_forward.
Print Assumptions source_auxiliary_representation_exists_forward.
