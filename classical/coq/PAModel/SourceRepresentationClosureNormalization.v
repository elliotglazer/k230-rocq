(** Exact coordinate normalization of a named representation witness.
    The exterior carrier1 moves to carrier0, while exterior container2
    remains2. The quantified representative itself stays bound at0. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 NumericalRenamingMaps NumericalRenaming SourceRenamingIdentity SourceRenamingDiamond SourceShiftSpecialization
 RawBinderRenaming SourceNamedQuantifierRules SourceRepresentationNamedWitness SourceNamedFiniteCalibration.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_named_representation_exists_rename M rep original namedex targetbody targetex rb rc rn delta :
 source_bounded M rep(code_numeral M 2) ->
 sf_relation M SFAnd(representation_named_member02 M)rep original ->
 source_named_quantifier M false(zeroM M)original namedex ->
 renaming_lookup M rb rc rn delta(code_numeral M 1)(zeroM M) ->
 renaming_lookup M rb rc rn delta(code_numeral M 2)(code_numeral M 2) ->
 sf_relation M SFAnd(code_numeral M(sf_make SFMember 0 3))rep targetbody ->
 sf_relation M SFEx targetbody(zeroM M)targetex ->
 numerical_renaming M namedex rb rc rn delta targetex.
Proof.
 intros BRep HOriginal(sb&sc&closed&HM&HClosed&HEx)HOne HTwo HTarget HTargetEx.
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
 assert(HRep:numerical_renaming M repr lb lc ln delta rep).
 { apply(numerical_source_renaming_diamond M rep(code_numeral M 2)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)
    sb sc(succM M(zeroM M))(code_numeral M 1)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M) lb lc ln delta rep repr rep BRep HId HRRep HId).
   intros i j l m HI HJ HJM HClose.
   rewrite(renaming_lookup_functional M _ _ _ _ i j i HJ(source_empty_renaming_lookup M i))in HJM.
   rewrite(renaming_lookup_functional M _ _ _ _ i m i HJM(source_empty_renaming_lookup M i)).
   destruct(source_numeral_initial_segment M 2 i HI)as(index&HN&->).
   destruct index as[|[|index]];try lia.
   - apply(proj1(HM(zeroM M)l))in HClose. destruct HClose as[[_ ->]|[H _]];[|contradiction].
     exact(proj2(renaming_lift_head M rb rc rn delta lb lc ln(zeroM M)HLift)eq_refl).
   - apply(proj1(HM(code_numeral M 1)l))in HClose. destruct HClose as[[E _]|[_ ->]].
     + exfalso. exact(source_fixed_numeral_neq M 1 0 ltac:(lia)E).
     + exact(proj2(renaming_lift_tail M rb rc rn delta lb lc ln(code_numeral M 1)(zeroM M)HLift)HOne). }
 assert(HMember:numerical_renaming M(code_numeral M(sf_make SFMember 0 3))lb lc ln delta
   (code_numeral M(sf_make SFMember 0 3))).
 { apply(proj2(numerical_renaming_member M(zeroM M)(code_numeral M 3)(code_numeral M(sf_make SFMember 0 3))
    lb lc ln delta(code_numeral M(sf_make SFMember 0 3))(sf_make_numeral M SFMember 0 3))).
   exists(zeroM M),(code_numeral M 3). split.
   - exact(proj2(renaming_lift_head M rb rc rn delta lb lc ln(zeroM M)HLift)eq_refl).
   - split;[|exact(sf_make_numeral M SFMember 0 3)].
     exact(proj2(renaming_lift_tail M rb rc rn delta lb lc ln(code_numeral M 2)(code_numeral M 2)HLift)HTwo). }
 apply(proj2(numerical_renaming_quantifier M false closed namedex rb rc rn delta targetex HEx)).
 exists lb,lc,ln,targetbody. split;[exact HLift|]. split;[|exact HTargetEx].
 apply(proj2(numerical_renaming_binary M SFAnd(code_numeral M(sf_make SFMember 0 3))repr closed
  lb lc ln delta targetbody(or_introl eq_refl)HBody)).
 exists(code_numeral M(sf_make SFMember 0 3)),rep. exact(conj HMember(conj HRep HTarget)).
Qed.

Print Assumptions source_named_representation_exists_rename.
