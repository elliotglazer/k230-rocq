(** Arbitrary-role naming of a closure-container witness. The representative
    matrix is an arbitrary internal source code bounded by two. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 SourceBounded NumericalRenamingMaps NumericalRenaming SourceRenamingIdentity SourceRenamingDiamond
 NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution SourceRoleReopening
 RawBinderRenaming SourceNamedQuantifierRules SourceShiftSpecialization SourceNumeralLift FixedSourceBounds.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_local_closure_witness_renaming M rep carrier container witness assigned rb rc rn
 openb openc member namedbody namedex originalbody originalex:
 source_bounded M rep(code_numeral M 2) ->witness<>carrier ->witness<>container ->
 source_role_reopening M carrier witness openb openc ->
 numerical_substitution M rep openb openc(code_numeral M 2)(code_numeral M 2)assigned ->
 renaming_lookup M rb rc rn(zeroM M)(zeroM M)carrier ->
 renaming_lookup M rb rc rn(zeroM M)(code_numeral M 2)container ->
 sf_relation M SFMember witness container member ->sf_relation M SFAnd member assigned namedbody ->
 source_named_quantifier M false witness namedbody namedex ->
 sf_relation M SFAnd(code_numeral M(sf_make SFMember 0 3))rep originalbody ->
 sf_relation M SFEx originalbody(zeroM M)originalex ->
 numerical_renaming M originalex rb rc rn(zeroM M)namedex.
Proof.
 intros BRep WA WC HOpen HAssigned HCarrier HContainer HMember HNamed
  (cb&cc&closed&HClose&HClosed&HEx)HOriginal HOriginalEx.
 assert(HAssignedRen:numerical_renaming M rep openb openc(code_numeral M 2)(zeroM M)assigned).
 { apply(proj2(numerical_renaming_substitution M rep openb openc(code_numeral M 2)(zeroM M)assigned)).
   now rewrite coding_add_zero_r. }
 assert(HHead:renaming_lookup M openb openc(code_numeral M 2)(zeroM M)(zeroM M)witness).
 { apply(proj2(renaming_lookup_inside M openb openc(code_numeral M 2)(zeroM M)(zeroM M)witness(coding_zero_lt_succ M(code_numeral M 1)))).
   exact(proj1(substitution_lookup_inside M openb openc(code_numeral M 2)(zeroM M)(zeroM M)witness
    (coding_zero_lt_succ M(code_numeral M 1)))(proj1 HOpen)). }
 assert(HCarrierIn:renaming_lookup M openb openc(code_numeral M 2)(zeroM M)(code_numeral M 1)carrier).
 { apply(proj2(renaming_lookup_inside M openb openc(code_numeral M 2)(zeroM M)(code_numeral M 1)carrier(coding_lt_succ M(code_numeral M 1)))).
   exact(proj1(substitution_lookup_inside M openb openc(code_numeral M 2)(zeroM M)(code_numeral M 1)carrier
    (coding_lt_succ M(code_numeral M 1)))(proj2 HOpen)). }
 destruct(proj1(numerical_renaming_binary M SFAnd member assigned namedbody cb cc(succM M witness)(code_numeral M 1)
  closed(or_introl eq_refl)HNamed)HClosed)as(cm&cr&HCM&HCR&HBody).
 destruct(renaming_lift_total M rb rc rn(zeroM M))as(lb&lc&ln&HL).
 assert(HId:numerical_renaming M rep(zeroM M)(zeroM M)(zeroM M)(zeroM M)rep).
 { apply(numerical_renaming_identity_on_bound M rep _ _ _ _(code_numeral M 2)BRep).
   intros i _. apply source_empty_renaming_lookup. }
 assert(HRep:numerical_renaming M rep lb lc ln(zeroM M)cr).
 { apply(numerical_source_renaming_diamond M rep(code_numeral M 2)
    openb openc(code_numeral M 2)(zeroM M)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)
    cb cc(succM M witness)(code_numeral M 1)
    lb lc ln(zeroM M)assigned rep cr BRep HAssignedRen HId HCR).
   intros i j l m HI HJ HJM HIL.
   rewrite(renaming_lookup_functional M _ _ _ _ i l i HIL(source_empty_renaming_lookup M i)).
   destruct(source_numeral_initial_segment M 2 i HI)as(index&HN&->).
   destruct index as[|[|index]];try lia.
   - rewrite(renaming_lookup_functional M _ _ _ _ _ j witness HJ HHead)in HJM.
     apply(proj1(HClose witness m))in HJM. destruct HJM as[[_ ->]|[H _]];[|contradiction].
     exact(proj2(renaming_lift_head M rb rc rn(zeroM M)lb lc ln(zeroM M)HL)eq_refl).
   - rewrite(renaming_lookup_functional M _ _ _ _ _ j carrier HJ HCarrierIn)in HJM.
     apply(proj1(HClose carrier m))in HJM. destruct HJM as[[E _]|[_ ->]].
     + exfalso. exact(WA(eq_sym E)).
     + exact(proj2(renaming_lift_tail M rb rc rn(zeroM M)lb lc ln(zeroM M)carrier HL)HCarrier). }
 assert(HMem:numerical_renaming M(code_numeral M(sf_make SFMember 0 3))lb lc ln(zeroM M)cm).
 { destruct(proj1(numerical_renaming_member M witness container member cb cc(succM M witness)(code_numeral M 1)cm HMember)HCM)
    as(x&y&HX&HY&HM).
   apply(proj1(HClose witness x))in HX. destruct HX as[[_ ->]|[H _]];[|contradiction].
   apply(proj1(HClose container y))in HY. destruct HY as[[E _]|[_ ->]];[exfalso;exact(WC(eq_sym E))|].
   apply(proj2(numerical_renaming_member M(zeroM M)(code_numeral M 3)
    (code_numeral M(sf_make SFMember 0 3))lb lc ln(zeroM M)cm(sf_make_numeral M SFMember 0 3))).
   exists(zeroM M),(succM M container). split.
   - exact(proj2(renaming_lift_head M rb rc rn(zeroM M)lb lc ln(zeroM M)HL)eq_refl).
   - split;[|exact HM]. exact(proj2(renaming_lift_tail M rb rc rn(zeroM M)lb lc ln(code_numeral M 2)container HL)HContainer). }
 apply(proj2(numerical_renaming_quantifier M false originalbody originalex rb rc rn(zeroM M)namedex HOriginalEx)).
 exists lb,lc,ln,closed. split;[exact HL|]. split;[|exact HEx].
 apply(proj2(numerical_renaming_binary M SFAnd(code_numeral M(sf_make SFMember 0 3))rep originalbody
  lb lc ln(zeroM M)closed(or_introl eq_refl)HOriginal)). exists cm,cr. auto.
Qed.
Print Assumptions source_local_closure_witness_renaming.
