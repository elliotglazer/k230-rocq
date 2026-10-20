(** A condition using only the representative and carrier remains outside
    one actual Dn step. The three-cycle agrees with ordinary shift below2. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
 SetFormulaCodes SourceBounded SourceBoundMonotone SourceQuantifierRules SourceDnStep SourceNumeralLift
 SourceSubstitutionIdentity SourceSubstitutionRenaming SourceShiftSpecialization NumericalSubstitutionMaps NumericalSubstitution
 NumericalRenamingMaps NumericalRenaming RenamingSubstitution
 SourceDescriptorProvability SourceDescriptorClosure SourceDescriptorConditionalMap
 NumericalContexts NumericalEnvironments NumericalContextRenaming SourceClosedContextShift
 SourceContextProofHelpers SourceContextTransport SourceProofWeakening SourceSequents
 SourceTraceBounds NumericalSourceFull SourceDerivedRules SourceImplicationAllShift.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma source_dn_rotate_condition_shift M condition shifted rotated :
 source_bounded M condition(code_numeral M 2) ->source_formula_shift M condition shifted ->
 numerical_renaming M condition(code_numeral M 1653)(code_numeral M 6)
  (code_numeral M 3)(zeroM M) rotated ->rotated=shifted.
Proof.
 intros HC HS HR.
 assert(HI:numerical_substitution M condition(zeroM M)(zeroM M)(zeroM M)(zeroM M) condition).
 { apply(numerical_substitution_identity_on_bound M condition _ _ _ _ (code_numeral M 2) HC).
   intros i _. apply source_empty_substitution_lookup. }
 assert(HT:numerical_substitution M condition(code_numeral M 1653)(code_numeral M 6)
   (code_numeral M 3)(code_numeral M 3) shifted).
 { apply(numerical_substitution_then_renaming M condition(code_numeral M 2)
    (zeroM M)(zeroM M)(zeroM M)(zeroM M)
    (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
    (code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(code_numeral M 3)
    condition shifted HC HI HS).
   intros i j v HB HJ HV.
   assert(EJ:j=i)by(eapply substitution_lookup_functional;[exact HJ|apply source_empty_substitution_lookup]).
   subst j. apply context_shift_lookup in HV. subst v.
   assert(HR':renaming_lookup M(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)
     (zeroM M) i(succM M i)).
   { destruct(source_numeral_initial_segment M 2 i HB)as(index&HIndex&->).
     destruct index as[|[|index]];try lia.
     - exact(source_dn_rotate_zero M).
     - exact(source_dn_rotate_one M). }
   pose proof(proj1(renaming_substitution_lookup M _ _ _ _ _ _) HR')as HT'.
   now rewrite coding_add_zero_r in HT'. }
 assert(HT':numerical_renaming M condition(code_numeral M 1653)(code_numeral M 6)
   (code_numeral M 3)(zeroM M) shifted).
 { apply(proj2(numerical_renaming_substitution M condition _ _ _ _ shifted)).
   now rewrite coding_add_zero_r. }
 exact(numerical_renaming_functional M condition _ _ _ _ rotated shifted HR HT').
Qed.

Theorem source_descriptor_conditional_guarded_all_intro M T condition shifted matrix guard point guarded target result k :
 source_bounded M condition k ->source_bounded M matrix(succM M k) ->
 source_bounded M guard(succM M k) ->source_formula_shift M condition shifted ->
 sf_relation M SFImpl shifted matrix point ->sf_relation M SFImpl guard matrix guarded ->
 sf_relation M SFAll guarded(zeroM M) target ->sf_relation M SFImpl condition target result ->
 source_descriptor_provable M T point ->source_descriptor_provable M T result.
Proof.
 intros HC HM HG HS HP HGM HAll HResult(b&c&n&HCtx&PP).
 pose proof(source_shift_bound M condition shifted k HC HS)as HSC.
 assert(BG:source_bounded M guarded(succM M k)).
 { exact(proj2(source_bounded_accept_binary M SFImpl guard matrix guarded(succM M k)
   (or_intror(or_intror eq_refl)) HGM)(conj HG HM)). }
 assert(BT:source_bounded M target k).
 { exact(proj2(source_bounded_accept_unary M SFAll guarded target k(or_introl eq_refl) HAll) BG). }
 assert(BR:source_bounded M result k).
 { exact(proj2(source_bounded_accept_binary M SFImpl condition target result k
   (or_intror(or_intror eq_refl)) HResult)(conj HC BT)). }
 destruct(environment_cons_total M b c n condition)as(b1&c1&n1&H1).
 destruct(environment_cons_total M b c n shifted)as(b2&c2&n2&H2).
 assert(En:n2=n1)by(rewrite(proj1 H1),(proj1 H2);reflexivity). subst n2.
 assert(C0:context_bounded M b c n k).
 { exact(context_bounded_monotone M b c n(zeroM M) k(proj1 HCtx)(coding_zero_lt_succ M k)). }
 assert(C1:context_bounded M b1 c1 n1 k).
 { exact(proj2(context_bounded_cons M b c n condition b1 c1 n1 k H1)(conj HC C0)). }
 assert(C2:context_bounded M b2 c2 n1(succM M k)).
 { apply(proj2(context_bounded_cons M b c n shifted b2 c2 n1(succM M k) H2)).
   split;[exact HSC|]. exact(context_bounded_monotone M b c n(zeroM M)(succM M k)
     (proj1 HCtx)(coding_zero_lt_succ M(succM M k))). }
 pose proof(source_full_cons_weaken M b c n shifted b2 c2 n1(succM M k) point H2 C2 PP)as PP2.
 pose proof(source_full_cons_head M b c n shifted b2 c2 n1(succM M k) H2 HSC C2)as PC2.
 pose proof(source_full_modus_ponens M b2 c2 n1 shifted matrix point HP PP2 PC2)as PM.
 destruct(environment_cons_total M b2 c2 n1 guard)as(b3&c3&n3&H3).
 assert(C3:context_bounded M b3 c3 n3(succM M k)).
 { exact(proj2(context_bounded_cons M b2 c2 n1 guard b3 c3 n3(succM M k) H3)(conj HG C2)). }
 pose proof(source_full_cons_weaken M b2 c2 n1 guard b3 c3 n3(succM M k) matrix H3 C3 PM)as PM3.
 pose proof(full_source_II M b2 c2 n1 guard matrix guarded b3 c3 n3
   (ex_intro _ (succM M k)(conj BG C2)) PM3 H3 HGM)as PG.
 assert(HShift:context_shift M b1 c1 n1 b2 c2).
 { exact(context_renaming_cons M b c n(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
    b c condition shifted b1 c1 n1 b2 c2(source_closed_context_shift_self M b c n(proj1 HCtx)) HS H1 H2). }
 pose proof(full_source_AllI M b1 c1 n1 guarded target b2 c2(ex_intro _ k(conj BT C1)) PG HShift HAll)as PT.
 exists b,c,n. split;[exact HCtx|].
 exact(full_source_II M b c n condition target result b1 c1 n1(ex_intro _ k(conj BR C0)) PT H1 HResult).
Qed.

Theorem source_descriptor_dn_successor_conditional_intro M T condition previous out point result k :
 source_bounded M condition(code_numeral M 2) ->
 source_bounded M previous(succM M(succM M(succM M k))) ->
 source_dn_successor M previous out ->sf_relation M SFImpl condition previous point ->
 sf_relation M SFImpl condition out result ->source_descriptor_provable M T point ->
 source_descriptor_provable M T result.
Proof.
 intros HC HP(rot&guard&guarded&HR&HG&HGuard&HAll) HPoint HResult PP.
 destruct(numerical_renaming_total M condition(code_numeral M 1653)(code_numeral M 6)
   (code_numeral M 3)(zeroM M))as(shifted&HS).
 destruct(numerical_renaming_total M condition(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(shifted'&HS').
 pose proof(source_dn_rotate_condition_shift M condition shifted' shifted HC HS' HS)as E. subst shifted'.
 destruct(sf_relation_total M SFImpl shifted rot)as(rotpoint&HRotPoint).
 assert(HRPoint:numerical_renaming M point(code_numeral M 1653)(code_numeral M 6)
    (code_numeral M 3)(zeroM M) rotpoint).
 { apply(proj2(numerical_renaming_binary M SFImpl condition previous point _ _ _ _ rotpoint
    (or_intror(or_intror eq_refl)) HPoint)). exists shifted,rot. exact(conj HS(conj HR HRotPoint)). }
 apply(source_descriptor_conditional_guarded_all_intro M T condition shifted rot guard rotpoint guarded out result
   (succM M(succM M k))).
 - apply(source_bounded_monotone M condition(code_numeral M 2)(succM M(succM M k)) HC).
   do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ.
 - exact(source_dn_rotate_bounded M previous rot k HP HR).
 - apply(proj2(source_bounded_accept_atom M SFMember _ _ guard(succM M(succM M(succM M k)))
    (or_introl eq_refl) HG)). split;[apply coding_zero_lt_succ|].
   do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ.
 - exact HS'.
 - exact HRotPoint.
 - exact HGuard.
 - exact HAll.
 - exact HResult.
 - exact(source_descriptor_provable_renaming M T point _ _ _ _ rotpoint PP HRPoint).
Qed.

Print Assumptions source_dn_rotate_condition_shift.
Print Assumptions source_descriptor_conditional_guarded_all_intro.
Print Assumptions source_descriptor_dn_successor_conditional_intro.
