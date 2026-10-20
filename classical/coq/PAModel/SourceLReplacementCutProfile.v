(** The actual finite range-cut deduction. A bounded L set carrying all
    constructible members of the ambient range is cut by L Separation;
    the resulting set has the exact relative Replacement profile. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalContextRenaming NumericalSourceFull SourceQuantifierRules
 SourcePropositionalTemplates SourceBooleanIffPrograms SourceUniversalPropositional.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
(* Slots: L(z), z in ambient range, z in bounding level, z in output, image(z). *)
Definition lrep_range_point:=SPTImpl(SPTSlot 0)(tv_iff_template(SPTSlot 1)(SPTSlot 4)).
Definition lrep_cover_point:=SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 0)(SPTSlot 2)).
Definition lrep_selection_point:=SPTImpl(SPTSlot 0)(tv_iff_template(SPTSlot 3)(SPTAnd(SPTSlot 2)(SPTSlot 4))).
Definition lrep_cut_point:=SPTImpl(SPTSlot 0)(tv_iff_template(SPTSlot 3)(SPTSlot 4)).
Definition lrep_cut_inputs:=[lrep_range_point;lrep_cover_point;lrep_selection_point].
Lemma lrep_cut_program:source_prop_program lrep_cut_inputs lrep_cut_point.
Proof.
 unfold lrep_cut_point. apply SPTII. unfold tv_iff_template;apply SPTCI.
 - apply SPTII. set(A:=SPTSlot 3::SPTSlot 0::lrep_cut_inputs).
   assert(PD:source_prop_program A(SPTSlot 0))by(apply SPTCtx;unfold A;cbn;tauto).
   assert(PB:source_prop_program A(SPTSlot 3))by(apply SPTCtx;unfold A;now left).
   assert(PS:source_prop_program A lrep_selection_point)by(apply SPTCtx;unfold A,lrep_cut_inputs;cbn;tauto).
   assert(PIff:source_prop_program A(tv_iff_template(SPTSlot 3)(SPTAnd(SPTSlot 2)(SPTSlot 4)))).
   { eapply SPTIE;[exact PS|exact PD]. }
   apply(SPTCE2 A(SPTSlot 2)). eapply SPTIE;[eapply SPTCE1;exact PIff|exact PB].
 - apply SPTII. set(A:=SPTSlot 4::SPTSlot 0::lrep_cut_inputs).
   assert(PD:source_prop_program A(SPTSlot 0))by(apply SPTCtx;unfold A;cbn;tauto).
   assert(PT:source_prop_program A(SPTSlot 4))by(apply SPTCtx;unfold A;now left).
   assert(PR:source_prop_program A lrep_range_point)by(apply SPTCtx;unfold A,lrep_cut_inputs;cbn;tauto).
   assert(PC:source_prop_program A lrep_cover_point)by(apply SPTCtx;unfold A,lrep_cut_inputs;cbn;tauto).
   assert(PS:source_prop_program A lrep_selection_point)by(apply SPTCtx;unfold A,lrep_cut_inputs;cbn;tauto).
   assert(PRiff:source_prop_program A(tv_iff_template(SPTSlot 1)(SPTSlot 4)))by(eapply SPTIE;[exact PR|exact PD]).
   assert(PZ:source_prop_program A(SPTSlot 1))by(eapply SPTIE;[eapply SPTCE2;exact PRiff|exact PT]).
   assert(PY:source_prop_program A(SPTSlot 2)).
   { eapply SPTIE;[eapply SPTIE;[exact PC|exact PZ]|exact PD]. }
   assert(PSiff:source_prop_program A(tv_iff_template(SPTSlot 3)(SPTAnd(SPTSlot 2)(SPTSlot 4))))by(eapply SPTIE;[exact PS|exact PD]).
   eapply SPTIE;[eapply SPTCE2;exact PSiff|]. apply SPTCI;assumption.
Qed.
Theorem source_full_L_replacement_cut_point M rho k b c n range cover selection result:
 (forall i,source_bounded M(rho i)k) ->context_bounded M b c n k ->
 code_relation M rho(source_prop_expression lrep_range_point)range ->
 code_relation M rho(source_prop_expression lrep_cover_point)cover ->
 code_relation M rho(source_prop_expression lrep_selection_point)selection ->
 code_relation M rho(source_prop_expression lrep_cut_point)result ->
 source_full_prv M b c n range ->source_full_prv M b c n cover ->source_full_prv M b c n selection ->source_full_prv M b c n result.
Proof.
 intros HB HC HR HG HS HT PR PG PS.
 apply(source_prop_program_sound M lrep_cut_inputs lrep_cut_point lrep_cut_program rho k b c n result HB HC);[|exact HT].
 intros a HA f HF. destruct HA as[<-|[<-|[<-|[]]]].
 - rewrite(code_relation_functional M _ rho f range HF HR);exact PR.
 - rewrite(code_relation_functional M _ rho f cover HF HG);exact PG.
 - rewrite(code_relation_functional M _ rho f selection HF HS);exact PS.
Qed.
Theorem source_full_L_replacement_cut_profile M rho k b c n range cover selection result allRange allCover allSelection allResult:
 (forall i,source_bounded M(rho i)(succM M k)) ->context_bounded M b c n k ->
 code_relation M rho(source_prop_expression lrep_range_point)range ->
 code_relation M rho(source_prop_expression lrep_cover_point)cover ->
 code_relation M rho(source_prop_expression lrep_selection_point)selection ->
 code_relation M rho(source_prop_expression lrep_cut_point)result ->
 sf_relation M SFAll range(zeroM M)allRange ->sf_relation M SFAll cover(zeroM M)allCover ->
 sf_relation M SFAll selection(zeroM M)allSelection ->sf_relation M SFAll result(zeroM M)allResult ->
 source_full_prv M b c n allRange ->source_full_prv M b c n allCover ->source_full_prv M b c n allSelection ->source_full_prv M b c n allResult.
Proof.
 intros HB HC HR HG HS HT HAR HAG HAS HAT PR PG PS.
 destruct(context_shift_total M b c n)as(sb&sc&HShift).
 apply(full_source_AllI M b c n result allResult sb sc);[| |exact HShift|exact HAT].
 - exists k. split;[|exact HC].
   apply(proj2(source_bounded_accept_unary M SFAll result allResult k(or_introl eq_refl)HAT)).
   exact(source_prop_template_bound M rho lrep_cut_point(succM M k)HB result HT).
 - apply(source_full_L_replacement_cut_point M rho(succM M k)sb sc n range cover selection result HB
    (context_shift_preserves_bound M b c n sb sc k HShift HC)HR HG HS HT).
   + exact(source_full_all_shift M b c n range allRange sb sc HAR PR HShift).
   + exact(source_full_all_shift M b c n cover allCover sb sc HAG PG HShift).
   + exact(source_full_all_shift M b c n selection allSelection sb sc HAS PS HShift).
Qed.
Print Assumptions lrep_cut_program.
Print Assumptions source_full_L_replacement_cut_point.
Print Assumptions source_full_L_replacement_cut_profile.
