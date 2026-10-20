(** Named source proof rules with their actual context-vacuity conditions.
    These rules operate on source proof objects and numerical syntax graphs. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions
  SetFormulaCodes SourceBounded SourceBoundMonotone NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalRenamingMaps NumericalRenaming NumericalInstantiation
  SourceSequents SourceTraceBounds NumericalSourceFull SourceQuantifierRules
  SourceContextTransport SourceUniversalDistribution SourceInstantiationConstructors SourceImplicationAllShift
  SourceExistentialShift SourceProofWeakening SourceDerivedRules RawBinderRenaming
  SourceNamedSelfSpecialization SourceNamedVacuity.
Unset Implicit Arguments.

Theorem source_full_ignore_antecedent M b c n f g imp k :
  source_bounded M f k ->sf_relation M SFImpl f g imp ->source_full_prv M b c n g ->
  source_full_prv M b c n imp.
Proof.
  intros HF HI PG.
  pose proof (source_full_prv_wellformed M b c n g PG) as HWG.
  destruct HWG as (l&HG&HC).
  destruct (environment_cons_total M b c n f) as (u&v&m&HCons).
  assert (HBound:source_context_finite_bound M u v m).
  { apply (source_context_finite_bound_cons M b c n f u v m (ex_intro _ l HC)
      (ex_intro _ k HF) HCons). }
  apply (full_source_II M b c n f g imp u v m).
  - apply (source_wf_binary M b c n SFImpl f g imp (or_intror(or_intror eq_refl)) HI).
    + apply (source_bounded_in_context_wf M b c n f k HF). now exists l.
    + now exists l.
  - destruct HBound as (q&HQ).
    apply (source_full_prv_weaken_bounded M b c n u v m g q PG);[|exact HQ].
    intros h HH. apply (proj2 (context_member_cons M b c n f u v m h HCons)). now right.
  - exact HCons.
  - exact HI.
Qed.

Theorem source_full_and_intro M b c n f g both :
  sf_relation M SFAnd f g both ->source_full_prv M b c n f ->source_full_prv M b c n g ->
  source_full_prv M b c n both.
Proof.
  intros HB PF PG. apply (full_source_CI M b c n f g both);[|exact PF|exact PG|exact HB].
  exact (source_wf_binary M b c n SFAnd f g both (or_introl eq_refl) HB
    (source_full_prv_wellformed M b c n f PF)(source_full_prv_wellformed M b c n g PG)).
Qed.

Theorem source_full_existential_map_shift M b c n f g exf exg imp u v :
  sf_relation M SFEx f (zeroM M) exf ->sf_relation M SFEx g (zeroM M) exg ->
  sf_relation M SFImpl f g imp ->context_shift M b c n u v ->
  source_full_prv M b c n exf ->source_full_prv M u v n imp ->
  source_full_prv M b c n exg.
Proof.
  intros HEF HEG HI HShift PEF PI.
  destruct (source_full_prv_wellformed M u v n imp PI) as (k&HImpB&HUC).
  destruct (proj1 (source_bounded_accept_binary M SFImpl f g imp k
    (or_intror(or_intror eq_refl)) HI) HImpB) as (HFB&HGB).
  destruct (source_full_prv_wellformed M b c n exf PEF) as (l&_&HBC).
  assert (HExGB:source_bounded M exg k).
  { apply (proj2 (source_bounded_accept_unary M SFEx g exg k (or_intror eq_refl) HEG)).
    apply (source_bounded_monotone M g k (succM M k) HGB).
    apply coding_lt_trans with (y:=succM M k);apply coding_lt_succ. }
  assert (HWExG:source_sequent_wf M b c n exg).
  { apply (source_bounded_in_context_wf M b c n exg k HExGB). now exists l. }
  destruct (environment_cons_total M u v n f) as (d&e&m&HCons).
  pose proof (source_context_finite_bound_cons M u v n f d e m (ex_intro _ k HUC)
    (ex_intro _ k HFB) HCons) as HDC.
  destruct (numerical_renaming_total M exg (zeroM M)(zeroM M)(zeroM M)
    (succM M (zeroM M))) as (shifted&HS).
  destruct (source_shifted_ex_specialization M g exg shifted k HGB HEG HS)
    as (gr&HExShift&HInst).
  assert (HWShift:source_sequent_wf M d e m shifted).
  { apply (source_bounded_in_context_wf M d e m shifted (succM M k)
      (source_shift_bound M exg shifted k HExGB HS) HDC). }
  assert (PI':source_full_prv M d e m imp).
  { destruct HDC as (q&HQ). apply (source_full_prv_weaken_bounded M u v n d e m imp q PI);[|exact HQ].
    intros h HH. apply (proj2 (context_member_cons M u v n f d e m h HCons)). now right. }
  assert (PF:source_full_prv M d e m f).
  { apply full_source_Ctx.
    - apply (source_bounded_in_context_wf M d e m f k HFB HDC).
    - apply (proj2 (context_member_cons M u v n f d e m f HCons)). now left. }
  apply (full_source_ExE M b c n f exf exg shifted u v d e m HWExG PEF).
  - apply (full_source_ExI M d e m gr shifted (zeroM M) g HWShift).
    + exact (source_full_modus_ponens M d e m f g imp HI PI' PF).
    + exact HExShift.
    + exact HInst.
  - exact HEF.
  - exact HShift.
  - exact HCons.
  - exact HS.
Qed.

Theorem source_full_named_exists_map M b c n f g x rb rc fb gb exf exg imp :
  source_named_context_vacuous M b c n x ->raw_binder_renaming M x rb rc ->
  numerical_renaming M f rb rc (succM M x)(succM M (zeroM M)) fb ->
  numerical_renaming M g rb rc (succM M x)(succM M (zeroM M)) gb ->
  sf_relation M SFEx fb (zeroM M) exf ->sf_relation M SFEx gb (zeroM M) exg ->
  sf_relation M SFImpl f g imp ->source_full_prv M b c n imp ->source_full_prv M b c n exf ->
  source_full_prv M b c n exg.
Proof.
  intros HCtx HM HF HG HEF HEG HI PI PEF.
  destruct (context_shift_total M b c n) as (u&v&HShift).
  destruct (sf_relation_total M SFImpl fb gb) as (ib&HIB).
  assert (HR:numerical_renaming M imp rb rc (succM M x)(succM M (zeroM M)) ib).
  { apply (proj2 (numerical_renaming_binary M SFImpl f g imp rb rc (succM M x)
      (succM M (zeroM M)) ib (or_intror(or_intror eq_refl)) HI)). exists fb,gb. auto. }
  exact (source_full_existential_map_shift M b c n fb gb exf exg ib u v HEF HEG HIB HShift PEF
    (source_full_named_close_proof M b c n imp x rb rc ib u v HCtx HM HR HShift PI)).
Qed.

Print Assumptions source_full_existential_map_shift.
Print Assumptions source_full_named_exists_map.
