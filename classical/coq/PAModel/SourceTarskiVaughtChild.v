(** The actual guarded child-induction proof used at both quantifiers.
    Old parameter and piece-witness proofs are shifted and weakened here. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs SetFormulaCodes
  SourceBounded SourceBoundMonotone SourceTraceBounds NumericalContexts NumericalEnvironments NumericalContextRenaming
  NumericalRenamingMaps NumericalRenaming SourceProofRenaming NumericalSourceFull SourceContextProofHelpers
  SourceRelativization SourceRelativizationBounds SourceSetRelativization SourceSetRelativizationBounds
  SourceIffGraphs SourceTarskiVaughtInputs SourceTarskiVaughtInvariant.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_tv_members_guarded_shift M cb cc cn ub uc gb gc gn count carrier guard k:
  context_shift M cb cc cn ub uc ->environment_cons M ub uc cn guard gb gc gn ->
  context_bounded M gb gc gn k ->source_bounded M guard k ->
  sf_relation M SFMember(zeroM M)(succM M carrier)guard ->
  source_tv_members M cb cc cn count carrier ->source_tv_members M gb gc gn(succM M count)(succM M carrier).
Proof.
  intros HC HG BC BG HGuard HM i member HI HMember.
  destruct(@Peano.zero_or_succ(Model.carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)
    as[E|(j&E)];subst i.
  - rewrite(sf_relation_functional M SFMember(zeroM M)(succM M carrier)member guard HMember HGuard).
    exact(source_full_cons_head M ub uc cn guard gb gc gn k HG BG BC).
  - pose proof(proj1(coding_lt_succ_cancel M j count)HI)as HJ.
    destruct(sf_relation_total M SFMember j carrier)as(old&HOld).
    pose proof(HM j old HJ HOld)as POld.
    assert(HR:numerical_renaming M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)member).
    { apply(proj2(numerical_renaming_member M j carrier old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)member HOld)).
      exists(succM M j),(succM M carrier). split;[apply context_shift_lookup;reflexivity|].
      split;[apply context_shift_lookup;reflexivity|exact HMember]. }
    exact(source_full_cons_weaken M ub uc cn guard gb gc gn k member HG BC
      (source_full_prv_renaming M cb cc cn old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)ub uc member POld HC HR)).
Qed.

Theorem source_full_tv_guarded_child M body domain count carrier left right equiv guard point all cb cc cn k:
  source_tv_at M body ->source_bounded M domain(code_numeral M 1) ->source_bounded M body(succM M count) ->
  context_bounded M cb cc cn k ->coding_lt M count(succM M k) ->coding_lt M carrier k ->
  source_relativization M domain body left ->source_set_relativization M(succM M carrier)body right ->
  source_iff_graph M left right equiv ->sf_relation M SFMember(zeroM M)(succM M carrier)guard ->
  sf_relation M SFImpl guard equiv point ->sf_relation M SFAll point(zeroM M)all ->
  source_tv_members M cb cc cn count carrier ->source_tv_witnesses M domain body(succM M count)carrier cb cc cn ->
  source_tv_containment M domain carrier cb cc cn ->source_full_prv M cb cc cn all.
Proof.
  intros IH HD HB BC HCount HY HL HR HE HG HP HQ HM HW HS.
  pose proof(proj2(coding_lt_succ_cancel M count(succM M k))HCount)as HCount'.
  pose proof(proj2(coding_lt_succ_cancel M carrier k)HY)as HY'.
  pose proof(source_bounded_monotone M body(succM M count)(succM M k)HB HCount')as BB.
  pose proof(source_relativization_preserves_bound M body domain(succM M k)left HD BB HL)as BL.
  pose proof(source_set_relativization_preserves_bound M body(succM M carrier)(succM M k)right HY' BB HR)as BR.
  pose proof(source_iff_bounded M left right equiv(succM M k)BL BR HE)as BE.
  assert(BG:source_bounded M guard(succM M k)).
  { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M carrier)guard(succM M k)(or_introl eq_refl)HG)).
    split;[apply coding_zero_lt_succ|exact HY']. }
  pose proof(proj2(source_bounded_accept_binary M SFImpl guard equiv point(succM M k)
    (or_intror(or_intror eq_refl))HP)(conj BG BE))as BP.
  pose proof(proj2(source_bounded_accept_unary M SFAll point all k(or_introl eq_refl)HQ)BP)as BA.
  destruct(context_shift_total M cb cc cn)as(ub&uc&HShift).
  pose proof(context_shift_preserves_bound M cb cc cn ub uc k HShift BC)as BShift.
  destruct(environment_cons_total M ub uc cn guard)as(gb&gc&gn&HCons).
  pose proof(proj2(context_bounded_cons M ub uc cn guard gb gc gn(succM M k)HCons)(conj BG BShift))as BGuard.
  assert(HIncl:context_included M ub uc cn gb gc gn).
  { intros f HF. apply(proj2(context_member_cons M ub uc cn guard gb gc gn f HCons)). now right. }
  pose proof(source_tv_members_guarded_shift M cb cc cn ub uc gb gc gn count carrier guard(succM M k)
    HShift HCons BGuard BG HG HM)as HM'.
  pose proof(source_tv_witnesses_weaken M domain body(succM M count)(succM M carrier)ub uc cn gb gc gn(succM M k)
    HIncl BGuard(source_tv_witnesses_shift M domain body(succM M count)carrier cb cc cn ub uc HD HB HShift HW))as HW'.
  pose proof(source_tv_containment_weaken M domain(succM M carrier)ub uc cn gb gc gn(succM M k)HIncl BGuard
    (source_tv_containment_shift M domain carrier cb cc cn ub uc HD HShift HS))as HS'.
  pose proof(IH domain(succM M count)(succM M carrier)left right equiv gb gc gn(succM M k)
    HD HB BGuard HCount' HY' HL HR HE HM' HW' HS')as PE.
  pose proof(full_source_II M ub uc cn guard equiv point gb gc gn
    (ex_intro _(succM M k)(conj BP BShift))PE HCons HP)as PP.
  exact(full_source_AllI M cb cc cn point all ub uc(ex_intro _ k(conj BA BC))PP HShift HQ).
Qed.
Print Assumptions source_tv_members_guarded_shift.
Print Assumptions source_full_tv_guarded_child.
