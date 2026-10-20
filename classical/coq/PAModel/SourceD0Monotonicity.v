(** Actual D0 monotonicity, closing the hierarchy witness and universal
    quantifiers. The only auxiliary proof inputs are two literal fixed
    hierarchy laws in an explicitly included closed axiom context. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming
  NumericalInstantiation NumericalSourceFull SourceQuantifierRules SourceProofWeakening SourceProofShiftCons
  SourceContextTransport SourceClosedContextShift SourceLeastOrdinalWitness SourceContextProofHelpers
  SourceFiniteCutoffShift SourceD0At SourceD0Instances SourceD0Recipe SourceD0MonotonePoint SourceEwMonotone SourceEwShift
  SourceHierarchySyntax SourceHierarchyExistsShell SourceHierarchySubsetShell SourceHierarchyShifts
  SourceOrdinalPredicate SourceDomainInstances SourceRawSubset SourceDerivedRules SourceRelativizationRules
  SourceRelativizationBounds.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Definition source_d0_monotone_laws M d e lawEx lawSub :=
  (exists od body ex,source_hierarchy_exists_shell M (succM M d) od body ex lawEx) /\
  (exists od oe subset ld le result,source_hierarchy_subset_shell M
    (succM M (succM M d)) (succM M (succM M e)) (zeroM M) (code_numeral M 1)
    od oe subset ld le result lawSub).

Theorem source_full_d0_monotone M b c n ab ac an k domain phi d e od oe subset d0d d0e lawEx lawSub :
  context_bounded M b c n k ->context_bounded M ab ac an (zeroM M) ->
  context_included M ab ac an b c n ->source_bounded M domain (code_numeral M 1) ->
  source_bounded M phi (succM M k) ->coding_lt M d k ->coding_lt M e k ->
  numerical_instantiation M (source_ordinal_predicate_code M) d od ->
  numerical_instantiation M (source_ordinal_predicate_code M) e oe ->source_raw_subset_graph M d e subset ->
  source_d0_at M domain phi d d0d ->source_d0_at M domain phi e d0e ->
  source_d0_monotone_laws M d e lawEx lawSub ->
  source_full_prv M ab ac an lawEx ->source_full_prv M ab ac an lawSub ->
  source_full_prv M b c n od ->source_full_prv M b c n oe ->source_full_prv M b c n subset ->
  source_full_prv M b c n d0d ->source_full_prv M b c n d0e.
Proof.
  intros HC HAC HIncl HD HB HDN HEN HOD HOE HSub HD0 HE0
    [(ods&exBody&ex&HExShell) (odd&oee&sub2&ld2&le2&result2&HSubShell)] PExLaw PSubLaw POD POE PSub P0.
  pose proof HExShell as (HODS&HExBody&HEx&HExImp).
  pose proof HSubShell as (HODD&HOEE&HSub2&HLD2&HLE2&HResult2&HSubLawGraph).
  destruct HE0 as (phi1&le&ew&point&HShiftPhi&HLE&HEW&HPoint&HAll).
  pose proof (source_cutoff_shift_bounded M 1 phi phi1 k HB HShiftPhi) as HB1.
  destruct (source_cutoff_shift_total M 1 phi1) as (phi2&HShiftPhi1).
  pose proof (source_cutoff_shift_bounded M 1 phi1 phi2 (succM M k) HB1 HShiftPhi1) as HB2.
  pose proof (source_ew_recipe_bounded M domain phi1 ew k HD HB1 HEW) as BEW.
  pose proof (source_LL_instance_bounded M (succM M e) (zeroM M) le (succM M k)
    (proj2 (coding_lt_succ_cancel M e k) HEN) (coding_zero_lt_succ M k) HLE) as BLE.
  assert (BPoint:source_bounded M point (succM M k)).
  { exact (proj2 (source_bounded_accept_binary M SFImpl le ew point (succM M k)
      (or_intror (or_intror eq_refl)) HPoint) (conj BLE BEW)). }
  pose proof (source_d0_at_bounded M domain phi e d0e k HD HB HEN
    (ex_intro _ phi1 (ex_intro _ le (ex_intro _ ew (ex_intro _ point
      (conj HShiftPhi (conj HLE (conj HEW (conj HPoint HAll))))))))) as BGoal.
  destruct (context_shift_total M b c n) as (sb&sc&HS).
  pose proof (context_shift_preserves_bound M b c n sb sc k HS HC) as HSC.
  destruct (environment_cons_total M sb sc n le) as (cb&cc&cn&HConsL).
  pose proof (proj2 (context_bounded_cons M sb sc n le cb cc cn (succM M k) HConsL)
    (conj BLE HSC)) as HCC.
  pose proof (source_closed_context_shift_self M ab ac an HAC) as HAxShift.
  pose proof (source_context_included_shift M ab ac an b c n ab ac sb sc HIncl HAxShift HS) as HInclS.
  assert (HInclC:context_included M ab ac an cb cc cn).
  { intros f HF. exact (source_cons_tail_inclusion M sb sc n le cb cc cn HConsL f (HInclS f HF)). }
  destruct (context_shift_total M cb cc cn) as (tb&tc&HT).
  pose proof (context_shift_preserves_bound M cb cc cn tb tc (succM M k) HT HCC) as HTC.
  pose proof (source_LL_instance_functional M (succM M (succM M d)) (zeroM M) exBody ld2 HExBody HLD2) as E.
  subst exBody.
  pose proof (source_LL_instance_bounded M (succM M (succM M d)) (zeroM M) ld2
    (succM M (succM M k)) (proj2 (coding_lt_succ_cancel M (succM M d) (succM M k))
      (proj2 (coding_lt_succ_cancel M d k) HDN)) (coding_zero_lt_succ M (succM M k)) HLD2) as BLD2.
  destruct (environment_cons_total M tb tc cn ld2) as (ub&uc&un&HConsD).
  pose proof (proj2 (context_bounded_cons M tb tc cn ld2 ub uc un (succM M (succM M k)) HConsD)
    (conj BLD2 HTC)) as HUC.
  pose proof (source_context_included_shift M ab ac an cb cc cn ab ac tb tc HInclC HAxShift HT) as HInclT.
  assert (HInclU:context_included M ab ac an ub uc un).
  { intros f HF. exact (source_cons_tail_inclusion M tb tc cn ld2 ub uc un HConsD f (HInclT f HF)). }
  destruct (numerical_instantiation_total M (source_ordinal_predicate_code M) (succM M e)) as (oes&HOES).
  destruct (source_raw_subset_total M (succM M d) (succM M e)) as (sub1&HSub1).
  destruct (numerical_renaming_total M d0d (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)) as (d01&HR01).
  pose proof (source_d0_at_shift M domain phi phi1 d d0d d01 (succM M k) HD HB HShiftPhi HD0 HR01) as HD01.
  pose proof (source_full_prv_shift_cons M b c n sb sc cb cc cn le od ods (succM M k)
    HS HConsL HCC (source_domain_shift_to M (source_ordinal_predicate_code M) d od ods
      (source_ordinal_predicate_bounded M) HOD HODS) POD) as PODS.
  pose proof (source_full_prv_shift_cons M b c n sb sc cb cc cn le oe oes (succM M k)
    HS HConsL HCC (source_domain_shift_to M (source_ordinal_predicate_code M) e oe oes
      (source_ordinal_predicate_bounded M) HOE HOES) POE) as POES.
  pose proof (source_full_prv_shift_cons M b c n sb sc cb cc cn le subset sub1 (succM M k)
    HS HConsL HCC (source_raw_subset_shift_to M d e subset sub1 HSub HSub1) PSub) as PS1.
  pose proof (source_full_prv_shift_cons M b c n sb sc cb cc cn le d0d d01 (succM M k)
    HS HConsL HCC HR01 P0) as P01.
  pose proof (source_full_cons_head M sb sc n le cb cc cn (succM M k) HConsL BLE HCC) as PLE.
  pose proof (source_full_prv_weaken_bounded M ab ac an cb cc cn lawEx (succM M k)
    PExLaw HInclC HCC) as PExLawC.
  pose proof (source_full_modus_ponens M cb cc cn ods ex lawEx HExImp PExLawC PODS) as PEx.
  pose proof (source_full_prv_shift_cons M cb cc cn tb tc ub uc un ld2 ods odd (succM M (succM M k))
    HT HConsD HUC (source_domain_shift_to M (source_ordinal_predicate_code M) (succM M d) ods odd
      (source_ordinal_predicate_bounded M) HODS HODD) PODS) as PODD.
  pose proof (source_full_prv_shift_cons M cb cc cn tb tc ub uc un ld2 oes oee (succM M (succM M k))
    HT HConsD HUC (source_domain_shift_to M (source_ordinal_predicate_code M) (succM M e) oes oee
      (source_ordinal_predicate_bounded M) HOES HOEE) POES) as POEE.
  pose proof (source_full_prv_shift_cons M cb cc cn tb tc ub uc un ld2 sub1 sub2 (succM M (succM M k))
    HT HConsD HUC (source_raw_subset_shift_to M (succM M d) (succM M e) sub1 sub2 HSub1 HSub2) PS1) as PS2.
  pose proof (source_full_prv_shift_cons M cb cc cn tb tc ub uc un ld2 le le2 (succM M (succM M k))
    HT HConsD HUC (source_LL_shift_to M (succM M e) (zeroM M) le le2 HLE HLE2) PLE) as PLE2.
  destruct (numerical_renaming_total M d01 (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)) as (d02&HR02).
  pose proof (source_d0_at_shift M domain phi1 phi2 (succM M d) d01 d02 (succM M (succM M k))
    HD HB1 HShiftPhi1 HD01 HR02) as HD02.
  pose proof (source_full_prv_shift_cons M cb cc cn tb tc ub uc un ld2 d01 d02 (succM M (succM M k))
    HT HConsD HUC HR02 P01) as P02.
  pose proof (source_full_cons_head M tb tc cn ld2 ub uc un (succM M (succM M k)) HConsD BLD2 HUC) as PLD2.
  pose proof (source_full_prv_weaken_bounded M ab ac an ub uc un lawSub (succM M (succM M k))
    PSubLaw HInclU HUC) as PSubLawU.
  destruct (source_ew_recipe_total M domain phi2) as (ewU&HEWU).
  destruct (sf_relation_total M SFMember (zeroM M) (code_numeral M 2)) as (atomV&HAtomV).
  destruct (sr_quantifier_total M false domain phi2) as (leftV&HLeftV).
  destruct (sr_quantifier_total M false atomV phi2) as (rightV&HRightV).
  destruct (sf_relation_total M SFImpl leftV rightV) as (ewV&HEWV).
  assert (HAtV:source_ew_at M domain phi2 (code_numeral M 1) ewV).
  { exists atomV,leftV,rightV. repeat split;assumption. }
  pose proof (source_full_d0_monotone_point M ub uc un (succM M (succM M k)) domain phi2
    (succM M (succM M d)) (succM M (succM M e)) (zeroM M) (code_numeral M 1)
    d02 odd oee sub2 ld2 le2 result2 lawSub ewU ewV HUC HD HB2
    (coding_zero_lt_succ M (succM M k))
    (proj2 (coding_lt_succ_cancel M (zeroM M) (succM M k)) (coding_zero_lt_succ M k))
    HD02 (conj HODD (conj HOEE (conj HSub2 (conj HLD2 (conj HLE2 (conj HResult2 HSubLawGraph))))))
    HEWU HAtV PSubLawU PODD POEE PS2 PLD2 PLE2 P02) as PEWV.
  pose proof (source_ew_at_shift M domain phi1 phi2 (zeroM M) ew ewV HD HShiftPhi1 HEW HAtV) as HEWShift.
  pose proof (full_source_ExE M cb cc cn ld2 ex ew ewV tb tc ub uc un
    (ex_intro _ (succM M k) (conj BEW HCC)) PEx PEWV HEx HT HConsD HEWShift) as PEW.
  pose proof (full_source_II M sb sc n le ew point cb cc cn
    (ex_intro _ (succM M k) (conj BPoint HSC)) PEW HConsL HPoint) as PPoint.
  exact (full_source_AllI M b c n point d0e sb sc (ex_intro _ k (conj BGoal HC)) PPoint HS HAll).
Qed.

Print Assumptions source_full_d0_monotone.
