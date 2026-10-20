(** An actual witness in one hierarchy presentation supplies the complete
    universal D0 request. The two fixed laws are ordinary source proofs. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceSequents
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming NumericalInstantiation
  NumericalSourceFull SourceQuantifierRules SourceDerivedRules SourceDomainInstances SourceProofShiftCons
  SourceProofWeakening SourceLeastOrdinalWitness SourceUniversalPropositional SourceOrdinalPredicate
  SourceHierarchySyntax SourceHierarchyWitnessShell SourceD0At SourceCutoffInstantiation
  SourceFiniteCutoffShift SourceEWitness SourcePositiveWitnessPlan SourceWitnessAtomShift.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_full_positive_witness_request M b c n domain phi d y carrier
    ordinal known member instance request allUnique allMove k :
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi(succM M k) ->
  context_bounded M b c n k ->coding_lt M d k ->coding_lt M y k ->coding_lt M carrier k ->
  numerical_instantiation M(source_ordinal_predicate_code M)d ordinal ->
  source_LL_instance M d carrier known ->sf_relation M SFMember y carrier member ->
  numerical_instantiation M phi y instance ->source_d0_at M domain phi d request ->
  source_positive_witness_plan M d y carrier allUnique allMove ->
  source_full_prv M b c n ordinal ->source_full_prv M b c n known ->
  source_full_prv M b c n member ->source_full_prv M b c n instance ->
  source_full_prv M b c n allUnique ->source_full_prv M b c n allMove ->
  source_full_prv M b c n request.
Proof.
  intros HD HB HCtx HDB HYB HCB HOrd HKnown HMember HInstance HRequest
    (od&ld&le&equal&t1&t2&unique&oldMember&newMember&moveImp&move&
      HUnique&HOld&HNew&HMoveImp&HMove&HAU&HAM) POrd PKnown PMember PInstance PAU PAM.
  destruct HUnique as(HOD&HLD&HLE&HEqual&HT2&HT1&HU).
  pose proof(source_d0_at_bounded M domain phi d request k HD HB HDB HRequest) as HRequestBound.
  destruct HRequest as(matrix&level&ew&point&HC&HLevel&HEw&HPoint&HAll).
  pose proof(source_LL_instance_functional M(succM M d)(zeroM M)le level HLE HLevel) as E. subst le.
  pose proof(source_cutoff_shift_bounded M 1 phi matrix k HB HC) as HMatrixBound.
  pose proof(source_LL_instance_bounded M(succM M d)(zeroM M)level(succM M k)
    (proj2(coding_lt_succ_cancel M d k)HDB)(coding_zero_lt_succ M k)HLevel) as HLevelBound.
  destruct(context_shift_total M b c n) as(sb&sc&HShiftCtx).
  destruct(environment_cons_total M sb sc n level) as(ub&uc&un&HCons).
  assert(HBranch:context_bounded M ub uc un(succM M k)).
  { apply(proj2(context_bounded_cons M sb sc n level ub uc un(succM M k)HCons)).
    split;[exact HLevelBound|exact(context_shift_preserves_bound M b c n sb sc k HShiftCtx HCtx)]. }
  assert(PLevel:source_full_prv M ub uc un level).
  { apply full_source_Ctx;[exists(succM M k);auto|].
    apply(proj2(context_member_cons M sb sc n level ub uc un level HCons)). now left. }
  destruct(numerical_renaming_total M ordinal(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))
    as(ordinalShift&HOrdShift).
  pose proof(source_domain_instance_shift M(source_ordinal_predicate_code M)d ordinal ordinalShift
    (source_ordinal_predicate_bounded M)HOrd HOrdShift) as HOrdShiftInstance.
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)(succM M d)
    ordinalShift od HOrdShiftInstance HOD) as E. subst ordinalShift.
  pose proof(source_full_prv_shift_cons M b c n sb sc ub uc un level ordinal od(succM M k)
    HShiftCtx HCons HBranch HOrdShift POrd) as POD.
  destruct(numerical_renaming_total M known(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))
    as(knownShift&HKnownShift).
  pose proof(source_LL_instance_shift M d carrier known knownShift HKnown HKnownShift) as HKnownShiftGraph.
  pose proof(source_LL_instance_functional M(succM M d)(succM M carrier)knownShift ld
    HKnownShiftGraph HLD) as E. subst knownShift.
  pose proof(source_full_prv_shift_cons M b c n sb sc ub uc un level known ld(succM M k)
    HShiftCtx HCons HBranch HKnownShift PKnown) as PLD.
  destruct(numerical_renaming_total M member(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))
    as(memberShift&HMemberShift).
  pose proof(source_member_atom_shift M y carrier member memberShift HMember HMemberShift) as HMemberShiftGraph.
  pose proof(sf_relation_functional M SFMember(succM M y)(succM M carrier)memberShift oldMember
    HMemberShiftGraph HOld) as E. subst memberShift.
  pose proof(source_full_prv_shift_cons M b c n sb sc ub uc un level member oldMember(succM M k)
    HShiftCtx HCons HBranch HMemberShift PMember) as POld.
  destruct(numerical_renaming_total M instance(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))
    as(instanceShift&HInstanceShift).
  pose proof(source_instantiation_cutoff_shift M phi matrix y instance instanceShift(succM M k)
    HB HInstance HC HInstanceShift) as HInstanceShiftGraph.
  pose proof(source_full_prv_shift_cons M b c n sb sc ub uc un level instance instanceShift(succM M k)
    HShiftCtx HCons HBranch HInstanceShift PInstance) as PInstanceShift.
  assert(PUnique:source_full_prv M ub uc un unique).
  { exact(source_full_prv_weaken_bounded M sb sc n ub uc un unique(succM M k)
      (source_full_all_shift M b c n unique allUnique sb sc HAU PAU HShiftCtx)
      (source_cons_tail_inclusion M sb sc n level ub uc un HCons)HBranch). }
  assert(PMove:source_full_prv M ub uc un move).
  { exact(source_full_prv_weaken_bounded M sb sc n ub uc un move(succM M k)
      (source_full_all_shift M b c n move allMove sb sc HAM PAM HShiftCtx)
      (source_cons_tail_inclusion M sb sc n level ub uc un HCons)HBranch). }
  pose proof(source_full_modus_ponens M ub uc un od t1 unique HU PUnique POD) as PT1.
  pose proof(source_full_modus_ponens M ub uc un ld t2 t1 HT1 PT1 PLD) as PT2.
  pose proof(source_full_modus_ponens M ub uc un level equal t2 HT2 PT2 PLevel) as PEqual.
  pose proof(source_full_modus_ponens M ub uc un equal moveImp move HMove PMove PEqual) as PMoveImp.
  pose proof(source_full_modus_ponens M ub uc un oldMember newMember moveImp HMoveImp PMoveImp POld) as PNew.
  pose proof(source_full_ew_recipe_witness M ub uc un(succM M k)domain matrix ew(succM M y)
    instanceShift newMember HBranch(coding_zero_lt_succ M k)HD HMatrixBound
    (proj2(coding_lt_succ_cancel M y k)HYB)HEw HInstanceShiftGraph HNew PNew PInstanceShift) as PEw.
  apply(full_source_AllI M b c n point request sb sc(ex_intro _ k(conj HRequestBound HCtx)));
    [|exact HShiftCtx|exact HAll].
  apply(full_source_II M sb sc n level ew point ub uc un).
  - exists(succM M k). split.
    + exact(proj1(source_bounded_accept_unary M SFAll point request k(or_introl eq_refl)HAll)HRequestBound).
    + exact(context_shift_preserves_bound M b c n sb sc k HShiftCtx HCtx).
  - exact PEw.
  - exact HCons.
  - exact HPoint.
Qed.

Print Assumptions source_full_positive_witness_request.
