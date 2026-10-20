(** Actual L-above successor step after an old common-level witness is open.
    The varying membership matrix is arbitrary internally finite syntax. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes
  SourceBounded SourceBoundMonotone SourceSequents NumericalContexts NumericalEnvironments NumericalContextRenaming
  NumericalRenaming NumericalInstantiation NumericalSourceFull SourceQuantifierRules SourceProofWeakening SourceProofShiftCons
  SourceContextTransport SourceContextProofHelpers SourceClosedContextShift SourceTraceBounds SourceRelativizationBounds
  SourceLeastOrdinalWitness SourceImplicationAllShift SourceDerivedRules SourceConjunctionRules SourceHierarchySyntax SourceHierarchyWitnessShell SourceHierarchySubsetShell
  SourceHierarchySubsetUse SourceOrdinalPredicate SourceLFixed SourceRawSubset
  SourceCommonLevelPoint SourceCommonLevelRecipe SourceCommonLevelWitness SourceCommonLevelShift SourceCommonLevelExtendPoint.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code source_L_domain_code.

Lemma source_common_subset_functional M x y f g :
  source_raw_subset_graph M x y f ->source_raw_subset_graph M x y g ->f=g.
Proof.
  intros(a&b&p&HA&HB&HP&HF)(a'&b'&p'&HA'&HB'&HP'&HG).
  pose proof(sf_relation_functional M SFMember(zeroM M)(succM M x)a a' HA HA') as E. subst a'.
  pose proof(sf_relation_functional M SFMember(zeroM M)(succM M y)b b' HB HB') as E. subst b'.
  pose proof(sf_relation_functional M SFImpl a b p p' HP HP') as E. subst p'.
  exact(sf_relation_functional M SFAll p(zeroM M)f g HF HG).
Qed.

Definition source_common_above_laws M start count d y aboveLaw subsetLaw :=
  (exists ly og exD bodyD bodyY od subset pair level inner member tail,
    source_hierarchy_above_shell M(addM M count start)d ly og exD bodyD bodyY od subset pair level inner member tail aboveLaw /\
    source_raw_subset_graph M(succM M(succM M d))(code_numeral M 1)subset) /\
  (exists od oe subset ld le result,
    source_hierarchy_subset_shell M(succM M(succM M d))(code_numeral M 1)
      (succM M(succM M y))(zeroM M)od oe subset ld le result subsetLaw).

Theorem source_full_common_level_above M b c n ab ac an k start count d y old ly target aboveLaw subsetLaw :
  context_bounded M b c n k ->context_bounded M ab ac an(zeroM M) ->context_included M ab ac an b c n ->
  (forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i start)k) ->coding_lt M d k ->coding_lt M y k ->
  source_common_level_point M start count d y old ->
  numerical_instantiation M(source_L_domain_code M)(addM M count start)ly ->
  source_common_level_recipe M start(succM M count)target ->source_common_above_laws M start count d y aboveLaw subsetLaw ->
  source_full_prv M ab ac an aboveLaw ->source_full_prv M ab ac an subsetLaw ->
  source_full_prv M b c n old ->source_full_prv M b c n ly ->source_full_prv M b c n target.
Proof.
  intros HC HAC HIncl HNames HD HY HOld HLY HTarget
    [(ly0&og&exD&bodyD&bodyY&od&subset&pair&level&inner&member&tail&HAbove&HSubOrd)
     (od2&oe2&subset2&ld2&le2&result2&HSubShell)] PAboveLaw PSubsetLaw POld PLY.
  pose proof HAbove as(HLY0&HOG&HOD&HLevel&HMember&HPair&HInner&HBodyY&HBodyD&HExD&HTail&HAboveLaw).
  pose proof(numerical_instantiation_functional M _ (addM M count start)ly ly0 HLY HLY0) as E. subst ly0.
  pose proof HOld as(members&oldOrd&oldLevel&oldPair&HMembers&HOldOrd&HOldLevel&HOldPair&HOldBody).
  pose proof(numerical_instantiation_functional M _ d oldOrd og HOldOrd HOG) as E. subst og.
  pose proof(source_full_conjunction_left M b c n oldPair members old HOldBody POld) as POldPair.
  pose proof(source_full_conjunction_left M b c n oldOrd oldLevel oldPair HOldPair POldPair) as POldOrd.
  pose proof(source_full_prv_weaken_bounded M ab ac an b c n aboveLaw k PAboveLaw HIncl HC) as PAbove.
  pose proof(source_full_modus_ponens M b c n ly tail aboveLaw HAboveLaw PAbove PLY) as PTail.
  pose proof(source_full_modus_ponens M b c n oldOrd exD tail HTail PTail POldOrd) as PExD.
  destruct(source_full_prv_wellformed M b c n exD PExD) as(q&HExBound&HQCtx).
  set(t:=addM M k q).
  assert(HKT:coding_lt M k(succM M t)) by(unfold t;apply coding_le_add).
  assert(HQT:coding_lt M q(succM M t)).
  { unfold t. rewrite Arithmetic.add_comm. apply coding_le_add. }
  pose proof(context_bounded_monotone M b c n k t HC HKT) as HCT.
  pose proof(source_bounded_monotone M exD q t HExBound HQT) as HExT.
  pose proof(proj1(source_bounded_accept_unary M SFEx bodyD exD t(or_intror eq_refl)HExD)HExT) as HDBound.
  pose proof(proj1(source_bounded_accept_unary M SFEx bodyY bodyD(succM M t)(or_intror eq_refl)HBodyD)HDBound) as HYBound.
  destruct(context_shift_total M b c n) as(sb&sc&HS).
  pose proof(context_shift_preserves_bound M b c n sb sc t HS HCT) as HSC.
  destruct(environment_cons_total M sb sc n bodyD) as(cb&cc&cn&HConsD).
  pose proof(proj2(context_bounded_cons M sb sc n bodyD cb cc cn(succM M t)HConsD)(conj HDBound HSC)) as HCC.
  destruct(context_shift_total M cb cc cn) as(tb&tc&HT).
  pose proof(context_shift_preserves_bound M cb cc cn tb tc(succM M t)HT HCC) as HTC.
  destruct(environment_cons_total M tb tc cn bodyY) as(ub&uc&un&HConsY).
  pose proof(proj2(context_bounded_cons M tb tc cn bodyY ub uc un(succM M(succM M t))HConsY)(conj HYBound HTC)) as HUC.
  pose proof(source_closed_context_shift_self M ab ac an HAC) as HAxShift.
  pose proof(source_context_included_shift M ab ac an b c n ab ac sb sc HIncl HAxShift HS) as HInclS.
  assert(HInclC:context_included M ab ac an cb cc cn).
  { intros f HF. exact(source_cons_tail_inclusion M sb sc n bodyD cb cc cn HConsD f(HInclS f HF)). }
  pose proof(source_context_included_shift M ab ac an cb cc cn ab ac tb tc HInclC HAxShift HT) as HInclT.
  assert(HInclU:context_included M ab ac an ub uc un).
  { intros f HF. exact(source_cons_tail_inclusion M tb tc cn bodyY ub uc un HConsY f(HInclT f HF)). }
  destruct(source_common_level_point_total M(succM M start)count(succM M d)(succM M y)) as(old1&HOld1).
  destruct(source_common_level_point_total M(succM M(succM M start))count(succM M(succM M d))(succM M(succM M y))) as(old2&HOld2).
  pose proof(source_common_level_point_shift M start count d y old old1 HOld HOld1) as HOldShift1.
  pose proof(source_common_level_point_shift M(succM M start)count(succM M d)(succM M y)old1 old2 HOld1 HOld2) as HOldShift2.
  pose proof(source_full_prv_shift_cons M b c n sb sc cb cc cn bodyD old old1(succM M t)
    HS HConsD HCC HOldShift1 POld) as POld1.
  pose proof(source_full_prv_shift_cons M cb cc cn tb tc ub uc un bodyY old1 old2(succM M(succM M t))
    HT HConsY HUC HOldShift2 POld1) as POld2.
  pose proof(source_full_cons_head M tb tc cn bodyY ub uc un(succM M(succM M t))HConsY HYBound HUC) as PBodyY.
  pose proof(source_full_conjunction_left M ub uc un inner member bodyY HBodyY PBodyY) as PInner.
  pose proof(source_full_conjunction_right M ub uc un inner member bodyY HBodyY PBodyY) as PMember.
  pose proof(source_full_conjunction_left M ub uc un pair level inner HInner PInner) as PPair.
  pose proof(source_full_conjunction_right M ub uc un pair level inner HInner PInner) as PLevel.
  pose proof(source_full_conjunction_left M ub uc un od subset pair HPair PPair) as POrd.
  pose proof(source_full_conjunction_right M ub uc un od subset pair HPair PPair) as PSubOrd.
  pose proof HOld2 as(members2&oldOrd2&oldLevel2&oldPair2&HMembers2&HOldOrd2&HOldLevel2&HOldPair2&HOldBody2).
  pose proof(source_full_conjunction_left M ub uc un oldPair2 members2 old2 HOldBody2 POld2) as POldPair2.
  pose proof(source_full_conjunction_left M ub uc un oldOrd2 oldLevel2 oldPair2 HOldPair2 POldPair2) as POldOrd2.
  pose proof(source_full_conjunction_right M ub uc un oldOrd2 oldLevel2 oldPair2 HOldPair2 POldPair2) as POldLevel2.
  pose proof HSubShell as(HOD2&HOE2&HSubset2&HLD2&HLE2&HResult2&HSubLawGraph).
  pose proof(numerical_instantiation_functional M _(succM M(succM M d))oldOrd2 od2 HOldOrd2 HOD2) as E. subst od2.
  pose proof(numerical_instantiation_functional M _(code_numeral M 1)od oe2 HOD HOE2) as E. subst oe2.
  pose proof(source_common_subset_functional M(succM M(succM M d))(code_numeral M 1)subset subset2 HSubOrd HSubset2) as E. subst subset2.
  pose proof(source_LL_instance_functional M(succM M(succM M d))(succM M(succM M y))oldLevel2 ld2 HOldLevel2 HLD2) as E. subst ld2.
  pose proof(source_LL_instance_functional M(code_numeral M 1)(zeroM M)level le2 HLevel HLE2) as E. subst le2.
  pose proof(source_full_prv_weaken_bounded M ab ac an ub uc un subsetLaw(succM M(succM M t))PSubsetLaw HInclU HUC) as PSubsetLawU.
  pose proof(source_full_hierarchy_subset_use M ub uc un(succM M(succM M d))(code_numeral M 1)
    (succM M(succM M y))(zeroM M)oldOrd2 od subset oldLevel2 level result2 subsetLaw
    HSubShell PSubsetLawU POldOrd2 POrd PSubOrd POldLevel2 PLevel) as PSubsetY.
  destruct(source_common_level_recipe_total M(succM M start)(succM M count)) as(target1&HTarget1).
  destruct(source_common_level_recipe_total M(succM M(succM M start))(succM M count)) as(target2&HTarget2).
  pose proof(source_common_level_shift M start(succM M count)target target1 HTarget HTarget1) as HTargetShift1.
  pose proof(source_common_level_shift M(succM M start)(succM M count)target1 target2 HTarget1 HTarget2) as HTargetShift2.
  assert(HNamesT:forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i start)t).
  { intros i HI. exact(source_bound_lt_le M(addM M i start)k t(HNames i HI)HKT). }
  assert(HNamesT2:forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i(succM M(succM M start)))(succM M(succM M t))).
  { intros i HI. rewrite !source_common_add_successor. apply(proj2(coding_lt_succ_cancel M(succM M(addM M i start))(succM M t))).
    exact(proj2(coding_lt_succ_cancel M(addM M i start)t)(HNamesT i HI)). }
  assert(HY2:coding_lt M(succM M(succM M y))(succM M(succM M t))).
  { apply(proj2(coding_lt_succ_cancel M(succM M y)(succM M t))). apply(proj2(coding_lt_succ_cancel M y t)).
    exact(source_bound_lt_le M y k t HY HKT). }
  assert(HMemberTarget:sf_relation M SFMember(addM M count(succM M(succM M start)))(zeroM M)member).
  { rewrite !source_common_add_successor. exact HMember. }
  pose proof(source_full_common_level_extend_witness M ub uc un(succM M(succM M start))count
    (succM M(succM M d))(succM M(succM M y))old2(code_numeral M 1)(zeroM M)target2 od level result2 member
    (succM M(succM M t))HNamesT2 HY2(coding_zero_lt_succ M(succM M t))HUC HOld2 HTarget2 HOD HLevel HResult2 HMemberTarget
    POld2 POrd PLevel PSubsetY PMember) as PTarget2.
  pose proof(source_common_level_recipe_bounded M start(succM M count)target t HNamesT HTarget) as BTarget.
  pose proof(source_shift_bound M target target1 t BTarget HTargetShift1) as BTarget1.
  pose proof(source_full_cons_head M sb sc n bodyD cb cc cn(succM M t)HConsD HDBound HCC) as PBodyD.
  pose proof(full_source_ExE M cb cc cn bodyY bodyD target1 target2 tb tc ub uc un
    (ex_intro _ (succM M t)(conj BTarget1 HCC))PBodyD PTarget2 HBodyD HT HConsY HTargetShift2) as PTarget1.
  exact(full_source_ExE M b c n bodyD exD target target1 sb sc cb cc cn
    (ex_intro _ t(conj BTarget HCT))PExD PTarget1 HExD HS HConsD HTargetShift1).
Qed.
Print Assumptions source_full_common_level_above.
