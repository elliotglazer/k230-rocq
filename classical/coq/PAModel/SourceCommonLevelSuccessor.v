(** Actual four-witness L_common successor, including elimination of the
    old common ordinal/level. Only fixed literal hierarchy proofs are inputs. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded SourceSequents NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming
  NumericalInstantiation NumericalSourceFull SourceQuantifierRules SourceProofWeakening SourceProofShiftCons
  SourceContextTransport SourceContextProofHelpers SourceClosedContextShift SourceLeastOrdinalWitness SourceImplicationAllShift
  SourceDomainInstances SourceHierarchyShifts SourceLFixed SourceCommonLevelPoint SourceCommonLevelRecipe
  SourceCommonLevelWitness SourceCommonLevelShift SourceCommonLevelAbove.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.

Theorem source_full_common_level_successor M b c n ab ac an k start count old ly target aboveLaw subsetLaw :
  context_bounded M b c n k ->context_bounded M ab ac an(zeroM M) ->context_included M ab ac an b c n ->
  (forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i start)k) ->
  source_common_level_recipe M start count old ->
  numerical_instantiation M(source_L_domain_code M)(addM M count start)ly ->
  source_common_level_recipe M start(succM M count)target ->
  source_common_above_laws M(succM M(succM M start))count(code_numeral M 1)(zeroM M)aboveLaw subsetLaw ->
  source_full_prv M ab ac an aboveLaw ->source_full_prv M ab ac an subsetLaw ->
  source_full_prv M b c n old ->source_full_prv M b c n ly ->source_full_prv M b c n target.
Proof.
  intros HC HAC HIncl HNames HOld HLY HTarget HLaws PAbove PSubset POld PLY.
  destruct(source_common_level_recipe_shell M start count old HOld) as(matrix&exY&HM&HY&HTop).
  assert(HNamesPrefix:forall i,coding_lt M i count ->coding_lt M(addM M i start)k).
  { intros i HI. exact(HNames i(coding_lt_trans M i count(succM M count)HI(coding_lt_succ M count))). }
  pose proof(source_common_level_recipe_bounded M start count old k HNamesPrefix HOld) as BOld.
  pose proof(proj1(source_bounded_accept_unary M SFEx exY old k(or_intror eq_refl)HTop)BOld) as BExY.
  pose proof(proj1(source_bounded_accept_unary M SFEx matrix exY(succM M k)(or_intror eq_refl)HY)BExY) as BMatrix.
  destruct(context_shift_total M b c n) as(sb&sc&HS).
  pose proof(context_shift_preserves_bound M b c n sb sc k HS HC) as HSC.
  destruct(environment_cons_total M sb sc n exY) as(cb&cc&cn&HConsD).
  pose proof(proj2(context_bounded_cons M sb sc n exY cb cc cn(succM M k)HConsD)(conj BExY HSC)) as HCC.
  destruct(context_shift_total M cb cc cn) as(tb&tc&HT).
  pose proof(context_shift_preserves_bound M cb cc cn tb tc(succM M k)HT HCC) as HTC.
  destruct(environment_cons_total M tb tc cn matrix) as(ub&uc&un&HConsY).
  pose proof(proj2(context_bounded_cons M tb tc cn matrix ub uc un(succM M(succM M k))HConsY)(conj BMatrix HTC)) as HUC.
  pose proof(source_closed_context_shift_self M ab ac an HAC) as HAxShift.
  pose proof(source_context_included_shift M ab ac an b c n ab ac sb sc HIncl HAxShift HS) as HInclS.
  assert(HInclC:context_included M ab ac an cb cc cn).
  { intros f HF. exact(source_cons_tail_inclusion M sb sc n exY cb cc cn HConsD f(HInclS f HF)). }
  pose proof(source_context_included_shift M ab ac an cb cc cn ab ac tb tc HInclC HAxShift HT) as HInclT.
  assert(HInclU:context_included M ab ac an ub uc un).
  { intros f HF. exact(source_cons_tail_inclusion M tb tc cn matrix ub uc un HConsY f(HInclT f HF)). }
  destruct(numerical_instantiation_total M(source_L_domain_code M)(succM M(addM M count start))) as(ly1&HLY1).
  destruct(numerical_instantiation_total M(source_L_domain_code M)(succM M(succM M(addM M count start)))) as(ly2&HLY2).
  pose proof(source_domain_shift_to M(source_L_domain_code M)(addM M count start)ly ly1
    (numerical_L_domain_bounded M)HLY HLY1) as HLYShift1.
  pose proof(source_domain_shift_to M(source_L_domain_code M)(succM M(addM M count start))ly1 ly2
    (numerical_L_domain_bounded M)HLY1 HLY2) as HLYShift2.
  pose proof(source_full_prv_shift_cons M b c n sb sc cb cc cn exY ly ly1(succM M k)
    HS HConsD HCC HLYShift1 PLY) as PLY1.
  pose proof(source_full_prv_shift_cons M cb cc cn tb tc ub uc un matrix ly1 ly2(succM M(succM M k))
    HT HConsY HUC HLYShift2 PLY1) as PLY2.
  pose proof(source_full_cons_head M tb tc cn matrix ub uc un(succM M(succM M k))HConsY BMatrix HUC) as PMatrix.
  destruct(source_common_level_recipe_total M(succM M start)(succM M count)) as(target1&HTarget1).
  destruct(source_common_level_recipe_total M(succM M(succM M start))(succM M count)) as(target2&HTarget2).
  pose proof(source_common_level_shift M start(succM M count)target target1 HTarget HTarget1) as HTargetShift1.
  pose proof(source_common_level_shift M(succM M start)(succM M count)target1 target2 HTarget1 HTarget2) as HTargetShift2.
  assert(HNames2:forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i(succM M(succM M start)))(succM M(succM M k))).
  { intros i HI. rewrite !source_common_add_successor. apply(proj2(coding_lt_succ_cancel M(succM M(addM M i start))(succM M k))).
    exact(proj2(coding_lt_succ_cancel M(addM M i start)k)(HNames i HI)). }
  assert(HLY2':numerical_instantiation M(source_L_domain_code M)(addM M count(succM M(succM M start)))ly2).
  { rewrite !source_common_add_successor. exact HLY2. }
  assert(HOne:coding_lt M(code_numeral M 1)(succM M(succM M k))).
  { change(coding_lt M(succM M(zeroM M))(succM M(succM M k))).
    apply(proj2(coding_lt_succ_cancel M(zeroM M)(succM M k))). apply coding_zero_lt_succ. }
  pose proof(source_full_common_level_above M ub uc un ab ac an(succM M(succM M k))
    (succM M(succM M start))count(code_numeral M 1)(zeroM M)matrix ly2 target2 aboveLaw subsetLaw
    HUC HAC HInclU HNames2 HOne(coding_zero_lt_succ M(succM M k))HM HLY2' HTarget2 HLaws
    PAbove PSubset PMatrix PLY2) as PTarget2.
  pose proof(source_common_level_recipe_bounded M start(succM M count)target k HNames HTarget) as BTarget.
  pose proof(source_shift_bound M target target1 k BTarget HTargetShift1) as BTarget1.
  pose proof(source_full_cons_head M sb sc n exY cb cc cn(succM M k)HConsD BExY HCC) as PExY.
  pose proof(full_source_ExE M cb cc cn matrix exY target1 target2 tb tc ub uc un
    (ex_intro _(succM M k)(conj BTarget1 HCC))PExY PTarget2 HY HT HConsY HTargetShift2) as PTarget1.
  exact(full_source_ExE M b c n exY old target target1 sb sc cb cc cn
    (ex_intro _ k(conj BTarget HC))POld PTarget1 HTop HS HConsD HTargetShift1).
Qed.
Print Assumptions source_full_common_level_successor.
