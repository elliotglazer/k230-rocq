(** Eliminate actual common-level or shared-geometry witness pairs while
 collecting an explicitly generated closed ZFR background outside both ExE
 rules. Auxiliary names never occur in an ambient domain table. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalEnvironments NumericalSourceFull ContextCombination SourceZFRProvability SourceProofWeakening
 SourceClosedZFRImplication SourceCommonLevelPoint SourceCommonLevelRecipe SourceCommonLevelFreshElimination
 SourceReflectionGeometryPoint SourceReflectionGeometryRecipe SourceReflectionGeometryFreshElimination SourcePieceConjunctionBounds.
Unset Implicit Arguments.
Theorem source_full_closed_zfr_common_level_fresh M gb gc gn start count d y point target goal k wide
 bb bc bn ab ac an ub uc un:
 context_bounded M gb gc gn k->source_bounded M goal k->
 (forall i,coding_lt M i count->coding_lt M(addM M i start)k)->
 coding_lt M k(succM M d)->coding_lt M d wide->coding_lt M wide(succM M y)->
 source_common_level_point M start count d y point->source_common_level_recipe M start count target->
 environment_cons M gb gc gn point bb bc bn->source_zfr_context M ab ac an->context_union M bb bc bn ab ac an ub uc un->
 source_full_prv M ub uc un goal->source_full_prv M gb gc gn target->
 exists vb vc vn,context_union M gb gc gn ab ac an vb vc vn /\source_full_prv M vb vc vn goal.
Proof.
 intros BC BG HNames HD DW HY HPoint HTarget HCons HZ HU PGoal PTarget.
 destruct(sf_relation_total M SFImpl point goal)as(imp&HImp).
 destruct(source_full_closed_zfr_implication M gb gc gn point goal bb bc bn ab ac an ub uc un imp k
  BC HCons HZ HU PGoal HImp)as(vb&vc&vn&HV&BV&PImp).
 pose proof(source_full_prv_weaken_bounded M gb gc gn vb vc vn target k PTarget
  (context_union_left M gb gc gn ab ac an vb vc vn HV)BV)as PTargetV.
 exists vb,vc,vn. split;[exact HV|].
 exact(source_full_common_level_fresh_elim M vb vc vn start count d y point target goal imp k wide
  BV BG HNames HD DW HY HPoint HTarget HImp PImp PTargetV).
Qed.
Theorem source_full_closed_zfr_geometry_fresh M domain level sb sc pieces a gb gc gn K beta point target goal k wide
 bb bc bn ab ac an ub uc un:
 source_bounded M domain(code_numeral M 1)->source_bounded M level(code_numeral M 2)->
 source_piece_table_valid M sb sc pieces->coding_lt M a k->context_bounded M gb gc gn k->source_bounded M goal k->
 coding_lt M k(succM M K)->coding_lt M K wide->coding_lt M wide(succM M beta)->
 source_reflection_geometry_point M domain level sb sc pieces a K beta point->source_reflection_geometry_recipe M domain level sb sc pieces a target->
 environment_cons M gb gc gn point bb bc bn->source_zfr_context M ab ac an->context_union M bb bc bn ab ac an ub uc un->
 source_full_prv M ub uc un goal->source_full_prv M gb gc gn target->
 exists vb vc vn,context_union M gb gc gn ab ac an vb vc vn /\source_full_prv M vb vc vn goal.
Proof.
 intros HDomain HLevel HV BA BC BG HK KW HB HPoint HTarget HCons HZ HU PGoal PTarget.
 destruct(sf_relation_total M SFImpl point goal)as(imp&HImp).
 destruct(source_full_closed_zfr_implication M gb gc gn point goal bb bc bn ab ac an ub uc un imp k
  BC HCons HZ HU PGoal HImp)as(vb&vc&vn&HUnion&BV&PImp).
 pose proof(source_full_prv_weaken_bounded M gb gc gn vb vc vn target k PTarget
  (context_union_left M gb gc gn ab ac an vb vc vn HUnion)BV)as PTargetV.
 exists vb,vc,vn. split;[exact HUnion|].
 exact(source_full_reflection_geometry_fresh_elim M domain level sb sc pieces a vb vc vn K beta point target goal imp k wide
  HDomain HLevel HV BA BV BG HK KW HB HPoint HTarget HImp PImp PTargetV).
Qed.
Print Assumptions source_full_closed_zfr_common_level_fresh.
Print Assumptions source_full_closed_zfr_geometry_fresh.
