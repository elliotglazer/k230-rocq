(** Eliminate both actual shared-reflection geometry witnesses at fresh names without shifting the matrix parameters. *)
From PAModel Require Import Model Arithmetic BetaExtension FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceBoundMonotone SourceTraceBounds NumericalContexts NumericalEnvironments NumericalSourceFull
 SourceReflectionGeometryPoint SourceReflectionGeometryRecipe SourceReflectionGeometryWitness SourcePieceConjunctionBounds SourceFreshQuantifierProofs
 SourceProofWeakening SourceContextProofHelpers SourceQuantifierRules NumericalInstantiation.
Unset Implicit Arguments.
Theorem source_full_reflection_geometry_fresh_elim M domain level sb sc pieces a gb gc gn K beta point target goal pointimp k wide:
 source_bounded M domain(code_numeral M 1)->source_bounded M level(code_numeral M 2)->
 source_piece_table_valid M sb sc pieces->coding_lt M a k->
 context_bounded M gb gc gn k ->source_bounded M goal k ->
 coding_lt M k(succM M K) ->coding_lt M K wide ->coding_lt M wide(succM M beta) ->
 source_reflection_geometry_point M domain level sb sc pieces a K beta point ->
 source_reflection_geometry_recipe M domain level sb sc pieces a target ->
 sf_relation M SFImpl point goal pointimp ->source_full_prv M gb gc gn pointimp ->source_full_prv M gb gc gn target ->
 source_full_prv M gb gc gn goal.
Proof.
 intros HDomain HLevel HV BA HC BG HD DW HY HPoint HTarget HImp PImp PTarget.
 destruct(source_reflection_geometry_witness_instances M domain level sb sc pieces a K beta point target HDomain HLevel HV HPoint HTarget)
  as(matrix&exY&matrixD&exYD&HExY&HExD&HExYD&HID&HIY).
 assert(KW:coding_lt M k(succM M wide)).
 { exact(coding_lt_trans M k wide(succM M wide)(coding_le_lt_trans M k K wide HD DW)(coding_lt_succ M wide)). }
 assert(HCW:context_bounded M gb gc gn wide).
 { exact(context_bounded_monotone M gb gc gn k wide HC KW). }
 assert(BGW:source_bounded M goal wide).
 { exact(SourceBoundMonotone.source_bounded_monotone M goal k wide BG KW). }
 assert(BTarget:source_bounded M target k).
 { exact(source_reflection_geometry_recipe_bounded M domain level sb sc pieces a target k HDomain HLevel HV BA HTarget). }
 assert(BExY:source_bounded M exY(succM M k)).
 { exact(proj1(source_bounded_accept_unary M SFEx exY target k(or_intror eq_refl)HExD)BTarget). }
 assert(BExYWide:source_bounded M exY(succM M wide)).
 { exact(SourceBoundMonotone.source_bounded_monotone M exY(succM M k)(succM M wide)BExY
    (proj2(coding_lt_succ_cancel M k(succM M wide))KW)). }
 assert(BExYD:source_bounded M exYD wide).
 { exact(numerical_instantiation_bounded M exY K exYD wide BExYWide DW HID). }
 assert(BMatrixD:source_bounded M matrixD(succM M wide)).
 { exact(proj1(source_bounded_accept_unary M SFEx matrixD exYD wide(or_intror eq_refl)HExYD)BExYD). }
 destruct(sf_relation_total M SFImpl exYD goal)as(imp&HInner).
 destruct(environment_cons_total M gb gc gn exYD)as(b&c&n&HCons).
 assert(HBranch:context_bounded M b c n wide).
 { apply(proj2(context_bounded_cons M gb gc gn exYD b c n wide HCons)). now split. }
 assert(PExYD:source_full_prv M b c n exYD).
 { exact(source_full_cons_head M gb gc gn exYD b c n wide HCons BExYD HBranch). }
 assert(PInner:source_full_prv M gb gc gn imp).
 { apply(full_source_II M gb gc gn exYD goal imp b c n).
   - exists wide. split;[|exact HCW].
     exact(proj2(source_bounded_accept_binary M SFImpl exYD goal imp wide(or_intror(or_intror eq_refl))HInner)(conj BExYD BGW)).
   - apply(source_full_fresh_exists_elim M b c n matrixD exYD beta point goal pointimp wide HBranch BMatrixD BGW HY HExYD HIY HImp).
     + exact(source_full_cons_weaken M gb gc gn exYD b c n wide pointimp HCons HBranch PImp).
     + exact PExYD.
   - exact HCons.
   - exact HInner. }
 exact(source_full_fresh_exists_elim M gb gc gn exY target K exYD goal imp k HC BExY BG HD HExD HID HInner PInner PTarget).
Qed.
Print Assumptions source_full_reflection_geometry_fresh_elim.
