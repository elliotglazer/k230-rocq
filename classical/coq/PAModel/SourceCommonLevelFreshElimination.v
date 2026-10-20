(** Eliminate both actual common-level witnesses at fresh names without shifting the matrix parameters. *)
From PAModel Require Import Model Arithmetic BetaExtension FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceBoundMonotone SourceTraceBounds NumericalContexts NumericalEnvironments NumericalSourceFull
 SourceCommonLevelPoint SourceCommonLevelRecipe SourceCommonLevelWitness SourceFreshQuantifierProofs
 SourceProofWeakening SourceContextProofHelpers SourceQuantifierRules NumericalInstantiation.
Unset Implicit Arguments.
Theorem source_full_common_level_fresh_elim M gb gc gn start count d y point target goal pointimp k wide:
 context_bounded M gb gc gn k ->source_bounded M goal k ->
 (forall i,coding_lt M i count ->coding_lt M(addM M i start)k) ->
 coding_lt M k(succM M d) ->coding_lt M d wide ->coding_lt M wide(succM M y) ->
 source_common_level_point M start count d y point ->source_common_level_recipe M start count target ->
 sf_relation M SFImpl point goal pointimp ->source_full_prv M gb gc gn pointimp ->source_full_prv M gb gc gn target ->
 source_full_prv M gb gc gn goal.
Proof.
 intros HC BG HNames HD DW HY HPoint HTarget HImp PImp PTarget.
 destruct(source_common_level_witness_instances M start count d y point target HPoint HTarget)
  as(matrix&exY&matrixD&exYD&HExY&HExD&HExYD&HID&HIY).
 assert(KW:coding_lt M k(succM M wide)).
 { exact(coding_lt_trans M k wide(succM M wide)(coding_le_lt_trans M k d wide HD DW)(coding_lt_succ M wide)). }
 assert(HCW:context_bounded M gb gc gn wide).
 { exact(context_bounded_monotone M gb gc gn k wide HC KW). }
 assert(BGW:source_bounded M goal wide).
 { exact(SourceBoundMonotone.source_bounded_monotone M goal k wide BG KW). }
 assert(BTarget:source_bounded M target k).
 { exact(source_common_level_recipe_bounded M start count target k HNames HTarget). }
 assert(BExY:source_bounded M exY(succM M k)).
 { exact(proj1(source_bounded_accept_unary M SFEx exY target k(or_intror eq_refl)HExD)BTarget). }
 assert(BExYWide:source_bounded M exY(succM M wide)).
 { exact(SourceBoundMonotone.source_bounded_monotone M exY(succM M k)(succM M wide)BExY
    (proj2(coding_lt_succ_cancel M k(succM M wide))KW)). }
 assert(BExYD:source_bounded M exYD wide).
 { exact(numerical_instantiation_bounded M exY d exYD wide BExYWide DW HID). }
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
   - apply(source_full_fresh_exists_elim M b c n matrixD exYD y point goal pointimp wide HBranch BMatrixD BGW HY HExYD HIY HImp).
     + exact(source_full_cons_weaken M gb gc gn exYD b c n wide pointimp HCons HBranch PImp).
     + exact PExYD.
   - exact HCons.
   - exact HInner. }
 exact(source_full_fresh_exists_elim M gb gc gn exY target d exYD goal imp k HC BExY BG HD HExD HID HInner PInner PTarget).
Qed.
Print Assumptions source_full_common_level_fresh_elim.
