(** Actual chosen-output substitution of KF witnesses. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules
 SourceHierarchySyntax SourcePieceConjunction SourcePieceConjunctionBounds SourcePieceConjunctionSubstitution SourceReflectionKFWitness SourceRecursionShiftGraphs.
Unset Implicit Arguments.
Theorem source_piece_conjunction_substitution_exact M domain level sb sc count d X old e Y new rb rc rn base:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 source_piece_conjunction M domain level sb sc count d X old ->source_piece_conjunction M domain level sb sc count e Y new ->
 substitution_lookup M rb rc rn base d e ->substitution_lookup M rb rc rn base X Y ->numerical_substitution M old rb rc rn base new.
Proof.
 intros HD HL HV HO HN HDE HXY.
 destruct(numerical_substitution_total M old rb rc rn base)as(tmp&HT).
 pose proof(source_piece_conjunction_substitution M count domain level sb sc d X old rb rc rn base e Y tmp HD HL HV HO HT HDE HXY)as HG.
 rewrite(source_piece_conjunction_functional M domain level sb sc count e Y tmp new HG HN)in HT. exact HT.
Qed.
Theorem source_reflection_KF_witness_substitution M domain level sb sc count K x w old K' x' w' new rb rc rn base:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 source_reflection_KF_witness M domain level sb sc count K x w old ->source_reflection_KF_witness M domain level sb sc count K' x' w' new ->
 substitution_lookup M rb rc rn base K K' ->substitution_lookup M rb rc rn base x x' ->substitution_lookup M rb rc rn base w w' ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros HD HL HV(m&t&l&p&q&all&i&HM&HT&HLg&HP&HQ&HA&HI&HF)
 (m'&t'&l'&p'&q'&all'&i'&HM'&HT'&HLg'&HP'&HQ'&HA'&HI'&HF')HK HX HW.
 assert(SM:numerical_substitution M m rb rc rn base m').
 { apply(proj2(numerical_substitution_member M w K m rb rc rn base m' HM)). exists w',K'. auto. }
 assert(ST:numerical_substitution M t rb rc rn base t').
 { apply(proj2(numerical_substitution_member M x w t rb rc rn base t' HT)). exists x',w'. auto. }
 destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HMap).
 pose proof(source_LL_instance_substitution M(succM M x)(zeroM M)l(succM M x')(zeroM M)l' lb lc ln(succM M base)HLg HLg'(proj2(proj2 HMap)x x' HX)(proj1(proj2 HMap)))as SL.
 pose proof(source_piece_conjunction_substitution_exact M domain level sb sc count(succM M w)(zeroM M)p(succM M w')(zeroM M)p' lb lc ln(succM M base)
  HD HL HV HP HP'(proj2(proj2 HMap)w w' HW)(proj1(proj2 HMap)))as SP.
 assert(SQ:numerical_substitution M q lb lc ln(succM M base)q').
 { apply(proj2(numerical_substitution_binary M SFImpl l p q lb lc ln(succM M base)q'(or_intror(or_intror eq_refl))HQ)). exists l',p'. auto. }
 assert(SA:numerical_substitution M all rb rc rn base all').
 { apply(proj2(numerical_substitution_quantifier M true q all rb rc rn base all' HA)). exists lb,lc,ln,q'. auto. }
 assert(SI:numerical_substitution M i rb rc rn base i').
 { apply(proj2(numerical_substitution_binary M SFAnd t all i rb rc rn base i'(or_introl eq_refl)HI)). exists t',all'. auto. }
 apply(proj2(numerical_substitution_binary M SFAnd m i old rb rc rn base new(or_introl eq_refl)HF)). exists m',i'. auto.
Qed.
Theorem source_reflection_KF_witness_shift M domain level sb sc count K x w old new:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 source_reflection_KF_witness M domain level sb sc count K x w old ->
 source_reflection_KF_witness M domain level sb sc count(succM M K)(succM M x)(succM M w)new ->source_formula_shift M old new.
Proof.
 intros HD HL HV HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)). rewrite Arithmetic.add_zero.
 exact(source_reflection_KF_witness_substitution M domain level sb sc count K x w old(succM M K)(succM M x)(succM M w)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HD HL HV HO HN(source_rec_shift_lookup M K)(source_rec_shift_lookup M x)(source_rec_shift_lookup M w)).
Qed.
Print Assumptions source_piece_conjunction_substitution_exact.
Print Assumptions source_reflection_KF_witness_substitution.
Print Assumptions source_reflection_KF_witness_shift.
