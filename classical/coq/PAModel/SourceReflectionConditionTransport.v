(** Exact capture-avoiding transport of the two displayed Cond roles. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation NumericalRenamingMaps NumericalRenaming RenamingSubstitution
  SourceUnarySubstitution SourceHierarchySyntax SourcePieceConjunctionBounds SourcePieceConjunctionSubstitution
  SourceReflectionCondition SourceQuantifierRules NumericalContextRenaming.
Unset Implicit Arguments.

Theorem source_LL_substitution_image M d z f rb rc rn base d' z' out:
  source_LL_instance M d z f ->numerical_substitution M f rb rc rn base out ->
  substitution_lookup M rb rc rn base d d' ->substitution_lookup M rb rc rn base z z' ->
  source_LL_instance M d' z' out.
Proof.
  intros HF HS HD HZ. destruct(source_LL_instance_total M d' z') as(g&HG).
  pose proof(source_LL_instance_substitution M d z f d' z' g rb rc rn base HF HG HD HZ) as HT.
  pose proof(numerical_substitution_functional M f rb rc rn base out g HS HT) as E. now subst g.
Qed.

Theorem source_reflection_condition_substitution M domain level ordinal sb sc n x y f rb rc rn base u v out:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_bounded M ordinal(code_numeral M 1) ->source_piece_table_valid M sb sc n ->
  source_reflection_condition M domain level ordinal sb sc n x y f ->numerical_substitution M f rb rc rn base out ->
  substitution_lookup M rb rc rn base x u ->substitution_lookup M rb rc rn base y v ->
  source_reflection_condition M domain level ordinal sb sc n u v out.
Proof.
  intros HD HL HO HV(ord&member&lev&pc&point&all&both&HOrd&HM&HLev&HPC&HP&HA&HB&HF)HR HX HY.
  destruct(proj1(numerical_substitution_binary M SFImpl ord both f rb rc rn base out(or_intror(or_intror eq_refl))HF)HR)
    as(ord'&both'&HROrd&HRBoth&HF').
  destruct(proj1(numerical_substitution_binary M SFAnd member all both rb rc rn base both'(or_introl eq_refl)HB)HRBoth)
    as(member'&all'&HRMember&HRAll&HB').
  destruct(proj1(numerical_substitution_member M x y member rb rc rn base member' HM)HRMember)
    as(a&b&HXA&HYB&HM').
  pose proof(substitution_lookup_functional M rb rc rn base x a u HXA HX) as E. subst a.
  pose proof(substitution_lookup_functional M rb rc rn base y b v HYB HY) as E. subst b.
  pose proof(source_domain_instance_substitution M ordinal x ord rb rc rn base ord' u HO HOrd HROrd HX) as HOrd'.
  destruct(proj1(numerical_substitution_quantifier M true point all rb rc rn base all' HA)HRAll)
    as(ab&ac&an&point'&HMap&HRPoint&HA').
  destruct(proj1(numerical_substitution_binary M SFImpl lev pc point ab ac an(succM M base)point'
    (or_intror(or_intror eq_refl))HP)HRPoint) as(lev'&pc'&HRLev&HRPC&HP').
  pose proof(source_LL_substitution_image M(succM M x)(zeroM M)lev ab ac an(succM M base)
    (succM M u)(zeroM M)lev' HLev HRLev(proj2(proj2 HMap)x u HX)(proj1(proj2 HMap))) as HLev'.
  pose proof(source_piece_conjunction_substitution M n domain level sb sc(succM M y)(zeroM M)pc
    ab ac an(succM M base)(succM M v)(zeroM M)pc' HD HL HV HPC HRPC
    (proj2(proj2 HMap)y v HY)(proj1(proj2 HMap))) as HPC'.
  exists ord',member',lev',pc',point',all',both'. auto 10.
Qed.

Theorem source_reflection_condition_renaming M domain level ordinal sb sc n x y f rb rc rn delta u v out:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_bounded M ordinal(code_numeral M 1) ->source_piece_table_valid M sb sc n ->
  source_reflection_condition M domain level ordinal sb sc n x y f ->numerical_renaming M f rb rc rn delta out ->
  renaming_lookup M rb rc rn delta x u ->renaming_lookup M rb rc rn delta y v ->
  source_reflection_condition M domain level ordinal sb sc n u v out.
Proof.
  intros HD HL HO HV HF HR HX HY.
  exact(source_reflection_condition_substitution M domain level ordinal sb sc n x y f rb rc rn(addM M rn delta)u v out HD HL HO HV HF
    (proj1(numerical_renaming_substitution_uniform M f rb rc rn delta out)HR)
    (proj1(renaming_substitution_lookup M rb rc rn delta x u)HX)(proj1(renaming_substitution_lookup M rb rc rn delta y v)HY)).
Qed.

Theorem source_reflection_condition_shift M domain level ordinal sb sc n x y f out:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_bounded M ordinal(code_numeral M 1) ->source_piece_table_valid M sb sc n ->
  source_reflection_condition M domain level ordinal sb sc n x y f ->source_formula_shift M f out ->
  source_reflection_condition M domain level ordinal sb sc n(succM M x)(succM M y)out.
Proof.
  intros HD HL HO HV HF HR.
  apply(source_reflection_condition_renaming M domain level ordinal sb sc n x y f(zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1)(succM M x)(succM M y)out HD HL HO HV HF HR);apply context_shift_lookup;reflexivity.
Qed.

Print Assumptions source_LL_substitution_image.
Print Assumptions source_reflection_condition_substitution.
Print Assumptions source_reflection_condition_renaming.
Print Assumptions source_reflection_condition_shift.
