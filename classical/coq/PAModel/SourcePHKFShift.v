(** Actual covariance of the completed K-closure profile. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules SourceRecursionShiftGraphs
 SourcePieceConjunctionBounds SourceReflectionKF SourceReflectionKFNext SourceReflectionKFWitness.
Unset Implicit Arguments.
Lemma source_PH_KF_shell M domain level sb sc count K whole:
 source_reflection_KF M domain level sb sc count K whole ->exists guard next point,
 sf_relation M SFMember(zeroM M)(succM M K)guard /\
 source_reflection_KF_next M domain level sb sc count(succM M K)(zeroM M)next /\
 sf_relation M SFImpl guard next point /\sf_relation M SFAll point(zeroM M)whole.
Proof.
 intros(g&lev&pc&point&all&mk&kw&inner&body&ex&tail&HG&HLev&HPC&HPoint&HAll&HMK&HKW&HInner&HBody&HEx&HTail&HWhole).
 exists g,ex,tail. split;[exact HG|]. split;[|auto].
 exists body. split;[|exact HEx]. exists mk,kw,lev,pc,point,all,inner. auto 15.
Qed.
Theorem source_PH_KF_substitution M domain level sb sc count K old K' new rb rc rn base:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 source_reflection_KF M domain level sb sc count K old ->source_reflection_KF M domain level sb sc count K' new ->
 substitution_lookup M rb rc rn base K K' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros HD HL HV HO HN HK.
 destruct(source_PH_KF_shell M domain level sb sc count K old HO)as(g&next&p&HG&HNext&HP&HA).
 destruct(source_PH_KF_shell M domain level sb sc count K' new HN)as(g'&next'&p'&HG'&HNext'&HP'&HA').
 destruct(substitution_lift_total M rb rc rn base)as(lb&lc&ln&HMap).
 assert(SG:numerical_substitution M g lb lc ln(succM M base)g').
 { apply(proj2(numerical_substitution_member M(zeroM M)(succM M K)g lb lc ln(succM M base)g' HG)).
   exists(zeroM M),(succM M K'). split;[exact(proj1(proj2 HMap))|]. split;[exact(proj2(proj2 HMap)K K' HK)|exact HG']. }
 pose proof(source_reflection_KF_next_substitution M domain level sb sc count(succM M K)(zeroM M)next(succM M K')(zeroM M)next' lb lc ln(succM M base)
  HD HL HV HNext HNext'(proj2(proj2 HMap)K K' HK)(proj1(proj2 HMap)))as SN.
 assert(SP:numerical_substitution M p lb lc ln(succM M base)p').
 { apply(proj2(numerical_substitution_binary M SFImpl g next p lb lc ln(succM M base)p'(or_intror(or_intror eq_refl))HP)). exists g',next'. auto. }
 apply(proj2(numerical_substitution_quantifier M true p old rb rc rn base new HA)). exists lb,lc,ln,p'. auto.
Qed.
Theorem source_PH_KF_shift M domain level sb sc count K old new:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 source_reflection_KF M domain level sb sc count K old ->source_reflection_KF M domain level sb sc count(succM M K)new ->source_formula_shift M old new.
Proof.
 intros HD HL HV HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)). rewrite Arithmetic.add_zero.
 exact(source_PH_KF_substitution M domain level sb sc count K old(succM M K)new(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HD HL HV HO HN(source_rec_shift_lookup M K)).
Qed.
Print Assumptions source_PH_KF_substitution.
Print Assumptions source_PH_KF_shift.
