(** Exact fresh-beta opening and actual projections of the shared reflected level. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation NumericalContexts NumericalSourceFull
 SourceCommonLevelPoint SourceCommonLevelWitness SourceCommonReflectedLevel SourceOrdinaryReflectionSyntax
 SourceOrdinalPredicate SourceHierarchySyntax SourceMembershipBlocks SourceConjunctionRules.
Unset Implicit Arguments.
Theorem source_common_reflected_beta_opening M start paramCount reflectCount phi beta whole point opened:
 source_bounded M phi reflectCount ->source_common_reflected_level_recipe M start paramCount reflectCount phi whole ->
 source_common_reflected_level_point M(succM M start)paramCount reflectCount phi(succM M beta)(zeroM M)point ->
 sf_relation M SFEx point(zeroM M)opened ->
 exists body,sf_relation M SFEx body(zeroM M)whole /\numerical_instantiation M body beta opened.
Proof.
 intros HP(rawpoint&body&HRaw&HBody&HWhole)HPoint HOpened.
 destruct(substitution_singleton_total M beta)as(b&c&HHead&HTail).
 destruct(substitution_lift_total M b c(code_numeral M 1)(zeroM M))as(u&v&n&HLift).
 exists body. split;[exact HWhole|]. exists b,c. split;[exact HHead|].
 apply(proj2(numerical_substitution_quantifier M false rawpoint body b c(code_numeral M 1)(zeroM M)opened HBody)).
 exists u,v,n,point. split;[exact HLift|]. split;[|exact HOpened].
 apply(source_common_reflected_level_point_substitution M(succM M(succM M start))paramCount reflectCount phi
  (code_numeral M 1)(zeroM M)rawpoint(succM M start)(succM M beta)(zeroM M)point u v n(code_numeral M 1)HP HRaw HPoint).
 - exact(proj2(substitution_lift_tail M b c(code_numeral M 1)(zeroM M)u v n(zeroM M)beta HLift)HHead).
 - apply(proj2(substitution_lift_head M b c(code_numeral M 1)(zeroM M)u v n(zeroM M)HLift)). reflexivity.
 - intros i HI. rewrite !source_common_add_successor.
   exact(proj2(substitution_lift_tail M b c(code_numeral M 1)(zeroM M)u v n
    (succM M(addM M i start))(addM M i start)HLift)(HTail(addM M i start))).
Qed.
Theorem source_full_common_reflected_components M start paramCount reflectCount phi beta Y point gb gc gn:
 source_common_reflected_level_point M start paramCount reflectCount phi beta Y point ->source_full_prv M gb gc gn point ->
 exists ordinal level block refl,
 numerical_instantiation M(source_ordinal_predicate_code M)beta ordinal /\source_LL_instance M beta Y level /\
 source_membership_block M start Y paramCount block /\source_ordinary_reflection M(SourceLFixed.source_L_domain_code M)reflectCount phi beta refl /\
 source_full_prv M gb gc gn ordinal /\source_full_prv M gb gc gn level /\source_full_prv M gb gc gn block /\source_full_prv M gb gc gn refl.
Proof.
 intros(common&refl&(block&ordinal&level&pair&HB&HO&HL&HOP&HC)&HR&HPoint)P.
 pose proof(source_full_conjunction_left M gb gc gn common refl point HPoint P)as PC.
 pose proof(source_full_conjunction_right M gb gc gn common refl point HPoint P)as PR.
 pose proof(source_full_conjunction_left M gb gc gn pair block common HC PC)as PP.
 pose proof(source_full_conjunction_right M gb gc gn pair block common HC PC)as PB.
 exists ordinal,level,block,refl. do 4(split;[assumption|]).
 split;[exact(source_full_conjunction_left M gb gc gn ordinal level pair HOP PP)|].
 split;[exact(source_full_conjunction_right M gb gc gn ordinal level pair HOP PP)|]. now split.
Qed.
Print Assumptions source_common_reflected_beta_opening.
Print Assumptions source_full_common_reflected_components.
