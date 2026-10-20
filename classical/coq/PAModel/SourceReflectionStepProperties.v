(** Actual least-Cond step consequences, with every ordinary proof explicit. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes NumericalInstantiation NumericalContexts NumericalSourceFull
 SourceOrdinalPredicate SourceReflectionCondition SourceReflectionStep SourceConjunctionRules SourceDerivedRules.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Theorem source_full_reflection_step_properties M b c n domain level sb sc count x y step inputOrd:
 source_reflection_step M domain level sb sc count x y step ->
 numerical_instantiation M(source_ordinal_predicate_code M)x inputOrd ->
 source_full_prv M b c n step ->source_full_prv M b c n inputOrd ->
 exists ordinal member lev pc point all,
 numerical_instantiation M(source_ordinal_predicate_code M)y ordinal /\sf_relation M SFMember x y member /\
 SourceHierarchySyntax.source_LL_instance M(succM M x)(zeroM M)lev /\
 SourcePieceConjunction.source_piece_conjunction M domain level sb sc count(succM M y)(zeroM M)pc /\
 sf_relation M SFImpl lev pc point /\sf_relation M SFAll point(zeroM M)all /\
 source_full_prv M b c n ordinal /\source_full_prv M b c n member /\source_full_prv M b c n all.
Proof.
 intros(ordinal&condition&candidate&m&neg&q&tail&both&HOrdinal&HCondition&HCandidate&HM&HN&HQ&HT&HB&HStep)HInput PStep PInput.
 pose proof(source_full_conjunction_left M b c n both tail step HStep PStep)as PBoth.
 pose proof(source_full_conjunction_left M b c n ordinal condition both HB PBoth)as POrdinal.
 pose proof(source_full_conjunction_right M b c n ordinal condition both HB PBoth)as PCondition.
 destruct HCondition as(ord&member&lev&pc&point&all&both'&HO&HM'&HL&HPC&HP&HA&HB'&HCond).
 pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)x ord inputOrd HO HInput)as E. subst ord.
 pose proof(source_full_modus_ponens M b c n inputOrd both' condition HCond PCondition PInput)as PBoth'.
 exists ordinal,member,lev,pc,point,all. repeat split;try assumption.
 - exact(source_full_conjunction_left M b c n member all both' HB' PBoth').
 - exact(source_full_conjunction_right M b c n member all both' HB' PBoth').
Qed.
Print Assumptions source_full_reflection_step_properties.
