(** Actual ordinary reflection gives the universal carrier equivalence needed by Separation. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded NumericalContexts
 NumericalEnvironments NumericalContextRenaming NumericalSourceFull SourceContextProofHelpers
 SourceLFixed SourceOrdinaryReflectionSyntax SourceHierarchySyntax SourceMembershipBlocks SourceIffGraphs
 SourceRelativization SourceSetRelativization SourceD0Recipe SourceLSeparationReflectionPoint.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Local Opaque source_L_domain.
Theorem source_full_L_separation_reflection_all M phi matrix params d refl level block lp sp equiv member point allr
 gb gc gn ub uc width:
 source_bounded M phi(succM M params) ->context_bounded M gb gc gn width ->
 context_shift M gb gc gn ub uc ->context_bounded M ub uc gn(succM M width) ->
 coding_lt M d(succM M width) ->coding_lt M(code_numeral M 2)(succM M width) ->
 (forall i,coding_lt M i params ->coding_lt M(succM M(succM M(succM M(succM M i))))(succM M width)) ->
 source_bounded M equiv(succM M width) ->
 source_cutoff_shift_thrice M phi matrix ->
 source_ordinary_reflection M(source_L_domain_code M)(succM M params)phi d refl ->
 source_LL_instance M d(code_numeral M 2)level ->
 source_membership_block M(code_numeral M 4)(code_numeral M 2)params block ->
 source_relativization M(source_L_domain_code M)matrix lp ->source_set_relativization M(code_numeral M 2)matrix sp ->
 source_iff_graph M lp sp equiv ->sf_relation M SFMember(zeroM M)(code_numeral M 2)member ->
 sf_relation M SFImpl member equiv point ->sf_relation M SFAll point(zeroM M)allr ->
 source_full_prv M ub uc gn refl ->source_full_prv M ub uc gn level ->source_full_prv M ub uc gn block ->
 source_full_prv M gb gc gn allr.
Proof.
 intros HP HC HShift HSC BD B2 HNames BE HMat HR HL HB HLP HSP HE HM HPoint HAll PR PL PB.
 assert(B0:coding_lt M(zeroM M)(succM M width)).
 { exact(coding_lt_trans M(zeroM M)(code_numeral M 2)(succM M width)(coding_zero_lt_succ M(code_numeral M 1))B2). }
 assert(BM:source_bounded M member(succM M width)).
 { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 2)member(succM M width)(or_introl eq_refl)HM)). now split. }
 assert(BP:source_bounded M point(succM M width)).
 { apply(proj2(source_bounded_accept_binary M SFImpl member equiv point(succM M width)(or_intror(or_intror eq_refl))HPoint)). now split. }
 destruct(environment_cons_total M ub uc gn member)as(xb&xc&xn&HCons).
 assert(HBC:context_bounded M xb xc xn(succM M width)).
 { apply(proj2(context_bounded_cons M ub uc gn member xb xc xn(succM M width)HCons)). now split. }
 assert(PM:source_full_prv M xb xc xn member).
 { exact(source_full_cons_head M ub uc gn member xb xc xn(succM M width)HCons BM HBC). }
 assert(PE:source_full_prv M xb xc xn equiv).
 { apply(source_full_L_separation_reflection_point M phi matrix params d refl level block lp sp equiv member xb xc xn(succM M width)
    HP HBC BD B2 HNames HMat HR HL HB HLP HSP HE HM).
   - exact(source_full_cons_weaken M ub uc gn member xb xc xn(succM M width)refl HCons HBC PR).
   - exact(source_full_cons_weaken M ub uc gn member xb xc xn(succM M width)level HCons HBC PL).
   - exact(source_full_cons_weaken M ub uc gn member xb xc xn(succM M width)block HCons HBC PB).
   - exact PM. }
 assert(PPoint:source_full_prv M ub uc gn point).
 { apply(full_source_II M ub uc gn member equiv point xb xc xn);[exists(succM M width);now split|exact PE|exact HCons|exact HPoint]. }
 apply(full_source_AllI M gb gc gn point allr ub uc).
 - exists width. split;[|exact HC].
   apply(proj2(source_bounded_accept_unary M SFAll point allr width(or_introl eq_refl)HAll)). exact BP.
 - exact PPoint.
 - exact HShift.
 - exact HAll.
Qed.
Print Assumptions source_full_L_separation_reflection_all.
