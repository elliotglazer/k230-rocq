(** The literal old Separation reflection graph is proved from actual ordinary Refl. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors SourceBounded NumericalContexts
 NumericalContextRenaming NumericalSourceFull SourceLFixed SourceD0Recipe SourceLSeparationCarrierShell
 SourceLDefinableProfile SourceOrdinaryReflectionSyntax SourceHierarchySyntax SourceMembershipBlocks
 SourceRelativization SourceRelativizationBounds SourceSetRelativization SourceSetRelativizationBounds
 SourceIffGraphs SourceFunctionalityShells SourceLSeparationReflectionAll.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem source_full_L_separation_carrier_reflection M phi matrix params d refl level block lp sp allr
 gb gc gn ub uc width:
 source_bounded M phi(succM M params) ->source_bounded M matrix(succM M width) ->
 context_bounded M gb gc gn width ->context_shift M gb gc gn ub uc ->context_bounded M ub uc gn(succM M width) ->
 coding_lt M d(succM M width) ->coding_lt M(code_numeral M 2)(succM M width) ->
 (forall i,coding_lt M i params ->coding_lt M(succM M(succM M(succM M(succM M i))))(succM M width)) ->
 source_cutoff_shift_thrice M phi matrix ->
 source_ordinary_reflection M(source_L_domain_code M)(succM M params)phi d refl ->
 source_LL_instance M d(code_numeral M 2)level ->source_membership_block M(code_numeral M 4)(code_numeral M 2)params block ->
 source_relativization M(source_L_domain_code M)matrix lp ->source_set_relativization M(code_numeral M 2)matrix sp ->
 code_relation M(L_definable_profile_environment lp sp)(E_L_carrier_reflection(CEvar 0)(CEvar 1))allr ->
 source_full_prv M ub uc gn refl ->source_full_prv M ub uc gn level ->source_full_prv M ub uc gn block ->
 source_full_prv M gb gc gn allr.
Proof.
 intros HP BM HC HS HSC BD B2 HNames HMatrix HR HL HB HLP HSP HGraph PR PL PB.
 destruct(sf_relation_total M SFMember(zeroM M)(code_numeral M 2))as(member&HM).
 destruct(source_iff_total M lp sp)as(equiv&HE).
 destruct(sf_relation_total M SFImpl member equiv)as(point&HPoint).
 destruct(sf_relation_total M SFAll point(zeroM M))as(other&HAll).
 destruct(source_iff_parts M lp sp equiv HE)as(lr&rl&HLR&HRL&HIff).
 assert(HOther:code_relation M(L_definable_profile_environment lp sp)(E_L_carrier_reflection(CEvar 0)(CEvar 1))other).
 { unfold E_L_carrier_reflection,E_sf_iff,L_definable_profile_environment. functionality_graph. }
 pose proof(code_relation_functional M _ _ other allr HOther HGraph)as E. subst other.
 assert(BE:source_bounded M equiv(succM M width)).
 { apply(source_iff_bounded M lp sp equiv(succM M width));[| |exact HE].
   - exact(source_relativization_preserves_bound M matrix(source_L_domain_code M)(succM M width)lp(numerical_L_domain_bounded M)BM HLP).
   - exact(source_set_relativization_preserves_bound M matrix(code_numeral M 2)(succM M width)sp B2 BM HSP). }
 exact(source_full_L_separation_reflection_all M phi matrix params d refl level block lp sp equiv member point allr
  gb gc gn ub uc width HP HC HS HSC BD B2 HNames BE HMatrix HR HL HB HLP HSP HE HM HPoint HAll PR PL PB).
Qed.
Print Assumptions source_full_L_separation_carrier_reflection.
