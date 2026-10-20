(** A pure theorem relativized using only the domain of the actual
 renamed free support. Unused internal proof variables are not assumptions
 of the final context. The entire source proof rename and cut is explicit. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded SetFormulaCodes
 NumericalSourceFull NumericalContexts NumericalRenaming NumericalRenamingMaps ContextCombination
 SourcePureRelativeRule SourceContextTransport SourceClosedContextShift SourceDomainContexts SourceDomainInstances
 SourceDomainSupportedRenaming SourceRelativization SourceRelativizationFunctionality SourceRelativizationRenaming NumericalInstantiation.
Unset Implicit Arguments.
Theorem source_pure_relative_supported_rule M domain f:
 source_bounded M domain(code_numeral M 1)->source_full_prv M(zeroM M)(zeroM M)(zeroM M)f->
 exists bound,forall rb rc rn delta renamed relative b c n,
 numerical_renaming M f rb rc rn delta renamed->source_relativization M domain renamed relative->
 source_context_finite_bound M b c n->
 (forall i j di,coding_lt M i bound->renaming_lookup M rb rc rn delta i j->
  numerical_instantiation M domain j di->source_full_prv M b c n di)->source_full_prv M b c n relative.
Proof.
 intros HD PF. destruct(source_pure_relative_rule M domain f HD PF)as(bound&HApply).
 exists bound. intros rb rc rn delta renamed relative b c n HR HRelative HC PD.
 destruct(source_relativization_total M domain f)as(original&HOriginal).
 destruct(source_relativization_renaming_exists M f domain rb rc rn delta renamed original HD HR HOriginal)as(result&HResult&RRelative).
 pose proof(source_relativization_functional M renamed domain result relative HResult HRelative)as E;subst result.
 destruct(source_domain_context_total M domain bound)as(db&dc&HDC).
 destruct(context_union_total M(zeroM M)(zeroM M)(zeroM M)db dc bound)as(ub&uc&un&HU).
 pose proof(source_domain_context_bounded M domain bound db dc HD HDC)as BD.
 assert(BU:context_bounded M ub uc un bound).
 { apply(source_context_union_bounded M(zeroM M)(zeroM M)(zeroM M)db dc bound ub uc un bound HU);[|exact BD].
   intros h HH. exfalso. exact(context_empty M(zeroM M)(zeroM M)h HH). }
 assert(POriginal:source_full_prv M ub uc un original).
 { apply(HApply bound ub uc un original(coding_lt_succ M bound)(ex_intro _ bound BU));[|exact HOriginal].
   intros i di HI HDI. apply full_source_Ctx.
   - exists bound. split;[exact(source_domain_instance_bound M domain i di bound HD HI HDI)|exact BU].
   - apply(context_union_right M(zeroM M)(zeroM M)(zeroM M)db dc bound ub uc un HU).
     apply(proj2(source_domain_context_member_iff M domain bound db dc di HDC)). exists i. auto. }
 apply(source_full_domain_supported_renaming M domain(zeroM M)(zeroM M)(zeroM M)bound db dc ub uc un original
  rb rc rn delta relative b c n HD).
 - intros h HH. exfalso. exact(context_empty M(zeroM M)(zeroM M)h HH).
 - exact HDC.
 - exact HU.
 - exact POriginal.
 - exact RRelative.
 - exact HC.
 - intros h HH. exfalso. exact(context_empty M(zeroM M)(zeroM M)h HH).
 - exact PD.
Qed.
Print Assumptions source_pure_relative_supported_rule.
