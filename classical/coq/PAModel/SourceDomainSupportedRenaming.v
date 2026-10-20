(** Remove irrelevant internal proof-domain names by an actual numerical
 renaming. The finite closed background stays fixed; every renamed domain
 hypothesis is replaced by an actual source proof in the target context. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SourceBounded SourceBoundMonotone
 NumericalContexts NumericalContextRenaming NumericalRenaming NumericalRenamingMaps NumericalSourceFull
 SourceDomainContexts SourceDomainInstanceRenaming SourceProofRenaming SourceHypothesisTransport
 SourceContextTransport SourceTraceBounds SourceRenamingIdentity ContextCombination NumericalInstantiation.
Unset Implicit Arguments.
Theorem source_full_domain_supported_renaming M domain ab ac an count db dc ub uc un f
 rb rc rn delta renamed gb gc gn:
 source_bounded M domain(code_numeral M 1)->context_bounded M ab ac an(zeroM M)->
 source_domain_context M domain count db dc->context_union M ab ac an db dc count ub uc un->
 source_full_prv M ub uc un f->numerical_renaming M f rb rc rn delta renamed->
 source_context_finite_bound M gb gc gn->context_included M ab ac an gb gc gn->
 (forall i j di,coding_lt M i count->renaming_lookup M rb rc rn delta i j->
  numerical_instantiation M domain j di->source_full_prv M gb gc gn di)->
 source_full_prv M gb gc gn renamed.
Proof.
 intros HD BA HDC HU PF HR HC HIn PD.
 destruct(context_renaming_total M ub uc un rb rc rn delta)as(xb&xc&HX).
 pose proof(source_full_prv_renaming M ub uc un f rb rc rn delta xb xc renamed PF HX HR)as PX.
 apply(source_full_prv_replace_hypotheses M gb gc gn HC un xb xc renamed PX).
 intros g HG. apply(proj1(context_renaming_member_iff M ub uc un rb rc rn delta xb xc g HX))in HG.
 destruct HG as(h&HH&HHG). apply(proj1(proj2 HU h))in HH. destruct HH as[HH|HH].
 - assert(E:g=h).
   { apply(numerical_renaming_functional M h rb rc rn delta g h HHG).
     apply(numerical_renaming_identity_on_bound M h rb rc rn delta(zeroM M)(BA h HH)).
     intros i HI. exfalso. exact(coding_not_lt_zero M i HI). }
   subst g. apply full_source_Ctx;[|exact(HIn h HH)].
   destruct HC as(k&BC). exists k. split;[|exact BC].
   exact(source_bounded_monotone M h(zeroM M)k(BA h HH)(coding_zero_lt_succ M k)).
 - apply(proj1(source_domain_context_member_iff M domain count db dc h HDC))in HH.
   destruct HH as(i&HI&HDI). destruct(renaming_lookup_total M rb rc rn delta i)as(j&Hij).
   exact(PD i j g HI Hij(source_domain_instance_renaming M domain i h rb rc rn delta g j HD HDI HHG Hij)).
Qed.
Print Assumptions source_full_domain_supported_renaming.
