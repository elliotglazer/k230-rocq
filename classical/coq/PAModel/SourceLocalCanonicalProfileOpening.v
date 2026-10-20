(** The canonical L-definability formula is opened twice at actual high
    internal names. All binder graphs and the exact pointwise matrix are
    constructed; no formula interpretation or proof premise is assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetCodeDescent
 SetSchemaConstructors SourceBounded SourceBoundMonotone SourceLDefinableProfile SourceLFixed
 NumericalInstantiation NumericalSubstitution NumericalSubstitutionMaps NumericalRenaming SourceRepresentativeRenaming
 SourceSetRelativization SourceSetRelativizationBounds SourceNamedQuantifierRules SourceFreshNamedOpening
 SourceDefinableProfileOpening SourceIffGraphs SourcePropositionalRebase SourceRenamingBounds SourceDomainInstances.
Unset Implicit Arguments.
Local Opaque source_L_domain_code source_set_relativization source_bounded numerical_instantiation numerical_substitution numerical_renaming source_named_quantifier code_relation source_representative_renaming.
Theorem source_local_canonical_profile_open_total M phi count target selected value:
 source_bounded M phi(succM M count) ->source_L_definable_profile M phi target ->
 coding_lt M(succM M count)(succM M selected) ->coding_lt M(succM M selected)(succM M value) ->
 exists body inL allProfile profile assigned relative memberValue inSelected newPair,
 source_named_quantifier M false selected body target /\
 numerical_instantiation M(source_L_domain_code M)selected inL /\
 sf_relation M SFAnd inL allProfile body /\
 source_named_quantifier M true value profile allProfile /\
 source_representative_renaming M value phi assigned /\source_set_relativization M(zeroM M)assigned relative /\
 sf_relation M SFMember value(zeroM M)memberValue /\sf_relation M SFMember value selected inSelected /\
 sf_relation M SFAnd memberValue relative newPair /\source_iff_graph M inSelected newPair profile /\
 source_bounded M body(succM M selected) /\source_bounded M allProfile(succM M selected) /\
 source_bounded M profile(succM M value) /\source_bounded M relative(succM M value).
Proof.
 intros BF HT HSelected HValue.
 pose proof(source_L_definable_profile_bounded M count phi target BF HT)as BT.
 destruct HT as(first&matrix&oldRel&HFirst&HMatrix&HOldRel&HRecipe).
 set(rho:=L_definable_profile_environment oldRel(source_L_domain_code M)).
 change(code_relation M rho(E_L_definable_profile(CEvar 0)(CEvar 1))target)in HRecipe.
 unfold E_L_definable_profile in HRecipe.
 destruct(schema_expression_split M rho SFEx _ _ target HRecipe)as(rawbody&zero&HBody&HZ&HRawEx).
 change(zero=zeroM M)in HZ. subst zero.
 destruct(schema_expression_split M rho SFAnd _ _ rawbody HBody)as(oldL&oldAll&HOldL&HOldAll&HRawAnd).
 change(oldL=source_L_domain_code M)in HOldL. subst oldL.
 destruct(schema_expression_split M rho SFAll _ _ oldAll HOldAll)as(oldPoint&zero&HOldPoint&HZ&HRawAll).
 change(zero=zeroM M)in HZ. subst zero.
 destruct(numerical_instantiation_total M rawbody selected)as(body&HOpened).
 destruct HOpened as(ib&ic&HHead&HSub).
 destruct(proj1(numerical_substitution_binary M SFAnd(source_L_domain_code M)oldAll rawbody ib ic(code_numeral M 1)(zeroM M)body
  (or_introl eq_refl)HRawAnd)HSub)as(inL&allProfile&HInL&HAllSub&HAnd).
 destruct(proj1(numerical_substitution_quantifier M true oldPoint oldAll ib ic(code_numeral M 1)(zeroM M)allProfile HRawAll)HAllSub)
  as(lb&lc&ln&profileBody&HLift&HPointSub&HAll).
 assert(HOpened:numerical_instantiation M rawbody selected body)by(exists ib,ic;auto).
 assert(BRaw:source_bounded M rawbody(succM M(succM M count))).
 { exact(proj1(source_bounded_accept_unary M SFEx rawbody target(succM M count)(or_intror eq_refl)HRawEx)BT). }
 assert(BBody:source_bounded M body(succM M selected)).
 { apply(numerical_instantiation_bounded M rawbody selected body(succM M selected));[|apply coding_lt_succ|exact HOpened].
   apply(source_bounded_monotone M rawbody(succM M(succM M count))_ BRaw).
   exact(coding_lt_trans M _ _ _(proj2(coding_lt_succ_cancel M(succM M count)(succM M selected))HSelected)(coding_lt_succ M _)). }
 pose proof(proj2(proj1(source_bounded_accept_binary M SFAnd inL allProfile body(succM M selected)(or_introl eq_refl)HAnd)BBody))as BAll.
 pose proof(proj1(source_bounded_accept_unary M SFAll profileBody allProfile(succM M selected)(or_introl eq_refl)HAll)BAll)as BProfileBody.
 destruct(numerical_instantiation_total M profileBody value)as(profile&HPoint).
 assert(BProfile:source_bounded M profile(succM M value)).
 { apply(numerical_instantiation_bounded M profileBody value profile(succM M value));[|apply coding_lt_succ|exact HPoint].
   apply(source_bounded_monotone M profileBody(succM M(succM M selected))_ BProfileBody).
   exact(coding_lt_trans M _ _ _(proj2(coding_lt_succ_cancel M(succM M selected)(succM M value))HValue)(coding_lt_succ M _)). }
 destruct(source_representative_renaming_total M value phi)as(assigned&HAssigned).
 destruct(source_set_relativization_total M(zeroM M)assigned)as(relative&HRelative).
 assert(HT':source_definable_profile M(source_L_domain_code M)phi target).
 { exists first,matrix,oldRel. repeat split;assumption. }
 destruct(source_definable_profile_opening M(source_L_domain_code M)phi count target rawbody selected body inL allProfile profileBody value profile assigned relative
  BF HT' HRawEx HOpened HAnd HAll HPoint HAssigned HRelative)as(HDomain&memberY&memberA&rhs&HMY&HMA&HRight&HIff).
 assert(BAssigned:source_bounded M assigned(succM M value)).
 { apply(numerical_renaming_preserves_bound M phi value value(code_numeral M 1)(zeroM M)assigned(succM M count)(succM M value)BF HAssigned).
   intros i j HI HMap. destruct HMap as[[HSmall HBeta]|[HOutside EJ]].
   - rewrite(domain_index_below_one M i HSmall)in HBeta.
     rewrite(beta_unique M value value(zeroM M)j value HBeta(beta_singleton M value)). apply coding_lt_succ.
   - rewrite EJ,coding_add_zero_r. exact(source_bound_lt_le M i(succM M count)(succM M value)HI
      (coding_lt_trans M _ _ _ HSelected(coding_lt_trans M _ _ _ HValue(coding_lt_succ M _)))). }
 assert(BRelative:source_bounded M relative(succM M value)).
 { exact(source_set_relativization_preserves_bound M assigned(zeroM M)(succM M value)relative(coding_zero_lt_succ M value)BAssigned HRelative). }
 exists body,inL,allProfile,profile,assigned,relative,memberA,memberY,rhs.
 repeat split;try assumption.
 - exact(source_fresh_instantiation_named_quantifier M false rawbody target selected body(succM M count)BRaw HSelected HOpened HRawEx).
 - exact(source_fresh_instantiation_named_quantifier M true profileBody allProfile value profile(succM M selected)BProfileBody HValue HPoint HAll).
Qed.
Print Assumptions source_local_canonical_profile_open_total.
