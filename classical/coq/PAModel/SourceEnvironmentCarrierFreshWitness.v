(** Allocate the old-environment eigenname in the actual reopened An
 invariant. Both Dn and the named universal graph are derived, with no
 assumption that the internal assignment count is standard. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceEnvironmentCarrierRecipe SourceEnvironmentCarrierReopen SourceEnvironmentCoverageNaming
 SourceDefinabilityBounds SourceFiniteCutoffShift SourceRepresentativeRenaming SourceDn SourceNamedQuantifierRules.
From FOL.Tennenbaum Require Peano.
Unset Implicit Arguments.
Theorem source_environment_carrier_fresh_witness M count carrier named witness:
 source_environment_carrier_recipe M count carrier ->source_representative_renaming M(code_numeral M 2)carrier named ->
 ~coding_lt M witness(succM M(succM M(succM M count))) ->
 exists environment first guard original point namedguard member namedmember body namedbody,
 source_envf M count environment /\source_cutoff_shift M 1 environment first /\source_cutoff_shift M 1 first guard /\
 code_relation M(fun _=>guard)E_environment_carrier_point original /\source_dn M count original carrier /\
 source_representative_renaming M witness first namedguard /\
 sf_relation M SFMember(zeroM M)(succM M(succM M count))member /\
 sf_relation M SFMember witness(succM M(succM M count))namedmember /\
 sf_relation M SFImpl first member body /\sf_relation M SFImpl namedguard namedmember namedbody /\
 source_named_quantifier M true witness namedbody point /\
 source_dn M count point named /\source_bounded M body(succM M(succM M(succM M count))).
Proof.
 intros HR HNamed HFresh.
 destruct(source_environment_carrier_reopen M count carrier named HR HNamed)
  as(environment&first&guard&original&oldmember&inner&point&HE&H1&H2&HP&HD&HM&HI&HAll&HPointName&HDNamed).
 pose proof(source_cutoff_shift_bounded M 1 environment first count(source_envf_bound M count environment HE)H1)as BF.
 assert(BFirst:source_bounded M first(succM M(succM M(succM M count)))).
 { apply(source_bounded_monotone M first(succM M(succM M count))(succM M(succM M(succM M count)))BF).
   apply coding_lt_succ_cases. left. apply coding_lt_succ. }
 destruct(source_environment_coverage_witness_total M first guard(succM M count)witness
  (succM M(succM M(succM M count)))BFirst H2(coding_lt_succ M(succM M(succM M count)))HFresh)
  as(namedguard&member&namedmember&shiftedmember&body&namedbody&shiftedbody&otherpoint&HG&HM0&HMN&HMS&HB&HNB&HSB&HOtherAll&HBodyName&HNamedAll&BBody).
 assert(EM:shiftedmember=oldmember)by(eapply sf_relation_functional;eassumption). subst shiftedmember.
 assert(EI:shiftedbody=inner)by(eapply sf_relation_functional;eassumption). subst shiftedbody.
 assert(EP:otherpoint=point)by(eapply sf_relation_functional;eassumption). subst otherpoint.
 exists environment,first,guard,original,point,namedguard,member,namedmember,body,namedbody.
 exact(conj HE(conj H1(conj H2(conj HP(conj HD(conj HG(conj HM0(conj HMN(conj HB(conj HNB(conj HNamedAll(conj HDNamed BBody)))))))))))).
Qed.
Print Assumptions source_environment_carrier_fresh_witness.
