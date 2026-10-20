(** Assign the actual EnvF syntax to a complete vector [environment,values].
    The two inserted representation roles disappear by checked substitution;
    no semantic EnvF predicate is assumed. *)
From FOL.Tennenbaum Require Peano.
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 SourceBounded SourceDefinabilityBounds SourceFiniteCutoffShift NumericalEnvironments
 NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SubstitutionSource SourceDnAssignments
 SourceDnAssignedMatrix SourceSubstitutionComposition.
Unset Implicit Arguments.
Theorem source_representation_environment_query M count environment first shifted d X pb pc ab ac lb lc ln
 assignedEnv witness eb ec envAt:
 source_envf M count environment ->source_cutoff_shift M 1 environment first ->
 source_cutoff_shift M 1 first shifted ->source_dn_assignment M count pb pc d X ab ac ->
 substitution_lift M ab ac(succM M(succM M count))(zeroM M)lb lc ln ->
 numerical_substitution M shifted lb lc ln(code_numeral M 1)assignedEnv ->
 environment_cons M pb pc count witness eb ec(succM M count) ->
 numerical_substitution M environment eb ec(succM M count)(zeroM M)envAt ->
 numerical_instantiation M assignedEnv witness envAt.
Proof.
 intros HE H1 H2 HA HL HAssigned HCons HAt.
 destruct(substitution_lift_total M pb pc count(zeroM M))as(ub&uc&un&HU).
 pose proof(source_dn_assigned_matrix M count pb pc d X ab ac lb lc ln ub uc un
  environment first shifted assignedEnv(source_envf_bound M count environment HE)H1 H2 HA HL HU HAssigned)as HRaw.
 destruct(numerical_instantiation_total M assignedEnv witness)as(candidate&ib&ic&HHead&HCandidate).
 assert(HCandidateRaw:numerical_substitution M environment eb ec(succM M count)(zeroM M)candidate).
 { apply(numerical_substitution_composition M environment(succM M count)
    ub uc un(code_numeral M 1)ib ic(code_numeral M 1)(zeroM M)
    eb ec(succM M count)(zeroM M)assignedEnv candidate
    (source_envf_bound M count environment HE)HRaw HCandidate).
   intros i j v HI HJ HV.
   destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)
    as[->|[q ->]].
   - assert(EJ:j=zeroM M)by(exact(proj1(substitution_lift_head M _ _ _ _ _ _ _ _ HU)HJ)). subst j.
     assert(EV:v=witness)by(eapply substitution_lookup_functional;eassumption). subst v.
     apply(proj2(substitution_lookup_inside M eb ec(succM M count)(zeroM M)(zeroM M)witness
      (coding_zero_lt_succ M count))).
     apply(proj1(environment_lookup_inside M eb ec(succM M count)(zeroM M)witness(coding_zero_lt_succ M count))).
     exact(proj2(environment_cons_head M _ _ _ _ _ _ _ _ HCons)eq_refl).
   - assert(HQ:coding_lt M q count)by(exact(proj1(coding_lt_succ_cancel M q count)HI)).
     destruct(beta_total M pb pc q)as(value&HValue).
     assert(EJ:j=succM M value).
     { eapply substitution_lookup_functional;[exact HJ|].
       apply(proj2(substitution_lift_tail M _ _ _ _ _ _ _ _ _ HU)).
       exact(proj2(substitution_lookup_inside M pb pc count(zeroM M)q value HQ)HValue). }
     subst j. assert(EV:v=value)by(eapply substitution_lookup_functional;[exact HV|apply substitution_singleton_tail]). subst v.
     apply(proj2(substitution_lookup_inside M eb ec(succM M count)(zeroM M)(succM M q)value HI)).
     apply(proj1(environment_lookup_inside M eb ec(succM M count)(succM M q)value HI)).
     apply(proj2(environment_cons_tail M _ _ _ _ _ _ _ _ _ HCons)).
     exact(proj2(environment_lookup_inside M pb pc count q value HQ)HValue). }
 assert(E:candidate=envAt)by(eapply numerical_substitution_functional;eassumption). subst candidate.
 exists ib,ic. auto.
Qed.
Print Assumptions source_representation_environment_query.
