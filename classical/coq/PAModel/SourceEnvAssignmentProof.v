(** Actual source inference for extending an assigned EnvF environment.
    All mathematical content is in the literal Ext0 premise. *)
From FOL.Tennenbaum Require Peano.
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs SetFormulaCodes
 SourceBounded SourceDefinabilityBounds SourceDefinabilityStep NumericalEnvironments NumericalSubstitution
 NumericalSourceFull SourceInstantiationConstructors SourceNamedQuantifierRules SourceEnvInClosureConstructor
 SourceEnvAssignmentConstructor SourceDnEliminationInvariant.
Unset Implicit Arguments.
Theorem source_full_env_assignment_extension M count environment next pb pc value vb vc
 old ob oc previous new nb nc target extension gb gc gn:
 source_envf M count environment ->source_def_step M true environment next ->
 environment_cons M pb pc count value vb vc(succM M count) ->
 environment_cons M pb pc count old ob oc(succM M count) ->
 environment_cons M vb vc(succM M count)new nb nc(succM M(succM M count)) ->
 numerical_substitution M environment ob oc(succM M count)(zeroM M)previous ->
 numerical_substitution M next nb nc(succM M(succM M count))(zeroM M)target ->
 code_relation M(EIC_ext_roles old new value)EIC_ext_expression extension ->
 old<>new ->value<>old ->(forall i v,coding_lt M i count ->beta M pb pc i v ->v<>old) ->
 source_full_prv M gb gc gn previous ->source_full_prv M gb gc gn extension ->
 source_full_prv M gb gc gn target.
Proof.
 intros HE HS HV HO HN HP HT HExt HON HVO HFresh POld PExt.
 destruct(sf_relation_total M SFAnd previous extension)as(pair&HPair).
 pose proof(source_env_assignment_named_constructor M count environment next pb pc value vb vc
  old ob oc previous new nb nc target extension pair HE HS HV HO HN HP HT HExt HPair HON HVO HFresh)as HQ.
 apply(source_full_named_quantifier_ex_intro M gb gc gn old pair target HQ).
 apply(full_source_CI M gb gc gn previous extension pair).
 - apply(source_wf_binary M gb gc gn SFAnd previous extension pair(or_introl eq_refl)HPair
    (source_full_prv_wellformed M gb gc gn previous POld)(source_full_prv_wellformed M gb gc gn extension PExt)).
 - exact POld.
 - exact PExt.
 - exact HPair.
Qed.
Theorem source_dn_parameter_proofs_cons M count pb pc head qb qc X gb gc gn member:
 environment_cons M pb pc count head qb qc(succM M count) ->sf_relation M SFMember head X member ->
 source_full_prv M gb gc gn member ->source_dn_parameter_proofs M count pb pc X gb gc gn ->
 source_dn_parameter_proofs M(succM M count)qb qc X gb gc gn.
Proof.
 intros HC HM PM HP i value test HI HV HTest.
 apply(proj2(environment_lookup_inside M qb qc(succM M count)i value HI))in HV.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)
  as[->|[q ->]].
 - pose proof(proj1(environment_cons_head M _ _ _ _ _ _ _ _ HC)HV)as E. subst value.
   assert(ET:test=member)by(eapply sf_relation_functional;eassumption). now subst test.
 - assert(HQ:coding_lt M q count)by(exact(proj1(coding_lt_succ_cancel M q count)HI)).
   apply(proj1(environment_cons_tail M _ _ _ _ _ _ _ _ _ HC))in HV.
   exact(HP q value test HQ(proj1(environment_lookup_inside M pb pc count q value HQ)HV)HTest).
Qed.
Print Assumptions source_full_env_assignment_extension.
Print Assumptions source_dn_parameter_proofs_cons.
