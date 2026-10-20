(** Actual EnvF existence for arbitrary assigned parameter names.
    The varying-count uniform theorem is transported in its closed axiom
    context, then used in an arbitrary bounded extension of that context. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 SourcePropositionalRebase SourceBounded SourceDefinabilityBounds SourceDefinabilityPrimitives SourceEnvInClosureRecipe
 SourceEnvFScopedHole SourceEnvInClosureRoleMaps SourceLocalAssignedEnvRenaming SourceLocalNamedClosureExistence
 SourceLocalParameterAssignment SourceLocalMembershipBlock SourceLocalRoleParameterGraphs
 SourceMembershipBlocks SourceFiniteCutoffShift SourceRepresentationClosureRecipe
 SourceDnEliminationInvariant NumericalEnvironments NumericalSubstitution SourceNamedQuantifierRules
 NumericalContexts NumericalSourceFull NumericalRenamingMaps NumericalRenaming SourceProofWeakening SourceDerivedRules.
Unset Implicit Arguments.
Local Opaque source_def_successor01 representation_closure_condition.
Theorem source_full_local_assigned_env_exists M fb fc fn gb gc gn count environment canonical A S C old pb pc ob oc previous
 member body ex succ closure k:
 source_envf M count environment ->source_env_in_closure_recipe M count environment canonical ->
 context_bounded M fb fc fn(zeroM M) ->source_full_prv M fb fc fn canonical ->
 context_included M fb fc fn gb gc gn ->context_bounded M gb gc gn k ->
 environment_cons M pb pc count old ob oc(succM M count) ->
 numerical_substitution M environment ob oc(succM M count)(zeroM M)previous ->old<>C ->
 (forall i v,coding_lt M i count ->beta M pb pc i v ->v<>old) ->
 sf_relation M SFMember old C member ->sf_relation M SFAnd previous member body ->
 source_named_quantifier M false old body ex ->
 code_relation M(local_closure_roles A S C)representation_successor_expression succ ->
 code_relation M(local_closure_roles A S C)representation_closure_expression closure ->
 source_dn_parameter_proofs M count pb pc A gb gc gn ->
 source_full_prv M gb gc gn succ ->source_full_prv M gb gc gn closure ->source_full_prv M gb gc gn ex.
Proof.
 intros HE(block&first&second&shifted&HB&H1&H2&H3&HCanonical)BC0 PCanonical HIncluded BC HCons HPrevious OC HFresh
  HMember HBody HEx HS HCl HProofs PS PC.
 pose proof(source_envf_bound M count environment HE)as BE.
 pose proof(source_low_parameter_shift_zero M environment(succM M count)BE)as L0.
 pose proof(source_low_parameter_shift_step M 0 environment environment first(succM M count)BE L0 H1)as L1.
 pose proof(source_low_parameter_shift_step M 1 environment first second(succM M count)BE L1 H2)as L2.
 pose proof(source_low_parameter_shift_step M 2 environment second shifted(succM M count)BE L2 H3)as L3.
 unfold E_env_in_closure in HCanonical.
 destruct(schema_expression_split M _ SFImpl _ _ canonical HCanonical)as(s0&cmid&HS0&HCMid&HOut).
 change(s0=code_numeral M(sf_encode source_def_successor01))in HS0. subst s0.
 destruct(schema_expression_split M _ SFImpl _ _ cmid HCMid)as(c0&clast&HC0&HCLast&HCM).
 change(c0=code_numeral M(sf_encode representation_closure_condition))in HC0. subst c0.
 destruct(schema_expression_split M _ SFImpl _ _ clast HCLast)as(b0&cex&HB0&HCEx&HCL).
 change(b0=block)in HB0. subst b0.
 destruct(schema_expression_split M _ SFEx _ _ cex HCEx)as(cbody&z0&HCB&HZ0&HCE).
 change(z0=zeroM M)in HZ0. subst z0.
 destruct(schema_expression_split M _ SFAnd _ _ cbody HCB)as(sh&mem&HSh&HMem&HCBAnd).
 change(sh=shifted)in HSh. subst sh. change(mem=code_numeral M(sf_make SFMember 0 3))in HMem. subst mem.
 destruct(source_local_role_assignment_total M count pb pc A S C)as(rb&rc&HRole).
 pose proof(source_local_role_zero M count pb pc A S C rb rc HRole)as HZero.
 pose proof(source_local_role_one M count pb pc A S C rb rc HRole)as HOne.
 pose proof(source_local_role_two M count pb pc A S C rb rc HRole)as HTwo.
 pose proof(source_local_three_roles_renaming M source_def_successor01 A S C rb rc(source_local_role_length M count)succ
  representation_successor_finite_bound HZero HOne HTwo HS)as HSR.
 pose proof(source_local_three_roles_renaming M representation_closure_condition A S C rb rc(source_local_role_length M count)closure
  representation_closure_finite_bound HZero HOne HTwo HCl)as HCR.
 pose proof(source_local_assigned_env_witness_renaming M count environment shifted previous pb pc old ob oc C rb rc(source_local_role_length M count)
  member body ex cbody cex BE L3 HCons HPrevious OC HFresh
  (fun i v HI HV=>source_local_role_parameter M count pb pc A S C rb rc i v HRole HI HV)HTwo HMember HBody HEx HCBAnd HCE)as HER.
 destruct(numerical_renaming_total M block rb rc(source_local_role_length M count)(zeroM M))as(mapped&HBR).
 destruct(sf_relation_total M SFImpl mapped ex)as(last&HL).
 destruct(sf_relation_total M SFImpl closure last)as(middle&HM).
 destruct(sf_relation_total M SFImpl succ middle)as(out&HO).
 assert(HLast:numerical_renaming M clast rb rc(source_local_role_length M count)(zeroM M)last).
 { apply(proj2(numerical_renaming_binary M SFImpl block cex clast rb rc(source_local_role_length M count)(zeroM M)last
    (or_intror(or_intror eq_refl))HCL)). exists mapped,ex. auto. }
 assert(HMid:numerical_renaming M cmid rb rc(source_local_role_length M count)(zeroM M)middle).
 { apply(proj2(numerical_renaming_binary M SFImpl(code_numeral M(sf_encode representation_closure_condition))clast cmid
    rb rc(source_local_role_length M count)(zeroM M)middle(or_intror(or_intror eq_refl))HCM)). exists closure,last. auto. }
 assert(HFinal:numerical_renaming M canonical rb rc(source_local_role_length M count)(zeroM M)out).
 { apply(proj2(numerical_renaming_binary M SFImpl(code_numeral M(sf_encode source_def_successor01))cmid canonical
    rb rc(source_local_role_length M count)(zeroM M)out(or_intror(or_intror eq_refl))HOut)). exists succ,middle. auto. }
 pose proof(source_full_local_closed_renaming M fb fc fn canonical rb rc(source_local_role_length M count)(zeroM M)out BC0 PCanonical HFinal)as POut0.
 pose proof(source_full_prv_weaken_bounded M fb fc fn gb gc gn out k POut0 HIncluded BC)as POut.
 pose proof(source_full_local_membership_block M count pb pc A S C rb rc block mapped gb gc gn k HRole HB HBR BC HProofs)as PBlock.
 exact(source_full_modus_ponens M gb gc gn mapped ex last HL
  (source_full_modus_ponens M gb gc gn closure last middle HM
   (source_full_modus_ponens M gb gc gn succ middle out HO POut PS)PC)PBlock).
Qed.
Print Assumptions source_full_local_assigned_env_exists.
