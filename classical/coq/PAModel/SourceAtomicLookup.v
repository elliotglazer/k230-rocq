(** Actual arbitrary-index lookup in the precise canonical representation
    environment: environment0, representative1, carrier2, assignment3+. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceFiniteCutoffShift
 SourceDefinabilityBounds SourceQuantifierRules SourceDefinabilityLogicalStep SourceUnaryRenamingGraph
 NumericalRenaming NumericalInstantiation SourceEnvFLookupRecipe SourceEnvFLookupInduction
 SourceEnvFLookupProfile SourceEnvFLookupProfileTransport SourceAtomicLookupMaps SourceAtomicReverseIndices
 SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_zfr_atomic_lookup M count index reverse environment first guard numeral name namedNumeral profile inner result:
 source_reverse_index M count index reverse->source_envf M count environment->source_numf M reverse numeral->
 source_cutoff_shift M 1 environment first->source_cutoff_shift M 1 first guard->
 numerical_instantiation M numeral name namedNumeral->
 source_env_profile M(zeroM M)name(succM M(succM M(succM M index)))profile->
 sf_relation M SFImpl namedNumeral profile inner->sf_relation M SFImpl guard inner result->source_zfr_provable M result.
Proof.
 intros HIndex HEnv HNum HFirst HGuard HNamed HProfile HInner HResult.
 destruct(source_env_lookup_recipe_total M environment numeral index)as(old&HOld).
 pose proof(source_zfr_env_lookup_uniform M count reverse index environment numeral old HIndex HEnv HNum HOld)as POld.
 destruct HOld as(shifted&oldProfile&oldInner&HShifted&HOldProfile&HOldInner&HOld).
 destruct(source_atomic_lookup_map_total M name)as(rb&rc&HMap).
 pose proof(source_atomic_lookup_environment_action M environment first guard shifted name rb rc(succM M count)
  (source_envf_bound M count environment HEnv)HFirst HGuard HShifted HMap)as REnv.
 destruct HMap as(HZero&HOne&HTail).
 pose proof(source_numf_bound M reverse numeral HNum)as BN.
 pose proof(source_unary_instance_renaming_graph M numeral(zeroM M)numeral rb rc(code_numeral M 2)(code_numeral M 1)name namedNumeral
  BN(source_unit_instantiation_self M numeral BN)HZero HNamed)as RNum.
 pose proof(source_env_profile_renaming M(code_numeral M 1)(zeroM M)(succM M(succM M index))oldProfile
  (zeroM M)name(succM M(succM M(succM M index)))profile rb rc(code_numeral M 2)(code_numeral M 1)
  HOldProfile HProfile HOne HZero(HTail index))as RProfile.
 assert(RInner:numerical_renaming M oldInner rb rc(code_numeral M 2)(code_numeral M 1)inner).
 { apply(proj2(numerical_renaming_binary M SFImpl numeral oldProfile oldInner rb rc(code_numeral M 2)(code_numeral M 1)inner
    (or_intror(or_intror eq_refl))HOldInner)). exists namedNumeral,profile. repeat split;assumption. }
 assert(ROut:numerical_renaming M old rb rc(code_numeral M 2)(code_numeral M 1)result).
 { apply(proj2(numerical_renaming_binary M SFImpl shifted oldInner old rb rc(code_numeral M 2)(code_numeral M 1)result
    (or_intror(or_intror eq_refl))HOld)). exists guard,inner. repeat split;assumption. }
 apply(proj1(source_zfr_descriptor_provable M result)).
 exact(source_descriptor_provable_renaming M ZFRSourceDescriptor old rb rc(code_numeral M 2)(code_numeral M 1)result
  (proj2(source_zfr_descriptor_provable M old)POld)ROut).
Qed.
Print Assumptions source_zfr_atomic_lookup.
