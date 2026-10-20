(** Actual old lookup-proof relocation into the two-witness successor roles.
    The exact finite map moves query0 to2 without moving environment1. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceFiniteCutoffShift SourceQuantifierRules NumericalRenaming NumericalInstantiation SourceDefinabilityLogicalStep
 SourceUnaryRenamingGraph SourceEnvFLookupRecipe SourceEnvFLookupProfile SourceEnvFLookupProfileTransport SourceEnvFLookupRoleMap
 SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_zfr_env_lookup_ih_relocation M p q tail old p1 p2 p3 shifted q2 profile inner target count:
 source_bounded M p(succM M count)->source_bounded M q(code_numeral M 1)->
 source_env_lookup_recipe M p q tail old->source_cutoff_shift M 1 p p1->source_cutoff_shift M 1 p1 p2->source_cutoff_shift M 1 p2 p3->
 source_formula_shift M p3 shifted->numerical_instantiation M q(code_numeral M 2)q2->
 source_env_profile M(code_numeral M 1)(code_numeral M 2)(succM M(succM M(succM M(succM M(succM M tail)))))profile->
 sf_relation M SFImpl q2 profile inner->sf_relation M SFImpl shifted inner target->
 source_zfr_provable M old->source_zfr_provable M target.
Proof.
 intros BP BQ(ps&oldprofile&oldinner&HPS&HP&HOldInner&HOld)H1 H2 H3 HS HQ2 HProfile HInner HTarget POld.
 destruct(source_env_lookup_role_map_total M)as(rb&rc&HMap).
 pose proof(source_env_lookup_environment_action M p p1 p2 p3 ps shifted rb rc(succM M count)BP H1 H2 H3 HPS HS HMap)as REnv.
 destruct HMap as(HZero&HOne&HTail).
 pose proof(source_unary_instance_renaming_graph M q(zeroM M)q rb rc(code_numeral M 2)(code_numeral M 3)(code_numeral M 2)q2
  BQ(source_unit_instantiation_self M q BQ)HZero HQ2)as RNum.
 pose proof(source_env_profile_renaming M(code_numeral M 1)(zeroM M)(succM M(succM M tail))oldprofile
  (code_numeral M 1)(code_numeral M 2)(succM M(succM M(succM M(succM M(succM M tail)))))profile
  rb rc(code_numeral M 2)(code_numeral M 3)HP HProfile HOne HZero(HTail tail))as RProfile.
 assert(RInner:numerical_renaming M oldinner rb rc(code_numeral M 2)(code_numeral M 3)inner).
 { apply(proj2(numerical_renaming_binary M SFImpl q oldprofile oldinner rb rc(code_numeral M 2)(code_numeral M 3)inner
    (or_intror(or_intror eq_refl))HOldInner)). exists q2,profile. repeat split;assumption. }
 assert(ROut:numerical_renaming M old rb rc(code_numeral M 2)(code_numeral M 3)target).
 { apply(proj2(numerical_renaming_binary M SFImpl ps oldinner old rb rc(code_numeral M 2)(code_numeral M 3)target
    (or_intror(or_intror eq_refl))HOld)). exists shifted,inner. repeat split;assumption. }
 apply(proj1(source_zfr_descriptor_provable M target)).
 exact(source_descriptor_provable_renaming M ZFRSourceDescriptor old rb rc(code_numeral M 2)(code_numeral M 3)target
  (proj2(source_zfr_descriptor_provable M old)POld)ROut).
Qed.
Print Assumptions source_zfr_env_lookup_ih_relocation.
