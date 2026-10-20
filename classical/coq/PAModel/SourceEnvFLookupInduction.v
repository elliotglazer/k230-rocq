(** Actual proof-producing PA induction for lookup in internally finite
    environments, including nonstandard lengths and indices. *)
From PAModel Require Import Model CodeExpressions NumericalProofs SourceEnvFLookupRecipe SourceEnvFLookupSuccessor
 SourceDefinabilityBounds SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_zfr_env_lookup_uniform M n:source_env_lookup_proof_at M n.
Proof.
 revert n. apply(definable_induction M(source_env_lookup_proof_at M)(source_env_lookup_proof_definable M)).
 - exact(source_zfr_env_lookup_zero M).
 - exact(source_zfr_env_lookup_successor M).
Qed.
Theorem source_zfr_env_lookup_total M n k tail environment numeral:
 n=succM M(addM M k tail)->source_envf M n environment->source_numf M k numeral->
 exists out,source_env_lookup_recipe M environment numeral tail out/\source_zfr_provable M out.
Proof.
 intros HN HE HK. destruct(source_env_lookup_recipe_total M environment numeral tail)as(out&HO).
 exists out. split;[exact HO|exact(source_zfr_env_lookup_uniform M n k tail environment numeral out HN HE HK HO)].
Qed.
Print Assumptions source_zfr_env_lookup_uniform.
Print Assumptions source_zfr_env_lookup_total.
