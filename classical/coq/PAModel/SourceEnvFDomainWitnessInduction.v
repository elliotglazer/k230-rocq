(** PA-definable induction proving the actual EnvF domain law for every
    internal environment length, including nonstandard lengths. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SourceDefinabilityIteration SourceDefinabilityBounds
 SourceEnvFDomainWitnessRecipe SourceEnvFDomainWitnessFixed SourceEnvFDomainWitnessStep SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_zfr_env_domain_witness M count:source_env_domain_witness_proof_at M count.
Proof.
 revert count. apply(definable_induction M(source_env_domain_witness_proof_at M)(source_env_domain_witness_proof_definable M)).
 - exact(source_zfr_env_domain_witness_zero M).
 - intros count IH environment numeral out HE HN HO.
   apply source_def_iteration_succ in HE,HN. destruct HE as(p&HP&HEnv),HN as(q&HQ&HNum).
   destruct(source_env_domain_witness_recipe_total M p q)as(old&HOld).
   exact(source_zfr_env_domain_witness_step M count p q environment numeral old out
    (source_envf_bound M count p HP)(source_numf_bound M count q HQ)HEnv HNum HOld HO(IH p q old HP HQ HOld)).
Qed.
Theorem source_zfr_env_domain_witness_total M count environment numeral:
 source_envf M count environment->source_numf M count numeral->exists out,
 source_env_domain_witness_recipe M environment numeral out/\source_zfr_provable M out.
Proof.
 intros HE HN. destruct(source_env_domain_witness_recipe_total M environment numeral)as(out&HO).
 exists out. split;[exact HO|exact(source_zfr_env_domain_witness M count environment numeral out HE HN HO)].
Qed.
Print Assumptions source_zfr_env_domain_witness.
Print Assumptions source_zfr_env_domain_witness_total.
