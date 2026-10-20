(** Name transport for literal application profiles. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceEnvFLookupProfile
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps NumericalRenaming RenamingSubstitution
 SourceQuantifierRules SourceFiniteCutoffShift NumericalContextRenaming.
Unset Implicit Arguments.
Theorem source_env_profile_renaming M e i a old e' i' a' new b c n delta:
 source_env_profile M e i a old->source_env_profile M e' i' a' new->
 renaming_lookup M b c n delta e e'->renaming_lookup M b c n delta i i'->renaming_lookup M b c n delta a a'->
 numerical_renaming M old b c n delta new.
Proof.
 intros HO HN HE HI HA. apply(proj2(numerical_renaming_substitution M old b c n delta new)).
 exact(source_env_profile_substitution M e i a old e' i' a' new b c n(addM M n delta)HO HN
  (proj1(renaming_substitution_lookup M b c n delta e e')HE)
  (proj1(renaming_substitution_lookup M b c n delta i i')HI)
  (proj1(renaming_substitution_lookup M b c n delta a a')HA)).
Qed.
Theorem source_env_profile_shift M e i a old new:
 source_env_profile M e i a old->source_env_profile M(succM M e)(succM M i)(succM M a)new->source_formula_shift M old new.
Proof.
 intros HO HN. apply(source_env_profile_renaming M e i a old(succM M e)(succM M i)(succM M a)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN);apply context_shift_lookup;reflexivity.
Qed.
Print Assumptions source_env_profile_renaming.
Print Assumptions source_env_profile_shift.
