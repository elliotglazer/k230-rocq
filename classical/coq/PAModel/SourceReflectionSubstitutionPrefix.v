(** Complete an arbitrary numerical substitution to its internally finite
 live prefix. This is genuine PA bounded collection and beta packing. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalSubstitutionMaps NumericalSubstitution
 SourceBounded SourceBoundedMapComposition SourceSubstitutionComposition SourceSubstitutionBounds SourceSubstitutionIdentity SourceShiftSpecialization.
Unset Implicit Arguments.
Theorem source_substitution_live_prefix_total M rb rc rn base count:
 exists pb pc,forall i v,coding_lt M i count ->
 (substitution_lookup M pb pc count(zeroM M)i v <->substitution_lookup M rb rc rn base i v).
Proof.
 destruct(bounded_substitution_composition_map M rb rc rn base(zeroM M)(zeroM M)(zeroM M)(zeroM M)count)as(pb&pc&HP).
 exists pb,pc. intros i v HI. rewrite(HP i v HI). split.
 - intros(j&HJ&HV). pose proof(substitution_lookup_functional M(zeroM M)(zeroM M)(zeroM M)(zeroM M)j v j HV(source_empty_substitution_lookup M j))as E. now subst v.
 - intro HV. exists v. split;[exact HV|apply source_empty_substitution_lookup].
Qed.
Theorem numerical_substitution_live_prefix M f count rb rc rn base out pb pc k:
 source_bounded M f count ->substitution_maps_bound M rb rc rn base count k ->
 numerical_substitution M f rb rc rn base out ->
 (forall i v,coding_lt M i count ->substitution_lookup M rb rc rn base i v ->substitution_lookup M pb pc count(zeroM M)i v) ->
 numerical_substitution M f pb pc count(zeroM M)out.
Proof.
 intros HF HM HS HP.
 pose proof(numerical_substitution_preserves_bound M f rb rc rn base out count k HF HS HM)as BO.
 assert(HId:numerical_substitution M out(zeroM M)(zeroM M)(zeroM M)(zeroM M)out).
 { apply(numerical_substitution_identity_on_bound M out(zeroM M)(zeroM M)(zeroM M)(zeroM M)k BO).
   intros i _. apply source_empty_substitution_lookup. }
 apply(numerical_substitution_composition M f count rb rc rn base(zeroM M)(zeroM M)(zeroM M)(zeroM M)pb pc count(zeroM M)out out HF HS HId).
 intros i j v HI HJ HV. pose proof(substitution_lookup_functional M(zeroM M)(zeroM M)(zeroM M)(zeroM M)j v j HV(source_empty_substitution_lookup M j))as E. subst v.
 exact(HP i j HI HJ).
Qed.
Print Assumptions source_substitution_live_prefix_total.
Print Assumptions numerical_substitution_live_prefix.
