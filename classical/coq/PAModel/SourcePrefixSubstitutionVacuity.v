(** A source formula whose whole free-variable bound lies inside an actual
    substitution prefix is a renaming image of that prefix. Consequently a
    name absent from every prefix value is genuinely vacuous in the output. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SourceBounded
 NumericalSubstitution NumericalSubstitutionMaps NumericalRenaming NumericalRenamingMaps
 SourceRenamingSquare SourceShiftSpecialization SourceRenamingIdentity RenamingSubstitution
 SourceNamedVacuity SourceNamedVacuityImages.
Unset Implicit Arguments.
Theorem source_prefix_substitution_is_renaming M f b c n g l:
 source_bounded M f n ->numerical_substitution M f b c n(zeroM M)g ->
 source_bounded M g l ->numerical_renaming M f b c n(zeroM M)g.
Proof.
 intros BF HS BG.
 assert(HF:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ n BF).
   intros i _. apply source_empty_renaming_lookup. }
 assert(HG:numerical_renaming M g(zeroM M)(zeroM M)(zeroM M)(zeroM M)g).
 { apply(numerical_renaming_identity_on_bound M g _ _ _ _ l BG).
   intros i _. apply source_empty_renaming_lookup. }
 apply(proj2(numerical_renaming_substitution M f b c n(zeroM M)g)).
 rewrite coding_add_zero_r.
 apply(numerical_source_renaming_square M f n b c n(zeroM M)
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)b c n n g f g BF HS HF HG).
 intros i j v w HI HJ HV HW.
 assert(EV:v=i)by(exact(renaming_lookup_functional M _ _ _ _ i v i HW(source_empty_renaming_lookup M i))). subst v.
 assert(EW:w=j)by(exact(renaming_lookup_functional M _ _ _ _ j w j HV(source_empty_renaming_lookup M j))). subst w.
 apply(proj2(substitution_lookup_inside M b c n n i j HI)).
 exact(proj1(substitution_lookup_inside M b c n(zeroM M)i j HI)HJ).
Qed.
Theorem source_named_vacuous_prefix_substitution M f b c n g l x:
 source_bounded M f n ->numerical_substitution M f b c n(zeroM M)g ->source_bounded M g l ->
 (forall i j,coding_lt M i n ->substitution_lookup M b c n(zeroM M)i j ->j<>x) ->
 source_named_vacuous M x g.
Proof.
 intros BF HS BG HA.
 apply(source_named_vacuous_renaming_image M f g n b c n(zeroM M)x BF
  (source_prefix_substitution_is_renaming M f b c n g l BF HS BG)).
 intros i j HI HJ. apply(HA i j HI).
 apply(proj2(substitution_lookup_inside M b c n(zeroM M)i j HI)).
 exact(proj1(renaming_lookup_inside M b c n(zeroM M)i j HI)HJ).
Qed.
Print Assumptions source_prefix_substitution_is_renaming.
Print Assumptions source_named_vacuous_prefix_substitution.
