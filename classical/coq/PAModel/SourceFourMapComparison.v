(** The exact finite variable-action chain in the named K core alignment.
    Intermediate compositions are beta-packed on the source bound; there
    is no additional induction or assumed compositionality of coded syntax. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  SourceBounded NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps NumericalRenaming
  RenamingSubstitution SourceBoundedMapComposition.
Unset Implicit Arguments.

Theorem numerical_four_substitutions_compare M f k
    ab ac an abase bb bc bn bbase cb cc cn cbase db dc dn dbase tb tc tn tbase f1 f2 f3 out :
  source_bounded M f k ->
  numerical_substitution M f ab ac an abase f1 ->
  numerical_substitution M f1 bb bc bn bbase f2 ->
  numerical_substitution M f2 cb cc cn cbase f3 ->
  numerical_substitution M f3 db dc dn dbase out ->
  (forall i j1 j2 j3 v,coding_lt M i k ->
    substitution_lookup M ab ac an abase i j1 ->
    substitution_lookup M bb bc bn bbase j1 j2 ->
    substitution_lookup M cb cc cn cbase j2 j3 ->
    substitution_lookup M db dc dn dbase j3 v ->
    substitution_lookup M tb tc tn tbase i v) ->
  numerical_substitution M f tb tc tn tbase out.
Proof.
  intros HF H1 H2 H3 H4 HPoint.
  destruct (numerical_substitution_composition_total M f k ab ac an abase bb bc bn bbase f1 f2 HF H1 H2)
    as (p&q&HP&HEP).
  destruct (numerical_substitution_composition_total M f k p q k (zeroM M) cb cc cn cbase f2 f3 HF HP H3)
    as (r&s&HR&HER).
  destruct (numerical_substitution_composition_total M f k r s k (zeroM M) db dc dn dbase f3 out HF HR H4)
    as (u&v&HU&HEU).
  apply (numerical_prefix_substitution_compare M f k u v out tb tc tn tbase HF HU).
  intros i value HI HV.
  apply (proj1 (HEU i value HI)) in HV. destruct HV as (j3&HJ3&H4').
  apply (proj1 (HER i j3 HI)) in HJ3. destruct HJ3 as (j2&HJ2&H3').
  apply (proj1 (HEP i j2 HI)) in HJ2. destruct HJ2 as (j1&H1'&H2').
  exact (HPoint i j1 j2 j3 value HI H1' H2' H3' H4').
Qed.

Theorem numerical_two_renamings_two_substitutions_compare M f k
    ab ac an adelta bb bc bn bdelta cb cc cn cbase db dc dn dbase tb tc tn tbase f1 f2 f3 out :
  source_bounded M f k ->
  numerical_renaming M f ab ac an adelta f1 ->
  numerical_renaming M f1 bb bc bn bdelta f2 ->
  numerical_substitution M f2 cb cc cn cbase f3 ->
  numerical_substitution M f3 db dc dn dbase out ->
  (forall i j1 j2 j3 v,coding_lt M i k ->
    renaming_lookup M ab ac an adelta i j1 ->
    renaming_lookup M bb bc bn bdelta j1 j2 ->
    substitution_lookup M cb cc cn cbase j2 j3 ->
    substitution_lookup M db dc dn dbase j3 v ->
    substitution_lookup M tb tc tn tbase i v) ->
  numerical_substitution M f tb tc tn tbase out.
Proof.
  intros HF H1 H2 H3 H4 HP.
  apply (numerical_four_substitutions_compare M f k ab ac an (addM M an adelta)
    bb bc bn (addM M bn bdelta) cb cc cn cbase db dc dn dbase tb tc tn tbase f1 f2 f3 out HF
    (proj1 (numerical_renaming_substitution M f ab ac an adelta f1) H1)
    (proj1 (numerical_renaming_substitution M f1 bb bc bn bdelta f2) H2) H3 H4).
  intros i j1 j2 j3 v HI HA HB HC HD.
  exact (HP i j1 j2 j3 v HI
    (proj2 (renaming_substitution_lookup M ab ac an adelta i j1) HA)
    (proj2 (renaming_substitution_lookup M bb bc bn bdelta j1 j2) HB) HC HD).
Qed.

Print Assumptions numerical_two_renamings_two_substitutions_compare.
