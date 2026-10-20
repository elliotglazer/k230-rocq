(** A commuting diamond of actual internal renamings.  Its proof reuses
    the checked renaming/substitution square; no standard-formula induction
    or syntactic representation assumption is involved. *)
From PAModel Require Import Model Arithmetic FiniteCoding NumericalRenamingMaps NumericalRenaming
  NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution SourceBounded SourceRenamingSquare.
Unset Implicit Arguments.

Theorem numerical_source_renaming_diamond M f k
    sb sc sn sdelta rb rc rn rdelta tb tc tn tdelta ub uc un udelta fs fr v :
  source_bounded M f k -> numerical_renaming M f sb sc sn sdelta fs ->
  numerical_renaming M f rb rc rn rdelta fr ->
  numerical_renaming M fs tb tc tn tdelta v ->
  (forall i j l m,coding_lt M i k ->
    renaming_lookup M sb sc sn sdelta i j ->
    renaming_lookup M tb tc tn tdelta j m ->
    renaming_lookup M rb rc rn rdelta i l ->
    renaming_lookup M ub uc un udelta l m) ->
  numerical_renaming M fr ub uc un udelta v.
Proof.
  intros HF HS HR HT HD.
  apply (proj2 (numerical_renaming_substitution M fr ub uc un udelta v)).
  apply (numerical_source_renaming_square M f k
    sb sc sn (addM M sn sdelta) rb rc rn rdelta tb tc tn tdelta
    ub uc un (addM M un udelta) fs fr v HF
    (proj1 (numerical_renaming_substitution M f sb sc sn sdelta fs) HS) HR HT).
  intros i j l m HI HSI HTJ HRI.
  apply (proj1 (renaming_substitution_lookup M ub uc un udelta l m)).
  exact (HD i j l m HI (proj2 (renaming_substitution_lookup M sb sc sn sdelta i j) HSI) HTJ HRI).
Qed.

Print Assumptions numerical_source_renaming_diamond.
