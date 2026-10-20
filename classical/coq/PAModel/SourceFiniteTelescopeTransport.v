(** Actual transport of a finite implication telescope. Formula holes,
    substitution tables and variable names remain arbitrary model elements. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  NumericalSubstitution NumericalRenaming SourceFiniteTelescope.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem source_finite_telescope_substitution M A B target target' out out' rb rc rn base:
  Forall2(fun a b=>numerical_substitution M a rb rc rn base b)A B ->
  numerical_substitution M target rb rc rn base target' ->
  source_finite_telescope M A target out ->source_finite_telescope M B target' out' ->
  numerical_substitution M out rb rc rn base out'.
Proof.
  intro H. revert target target' out out'. induction H as[|a b A B HAB HRest IH];
    intros target target' out out' HT HO HN.
  - change(out=target)in HO. change(out'=target')in HN. now subst out out'.
  - destruct HO as(inner&HInner&HOut),HN as(inner'&HInner'&HOut').
    apply(proj2(numerical_substitution_binary M SFImpl a inner out rb rc rn base out'
      (or_intror(or_intror eq_refl))HOut)).
    exists b,inner'. split;[exact HAB|]. split;[exact(IH target target' inner inner' HT HInner HInner')|exact HOut'].
Qed.

Theorem source_finite_telescope_renaming M A B target target' out out' rb rc rn delta:
  Forall2(fun a b=>numerical_renaming M a rb rc rn delta b)A B ->
  numerical_renaming M target rb rc rn delta target' ->
  source_finite_telescope M A target out ->source_finite_telescope M B target' out' ->
  numerical_renaming M out rb rc rn delta out'.
Proof.
  intro H. revert target target' out out'. induction H as[|a b A B HAB HRest IH];
    intros target target' out out' HT HO HN.
  - change(out=target)in HO. change(out'=target')in HN. now subst out out'.
  - destruct HO as(inner&HInner&HOut),HN as(inner'&HInner'&HOut').
    apply(proj2(numerical_renaming_binary M SFImpl a inner out rb rc rn delta out'
      (or_intror(or_intror eq_refl))HOut)).
    exists b,inner'. split;[exact HAB|]. split;[exact(IH target target' inner inner' HT HInner HInner')|exact HOut'].
Qed.
Print Assumptions source_finite_telescope_substitution.
Print Assumptions source_finite_telescope_renaming.
