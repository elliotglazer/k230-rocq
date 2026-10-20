(** A shifted universal assumption specializes at variable0 to its original
    matrix. All formula bounds, matrices and maps are internal PA codes. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalRenamingMaps NumericalRenaming NumericalContextRenaming SourceRenamingIdentity
  NumericalSubstitutionMaps NumericalSubstitution SubstitutionSource RenamingSubstitution NumericalInstantiation
  SourceBounded SetFormulaCodes SourceQuantifierRules SourceRenamingSquare.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma source_empty_renaming_lookup M i :
  renaming_lookup M (zeroM M) (zeroM M) (zeroM M) (zeroM M) i i.
Proof.
  apply (proj2 (renaming_lookup_outside M _ _ _ _ i i (coding_not_lt_zero M i))).
  symmetry. apply coding_add_zero_r.
Qed.
Lemma source_empty_substitution_lookup M i :
  substitution_lookup M (zeroM M) (zeroM M) (zeroM M) (zeroM M) i i.
Proof.
  pose proof (proj1 (renaming_substitution_lookup M (zeroM M) (zeroM M) (zeroM M)
    (zeroM M) i i) (source_empty_renaming_lookup M i)) as H.
  now rewrite Arithmetic.add_zero in H.
Qed.

Theorem source_lifted_shift_specialization M a k rb rc rn ar :
  source_bounded M a k ->
  renaming_lift M (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) rb rc rn ->
  numerical_renaming M a rb rc rn (succM M (zeroM M)) ar ->
  numerical_instantiation M ar (zeroM M) a.
Proof.
  intros HA HL HR.
  destruct (substitution_singleton_total M (zeroM M)) as (ub&uc&HU&_).
  assert (HI:numerical_renaming M a (zeroM M) (zeroM M) (zeroM M) (zeroM M) a).
  { apply (numerical_renaming_identity_on_bound M a _ _ _ _ k HA).
    intros i _. apply source_empty_renaming_lookup. }
  assert (HS:numerical_substitution M a (zeroM M) (zeroM M) (zeroM M) (zeroM M) a).
  { exact (proj1 (numerical_renaming_empty_substitution M a _ _ _ a) HI). }
  exists ub,uc. split;[exact HU|].
  apply (numerical_source_renaming_square M a k
    (zeroM M) (zeroM M) (zeroM M) (zeroM M)
    rb rc rn (succM M (zeroM M))
    (zeroM M) (zeroM M) (zeroM M) (zeroM M)
    ub uc (succM M (zeroM M)) (zeroM M) a ar a HA HS HR HI).
  intros i j l m Hbound HSub HId HMap.
  assert (EJ:j=i).
  { exact (substitution_lookup_functional M _ _ _ _ i j i HSub (source_empty_substitution_lookup M i)). }
  subst j.
  assert (EM:m=i).
  { exact (renaming_lookup_functional M _ _ _ _ i m i HId (source_empty_renaming_lookup M i)). }
  subst m.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[i' E]];subst i.
  - apply (proj1 (renaming_lift_head M _ _ _ _ rb rc rn l HL)) in HMap.
    subst l. exact HU.
  - destruct (renaming_lift_tail_inv M _ _ _ _ rb rc rn i' l HL HMap) as (v&HV&EL).
    apply context_shift_lookup in HV. subst v l.
    apply substitution_singleton_tail.
Qed.

Theorem source_shifted_all_specialization M a all shifted k :
  source_bounded M a k -> sf_relation M SFAll a (zeroM M) all ->
  source_formula_shift M all shifted ->
  exists ar,sf_relation M SFAll ar (zeroM M) shifted /\
    numerical_instantiation M ar (zeroM M) a.
Proof.
  intros HA HAll HS.
  apply (proj1 (numerical_renaming_quantifier M true a all (zeroM M) (zeroM M)
    (zeroM M) (succM M (zeroM M)) shifted HAll)) in HS.
  destruct HS as (rb&rc&rn&ar&HL&HR&HOut).
  exists ar. split;[exact HOut|].
  exact (source_lifted_shift_specialization M a k rb rc rn ar HA HL HR).
Qed.

Print Assumptions source_lifted_shift_specialization.
Print Assumptions source_shifted_all_specialization.
