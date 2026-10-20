(** Finite raw Collection clauses permit distinct names for the original
    profile binders and the later quotient-proof witnesses. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent FreshNames NumericalProofs NumericalEquivalence
  NamedSubstitution NamedSubstitutionRules NamedBinderFresh NamedAlpha TemplateNamedSubstitution
  NamedExistential NumericalVacuitySteps ProofTemplates RawCollectionProfile.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Lemma expression_replace_from_graphs M rho rho' old new e e' a b :
  code_relation M rho e a -> code_relation M rho' e' b -> named_replace M old new a b ->
  expression_named_replace M rho rho' old new e e'.
Proof.
  intros HA HB HR u v HU HV.
  assert (u=a) by exact (code_relation_functional M e rho u a HU HA).
  assert (v=b) by exact (code_relation_functional M e' rho' v b HV HB).
  now subst u v.
Qed.
Lemma expression_substitution_from_graphs M rho rho' old new e e' a b :
  code_relation M rho e a -> code_relation M rho' e' b -> named_substitution M a old new b ->
  expression_named_substitution M rho rho' old new e e'.
Proof.
  intros HA HB HR u v HU HV.
  assert (u=a) by exact (code_relation_functional M e rho u a HU HA).
  assert (v=b) by exact (code_relation_functional M e' rho' v b HV HB).
  now subst u v.
Qed.

Definition raw_clause_parameters M (t a c u v theta:carrier M) :=
  t .: a .: c .: u .: v .: theta .: fun _=>zeroM M.
Definition E_raw_support_clause :=
  E_raw_collection_support (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5).
Definition E_raw_coverage_clause :=
  E_raw_collection_coverage (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5).

Theorem raw_support_clause_outer_substitution M t a c u old new theta theta' body body' :
  old<>zeroM M -> t<>old -> a<>old -> c<>old -> u<>old -> u<>new ->
  named_substitution M theta old new theta' ->
  code_relation M (raw_clause_parameters M t a c u old theta) E_raw_support_clause body ->
  code_relation M (raw_clause_parameters M t a c u new theta') E_raw_support_clause body' ->
  named_substitution M body old new body'.
Proof.
  intros H0 HT HA HC HU HUN HTheta HB HB'.
  set (rho:=raw_clause_parameters M t a c u old theta).
  set (rho':=raw_clause_parameters M t a c u new theta').
  assert (R0 : expression_named_replace M rho rho' old new (CEvar 0) (CEvar 0)).
  { exact (expression_replace_from_graphs M rho rho' old new (CEvar 0) (CEvar 0) t t eq_refl eq_refl (or_intror (conj HT eq_refl))). }
  assert (R1 : expression_named_replace M rho rho' old new (CEvar 1) (CEvar 1)).
  { exact (expression_replace_from_graphs M rho rho' old new (CEvar 1) (CEvar 1) a a eq_refl eq_refl (or_intror (conj HA eq_refl))). }
  assert (R2 : expression_named_replace M rho rho' old new (CEvar 2) (CEvar 2)).
  { exact (expression_replace_from_graphs M rho rho' old new (CEvar 2) (CEvar 2) c c eq_refl eq_refl (or_intror (conj HC eq_refl))). }
  assert (R3 : expression_named_replace M rho rho' old new (CEvar 3) (CEvar 3)).
  { exact (expression_replace_from_graphs M rho rho' old new (CEvar 3) (CEvar 3) u u eq_refl eq_refl (or_intror (conj HU eq_refl))). }
  assert (R4 : expression_named_replace M rho rho' old new (CEvar 4) (CEvar 4)).
  { exact (expression_replace_from_graphs M rho rho' old new (CEvar 4) (CEvar 4) old new eq_refl eq_refl (or_introl (conj eq_refl eq_refl))). }
  assert (R5 : expression_named_substitution M rho rho' old new (CEvar 5) (CEvar 5)).
  { exact (expression_substitution_from_graphs M rho rho' old new (CEvar 5) (CEvar 5) theta theta' eq_refl eq_refl HTheta). }
  assert (HS : expression_named_substitution M rho rho' old new E_raw_support_clause E_raw_support_clause).
  { unfold E_raw_support_clause,E_raw_collection_support.
    apply expression_ns_implication.
    - apply expression_ns_conjunction;[exact H0| |].
      + exact (expression_ns_atom M rho rho' old new false _ _ _ _ R0 R4).
      + exact (expression_ns_atom M rho rho' old new false _ _ _ _ R4 R2).
    - apply (expression_ns_existential M rho rho' old new (CEvar 3) (CEvar 3) _ _ u H0 eq_refl eq_refl HU HUN).
      apply expression_ns_conjunction;[exact H0| |exact R5].
      apply expression_ns_conjunction;[exact H0| |].
      + exact (expression_ns_atom M rho rho' old new false _ _ _ _ R0 R3).
      + exact (expression_ns_atom M rho rho' old new false _ _ _ _ R3 R1). }
  exact (HS body body' HB HB').
Qed.

Theorem raw_coverage_clause_outer_substitution M t a c old new v theta theta' body body' :
  old<>zeroM M -> t<>old -> a<>old -> c<>old -> v<>old -> v<>new ->
  named_substitution M theta old new theta' ->
  code_relation M (raw_clause_parameters M t a c old v theta) E_raw_coverage_clause body ->
  code_relation M (raw_clause_parameters M t a c new v theta') E_raw_coverage_clause body' ->
  named_substitution M body old new body'.
Proof.
  intros H0 HT HA HC HV HVN HTheta HB HB'.
  set (rho:=raw_clause_parameters M t a c old v theta).
  set (rho':=raw_clause_parameters M t a c new v theta').
  assert (R0 : expression_named_replace M rho rho' old new (CEvar 0) (CEvar 0)).
  { exact (expression_replace_from_graphs M rho rho' old new (CEvar 0) (CEvar 0) t t eq_refl eq_refl (or_intror (conj HT eq_refl))). }
  assert (R1 : expression_named_replace M rho rho' old new (CEvar 1) (CEvar 1)).
  { exact (expression_replace_from_graphs M rho rho' old new (CEvar 1) (CEvar 1) a a eq_refl eq_refl (or_intror (conj HA eq_refl))). }
  assert (R2 : expression_named_replace M rho rho' old new (CEvar 2) (CEvar 2)).
  { exact (expression_replace_from_graphs M rho rho' old new (CEvar 2) (CEvar 2) c c eq_refl eq_refl (or_intror (conj HC eq_refl))). }
  assert (R3 : expression_named_replace M rho rho' old new (CEvar 3) (CEvar 3)).
  { exact (expression_replace_from_graphs M rho rho' old new (CEvar 3) (CEvar 3) old new eq_refl eq_refl (or_introl (conj eq_refl eq_refl))). }
  assert (R4 : expression_named_replace M rho rho' old new (CEvar 4) (CEvar 4)).
  { exact (expression_replace_from_graphs M rho rho' old new (CEvar 4) (CEvar 4) v v eq_refl eq_refl (or_intror (conj HV eq_refl))). }
  assert (R5 : expression_named_substitution M rho rho' old new (CEvar 5) (CEvar 5)).
  { exact (expression_substitution_from_graphs M rho rho' old new (CEvar 5) (CEvar 5) theta theta' eq_refl eq_refl HTheta). }
  assert (HS : expression_named_substitution M rho rho' old new E_raw_coverage_clause E_raw_coverage_clause).
  { unfold E_raw_coverage_clause,E_raw_collection_coverage.
    apply expression_ns_implication.
    - apply expression_ns_conjunction;[exact H0| |].
      + exact (expression_ns_atom M rho rho' old new false _ _ _ _ R0 R3).
      + exact (expression_ns_atom M rho rho' old new false _ _ _ _ R3 R1).
    - apply expression_ns_implication;
        apply (expression_ns_existential M rho rho' old new (CEvar 4) (CEvar 4) _ _ v H0 eq_refl eq_refl HV HVN);
        apply expression_ns_conjunction;[exact H0| |exact R5|exact H0| |].
      + exact (expression_ns_atom M rho rho' old new false _ _ _ _ R0 R4).
      + exact (expression_ns_atom M rho rho' old new false _ _ _ _ R0 R4).
      + apply expression_ns_conjunction;[exact H0| |exact R5].
        exact (expression_ns_atom M rho rho' old new false _ _ _ _ R4 R2). }
  exact (HS body body' HB HB').
Qed.

Theorem numerical_named_all_alpha_equivalence_checked M f x y g allf allg :
  x<>y -> named_binder_absent M f x -> formula_fresh M f y -> named_substitution M f x y g ->
  universal_graph M x f allf -> universal_graph M y g allg -> numerical_equivalent M allf allg.
Proof.
  intros HXY HA HF HS HEF HEG. split;intros result HR.
  - destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
      (allg .: allf .: fun _=>zeroM M)) as [back HB].
    exact (proj1 (numerical_named_alpha M f x y g allf allg result back HXY HA HF HS HEF HEG HR HB)).
  - destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
      (allf .: allg .: fun _=>zeroM M)) as [forward HFor].
    exact (proj2 (numerical_named_alpha M f x y g allf allg forward result HXY HA HF HS HEF HEG HFor HR)).
Qed.

Print Assumptions raw_support_clause_outer_substitution.
Print Assumptions raw_coverage_clause_outer_substitution.
Print Assumptions numerical_named_all_alpha_equivalence_checked.

Theorem raw_support_clause_outer_alpha M t a c u old new theta theta' body body' all all' :
  old<>zeroM M -> old<>new -> t<>old -> a<>old -> c<>old -> u<>old -> u<>new ->
  named_binder_absent M body old -> formula_fresh M body new ->
  named_substitution M theta old new theta' ->
  code_relation M (raw_clause_parameters M t a c u old theta) E_raw_support_clause body ->
  code_relation M (raw_clause_parameters M t a c u new theta') E_raw_support_clause body' ->
  universal_graph M old body all -> universal_graph M new body' all' -> numerical_equivalent M all all'.
Proof.
  intros H0 HOn HT HA HC HU HUN HB HF HS HG HG' HAll HAll'.
  exact (numerical_named_all_alpha_equivalence_checked M body old new body' all all'
    HOn HB HF (raw_support_clause_outer_substitution M t a c u old new theta theta' body body'
      H0 HT HA HC HU HUN HS HG HG') HAll HAll').
Qed.

Theorem raw_coverage_clause_outer_alpha M t a c old new v theta theta' body body' all all' :
  old<>zeroM M -> old<>new -> t<>old -> a<>old -> c<>old -> v<>old -> v<>new ->
  named_binder_absent M body old -> formula_fresh M body new ->
  named_substitution M theta old new theta' ->
  code_relation M (raw_clause_parameters M t a c old v theta) E_raw_coverage_clause body ->
  code_relation M (raw_clause_parameters M t a c new v theta') E_raw_coverage_clause body' ->
  universal_graph M old body all -> universal_graph M new body' all' -> numerical_equivalent M all all'.
Proof.
  intros H0 HOn HT HA HC HV HVN HB HF HS HG HG' HAll HAll'.
  exact (numerical_named_all_alpha_equivalence_checked M body old new body' all all'
    HOn HB HF (raw_coverage_clause_outer_substitution M t a c old new v theta theta' body body'
      H0 HT HA HC HV HVN HS HG HG') HAll HAll').
Qed.

Print Assumptions raw_support_clause_outer_alpha.
Print Assumptions raw_coverage_clause_outer_alpha.
