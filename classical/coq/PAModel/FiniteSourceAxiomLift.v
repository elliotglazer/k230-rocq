(** Lift fixed external source axiom instances to arbitrary PA models.
    This calibrates finite library proof contexts. It does not replace the
    uniform arithmetic construction of nonstandard axiom instances. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  SetFormulaCodes SetSchemaConstructors SourceBounded FixedSourceBounds SourceNumeralLift
  SchemaRenamingDescriptors SchemaRenamingCalibration NumericalRenamingMaps
  NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
  RenamingSubstitution SubstitutionSource NumericalSetClosure NumericalZFCAxioms
  NumericalZFCCalibration NumericalZFCExactness NumericalCoreAxioms
  ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes.
From Undecidability.FOL Require Import Syntax.Facts Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lists.List Lia.
Unset Implicit Arguments.

Lemma finite_schema_lookup M s i :
  schema_lookup M s (code_numeral M i) (code_numeral M (sf_index (schema_substitution s i))).
Proof.
  destruct i as [|[|i]].
  - apply schema_lookup_first. destruct s;reflexivity.
  - apply schema_lookup_second. destruct s;reflexivity.
  - apply schema_lookup_tail.
    + intro H. apply (proj1 (fixed_source_numeral_lt_iff M (S(S i)) (schema_length s))) in H.
      destruct s;cbn in H;lia.
    + rewrite descriptor_numeral_add. f_equal. destruct s;cbn;lia.
Qed.

Theorem finite_schema_renaming M s (phi:sf_form) :
  schema_renaming M s (code_numeral M (sf_encode phi))
    (code_numeral M (sf_encode phi[schema_substitution s])).
Proof.
  unfold schema_renaming.
  apply (proj2 (numerical_renaming_substitution_uniform M _ _ _ _ _ _)).
  apply (fixed_source_substitution M (fun _=>zeroM M) phi (schema_substitution s)).
  - intro i. apply (proj1 (renaming_substitution_lookup M _ _ _ _ _ _)).
    exact (finite_schema_lookup M s i).
  - apply source_formula_numeral_graph.
  - apply source_formula_numeral_graph.
Qed.

Theorem finite_all_prefix M n (phi:sf_form) :
  all_prefix M (code_numeral M n) (code_numeral M (sf_encode phi))
    (code_numeral M (sf_encode (forall_times n phi))).
Proof.
  rewrite <- source_all_prefix_forall_times. induction n as [|n IH].
  - apply all_prefix_zero. reflexivity.
  - apply all_prefix_succ. exists (code_numeral M (sf_encode (source_all_prefix n phi))).
    split;[exact IH|]. exact (sf_make_numeral M SFAll (sf_encode (source_all_prefix n phi)) 0).
Qed.

Lemma finite_separation_constructor M (phi:sf_form) :
  sf_separation_constructor M (code_numeral M (sf_encode (source_sep_body phi)))
    (code_numeral M (sf_encode (ax_sep' phi))).
Proof.
  unfold sf_separation_constructor. rewrite sf_separation_source_calibration.
  exact (code_relation_numeral M (fun _=>sf_encode (source_sep_body phi)) _).
Qed.

Lemma finite_replacement_constructor M (phi:sf_form) :
  sf_replacement_constructor M (code_numeral M (sf_encode (source_rep_body_A phi)))
    (code_numeral M (sf_encode (source_rep_body_B phi)))
    (code_numeral M (sf_encode (source_rep_body_C phi)))
    (code_numeral M (sf_encode (ax_rep' phi))).
Proof.
  unfold sf_replacement_constructor. rewrite sf_replacement_source_calibration.
  apply (proj2 (code_relation_ext M _
    (schema_env3 (code_numeral M (sf_encode (source_rep_body_A phi)))
      (code_numeral M (sf_encode (source_rep_body_B phi)))
      (code_numeral M (sf_encode (source_rep_body_C phi))))
    (fun i=>code_numeral M (schema_env3 (sf_encode (source_rep_body_A phi))
      (sf_encode (source_rep_body_B phi)) (sf_encode (source_rep_body_C phi)) i)) _
    ltac:(intros [|[|i]];reflexivity))).
  apply code_relation_numeral.
Qed.

Theorem finite_separation_instance M (phi:sf_form) n :
  bounded (S n) phi -> numerical_separation_instance M (code_numeral M (sf_encode phi))
    (code_numeral M n) (code_numeral M (sf_encode (forall_times n (ax_sep' phi)))).
Proof.
  intro HB. split;[exact (proj2 (source_formula_numeral_bounded M phi (S n)) HB)|].
  exists (code_numeral M (sf_encode (source_sep_body phi))),
    (code_numeral M (sf_encode (ax_sep' phi))).
  split;[exact (finite_schema_renaming M SepBody phi)|].
  split;[apply finite_separation_constructor|apply finite_all_prefix].
Qed.

Theorem finite_replacement_instance M (phi:sf_form) n :
  bounded (S(S n)) phi -> numerical_replacement_instance M (code_numeral M (sf_encode phi))
    (code_numeral M n) (code_numeral M (sf_encode (forall_times n (ax_rep' phi)))).
Proof.
  intro HB. split;[exact (proj2 (source_formula_numeral_bounded M phi (S(S n))) HB)|].
  exists (code_numeral M (sf_encode (source_rep_body_A phi))),
    (code_numeral M (sf_encode (source_rep_body_B phi))),
    (code_numeral M (sf_encode (source_rep_body_C phi))),
    (code_numeral M (sf_encode (ax_rep' phi))).
  split;[exact (finite_schema_renaming M RepA phi)|].
  split;[exact (finite_schema_renaming M RepB phi)|].
  split;[exact (finite_schema_renaming M RepC phi)|].
  split;[apply finite_replacement_constructor|apply finite_all_prefix].
Qed.

Theorem finite_core_axiom_lift M (psi:sf_form) :
  standard_zfc_core_source_axiom psi ->
  numerical_zfc_core_source_axiom M (code_numeral M (sf_encode psi)).
Proof.
  intros [HFixed|[HSep|HRep]].
  - destruct (proj2 (standard_zfc_core_fixed_iff psi) HFixed) as [tag [HT ->]].
    left. exists tag. split;[exact HT|apply source_formula_numeral_graph].
  - destruct HSep as [phi [n [-> HC]]]. right;left. split.
    + exact (proj2 (source_formula_numeral_bounded M _ 0) HC).
    + exists (code_numeral M (sf_encode phi)),(code_numeral M n).
      apply finite_separation_instance,source_separation_bound_inv.
      exact (standard_prefix_bound_inv n (ax_sep' phi) HC).
  - destruct HRep as [phi [n [-> HC]]]. right;right. split.
    + exact (proj2 (source_formula_numeral_bounded M _ 0) HC).
    + exists (code_numeral M (sf_encode phi)),(code_numeral M n).
      apply finite_replacement_instance,source_replacement_bound_inv.
      exact (standard_prefix_bound_inv n (ax_rep' phi) HC).
Qed.

Print Assumptions finite_schema_renaming.
Print Assumptions finite_all_prefix.
Print Assumptions finite_separation_instance.
Print Assumptions finite_replacement_instance.
Print Assumptions finite_core_axiom_lift.
