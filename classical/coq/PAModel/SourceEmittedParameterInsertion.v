(** Exact compatibility between a predicate's cutoff-two parameter
    insertion and the emitted closure's cutoff-one container-preserving shift. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetSchemaConstructors
  SourceBounded SourceNativeKMatrixMaps SourceEmittedClosureRecipe SourceNativeKShifts
  SourceNativeParameterInsertion SourceSkeletonCutoffShift SourceFiniteCutoffShift
  QuotationSchemaSkeleton NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming
  RenamingSubstitution SchemaRenamingDescriptors SourceShiftSpecialization SubstitutionSource.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_native_matrix_insert_commutes M s phi phi' matrix matrix' k :
  source_bounded M phi k ->source_cutoff_shift M 2 phi phi' ->
  source_native_k_matrix M s phi matrix ->source_native_k_matrix M s phi' matrix' ->
  source_cutoff_shift M (native_k_parameter_cutoff s) matrix matrix'.
Proof.
  intros HP HS HM HM'.
  destruct (source_cutoff_shift_total M (native_k_parameter_cutoff s) matrix) as [out HO].
  pose proof (source_native_matrix_insert_output M s phi matrix out k HP HM HO) as HR.
  pose proof (source_native_matrix_insert_input M s phi phi' matrix' k HP HS HM') as HR'.
  pose proof (numerical_renaming_functional M phi _ _ _ _ out matrix' HR HR') as E.
  now subst out.
Qed.

Definition emitted_closure_skeleton :source_skeleton :=
  SkeletonQuantifier true (SkeletonBinary SkeletonImpl (SkeletonAtom false 0 1)
    (SkeletonQuantifier false (SkeletonBinary SkeletonAnd (SkeletonHole 0)
      (SkeletonQuantifier true (SkeletonBinary SkeletonImpl
        (SkeletonQuantifier true (SkeletonBinary SkeletonImpl (SkeletonAtom false 0 1)(SkeletonAtom false 0 3)))
        (SkeletonQuantifier true (SkeletonBinary SkeletonImpl (SkeletonHole 1)
          (SkeletonQuantifier false (SkeletonBinary SkeletonAnd (SkeletonHole 2)(SkeletonAtom false 0 5)))))))))).

Theorem source_emitted_closure_insert_cutoff M phi phi' f g k :
  source_bounded M phi k ->source_cutoff_shift M 2 phi phi' ->
  source_emitted_closure_recipe M phi f ->source_emitted_closure_recipe M phi' g ->
  source_cutoff_shift M 1 f g.
Proof.
  intros HP HS (a&b&c&HA&HB&HC&HF)(a'&b'&c'&HA'&HB'&HC'&HG).
  apply (skeleton_source_cutoff_shift M emitted_closure_skeleton 1
    (schema_env3 a b c)(schema_env3 a' b' c') f g);[|exact HF|exact HG].
  cbn [emitted_closure_skeleton skeleton_cutoff_holes schema_env3].
  repeat split;try lia.
  - exact (source_native_matrix_insert_commutes M NativeKA phi phi' a a' k HP HS HA HA').
  - exact (source_native_matrix_insert_commutes M NativeKB phi phi' b b' k HP HS HB HB').
  - exact (source_native_matrix_insert_commutes M NativeKC phi phi' c c' k HP HS HC HC').
Qed.

Lemma source_native_k_upshift_cutoff_map M :
  source_cutoff_shift_map M 1 (zeroM M)(zeroM M)(code_numeral M 1).
Proof.
  exists (zeroM M),(zeroM M),(zeroM M). split;[repeat split;reflexivity|].
  split;[reflexivity|]. split.
  - apply (proj2 (substitution_lookup_inside M _ _ _ _ _ _ (coding_zero_lt_succ M (zeroM M)))).
    apply (descriptor_beta_certificate M 0 0 0 0 0);reflexivity||lia.
  - intros i v HV. pose proof (substitution_lookup_functional M (zeroM M)(zeroM M)(zeroM M)
      (code_numeral M 1) i v (succM M i) HV (source_cutoff_shift_base_lookup M i)) as E. subst v.
    right. split.
    + intro H. apply (proj1 (coding_lt_succ_cancel M i (zeroM M))) in H.
      exact (coding_not_lt_zero M i H).
    + exists i. split;cbn [code_numeral];now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
Qed.

Theorem source_cutoff_one_native_upshift M f g :
  source_cutoff_shift M 1 f g ->source_native_k_upshift M f g.
Proof.
  intros (b&c&n&HM&HS).
  apply (proj2 (numerical_renaming_substitution M f (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 1) g)).
  rewrite descriptor_numeral_add.
  exact (proj1 (numerical_substitution_extensional M f b c n (zeroM M)(zeroM M)(code_numeral M 1)
    (code_numeral M 2) g
    (source_cutoff_shift_maps_equivalent M 1 b c n (zeroM M)(zeroM M)(code_numeral M 1)
      HM (source_native_k_upshift_cutoff_map M))) HS).
Qed.

Theorem source_emitted_closure_parameter_insertion M phi phi' f g k :
  source_bounded M phi k ->source_cutoff_shift M 2 phi phi' ->
  source_emitted_closure_recipe M phi f ->source_emitted_closure_recipe M phi' g ->
  source_native_k_upshift M f g.
Proof.
  intros HP HS HF HG. apply source_cutoff_one_native_upshift.
  exact (source_emitted_closure_insert_cutoff M phi phi' f g k HP HS HF HG).
Qed.

Print Assumptions source_native_matrix_insert_commutes.
Print Assumptions source_emitted_closure_insert_cutoff.
Print Assumptions source_emitted_closure_parameter_insertion.
