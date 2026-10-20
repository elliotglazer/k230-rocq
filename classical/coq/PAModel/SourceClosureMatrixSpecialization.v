(** Literal B/C matrix compatibility in emitted_closure. A fresh output
    witness0 specializes C to B, uniformly over arbitrary internal phi. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded SourceNativeKMatrixMaps SourceTraceMatrixAlignment NumericalRenamingMaps
  NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
  SourceSubstitutionComposition RenamingSubstitution SubstitutionSource SchemaRenamingDescriptors
  SourceRoleReopening SourceUpperWitnessRecipes SetSchemaConstructors.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_native_C_instantiates_B M phi k matC matB :
  source_bounded M phi k ->source_native_k_matrix M NativeKC phi matC ->
  source_native_k_matrix M NativeKB phi matB ->numerical_instantiation M matC (zeroM M) matB.
Proof.
  intros HP HC HB.
  destruct (numerical_instantiation_total M matC (zeroM M)) as [result [ib [ic [HZero HS]]]].
  assert (HR:source_native_k_matrix M NativeKB phi result).
  { apply (proj2 (numerical_renaming_substitution M phi (code_numeral M 4)
      (code_numeral M 1) (code_numeral M 2) (code_numeral M 4) result)).
    apply (numerical_substitution_composition M phi k
      (code_numeral M 2) (code_numeral M 1) (code_numeral M 2)
      (addM M (code_numeral M 2) (code_numeral M 5))
      ib ic (code_numeral M 1) (zeroM M)
      (code_numeral M 4) (code_numeral M 1) (code_numeral M 2)
      (addM M (code_numeral M 2) (code_numeral M 4)) matC result HP
      (proj1 (numerical_renaming_substitution M phi _ _ _ _ matC) HC) HS).
    intros i j v _ HFirst HSecond.
    apply (proj2 (renaming_substitution_lookup M (code_numeral M 2) (code_numeral M 1)
      (code_numeral M 2) (code_numeral M 5) i j)) in HFirst.
    apply (proj1 (renaming_substitution_lookup M (code_numeral M 4) (code_numeral M 1)
      (code_numeral M 2) (code_numeral M 4) i v)).
    destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i) as [->|[i' ->]].
    - pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HFirst
        (native_k_lookup_first M NativeKC)) as E. subst j.
      pose proof (substitution_lookup_functional M ib ic (code_numeral M 1) (zeroM M)
        (zeroM M) v (zeroM M) HSecond HZero) as E. subst v.
      exact (native_k_lookup_first M NativeKB).
    - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
        (fun ax H rho=>axioms M ax rho H) i') as [->|[i'' ->]].
      + pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HFirst
          (native_k_lookup_second M NativeKC)) as E. subst j.
        pose proof (substitution_lookup_functional M ib ic (code_numeral M 1) (zeroM M)
          (code_numeral M 2) v (code_numeral M 1) HSecond
          (substitution_singleton_tail M ib ic (code_numeral M 1))) as E. subst v.
        exact (native_k_lookup_second M NativeKB).
      + apply (proj1 (renaming_lookup_outside M _ _ _ _ _ _ (source_two_succ_not_lt_two M i''))) in HFirst.
        change (j=addM M (succM M (succM M i'')) (succM M (code_numeral M 4))) in HFirst.
        rewrite (Arithmetic.add_comm M (succM M (succM M i'')) (succM M (code_numeral M 4))),
          Arithmetic.add_succ,(Arithmetic.add_comm M (code_numeral M 4) (succM M (succM M i''))) in HFirst.
        subst j.
        pose proof (substitution_lookup_functional M ib ic (code_numeral M 1) (zeroM M)
          _ v _ HSecond (substitution_singleton_tail M ib ic
            (addM M (succM M (succM M i'')) (code_numeral M 4)))) as E. subst v.
        apply (proj2 (renaming_lookup_outside M _ _ _ _ _ _ (source_two_succ_not_lt_two M i''))). reflexivity. }
  pose proof (source_native_k_matrix_functional M NativeKB phi result matB HR HB) as E. subst result.
  now exists ib,ic.
Qed.

Theorem source_native_C_request_recipe M phi matC out :
  source_native_k_matrix M NativeKC phi matC ->
  code_relation M (schema_env3 matC (code_numeral M 4) (code_numeral M 4))
    (E_upper_matrix_request (CEvar 0) (CEvar 1)) out ->
  source_upper_matrix_request_recipe M phi (code_numeral M 6)
    (code_numeral M 1) (code_numeral M 4) out.
Proof.
  intros HM HO. exists (code_numeral M 2),(code_numeral M 1),matC.
  split.
  - split.
    + apply (proj2 (substitution_lookup_inside M _ _ (code_numeral M 2) (zeroM M)
        (zeroM M) (zeroM M) (coding_zero_lt_succ M (code_numeral M 1)))).
      apply (descriptor_beta_certificate M 2 1 0 0 1);reflexivity||lia.
    + apply (proj2 (substitution_lookup_inside M _ _ (code_numeral M 2) (zeroM M)
        (code_numeral M 1) (code_numeral M 2) (coding_lt_succ M (code_numeral M 1)))).
      apply (descriptor_beta_certificate M 2 1 1 2 0);reflexivity||lia.
  - split;[|exact HO].
    pose proof (proj1 (numerical_renaming_substitution M phi (code_numeral M 2)
      (code_numeral M 1) (code_numeral M 2) (code_numeral M 5) matC) HM) as H.
    rewrite descriptor_numeral_add in H. exact H.
Qed.

Print Assumptions source_native_C_instantiates_B.
Print Assumptions source_native_C_request_recipe.
