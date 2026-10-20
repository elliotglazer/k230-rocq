(** The reflected request matrix is literally the native witness matrix.
 C2 inserts one protected-tail slot; the native identity-prefix renaming
 inserts the second. This is actual arbitrary-code substitution composition. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceFiniteCutoffShift SourceTraceMatrixAlignment SourceWitnessMatrixSpecialization SourceWitnessThetaInstances
 SourceWitnessThetaMatrixActions SourceSubstitutionComposition NumericalSubstitutionMaps NumericalSubstitution
 NumericalRenamingMaps NumericalRenaming RenamingSubstitution.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Theorem source_native_witness_matrix_alignment M phi shifted native rb rc matrix k:
 source_bounded M phi k->source_cutoff_shift M 2 phi shifted->
 numerical_renaming M shifted(code_numeral M 4)(code_numeral M 1)(code_numeral M 2)(code_numeral M 1)native->
 source_witness_matrix_map M(zeroM M)(code_numeral M 3)rb rc->
 numerical_substitution M phi rb rc(code_numeral M 2)(code_numeral M 4)matrix->native=matrix.
Proof.
 intros BP(ab&ac&an&HMap&HFirst)HSecond HTarget HMatrix.
 assert(HNative:numerical_substitution M phi rb rc(code_numeral M 2)(code_numeral M 4)native).
 { apply(numerical_substitution_composition M phi k ab ac an(code_numeral M 3)
    (code_numeral M 4)(code_numeral M 1)(code_numeral M 2)
    (addM M(code_numeral M 2)(code_numeral M 1))
    rb rc(code_numeral M 2)(code_numeral M 4)shifted native BP HFirst
    (proj1(numerical_renaming_substitution M shifted _ _ _ _ native)HSecond)).
   intros i j v HI HA HV. apply(proj2(renaming_substitution_lookup M(code_numeral M 4)(code_numeral M 1)
    (code_numeral M 2)(code_numeral M 1)j v))in HV.
   destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[i' ->]].
   - pose proof(substitution_lookup_functional M ab ac an(code_numeral M 3)(zeroM M)j(zeroM M)HA
      (source_cutoff_shift_map_fixed_lookup M 2 ab ac an HMap 0))as E;subst j.
     pose proof(renaming_lookup_functional M _ _ _ _ _ v _ HV(proj1(source_identity_delta_prefix M(code_numeral M 1))))as E;subst v.
     exact(HTarget 0 ltac:(auto)).
   - destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i')as[->|[i'' ->]].
     + pose proof(substitution_lookup_functional M ab ac an(code_numeral M 3)(code_numeral M 1)j(code_numeral M 1)HA
        (source_cutoff_shift_map_fixed_lookup M 2 ab ac an HMap 1))as E;subst j.
       pose proof(renaming_lookup_functional M _ _ _ _ _ v _ HV(proj2(source_identity_delta_prefix M(code_numeral M 1))))as E;subst v.
       exact(HTarget 1 ltac:(auto)).
     + pose proof(substitution_lookup_functional M ab ac an(code_numeral M 3)_ j _ HA
        (source_cutoff_shift_map_tail M 2 ab ac an i'' HMap))as E;subst j.
       apply renaming_lookup_outside in HV;[|apply source_two_succ_not_lt_two].
       cbn[source_succ_iter]in HV. subst v.
       replace(addM M(succM M(succM M(succM M i'')))(code_numeral M 1))with(addM M(code_numeral M 4)i'').
       * exact(witness_substitution_tail M rb rc 2(code_numeral M 4)i'').
       * cbn[code_numeral]. repeat rewrite Arithmetic.add_succ. repeat rewrite Arithmetic.add_zero.
         rewrite Arithmetic.add_comm. repeat rewrite Arithmetic.add_succ. repeat rewrite Arithmetic.add_zero. reflexivity. }
 exact(numerical_substitution_functional M phi rb rc(code_numeral M 2)(code_numeral M 4)native matrix HNative HMatrix).
Qed.
Print Assumptions source_native_witness_matrix_alignment.
