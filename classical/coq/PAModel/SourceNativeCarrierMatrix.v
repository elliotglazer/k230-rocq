(** The native witness matrix is invariant under the twice-lifted fresh
 carrier transposition. The statement acts on arbitrary internal codes. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceFiniteCutoffShift SourceNativeWitnessMatrixAlignment SourceWitnessThetaInstances SourceWitnessThetaMatrixActions
 SourceZeroTransposition SourceShiftSpecialization SourceCarrierRenaming SourceRenamingDiamond SourceRenamingBounds SourceRenamingWellformedness
 NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution RenamingSubstitution.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Lemma source_native_matrix_tail_base M:addM M(code_numeral M 2)(code_numeral M 2)=code_numeral M 4.
Proof. cbn[code_numeral]. repeat rewrite Arithmetic.add_succ. rewrite Arithmetic.add_zero. reflexivity. Qed.
Theorem source_native_matrix_original_renaming M phi shifted matrix k:
 source_bounded M phi k->source_cutoff_shift M 2 phi shifted->
 numerical_renaming M shifted(code_numeral M 4)(code_numeral M 1)(code_numeral M 2)(code_numeral M 1)matrix->
 exists rb rc,source_witness_matrix_map M(zeroM M)(code_numeral M 3)rb rc /\
 numerical_renaming M phi rb rc(code_numeral M 2)(code_numeral M 2)matrix.
Proof.
 intros BP HCut HNative.
 destruct(witness_finite_substitution_total M 2(witness_matrix_names M(zeroM M))(code_numeral M 4))as(rb&rc&HMap).
 destruct(numerical_substitution_total M phi rb rc(code_numeral M 2)(code_numeral M 4))as(actual&HActual).
 pose proof(source_native_witness_matrix_alignment M phi shifted matrix rb rc actual k BP HCut HNative HMap HActual)as E;subst actual.
 exists rb,rc. split;[exact HMap|]. apply(proj2(numerical_renaming_substitution M phi rb rc(code_numeral M 2)(code_numeral M 2)matrix)).
 rewrite source_native_matrix_tail_base. exact HActual.
Qed.
Theorem source_native_witness_matrix_carrier_fixed M phi shifted matrix k fresh b c r1 r2 n1 s1 s2 n2:
 source_bounded M phi k->coding_lt M k fresh->source_cutoff_shift M 2 phi shifted->
 numerical_renaming M shifted(code_numeral M 4)(code_numeral M 1)(code_numeral M 2)(code_numeral M 1)matrix->
 source_zero_transposition M fresh b c->
 renaming_lift M b c(succM M fresh)(zeroM M)r1 r2 n1->renaming_lift M r1 r2 n1(zeroM M)s1 s2 n2->
 numerical_renaming M matrix s1 s2 n2(zeroM M)matrix.
Proof.
 intros BP HK HCut HNative HTrans HL1 HL2.
 destruct(source_native_matrix_original_renaming M phi shifted matrix k BP HCut HNative)as(rb&rc&HMap&HMatrix).
 destruct(source_renaming_range_bound M rb rc(code_numeral M 2)(code_numeral M 2)k)as(km&HRange).
 pose proof(numerical_renaming_preserves_bound M phi rb rc(code_numeral M 2)(code_numeral M 2)matrix k km BP HMatrix HRange)as BM.
 apply(numerical_source_renaming_diamond M phi k rb rc(code_numeral M 2)(code_numeral M 2)
  rb rc(code_numeral M 2)(code_numeral M 2)(zeroM M)(zeroM M)(zeroM M)(zeroM M)
  s1 s2 n2(zeroM M)matrix matrix matrix BP HMatrix HMatrix(source_valid_identity M matrix km BM)).
 intros i j l m HI HJ HM HL.
 pose proof(renaming_lookup_functional M rb rc(code_numeral M 2)(code_numeral M 2)i j l HJ HL)as E;subst l.
 pose proof(renaming_lookup_functional M(zeroM M)(zeroM M)(zeroM M)(zeroM M)j m j HM(source_empty_renaming_lookup M j))as E;subst m.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[i' ->]].
 - assert(HHead:renaming_lookup M rb rc(code_numeral M 2)(code_numeral M 2)(zeroM M)(zeroM M)).
   { apply(proj2(renaming_substitution_lookup M rb rc(code_numeral M 2)(code_numeral M 2)(zeroM M)(zeroM M))).
     rewrite source_native_matrix_tail_base. exact(HMap 0 ltac:(lia)). }
   pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HJ HHead)as E;subst j. exact(proj1(proj2 HL2)).
 - destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i')as[->|[q ->]].
   + assert(HHead:renaming_lookup M rb rc(code_numeral M 2)(code_numeral M 2)(code_numeral M 1)(code_numeral M 1)).
     { apply(proj2(renaming_substitution_lookup M rb rc(code_numeral M 2)(code_numeral M 2)(code_numeral M 1)(code_numeral M 1))).
       rewrite source_native_matrix_tail_base. exact(HMap 1 ltac:(lia)). }
     pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HJ HHead)as E;subst j.
     exact(proj2(proj2 HL2)(zeroM M)(zeroM M)(proj1(proj2 HL1))).
   + apply renaming_lookup_outside in HJ;[|apply SourceTraceMatrixAlignment.source_two_succ_not_lt_two].
     subst j. change(renaming_lookup M s1 s2 n2(zeroM M)
      (addM M(succM M(succM M q))(code_numeral M 2))(addM M(succM M(succM M q))(code_numeral M 2))).
     assert(E:addM M(succM M(succM M q))(code_numeral M 2)=succM M(succM M(succM M(succM M q)))).
     { rewrite Arithmetic.add_comm. cbn[code_numeral]. repeat rewrite Arithmetic.add_succ. rewrite Arithmetic.add_zero. reflexivity. }
     rewrite E. apply(proj2(proj2 HL2)). apply(proj2(proj2 HL1)).
     apply(source_zero_transposition_other M fresh b c(succM M(succM M q))HTrans).
     * intro E0. pose proof(coding_zero_lt_succ M(succM M q))as HPos. rewrite E0 in HPos. exact(coding_not_lt_zero M(zeroM M)HPos).
     * intro E0. exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)
        (succM M(succM M q))fresh(coding_lt_trans M _ k fresh HI HK)E0).
Qed.
Print Assumptions source_native_matrix_original_renaming.
Print Assumptions source_native_witness_matrix_carrier_fixed.
