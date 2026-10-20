(** Exact short-prefix action of three cutoff-one insertions. This
    supplies the noncontiguous ordinary-Refl assignment used by L Separation. *)
From PAModel Require Import SourceCutoffShiftCommutation Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps RenamingSubstitution SourceSubstitutionComposition
 SourceFiniteCutoffShift SourceD0Recipe SchemaRenamingDescriptors SourceLSeparationMatrixShift.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Lemma source_lsep_matrix_lookup_zero M:
 substitution_lookup M(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 4)(zeroM M)(zeroM M).
Proof.
 left. split;[apply coding_zero_lt_succ|]. exact(schema_beta_first M SepBody).
Qed.
Lemma source_lsep_matrix_lookup_succ M i:
 substitution_lookup M(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 4)(succM M i)
  (succM M(succM M(succM M(succM M i)))).
Proof.
 right. split.
 - intro H. exact(coding_not_lt_zero M i(proj1(coding_lt_succ_cancel M i(zeroM M))H)).
 - exists i. split.
   + change(succM M i=addM M(succM M(zeroM M))i).
     rewrite Arithmetic.add_succ,Arithmetic.add_zero. reflexivity.
   + change(succM M(succM M(succM M(succM M i)))=
      addM M(succM M(succM M(succM M(succM M(zeroM M)))))i).
     rewrite !Arithmetic.add_succ,Arithmetic.add_zero. reflexivity.
Qed.
Theorem source_lsep_matrix_substitution M phi matrix bound:
 source_bounded M phi bound ->source_cutoff_shift_thrice M phi matrix ->
 numerical_substitution M phi(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 4)matrix.
Proof.
 intros HB(first&second&H1&H2&rb&rc&rn&HMap&H3).
 pose proof(source_cutoff_twice_is_SepBody M phi first second bound HB H1 H2)as HSep.
 assert(HS:numerical_substitution M phi(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 3)second).
 { apply(proj1(numerical_renaming_substitution M phi(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 2)second))in HSep.
   rewrite descriptor_numeral_add in HSep. exact HSep. }
 apply(numerical_substitution_composition M phi bound(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 3)
  rb rc rn(code_numeral M 2)(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 4)second matrix HB HS H3).
 intros i j v _ HJ HV.
 assert(HJ':schema_lookup M SepBody i j).
 { apply(proj2(renaming_substitution_lookup M(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 2)i j)).
   rewrite descriptor_numeral_add. exact HJ. }
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[E|[idx E]];subst i.
 - apply(proj1(schema_lookup_first M SepBody j))in HJ'. subst j.
   assert(E:v=zeroM M)by(exact(substitution_lookup_functional M rb rc rn(code_numeral M 2)(zeroM M)v(zeroM M)HV
    (source_cutoff_shift_map_fixed_lookup M 1 rb rc rn HMap 0))). subst v. apply source_lsep_matrix_lookup_zero.
 - apply(proj1(schema_lookup_tail M SepBody(succM M idx)j
    ltac:(intro H;exact(coding_not_lt_zero M idx(proj1(coding_lt_succ_cancel M idx(zeroM M))H)))))in HJ'.
   assert(E:j=succM M(succM M(succM M idx))).
   { rewrite HJ',Arithmetic.add_comm. change(addM M(succM M(succM M(zeroM M)))(succM M idx)=succM M(succM M(succM M idx))).
     rewrite !Arithmetic.add_succ,Arithmetic.add_zero. reflexivity. } subst j. rewrite E in HV.
   assert(EV:v=succM M(succM M(succM M(succM M idx)))).
   { exact(substitution_lookup_functional M rb rc rn(code_numeral M 2)(succM M(succM M(succM M idx)))v
      (succM M(succM M(succM M(succM M idx))))HV
      (source_cutoff_shift_map_tail_lookup M 1 rb rc rn(succM M(succM M idx))HMap)). } subst v.
   apply source_lsep_matrix_lookup_succ.
Qed.
Print Assumptions source_lsep_matrix_substitution.
