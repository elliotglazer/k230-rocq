(** Specializing witness_closed at input p preserves the output binder
    and realizes the exact matrix_request substitution phi[0,p+1,tail+1]. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SourceBounded NumericalRenaming NumericalRenamingMaps NumericalSubstitutionMaps
  NumericalSubstitution SourceSubstitutionComposition RenamingSubstitution
  SourceRoleReopening SourceTraceValueAlignment SourceTraceMatrixAlignment
  SchemaRenamingDescriptors.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma source_identity_delta_prefix M delta :
  renaming_lookup M (code_numeral M 4) (code_numeral M 1) (code_numeral M 2) delta
    (zeroM M) (zeroM M) /\
  renaming_lookup M (code_numeral M 4) (code_numeral M 1) (code_numeral M 2) delta
    (code_numeral M 1) (code_numeral M 1).
Proof.
  split.
  - apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_zero_lt_succ M (code_numeral M 1)))).
    apply (descriptor_beta_certificate M 4 1 0 0 2);reflexivity||lia.
  - apply (proj2 (renaming_lookup_inside M _ _ _ _ _ _ (coding_lt_succ M (code_numeral M 1)))).
    apply (descriptor_beta_certificate M 4 1 1 1 1);reflexivity||lia.
Qed.

Theorem source_witness_matrix_specialization M phi mat p k delta sb sc ad ae am rb rc out :
  source_bounded M phi k ->
  numerical_renaming M phi (code_numeral M 4) (code_numeral M 1) (code_numeral M 2) delta mat ->
  substitution_lookup M sb sc (code_numeral M 1) (zeroM M) (zeroM M) p ->
  substitution_lift M sb sc (code_numeral M 1) (zeroM M) ad ae am ->
  numerical_substitution M mat ad ae am (code_numeral M 1) out ->
  source_role_reopening M (succM M p) (zeroM M) rb rc ->
  numerical_substitution M phi rb rc (code_numeral M 2) (succM M delta) out.
Proof.
  intros HP HM HInput HL HMat [HZero HOne].
  apply (numerical_substitution_composition M phi k
    (code_numeral M 4) (code_numeral M 1) (code_numeral M 2)
    (addM M (code_numeral M 2) delta) ad ae am (code_numeral M 1)
    rb rc (code_numeral M 2) (succM M delta) mat out HP
    (proj1 (numerical_renaming_substitution M phi _ _ _ _ mat) HM) HMat).
  intros i j v _ HFirst HSecond.
  apply (proj2 (renaming_substitution_lookup M (code_numeral M 4) (code_numeral M 1)
    (code_numeral M 2) delta i j)) in HFirst.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[i' ->]].
  - pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HFirst
      (proj1 (source_identity_delta_prefix M delta))) as E. subst j.
    apply (proj1 (substitution_lift_head M sb sc (code_numeral M 1) (zeroM M)
      ad ae am v HL)) in HSecond. subst v.
    exact (source_two_prefix_change_base M rb rc (zeroM M) (zeroM M) (succM M delta)
      (coding_zero_lt_succ M (code_numeral M 1)) HZero).
  - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i') as [->|[i'' ->]].
    + pose proof (renaming_lookup_functional M _ _ _ _ _ j _ HFirst
        (proj2 (source_identity_delta_prefix M delta))) as E. subst j.
      pose proof (substitution_lookup_functional M ad ae am (code_numeral M 1)
        (code_numeral M 1) v (succM M p) HSecond
        (proj2 (substitution_lift_tail M sb sc (code_numeral M 1) (zeroM M)
          ad ae am (zeroM M) p HL) HInput)) as E. subst v.
      exact (source_two_prefix_change_base M rb rc (code_numeral M 1) (succM M p) (succM M delta)
        (coding_lt_succ M (code_numeral M 1)) HOne).
    + apply (proj1 (renaming_lookup_outside M _ _ _ _ _ _
        (source_two_succ_not_lt_two M i''))) in HFirst.
      rewrite !Arithmetic.add_succ in HFirst. subst j.
      assert (HAct:substitution_lookup M ad ae am (code_numeral M 1)
        (succM M (succM M (addM M i'' delta))) (succM M (addM M i'' delta))).
      { apply (proj2 (substitution_lift_tail M sb sc (code_numeral M 1) (zeroM M)
          ad ae am (succM M (addM M i'' delta)) (addM M i'' delta) HL)).
        apply SubstitutionSource.substitution_singleton_tail. }
      pose proof (substitution_lookup_functional M ad ae am (code_numeral M 1)
        _ v _ HSecond HAct) as E. subst v.
      right. split;[exact (source_two_succ_not_lt_two M i'')|].
      exists i''. split.
      * cbn [code_numeral]. now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
      * rewrite Arithmetic.add_succ,Arithmetic.add_comm. reflexivity.
Qed.

Print Assumptions source_identity_delta_prefix.
Print Assumptions source_witness_matrix_specialization.
