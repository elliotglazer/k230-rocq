(** Actual RepC cancellation and two witness specializations. The same
    two-entry beta prefix supplies both input/output values; the different
    tail bases record exactly which two binders have been removed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SourceBounded NumericalRenamingMaps NumericalRenaming
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation RenamingSubstitution
  SchemaRenamingDescriptors SchemaRenamingBounds SourceSubstitutionComposition
  SourceRoleReopening SourceDoubleSpecialization.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_repc_prefix_cancellation M phi matrix b c result k :
  source_bounded M phi k ->schema_renaming M RepC phi matrix ->
  numerical_substitution M matrix b c (code_numeral M 2) (zeroM M) result ->
  numerical_substitution M phi b c (code_numeral M 2) (code_numeral M 2) result.
Proof.
  intros HB HR HS.
  pose proof (proj1 (numerical_renaming_substitution M phi (code_numeral M 4) (code_numeral M 1)
    (code_numeral M 2) (code_numeral M 2) matrix) HR) as HC.
  rewrite descriptor_numeral_add in HC.
  apply (numerical_substitution_composition M phi k (code_numeral M 4) (code_numeral M 1)
    (code_numeral M 2) (code_numeral M 4) b c (code_numeral M 2) (zeroM M)
    b c (code_numeral M 2) (code_numeral M 2) matrix result HB HC HS).
  intros i j v HI HCJ HJV.
  assert (HRI:schema_lookup M RepC i j).
  { unfold schema_lookup. apply (proj2 (renaming_substitution_lookup M (code_numeral M 4)
      (code_numeral M 1) (code_numeral M 2) (code_numeral M 2) i j)).
    rewrite descriptor_numeral_add. exact HCJ. }
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[idx E]];subst i.
  - apply (proj1 (schema_lookup_first M RepC j)) in HRI. subst j.
    apply (proj2 (substitution_lookup_inside M b c (code_numeral M 2) (code_numeral M 2)
      (zeroM M) v (coding_zero_lt_succ M (code_numeral M 1)))).
    exact (proj1 (substitution_lookup_inside M b c (code_numeral M 2) (zeroM M)
      (zeroM M) v (coding_zero_lt_succ M (code_numeral M 1))) HJV).
  - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) idx) as [E|[idx' E]];subst idx.
    + apply (proj1 (schema_lookup_second M RepC j)) in HRI. subst j.
      apply (proj2 (substitution_lookup_inside M b c (code_numeral M 2) (code_numeral M 2)
        (code_numeral M 1) v (coding_lt_succ M (code_numeral M 1)))).
      exact (proj1 (substitution_lookup_inside M b c (code_numeral M 2) (zeroM M)
        (code_numeral M 1) v (coding_lt_succ M (code_numeral M 1))) HJV).
    + assert (HOutside:~coding_lt M (succM M (succM M idx')) (code_numeral M 2)).
      { intro H. exact (coding_not_lt_zero M idx' (proj1 (coding_lt_succ_cancel M idx' (zeroM M))
          (proj1 (coding_lt_succ_cancel M (succM M idx') (code_numeral M 1)) H))). }
      apply (proj1 (schema_lookup_tail M RepC _ j HOutside)) in HRI.
      change (j=addM M (succM M (succM M idx')) (succM M (succM M (zeroM M)))) in HRI.
      rewrite Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_zero in HRI. subst j.
      pose proof (substitution_lookup_functional M b c (code_numeral M 2) (zeroM M)
        _ v (succM M (succM M idx')) HJV (source_role_reopening_tail M b c (succM M (succM M idx')))) as EV.
      subst v. right. split;[exact HOutside|]. exists idx'. split;
        change (succM M (succM M idx')=addM M (succM M (succM M (zeroM M))) idx');
        now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
Qed.

Theorem source_repc_double_specialization M phi matrix count d v ab ac ad ae am first result sb sc :
  source_bounded M phi (succM M (succM M count)) ->schema_renaming M RepC phi matrix ->
  substitution_lookup M ab ac (code_numeral M 1) (zeroM M) (zeroM M) d ->
  substitution_lift M ab ac (code_numeral M 1) (zeroM M) ad ae am ->
  numerical_substitution M matrix ad ae am (code_numeral M 1) first ->
  numerical_instantiation M first v result ->source_role_reopening M d v sb sc ->
  numerical_substitution M phi sb sc (code_numeral M 2) (code_numeral M 2) result.
Proof.
  intros HB HR HA HL HF (rb&rc&HOut&HSecond) HReopen.
  pose proof (schema_replacement_c_bound M phi matrix count HB HR) as HM.
  apply (source_repc_prefix_cancellation M phi matrix sb sc result (succM M (succM M count)) HB HR).
  apply (numerical_substitution_composition M matrix (succM M (succM M (succM M (succM M count))))
    ad ae am (code_numeral M 1) rb rc (code_numeral M 1) (zeroM M)
    sb sc (code_numeral M 2) (zeroM M) first result HM HF HSecond).
  exact (source_double_specialization_maps M d v ab ac ad ae am rb rc sb sc
    (succM M (succM M (succM M (succM M count)))) HA HL HOut HReopen).
Qed.

Print Assumptions source_repc_prefix_cancellation.
Print Assumptions source_repc_double_specialization.
