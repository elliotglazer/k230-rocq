(** Different beta representations of the same two-entry request map
    produce the identical formula code. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution SourceRoleReopening SourceTraceValueAlignment
  SourceTraceMatrixAlignment SourceUpperWitnessRecipes SourceWitnessClosedUse NumericalSourceFull.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_role_reopening_base_equivalent M a b rb rc sb sc base :
  source_role_reopening M a b rb rc ->source_role_reopening M a b sb sc ->
  substitution_equivalent M rb rc (code_numeral M 2) sb sc (code_numeral M 2) base.
Proof.
  intros [HR0 HR1] [HS0 HS1] i v.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[i' ->]].
  - pose proof (source_two_prefix_change_base M rb rc (zeroM M) b base
      (coding_zero_lt_succ M (code_numeral M 1)) HR0) as HR.
    pose proof (source_two_prefix_change_base M sb sc (zeroM M) b base
      (coding_zero_lt_succ M (code_numeral M 1)) HS0) as HS.
    split;intro H;pose proof (substitution_lookup_functional M _ _ _ _ _ v b H ltac:(eassumption)) as E;
      subst v;assumption.
  - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i') as [->|[i'' ->]].
    + pose proof (source_two_prefix_change_base M rb rc (code_numeral M 1) a base
        (coding_lt_succ M (code_numeral M 1)) HR1) as HR.
      pose proof (source_two_prefix_change_base M sb sc (code_numeral M 1) a base
        (coding_lt_succ M (code_numeral M 1)) HS1) as HS.
      split;intro H;pose proof (substitution_lookup_functional M _ _ _ _ _ v a H ltac:(eassumption)) as E;
        subst v;assumption.
    + rewrite (substitution_lookup_outside M rb rc (code_numeral M 2) base
        _ v (source_two_succ_not_lt_two M i'')),
        (substitution_lookup_outside M sb sc (code_numeral M 2) base
        _ v (source_two_succ_not_lt_two M i'')). reflexivity.
Qed.

Theorem source_upper_matrix_request_matrix_unique M phi delta p rb rc mat sb sc mat' :
  source_role_reopening M (succM M p) (zeroM M) rb rc ->
  numerical_substitution M phi rb rc (code_numeral M 2) (succM M delta) mat ->
  source_role_reopening M (succM M p) (zeroM M) sb sc ->
  numerical_substitution M phi sb sc (code_numeral M 2) (succM M delta) mat' ->mat=mat'.
Proof.
  intros HR HM HS HM'.
  exact (numerical_substitution_functional_equivalent M phi rb rc (code_numeral M 2)
    sb sc (code_numeral M 2) (succM M delta) mat mat'
    (source_role_reopening_base_equivalent M (succM M p) (zeroM M) rb rc sb sc
      (succM M delta) HR HS) HM HM').
Qed.

Theorem source_upper_matrix_request_functional M phi delta p b x y :
  source_upper_matrix_request_recipe M phi delta p b x ->
  source_upper_matrix_request_recipe M phi delta p b y ->x=y.
Proof.
  intros [rb [rc [mat [HR [HM HX]]]]] [sb [sc [mat' [HS [HM' HY]]]]].
  pose proof (source_upper_matrix_request_matrix_unique M phi delta p rb rc mat sb sc mat'
    HR HM HS HM') as E. subst mat'. exact (code_relation_functional M _ _ x y HX HY).
Qed.

Theorem source_full_upper_witness_closed_use M cb cc cn phi k delta b closed p pb request :
  source_bounded M phi k ->source_upper_witness_closed_recipe M phi delta b closed ->
  sf_relation M SFMember p b pb ->source_upper_matrix_request_recipe M phi delta p b request ->
  source_full_prv M cb cc cn closed ->source_full_prv M cb cc cn pb ->
  source_full_prv M cb cc cn request.
Proof.
  intros HP HC HB HR PC PB.
  destruct (source_full_upper_witness_closed_use_total M cb cc cn phi k delta b closed p pb
    HP HC HB PC PB) as [result [HResult PResult]].
  pose proof (source_upper_matrix_request_functional M phi delta p b result request HResult HR) as E.
  now subst result.
Qed.

Print Assumptions source_role_reopening_base_equivalent.
Print Assumptions source_upper_matrix_request_functional.
Print Assumptions source_full_upper_witness_closed_use.
