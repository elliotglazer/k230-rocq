(** Exact environment calculation for minZF's SeparationBody renaming.
    Under the three schema binders, it sees the element followed by the
    original parameter environment, skipping subset and containing set. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalEnvironments NumericalSubstitutionMaps SubstitutionEnvironment
  SchemaRenamingDescriptors RenamingSubstitution SchemaQuotationTransport
  NumericalQuotation QuotationSubstitution SourceBounded QuotationHygiene SubstitutionEnvironmentTotal
  QuotationFormulaFresh FreshNames.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma separation_substitution_lookup M i v :
  substitution_lookup M (code_numeral M 0) (code_numeral M 0)
    (code_numeral M 1) (code_numeral M 3) i v <-> schema_lookup M SepBody i v.
Proof.
  unfold schema_lookup. cbn [schema_dividend schema_modulus schema_length schema_delta].
  rewrite (renaming_substitution_lookup M (code_numeral M 0) (code_numeral M 0)
    (code_numeral M 1) (code_numeral M 2) i v).
  rewrite descriptor_numeral_add. reflexivity.
Qed.

Theorem separation_matrix_environment_agreement M eb ec en a b x
    ab ac an bb bc bn xb xc xn mb mc mn bound :
  environment_cons M eb ec en a ab ac an ->
  environment_cons M ab ac an b bb bc bn ->
  environment_cons M bb bc bn x xb xc xn ->
  environment_cons M eb ec en x mb mc mn ->
  substitution_environment_agreement M (code_numeral M 0) (code_numeral M 0)
    (code_numeral M 1) (code_numeral M 3) xb xc xn mb mc mn bound.
Proof.
  intros HA HB HX HM i j u v Hi Hij Hu Hv.
  apply separation_substitution_lookup in Hij.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[idx ->]].
  - apply schema_lookup_first in Hij. subst j.
    apply (proj1 (environment_cons_head M bb bc bn x xb xc xn u HX)) in Hu.
    apply (proj1 (environment_cons_head M eb ec en x mb mc mn v HM)) in Hv.
    congruence.
  - apply (schema_lookup_tail M SepBody (succM M idx) j) in Hij.
    2: { intro Hbad. apply (proj1 (coding_lt_succ_cancel M idx (zeroM M))) in Hbad.
         exact (coding_not_lt_zero M idx Hbad). }
    change (j=addM M (succM M idx) (code_numeral M 2)) in Hij.
    rewrite Arithmetic.add_succ,(Arithmetic.add_comm M idx (code_numeral M 2)) in Hij.
    change (j=succM M (addM M (succM M (succM M (zeroM M))) idx)) in Hij.
    rewrite !Arithmetic.add_succ,Arithmetic.add_zero in Hij.
    subst j.
    apply (proj1 (environment_cons_tail M bb bc bn x xb xc xn (succM M (succM M idx)) u HX)) in Hu.
    apply (proj1 (environment_cons_tail M ab ac an b bb bc bn (succM M idx) u HB)) in Hu.
    apply (proj1 (environment_cons_tail M eb ec en a ab ac an idx u HA)) in Hu.
    apply (proj1 (environment_cons_tail M eb ec en x mb mc mn idx v HM)) in Hv.
    exact (environment_lookup_functional M eb ec en idx u v Hu Hv).
Qed.

Theorem separation_matrix_quotation M phi body bound eb ec en a b x
    ab ac an bb bc bn xb xc xn mb mc mn fresh domain theta quoted :
  source_bounded M phi bound -> schema_renaming M SepBody phi body ->
  environment_cons M eb ec en a ab ac an ->
  environment_cons M ab ac an b bb bc bn ->
  environment_cons M bb bc bn x xb xc xn ->
  environment_cons M eb ec en x mb mc mn ->
  numerical_quotation M phi mb mc mn fresh domain theta ->
  numerical_quotation M body xb xc xn fresh domain quoted -> theta=quoted.
Proof.
  intros HBound HRen HA HB HX HM HTheta HQuoted.
  apply (numerical_quotation_substitution M phi bound
    (code_numeral M 0) (code_numeral M 0) (code_numeral M 1) (code_numeral M 3)
    xb xc xn mb mc mn fresh domain body theta quoted HBound).
  - exact (separation_matrix_environment_agreement M eb ec en a b x
      ab ac an bb bc bn xb xc xn mb mc mn bound HA HB HX HM).
  - pose proof (proj1 (numerical_renaming_substitution M phi
      (code_numeral M 0) (code_numeral M 0) (code_numeral M 1) (code_numeral M 2) body) HRen) as HSub.
    rewrite descriptor_numeral_add in HSub. exact HSub.
  - exact HTheta.
  - exact HQuoted.
Qed.

Lemma separation_below_avoids M b c n k :
  environment_below M b c n k -> quotation_environment_avoids M b c n k.
Proof.
  intros H i v HV. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) v k (H i v HV)).
Qed.

Theorem separation_matrix_fresh M phi eb ec en k mb mc mn theta :
  quotation_safe M eb ec en k (code_numeral M 1) ->
  environment_cons M eb ec en (succM M (succM M k)) mb mc mn ->
  numerical_quotation M phi mb mc mn (succM M (succM M (succM M k))) (code_numeral M 1) theta ->
  formula_fresh M theta k /\ formula_fresh M theta (succM M k).
Proof.
  intros [H1K HEnv] HCons HTheta.
  assert (H0K : coding_lt M (zeroM M) k) by exact (environment_below_zero M eb ec en k HEnv).
  assert (HKS : coding_lt M k (succM M k)) by apply coding_lt_succ.
  assert (HSS : coding_lt M (succM M k) (succM M (succM M k))) by apply coding_lt_succ.
  assert (HSSS : coding_lt M (succM M (succM M k)) (succM M (succM M (succM M k)))) by apply coding_lt_succ.
  assert (HKE : quotation_environment_avoids M mb mc mn k).
  { apply (quotation_environment_avoids_cons M eb ec en (succM M (succM M k)) mb mc mn k
      (separation_below_avoids M eb ec en k HEnv));[|exact HCons].
    intro E. apply (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) k (succM M (succM M k))
      (coding_lt_trans M _ _ _ HKS HSS)). symmetry;exact E. }
  assert (HSE : quotation_environment_avoids M mb mc mn (succM M k)).
  { assert (HBelow : environment_below M eb ec en (succM M k)).
    { intros i v HV. exact (coding_lt_trans M v k (succM M k) (HEnv i v HV) HKS). }
    apply (quotation_environment_avoids_cons M eb ec en (succM M (succM M k)) mb mc mn (succM M k)
      (separation_below_avoids M eb ec en (succM M k) HBelow));[|exact HCons].
    intro E. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) (succM M k) (succM M (succM M k)) HSS (Logic.eq_sym E)). }
  split;apply (numerical_quotation_formula_fresh M phi mb mc mn
    (succM M (succM M (succM M k))) (code_numeral M 1) theta);try assumption.
  - exact (coding_lt_trans M _ _ _ HKS (coding_lt_trans M _ _ _ HSS HSSS)).
  - intro E. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) (zeroM M) k H0K (Logic.eq_sym E)).
  - intro E. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) (code_numeral M 1) k H1K (Logic.eq_sym E)).
  - exact (coding_lt_trans M _ _ _ HSS HSSS).
  - intro E. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) (zeroM M) (succM M k)
      (coding_lt_trans M _ _ _ H0K HKS) (Logic.eq_sym E)).
  - intro E. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) (code_numeral M 1) (succM M k)
      (coding_lt_trans M _ _ _ H1K HKS) (Logic.eq_sym E)).
Qed.

Print Assumptions separation_matrix_environment_agreement.
Print Assumptions separation_matrix_quotation.
Print Assumptions separation_matrix_fresh.
