(** Literal environment calculations for all three Replacement matrices. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalEnvironments NumericalSubstitutionMaps SubstitutionEnvironment
  SchemaRenamingDescriptors RenamingSubstitution SchemaQuotationTransport
  NumericalQuotation QuotationSubstitution SourceBounded.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma replacement_substitution_lookup M s i v :
  substitution_lookup M (code_numeral M (schema_dividend s))
    (code_numeral M (schema_modulus s)) (code_numeral M (schema_length s))
    (code_numeral M (schema_length s + schema_delta s)) i v <-> schema_lookup M s i v.
Proof.
  unfold schema_lookup. rewrite <-descriptor_numeral_add.
  symmetry;apply renaming_substitution_lookup.
Qed.

Definition replacement_output s {A} (y z:A) := match s with RepB=>z|_=>y end.

Theorem replacement_functionality_environment_agreement M s eb ec en x y z
    xb xc xn yb yc yn zb zc zn ob oc on mb mc mn bound :
  (s=RepA \/ s=RepB) ->
  environment_cons M eb ec en x xb xc xn ->
  environment_cons M xb xc xn y yb yc yn ->
  environment_cons M yb yc yn z zb zc zn ->
  environment_cons M eb ec en (replacement_output s y z) ob oc on ->
  environment_cons M ob oc on x mb mc mn ->
  substitution_environment_agreement M (code_numeral M (schema_dividend s))
    (code_numeral M (schema_modulus s)) (code_numeral M (schema_length s))
    (code_numeral M (schema_length s + schema_delta s))
    zb zc zn mb mc mn bound.
Proof.
  intros HS HX HY HZ HO HM i j u v Hi Hij Hu Hv.
  apply replacement_substitution_lookup in Hij.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[idx ->]].
  - apply schema_lookup_first in Hij.
    assert (Hfirst : schema_first s=2) by (destruct HS as [HS|HS];rewrite HS;reflexivity).
    rewrite Hfirst in Hij;subst j.
    change (environment_lookup M zb zc zn (succM M (succM M (zeroM M))) u) in Hu.
    apply (proj1 (environment_cons_tail M yb yc yn z zb zc zn (succM M (zeroM M)) u HZ)) in Hu.
    apply (proj1 (environment_cons_tail M xb xc xn y yb yc yn (zeroM M) u HY)) in Hu.
    apply (proj1 (environment_cons_head M eb ec en x xb xc xn u HX)) in Hu.
    apply (proj1 (environment_cons_head M ob oc on x mb mc mn v HM)) in Hv.
    congruence.
  - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) idx) as [Eidx|[tail Eidx]];subst idx.
    + apply schema_lookup_second in Hij.
      apply (proj1 (environment_cons_tail M ob oc on x mb mc mn (zeroM M) v HM)) in Hv.
      apply (proj1 (environment_cons_head M eb ec en (replacement_output s y z) ob oc on v HO)) in Hv.
      destruct HS as [HS|HS];subst s;cbn [schema_second replacement_output] in Hij,Hv;subst j.
      * change (environment_lookup M zb zc zn (succM M (zeroM M)) u) in Hu.
        apply (proj1 (environment_cons_tail M yb yc yn z zb zc zn (zeroM M) u HZ)) in Hu.
        apply (proj1 (environment_cons_head M xb xc xn y yb yc yn u HY)) in Hu.
        congruence.
      * change (environment_lookup M zb zc zn (zeroM M) u) in Hu.
        apply (proj1 (environment_cons_head M yb yc yn z zb zc zn u HZ)) in Hu.
        congruence.
    + assert (Htail : ~coding_lt M (succM M (succM M tail)) (code_numeral M (schema_length s))).
      { destruct HS as [HS|HS];rewrite HS;cbn [schema_length];intro Hbad;
          apply (proj1 (coding_lt_succ_cancel M (succM M tail) (succM M (zeroM M)))) in Hbad;
          apply (proj1 (coding_lt_succ_cancel M tail (zeroM M))) in Hbad;
          exact (coding_not_lt_zero M tail Hbad). }
      apply (schema_lookup_tail M s (succM M (succM M tail)) j Htail) in Hij.
      assert (Hdelta : schema_delta s=1) by (destruct HS as [HS|HS];rewrite HS;reflexivity).
      rewrite Hdelta in Hij.
      change (j=addM M (succM M (succM M tail)) (succM M (zeroM M))) in Hij.
      rewrite !Arithmetic.add_succ,Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_zero in Hij.
      subst j.
      apply (proj1 (environment_cons_tail M yb yc yn z zb zc zn (succM M (succM M tail)) u HZ)) in Hu.
      apply (proj1 (environment_cons_tail M xb xc xn y yb yc yn (succM M tail) u HY)) in Hu.
      apply (proj1 (environment_cons_tail M eb ec en x xb xc xn tail u HX)) in Hu.
      apply (proj1 (environment_cons_tail M ob oc on x mb mc mn (succM M tail) v HM)) in Hv.
      apply (proj1 (environment_cons_tail M eb ec en (replacement_output s y z) ob oc on tail v HO)) in Hv.
      exact (environment_lookup_functional M eb ec en tail u v Hu Hv).
Qed.

Theorem replacement_range_environment_agreement M eb ec en a b x y
    ab ac an bb bc bn yb yc yn xb xc xn mb mc mn fb fc fn bound :
  environment_cons M eb ec en a ab ac an ->
  environment_cons M ab ac an b bb bc bn ->
  environment_cons M bb bc bn y yb yc yn ->
  environment_cons M yb yc yn x xb xc xn ->
  environment_cons M eb ec en y mb mc mn ->
  environment_cons M mb mc mn x fb fc fn ->
  substitution_environment_agreement M (code_numeral M (schema_dividend RepC))
    (code_numeral M (schema_modulus RepC)) (code_numeral M (schema_length RepC))
    (code_numeral M (schema_length RepC + schema_delta RepC))
    xb xc xn fb fc fn bound.
Proof.
  intros HA HB HY HX HM HF i j u v Hi Hij Hu Hv.
  apply replacement_substitution_lookup in Hij.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[idx ->]].
  - apply schema_lookup_first in Hij. cbn [schema_first] in Hij;subst j.
    apply (proj1 (environment_cons_head M yb yc yn x xb xc xn u HX)) in Hu.
    apply (proj1 (environment_cons_head M mb mc mn x fb fc fn v HF)) in Hv.
    congruence.
  - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) idx) as [Eidx|[tail Eidx]];subst idx.
    + apply schema_lookup_second in Hij. cbn [schema_second] in Hij;subst j.
      apply (proj1 (environment_cons_tail M yb yc yn x xb xc xn (zeroM M) u HX)) in Hu.
      apply (proj1 (environment_cons_head M bb bc bn y yb yc yn u HY)) in Hu.
      apply (proj1 (environment_cons_tail M mb mc mn x fb fc fn (zeroM M) v HF)) in Hv.
      apply (proj1 (environment_cons_head M eb ec en y mb mc mn v HM)) in Hv.
      congruence.
    + assert (Htail : ~coding_lt M (succM M (succM M tail)) (code_numeral M (schema_length RepC))).
      { cbn [schema_length];intro Hbad.
        apply (proj1 (coding_lt_succ_cancel M (succM M tail) (succM M (zeroM M)))) in Hbad.
        apply (proj1 (coding_lt_succ_cancel M tail (zeroM M))) in Hbad.
        exact (coding_not_lt_zero M tail Hbad). }
      apply (schema_lookup_tail M RepC (succM M (succM M tail)) j Htail) in Hij.
      change (j=addM M (succM M (succM M tail)) (succM M (succM M (zeroM M)))) in Hij.
      rewrite !Arithmetic.add_succ,Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_zero in Hij.
      subst j.
      apply (proj1 (environment_cons_tail M yb yc yn x xb xc xn (succM M (succM M (succM M tail))) u HX)) in Hu.
      apply (proj1 (environment_cons_tail M bb bc bn y yb yc yn (succM M (succM M tail)) u HY)) in Hu.
      apply (proj1 (environment_cons_tail M ab ac an b bb bc bn (succM M tail) u HB)) in Hu.
      apply (proj1 (environment_cons_tail M eb ec en a ab ac an tail u HA)) in Hu.
      apply (proj1 (environment_cons_tail M mb mc mn x fb fc fn (succM M tail) v HF)) in Hv.
      apply (proj1 (environment_cons_tail M eb ec en y mb mc mn tail v HM)) in Hv.
      exact (environment_lookup_functional M eb ec en tail u v Hu Hv).
Qed.

Theorem replacement_functionality_matrix_quotation M s phi body bound eb ec en x y z
    xb xc xn yb yc yn zb zc zn ob oc on mb mc mn fresh domain theta quoted :
  (s=RepA \/ s=RepB) -> source_bounded M phi bound -> schema_renaming M s phi body ->
  environment_cons M eb ec en x xb xc xn ->
  environment_cons M xb xc xn y yb yc yn ->
  environment_cons M yb yc yn z zb zc zn ->
  environment_cons M eb ec en (replacement_output s y z) ob oc on ->
  environment_cons M ob oc on x mb mc mn ->
  numerical_quotation M phi mb mc mn fresh domain theta ->
  numerical_quotation M body zb zc zn fresh domain quoted -> theta=quoted.
Proof.
  intros HS HBound HRen HX HY HZ HO HM HTheta HQuoted.
  apply (numerical_quotation_substitution M phi bound
    (code_numeral M (schema_dividend s)) (code_numeral M (schema_modulus s))
    (code_numeral M (schema_length s)) (code_numeral M (schema_length s + schema_delta s))
    zb zc zn mb mc mn fresh domain body theta quoted HBound).
  - exact (replacement_functionality_environment_agreement M s eb ec en x y z
      xb xc xn yb yc yn zb zc zn ob oc on mb mc mn bound HS HX HY HZ HO HM).
  - pose proof (proj1 (numerical_renaming_substitution M phi
      (code_numeral M (schema_dividend s)) (code_numeral M (schema_modulus s))
      (code_numeral M (schema_length s)) (code_numeral M (schema_delta s)) body) HRen) as HSub.
    rewrite descriptor_numeral_add in HSub. exact HSub.
  - exact HTheta.
  - exact HQuoted.
Qed.

Theorem replacement_range_matrix_quotation M phi body bound eb ec en a b x y
    ab ac an bb bc bn yb yc yn xb xc xn mb mc mn fb fc fn fresh domain theta quoted :
  source_bounded M phi bound -> schema_renaming M RepC phi body ->
  environment_cons M eb ec en a ab ac an ->
  environment_cons M ab ac an b bb bc bn ->
  environment_cons M bb bc bn y yb yc yn ->
  environment_cons M yb yc yn x xb xc xn ->
  environment_cons M eb ec en y mb mc mn ->
  environment_cons M mb mc mn x fb fc fn ->
  numerical_quotation M phi fb fc fn fresh domain theta ->
  numerical_quotation M body xb xc xn fresh domain quoted -> theta=quoted.
Proof.
  intros HBound HRen HA HB HY HX HM HF HTheta HQuoted.
  apply (numerical_quotation_substitution M phi bound
    (code_numeral M (schema_dividend RepC)) (code_numeral M (schema_modulus RepC))
    (code_numeral M (schema_length RepC)) (code_numeral M (schema_length RepC + schema_delta RepC))
    xb xc xn fb fc fn fresh domain body theta quoted HBound).
  - exact (replacement_range_environment_agreement M eb ec en a b x y
      ab ac an bb bc bn yb yc yn xb xc xn mb mc mn fb fc fn bound HA HB HY HX HM HF).
  - pose proof (proj1 (numerical_renaming_substitution M phi
      (code_numeral M (schema_dividend RepC)) (code_numeral M (schema_modulus RepC))
      (code_numeral M (schema_length RepC)) (code_numeral M (schema_delta RepC)) body) HRen) as HSub.
    rewrite descriptor_numeral_add in HSub. exact HSub.
  - exact HTheta.
  - exact HQuoted.
Qed.

Print Assumptions replacement_substitution_lookup.
Print Assumptions replacement_functionality_environment_agreement.
Print Assumptions replacement_range_environment_agreement.
Print Assumptions replacement_functionality_matrix_quotation.
Print Assumptions replacement_range_matrix_quotation.
