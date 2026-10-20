(** Source-defined binary matrices, independently of the surrounding
    Replacement syntax. The three schema renamings quote these matrices. *)
From PAModel Require Import Model NumericalEnvironments NumericalQuotation
  QuotationFunctionality SourceBounded SchemaRenamingDescriptors ReplacementMatrixEnvironment.
Unset Implicit Arguments.

Definition binary_matrix_quotation M phi eb ec en x y fresh domain theta :=
  exists yb yc yn xb xc xn,
    environment_cons M eb ec en y yb yc yn /\
    environment_cons M yb yc yn x xb xc xn /\
    numerical_quotation M phi xb xc xn fresh domain theta.

Lemma binary_matrix_quotation_functional M phi eb ec en x y fresh domain theta theta' :
  binary_matrix_quotation M phi eb ec en x y fresh domain theta ->
  binary_matrix_quotation M phi eb ec en x y fresh domain theta' -> theta=theta'.
Proof.
  intros [yb [yc [yn [xb [xc [xn [HY [HX HQ]]]]]]]]
    [yb' [yc' [yn' [xb' [xc' [xn' [HY' [HX' HQ']]]]]]]].
  assert (EY : environment_equivalent M yb yc yn yb' yc' yn').
  { apply (environment_cons_extensional M eb ec en eb ec en y yb yc yn yb' yc' yn');
      [intros i v;reflexivity|exact HY|exact HY']. }
  assert (EX : environment_equivalent M xb xc xn xb' xc' xn').
  { exact (environment_cons_extensional M yb yc yn yb' yc' yn' x xb xc xn xb' xc' xn' EY HX HX'). }
  apply (numerical_quotation_environment_extensional M phi xb xc xn xb' xc' xn' fresh domain theta EX) in HQ.
  exact (numerical_quotation_functional M phi xb' xc' xn' fresh domain theta theta' HQ HQ').
Qed.

Theorem functionality_body_is_binary_matrix M s phi body bound eb ec en x y z
    xb xc xn yb yc yn zb zc zn fresh domain theta :
  (s=RepA \/ s=RepB) -> source_bounded M phi bound -> schema_renaming M s phi body ->
  environment_cons M eb ec en x xb xc xn ->
  environment_cons M xb xc xn y yb yc yn ->
  environment_cons M yb yc yn z zb zc zn ->
  numerical_quotation M body zb zc zn fresh domain theta ->
  binary_matrix_quotation M phi eb ec en x (replacement_output s y z) fresh domain theta.
Proof.
  intros HS HBound HRen HX HY HZ HQ.
  destruct (environment_cons_total M eb ec en (replacement_output s y z)) as [ob [oc [on HO]]].
  destruct (environment_cons_total M ob oc on x) as [mb [mc [mn HM]]].
  destruct (numerical_quotation_total M phi mb mc mn fresh domain) as [v HV].
  assert (E : v=theta).
  { exact (replacement_functionality_matrix_quotation M s phi body bound eb ec en x y z
      xb xc xn yb yc yn zb zc zn ob oc on mb mc mn fresh domain v theta
      HS HBound HRen HX HY HZ HO HM HV HQ). }
  subst v. exists ob,oc,on,mb,mc,mn. split;[exact HO|]. split;[exact HM|exact HV].
Qed.

Theorem range_body_is_binary_matrix M phi body bound eb ec en a b x y
    ab ac an bb bc bn yb yc yn xb xc xn fresh domain theta :
  source_bounded M phi bound -> schema_renaming M RepC phi body ->
  environment_cons M eb ec en a ab ac an ->
  environment_cons M ab ac an b bb bc bn ->
  environment_cons M bb bc bn y yb yc yn ->
  environment_cons M yb yc yn x xb xc xn ->
  numerical_quotation M body xb xc xn fresh domain theta ->
  binary_matrix_quotation M phi eb ec en x y fresh domain theta.
Proof.
  intros HBound HRen HA HB HY HX HQ.
  destruct (environment_cons_total M eb ec en y) as [mb [mc [mn HM]]].
  destruct (environment_cons_total M mb mc mn x) as [fb [fc [fn HF]]].
  destruct (numerical_quotation_total M phi fb fc fn fresh domain) as [v HV].
  assert (E : v=theta).
  { exact (replacement_range_matrix_quotation M phi body bound eb ec en a b x y
      ab ac an bb bc bn yb yc yn xb xc xn mb mc mn fb fc fn fresh domain v theta
      HBound HRen HA HB HY HX HM HF HV HQ). }
  subst v. exists mb,mc,mn,fb,fc,fn. split;[exact HM|]. split;[exact HF|exact HV].
Qed.

Print Assumptions binary_matrix_quotation_functional.
Print Assumptions functionality_body_is_binary_matrix.
Print Assumptions range_body_is_binary_matrix.
