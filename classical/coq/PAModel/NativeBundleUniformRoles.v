(** Equal and distinct active names share one actual source-proof consumer.
    The only fixed background proofs are Empty and Hosting. No theorem
    about an L relativization is asserted in this source-calculus module. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  NumericalContexts NumericalSourceFull RawSourceImage SourceRoleAbstraction SourceNativeKRecipes
  SourceNamedQuantifierRules NativeEmptyClosure NativeEqualBundle NativeEqualBackgroundCalibration
  NativeKBundle NativeBundleAssembly.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem source_full_equal_native_bundle_standard M b c n a private u phi native :
  private<>a ->raw_source_image M private phi ->
  native_named_evaluation M (code_parameters a a private u) native_K_bundle_template native ->
  source_full_prv M b c n (code_numeral M(sf_encode source_equal_empty)) ->
  source_full_prv M b c n (code_numeral M(sf_encode source_equal_hosting)) ->source_full_prv M b c n native.
Proof.
  intros HNe HDecode HNative PEmpty PHosting.
  destruct(sf_relation_total M SFMember a private) as(member&HMember).
  destruct(sf_relation_total M SFImpl member (zeroM M)) as(negative&HNegative).
  destruct(source_named_quantifier_total M true a negative) as(empty&HEmpty).
  destruct(source_named_quantifier_total M false private empty) as(emptyExists&HEmptyExists).
  destruct(source_named_quantifier_total M false private member) as(host&HHost).
  assert (HEmptyGraph:source_named_empty M a private empty).
  { exists member,negative;auto. }
  apply(source_full_equal_native_bundle M b c n a private u phi member host empty emptyExists native
    HNe HDecode HMember HHost HEmptyGraph HEmptyExists HNative).
  - exact(source_full_hosting_named_instance M b c n a private member host HNe HMember HHost PHosting).
  - rewrite(source_named_empty_exists_code M a private empty emptyExists HNe HEmptyGraph HEmptyExists).
    exact PEmpty.
Qed.

Theorem source_full_kprime_to_native_bundle M b c n a d private u phi abstract kprime native :
  private<>a ->private<>d ->raw_source_image M private phi ->
  source_role_abstraction M a d phi abstract ->source_kprime_core_recipe M abstract kprime ->
  native_named_evaluation M (code_parameters a d private u) native_K_bundle_template native ->
  source_full_prv M b c n (code_numeral M(sf_encode source_equal_empty)) ->
  source_full_prv M b c n (code_numeral M(sf_encode source_equal_hosting)) ->
  source_full_prv M b c n kprime ->source_full_prv M b c n native.
Proof.
  intros HPA HPD HDecode HAbstract HKPrime HNative PEmpty PHost PK.
  destruct(@Peano.D_eq_dec (carrier M)(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) a d) as[E|HNe].
  - subst d. exact(source_full_equal_native_bundle_standard M b c n a private u phi native HPA HDecode HNative PEmpty PHost).
  - exact(source_full_kprime_to_distinct_native_bundle M b c n a d private u phi abstract kprime native
      HNe HPA HPD HDecode HAbstract HKPrime HNative PK).
Qed.

Print Assumptions source_full_equal_native_bundle_standard.
Print Assumptions source_full_kprime_to_native_bundle.
