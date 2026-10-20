(** Actual named pair/union certificates used by disjunction witnesses. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge SourceNamedPairUnionOld
 SourceLFixed SourceLNonempty OldZFRProofLift SourceNamedDifferenceCertificates SourceNamedFiniteCalibration
 SourceNamedQuantifierRules SourceZFRProvability.
From OldZFC Require Z_base.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition named_pair_operation:sf_form:=isolated_formula(OldZFC.Z_base.Pair0
 (@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 5)).
Definition named_union_operation:sf_form:=isolated_formula(OldZFC.Z_base.Union0
 (@OC.var OB.sig_empty 5)(@OC.var OB.sig_empty 0)).
Definition named_pair_matrix:sf_form:=($5 ∈' $2)∧named_pair_operation.
Definition named_union_matrix:sf_form:=($0 ∈' $2)∧named_union_operation.
Definition named_pair_exists:sf_form:=∃(source_finite_closing 5 named_pair_matrix).
Definition named_union_exists:sf_form:=∃(source_finite_closing 0 named_union_matrix).
Definition named_pair_certificate:sf_form:=named_difference_successor →named_difference_closure →
 ($3 ∈' $2)→($4 ∈' $2)→named_pair_exists.
Definition named_union_certificate:sf_form:=named_difference_successor →named_difference_closure →
 ($3 ∈' $2)→($5 ∈' $2)→named_union_exists.
Lemma named_pair_certificate_shape:named_pair_certificate=isolated_formula old_named_pair_certificate.
Proof. reflexivity. Qed.
Lemma named_union_certificate_shape:named_union_certificate=isolated_formula old_named_union_certificate.
Proof. reflexivity. Qed.
Theorem source_zfr_named_pair_certificate M:source_zfr_provable M(code_numeral M(sf_encode named_pair_certificate)).
Proof.
 rewrite named_pair_certificate_shape. exact(finite_old_zfr_proof_lift M old_L_background old_named_pair_certificate
  old_L_background_valid old_named_pair_proof).
Qed.
Theorem source_zfr_named_union_certificate M:source_zfr_provable M(code_numeral M(sf_encode named_union_certificate)).
Proof.
 rewrite named_union_certificate_shape. exact(finite_old_zfr_proof_lift M old_L_background old_named_union_certificate
  old_L_background_valid old_named_union_proof).
Qed.
Theorem named_pair_quantifier M:source_named_quantifier M false(code_numeral M 5)
 (code_numeral M(sf_encode named_pair_matrix))(code_numeral M(sf_encode named_pair_exists)).
Proof. exact(source_finite_named_quantifier_calibration M false 5 named_pair_matrix). Qed.
Theorem named_union_quantifier M:source_named_quantifier M false(zeroM M)
 (code_numeral M(sf_encode named_union_matrix))(code_numeral M(sf_encode named_union_exists)).
Proof. exact(source_finite_named_quantifier_calibration M false 0 named_union_matrix). Qed.
Print Assumptions source_zfr_named_pair_certificate.
Print Assumptions source_zfr_named_union_certificate.
Print Assumptions named_pair_quantifier.
Print Assumptions named_union_quantifier.
