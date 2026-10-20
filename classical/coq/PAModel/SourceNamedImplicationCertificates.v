(** Literal second Op2 existence proof for An6 minus temporary5. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNamedDifferenceCertificates SourceNamedFiniteCalibration
 SourceNamedQuantifierRules SourceZFRProvability OldNamedSyntaxBridge.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Open Scope minZFsyn.
Unset Implicit Arguments.
Lemma named_implication_second_shape:named_difference_certificate 6 5=
 (named_difference_successor →named_difference_closure →($6 ∈' $2)→($5 ∈' $2)→named_difference_exists 6 5 0).
Proof. reflexivity. Qed.
Theorem source_zfr_named_implication_second M:source_zfr_provable M(code_numeral M(sf_encode
 (named_difference_successor →named_difference_closure →($6 ∈' $2)→($5 ∈' $2)→named_difference_exists 6 5 0))).
Proof. rewrite <-named_implication_second_shape. exact(source_zfr_named_difference_certificate M 6 5). Qed.
Theorem named_implication_second_quantifier M:source_named_quantifier M false(zeroM M)
 (code_numeral M(sf_encode(named_difference_matrix 6 5 0)))(code_numeral M(sf_encode(named_difference_exists 6 5 0))).
Proof. exact(source_finite_named_quantifier_calibration M false 0(named_difference_matrix 6 5 0)). Qed.
Print Assumptions source_zfr_named_implication_second.
Print Assumptions named_implication_second_quantifier.
