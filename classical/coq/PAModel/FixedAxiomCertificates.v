(** Exact finite-certificate targets for the fixed source axioms. A
    certificate is a derivation in thm230, not an assumed axiom image.
    This adapter does not produce the set-theoretic certificate itself. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalEquivalence NumericalEnvironments NumericalQuotation QuotationFunctionality
  QuotationSource QuotationFixedSource QuotientAtomTemplates ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes
  SourceNumeralLift TargetNumeralLift BootstrapSpecializations ProofTemplates.
From K230L Require Import Thm230.
Unset Implicit Arguments.

Definition finite_source_quotation_expression (phi:set_form) :=
  quotation_expression (fun _=>CEconst 0) (CEconst 4) (CEconst 1) phi.
Definition finite_marker_certificate_expression (phi:set_form) :=
  E_wim specialized_marker_expression (finite_source_quotation_expression phi).
Definition finite_marker_certificate_code (phi:set_form) :=
  code_value (fun _=>0) (finite_marker_certificate_expression phi).

Definition fixed_axiom_quotation_expression tag :=
  finite_source_quotation_expression (zfc_fixed_source tag).
Definition fixed_marker_certificate_expression tag :=
  finite_marker_certificate_expression (zfc_fixed_source tag).
Definition fixed_marker_certificate_code tag :=
  finite_marker_certificate_code (zfc_fixed_source tag).

Theorem finite_source_quotation_graph M (phi:set_form) f q :
  code_relation M (fun _=>zeroM M) (sf_expression phi) f ->
  numerical_quotation M f (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 4) (code_numeral M 1) q ->
  code_relation M (fun _=>zeroM M) (finite_source_quotation_expression phi) q.
Proof.
  intros HF HQ.
  destruct (code_relation_total M (finite_source_quotation_expression phi)
    (fun _=>zeroM M)) as [canonical HC].
  assert (HQC : numerical_quotation M f (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 4) (code_numeral M 1) canonical).
  { apply (fixed_source_quotation M (fun _=>zeroM M) phi
      (fun _=>CEconst 0) (CEconst 4) (CEconst 1) (fun _=>zeroM M)
      (code_numeral M 4) (code_numeral M 1) f canonical
      (zeroM M) (zeroM M) (zeroM M)).
    - intro i. reflexivity.
    - intro i. apply (proj2 (environment_empty M (zeroM M) (zeroM M)
        (code_numeral M i) (zeroM M))). reflexivity.
    - reflexivity.
    - reflexivity.
    - exact HF.
    - exact HC. }
  assert (E : canonical=q) by exact (numerical_quotation_functional M f
    (zeroM M) (zeroM M) (zeroM M) (code_numeral M 4) (code_numeral M 1)
    canonical q HQC HQ).
  now subst canonical.
Qed.

Theorem finite_marker_certificate_sound (phi:set_form) :
  thm230 (finite_marker_certificate_code phi) ->
  forall M marker f q,
    code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
    code_relation M (fun _=>zeroM M) (sf_expression phi) f ->
    numerical_quotation M f (zeroM M) (zeroM M) (zeroM M)
      (code_numeral M 4) (code_numeral M 1) q ->
    numerical_implies M marker q.
Proof.
  intros HP M marker f q HM HF HQ.
  apply (proj1 (numerical_implies_expression M (fun _=>zeroM M)
    specialized_marker_expression (finite_source_quotation_expression phi) marker q HM
    (finite_source_quotation_graph M phi f q HF HQ))).
  intros result HR.
  pose proof (code_relation_numeral M (fun _=>0)
    (finite_marker_certificate_expression phi)) as HC.
  change (code_relation M (fun _=>zeroM M) (finite_marker_certificate_expression phi)
    (code_numeral M (finite_marker_certificate_code phi))) in HC.
  assert (E : result=code_numeral M (finite_marker_certificate_code phi)).
  { exact (code_relation_functional M (finite_marker_certificate_expression phi)
      (fun _=>zeroM M) result (code_numeral M (finite_marker_certificate_code phi)) HR HC). }
  subst result. exact (thm230_numeral_lift M (finite_marker_certificate_code phi) HP).
Qed.

Corollary fixed_axiom_quotation_graph M tag f q :
  zfc_source_graph M tag f ->
  numerical_quotation M f (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 4) (code_numeral M 1) q ->
  code_relation M (fun _=>zeroM M) (fixed_axiom_quotation_expression tag) q.
Proof. apply finite_source_quotation_graph. Qed.

Corollary fixed_marker_certificate_sound tag :
  thm230 (fixed_marker_certificate_code tag) ->
  forall M marker f q,
    code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
    zfc_source_graph M tag f ->
    numerical_quotation M f (zeroM M) (zeroM M) (zeroM M)
      (code_numeral M 4) (code_numeral M 1) q ->
    numerical_implies M marker q.
Proof. apply finite_marker_certificate_sound. Qed.

Corollary extensionality_marker_certificate_sound :
  thm230 (fixed_marker_certificate_code ZFCExt) ->
  forall M marker f q,
    code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
    zfc_source_graph M ZFCExt f ->
    numerical_quotation M f (zeroM M) (zeroM M) (zeroM M)
      (code_numeral M 4) (code_numeral M 1) q ->
    numerical_implies M marker q.
Proof. apply fixed_marker_certificate_sound. Qed.

Print Assumptions finite_source_quotation_graph.
Print Assumptions finite_marker_certificate_sound.
Print Assumptions fixed_axiom_quotation_graph.
Print Assumptions fixed_marker_certificate_sound.
Print Assumptions extensionality_marker_certificate_sound.
