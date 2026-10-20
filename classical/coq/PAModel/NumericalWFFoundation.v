(** An actual fixed axiom image in every PA model: relativized Foundation
    is provable already in pure source logic, with the relational WF domain. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalContexts
  NumericalSourceFull SourceProofWeakening SourceNumeralLift SourceBounded
  SetFormulaCodes ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes
  SourceRelativization SourceRelativizationFunctionality SourceRelativizationCalibration
  SourceWFFormula SourceWFFoundation.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition source_wf_domain_code M := code_numeral M (sf_encode wf_domain).
Definition source_wf_foundation_image_code M :=
  code_numeral M (sf_encode (sf_relativize wf_domain source_foundation)).

Theorem numerical_wf_domain_bounded M :
  source_bounded M (source_wf_domain_code M) (code_numeral M 1).
Proof.
  apply (proj2 (source_formula_numeral_bounded M wf_domain 1)),wf_domain_bounded.
Qed.

Theorem numerical_wf_foundation_empty M :
  source_full_prv M (zeroM M) (zeroM M) (zeroM M) (source_wf_foundation_image_code M).
Proof.
  exact (source_full_forward_model_empty M (sf_relativize wf_domain source_foundation)
    (wf_foundation_image_prv (@nil sf_form))).
Qed.

Theorem numerical_wf_foundation_image M b c n f rf :
  context_bounded M b c n (zeroM M) -> zfc_source_graph M ZFCFoundation f ->
  source_relativization M (source_wf_domain_code M) f rf -> source_full_prv M b c n rf.
Proof.
  intros HC HF HR.
  assert (HF0:zfc_source_graph M ZFCFoundation (code_numeral M (sf_encode source_foundation))).
  { exact (source_formula_numeral_graph M source_foundation). }
  pose proof (zfc_source_graph_functional M ZFCFoundation f
    (code_numeral M (sf_encode source_foundation)) HF HF0) as EF. subst f.
  pose proof (source_relativization_finite_lift M wf_domain source_foundation) as HR0.
  pose proof (source_relativization_functional M (code_numeral M (sf_encode source_foundation))
    (source_wf_domain_code M) rf (source_wf_foundation_image_code M) HR HR0) as ER. subst rf.
  apply (source_full_prv_weaken_bounded M (zeroM M) (zeroM M) (zeroM M)
    b c n (source_wf_foundation_image_code M) (zeroM M)).
  - exact (numerical_wf_foundation_empty M).
  - intros h HH. exfalso. exact (context_empty M (zeroM M) (zeroM M) h HH).
  - exact HC.
Qed.

Print Assumptions numerical_wf_domain_bounded.
Print Assumptions numerical_wf_foundation_empty.
Print Assumptions numerical_wf_foundation_image.
