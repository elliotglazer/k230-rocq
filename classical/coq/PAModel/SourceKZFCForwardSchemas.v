(** The forward K/ZFC comparison reduced to its four remaining, explicit
    uniform schema-image obligations. All fixed axiom images and domain
    nonemptiness proofs are supplied by checked concrete constructions. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes SourceBounded SourceRelativization NumericalZFCAxioms
  NumericalCoreAxioms NumericalZFRAxioms CoreConsistencyReduction
  SourceZFCProvability SourceZFRProvability SourceSetRelativeTransfer
  SourceWFFormula NumericalWFFoundation NumericalWFNonempty NumericalWFCoreFixed
  SourceLFixed SourceLNonempty SourceLFixedImages ActualCoreComparison.
Unset Implicit Arguments.

Definition wf_separation_image_obligation M := forall f rf,
  numerical_closed_separation M f ->
  source_relativization M (source_wf_domain_code M) f rf -> source_core_provable M rf.
Definition wf_replacement_image_obligation M := forall f rf,
  numerical_closed_replacement M f ->
  source_relativization M (source_wf_domain_code M) f rf -> source_core_provable M rf.
Definition L_separation_image_obligation M := forall f rf,
  numerical_closed_separation M f ->
  source_relativization M (source_L_domain_code M) f rf -> source_zfr_provable M rf.
Definition L_replacement_image_obligation M := forall f rf,
  numerical_closed_replacement M f ->
  source_relativization M (source_L_domain_code M) f rf -> source_zfr_provable M rf.

Theorem wf_axiom_images_from_uniform_schemas M :
  wf_separation_image_obligation M -> wf_replacement_image_obligation M ->
  forall f,numerical_zfr_source_axiom M f -> exists rf,
    source_relativization M (source_wf_domain_code M) f rf /\ source_core_provable M rf.
Proof.
  intros HS HR f HA.
  destruct (source_relativization_total M (source_wf_domain_code M) f) as [rf HRel].
  exists rf. split;[exact HRel|].
  destruct HA as [HC|HF].
  - destruct HC as [[tag [HT HG]]|[Hsep|Hrep]].
    + exact (numerical_wf_all_fixed_core M tag f rf HT HG HRel).
    + exact (HS f rf Hsep HRel).
    + exact (HR f rf Hrep HRel).
  - exact (numerical_wf_foundation_core M f rf HF HRel).
Qed.

Theorem L_axiom_images_from_uniform_schemas M :
  L_separation_image_obligation M -> L_replacement_image_obligation M ->
  forall f,numerical_zfc_source_axiom M f -> exists rf,
    source_relativization M (source_L_domain_code M) f rf /\ source_zfr_provable M rf.
Proof.
  intros HS HR f HA.
  destruct (source_relativization_total M (source_L_domain_code M) f) as [rf HRel].
  exists rf. split;[exact HRel|].
  destruct HA as [[tag HG]|[Hsep|Hrep]].
  - exact (numerical_L_fixed_axiom_images M tag f rf HG HRel).
  - exact (HS f rf Hsep HRel).
  - exact (HR f rf Hrep HRel).
Qed.

Theorem numerical_wf_nonempty_core M :
  source_core_provable M (source_wf_nonempty_code M).
Proof.
  destruct (numerical_wf_nonempty_core_background M) as (b&c&n&HC&HB&HE&HP).
  exists b,c,n. auto.
Qed.

Theorem source_zfc_refutation_to_K_from_uniform_schemas M :
  wf_separation_image_obligation M -> wf_replacement_image_obligation M ->
  L_separation_image_obligation M -> L_replacement_image_obligation M ->
  source_zfc_provable M (zeroM M) -> numerically_provable M (code_numeral M 1).
Proof.
  intros WS WR LS LR HP. apply actual_source_core_refutation_to_K.
  apply (source_zfc_relative_refutation_to_core M
    (source_wf_domain_code M) (source_wf_nonempty_code M)
    (source_L_domain_code M) (source_L_nonempty_code M)).
  - apply numerical_wf_domain_bounded.
  - exact (source_formula_ex_numeral M wf_domain).
  - apply numerical_wf_nonempty_core.
  - exact (wf_axiom_images_from_uniform_schemas M WS WR).
  - apply numerical_L_domain_bounded.
  - exact (source_formula_ex_numeral M source_L_domain).
  - apply numerical_L_nonempty_zfr.
  - exact (L_axiom_images_from_uniform_schemas M LS LR).
  - exact HP.
Qed.

Corollary K_consistency_implies_zfc_from_uniform_schemas M :
  wf_separation_image_obligation M -> wf_replacement_image_obligation M ->
  L_separation_image_obligation M -> L_replacement_image_obligation M ->
  numerical_k_consistent M -> source_zfc_consistent M.
Proof.
  intros WS WR LS LR HK HZ.
  exact (HK (source_zfc_refutation_to_K_from_uniform_schemas M WS WR LS LR HZ)).
Qed.

Print Assumptions wf_axiom_images_from_uniform_schemas.
Print Assumptions L_axiom_images_from_uniform_schemas.
Print Assumptions numerical_wf_nonempty_core.
Print Assumptions source_zfc_refutation_to_K_from_uniform_schemas.
Print Assumptions K_consistency_implies_zfc_from_uniform_schemas.
