(** The lower consistency comparison with its remaining raw-schema inputs
    exposed. This does not prove those inputs or the full ZFC comparison. *)
From PAModel Require Import Model FiniteCoding CodeExpressions ProofTemplates
  FixedSourceBounds BootstrapSpecializations NumericalProofs RawQuotientAtomCongruence
  RawSeparationContract OpenSeparationFromRaw DomainReplacementTemplate
  CoreConsistencyReduction CoreSchemaComparison.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma specialized_marker_raw_graph M marker :
  code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
  raw_empty_marker_graph M (code_numeral M 1) (code_numeral M 2) marker.
Proof.
  intro HM. split.
  - apply (proj2 (fixed_source_numeral_lt_iff M 0 2));lia.
  - split.
    + apply (proj2 (fixed_source_numeral_lt_iff M 1 2));lia.
    + change (code_relation M (fun _=>zeroM M)
        (code_subst (CEconst 1 .: CEconst 2 .: fun _=>CEconst 0)
          (E_wal (CEvar 1) (E_wn (E_wel (CEvar 1) (CEvar 0))))) marker) in HM.
      apply (proj1 (code_subst_graph M (fun _=>zeroM M)
        (CEconst 1 .: CEconst 2 .: fun _=>CEconst 0)
        (code_numeral M 1 .: code_numeral M 2 .: fun _=>zeroM M)
        ltac:(intros [|[|i]];reflexivity) _ marker)). exact HM.
Qed.

Definition raw_core_schema_certificates M := forall marker,
  code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
  raw_domain_separation_certificates M marker /\
  quoted_domain_replacement_template_certificates M marker.

Theorem core_images_from_raw_schema_certificates M :
  raw_core_schema_certificates M -> core_marker_images M.
Proof.
  intro H. apply core_marker_images_from_open_schemas.
  intros marker HM. destruct (H marker HM) as [HS HR]. split.
  - exact (open_separation_images_from_raw_domain M marker
      (specialized_marker_raw_graph M marker HM) HS).
  - exact (open_replacement_images_from_quoted_template M marker HR).
Qed.

Theorem core_refutation_from_raw_schema_certificates M :
  raw_core_schema_certificates M -> source_core_provable M (zeroM M) ->
  numerically_provable M (code_numeral M 1).
Proof.
  intro H. apply source_core_refutation_to_K.
  exact (core_images_from_raw_schema_certificates M H).
Qed.

Theorem core_consistency_from_raw_schema_certificates M :
  raw_core_schema_certificates M ->
  (~numerically_provable M (code_numeral M 1)) -> source_core_consistent M.
Proof.
  intro H. apply K_consistency_implies_source_core_consistency.
  exact (core_images_from_raw_schema_certificates M H).
Qed.

Print Assumptions specialized_marker_raw_graph.
Print Assumptions core_images_from_raw_schema_certificates.
Print Assumptions core_refutation_from_raw_schema_certificates.
Print Assumptions core_consistency_from_raw_schema_certificates.
