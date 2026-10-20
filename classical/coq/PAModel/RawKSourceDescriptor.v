(** A genuine arithmetic source theory: ZFC plus universal closures of the
    actual translated raw K bundles.  Its axiom test mentions only syntax,
    numerical quotation, bounds and closure graphs; no provability predicate
    or successful proof output occurs in the axiom definition. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs NumericalTheories
  NumericalZFCAxioms ClosedSourceQuotation SourceBounded SourceBoundedCalibration NumericalSetClosure SetFormulaCodes SentenceBounds
  RawSourceImage RawSourceImageBounds SourceDescriptorProvability SourceDescriptorClosure
  SourceDescriptorRawTransfer.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition closed_raw_K_bundle M out :=exists a b c u raw source bound,
  c<>a /\ c<>b /\code_relation M (code_parameters a b c u) code_bundle raw /\
  raw_source_image M raw source /\source_bounded M source bound /\all_prefix M bound source out.
Definition rawK_lift7 (t:term) :=t`[↑]`[↑]`[↑]`[↑]`[↑]`[↑]`[↑].
Definition closed_raw_K_bundle_formula (out:term) :form :=
  ∃∃∃∃∃∃∃ ((($4 == $6)→⊥) ∧ ((($4 == $5)→⊥) ∧
    (code_formula code_bundle (code_parameters $6 $5 $4 $3) $2 ∧
    (raw_source_image_formula $2 $1 ∧
    (source_bounded_accept_formula $1 $0 ∧all_prefix_formula $0 $1 (rawK_lift7 out)))))).
Local Opaque holds raw_source_image_formula source_bounded_accept_formula all_prefix_formula.

Theorem closed_raw_K_bundle_formula_correct M rho out :
  holds M rho (closed_raw_K_bundle_formula out) <->closed_raw_K_bundle M (evalM M rho out).
Proof.
  unfold closed_raw_K_bundle_formula,closed_raw_K_bundle.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite code_formula_correct. setoid_rewrite raw_source_image_formula_correct.
  setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite all_prefix_formula_correct.
  unfold evalM,rawK_lift7. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Definition raw_K_source_axiom_formula (out:term) :form :=
  numerical_zfc_source_axiom_formula out ∨closed_raw_K_bundle_formula out.

Theorem raw_K_source_axiom_formula_unary :bounded 1 (raw_K_source_axiom_formula $0).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Definition RawKSourceDescriptor :NumericalTheory :=
  {|theory_formula:=raw_K_source_axiom_formula $0;
    theory_bounded:=raw_K_source_axiom_formula_unary|}.

Theorem RawKSourceDescriptor_axiom M out :
  theory_axiom M RawKSourceDescriptor out <->
    numerical_zfc_source_axiom M out \/closed_raw_K_bundle M out.
Proof.
  unfold theory_axiom,RawKSourceDescriptor,raw_K_source_axiom_formula;cbn -[holds].
  rewrite holds_or,numerical_zfc_source_axiom_formula_correct,closed_raw_K_bundle_formula_correct.
  reflexivity.
Qed.

Theorem closed_raw_K_bundle_closed M out :closed_raw_K_bundle M out ->source_bounded M out (zeroM M).
Proof.
  intros (a&b&c&u&raw&source&bound&HCA&HCB&HR&HS&HB&HP).
  exact (all_prefix_closes M bound source out HB HP).
Qed.

Theorem RawKSourceDescriptor_closed M out :
  theory_axiom M RawKSourceDescriptor out ->source_bounded M out (zeroM M).
Proof.
  intro HA. apply RawKSourceDescriptor_axiom in HA. destruct HA as [HZ|HK].
  - exact (numerical_zfc_source_axiom_closed M out HZ).
  - exact (closed_raw_K_bundle_closed M out HK).
Qed.

Theorem RawKSourceDescriptor_extends_zfc M :source_descriptor_extends_zfc M RawKSourceDescriptor.
Proof. intros out HO. apply RawKSourceDescriptor_axiom. now left. Qed.

Theorem RawKSourceDescriptor_bundle_images M :source_descriptor_raw_bundle_images M RawKSourceDescriptor.
Proof.
  intros a b c u raw out HCA HCB HR HO.
  destruct (raw_source_image_bounded M raw out HO) as (bound&HB).
  destruct (all_prefix_total M bound out) as (closed&HC).
  apply (source_descriptor_provable_prefix_eliminate M RawKSourceDescriptor bound out closed HC).
  apply source_descriptor_provable_axiom.
  - apply RawKSourceDescriptor_axiom. right. exists a,b,c,u,raw,out,bound.
    repeat first[assumption|split].
  - exact (all_prefix_closes M bound out closed HB HC).
Qed.

Theorem raw_K_source_proof_transfer M raw out :
  numerically_provable M raw ->raw_source_image M raw out ->
    source_descriptor_provable M RawKSourceDescriptor out.
Proof.
  exact (raw_source_descriptor_proof_transfer M RawKSourceDescriptor
    (RawKSourceDescriptor_extends_zfc M) (RawKSourceDescriptor_bundle_images M) raw out).
Qed.

Theorem raw_K_source_refutation_transfer M :
  numerically_provable M (code_numeral M 1) ->source_descriptor_provable M RawKSourceDescriptor (zeroM M).
Proof.
  exact (raw_source_descriptor_refutation_transfer M RawKSourceDescriptor
    (RawKSourceDescriptor_extends_zfc M) (RawKSourceDescriptor_bundle_images M)).
Qed.

Print Assumptions closed_raw_K_bundle_formula_correct.
Print Assumptions RawKSourceDescriptor_axiom.
Print Assumptions RawKSourceDescriptor_closed.
Print Assumptions RawKSourceDescriptor_bundle_images.
Print Assumptions raw_K_source_proof_transfer.
Print Assumptions raw_K_source_refutation_transfer.
