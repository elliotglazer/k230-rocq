(** Consume the original trace frame at the exact inner emitted roles. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes
  SetSchemaConstructors SchemaConstructorBounds SourceBounded SourceNativeKMatrixMaps
  SourceUpperTraceFrame SourceEmittedClosureRequest SourceFiniteParameters
  SourceFiniteParameterProofs SourceSubsetClosedPoint SourceUpperProofHelpers
  SourceSequents SourceBoundMonotone SourceTraceBounds NumericalContexts
  NumericalSourceFull SourceContextTransport.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Unset Implicit Arguments.

Theorem source_wf_from_finite M cb cc cn f k :
  source_bounded M f k ->source_context_finite_bound M cb cc cn ->
  source_sequent_wf M cb cc cn f.
Proof.
  intros HF [j HC]. exists (addM M k j). split.
  - exact (source_bounded_monotone M f k (addM M k j) HF (coding_le_add M k j)).
  - apply (context_bounded_monotone M cb cc cn j (addM M k j) HC).
    rewrite Arithmetic.add_comm. apply coding_le_add.
Qed.

Theorem source_upper_trace_frame_context_finite M cb cc cn phi k delta c b x :
  source_upper_trace_frame M cb cc cn phi k delta c b x ->
  source_context_finite_bound M cb cc cn.
Proof.
  intros (profile&theta&atom&matrix&body&witness&sc&xb&HP&HM&HA&HB&HE&HProfile&HW&HSC&HXB&PSC&PW&PProfile&PXB).
  destruct (source_full_prv_wellformed M cb cc cn profile PProfile) as [j [_ HC]]. now exists j.
Qed.

Theorem source_full_frame_emitted_inner_request M cb cc cn phi n subset matB matC selected finalbody target :
  source_upper_trace_frame M cb cc cn phi (succM M (succM M n))
    (code_numeral M 6)(code_numeral M 4)(code_numeral M 5)(code_numeral M 3) ->
  code_relation M (schema_env3 (code_numeral M 5)(code_numeral M 3)(code_numeral M 1))
    (source_parameter_expression source_three_parameter_names (source_point_raw_subset $2 $1)) subset ->
  source_native_k_matrix M NativeKB phi matB ->source_native_k_matrix M NativeKC phi matC ->
  sf_relation M SFAnd matC selected finalbody ->
  sf_relation M SFMember (zeroM M)(code_numeral M 5) selected ->
  sf_relation M SFEx finalbody (zeroM M) target ->
  source_full_prv M cb cc cn subset ->source_full_prv M cb cc cn matB ->
  source_full_prv M cb cc cn target.
Proof.
  intros (profile&theta&atom&matrix&body&witness&sc&xb&HP&HM&HA&HB&HE&HProfile&HW&HSC&HXB&PSC&PW&PProfile&PXB)
    HSub HMB HMC HFinal HSelected HTarget PSub PMB.
  assert (HXBC:code_relation M
    (schema_env3 (code_numeral M 5)(code_numeral M 3)(code_numeral M 1))
    (source_parameter_expression source_three_parameter_names ($1 ∈' $0)) xb).
  { exact (proj2 (schema_expression_graph M _ SFMember (CEvar 1)(CEvar 0)
      (code_numeral M 3)(code_numeral M 5) xb eq_refl eq_refl) HXB). }
  exact (source_full_emitted_inner_request M cb cc cn phi n profile theta atom matrix body
    witness sc xb subset matB matC selected finalbody target HP HM HA HB HE HProfile HW
    (proj1 (source_subset_closed_graph_environment M
      (schema_env3 (code_numeral M 5)(code_numeral M 3)(code_numeral M 1)) sc) HSC)
    HXBC HSub HMB HMC HFinal HSelected HTarget PSC PW PProfile PXB PSub PMB).
Qed.

Print Assumptions source_wf_from_finite.
Print Assumptions source_upper_trace_frame_context_finite.
Print Assumptions source_full_frame_emitted_inner_request.
